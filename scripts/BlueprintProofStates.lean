module

import Lean.Meta.PPGoal
import Lean.Server.References
import Lean.Server.InfoUtils
import Lean.Elab.Command
import Lean.Elab.Command.Scope
import Lean.Elab.Frontend
import Lean.Elab.Import
import SubVerso.Compat
import SubVerso.Highlighting.Code
import SubVerso.Highlighting.Export
import SubVerso.Module

open Lean Elab Frontend Meta
open Lean.Elab.Command hiding Context
open SubVerso
open SubVerso.Highlighting

noncomputable section

private structure TermGoal where
  startPos : Nat
  endPos : Nat
  goals : Array Nat
deriving ToJson

private structure TermGoalRequest where
  startPos : Nat
  endPos : Nat
  contextInfo : ContextInfo
  goalId : MVarId

/-- A maximal interval of caret positions for which Lean's InfoView selects the same proof state. -/
private structure TacticState where
  startPos : Nat
  endPos : Nat
  goals : Array Nat
deriving ToJson

private structure SourceItem where
  name : String
  displayName : String
  itemIndex : Nat
  sourceStart : Nat
  sourceEnd : Nat
  declarationStart : Nat
  bodyStart : Nat
  bodyEnd : Nat
  tacticProof : Bool
deriving ToJson

private structure SourceReference where
  moduleName : String
  name : String
  range : Option Lean.Lsp.Range
  targetStartLine : Option Nat
  targetEndLine : Option Nat
deriving ToJson

private structure SourceCommand where
  sourceStart : Nat
  sourceEnd : Nat
deriving ToJson

private structure SourceMessage where
  startPos : Nat
  endPos : Nat
  severity : String
  text : String
deriving ToJson

private structure ProofStates where
  termGoals : Array TermGoal
  tacticStates : Array TacticState
  data : SubVerso.Highlighting.Export
  highlighted : SubVerso.Module.Module
  commands : Array SourceCommand
  items : Array SourceItem
  references : Array SourceReference
  messages : Array SourceMessage
deriving ToJson

private structure SourceRange where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  tacticProof : Bool

private partial def collectTermGoalRequests (trees : PersistentArray InfoTree) :
    IO (Array TermGoalRequest) := do
  let goals ← IO.mkRef (#[] : Array TermGoalRequest)
  for tree in trees do
    tree.visitM' (m := IO) (postNode := fun ci info _ => do
      let .ofTermInfo ti := info | return
      let some startPos := ti.stx.getPos? (canonicalOnly := true) | return
      let some endPos := ti.stx.getTailPos? (canonicalOnly := true) | return
      if startPos >= endPos then return
      try
        let localContext := if ti.isBinder then ti.lctx.pop else ti.lctx
        let (goalId, mctx) ← ci.runMetaM localContext do
          let expectedType ← instantiateMVars <| ti.expectedType?.getD (← inferType ti.expr)
          let goal ← mkFreshExprMVar expectedType
          return (goal.mvarId!, (← getMCtx))
        goals.modify (·.push {
          startPos := startPos.byteIdx
          endPos := endPos.byteIdx
          contextInfo := { ci with mctx }
          goalId
        })
      catch _ => return)
  goals.get

private def selectedGoals (fileMap : FileMap) (trees : PersistentArray InfoTree)
    (pos : String.Pos.Raw) : List GoalsAtResult :=
  let results := trees.toList.flatMap fun tree => tree.goalsAt? fileMap pos
  let maxPriority := results.map (·.priority) |>.max?
  results.filter (some ·.priority == maxPriority)

private def selectedGoalsKey (results : List GoalsAtResult) : String :=
  String.intercalate "|" <| results.map fun result =>
    let tactic := result.tacticInfo
    let goals := if result.useAfter then tactic.goalsAfter else tactic.goalsBefore
    let startPos :=
      tactic.stx.getPos? (canonicalOnly := true) |>.map (·.byteIdx) |>.getD 0
    let endPos :=
      tactic.stx.getTailPos? (canonicalOnly := true) |>.map (·.byteIdx) |>.getD 0
    let goalNames := String.intercalate "," <| goals.map (·.name.toString)
    s!"{startPos}:{endPos}:{result.useAfter}:{goalNames}"

private structure DiffSpan where
  startPos : Nat
  endPos : Nat
  status : String

private partial def diffStatus? : Token.Kind → Option String
  | .diff status _ => some status
  | _ => none

private partial def diffSpans (highlighted : Highlighted) (position : Nat := 0) :
    Nat × Array DiffSpan :=
  match highlighted with
  | .token token =>
    let endPos := position + token.content.utf8ByteSize
    let spans := match diffStatus? token.kind with
      | some status => #[⟨position, endPos, status⟩]
      | none => #[]
    (endPos, spans)
  | .text value | .unparsed value => (position + value.utf8ByteSize, #[])
  | .seq values => values.foldl (init := (position, #[])) fun (position, spans) value =>
      let (position, next) := diffSpans value position
      (position, spans ++ next)
  | .span _ content | .tactics _ _ _ content => diffSpans content position
  | .point .. => (position, #[])

private partial def applyDiffSpans (spans : Array DiffSpan) (highlighted : Highlighted)
    (position : Nat := 0) : Nat × Highlighted :=
  match highlighted with
  | .token token =>
    let endPos := position + token.content.utf8ByteSize
    let status := spans.find? fun span => span.startPos < endPos && position < span.endPos
    let token := status.map (fun span => { token with kind := .diff span.status token.kind })
      |>.getD token
    (endPos, .token token)
  | .text value => (position + value.utf8ByteSize, .text value)
  | .unparsed value => (position + value.utf8ByteSize, .unparsed value)
  | .seq values =>
    let (position, values) := values.foldl (init := (position, #[]))
      fun (position, output) value =>
        let (position, value) := applyDiffSpans spans value position
        (position, output.push value)
    (position, .seq values)
  | .span info content =>
    let (position, content) := applyDiffSpans spans content position
    (position, .span info content)
  | .tactics info startPos endPos content =>
    let (position, content) := applyDiffSpans spans content position
    (position, .tactics info startPos endPos content)
  | value@(.point ..) => (position, value)

private def applyDiff (rich diff : Highlighted) : Highlighted :=
  if rich.toString != diff.toString then rich
  else (applyDiffSpans (diffSpans diff).2 rich).2

private def mergeGoalDiff (rich diff : Highlighted.Goal Highlighted) :
    Highlighted.Goal Highlighted :=
  let hypotheses := if rich.hypotheses.size != diff.hypotheses.size then rich.hypotheses
    else rich.hypotheses.zipWith (fun rich diff => {
      rich with
      typeAndVal := applyDiff rich.typeAndVal diff.typeAndVal
      isInserted := diff.isInserted
      isRemoved := diff.isRemoved
    }) diff.hypotheses
  {
    rich with
    hypotheses
    conclusion := applyDiff rich.conclusion diff.conclusion
    isInserted := diff.isInserted
    isRemoved := diff.isRemoved
  }

private structure SemanticGoals where
  value : Array (Highlighted.Goal Highlighted)

/-- Highlight proof states from one command while sharing SubVerso's expression caches. -/
private structure GoalHighlighter where
  context : Highlighting.Context
  infoTable : Highlighting.InfoTable
  state : IO.Ref Highlighting.HighlightState

private def GoalHighlighter.create (trees : PersistentArray InfoTree) :
    TermElabM GoalHighlighter := do
  let trees := trees.toArray
  let moduleReferences := Lean.Server.findModuleRefs (← getFileMap) trees
  let signatureCache ← IO.mkRef {}
  let state ← IO.mkRef Highlighting.HighlightState.empty
  return {
    context := {
      ids := Highlighting.build moduleReferences
      definitionsPossible := true
      includeUnparsed := false
      suppressNamespaces := []
      collectFormat := false
      sigCache := signatureCache
    }
    infoTable := .ofInfoTrees trees
    state
  }

private def GoalHighlighter.run {α : Type} (highlighter : GoalHighlighter)
    (action : Highlighting.HighlightM α) : TermElabM α := do
  let state ← highlighter.state.get
  let (result, state) ← action.run highlighter.context |>.run highlighter.infoTable |>.run state
  highlighter.state.set state
  return result

private partial def semanticConstant? : Token.Kind → Option Name
  | .diff _ kind => semanticConstant? kind
  | .const name .. => some name
  | _ => none

private partial def highlightedSemanticConstants (highlighted : Highlighted) : Array Name :=
  match highlighted with
  | .token token => semanticConstant? token.kind |>.map (#[·]) |>.getD #[]
  | .seq values => values.flatMap highlightedSemanticConstants
  | .span _ content | .tactics _ _ _ content => highlightedSemanticConstants content
  | _ => #[]

private def SemanticGoals.semanticConstants (goals : SemanticGoals) : Array Name :=
  goals.value.flatMap fun goal =>
    goal.hypotheses.flatMap (highlightedSemanticConstants ·.typeAndVal) ++
      highlightedSemanticConstants goal.conclusion

private structure SemanticTermGoal where
  startPos : Nat
  endPos : Nat
  goals : SemanticGoals

private def highlightTermGoals (highlighter : GoalHighlighter)
    (requests : Array TermGoalRequest) :
    TermElabM (Array SemanticTermGoal) := do
  let mut output := #[]
  for request in requests do
    try
      let context := highlighter.context.noDefinitions
      let state ← highlighter.state.get
      let (goals, state) ← Highlighting.highlightGoals request.contextInfo [request.goalId]
        |>.run context |>.run highlighter.infoTable |>.run state
      highlighter.state.set state
      output := output.push {
        startPos := request.startPos
        endPos := request.endPos
        goals := ⟨goals⟩
      }
    catch _ => pure ()
  return output

private def highlightResult (highlighter : GoalHighlighter) (result : GoalsAtResult) :
    TermElabM SemanticGoals := do
  let ci := if result.useAfter then
    { result.ctxInfo with mctx := result.tacticInfo.mctxAfter }
  else
    { result.ctxInfo with mctx := result.tacticInfo.mctxBefore }
  let goalIds := if result.useAfter then
    result.tacticInfo.goalsAfter
  else
    result.tacticInfo.goalsBefore
  let richGoals ← highlighter.run <| Highlighting.highlightGoals ci goalIds
  let diffGoals ← highlighter.run <| Highlighting.diffedTacticGoals
    result.ctxInfo result.tacticInfo (!result.useAfter)
  if richGoals.size != diffGoals.size then return ⟨richGoals⟩
  return ⟨richGoals.zipWith mergeGoalDiff diffGoals⟩

private def highlightResults (highlighter : GoalHighlighter) (results : List GoalsAtResult) :
    TermElabM SemanticGoals := do
  let mut goals := #[]
  for result in results do
    goals := goals ++ (← highlightResult highlighter result).value
  pure ⟨goals⟩

private def exportGoals (goals : SemanticGoals)
    (state : SubVerso.Highlighting.Exporting) :
    Array Nat × SubVerso.Highlighting.Exporting :=
  goals.value.mapM (fun goal => Highlighted.Goal.export goal) |>.run state

private def parseNames (value : String) : Array Name :=
  value.splitOn "," |>.filter (!·.isEmpty) |>.toArray.map (·.toName)

private partial def declarationCommand? (command : Syntax) : Option Syntax :=
  match command with
  | `(command| $_command₁ in $command₂) => declarationCommand? command₂
  | _ => if command.isOfKind ``Parser.Command.declaration then some command else none

private def declarationValue? (command : Syntax) : Option Syntax := do
  let command ← declarationCommand? command
  let declaration := command[1]
  let kind := declaration.getKind
  if kind == ``Parser.Command.«abbrev» || kind == ``Parser.Command.definition ||
      kind == ``Parser.Command.theorem then
    return declaration[3]
  if kind == ``Parser.Command.opaque then
    return ← declaration[3].getOptional?
  if kind == ``Parser.Command.instance then
    return declaration[5]
  if kind == ``Parser.Command.«example» then
    return declaration[2]
  none

private def declarationBody? (command : Syntax) : Option Syntax := do
  let value ← declarationValue? command
  if value.isOfKind ``Parser.Command.declValSimple then some value[1] else some value

private def declarationStart? (command : Syntax) : Option String.Pos.Raw := do
  let command ← declarationCommand? command
  command[1].getPos? (canonicalOnly := true)

private def declarationDisplayName? (command : Syntax) : Option Name := do
  let command ← declarationCommand? command
  let declaration := command[1]
  if declaration.getKind == ``Parser.Command.instance then
    let name ← declaration[3].getOptional?
    if name[0].isIdent then some name[0].getId else none
  else if declaration.getKind == ``Parser.Command.«example» then
    none
  else if declaration[1][0].isIdent then
    some declaration[1][0].getId
  else
    none

private partial def commandKind (command : Syntax) : SyntaxNodeKind :=
  match command with
  | `(command| $_command₁ in $command₂) => commandKind command₂
  | _ => command.getKind

private def itemRange? (item : Compat.Frontend.FrontendItem) : Option SourceRange := do
  let startPos ← item.commandSyntax.getPos? (canonicalOnly := true)
  let endPos ← item.commandSyntax.getTrailingTailPos? (canonicalOnly := true)
  return ⟨startPos, endPos, false⟩

private def intersection? (left right : SourceRange) : Option SourceRange :=
  let startPos := max left.startPos right.startPos
  let endPos := min left.endPos right.endPos
  if startPos ≤ endPos then some ⟨startPos, endPos, right.tacticProof⟩ else none

/-- Remove tactic goals from the copy of an info tree used for ordinary source highlighting. -/
private partial def withoutTacticGoals : InfoTree → InfoTree
  | .context context tree => .context context (withoutTacticGoals tree)
  | .node info children =>
    let info := match info with
      | .ofTacticInfo tactic =>
        .ofTacticInfo { tactic with
          goalsBefore := []
          goalsAfter := [] }
      | info => info
    let children := children.foldl (init := {}) fun output child =>
      output.push (withoutTacticGoals child)
    .node info children
  | .hole mvarId => .hole mvarId

/-- Locate selected declarations without highlighting every command. Private names acquire a fresh
internal prefix during re-elaboration, so compare their stable user-facing names. -/
private def findSelectedItemNames (fileMap : FileMap) (result : Compat.Frontend.FrontendResult)
    (references : Lean.Server.ModuleRefs) (requestedNames : Array Name) :
    IO (Array (Nat × Name)) := do
  let mut selected := #[]
  for name in requestedNames do
    let mut position? := none
    for (ident, info) in references do
      match ident, info.definition with
      | .const _ defined, some definition =>
        if privateToUserName name == privateToUserName defined.toName then
          position? := some definition.range.start
          break
      | _, _ => continue
    let some position := position?
      | throw <| IO.userError s!"{name}: declaration reference not found"
    let mut itemIndex? := none
    for itemIndex in [:result.items.size] do
      let item := result.items[itemIndex]!
      match item.commandSyntax.getPos? (canonicalOnly := true),
          item.commandSyntax.getTrailingTailPos? (canonicalOnly := true) with
      | some startPos, some endPos =>
        let startPos := fileMap.utf8PosToLspPos startPos
        let endPos := fileMap.utf8PosToLspPos endPos
        if startPos ≤ position && position ≤ endPos then
          itemIndex? := some itemIndex
          break
      | _, _ => continue
    let some itemIndex := itemIndex?
      | throw <| IO.userError s!"{name}: declaration command not found"
    selected := selected.push (itemIndex, name)
  return selected.qsort fun left right => left.1 < right.1

/-- Retain the commands rendered by the guide and discard tactic goals, which are exported by the
separate exact-goal pass below. -/
private def sourceHighlightResult (result : Compat.Frontend.FrontendResult)
    (selectedItemIndices : Array Nat) (selectAll : Bool) : Compat.Frontend.FrontendResult :=
  { result with items := result.items.mapIdx fun itemIndex item =>
      let kind := commandKind item.commandSyntax
      if selectAll || selectedItemIndices.contains itemIndex ||
          kind == ``Parser.Command.universe || kind == ``Parser.Command.variable then
        { item with info := item.info.foldl (init := {}) fun output tree =>
            output.push (withoutTacticGoals tree) }
      else
        { commandSyntax := .missing, info := {}, messages := {} } }

/--
Caret positions on which `InfoTree.goalsAt?` can change. Its definition compares the caret only
with tactic starts, tactic ends, trailing ends, nested tactic ends, and indentation columns.
-/
private partial def goalSelectionBoundaries (contents : String) (fileMap : FileMap)
    (trees : PersistentArray InfoTree) (range : SourceRange) : IO (Array String.Pos.Raw) := do
  let positions ← IO.mkRef #[range.startPos, range.endPos]
  let indentationRanges ← IO.mkRef
    (#[] : Array (String.Pos.Raw × String.Pos.Raw × Nat))
  let add (pos : String.Pos.Raw) : IO Unit := do
    if range.startPos ≤ pos && pos ≤ range.endPos then
      positions.modify (·.push pos)
  let addWithSuccessor (pos : String.Pos.Raw) : IO Unit := do
    add pos
    if pos < range.endPos then
      add (min (String.Pos.Raw.next contents pos) range.endPos)
  for tree in trees do
    tree.visitM' (m := IO) (postNode := fun _ info _ => do
      let .ofTacticInfo tactic := info | return
      let some startPos := tactic.stx.getPos? (canonicalOnly := true) | return
      let some endPos := tactic.stx.getTailPos? (canonicalOnly := true) | return
      addWithSuccessor startPos
      addWithSuccessor endPos
      let trailingEnd : String.Pos.Raw := ⟨endPos.byteIdx + tactic.stx.getTrailingSize⟩
      addWithSuccessor trailingEnd
      let hoverEnd : String.Pos.Raw :=
        ⟨endPos.byteIdx + max 1 tactic.stx.getTrailingSize⟩
      addWithSuccessor hoverEnd
      indentationRanges.modify (·.push
        (startPos, hoverEnd, (fileMap.toPosition startPos).column)))
  let indentationRanges ← indentationRanges.get
  let mut pos := range.startPos
  while pos ≤ range.endPos do
    let column := (fileMap.toPosition pos).column
    if indentationRanges.any fun (startPos, endPos, tacticColumn) =>
        startPos ≤ pos && pos ≤ endPos && (column == 0 || column == tacticColumn) then
      add pos
    if pos == range.endPos then break
    pos := min (String.Pos.Raw.next contents pos) range.endPos
  let sorted := (← positions.get).qsort (fun left right => left < right)
  return sorted.foldl (init := #[]) fun unique pos =>
    if unique.back? == some pos then unique else unique.push pos

private unsafe def extract (moduleName : Name) (requestedNames : Array Name) (timings : Bool) :
    IO ProofStates := do
  let totalStart ← IO.monoMsNow
  initSearchPath (← findSysroot)
  let searchPath ← Compat.initSrcSearchPath
  let searchPath : SearchPath :=
    (searchPath : List System.FilePath) ++ [("." : System.FilePath)]
  let some fileName ← searchPath.findModuleWithExt "lean" moduleName
    | throw <| IO.userError s!"cannot find module {moduleName}"
  let contents ← IO.FS.readFile fileName
  let fileMap := FileMap.ofString contents
  let inputContext := Parser.mkInputContext contents fileName.toString
  let (headerSyntax, parserState, messages) ← Parser.parseHeader inputContext
  let imports := headerToImports headerSyntax
  enableInitializersExecution
  let environment ← Compat.importModules imports {} (isModule := Compat.isModule headerSyntax)
    (asServer := true)
  let parserContext : Frontend.Context := { inputCtx := inputContext }
  let commandState : Command.State :=
    { env := environment
      maxRecDepth := defaultMaxRecDepth
      messages := messages }
  let commandStateRef ← IO.mkRef { commandState, parserState, cmdPos := parserState.pos }
  let processStart ← IO.monoMsNow
  let result ← Compat.Frontend.processCommands headerSyntax parserContext commandStateRef
  let processMs := (← IO.monoMsNow) - processStart
  let moduleReferencesStart ← IO.monoMsNow
  let moduleReferences := Lean.Server.findModuleRefs fileMap <|
    result.items.flatMap (·.info.toArray)
  let moduleReferencesMs := (← IO.monoMsNow) - moduleReferencesStart
  let selectAll := requestedNames.contains `__all__
  let selectedCommands ← if selectAll then pure #[] else
    findSelectedItemNames fileMap result moduleReferences requestedNames
  let selectedItemIndices := selectedCommands.map (·.1)
  let sourceHighlightStart ← IO.monoMsNow
  let highlighted ← (Frontend.runCommandElabM <| liftTermElabM <|
    Highlighting.highlightFrontendResult
      (sourceHighlightResult result selectedItemIndices selectAll))
      parserContext commandStateRef
  let sourceHighlightMs := (← IO.monoMsNow) - sourceHighlightStart
  let header := highlighted[0]!
  let highlighted := highlighted.extract 1 highlighted.size
  let moduleItems : Array SubVerso.Module.ModuleItem :=
      highlighted.zip result.items |>.map fun (code, item) => {
    defines := code.definedNames.toArray
    kind := commandKind item.commandSyntax
    range := item.commandSyntax.getRange?.map fun ⟨startPos, endPos⟩ =>
      (fileMap.toPosition startPos, fileMap.toPosition endPos)
    code
  }
  let headerItem : SubVerso.Module.ModuleItem := {
    defines := header.definedNames.toArray
    kind := result.headerSyntax.getKind
    range := result.headerSyntax.getRange?.map fun ⟨startPos, endPos⟩ =>
      (fileMap.toPosition startPos, fileMap.toPosition endPos)
    code := header
  }
  let highlightedModule : SubVerso.Module.Module := ⟨#[headerItem] ++ moduleItems⟩
  let commands := result.items.map fun item => {
    sourceStart := item.commandSyntax.getPos? (canonicalOnly := true) |>.map (·.byteIdx) |>.getD 0
    sourceEnd := item.commandSyntax.getTrailingTailPos? (canonicalOnly := true)
      |>.map (·.byteIdx) |>.getD 0
  }
  let mut selectedItems := #[]
  let mut requestedRanges := #[]
  let selectedDefinitions : Array (Nat × Name) := if selectAll then
    (highlighted.mapIdx fun itemIndex code =>
      code.definedNames.toArray[0]?.map (itemIndex, ·)).filterMap id
  else selectedCommands
  for (itemIndex, name) in selectedDefinitions do
    let item := result.items[itemIndex]!
    let some sourceStart := item.commandSyntax.getPos? (canonicalOnly := true)
      | throw <| IO.userError s!"{name}: command has no source start"
    let some sourceEnd := item.commandSyntax.getTrailingTailPos? (canonicalOnly := true)
      | throw <| IO.userError s!"{name}: command has no source end"
    let some declarationStart := declarationStart? item.commandSyntax
      | if selectAll then continue
        else throw <| IO.userError s!"{name}: unsupported command {item.commandSyntax.getKind}"
    let some body := declarationBody? item.commandSyntax
      | if selectAll then continue
        else throw <| IO.userError s!"{name}: declaration has no body"
    let some bodyStart := body.getPos? (canonicalOnly := true)
      | throw <| IO.userError s!"{name}: body has no source start"
    let some bodyEnd := body.getTailPos? (canonicalOnly := true)
      | throw <| IO.userError s!"{name}: body has no source end"
    let tacticProof := body.isOfKind ``Parser.Term.byTactic
    selectedItems := selectedItems.push {
      name := name.toString
      displayName := (declarationDisplayName? item.commandSyntax).getD name |>.toString
      itemIndex
      sourceStart := sourceStart.byteIdx
      sourceEnd := sourceEnd.byteIdx
      declarationStart := declarationStart.byteIdx
      bodyStart := bodyStart.byteIdx
      bodyEnd := bodyEnd.byteIdx
      tacticProof
    }
    requestedRanges := requestedRanges.push ⟨bodyStart, bodyEnd, tacticProof⟩
  let mut termGoals := #[]
  let mut tacticStates := #[]
  let mut goalConstants := #[]
  let mut exported : SubVerso.Highlighting.Exporting := {}
  let mut boundaryMs := 0
  let mut selectionMs := 0
  let mut goalHighlightMs := 0
  let needsTermGoals := requestedRanges.any (!·.tacticProof)
  for item in result.items do
    if needsTermGoals then
      let termGoalRequests ← collectTermGoalRequests item.info
      unless termGoalRequests.isEmpty do
        let semanticTermGoals ← (Frontend.runCommandElabM do
          liftTermElabM do
            let highlighter ← GoalHighlighter.create item.info
            highlightTermGoals highlighter termGoalRequests)
            parserContext commandStateRef
        for termGoal in semanticTermGoals do
          goalConstants := goalConstants ++ termGoal.goals.semanticConstants
          let (goalKeys, nextExported) := exportGoals termGoal.goals exported
          exported := nextExported
          termGoals := termGoals.push {
            startPos := termGoal.startPos
            endPos := termGoal.endPos
            goals := goalKeys
          }
    let some itemRange := itemRange? item | continue
    for requestedRange in requestedRanges do
      let some range := intersection? itemRange requestedRange | continue
      unless range.tacticProof do continue
      let boundaryStart ← if timings then IO.monoMsNow else pure 0
      let boundaries ← goalSelectionBoundaries contents fileMap item.info range
      if timings then boundaryMs := boundaryMs + (← IO.monoMsNow) - boundaryStart
      if boundaries.isEmpty then continue
      let highlighter ← (Frontend.runCommandElabM <| liftTermElabM <|
        GoalHighlighter.create item.info) parserContext commandStateRef
      let mut runStart := boundaries[0]!
      let mut previousKey : Option String := none
      let mut previousGoals : Array Nat := #[]
      for pos in boundaries do
        let selectionStart ← if timings then IO.monoMsNow else pure 0
        let results := selectedGoals fileMap item.info pos
        if timings then selectionMs := selectionMs + (← IO.monoMsNow) - selectionStart
        let key := if results.isEmpty then none else some (selectedGoalsKey results)
        if key != previousKey then
          if previousKey.isSome then
            tacticStates := tacticStates.push {
              startPos := runStart.byteIdx
              endPos := pos.byteIdx
              goals := previousGoals
            }
          runStart := pos
          previousKey := key
          if results.isEmpty then
            previousGoals := #[]
          else
            let goalHighlightStart ← if timings then IO.monoMsNow else pure 0
            let goals ← (Frontend.runCommandElabM <| liftTermElabM <|
              highlightResults highlighter results) parserContext commandStateRef
            if timings then
              goalHighlightMs := goalHighlightMs + (← IO.monoMsNow) - goalHighlightStart
            goalConstants := goalConstants ++ goals.semanticConstants
            let (goalKeys, nextExported) := exportGoals goals exported
            exported := nextExported
            previousGoals := goalKeys
      if previousKey.isSome then
        tacticStates := tacticStates.push {
          startPos := runStart.byteIdx
          endPos := range.endPos.byteIdx + 1
          goals := previousGoals
        }
  let referencesStart ← IO.monoMsNow
  let referenceLocations := moduleReferences.foldl (init := #[]) fun references ident info =>
    match ident with
    | .fvar .. => references
    | .const referenceModule name =>
      let referenceModule := if referenceModule == "[anonymous]" then moduleName.toString
        else referenceModule
      let add (references : Array (String × String × Lean.Lsp.Range))
          (reference : Lean.Server.Reference) :=
        references.push (referenceModule, name, reference.range)
      let references := info.definition.map (add references) |>.getD references
      info.usages.foldl add references
  let references ← (Frontend.runCommandElabM do
    let sourceReferences ← referenceLocations.mapM fun (moduleName, name, range) => do
      let targetRange ← Lean.findDeclarationRanges? name.toName
      return {
        moduleName
        name
        range := some range
        targetStartLine := targetRange.map (·.range.pos.line)
        targetEndLine := targetRange.map (·.range.endPos.line)
      }
    let uniqueGoalConstants := goalConstants.foldl (init := #[]) fun names name =>
      if names.contains name then names else names.push name
    let goalReferences ← uniqueGoalConstants.mapM fun name => do
      let referenceModule ← Lean.findModuleOf? name
      let targetRange ← Lean.findDeclarationRanges? name
      return {
        moduleName := referenceModule.getD moduleName |>.toString
        name := name.toString
        range := none
        targetStartLine := targetRange.map (·.range.pos.line)
        targetEndLine := targetRange.map (·.range.endPos.line)
      }
    return sourceReferences ++ goalReferences) parserContext commandStateRef
  let referencesMs := moduleReferencesMs + ((← IO.monoMsNow) - referencesStart)
  let mut messages := #[]
  for item in result.items do
    let some startPos := item.commandSyntax.getPos? (canonicalOnly := true) | continue
    let some endPos := item.commandSyntax.getTrailingTailPos? (canonicalOnly := true) | continue
    for message in Compat.messageLogArray item.messages do
      let text := (← message.data.toString).trimAscii.toString
      unless text.isEmpty do
        messages := messages.push {
          startPos := startPos.byteIdx
          endPos := endPos.byteIdx
          severity := message.severity.toString
          text
        }
  let output : ProofStates := {
    termGoals
    tacticStates
    data := exported.toExport
    highlighted := highlightedModule
    commands
    items := selectedItems
    references
    messages
  }
  if timings then
    let totalMs := (← IO.monoMsNow) - totalStart
    IO.eprintln s!"blueprint-source-timing: process={processMs}ms source={sourceHighlightMs}ms"
    IO.eprintln s!"blueprint-source-timing: boundaries={boundaryMs}ms selection={selectionMs}ms"
    IO.eprintln s!"blueprint-source-timing: goals={goalHighlightMs}ms references={referencesMs}ms"
    IO.eprintln s!"blueprint-source-timing: total-before-json={totalMs}ms"
  return output

public unsafe def main (arguments : List String) : IO UInt32 := do
  let moduleName :: nameSpec :: rest := arguments
    | throw <| IO.userError "expected a module name and declaration names"
  let timings := rest.contains "--timings"
  let states ← extract moduleName.toName (parseNames nameSpec) timings
  IO.println (toJson states).compress
  return 0
