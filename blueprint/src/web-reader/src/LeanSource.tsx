import {
  memo, useCallback, useEffect, useLayoutEffect, useRef, useState,
} from 'react';
import { createPortal, flushSync } from 'react-dom';
import { stateAtOffset } from './proofState';
import type {
  LeanMessage, LeanReference, LeanSource as LeanSourceData, LeanState,
} from './types';

function ProofState({ source, state }: { source: LeanSourceData; state: LeanState }) {
  if (!state.goals.length) return <div className="lean-no-goals">No goals</div>;
  return <div className="lean-goal-pane-content">
    {state.goals.map(id => source.goals[id]).filter(Boolean).map((goal, index) =>
      <div key={`${state.start}-${index}`} dangerouslySetInnerHTML={{ __html: goal }} />)}
  </div>;
}

function LeanOutput({ message }: { message: LeanMessage }) {
  const axiomAudit = message.text.includes('depends on axioms:');
  const acceptedAxioms = axiomAudit
    && /\[propext,\s*Classical\.choice,\s*Quot\.sound\]\s*$/.test(message.text);
  const status = axiomAudit ? acceptedAxioms ? ' is-passed' : ' is-failed' : '';
  return <div className={`lean-output${status}`}>
    <pre><code>{message.text}</code></pre>
  </div>;
}

type ActivePane =
  | { kind: 'state'; value: LeanState }
  | { kind: 'message'; value: LeanMessage }
  | null;

const EXPANDABLE_LINE_COUNT = 16;
const MOBILE_SOURCE_QUERY = '(max-width: 850px), (hover: none), (pointer: coarse)';

function paneAtOffset(source: LeanSourceData, offset: number): ActivePane {
  const message = source.messages?.find(value => value.start <= offset && offset < value.end);
  if (message) return { kind: 'message', value: message };
  const state = stateAtOffset(source.states, offset);
  return state ? { kind: 'state', value: state } : null;
}

function DocText({ value }: { value: string }) {
  return value.split(/(`[^`]+`)/g).map((part, index) => part.startsWith('`') && part.endsWith('`')
    ? <code key={index}>{part.slice(1, -1)}</code>
    : part);
}

function TooltipDocs({ value }: { value: string }) {
  const ref = useRef<HTMLParagraphElement>(null);
  const [clipped, setClipped] = useState(false);
  useLayoutEffect(() => {
    const element = ref.current;
    setClipped(Boolean(element && element.scrollHeight > element.clientHeight));
  }, [value]);
  return <p ref={ref} className={clipped ? 'is-clipped' : undefined}>
    <DocText value={value} />
  </p>;
}

function TooltipSignature({ value }: { value: string }) {
  const ref = useRef<HTMLPreElement>(null);
  const [clipped, setClipped] = useState(false);
  useLayoutEffect(() => {
    const element = ref.current;
    setClipped(Boolean(element && element.scrollHeight > element.clientHeight));
  }, [value]);
  return <pre ref={ref} className={clipped ? 'is-clipped' : undefined}>{value}</pre>;
}

function tooltipPosition(
  anchor: { left: number; right: number; top: number; bottom: number },
  pane: { left: number; right: number } | null,
): React.CSSProperties {
  const leftEdge = Math.max(14, (pane?.left ?? 6) + 8);
  const rightEdge = Math.min(innerWidth - 14, (pane?.right ?? innerWidth - 6) - 8);
  const width = Math.min(560, rightEdge - leftEdge);
  const preferredLeft = anchor.right - width + 24;
  const left = Math.max(leftEdge, Math.min(preferredLeft, rightEdge - width));
  if (anchor.bottom + 308 < innerHeight) {
    return { left, top: anchor.bottom + 8, width };
  }
  return { left, top: anchor.top - 8, transform: 'translateY(-100%)', width };
}

function sourceShortcut(): string {
  return /Mac|iPhone|iPad/.test(navigator.platform) ? '⌘-click' : 'Ctrl-click';
}

function opensSource(event: React.MouseEvent): boolean {
  return event.metaKey || event.ctrlKey;
}

function wrapLines(code: HTMLElement, messages: LeanMessage[]): void {
  if (code.querySelector('.lean-code-line')) return;
  const sourceMarker = code.querySelector<HTMLElement>('.lean-declaration-start');
  const walker = document.createTreeWalker(code, NodeFilter.SHOW_TEXT);
  const nodes: Text[] = [];
  while (walker.nextNode()) nodes.push(walker.currentNode as Text);
  if (!nodes.length) return;
  const ranges: Array<[Text, number, Text, number]> = [];
  let startNode = nodes[0];
  let startOffset = 0;
  for (const node of nodes) {
    for (let index = 0; index < node.data.length; index += 1) {
      if (node.data[index] !== '\n') continue;
      ranges.push([startNode, startOffset, node, index]);
      startNode = node;
      startOffset = index + 1;
    }
  }
  const last = nodes.at(-1)!;
  ranges.push([startNode, startOffset, last, last.data.length]);
  const fragment = document.createDocumentFragment();
  for (const points of ranges) {
    const range = document.createRange();
    range.setStart(points[0], points[1]);
    range.setEnd(points[2], points[3]);
    const line = document.createElement('span');
    line.className = 'lean-code-line';
    line.append(range.cloneContents());
    if (!line.textContent) line.append('\u200b');
    fragment.append(line);
  }
  if (sourceMarker && !fragment.querySelector('.lean-declaration-start')) {
    fragment.firstElementChild?.prepend(sourceMarker.cloneNode(true));
  }
  code.replaceChildren(fragment);
  let sourceOffset: number | null = null;
  for (const line of code.querySelectorAll<HTMLElement>('.lean-code-line')) {
    const lineMarker = line.querySelector<HTMLElement>('.lean-declaration-start');
    if (lineMarker) sourceOffset = Number(lineMarker.dataset.sourceStart);
    const lineText = line.textContent!.replaceAll('\u200b', '');
    const lineEnd: number | null = sourceOffset === null ? null : sourceOffset + lineText.length;
    if (sourceOffset !== null) line.dataset.sourceStart = String(sourceOffset);
    const diagnostic = lineText && lineEnd !== null && messages.find(
      message => message.start < lineEnd && sourceOffset! < message.end,
    );
    if (diagnostic) line.classList.add('has-diagnostic', `is-${diagnostic.severity}`);
    if (lineEnd !== null) sourceOffset = lineEnd + 1;
  }
}

const SourceCode = memo(function SourceCode({ html, codeRef, messages }: {
  html: string;
  codeRef: React.RefObject<HTMLElement | null>;
  messages?: LeanMessage[];
}) {
  useLayoutEffect(() => {
    if (codeRef.current) {
      codeRef.current.setAttribute('writingsuggestions', 'false');
      wrapLines(codeRef.current, messages ?? []);
    }
  }, [codeRef, html, messages]);
  return <code ref={codeRef} contentEditable suppressContentEditableWarning spellCheck={false}
    autoCorrect="off" autoCapitalize="off"
    tabIndex={0} role="textbox" aria-readonly="true"
    dangerouslySetInnerHTML={{ __html: html }} />;
});

function sourceOffsetAtPosition(code: HTMLElement, node: Node, offset: number): number | null {
  const targetLine = containingLine(node);
  const sourceStart = Number((targetLine as HTMLElement | null)?.dataset.sourceStart);
  if (!targetLine || !Number.isFinite(sourceStart) || !code.contains(node)) return null;
  const range = document.createRange();
  try {
    range.setStart(targetLine, 0);
    range.setEnd(node, offset);
  } catch { return null; }
  return sourceStart + range.toString().replaceAll('\u200b', '').length;
}

function selectionOffset(code: HTMLElement): number | null {
  const selection = window.getSelection();
  if (!selection?.isCollapsed || !selection.anchorNode) return null;
  return sourceOffsetAtPosition(code, selection.anchorNode, selection.anchorOffset);
}

type TextPosition = { node: Node; offset: number };

function positionOffset(code: HTMLElement, position: TextPosition): number | null {
  return sourceOffsetAtPosition(code, position.node, position.offset);
}

function positionAtPoint(code: HTMLElement, x: number, y: number): TextPosition | null {
  const documentWithCaret = document as Document & {
    caretPositionFromPoint?: (x: number, y: number) => { offsetNode: Node; offset: number } | null;
    caretRangeFromPoint?: (x: number, y: number) => Range | null;
  };
  const position = documentWithCaret.caretPositionFromPoint?.(x, y);
  if (position && code.contains(position.offsetNode)) {
    return { node: position.offsetNode, offset: position.offset };
  }
  const range = documentWithCaret.caretRangeFromPoint?.(x, y);
  if (range && code.contains(range.startContainer)) {
    return { node: range.startContainer, offset: range.startOffset };
  }
  return null;
}

function containingLine(node: Node | null): Element | null {
  const element = node?.nodeType === Node.ELEMENT_NODE ? node as Element : node?.parentElement;
  return element?.closest('.lean-code-line') ?? null;
}

export default function LeanSource({ source }: { source: LeanSourceData }) {
  const codeRef = useRef<HTMLElement>(null);
  const rootRef = useRef<HTMLElement>(null);
  const lastPaneRef = useRef<Exclude<ActivePane, null> | null>(null);
  const lockedRef = useRef(false);
  const referenceTokenRef = useRef<HTMLElement | null>(null);
  const referenceClearRef = useRef<number | undefined>(undefined);
  const hoverClearRef = useRef<number | undefined>(undefined);
  const [locked, setLocked] = useState(false);
  const [expanded, setExpanded] = useState(false);
  const [caretPane, setCaretPane] = useState<ActivePane>(null);
  const [hoverPane, setHoverPane] = useState<ActivePane>(null);
  const [reference, setReference] = useState<{
    value: LeanReference;
    anchor: { left: number; right: number; top: number; bottom: number };
    pane: { left: number; right: number } | null;
  }>();
  const mobileSource = matchMedia(MOBILE_SOURCE_QUERY).matches;
  const active = locked ? caretPane : hoverPane;
  if (active) lastPaneRef.current = active;
  const renderedPane = active ?? lastPaneRef.current;
  const supportsPane = source.states.length > 0 || Boolean(source.messages?.length);
  const isExpandable = source.html.split('\n').length > EXPANDABLE_LINE_COUNT;
  const showExpand = isExpandable || expanded;

  const cancelReferenceClear = useCallback(() => {
    if (referenceClearRef.current === undefined) return;
    window.clearTimeout(referenceClearRef.current);
    referenceClearRef.current = undefined;
  }, []);

  const clearReference = useCallback(() => {
    cancelReferenceClear();
    referenceTokenRef.current?.classList.remove('is-reference-hover');
    referenceTokenRef.current = null;
    setReference(undefined);
  }, [cancelReferenceClear]);

  const deferReferenceClear = useCallback(() => {
    if (referenceClearRef.current !== undefined) return;
    referenceClearRef.current = window.setTimeout(clearReference, 80);
  }, [clearReference]);

  const markLine = useCallback((line: Element | null) => {
    rootRef.current?.querySelectorAll('.lean-code-line.is-current')
      .forEach(current => current.classList.remove('is-current'));
    line?.classList.add('is-current');
  }, []);

  const cancelHoverClear = useCallback(() => {
    if (hoverClearRef.current === undefined) return;
    window.clearTimeout(hoverClearRef.current);
    hoverClearRef.current = undefined;
  }, []);

  const deferHoverClear = useCallback(() => {
    if (hoverClearRef.current !== undefined) return;
    hoverClearRef.current = window.setTimeout(() => {
      hoverClearRef.current = undefined;
      setHoverPane(null);
    }, 80);
  }, []);

  const updateCaret = useCallback(() => {
    const code = codeRef.current;
    if (!code) return;
    const offset = selectionOffset(code);
    const next = offset === null ? null : paneAtOffset(source, offset);
    setCaretPane(next);
    const anchor = window.getSelection()?.anchorNode;
    markLine(containingLine(anchor ?? null));
  }, [markLine, source]);

  useEffect(() => {
    const onSelection = () => {
      if (lockedRef.current && codeRef.current?.contains(window.getSelection()?.anchorNode ?? null)) {
        updateCaret();
      }
    };
    const unlock = (event: PointerEvent) => {
      if (rootRef.current?.contains(event.target as Node)) return;
      lockedRef.current = false;
      setLocked(false);
      setCaretPane(null);
      cancelHoverClear();
      setHoverPane(null);
      clearReference();
      markLine(null);
    };
    document.addEventListener('selectionchange', onSelection);
    document.addEventListener('pointerdown', unlock);
    window.addEventListener('scroll', clearReference, true);
    return () => {
      document.removeEventListener('selectionchange', onSelection);
      document.removeEventListener('pointerdown', unlock);
      window.removeEventListener('scroll', clearReference, true);
      if (referenceClearRef.current !== undefined) {
        window.clearTimeout(referenceClearRef.current);
      }
      if (hoverClearRef.current !== undefined) window.clearTimeout(hoverClearRef.current);
    };
  }, [cancelHoverClear, clearReference, markLine, updateCaret]);

  const hoverReference = (event: React.MouseEvent) => {
    const token = (event.target as Element).closest<HTMLElement>('[data-lean-reference]');
    const key = token?.dataset.leanReference;
    const value = key && source.references[key];
    if (value && token) {
      cancelReferenceClear();
      if (referenceTokenRef.current === token) return;
      referenceTokenRef.current?.classList.remove('is-reference-hover');
      const bounds = token.getBoundingClientRect();
      const pane = token.closest<HTMLElement>('.lean-goal-pane, pre')?.getBoundingClientRect();
      referenceTokenRef.current = token;
      if (value.url) token.classList.add('is-reference-hover');
      setReference({
        value,
        anchor: {
          left: bounds.left, right: bounds.right, top: bounds.top, bottom: bounds.bottom,
        },
        pane: pane ? { left: pane.left, right: pane.right } : null,
      });
    }
    else deferReferenceClear();
  };

  const previewAtPoint = (event: React.MouseEvent) => {
    hoverReference(event);
    if (lockedRef.current) return;
    const code = codeRef.current;
    const codePane = code?.closest('pre');
    if (!code || !codePane?.contains(event.target as Node)) return;
    const position = code && positionAtPoint(code, event.clientX, event.clientY);
    // Scrollbars and the empty area after a short line have no caret position. They are still
    // part of the source pane, so keep the last preview instead of collapsing the goal pane and
    // changing the geometry underneath the pointer.
    if (!position) return;
    const offset = positionOffset(code, position);
    const next = offset === null ? null : paneAtOffset(source, offset);
    if (next) {
      cancelHoverClear();
      setHoverPane(next);
    }
    else deferHoverClear();
    markLine(position ? containingLine(position.node) : null);
  };

  return <section ref={rootRef}
    className={`lean-source${expanded ? ' is-expanded' : ''}${showExpand ? ' can-expand' : ''}`}
    aria-label="Lean source" onClick={event => {
    const token = (event.target as Element).closest<HTMLElement>('[data-lean-reference]');
    const value = token && source.references[token.dataset.leanReference!];
    if (value?.url && mobileSource) {
      event.preventDefault();
      return;
    }
    if (value?.url && opensSource(event)) {
      event.preventDefault();
      window.open(value.url, '_blank', 'noopener,noreferrer');
    }
  }}
    onMouseMove={previewAtPoint} onMouseLeave={() => {
      deferReferenceClear();
      if (!lockedRef.current) {
        deferHoverClear();
        markLine(null);
      }
    }}>
    <header className="lean-source-heading">
      <strong>Lean</strong><code>{source.displayName}</code>
      <a href={source.url} target="_blank" rel="noreferrer">GitHub ↗</a>
    </header>
    <div className={supportsPane
      ? `lean-source-body has-pane${active ? ' has-active-pane' : ''}`
      : 'lean-source-body'}>
      <pre onBeforeInput={event => event.preventDefault()} onClick={event => {
        const token = (event.target as Element).closest<HTMLElement>('[data-lean-reference]');
        const value = token && source.references[token.dataset.leanReference!];
        if (value?.url && !mobileSource && opensSource(event)) return;
        lockedRef.current = true;
        updateCaret();
        setLocked(true);
      }} onKeyUp={updateCaret}>
        <SourceCode html={source.html} codeRef={codeRef} messages={source.messages} />
      </pre>
      <aside className={active ? 'lean-goal-pane' : 'lean-goal-pane is-empty'}
        aria-hidden={!active}>
        <div className="lean-goal-pane-sticky">
          {renderedPane?.kind === 'state'
            && <ProofState source={source} state={renderedPane.value} />}
          {renderedPane?.kind === 'message' && <LeanOutput message={renderedPane.value} />}
        </div>
      </aside>
    </div>
    {showExpand && <button className="lean-source-expand" type="button"
      aria-expanded={expanded} onClick={() => {
        const nextExpanded = !expanded;
        flushSync(() => setExpanded(nextExpanded));
        if (!nextExpanded && rootRef.current) {
          const root = rootRef.current as HTMLElement & { scrollIntoViewIfNeeded?: () => void };
          if (root.scrollIntoViewIfNeeded) root.scrollIntoViewIfNeeded();
          else root.scrollIntoView({ block: 'nearest', inline: 'nearest' });
        }
      }}>
      {expanded ? 'Collapse' : 'Expand'}
    </button>}
    {reference && createPortal(<div className="lean-tooltip"
      style={tooltipPosition(reference.anchor, reference.pane)}>
      {reference.value.signature
        ? <TooltipSignature value={reference.value.signature} />
        : <div className="lean-tooltip-name">{reference.value.name}</div>}
      {reference.value.docs && <TooltipDocs value={reference.value.docs} />}
      {reference.value.url && !mobileSource && <div className="lean-tooltip-shortcut">
        <span>{sourceShortcut()}</span> to view definition on GitHub
      </div>}
    </div>, document.body)}
  </section>;
}
