#!/usr/bin/env node

import { execFile, execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { gzipSync } from 'node:zlib';
import { mkdir, readFile, rename, rm, stat, writeFile } from 'node:fs/promises';
import { existsSync, readFileSync } from 'node:fs';
import { promisify } from 'node:util';
import path from 'node:path';
import process from 'node:process';
import { embedBlueprintReader } from './embed-blueprint-reader.mjs';

const execFileAsync = promisify(execFile);
const root = path.resolve(import.meta.dirname, '../../../..');
const nodeDataPath = path.join(root, '.lake/build/blueprint/nodes.json');
const webDataPath = path.join(root, 'blueprint/web/data.json');
const output = path.join(root, 'blueprint/web');
const legacyBundlePath = path.join(output, 'source-bundles.json');
const cacheRoot = path.join(root, '.lake/build/blueprint-source');
const manifest = JSON.parse(readFileSync(path.join(root, 'lake-manifest.json'), 'utf8'));
const packages = new Map(manifest.packages.map(packageData => [packageData.name, packageData]));
const htmlEscape = value => value.replaceAll('&', '&amp;').replaceAll('<', '&lt;')
  .replaceAll('>', '&gt;').replaceAll('"', '&quot;').replaceAll("'", '&#39;');

const standaloneDeclarations = [
  {
    key: 'cut',
    title: "Conway's cut formulation",
    description: "Conway’s refinement conjecture using the surreal numbers from CombinatorialGames.",
    module: 'ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinement',
    name: 'ConwayRefinement.Standalone.Oz.ConwayConjecture',
    source: 'ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinement.lean',
    proofModule: 'ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinementProof',
    proofName: 'ConwayRefinement.Standalone.Oz.ConwayConjecture.proof',
    proofSource: 'ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinementProof.lean',
    standalone: true,
  },
  {
    key: 'inline',
    title: "Conway’s refinement conjecture from first principles",
    description: 'A Mathlib-only statement built from an inlined construction of surreal numbers.',
    module: 'ConwayRefinement.Standalone.Mathlib.InlineConwayRefinement',
    name: 'ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture',
    source: 'ConwayRefinement/Standalone/Mathlib/InlineConwayRefinement.lean',
    proofModule: 'ConwayRefinement.Standalone.Mathlib.InlineConwayRefinementProof',
    proofName: 'ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture.proof',
    proofSource: 'ConwayRefinement/Standalone/Mathlib/InlineConwayRefinementProof.lean',
    standalone: true,
  },
  {
    key: 'hahn',
    title: 'Refinement over saturated exponent groups',
    description: 'The Mathlib-only generalised-power-series statement.',
    module: 'ConwayRefinement.Standalone.Mathlib.HahnIntegerPartRefinement',
    name: 'ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement',
    source: 'ConwayRefinement/Standalone/Mathlib/HahnIntegerPartRefinement.lean',
    proofModule: 'ConwayRefinement.Standalone.Mathlib.HahnIntegerPartRefinementProof',
    proofName: 'ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement.proof',
    proofSource: 'ConwayRefinement/Standalone/Mathlib/HahnIntegerPartRefinementProof.lean',
    standalone: true,
  },
];

const standaloneFiles = standaloneDeclarations.flatMap(declaration => [
  {
    key: declaration.key,
    module: declaration.module,
    name: declaration.name,
    source: declaration.source,
    standalone: true,
    standalonePart: 'statement',
    extractAll: true,
  },
  {
    key: declaration.key,
    module: declaration.proofModule,
    name: declaration.proofName,
    source: declaration.proofSource,
    standalone: true,
    standalonePart: 'proof',
    extractAll: true,
  },
]);

function modulePath(module, extension) {
  return `${module.replaceAll('.', '/')}.${extension}`;
}

function packageRevision(name) {
  const packageData = packages.get(name);
  if (!packageData) throw new Error(`missing package ${name} in lake-manifest.json`);
  return packageData.rev;
}

function targetUrl(reference, sourceRevision, leanRevision) {
  const module = reference.moduleName;
  let base;
  let source;
  if (module.startsWith('ConwayRefinement')) {
    base = `https://github.com/gaearon/conway-refinement/blob/${sourceRevision}`;
    source = modulePath(module, 'lean');
  } else if (module.startsWith('Mathlib')) {
    base = `https://github.com/leanprover-community/mathlib4/blob/${packageRevision('mathlib')}`;
    source = modulePath(module, 'lean');
  } else if (module.startsWith('CombinatorialGames')) {
    base = 'https://github.com/vihdzp/combinatorial-games/blob/'
      + packageRevision('CombinatorialGames');
    source = modulePath(module, 'lean');
  } else if (['Init', 'Lean', 'Std'].some(prefix => module.startsWith(prefix))) {
    base = `https://github.com/leanprover/lean4/blob/${leanRevision}`;
    source = `src/lean/${modulePath(module, 'lean')}`;
  } else {
    return '';
  }
  const start = reference.targetStartLine;
  const end = reference.targetEndLine;
  const anchor = start == null ? '' : end !== start ? `#L${start}-L${end}` : `#L${start}`;
  return `${base}/${source}${anchor}`;
}

function byteOffsets(source) {
  const bytes = Buffer.byteLength(source);
  const offsets = new Array(bytes + 1);
  let byteOffset = 0;
  let stringOffset = 0;
  for (const character of source) {
    const width = Buffer.byteLength(character);
    for (let interior = 0; interior < width; interior += 1) {
      offsets[byteOffset + interior] = stringOffset;
    }
    byteOffset += width;
    stringOffset += character.length;
  }
  offsets[byteOffset] = source.length;
  return offsets;
}

function lineStarts(source) {
  const starts = [0];
  for (let index = 0; index < source.length; index += 1) {
    if (source[index] === '\n') starts.push(index + 1);
  }
  return starts;
}

function lspOffset(starts, position) {
  return starts[position.line] + position.character;
}

function tokenKind(token) {
  let kind = token.kind ?? 'unknown';
  let diff = null;
  while (typeof kind === 'object' && kind.diff) {
    diff = kind.diff.status;
    kind = kind.diff.kind;
  }
  if (typeof kind === 'string') return [kind, {}, diff];
  const [name, details] = Object.entries(kind)[0];
  return [name, details ?? {}, diff];
}

function diffClass(status) {
  if (['wasChanged', 'wasInserted', 'willInsert'].includes(status)) {
    return ' lean-diff-inserted';
  }
  if (['willChange', 'willDelete', 'wasDeleted'].includes(status)) {
    return ' lean-diff-removed';
  }
  return '';
}

function plainCode(data, codeId) {
  const value = data.code[codeId];
  if (value.text) return value.text.str;
  if (value.token) return data.tokens[value.token.tok].content;
  if (value.seq) return value.seq.highlights.map(child => plainCode(data, child)).join('');
  if (value.tactics) return plainCode(data, value.tactics.content);
  if (value.span) return plainCode(data, value.span.content);
  throw new Error(`unknown highlighted-code node ${JSON.stringify(value)}`);
}

function codeLeaves(data, codeId) {
  const value = data.code[codeId];
  if (value.text) return [[value.text.str, '', {}, '']];
  if (value.token) {
    const token = data.tokens[value.token.tok];
    return [[token.content, ...tokenKind(token)]];
  }
  if (value.seq) return value.seq.highlights.flatMap(child => codeLeaves(data, child));
  if (value.tactics) return codeLeaves(data, value.tactics.content);
  if (value.span) return codeLeaves(data, value.span.content);
  throw new Error(`unknown highlighted-code node ${JSON.stringify(value)}`);
}

function referenceKey(reference) {
  return `${reference.module ?? ''}␟${reference.name}`;
}

function addReference(references, target, name, details) {
  const reference = {
    name: target?.name ?? name,
    module: target?.module ?? '',
    signature: details.signature ?? '',
    docs: details.docs ?? '',
    url: target?.url ?? '',
  };
  const key = referenceKey(reference);
  const previous = references[key];
  references[key] = previous ? {
    ...previous,
    signature: previous.signature || reference.signature,
    docs: previous.docs || reference.docs,
    url: previous.url || reference.url,
  } : reference;
  return [key, references[key]];
}

class Renderer {
  constructor(data, sourceStart, cut, proofStart, targets, knownTargets, definition) {
    this.data = data;
    this.position = sourceStart;
    this.cut = cut;
    this.proofStart = proofStart;
    this.targets = targets;
    this.knownTargets = knownTargets;
    this.definition = definition;
    this.references = {};
  }

  render(codeId) {
    const value = this.data.code[codeId];
    if (value.text) return this.renderText(value.text.str);
    if (value.token) return this.renderToken(this.data.tokens[value.token.tok]);
    if (value.seq) return value.seq.highlights.map(child => this.render(child)).join('');
    if (value.tactics) {
      const start = this.position;
      const content = this.render(value.tactics.content);
      if (start < this.proofStart) return content;
      return `<span class="lean-tactic">${content}</span>`;
    }
    if (value.span) return this.render(value.span.content);
    throw new Error(`unknown highlighted-code node ${JSON.stringify(value)}`);
  }

  visible(value) {
    let start = this.position;
    this.position += value.length;
    const end = this.position;
    if (end <= this.cut) return ['', start, end];
    if (start < this.cut) {
      value = value.slice(this.cut - start);
      start = this.cut;
    }
    return [value, start, end];
  }

  renderText(value) {
    return htmlEscape(this.visible(value)[0]);
  }

  renderToken(token) {
    const [value, start, end] = this.visible(token.content);
    if (!value) return '';
    const [kind, details, diff] = tokenKind(token);
    const css = String(kind).replaceAll(/[^a-zA-Z0-9_-]/g, '-') + diffClass(diff);
    const body = htmlEscape(value);
    if (kind !== 'const') return value.split('\n').map(line =>
      `<span class="lean-token lean-${css}">${htmlEscape(line)}</span>`).join('\n');
    const name = (details.name ?? []).map(String).join('.');
    let target = this.targets.get(`${start}:${end}`) ?? this.knownTargets.get(name);
    if (!target && this.definition && this.definition.sourceName === name) {
      target = this.definition;
    }
    const [key, reference] = addReference(this.references, target, name, details);
    const linkClass = reference.url ? ' lean-source-link' : '';
    const attributes = `class="lean-token lean-${css}${linkClass}" `
      + `data-lean-reference="${htmlEscape(key)}"`;
    return reference.url
      ? `<a ${attributes} href="${htmlEscape(reference.url)}" target="_blank" `
        + `rel="noreferrer">${body}</a>`
      : `<span ${attributes}>${body}</span>`;
  }
}

function renderCodeLeaf(text, kind, details, diff, references, knownTargets) {
  const body = htmlEscape(text);
  const diffCss = diffClass(diff);
  const inaccessible = text.includes('✝') ? ' lean-inaccessible-name' : '';
  if (!kind) return diffCss || inaccessible
    ? `<span class="lean-token lean-unknown${diffCss}${inaccessible}">${body}</span>` : body;
  if (kind !== 'const') {
    return `<span class="lean-token lean-${kind}${diffCss}${inaccessible}">${body}</span>`;
  }
  const name = (details.name ?? []).map(String).join('.');
  const target = knownTargets.get(name);
  const [key, reference] = addReference(references, target, name, details);
  const linkClass = reference.url ? ' lean-source-link' : '';
  const attributes = `class="lean-token lean-const${diffCss}${inaccessible}${linkClass}" `
    + `data-lean-reference="${htmlEscape(key)}"`;
  return reference.url
    ? `<a ${attributes} href="${htmlEscape(reference.url)}" target="_blank" `
      + `rel="noreferrer">${body}</a>`
    : `<span ${attributes}>${body}</span>`;
}

function fragmentHtml(data, codeId, references, knownTargets) {
  return codeLeaves(data, codeId).map(leaf =>
    renderCodeLeaf(...leaf, references, knownTargets)).join('');
}

function goalHtml(data, goalId, references, knownTargets) {
  const goal = data.goals[goalId];
  const hypotheses = [...goal.hypotheses].reverse().map(hypothesis => {
    const names = hypothesis.names.map(nameId => {
      const content = data.tokens[nameId].content;
      const inaccessible = content.includes('✝') ? ' is-inaccessible' : '';
      return `<span class="lean-goal-hypothesis-name${inaccessible}">`
        + `${htmlEscape(content)}</span>`;
    }).join(' ');
    const inserted = hypothesis.isInserted ? ' is-inserted' : '';
    const removed = hypothesis.isRemoved ? ' is-removed' : '';
    return '<div class="lean-goal-hypothesis">'
      + `<span class="lean-goal-hypothesis-names${inserted}${removed}">${names}</span> : `
      + '<span class="lean-goal-hypothesis-value">'
      + fragmentHtml(data, hypothesis.typeAndVal, references, knownTargets)
      + '</span></div>';
  }).join('');
  const caseName = goal.name
    ? `<div class="lean-goal-case">case ${htmlEscape(goal.name)}</div>` : '';
  const inserted = goal.isInserted ? ' is-inserted' : '';
  const removed = goal.isRemoved ? ' is-removed' : '';
  return `<div class="lean-goal-state${inserted}${removed}">${caseName}`
    + '<div class="lean-goal-conclusion"><span class="lean-goal-conclusion-content">'
    + htmlEscape(goal.goalPrefix)
    + fragmentHtml(data, goal.conclusion, references, knownTargets)
    + `</span></div>${hypotheses}</div>`;
}

function activeContext(items, declarationIndex) {
  const scopes = [[]];
  for (const [index, item] of items.slice(0, declarationIndex).entries()) {
    const kind = item.kind;
    if (kind.endsWith('.section') || kind.endsWith('.namespace')) scopes.push([]);
    else if (kind.endsWith('.end')) {
      if (scopes.length > 1) scopes.pop();
    } else if (kind.endsWith('.universe') || kind.endsWith('.variable')) {
      scopes.at(-1).push(index);
    }
  }
  return scopes.flat();
}

function moduleTargets(moduleData, moduleName, source, sourceRevision, leanRevision) {
  const starts = lineStarts(source);
  const offsets = byteOffsets(source);
  const targets = new Map();
  const known = new Map();
  for (const item of moduleData.items) {
    const start = offsets[item.sourceStart];
    const end = offsets[item.sourceEnd];
    if (start === undefined || end === undefined) continue;
    const targetStartLine = source.slice(0, start).split('\n').length;
    const targetEndLine = source.slice(0, end).split('\n').length;
    known.set(item.name, {
      module: moduleName,
      name: item.name,
      url: targetUrl({ moduleName, targetStartLine, targetEndLine }, sourceRevision, leanRevision),
    });
  }
  for (const reference of moduleData.references) {
    if (reference.moduleName === '[anonymous]') {
      throw new Error(`unresolved same-module reference ${reference.name}`);
    }
    const target = known.get(reference.name) ?? {
      module: reference.moduleName,
      name: reference.name,
      url: targetUrl(reference, sourceRevision, leanRevision),
    };
    if (reference.range) {
      targets.set(`${lspOffset(starts, reference.range.start)}:`
        + `${lspOffset(starts, reference.range.end)}`, target);
    }
    if (!known.has(reference.name) || target.url) known.set(reference.name, target);
  }
  return [targets, known];
}

function renderNode(node, moduleData, source, sourceRevision, leanRevision) {
  const selected = moduleData.items.find(item => item.name === node.name);
  if (!selected) throw new Error(`Lean exporter did not find ${node.name} in ${node.module}`);
  const offsets = byteOffsets(source);
  const sourceStart = offsets[selected.sourceStart];
  const sourceEnd = offsets[selected.sourceEnd];
  const declarationStart = offsets[selected.declarationStart];
  const bodyStart = offsets[selected.bodyStart];
  const bodyEnd = offsets[selected.bodyEnd];
  const [targets, knownTargets] = moduleTargets(
    moduleData, node.module, source, sourceRevision, leanRevision,
  );
  const line = source.slice(0, declarationStart).split('\n').length;
  const endLine = source.slice(0, sourceEnd).split('\n').length;
  const url = `https://github.com/gaearon/conway-refinement/blob/${sourceRevision}/${node.source}`
    + `#L${line}-L${endLine}`;
  const definition = {
    sourceName: selected.name,
    name: selected.name,
    module: node.module,
    url,
  };
  const data = moduleData.highlighted.data;
  const commandItems = moduleData.highlighted.items.slice(1);
  const item = commandItems[selected.itemIndex];
  const renderer = new Renderer(
    data, sourceStart, declarationStart, bodyStart, targets, knownTargets, definition,
  );
  let rendered = renderer.render(item.code).replace(/\n+$/, '\n');
  rendered = `<span class="lean-declaration-start" data-source-start="${declarationStart}"></span>`
    + rendered;
  const context = [];
  for (const contextIndex of activeContext(commandItems, selected.itemIndex)) {
    const command = moduleData.commands[contextIndex];
    const contextRenderer = new Renderer(
      data, offsets[command.sourceStart], offsets[command.sourceStart], source.length + 1,
      targets, knownTargets,
    );
    context.push(contextRenderer.render(commandItems[contextIndex].code).trim());
    Object.assign(renderer.references, contextRenderer.references);
  }
  if (context.length) rendered = `${context.join('\n')}\n\n${rendered}`;

  const goals = {};
  const states = [];
  if (selected.tacticProof) {
    const used = new Set();
    for (const state of moduleData.tacticStates) {
      if (state.endPos < selected.bodyStart || state.startPos > selected.bodyEnd) continue;
      const goalNames = state.goals.map(goal => `exact-${goal}`);
      goalNames.forEach(name => used.add(name));
      const clippedEnd = Math.min(selected.bodyEnd + 1, state.endPos);
      const end = state.goals.length === 0 && clippedEnd > selected.bodyEnd
        ? Math.min(selected.sourceEnd, clippedEnd + 1)
        : clippedEnd;
      states.push({
        start: offsets[Math.max(selected.bodyStart, state.startPos)],
        end: offsets[end],
        goals: goalNames,
      });
    }
    for (const name of used) {
      goals[name] = goalHtml(
        moduleData.data, name.slice('exact-'.length), renderer.references, knownTargets,
      );
    }
  } else {
    const used = new Set();
    for (const goal of moduleData.termGoals) {
      if (goal.startPos < selected.bodyStart || goal.endPos > selected.bodyEnd) continue;
      const goalNames = goal.goals.map(id => `exact-${id}`);
      goalNames.forEach(name => used.add(name));
      states.push({ start: offsets[goal.startPos], end: offsets[goal.endPos], goals: goalNames });
    }
    for (const name of used) {
      goals[name] = goalHtml(
        moduleData.data, name.slice('exact-'.length), renderer.references, knownTargets,
      );
    }
  }
  states.sort((left, right) => left.start - right.start || left.end - right.end);
  return {
    name: node.name,
    displayName: selected.displayName,
    line,
    endLine,
    url,
    html: rendered,
    goals,
    states,
    references: renderer.references,
    leanSource: {
      name: node.name,
      displayName: selected.displayName,
      line,
      endLine,
      url,
      html: rendered,
    },
  };
}

function renderStandaloneFile(node, moduleData, source, sourceRevision, leanRevision) {
  const offsets = byteOffsets(source);
  const [targets, knownTargets] = moduleTargets(
    moduleData, node.module, source, sourceRevision, leanRevision,
  );
  const references = {};
  const header = source.match(/^\/-[\s\S]*?-\//);
  const headerEnd = header?.[0].length ?? 0;
  const displayStart = headerEnd
    + (source.slice(headerEnd).match(/^\s*/)?.[0].length ?? 0);
  const headerRenderer = new Renderer(
    moduleData.highlighted.data, 0, displayStart, source.length + 1,
    targets, knownTargets, undefined,
  );
  let rendered = headerRenderer.render(moduleData.highlighted.items[0].code);
  Object.assign(references, headerRenderer.references);
  let previous = plainCode(
    moduleData.highlighted.data, moduleData.highlighted.items[0].code,
  ).length;
  for (let index = 0; index < moduleData.commands.length; index += 1) {
    const command = moduleData.commands[index];
    const item = moduleData.highlighted.items[index + 1];
    const start = offsets[command.sourceStart];
    const end = offsets[command.sourceEnd];
    if (start === undefined || end === undefined || start < previous || end < start) {
      throw new Error(`stale source positions while rendering ${node.module}`);
    }
    rendered += htmlEscape(source.slice(previous, start));
    const renderer = new Renderer(
      moduleData.highlighted.data, start, start, source.length + 1,
      targets, knownTargets, undefined,
    );
    rendered += renderer.render(item.code);
    Object.assign(references, renderer.references);
    previous = end;
  }
  rendered += htmlEscape(source.slice(previous));
  rendered = `<span class="lean-declaration-start" data-source-start="${displayStart}"></span>`
    + rendered;
  const goals = {};
  const states = [];
  const used = new Set();
  for (const state of moduleData.tacticStates) {
    const goalNames = state.goals.map(goal => `exact-${goal}`);
    goalNames.forEach(name => used.add(name));
    states.push({
      start: offsets[state.startPos],
      end: offsets[state.endPos],
      goals: goalNames,
    });
  }
  for (const goal of moduleData.termGoals) {
    const goalNames = goal.goals.map(id => `exact-${id}`);
    goalNames.forEach(name => used.add(name));
    states.push({ start: offsets[goal.startPos], end: offsets[goal.endPos], goals: goalNames });
  }
  for (const name of used) {
    goals[name] = goalHtml(
      moduleData.data, name.slice('exact-'.length), references, knownTargets,
    );
  }
  states.sort((left, right) => left.start - right.start || left.end - right.end);
  const messages = renderMessages(moduleData, offsets);
  const endLine = source.split('\n').length;
  return {
    name: node.name,
    displayName: path.basename(node.source, '.lean'),
    line: 1,
    endLine,
    url: `https://github.com/gaearon/conway-refinement/blob/${sourceRevision}/${node.source}`
      + `#L1-L${endLine}`,
    html: rendered,
    goals,
    states,
    references,
    messages,
  };
}

function renderStandaloneProof(
  node, moduleData, source, sourceRevision, leanRevision, renderedNode,
) {
  const selected = moduleData.items.find(item => item.name === node.name);
  if (!selected) throw new Error(`Lean exporter did not find ${node.name} in ${node.module}`);
  const offsets = byteOffsets(source);
  const commandItems = moduleData.highlighted.items.slice(1);
  const printIndex = moduleData.commands.findIndex(command => {
    const start = offsets[command.sourceStart];
    const end = offsets[command.sourceEnd];
    return source.slice(start, end).trimStart().startsWith('#print axioms');
  });
  if (printIndex < selected.itemIndex) {
    throw new Error(`cannot find #print axioms after ${node.name} in ${node.module}`);
  }
  const [targets, knownTargets] = moduleTargets(
    moduleData, node.module, source, sourceRevision, leanRevision,
  );
  const references = { ...renderedNode.references };
  const displayStart = offsets[selected.declarationStart];
  const displayEnd = offsets[moduleData.commands[printIndex].sourceEnd];
  const definition = {
    sourceName: selected.name,
    name: selected.name,
    module: node.module,
    url: renderedNode.url,
  };
  const declarationRenderer = new Renderer(
    moduleData.highlighted.data, offsets[selected.sourceStart], displayStart,
    offsets[selected.bodyStart], targets, knownTargets, definition,
  );
  let html = declarationRenderer.render(commandItems[selected.itemIndex].code);
  Object.assign(references, declarationRenderer.references);
  const printCommand = moduleData.commands[printIndex];
  const printStart = offsets[printCommand.sourceStart];
  html += htmlEscape(source.slice(offsets[selected.sourceEnd], printStart));
  const printRenderer = new Renderer(
    moduleData.highlighted.data, printStart, printStart, source.length + 1,
    targets, knownTargets, undefined,
  );
  html += printRenderer.render(commandItems[printIndex].code);
  Object.assign(references, printRenderer.references);
  html = `${html.replace(/\s+$/, '')}\n`;
  html = `<span class="lean-declaration-start" data-source-start="${displayStart}"></span>${html}`;
  const line = source.slice(0, displayStart).split('\n').length;
  const endLine = source.slice(0, displayEnd).split('\n').length;
  return {
    ...renderedNode.leanSource,
    displayName: path.basename(node.source, '.lean'),
    line,
    endLine,
    url: `https://github.com/gaearon/conway-refinement/blob/${sourceRevision}/${node.source}`
      + `#L${line}-L${endLine}`,
    html,
    goals: renderedNode.goals,
    states: renderedNode.states,
    references,
    messages: renderMessages(moduleData, offsets, node.name),
  };
}

function renderMessages(moduleData, offsets, declarationName) {
  const messages = [];
  const messageKeys = new Set();
  for (const message of moduleData.messages) {
    if (declarationName && (!message.text.includes(declarationName)
      || !message.text.includes('depends on axioms'))) continue;
    const renderedMessage = {
      start: offsets[message.startPos],
      end: offsets[message.endPos],
      severity: message.severity,
      text: message.text,
    };
    const key = `${renderedMessage.severity}\u241f${renderedMessage.text}`;
    if (messageKeys.has(key)) continue;
    messageKeys.add(key);
    messages.push(renderedMessage);
  }
  return messages;
}

async function extractModules(nodes, consume) {
  const modules = new Map();
  for (const node of nodes) {
    const list = modules.get(node.module) ?? [];
    list.push(node);
    modules.set(node.module, list);
  }
  const entries = [...modules.entries()];
  execFileSync('lake', ['-q', 'build', ...entries.map(([module]) => module)], {
    cwd: root, stdio: 'inherit',
  });
  execFileSync('lake', ['-q', 'build', 'blueprint-proof-states'], { cwd: root, stdio: 'inherit' });
  const extractor = path.join(root, '.lake/build/bin/blueprint-proof-states');
  const extractorHash = createHash('sha256');
  extractorHash.update(await readFile(extractor));
  const leanPath = execFileSync('lake', ['env', 'printenv', 'LEAN_PATH'], {
    cwd: root, encoding: 'utf8',
  }).trim();
  await mkdir(cacheRoot, { recursive: true });
  const jobs = [];
  for (const [order, [module, moduleNodes]] of entries.entries()) {
    const names = moduleNodes.map(node => node.extractAll ? '__all__' : node.name)
      .sort().join(',');
    const relative = modulePath(module, 'json');
    const cache = path.join(cacheRoot, relative);
    const stamp = `${cache}.hash`;
    const olean = path.join(root, '.lake/build/lib/lean', modulePath(module, 'olean'));
    const source = path.join(root, modulePath(module, 'lean'));
    const hash = extractorHash.copy();
    hash.update(await readFile(olean));
    hash.update(await readFile(source));
    hash.update(names);
    const digest = hash.digest('hex');
    const cached = existsSync(cache);
    const hit = cached && existsSync(stamp)
      && readFileSync(stamp, 'utf8') === digest;
    const estimatedSize = (await stat(cached ? cache : source)).size;
    jobs.push({
      order, module, moduleNodes, names, cache, stamp, digest, cached, hit, estimatedSize,
    });
  }
  jobs.sort((left, right) => {
    // Start uncached modules from a refactor first, using source size as their cost estimate.
    // Otherwise use the previous output size to prevent a large module from becoming a straggler.
    if (left.hit !== right.hit) return left.hit ? 1 : -1;
    if (left.cached !== right.cached) return left.cached ? 1 : -1;
    if (!left.hit && left.estimatedSize !== right.estimatedSize) {
      return right.estimatedSize - left.estimatedSize;
    }
    return left.order - right.order;
  });
  let next = 0;
  let completed = 0;
  function report(module) {
    completed += 1;
    console.error(`blueprint-source: ${completed}/${entries.length} ${module}`);
  }
  async function worker() {
    while (next < jobs.length) {
      const job = jobs[next++];
      const { module, moduleNodes, names, cache, stamp, digest, hit } = job;
      if (hit) {
        await consume(module, moduleNodes, JSON.parse(await readFile(cache, 'utf8')));
        report(module);
        continue;
      }
      await mkdir(path.dirname(cache), { recursive: true });
      const temporary = `${cache}.tmp`;
      const { stdout } = await execFileAsync(extractor, [module, names], {
        cwd: root,
        env: { ...process.env, LEAN_PATH: leanPath },
        encoding: 'utf8',
        maxBuffer: 1024 * 1024 * 512,
      });
      const moduleData = JSON.parse(stdout);
      await writeFile(temporary, stdout);
      await rename(temporary, cache);
      await writeFile(stamp, digest);
      await consume(module, moduleNodes, moduleData);
      report(module);
    }
  }
  await Promise.all([worker(), worker(), worker(), worker()]);
}

async function main() {
  const nodes = JSON.parse(await readFile(nodeDataPath, 'utf8'));
  const web = JSON.parse(await readFile(webDataPath, 'utf8'));
  const webNodes = new Map(web.nodes.map(node => [node.id, node]));
  const leanVersion = execFileSync('lean', ['--version'], { encoding: 'utf8' });
  const leanRevision = leanVersion.match(/commit ([0-9a-f]+)/)?.[1];
  if (!leanRevision) throw new Error('cannot read the Lean commit from lean --version');
  const proofMetadata = {};
  const standaloneSources = {};
  const standaloneOnly = process.env.BLUEPRINT_STANDALONE_ONLY === '1';
  const extractionNodes = standaloneOnly ? standaloneFiles : [...nodes, ...standaloneFiles];
  await extractModules(extractionNodes, async (_module, moduleNodes, moduleData) => {
    for (const node of moduleNodes) {
      const source = await readFile(path.join(root, node.source), 'utf8');
      const rendered = renderNode(
        node, moduleData, source, web.source.revision, leanRevision,
      );
      if (node.standalone) {
        standaloneSources[node.key] ??= {};
        standaloneSources[node.key][node.standalonePart] = node.standalonePart === 'statement'
          ? renderStandaloneFile(node, moduleData, source, web.source.revision, leanRevision)
          : renderStandaloneProof(
            node, moduleData, source, web.source.revision, leanRevision, rendered,
          );
        continue;
      }
      proofMetadata[node.label] = {
        goals: rendered.goals,
        states: rendered.states,
        references: rendered.references,
      };
      const webNode = webNodes.get(node.label);
      webNode.line = rendered.line;
      webNode.endLine = rendered.endLine;
      webNode.leanSource = rendered.leanSource;
      delete webNode.sourcePreview;
    }
  });
  web.standaloneStatements = standaloneDeclarations.map(({ key, title, description }) => ({
    key,
    title,
    description,
    leanSource: standaloneSources[key]?.statement,
    proofSource: standaloneSources[key]?.proof,
  }));
  delete web.sourceBundles;
  delete web.sourceBundleIndices;
  if (!standaloneOnly) {
    web.proofBundles = {};
    const generated = await import('node:fs/promises');
    for (const file of await generated.readdir(output)) {
      if (file.startsWith('lean-proof-') && file.endsWith('.bin')) {
        await rm(path.join(output, file));
      }
    }
    const chunkSize = 10;
    for (let start = 0; start < nodes.length; start += chunkSize) {
      const chunk = nodes.slice(start, start + chunkSize);
      const file = `lean-proof-${String(start / chunkSize + 1).padStart(3, '0')}.bin`;
      const bundle = { nodes: {} };
      for (const node of chunk) {
        const metadata = proofMetadata[node.label];
        if (!metadata) throw new Error(`missing proof metadata for ${node.label}`);
        bundle.nodes[node.label] = metadata;
        web.proofBundles[node.label] = file;
      }
      await writeFile(path.join(output, file), gzipSync(JSON.stringify(bundle), { mtime: 0 }));
    }
  }
  await writeFile(webDataPath, `${JSON.stringify(web, null, 2)}\n`);
  await rm(legacyBundlePath, { force: true });
  await embedBlueprintReader();
  console.log(`blueprint-source: wrote semantic source for ${nodes.length} selected declarations`);
}

main().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
