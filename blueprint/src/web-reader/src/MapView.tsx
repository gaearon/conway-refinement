import { useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react';
import ResultPreview, { useResultPreview } from './ResultPreview';
import {
  chapterPath, navigate, navigatePreservingNode, phaseIndex, phaseMetadata, resultPath,
} from './routes';
import type { BlueprintData, BlueprintNode } from './types';

const BOX_WIDTH = 232;
const BOX_HEIGHT = 106;
const X_GAP = 22;
const Y_GAP = 72;
const MAX_COLUMNS = 4;
const MIN_COLUMNS = 3;
const HORIZONTAL_PADDING = 64;
const DEFAULT_WIDTH = 760;
const MIN_GRAPH_WIDTH = HORIZONTAL_PADDING + MIN_COLUMNS * BOX_WIDTH
  + (MIN_COLUMNS - 1) * X_GAP;

type BoundaryNode = {
  id: string;
  kind: 'Earlier section' | 'Later section';
  title: string;
  titleHtml: string;
  phase: string;
  dependencies: string[];
  boundary: 'input' | 'output';
  boundaryCount: number;
  members: string[];
};

type GraphNode = BlueprintNode | BoundaryNode;

function isBoundary(node: GraphNode): node is BoundaryNode {
  return 'boundary' in node;
}

function closure(data: BlueprintData, id: string, descendants = false): Set<string> {
  const result = new Set<string>();
  const pending = [id];
  while (pending.length) {
    const current = pending.pop()!;
    if (result.has(current)) continue;
    result.add(current);
    if (descendants) {
      data.nodes.forEach(node => {
        if (node.dependencies.includes(current)) pending.push(node.id);
      });
    } else {
      pending.push(...(data.nodes.find(node => node.id === current)?.dependencies ?? []));
    }
  }
  return result;
}

function sectionGraphNodes(data: BlueprintData, phase: string): GraphNode[] {
  const local = data.nodes.filter(node => node.phase === phase);
  const localIds = new Set(local.map(node => node.id));
  const incoming = new Map<string, Set<string>>();
  const outgoing = new Map<string, Set<string>>();
  local.forEach(node => node.dependencies.forEach(dependency => {
    if (localIds.has(dependency)) return;
    const sourcePhase = data.nodes.find(candidate => candidate.id === dependency)?.phase;
    if (!sourcePhase) return;
    const members = incoming.get(sourcePhase) ?? new Set<string>();
    members.add(dependency);
    incoming.set(sourcePhase, members);
  }));
  data.nodes.forEach(node => node.dependencies.forEach(dependency => {
    if (!localIds.has(dependency) || localIds.has(node.id)) return;
    const members = outgoing.get(node.phase) ?? new Set<string>();
    members.add(dependency);
    outgoing.set(node.phase, members);
  }));
  const inputId = (source: string) => `boundary:input:${phase}:${source}`;
  const outputId = (target: string) => `boundary:output:${phase}:${target}`;
  const inputs: BoundaryNode[] = [...incoming]
    .sort(([left], [right]) => phaseIndex(data, left) - phaseIndex(data, right))
    .map(([source, members]) => ({
      id: inputId(source),
      kind: 'Earlier section',
      title: phaseMetadata(data, source).title,
      titleHtml: phaseMetadata(data, source).title,
      phase: source,
      dependencies: [],
      boundary: 'input',
      boundaryCount: members.size,
      members: [...members],
    }));
  const current = local.map(node => ({
    ...node,
    dependencies: [...new Set(node.dependencies.map(dependency => {
      if (localIds.has(dependency)) return dependency;
      const source = data.nodes.find(candidate => candidate.id === dependency)?.phase;
      return source ? inputId(source) : dependency;
    }))],
  }));
  const outputs: BoundaryNode[] = [...outgoing]
    .sort(([left], [right]) => phaseIndex(data, left) - phaseIndex(data, right))
    .map(([target, members]) => ({
      id: outputId(target),
      kind: 'Later section',
      title: phaseMetadata(data, target).title,
      titleHtml: phaseMetadata(data, target).title,
      phase: target,
      dependencies: [...members],
      boundary: 'output',
      boundaryCount: members.size,
      members: [...members],
    }));
  return [...inputs, ...current, ...outputs];
}

function levels(nodes: GraphNode[]): Map<number, GraphNode[]> {
  const ids = new Set(nodes.map(node => node.id));
  const memo = new Map<string, number>();
  const visit = (node: GraphNode): number => {
    const known = memo.get(node.id);
    if (known !== undefined) return known;
    const local = node.dependencies
      .map(id => nodes.find(candidate => candidate.id === id))
      .filter((candidate): candidate is GraphNode => Boolean(candidate && ids.has(candidate.id)));
    const level = local.length ? Math.max(...local.map(visit)) + 1 : 0;
    memo.set(node.id, level);
    return level;
  };
  const result = new Map<number, GraphNode[]>();
  nodes.forEach(node => {
    const level = visit(node);
    const row = result.get(level) ?? [];
    row.push(node);
    result.set(level, row);
  });
  const order = (node: GraphNode) => isBoundary(node)
    ? (node.boundary === 'input' ? -1 : Number.MAX_SAFE_INTEGER)
    : node.number;
  result.forEach(row => row.sort((left, right) =>
    order(left) - order(right) || left.id.localeCompare(right.id)));
  return result;
}

function rowsFor(nodes: GraphNode[], columns: number) {
  return [...levels(nodes)].sort(([left], [right]) => left - right)
    .flatMap(([, row]) => Array.from({ length: Math.ceil(row.length / columns) }, (_, index) =>
      row.slice(index * columns, (index + 1) * columns)));
}

function layout(nodes: GraphNode[], phases: string[] = [], availableWidth = DEFAULT_WIDTH) {
  const width = Math.max(MIN_GRAPH_WIDTH, availableWidth);
  const columns = Math.max(1, Math.min(MAX_COLUMNS,
    Math.floor((width - HORIZONTAL_PADDING + X_GAP) / (BOX_WIDTH + X_GAP))));
  const phaseRows = phases.map(phase => ({
    phase,
    rows: rowsFor(nodes.filter(node => node.phase === phase), columns),
  }));
  const rows = phaseRows.length ? phaseRows.flatMap(section => section.rows) : rowsFor(nodes, columns);
  const positions = new Map<string, { x: number; y: number }>();
  const placeRows = (localRows: GraphNode[][], startY: number) => {
    localRows.forEach((row, rowIndex) => {
      const rowWidth = row.length * BOX_WIDTH + (row.length - 1) * X_GAP;
      const start = (width - rowWidth) / 2;
      row.forEach((node, column) => positions.set(node.id, {
        x: start + column * (BOX_WIDTH + X_GAP),
        y: startY + rowIndex * (BOX_HEIGHT + Y_GAP),
      }));
    });
    return localRows.length
      ? localRows.length * BOX_HEIGHT + (localRows.length - 1) * Y_GAP
      : 0;
  };
  if (phaseRows.length) {
    const sections: Array<{ phase: string; y: number; height: number }> = [];
    let currentY = 24;
    phaseRows.forEach(section => {
      const contentY = currentY + 42;
      const contentHeight = placeRows(section.rows, contentY);
      const sectionBottom = contentY + contentHeight + 26;
      sections.push({ phase: section.phase, y: currentY, height: sectionBottom - currentY });
      currentY = sectionBottom + 22;
    });
    return { positions, sections, width, height: currentY + 2 };
  }
  placeRows(rows, 32);
  return {
    positions,
    sections: [] as Array<{ phase: string; y: number; height: number }>,
    width,
    height: 64 + rows.length * BOX_HEIGHT + Math.max(0, rows.length - 1) * Y_GAP,
  };
}

function graphNodeIsRelated(node: GraphNode, related: Set<string>): boolean {
  return isBoundary(node) ? node.members.some(member => related.has(member)) : related.has(node.id);
}

export default function MapView({ data, phase, focused }: {
  data: BlueprintData;
  phase?: string;
  focused?: BlueprintNode;
}) {
  const spansPhases = Boolean(focused) || !phase;
  const [expandedPhases, setExpandedPhases] = useState<Set<string>>(new Set());
  const stage = useRef<HTMLDivElement>(null);
  const [stageWidth, setStageWidth] = useState(DEFAULT_WIDTH);
  useEffect(() => setExpandedPhases(new Set()), [focused?.id]);
  useLayoutEffect(() => {
    const element = stage.current;
    if (!element) return;
    const update = () => setStageWidth(current => {
      const next = element.clientWidth;
      return next && next !== current ? next : current;
    });
    update();
    const observer = new ResizeObserver(update);
    observer.observe(element);
    return () => observer.disconnect();
  }, []);
  const focusedIds = useMemo(() => {
    if (!focused) return undefined;
    const ids = closure(data, focused.id);
    closure(data, focused.id, true).forEach(id => ids.add(id));
    return ids;
  }, [data, focused]);
  const nodes = useMemo(() => {
    if (focusedIds) return data.nodes.filter(node =>
      focusedIds.has(node.id) || expandedPhases.has(node.phase));
    return phase ? sectionGraphNodes(data, phase) : data.nodes;
  }, [data, expandedPhases, focusedIds, phase]);
  const groupedPhases = phase && !focused ? [] : data.phases.map(item => item.id);
  const { positions, sections, width, height } = useMemo(
    () => layout(nodes, groupedPhases, stageWidth), [groupedPhases, nodes, stageWidth]);
  const nodeIds = new Set(nodes.map(node => node.id));
  const nodeById = new Map(nodes.map(node => [node.id, node]));
  const preview = useResultPreview();
  const emphasized = preview.target?.node ?? focused;
  const related = emphasized
    ? new Set([...closure(data, emphasized.id), ...closure(data, emphasized.id, true)])
    : null;

  return <div className={`map-page${focused ? ' is-focused' : ''}`}>
    {!focused && <header className="map-route-bar">
      <strong>{phase ? `${phaseIndex(data, phase) + 1}. ${phaseMetadata(data, phase).title}`
        : 'Complete proof map'}</strong>
    </header>}
    <div ref={stage} className="react-map-stage">
      <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}
        role="img" aria-label="Dependency map">
        <g>
          {sections.map(section => <g key={section.phase} className="graph-phase-band">
            <rect x={16} y={section.y} width={width - 32} height={section.height} />
            <foreignObject x={30} y={section.y + 7} width={width - 230} height={28}>
              <div className="graph-phase-title">{phaseMetadata(data, section.phase).title}</div>
            </foreignObject>
            {focusedIds && data.nodes.some(node =>
              node.phase === section.phase && !focusedIds.has(node.id))
              && <foreignObject x={width - 194} y={section.y + 7} width={164} height={28}>
                <button className="graph-phase-toggle" onClick={() => setExpandedPhases(current => {
                  const next = new Set(current);
                  if (next.has(section.phase)) next.delete(section.phase);
                  else next.add(section.phase);
                  return next;
                })}>{expandedPhases.has(section.phase) ? 'Hide' : 'Show'} other statements</button>
              </foreignObject>}
          </g>)}
          {nodes.flatMap(target => target.dependencies.filter(id => nodeIds.has(id)).map(id => {
            const source = positions.get(id)!;
            const end = positions.get(target.id)!;
            const active = !related || graphNodeIsRelated(nodeById.get(id)!, related)
              && graphNodeIsRelated(target, related);
            const x1 = source.x + BOX_WIDTH / 2;
            const y1 = source.y + BOX_HEIGHT;
            const x2 = end.x + BOX_WIDTH / 2;
            const y2 = end.y;
            const bend = Math.max(28, (y2 - y1) * .45);
            return <path key={`${id}-${target.id}`}
              className={`graph-edge${related ? active ? ' is-highlighted' : ' is-dimmed' : ''}`}
              d={`M ${x1} ${y1} C ${x1} ${y1 + bend}, ${x2} ${y2 - bend}, ${x2} ${y2}`} />;
          }))}
          {nodes.map(node => {
            const point = positions.get(node.id)!;
            const boundary = isBoundary(node);
            const dimmed = related && !graphNodeIsRelated(node, related);
            const showPhase = spansPhases && sections.length === 0;
            const meta = boundary
              ? node.boundary === 'input'
                ? `${node.kind} · ${node.boundaryCount} prerequisite${node.boundaryCount === 1 ? '' : 's'}`
                : `${node.kind} · ${node.boundaryCount} result${node.boundaryCount === 1 ? '' : 's'} used downstream`
              : `${node.kind} ${node.number}${showPhase
                ? ` · §${phaseIndex(data, node.phase) + 1}` : ''}`;
            const destination = boundary
              ? chapterPath(data, node.phase)
              : resultPath(node);
            return <foreignObject key={node.id} x={point.x} y={point.y}
              width={BOX_WIDTH} height={BOX_HEIGHT}
              data-proof-node={boundary ? undefined : node.id}
              className={`graph-node${boundary ? ' is-boundary' : ''}${
                !boundary && node.highlight ? ' is-major' : ''}${
                focused?.id === node.id ? ' is-selected' : ''}${dimmed ? ' is-dimmed' : ''}`}>
              <a className={`node-card${boundary ? ' phase-node-card' : ''}`}
                href={`#${destination}`} onClick={event => {
                  if (event.button !== 0 || event.metaKey || event.ctrlKey
                    || event.shiftKey || event.altKey) return;
                  event.preventDefault();
                  if (boundary) navigate(destination);
                  else navigatePreservingNode(destination, node, 'start');
                }}
                onMouseEnter={boundary ? undefined
                  : event => preview.show({ node, x: event.clientX, y: event.clientY })}
                onMouseMove={boundary ? undefined
                  : event => preview.show({ node, x: event.clientX, y: event.clientY })}
                onMouseLeave={boundary ? undefined : preview.close}>
                <span className="node-meta">{meta}</span>
                <span className="node-title" dangerouslySetInnerHTML={{ __html: node.titleHtml }} />
              </a>
            </foreignObject>;
          })}
        </g>
      </svg>
    </div>
    <ResultPreview data={data} target={preview.target} />
  </div>;
}
