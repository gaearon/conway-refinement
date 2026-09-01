import type { BlueprintData, BlueprintNode, BlueprintPhase } from './types';

export type Route =
  | { kind: 'highlights' }
  | { kind: 'statements' }
  | { kind: 'references' }
  | { kind: 'chapter'; phase: string }
  | { kind: 'result'; node: BlueprintNode }
  | { kind: 'map'; node: BlueprintNode };

export function phaseMetadata(data: BlueprintData, id: string): BlueprintPhase {
  const phase = data.phases.find(candidate => candidate.id === id);
  if (!phase) throw new Error(`Unknown blueprint phase: ${id}`);
  return phase;
}

export function phaseIndex(data: BlueprintData, id: string): number {
  return data.phases.findIndex(candidate => candidate.id === id);
}

export function nodeSlug(node: BlueprintNode): string {
  return node.id.replace(/^[^:]+:/, '');
}

export function chapterPath(data: BlueprintData, phase: string): string {
  return `/chapter/${phaseMetadata(data, phase).id}`;
}

export function resultPath(node: BlueprintNode): string {
  return `/result/${encodeURIComponent(nodeSlug(node))}`;
}

export function mapPath(node: BlueprintNode): string {
  return `/map/${encodeURIComponent(nodeSlug(node))}`;
}

export function parseRoute(data: BlueprintData, value = location.hash.slice(1) || '/'): Route {
  if (value === '/' || value === '/highlights') return { kind: 'highlights' };
  if (value === '/statements') return { kind: 'statements' };
  if (value === '/references') return { kind: 'references' };
  const map = value.match(/^\/map\/(.+)$/);
  if (map) {
    const slug = decodeURIComponent(map[1]);
    const node = data.nodes.find(candidate => nodeSlug(candidate) === slug);
    if (node) return { kind: 'map', node };
  }
  const result = value.match(/^\/result\/(.+)$/);
  if (result) {
    const slug = decodeURIComponent(result[1]);
    const node = data.nodes.find(candidate => nodeSlug(candidate) === slug);
    if (node) return { kind: 'result', node };
  }
  const chapter = value.match(/^\/(?:map\/)?chapter\/(.+)$/);
  if (chapter) {
    const phase = data.phases.find(candidate => candidate.id === chapter[1]);
    if (phase) return { kind: 'chapter', phase: phase.id };
  }
  return { kind: 'highlights' };
}

export function navigate(path: string, replace = false): void {
  const next = `#${path}`;
  if (replace) history.replaceState(null, '', next);
  else location.hash = path;
  if (replace) window.dispatchEvent(new HashChangeEvent('hashchange'));
}

type ScrollPosition =
  | { kind: 'map'; left: number; top: number; node?: string; nodeLeft?: number; nodeTop?: number }
  | { kind: 'statements'; left: number; top: number; node?: string; nodeTop?: number };

type PendingNavigation =
  | { node: string; alignment: 'center' | 'start'; stableFrames: number }
  | { position: ScrollPosition; stableFrames: number };

const scrollPositions = new Map<string, ScrollPosition>();
let pendingNavigation: PendingNavigation | undefined;

function setElementScroll(element: HTMLElement, left: number, top: number): void {
  element.scrollLeft = left;
  element.scrollTop = top;
}

function pageScroller(): HTMLElement | null {
  return document.scrollingElement as HTMLElement | null;
}

function setPageScroll(left: number, top: number): void {
  const scroller = pageScroller();
  if (scroller) setElementScroll(scroller, left, top);
  else window.scrollTo(left, top);
}

function pageScrollStart(element: Element): number {
  const scroller = pageScroller();
  const padding = Number.parseFloat(getComputedStyle(scroller ?? document.documentElement)
    .scrollPaddingTop) || 0;
  const margin = Number.parseFloat(getComputedStyle(element).scrollMarginTop) || 0;
  return padding + margin;
}

function proofNodeElement(id: string): Element | undefined {
  return Array.from(document.querySelectorAll('[data-proof-node]'))
    .find(element => element.getAttribute('data-proof-node') === id);
}

function currentScrollPosition(node: BlueprintNode): ScrollPosition {
  const map = document.querySelector<HTMLElement>('.react-map-stage');
  const element = proofNodeElement(node.id);
  const rect = element?.getBoundingClientRect();
  const id = element?.getAttribute('data-proof-node') ?? undefined;
  return map
    ? { kind: 'map', left: map.scrollLeft, top: map.scrollTop, node: id,
      nodeLeft: rect?.left, nodeTop: rect?.top }
    : { kind: 'statements', left: window.scrollX, top: window.scrollY, node: id,
      nodeTop: rect?.top };
}

export function navigatePreservingNode(path: string, node: BlueprintNode,
  alignment: 'center' | 'start' = 'center'): void {
  const currentPath = location.hash.slice(1) || '/';
  scrollPositions.set(currentPath, currentScrollPosition(node));
  const saved = scrollPositions.get(path);
  pendingNavigation = saved?.node === node.id
    ? { position: saved, stableFrames: 0 }
    : { node: node.id, alignment, stableFrames: 0 };
  navigate(path);
}

export function hasPendingNodePosition(): boolean {
  return pendingNavigation !== undefined;
}

export function requestNodePosition(node: BlueprintNode, alignment: 'center' | 'start'): void {
  if (!pendingNavigation) pendingNavigation = { node: node.id, alignment, stableFrames: 0 };
}

export function restorePendingNodePosition(force = false): boolean {
  if (!pendingNavigation) return true;
  if ('position' in pendingNavigation) {
    const position = pendingNavigation.position;
    const map = document.querySelector<HTMLElement>('.react-map-stage');
    const element = position.node ? proofNodeElement(position.node) : undefined;
    if (position.kind === 'map') {
      if (!map) return false;
      if (element && position.nodeLeft !== undefined && position.nodeTop !== undefined) {
        const rect = element.getBoundingClientRect();
        setElementScroll(map,
          map.scrollLeft + rect.left - position.nodeLeft,
          map.scrollTop + rect.top - position.nodeTop);
      } else setElementScroll(map, position.left, position.top);
    } else {
      if (map) return false;
      if (element && position.nodeTop !== undefined)
        setPageScroll(window.scrollX,
          window.scrollY + element.getBoundingClientRect().top - position.nodeTop);
      else setPageScroll(position.left, position.top);
    }
    const restored = element?.getBoundingClientRect();
    const stable = restored && position.nodeTop !== undefined
      ? Math.abs(restored.top - position.nodeTop) < 1
        && (position.kind === 'statements' || position.nodeLeft === undefined
          || Math.abs(restored.left - position.nodeLeft) < 1)
      : position.kind === 'map' ? Math.abs(map!.scrollTop - position.top) < 1
        && Math.abs(map!.scrollLeft - position.left) < 1
        : Math.abs(window.scrollY - position.top) < 1;
    pendingNavigation.stableFrames = stable ? pendingNavigation.stableFrames + 1 : 0;
    if (pendingNavigation.stableFrames < 24 && !force) return false;
    pendingNavigation = undefined;
    return true;
  }
  const element = proofNodeElement(pendingNavigation.node);
  if (!element) return false;
  const rect = element.getBoundingClientRect();
  const map = element.closest<HTMLElement>('.react-map-stage');
  if (map) {
    const viewport = map.getBoundingClientRect();
    setElementScroll(map,
      map.scrollLeft + (rect.left + rect.right - viewport.left - viewport.right) / 2,
      map.scrollTop + (rect.top + rect.bottom - viewport.top - viewport.bottom) / 2);
  } else {
    if (pendingNavigation.alignment === 'start') {
      element.scrollIntoView({ block: 'start', inline: 'nearest', behavior: 'auto' });
    } else {
      setPageScroll(window.scrollX,
        window.scrollY + (rect.top + rect.bottom - window.innerHeight) / 2);
    }
  }
  const restored = element.getBoundingClientRect();
  const viewport = map?.getBoundingClientRect();
  const stable = map && viewport
    ? Math.abs(restored.left + restored.right - viewport.left - viewport.right) < 2
      && Math.abs(restored.top + restored.bottom - viewport.top - viewport.bottom) < 2
    : pendingNavigation.alignment === 'center'
      ? Math.abs(restored.top + restored.bottom - window.innerHeight) < 2
      : Math.abs(restored.top - pageScrollStart(element)) < 2;
  pendingNavigation.stableFrames = stable ? pendingNavigation.stableFrames + 1 : 0;
  if (pendingNavigation.stableFrames < 24 && !force) return false;
  pendingNavigation = undefined;
  return true;
}
