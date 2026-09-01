import { useCallback, useEffect, useLayoutEffect, useRef, useState } from 'react';
import { phaseMetadata } from './routes';
import type { BlueprintData, BlueprintNode } from './types';

export type ResultPreviewTarget = {
  node: BlueprintNode;
  x: number;
  y: number;
};

export function useResultPreview() {
  const [target, setTarget] = useState<ResultPreviewTarget>();
  const closeTimer = useRef<number | undefined>(undefined);
  const scrolling = useRef(false);
  const scrollTimer = useRef<number | undefined>(undefined);
  const keepOpen = useCallback(() => {
    if (closeTimer.current !== undefined) window.clearTimeout(closeTimer.current);
    closeTimer.current = undefined;
  }, []);
  const show = useCallback((next: ResultPreviewTarget) => {
    if (scrolling.current) return;
    keepOpen();
    setTarget(next);
  }, [keepOpen]);
  const close = useCallback(() => {
    keepOpen();
    closeTimer.current = window.setTimeout(() => setTarget(undefined), 110);
  }, [keepOpen]);
  useEffect(() => {
    const suppress = () => {
      scrolling.current = true;
      keepOpen();
      setTarget(undefined);
      if (scrollTimer.current !== undefined) window.clearTimeout(scrollTimer.current);
      scrollTimer.current = window.setTimeout(() => {
        scrolling.current = false;
        scrollTimer.current = undefined;
      }, 160);
    };
    window.addEventListener('scroll', suppress, { capture: true, passive: true });
    return () => {
      window.removeEventListener('scroll', suppress, { capture: true });
      keepOpen();
      if (scrollTimer.current !== undefined) window.clearTimeout(scrollTimer.current);
    };
  }, [keepOpen]);
  return { target, show, close };
}

export default function ResultPreview({ data, target }: {
  data: BlueprintData;
  target?: ResultPreviewTarget;
}) {
  const card = useRef<HTMLElement>(null);
  const statement = useRef<HTMLDivElement>(null);
  const [position, setPosition] = useState({ left: 10, top: 10 });
  const [overflowing, setOverflowing] = useState(false);

  useLayoutEffect(() => {
    if (!target || !card.current) return;
    const width = card.current.offsetWidth;
    const height = card.current.offsetHeight;
    setPosition({
      left: Math.max(10, Math.min(target.x + 18, window.innerWidth - width - 18)),
      top: Math.max(10, Math.min(target.y + 18, window.innerHeight - height - 18)),
    });
    const element = statement.current;
    setOverflowing(Boolean(element && element.scrollHeight > element.clientHeight + 1));
  }, [target]);

  if (!target) return null;
  return <aside ref={card} className="result-preview" style={position}>
    <small>{target.node.kind} {target.node.number} · {
      phaseMetadata(data, target.node.phase).title}</small>
    <strong dangerouslySetInnerHTML={{ __html: target.node.titleHtml }} />
    <div ref={statement}
      className={`result-preview-statement${overflowing ? ' is-overflowing' : ''}`}
      dangerouslySetInnerHTML={{ __html: target.node.statement }} />
  </aside>;
}
