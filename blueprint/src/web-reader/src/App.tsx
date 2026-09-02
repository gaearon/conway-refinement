import { memo, useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react';
import { loadProofBundle, readBlueprintData } from './data';
import LeanSource from './LeanSource';
import MapView from './MapView';
import ResultPreview, { type ResultPreviewTarget, useResultPreview } from './ResultPreview';
import {
  chapterPath, hasPendingNodePosition, mapPath, navigate, navigatePreservingNode, parseRoute,
  phaseIndex, phaseMetadata, requestNodePosition, restorePendingNodePosition, resultPath,
  type Route,
} from './routes';
import type {
  BlueprintData, BlueprintNode, LeanProofMetadata, LeanSource as LeanSourceData,
} from './types';

const PHASE_COLORS = ['#516f68', '#836f48', '#2f6f89', '#6b5b82', '#986149', '#3f7350', '#7b5267'];

function routePhase(route: Route): string | undefined {
  if (route.kind === 'chapter') return route.phase;
  if (route.kind === 'result' || route.kind === 'map') return route.node.phase;
  return undefined;
}

function isMapRoute(route: Route): boolean {
  return route.kind === 'map';
}

function Sidebar({ data, route, onSearch }: {
  data: BlueprintData;
  route: Route;
  onSearch: () => void;
}) {
  const contents = useRef<HTMLElement>(null);
  const [menuOpen, setMenuOpen] = useState(false);
  const active = routePhase(route);
  useEffect(() => setMenuOpen(false), [route]);
  useEffect(() => {
    if (!menuOpen) return;
    const dismiss = (event: PointerEvent) => {
      if (event.target instanceof Node && !contents.current?.contains(event.target)) {
        setMenuOpen(false);
      }
    };
    const escape = (event: KeyboardEvent) => {
      if (event.key === 'Escape') setMenuOpen(false);
    };
    document.addEventListener('pointerdown', dismiss);
    document.addEventListener('keydown', escape);
    return () => {
      document.removeEventListener('pointerdown', dismiss);
      document.removeEventListener('keydown', escape);
    };
  }, [menuOpen]);
  useLayoutEffect(() => {
    const sidebar = contents.current;
    if (!sidebar || window.matchMedia('(max-width: 850px)').matches) return;
    const current = sidebar.querySelector<HTMLElement>('.phase-link.is-active');
    if (!current) return;
    const sidebarRect = sidebar.getBoundingClientRect();
    const currentRect = current.getBoundingClientRect();
    const padding = 16;
    if (currentRect.top < sidebarRect.top + padding) {
      sidebar.scrollTop += currentRect.top - sidebarRect.top - padding;
    } else if (currentRect.bottom > sidebarRect.bottom - padding) {
      sidebar.scrollTop += currentRect.bottom - sidebarRect.bottom + padding;
    }
  }, [active, route.kind]);
  return <aside ref={contents} className={`contents${menuOpen ? ' is-open' : ''}`}>
    <div className="site-heading">
      <button className="site-title" onClick={() => navigate('/highlights')}>
        <span>Conway’s refinement conjecture</span><small>Lean proof guide</small>
      </button>
    </div>
    <button className="mobile-menu-toggle" aria-expanded={menuOpen}
      aria-controls="mobile-contents-menu" onClick={() => setMenuOpen(open => !open)}>
      <span className="visually-hidden">{menuOpen ? 'Close menu' : 'Open menu'}</span>
      <span /><span /><span />
    </button>
    <div id="mobile-contents-menu" className="contents-menu">
      <button className="reader-tool reader-search" onClick={() => {
        setMenuOpen(false);
        onSearch();
      }}>Search</button>
      <div className="contents-label">Contents</div>
      <div className="phase-nav-frame">
        <nav className="phase-nav">
          <button className={`phase-link phase-link-highlights${
            route.kind === 'highlights' ? ' is-active' : ''}`} onClick={() => navigate('/highlights')}>
            <span className="phase-number" aria-hidden="true">✦</span>
            <span className="phase-name">Highlights</span>
          </button>
          <button className={`phase-link${route.kind === 'statements' ? ' is-active' : ''}`}
            onClick={() => navigate('/statements')}>
            <span className="phase-number">0.</span><span className="phase-name">Formal statements</span>
          </button>
          {data.phases.map((phase, index) => <button key={phase.id}
            className={`phase-link${active === phase.id ? ' is-active' : ''}`}
            style={{ '--phase-color': PHASE_COLORS[index % PHASE_COLORS.length] } as React.CSSProperties}
            onClick={() => navigate(chapterPath(data, phase.id))}>
            <span className="phase-number">{index + 1}.</span>
            <span className="phase-name">{phase.title}</span>
          </button>)}
          <button className={`phase-link phase-link-references${
            route.kind === 'references' ? ' is-active' : ''}`} onClick={() => navigate('/references')}>
            <span className="phase-number" aria-hidden="true">§</span>
            <span className="phase-name">References</span>
          </button>
        </nav>
      </div>
      <div className="guide-menu-footer">
        <p className="site-provenance">All prose is AI-generated. Built from <a
          href={`${data.source.repository}/commit/${data.source.revision}`}
          target="_blank" rel="noreferrer">{data.source.revision.slice(0, 7)}</a>.</p>
        <GuideLinks data={data} />
      </div>
    </div>
  </aside>;
}

function GuideLinks({ data }: { data: BlueprintData }) {
  return <nav className="guide-icon-links" aria-label="Guide files">
    <a href="blueprint.pdf" target="_blank" rel="noreferrer"
      aria-label="Open PDF" title="PDF">
      <svg viewBox="0 0 24 24" aria-hidden="true">
        <path d="M6.5 2.5h7l4 4v15h-11z" /><path d="M13.5 2.5v4h4" />
        <path d="M9.5 11h5m-5 3h5m-5 3h3" />
      </svg>
    </a>
    <a href={data.source.repository} target="_blank" rel="noreferrer"
      aria-label="Open GitHub repository" title="GitHub">
      <svg viewBox="0 0 24 24" aria-hidden="true">
        <path d="M12 2.7a9.5 9.5 0 0 0-3 18.5c.5.1.7-.2.7-.5v-1.8c-2.9.6-3.5-1.2-3.5-1.2-.5-1.2-1.2-1.5-1.2-1.5-1-.7.1-.7.1-.7 1.1.1 1.7 1.1 1.7 1.1 1 1.7 2.5 1.2 3 .9.1-.7.4-1.2.7-1.5-2.3-.3-4.7-1.2-4.7-5.2 0-1.1.4-2.1 1-2.8-.1-.3-.4-1.3.1-2.8 0 0 .8-.3 2.9 1.1a9.7 9.7 0 0 1 5.2 0c2-1.4 2.9-1.1 2.9-1.1.5 1.5.2 2.5.1 2.8.7.7 1 1.7 1 2.8 0 4.1-2.5 5-4.8 5.2.4.3.7 1 .7 1.9v2.9c0 .3.2.6.7.5A9.5 9.5 0 0 0 12 2.7z" />
      </svg>
    </a>
  </nav>;
}

function ReaderBar({ route }: { route: Route }) {
  if (route.kind !== 'map') return null;
  const focused = route.node;
  const clear = () => {
    navigatePreservingNode(resultPath(focused), focused, 'start');
  };
  return <header className="reader-bar">
    <div className="reader-bar-center">
      <div className="reader-bar-focus" aria-label="Focused proof">
        <span className="reader-bar-focus-label">Proof map for {focused.kind} {focused.number}</span>
        <button className="reader-bar-focus-clear" onClick={clear}
          aria-label="Close proof map">×</button>
      </div>
    </div>
  </header>;
}

function FormalStatements({ data }: { data: BlueprintData }) {
  return <section className="formal-statements">
    <header className="phase-header"><h1>0. Formal statements</h1>
      <p>Three standalone files make the result easier to audit.</p>
      <ul className="formal-intro-list">
        <li>Conway's statement using the surreal numbers from{' '}
          <a href="https://github.com/vihdzp/combinatorial-games" target="_blank"
            rel="noreferrer">CombinatorialGames</a></li>
        <li>A{' '}<a href="https://github.com/leanprover-community/mathlib4" target="_blank"
          rel="noreferrer">Mathlib</a>-only construction of the needed surreal numbers, order,
          and arithmetic</li>
        <li>A{' '}<a href="https://github.com/leanprover-community/mathlib4" target="_blank"
          rel="noreferrer">Mathlib</a>-only refinement theorem for integer parts of generalised
          power-series fields</li>
      </ul>
    </header>
    <section className="result-list">
      {data.standaloneStatements.map(statement => <article key={statement.key}
        className="result formal-statement"><div className="result-body">
        <div className="result-lead"><h2 className="result-heading">{statement.title}</h2>
          <p className="formal-statement-description">{statement.description}</p></div>
        <h3 className="formal-source-heading">Standalone statement</h3>
        <SourceSlot source={statement.leanSource} />
        <h3 className="formal-source-heading">Proof</h3>
        <SourceSlot source={statement.proofSource} />
      </div></article>)}
    </section>
  </section>;
}

function Introduction({ text }: { text: string }) {
  return <div className="phase-introduction">{text.split(/\n\n+/).map((paragraph, index) =>
    <p key={index}>{paragraph}</p>)}</div>;
}

function Highlights({ data }: { data: BlueprintData }) {
  return <section className="highlights-page">
    <header className="phase-header"><h1>{data.highlights.title}</h1>
      <Introduction text={data.highlights.description} /></header>
    {data.phases.map(phase => {
      const nodes = data.nodes.filter(node => node.phase === phase.id && node.highlight);
      if (!nodes.length) return null;
      return <section className="highlight-group" key={phase.id}>
        <h2 className="highlight-phase-heading">{phase.title}</h2>
        <ResultCollection data={data} nodes={nodes} />
      </section>;
    })}
  </section>;
}

function References({ data }: { data: BlueprintData }) {
  return <section className="references-page">
    <header className="phase-header"><h1>References</h1></header>
    <ol className="reference-list">
      {data.references.map(reference => <li key={reference.key} id={`reference-${reference.key}`}>
        <span>{reference.authors}, </span>
        {reference.url ? <a href={reference.url} target="_blank" rel="noreferrer">
          <cite>{reference.title}</cite></a> : <cite>{reference.title}</cite>}
        <span>, <cite>{reference.venue}</cite>
          {reference.volume && <> <strong>{reference.volume}</strong></>}
          {reference.year && <> ({reference.year})</>}
          {reference.details && <>, {reference.details}</>}.</span>
      </li>)}
    </ol>
  </section>;
}

function SourceSlot({ source, metadata }: {
  source?: BlueprintNode['leanSource'] | LeanSourceData;
  metadata?: LeanProofMetadata;
}) {
  const complete = useMemo<LeanSourceData | undefined>(() => source ? {
    ...source,
    goals: metadata?.goals ?? ('goals' in source ? source.goals : {}),
    states: metadata?.states ?? ('states' in source ? source.states : []),
    references: metadata?.references ?? ('references' in source ? source.references : {}),
  } : undefined, [metadata, source]);
  if (!complete) return <div className="lean-source-slot" />;
  return <div className="lean-source-slot"><LeanSource source={complete} /></div>;
}

const Result = memo(function Result({ data, node, metadata, loadMetadata, selected, onPreview,
  closePreview, eager }: {
  data: BlueprintData;
  node: BlueprintNode;
  metadata?: LeanProofMetadata;
  loadMetadata: (node: string) => void;
  selected?: boolean;
  eager?: boolean;
  onPreview: (target: ResultPreviewTarget) => void;
  closePreview: () => void;
}) {
  const result = useRef<HTMLElement>(null);
  const [active, setActive] = useState(Boolean(selected || eager));
  useEffect(() => {
    if (selected || eager) {
      setActive(true);
      loadMetadata(node.id);
      return;
    }
    const element = result.current;
    if (!element || active) return;
    const observer = new IntersectionObserver(entries => {
      if (!entries.some(entry => entry.isIntersecting)) return;
      setActive(true);
      loadMetadata(node.id);
      observer.disconnect();
    }, { rootMargin: '800px 0px' });
    observer.observe(element);
    return () => observer.disconnect();
  }, [active, eager, loadMetadata, node.id, selected]);
  const updatePreview = (event: React.MouseEvent) => {
    const link = (event.target as Element).closest<HTMLAnchorElement>('a[data-reference]');
    const referenced = link && data.nodes.find(candidate => candidate.id === link.dataset.reference);
    if (referenced) onPreview({ node: referenced, x: event.clientX, y: event.clientY });
    else closePreview();
  };
  return <article ref={result} className={`result${selected ? ' is-targeted' : ''}`}
    onMouseMove={updatePreview} onMouseLeave={closePreview}
    id={`result-${node.number}`} data-proof-node={node.id}>
    <div className="result-body">
      <nav className="result-actions" aria-label={`${node.kind} ${node.number} actions`}>
        <a className="result-action result-permalink" href={`#${resultPath(node)}`}
          aria-label={`Permalink to ${node.kind} ${node.number}`}>
          <span className="result-action-icon result-permalink-icon" aria-hidden="true">
            <svg viewBox="0 0 16 14">
              <path d="M5.5 1.5 4 12.5M11.5 1.5 10 12.5M2 5h12M1.5 9h12" />
            </svg>
          </span>
          <span>Permalink</span></a>
        <a className="result-action result-focus" href={`#${mapPath(node)}`}
          onClick={event => {
            if (event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
            event.preventDefault();
            navigatePreservingNode(mapPath(node), node);
          }}
          aria-label={`Open proof map for ${node.kind} ${node.number}`}>
          <svg viewBox="0 0 18 14" aria-hidden="true">
            <path d="M4 3.5v3.1c0 1.1.9 2 2 2h6M12 5.4v6" />
            <circle cx="4" cy="2.5" r="1.5" />
            <circle cx="12" cy="3.5" r="1.5" />
            <circle cx="12" cy="11.5" r="1.5" />
          </svg>
          <span>Proof map</span></a>
        <a className="result-action result-edit"
          href={`${data.source.repository}/edit/main/${node.source}`
            + `#L${node.line}-L${node.endLine ?? node.line}`}
          target="_blank" rel="noreferrer"
          aria-label={`Edit ${node.kind} ${node.number} on GitHub`}>
          <svg viewBox="0 0 16 14" aria-hidden="true">
            <path d="m2.5 11.5.8-3.1 7-7 2.3 2.3-7 7-3.1.8ZM9.4 2.3l2.3 2.3" />
          </svg>
          <span>Edit</span></a>
      </nav>
      <div className="result-lead">
        <h2 className="result-heading">
          <a className="result-number" href={`#${resultPath(node)}`}
            aria-label={`Permalink to ${node.kind} ${node.number}`}>
            {node.kind} {node.number}</a>{' '}
          <span className="result-title"
            dangerouslySetInnerHTML={{ __html: `(${node.titleHtml})` }} /></h2>
        <div className="statement" dangerouslySetInnerHTML={{ __html: node.statement }} />
      </div>
      <div className="proof" dangerouslySetInnerHTML={{ __html: node.proof }} />
      <SourceSlot source={active ? node.leanSource : undefined} metadata={metadata} />
    </div>
  </article>;
});

function ResultCollection({ data, nodes, selected }: {
  data: BlueprintData;
  nodes: BlueprintNode[];
  selected?: BlueprintNode;
}) {
  const [metadata, setMetadata] = useState<Record<string, LeanProofMetadata>>({});
  const preview = useResultPreview();
  const requested = useRef(new Set<string>());
  const loadMetadata = useCallback((node: string) => {
    const file = data.proofBundles[node];
    if (!file || requested.current.has(node)) return;
    requested.current.add(node);
    void loadProofBundle(data, node).then(bundle => {
      const value = bundle.nodes[node];
      if (value) setMetadata(current => ({ ...current, [node]: value }));
    }).catch(error => {
      requested.current.delete(node);
      console.error(error);
    });
  }, [data]);
  const result = (node: BlueprintNode, index: number) => <Result key={node.id}
    data={data} node={node} metadata={metadata[node.id]} loadMetadata={loadMetadata}
    selected={selected?.id === node.id}
    eager={index < 2}
    onPreview={preview.show} closePreview={preview.close} />;
  return <><section className="result-list">{nodes.map(result)}</section>
    <ResultPreview data={data} target={preview.target} /></>;
}

function Chapter({ data, phase, selected }: {
  data: BlueprintData;
  phase: string;
  selected?: BlueprintNode;
}) {
  const nodes = data.nodes.filter(node => node.phase === phase);
  const metadata = phaseMetadata(data, phase);
  return <><header className="phase-header"><h1>{phaseIndex(data, phase) + 1}. {metadata.title}</h1>
    <Introduction text={metadata.description} /></header>
    <ResultCollection data={data} nodes={nodes} selected={selected} /></>;
}

function Search({ data, close }: { data: BlueprintData; close: () => void }) {
  const [query, setQuery] = useState('');
  const [activeIndex, setActiveIndex] = useState(-1);
  const activeOption = useRef<HTMLButtonElement>(null);
  const normalized = query.toLocaleLowerCase();
  const results = data.nodes.map((node, order) => ({
    node,
    order,
    titleStartsWithQuery: node.title.toLocaleLowerCase().indexOf(normalized) === 0,
  })).filter(({ node }) => `${node.number} ${node.kind} ${node.title} ${node.name}`
    .toLocaleLowerCase().includes(normalized))
    .sort((left, right) => Number(right.titleStartsWithQuery) - Number(left.titleStartsWithQuery)
      || left.order - right.order)
    .slice(0, 40).map(({ node }) => node);
  useLayoutEffect(() => {
    activeOption.current?.scrollIntoView({ block: 'nearest' });
  }, [activeIndex]);
  const choose = (node: BlueprintNode) => {
    close();
    navigate(resultPath(node));
  };
  const move = (step: 1 | -1) => {
    if (!results.length) return;
    setActiveIndex(current => current < 0
      ? (step === 1 ? 0 : results.length - 1)
      : (current + step + results.length) % results.length);
  };
  return <div className="search-backdrop" onMouseDown={event => event.target === event.currentTarget && close()}>
    <section className="search-dialog react-search" role="dialog" aria-modal="true">
      <header className="dialog-heading"><label htmlFor="search">Search the results</label>
        <button className="dialog-close" onClick={close}>Close</button></header>
      <input id="search" autoFocus type="search" role="combobox" aria-autocomplete="list"
        aria-expanded="true" aria-controls="search-results"
        aria-activedescendant={activeIndex < 0 ? undefined
          : `search-result-${results[activeIndex]?.number}`}
        value={query} onChange={event => {
          setQuery(event.target.value);
          setActiveIndex(-1);
        }}
        onKeyDown={event => {
          if (event.key === 'ArrowDown') { event.preventDefault(); move(1); }
          else if (event.key === 'ArrowUp') { event.preventDefault(); move(-1); }
          else if (event.key === 'Home' && results.length) {
            event.preventDefault(); setActiveIndex(0);
          } else if (event.key === 'End' && results.length) {
            event.preventDefault(); setActiveIndex(results.length - 1);
          } else if (event.key === 'Enter' && activeIndex >= 0) {
            event.preventDefault(); choose(results[activeIndex]);
          } else if (event.key === 'Escape') close();
        }} />
      <ol id="search-results" className="search-results" role="listbox">
        {results.map((node, index) => <li key={node.id}><button
          ref={activeIndex === index ? activeOption : null}
          id={`search-result-${node.number}`} role="option" tabIndex={-1}
          aria-selected={activeIndex === index}
          onMouseEnter={() => setActiveIndex(index)} onClick={() => choose(node)}>
          <small>{node.kind} {node.number} · {phaseMetadata(data, node.phase).title}</small>
          <strong dangerouslySetInnerHTML={{ __html: node.titleHtml }} /></button></li>)}</ol>
    </section>
  </div>;
}

export default function App() {
  const data = useMemo(readBlueprintData, []);
  const [route, setRoute] = useState(() => parseRoute(data));
  const [search, setSearch] = useState(false);
  useEffect(() => {
    let pageScrolling = false;
    let release: number | undefined;
    const markPageScrolling = () => {
      pageScrolling = true;
      if (release !== undefined) window.clearTimeout(release);
      release = window.setTimeout(() => {
        pageScrolling = false;
        release = undefined;
      }, 140);
    };
    const keepScrollingPage = (event: WheelEvent) => {
      const target = event.target instanceof Element ? event.target : undefined;
      if (!pageScrolling || !target?.closest('.lean-source-body > pre, .lean-goal-pane')) return;
      const scale = event.deltaMode === WheelEvent.DOM_DELTA_LINE ? 16
        : event.deltaMode === WheelEvent.DOM_DELTA_PAGE ? window.innerHeight : 1;
      event.preventDefault();
      window.scrollBy(event.deltaX * scale, event.deltaY * scale);
    };
    window.addEventListener('scroll', markPageScrolling, { passive: true });
    window.addEventListener('wheel', keepScrollingPage, { capture: true, passive: false });
    return () => {
      window.removeEventListener('scroll', markPageScrolling);
      window.removeEventListener('wheel', keepScrollingPage, { capture: true });
      if (release !== undefined) window.clearTimeout(release);
    };
  }, []);
  useEffect(() => {
    const restore = () => setRoute(parseRoute(data));
    window.addEventListener('hashchange', restore);
    return () => window.removeEventListener('hashchange', restore);
  }, [data]);
  useEffect(() => {
    const update = (event: KeyboardEvent) => {
      document.documentElement.classList.toggle('is-source-navigation', event.metaKey || event.ctrlKey);
    };
    const clear = () => document.documentElement.classList.remove('is-source-navigation');
    window.addEventListener('keydown', update);
    window.addEventListener('keyup', update);
    window.addEventListener('blur', clear);
    return () => {
      window.removeEventListener('keydown', update);
      window.removeEventListener('keyup', update);
      window.removeEventListener('blur', clear);
      clear();
    };
  }, []);
  const map = isMapRoute(route);
  const content = route.kind === 'highlights' ? <Highlights data={data} />
    : route.kind === 'statements' ? <FormalStatements data={data} />
    : route.kind === 'references' ? <References data={data} />
    : route.kind === 'chapter' ? <Chapter key={route.phase} data={data} phase={route.phase} />
      : route.kind === 'result' ? <Chapter key={route.node.phase} data={data}
        phase={route.node.phase} selected={route.node} />
        : <MapView data={data} phase={route.node.phase} focused={route.node} />;
  useLayoutEffect(() => {
    let frame = 0;
    let attempts = 0;
    if (!hasPendingNodePosition() && (route.kind === 'result' || route.kind === 'map')) {
      requestNodePosition(route.node, route.kind === 'map' ? 'center' : 'start');
    }
    const settle = () => {
      if (hasPendingNodePosition()) {
        if (!restorePendingNodePosition() && attempts++ < 90) frame = requestAnimationFrame(settle);
        else if (hasPendingNodePosition()) restorePendingNodePosition(true);
        return;
      }
      if (route.kind !== 'result' && route.kind !== 'map') window.scrollTo(0, 0);
    };
    frame = requestAnimationFrame(settle);
    return () => cancelAnimationFrame(frame);
  }, [route]);
  const hasReaderBar = route.kind === 'map';
  return <><div className={`page-shell${hasReaderBar ? ' has-reader-bar' : ''}${
    map ? ' is-map' : ''}`}>
    <ReaderBar route={route} />
    <Sidebar data={data} route={route} onSearch={() => setSearch(true)} />
    <main className={map ? 'map-reader' : 'reader'}>{content}</main></div>
    {search && <Search data={data} close={() => setSearch(false)} />}</>;
}
