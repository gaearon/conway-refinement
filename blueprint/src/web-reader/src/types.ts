export type BlueprintNode = {
  id: string;
  name: string;
  number: number;
  kind: string;
  phase: string;
  title: string;
  titleHtml: string;
  highlight: boolean;
  source: string;
  line: number;
  endLine?: number;
  dependencies: string[];
  proofDependencies: string[];
  statement: string;
  proof: string;
  leanSource?: {
    name: string;
    displayName: string;
    line: number;
    endLine: number;
    url: string;
    html: string;
  };
};

export type BlueprintPhase = {
  id: string;
  title: string;
  description: string;
};

export type BlueprintData = {
  highlights: {
    title: string;
    description: string;
  };
  phases: BlueprintPhase[];
  source: {
    repository: string;
    revision: string;
    published: boolean;
  };
  references: Array<{
    key: string;
    authors: string;
    title: string;
    url?: string;
    venue: string;
    volume?: string;
    year?: string;
    details?: string;
    kind: 'article' | 'book' | 'preprint';
  }>;
  standaloneStatements: Array<{
    key: string;
    title: string;
    description: string;
    leanSource: LeanSource;
    proofSource: LeanSource;
  }>;
  proofBundles: Record<string, string>;
  nodes: BlueprintNode[];
};

export type LeanReference = {
  name: string;
  module: string;
  signature: string;
  docs: string;
  url: string;
};

export type LeanState = {
  start: number;
  end: number;
  goals: string[];
};

export type LeanMessage = {
  start: number;
  end: number;
  severity: string;
  text: string;
};

export type LeanSource = {
  name: string;
  displayName: string;
  line: number;
  endLine: number;
  url: string;
  html: string;
  goals: Record<string, string>;
  states: LeanState[];
  references: Record<string, LeanReference>;
  messages?: LeanMessage[];
};

export type LeanProofMetadata = Pick<LeanSource, 'goals' | 'states' | 'references'>;

export type ProofBundle = { nodes: Record<string, LeanProofMetadata> };
