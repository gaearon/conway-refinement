import type { BlueprintData, ProofBundle } from './types';

export function readBlueprintData(): BlueprintData {
  const element = document.getElementById('blueprint-data');
  const value = element?.textContent?.trim();
  if (!value || value === '__BLUEPRINT_DATA__') {
    throw new Error('The checked blueprint data was not embedded in this guide.');
  }
  return JSON.parse(value) as BlueprintData;
}

const cache = new Map<string, Promise<ProofBundle>>();
let decoder: Worker | null = null;
let nextRequest = 0;
const pending = new Map<number, {
  resolve: (bundle: ProofBundle) => void;
  reject: (error: Error) => void;
}>();

function decoderWorker(): Worker {
  if (decoder) return decoder;
  const source = `self.onmessage = async event => {
    const { id, payload } = event.data;
    try {
      const compressed = payload instanceof Uint8Array ? payload : new Uint8Array(payload);
      const stream = new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'));
      const bundle = await new Response(stream).json();
      self.postMessage({ id, bundle });
    } catch (error) {
      self.postMessage({ id, error: error instanceof Error ? error.message : String(error) });
    }
  };`;
  decoder = new Worker(URL.createObjectURL(new Blob([source], { type: 'text/javascript' })));
  decoder.addEventListener('message', event => {
    const request = pending.get(event.data.id as number);
    if (!request) return;
    pending.delete(event.data.id as number);
    if (event.data.error) request.reject(new Error(event.data.error as string));
    else request.resolve(event.data.bundle as ProofBundle);
  });
  decoder.addEventListener('error', event => {
    const error = new Error(event.message || 'Lean source decoder failed.');
    pending.forEach(request => request.reject(error));
    pending.clear();
    decoder?.terminate();
    decoder = null;
  });
  return decoder;
}

async function decodeOnMainThread(payload: Uint8Array): Promise<ProofBundle> {
  const compressed = Uint8Array.from(payload);
  const stream = new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'));
  return new Response(stream).json() as Promise<ProofBundle>;
}

async function decodeBundle(payload: Uint8Array): Promise<ProofBundle> {
  if (!('Worker' in window)) return decodeOnMainThread(payload);
  const id = nextRequest++;
  try {
    return await new Promise<ProofBundle>((resolve, reject) => {
      pending.set(id, { resolve, reject });
      decoderWorker().postMessage({ id, payload });
    });
  } catch {
    pending.delete(id);
    return decodeOnMainThread(payload);
  }
}

export function loadProofBundle(data: BlueprintData, node: string): Promise<ProofBundle> {
  const file = data.proofBundles[node];
  const existing = cache.get(file);
  if (existing) return existing;
  const promise = (async () => {
    const response = await fetch(file);
    if (!response.ok) throw new Error(`Cannot load proof metadata for ${node}.`);
    return decodeBundle(new Uint8Array(await response.arrayBuffer()));
  })();
  cache.set(file, promise);
  return promise;
}
