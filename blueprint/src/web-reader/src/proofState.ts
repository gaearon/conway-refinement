import type { LeanState } from './types';

export function stateAtOffset(states: LeanState[], offset: number): LeanState | null {
  return states.find(state => state.start <= offset && offset < state.end) ?? null;
}
