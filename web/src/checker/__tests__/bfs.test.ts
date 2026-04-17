import { describe, it, expect } from 'vitest';
import { reachable, findViolations } from '../bfs';
import { Init } from '../../model/state';

describe('bounded reachability', () => {
  it('reachable from Init is finite and nonempty', () => {
    const r = reachable(Init);
    expect(r.size).toBeGreaterThan(1);
    // door(2) × rad(2) × power(2) × time(0..60) = 488. Bound generously.
    expect(r.size).toBeLessThan(2000);
  });

  it('no Safe violation is reachable under the real spec', () => {
    expect(findViolations(Init)).toEqual([]);
  });
});
