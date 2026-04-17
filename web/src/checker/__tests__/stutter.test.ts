import { describe, it, expect } from 'vitest';
import { Stutter, NextWithStutter, STUTTER_NAME } from '../stutter';
import { Init, Vars, eqVars } from '../../model/state';
import { Safe } from '../spec';

describe('stuttering semantics of [Next]_vars', () => {
  it('Stutter leaves vars unchanged (vars = vars)', () => {
    expect(eqVars(Stutter.step(Init), Init)).toBe(true);
  });

  it('Stutter is always enabled', () => {
    expect(Stutter.enabled(Init)).toBe(true);
    const other: Vars = { door: 'OPEN', time: 10, radiation: 'OFF', power: 'ON' };
    expect(Stutter.enabled(other)).toBe(true);
  });

  it('[Next]_vars always includes a stutter step', () => {
    expect(NextWithStutter(Init).some(s => s.name === STUTTER_NAME)).toBe(true);
  });

  it('Safe is closed under stuttering: Safe(v) iff Safe(Stutter(v))', () => {
    const safeState: Vars = { door: 'CLOSED', time: 5, radiation: 'ON', power: 'ON' };
    expect(Safe(Stutter.step(safeState))).toBe(Safe(safeState));

    const unsafeState: Vars = { door: 'OPEN', time: 5, radiation: 'ON', power: 'ON' };
    expect(Safe(Stutter.step(unsafeState))).toBe(Safe(unsafeState));
  });

  it('[Next]_vars is never empty (no deadlock in the TLA+ sense)', () => {
    // Even when no real action is enabled, stutter is always available.
    const quiesced: Vars = { door: 'CLOSED', time: 0, radiation: 'OFF', power: 'OFF' };
    expect(NextWithStutter(quiesced).length).toBeGreaterThan(0);
  });
});
