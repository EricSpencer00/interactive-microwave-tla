import { describe, it, expect } from 'vitest';
import {
  stutterTrapDetected,
  trailingStutterWhileRadiating,
  STUTTER_TRAP_THRESHOLD,
} from '../liveness';
import { Vars } from '../../model/state';

// Minimal trace-row shape the checker needs.
type R = { stutter: boolean; to: Vars };
const radiating: Vars = { door: 'CLOSED', time: 5, radiation: 'ON', power: 'ON' };
const idle: Vars = { door: 'CLOSED', time: 0, radiation: 'OFF', power: 'OFF' };

describe('HeatLiveness violation detection', () => {
  it('zero trailing stutter in an empty trace', () => {
    expect(trailingStutterWhileRadiating([])).toBe(0);
  });

  it('zero trailing stutter when last row is a real action', () => {
    const trace: R[] = [{ stutter: false, to: radiating }];
    expect(trailingStutterWhileRadiating(trace)).toBe(0);
  });

  it('counts a run of stutter rows while radiating', () => {
    const trace: R[] = Array.from({ length: 4 }, () => ({ stutter: true, to: radiating }));
    expect(trailingStutterWhileRadiating(trace)).toBe(4);
    expect(stutterTrapDetected(trace)).toBe(true);
  });

  it('resets the count when radiation turns off', () => {
    const trace: R[] = [
      { stutter: true, to: radiating },
      { stutter: true, to: radiating },
      { stutter: true, to: idle },
    ];
    // Last row is idle, so trailing stutter while radiating is 0.
    expect(trailingStutterWhileRadiating(trace)).toBe(0);
    expect(stutterTrapDetected(trace)).toBe(false);
  });

  it('threshold is conservative (>= 3 is a trap for demo purposes)', () => {
    expect(STUTTER_TRAP_THRESHOLD).toBeGreaterThanOrEqual(2);
  });
});
