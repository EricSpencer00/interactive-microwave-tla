import { describe, it, expect } from 'vitest';
import { Next, Safe } from '../spec';
import { Init, Vars } from '../../model/state';

describe('Microwave Next', () => {
  it('TogglePower is enabled from Init and flips power', () => {
    const tp = Next(Init).find(s => s.name === 'TogglePower');
    expect(tp).toBeDefined();
    expect(tp!.v2.power).toBe('ON');
    expect(tp!.v2.door).toBe('CLOSED');
    expect(tp!.v2.time).toBe(0);
    expect(tp!.v2.radiation).toBe('OFF');
  });

  it('Start requires time>0, door closed, power on', () => {
    expect(Next(Init).some(s => s.name === 'Start')).toBe(false);
    const ready: Vars = { door: 'CLOSED', time: 3, radiation: 'OFF', power: 'ON' };
    expect(Next(ready).some(s => s.name === 'Start')).toBe(true);
  });

  it('OpenDoor forces radiation OFF', () => {
    const heating: Vars = { door: 'CLOSED', time: 5, radiation: 'ON', power: 'ON' };
    const od = Next(heating).find(s => s.name === 'OpenDoor');
    expect(od!.v2.door).toBe('OPEN');
    expect(od!.v2.radiation).toBe('OFF');
  });

  it('Tick turns radiation OFF when time hits 0', () => {
    const last: Vars = { door: 'CLOSED', time: 1, radiation: 'ON', power: 'ON' };
    const t = Next(last).find(s => s.name === 'Tick');
    expect(t!.v2.time).toBe(0);
    expect(t!.v2.radiation).toBe('OFF');
  });

  it('IncrementTime leaves door/radiation/power unchanged', () => {
    const it_ = Next(Init).find(s => s.name === 'IncrementTime');
    expect(it_!.v2.time).toBe(3);
    expect(it_!.v2.door).toBe(Init.door);
    expect(it_!.v2.radiation).toBe(Init.radiation);
    expect(it_!.v2.power).toBe(Init.power);
  });

  it('Safe rejects radiation ON with door OPEN', () => {
    expect(Safe({ door: 'OPEN', time: 5, radiation: 'ON', power: 'ON' })).toBe(false);
    expect(Safe(Init)).toBe(true);
  });
});
