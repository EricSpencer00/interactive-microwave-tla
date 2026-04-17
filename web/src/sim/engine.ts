// Engine: owns the current Vars, dispatches user actions, and runs a tick
// loop that emits an explicit stutter row whenever no real action fires.
// This is the runtime half of the stuttering fix — the spec change lives in
// checker/stutter.ts; the engine makes it visible in the trace.

import { Vars, Init } from '../model/state';
import { Actions } from '../checker/spec';
import { Stutter, STUTTER_NAME } from '../checker/stutter';

export interface TraceRow {
  t: number;
  name: string;
  from: Vars;
  to: Vars;
  safe: boolean;
  stutter: boolean;
}

type Listener = () => void;

const isSafe = (v: Vars) => !(v.radiation === 'ON' && v.door === 'OPEN');
const MAX_TRACE = 500;

export class Engine {
  private v: Vars = { ...Init };
  private trace: TraceRow[] = [];
  private listeners = new Set<Listener>();
  private tickHandle: ReturnType<typeof setInterval> | undefined;
  public showStutter = true;

  getState(): Vars {
    return this.v;
  }
  getTrace(): readonly TraceRow[] {
    return this.trace;
  }
  subscribe(fn: Listener): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }
  private notify() {
    this.listeners.forEach(l => l());
  }

  /** Returns true iff the named action was enabled and fired. */
  dispatch(name: string): boolean {
    const action = Actions.find(a => a.name === name);
    if (!action || !action.enabled(this.v)) return false;
    const from = this.v;
    const to = action.step(this.v);
    this.v = to;
    this.push(name, from, to, false);
    this.notify();
    return true;
  }

  startTickLoop() {
    if (this.tickHandle !== undefined) return;
    this.tickHandle = setInterval(() => this.onTick(), 1000);
  }

  stopTickLoop() {
    if (this.tickHandle !== undefined) {
      clearInterval(this.tickHandle);
      this.tickHandle = undefined;
    }
  }

  /**
   * One tick of wall-clock time. If radiation is on and Tick is enabled we
   * fire Tick; otherwise we emit a stutter step. Either way the trace picks
   * up a row, so behaviors render as alternating action/stutter rather than
   * as "nothing happened".
   */
  private onTick() {
    const tick = Actions.find(a => a.name === 'Tick')!;
    if (this.v.radiation === 'ON' && tick.enabled(this.v)) {
      const from = this.v;
      const to = tick.step(this.v);
      this.v = to;
      this.push('Tick', from, to, false);
    } else {
      const from = this.v;
      const to = Stutter.step(this.v);
      // v is already equal to to; we still "transition" so the trace records it.
      this.v = to;
      this.push(STUTTER_NAME, from, to, true);
    }
    this.notify();
  }

  private push(name: string, from: Vars, to: Vars, stutter: boolean) {
    this.trace.push({ t: Date.now(), name, from, to, safe: isSafe(to), stutter });
    if (this.trace.length > MAX_TRACE) {
      this.trace.splice(0, this.trace.length - MAX_TRACE);
    }
  }

  reset() {
    this.v = { ...Init };
    this.trace = [];
    this.notify();
  }

  setShowStutter(show: boolean) {
    this.showStutter = show;
    this.notify();
  }
}
