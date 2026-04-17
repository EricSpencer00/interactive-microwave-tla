// The stuttering fix.
//
// Spec == Init /\ [][Next]_vars
//
// The [Next]_vars square-bracket form admits two kinds of step:
//   1. A Next step (one of the action disjuncts), OR
//   2. A stuttering step where vars' = vars.
//
// The previous web simulator only ever emitted (1), so users never saw
// stuttering. This module makes (2) explicit as a pseudo-action so the
// trace view and engine can emit it when no real action fires.

import { Vars } from '../model/state';
import { Action, Next } from './spec';

export const STUTTER_NAME = '(stutter)';

export const Stutter: Action = {
  name: STUTTER_NAME,
  enabled: () => true,
  // vars' = vars — return a new object so identity comparisons don't lie,
  // but every field is equal to the predecessor.
  step: v => ({ ...v }),
};

// [Next]_vars realized as concrete successor list.
// Real actions first, stutter last, matching the "action-or-stutter" reading.
export const NextWithStutter = (v: Vars): { name: string; v2: Vars }[] => [
  ...Next(v),
  { name: Stutter.name, v2: Stutter.step(v) },
];
