// TS port of Microwave.tla VARIABLES (lines 4-12).
// These four variables are the full state of the model.
export type DoorState = 'OPEN' | 'CLOSED';
export type OnOff = 'ON' | 'OFF';

export const MAX_TIME = 60;

export interface Vars {
  door: DoorState;
  time: number;
  radiation: OnOff;
  power: OnOff;
}

// Init == /\ door = CLOSED /\ time = 0 /\ radiation = OFF /\ power = OFF
export const Init: Vars = {
  door: 'CLOSED',
  time: 0,
  radiation: 'OFF',
  power: 'OFF',
};

export const eqVars = (a: Vars, b: Vars): boolean =>
  a.door === b.door && a.time === b.time && a.radiation === b.radiation && a.power === b.power;
