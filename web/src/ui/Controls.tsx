import { Vars } from '../model/state';
import { Actions } from '../checker/spec';
import { Engine } from '../sim/engine';

const BUTTON_LABELS: Record<string, string> = {
  TogglePower: 'Power',
  IncrementTime: '+3s',
  Start: 'Start',
  Cancel: 'Cancel',
  OpenDoor: 'Open door',
  CloseDoor: 'Close door',
  Tick: 'Tick (manual)',
};

const BUTTON_ORDER = [
  'TogglePower',
  'IncrementTime',
  'Start',
  'Cancel',
  'OpenDoor',
  'CloseDoor',
  'Tick',
];

export function Controls({ engine, v }: { engine: Engine; v: Vars }) {
  return (
    <div className="mw-controls">
      {BUTTON_ORDER.map(name => {
        const a = Actions.find(x => x.name === name);
        if (!a) return null;
        const enabled = a.enabled(v);
        return (
          <button
            key={name}
            className="mw-btn"
            disabled={!enabled}
            onClick={() => engine.dispatch(name)}
            title={
              enabled
                ? `Fire action ${name}`
                : `Action ${name} is not enabled in the current state`
            }
          >
            {BUTTON_LABELS[name] ?? name}
          </button>
        );
      })}
    </div>
  );
}
