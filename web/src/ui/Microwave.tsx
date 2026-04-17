import { Vars } from '../model/state';

export function Microwave({ v }: { v: Vars }) {
  const radiating = v.radiation === 'ON';
  const open = v.door === 'OPEN';
  const powered = v.power === 'ON';
  const unsafe = radiating && open;

  return (
    <div className={`mw-device ${radiating ? 'is-radiating' : ''} ${open ? 'is-open' : ''}`}>
      <div className="mw-screen">
        <span className="mw-time">
          {v.time.toString().padStart(2, '0')}
          <span className="mw-unit">s</span>
        </span>
        <div className="mw-indicators">
          <span className={`mw-dot ${powered ? 'on' : ''}`} title="power">PWR</span>
          <span className={`mw-dot ${radiating ? 'on' : ''}`} title="radiation">RAD</span>
        </div>
      </div>
      <div className={`mw-cavity ${open ? 'open' : 'closed'}`}>
        <div className="mw-glow" aria-hidden />
        <div className="mw-door" aria-label={`door ${v.door.toLowerCase()}`} />
      </div>
      {unsafe && (
        <div className="mw-violation" role="alert">
          ⚠ Safe violation: radiation ON with door OPEN
        </div>
      )}
    </div>
  );
}
