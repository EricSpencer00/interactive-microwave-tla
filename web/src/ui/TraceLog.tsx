import { TraceRow } from '../sim/engine';

const fmtVars = (v: TraceRow['to']) =>
  `door=${v.door.toLowerCase()}, time=${v.time}, radiation=${v.radiation.toLowerCase()}, power=${v.power.toLowerCase()}`;

export function TraceLog({
  trace,
  showStutter,
}: {
  trace: readonly TraceRow[];
  showStutter: boolean;
}) {
  const rows = showStutter ? trace : trace.filter(r => !r.stutter);

  return (
    <div className="mw-trace">
      <div className="mw-trace-header">TLA+ trace — {trace.length} total ({rows.length} shown)</div>
      <ol className="mw-trace-list">
        {rows.slice().reverse().map((r, i) => (
          <li
            key={`${r.t}-${i}`}
            className={`mw-trace-row ${r.stutter ? 'stutter' : ''} ${!r.safe ? 'violation' : ''}`}
          >
            <span className="mw-trace-name">
              {r.stutter ? '(stutter) vars′ = vars' : `\\* ${r.name}`}
            </span>
            <span className="mw-trace-state">{fmtVars(r.to)}</span>
          </li>
        ))}
      </ol>
    </div>
  );
}
