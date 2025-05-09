import { LitElement, html, css } from 'lit';
import { customElement, property } from 'lit/decorators.js';

@customElement('microwave-graphic')
export class MicrowaveGraphic extends LitElement {
  static styles = css`
    :host {
      display: grid;
      width: var(--mw-width, 600px);
      height: var(--mw-height, 370px);
      background: #f0f0f0;
      border: 2px solid #333;
      border-radius: 10px;
      overflow: hidden;
      grid-template-columns: 3fr 1fr;
      grid-template-rows: auto 1fr;
    }

    .door {
      grid-column: 1;
      grid-row: 1 / span 2;
      background: #ddd;
      transform-origin: left;
      transition: transform 0.3s ease-in-out;
      position: relative;
    }
    .door.open {
      transform: rotateY(-90deg);
    }

    /* digit box */
    .display {
      grid-column: 2;
      grid-row: 1;
      justify-self: end;
      align-self: start;
      background: #000;
      color: #0f0;
      padding: 5px 10px;
      border-radius: 4px;
      font-family: monospace;
      font-size: 18px;
      margin: 8px;
      z-index: 2;
      /* ensure fixed size so digits never push layout */
      min-width: 60px;
      text-align: center;
    }

    .waves {
      position: absolute;
      top: 50%;
      left: 50%;
      width: 80%;
      height: 60%;
      transform: translate(-50%, -50%);
      background: repeating-linear-gradient(
        45deg,
        rgba(255, 0, 0, 0.1),
        rgba(255, 0, 0, 0.1) 10px,
        rgba(255, 0, 0, 0.2) 10px,
        rgba(255, 0, 0, 0.2) 20px
      );
      opacity: 0;
      transition: opacity 0.3s ease-in-out;
      z-index: 1;
    }
    .waves.active {
      opacity: 1;
    }

    .beep {
      position: absolute;
      bottom: 10px;
      left: 50%;
      transform: translateX(-50%);
      font-size: 16px;
      color: #f00;
      opacity: 0;
      transition: opacity 0.5s ease-in-out;
      z-index: 2;
    }
    .beep.active {
      opacity: 1;
      animation: blink 1s infinite;
    }
    @keyframes blink {
      0%,100% { opacity: 1; }
      50% { opacity: 0; }
    }

    .controls {
      grid-column: 2;
      grid-row: 2;
      display: flex;
      flex-direction: column;
      align-items: center;
      justify-content: center;
      gap: 8px;
      padding: 0 8px;
    }
  `;

  @property({ type: Boolean }) doorOpen = false;
  @property({ type: Boolean }) heating = false;
  @property({ type: Boolean }) beeping = false;
  @property({ type: Number }) time = 0;  // in seconds

  private formatTime(seconds: number): string {
    const m = Math.floor(seconds / 60);
    const s = seconds % 60;
    const mm = String(m).padStart(2, '0');
    const ss = String(s).padStart(2, '0');
    return `${mm}:${ss}`;
  }

  render() {
    return html`
      <div class="door ${this.doorOpen ? 'open' : ''}">
        <div class="waves ${this.heating ? 'active' : ''}"></div>
        <div class="beep ${this.beeping ? 'active' : ''}">BEEP!</div>
      </div>
      <div class="display">${this.formatTime(this.time)}</div>
      <div class="controls">
        <slot name="buttons"></slot>
      </div>
    `;
  }
}
