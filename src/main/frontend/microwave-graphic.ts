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

      /* 75% for door, 25% for controls */
      grid-template-columns: 3fr 1fr;
      /* single row layout */
      grid-template-rows: auto 1fr;
      gap: 0;
    }

    /* Door takes the full left side (all rows) */
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

    /* Timer/display in top-right cell */
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
    }

    /* Waves overlay inside the door area */
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

    /* Beep indicator under the door area */
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

    /* Controls slot on the right, middle cell */
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
  @property({ type: Number }) time = 0;

  render() {
    return html`
      <div class="door ${this.doorOpen ? 'open' : ''}">
        <div class="waves ${this.heating ? 'active' : ''}"></div>
        <div class="beep ${this.beeping ? 'active' : ''}">BEEP!</div>
      </div>
      <div class="display">${String(this.time).padStart(2, '0')}</div>
      <div class="controls">
        <!-- Expect your buttons to be slotted in from the outside -->
        <slot name="buttons"></slot>
      </div>
    `;
  }
}
