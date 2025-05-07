import { LitElement, html, css } from 'lit';
import { customElement, property } from 'lit/decorators.js';

@customElement('microwave-graphic')
export class MicrowaveGraphic extends LitElement {
  static styles = css`
    :host {
      display: block;
      width: 300px;
      height: 200px;
      background: #f0f0f0;
      border: 2px solid #333;
      border-radius: 10px;
      position: relative;
      overflow: hidden;
    }

    .door {
      position: absolute;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      background: #ddd;
      transform-origin: left;
      transition: transform 0.3s ease-in-out;
    }

    .door.open {
      transform: rotateY(-90deg);
    }

    .display {
      position: absolute;
      top: 20px;
      left: 50%;
      transform: translateX(-50%);
      background: #000;
      color: #0f0;
      padding: 10px 20px;
      border-radius: 5px;
      font-family: monospace;
      font-size: 24px;
      z-index: 2;
    }

    .waves {
      position: absolute;
      top: 50%;
      left: 50%;
      transform: translate(-50%, -50%);
      width: 80%;
      height: 60%;
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
      bottom: 20px;
      left: 50%;
      transform: translateX(-50%);
      color: #f00;
      font-size: 20px;
      opacity: 0;
      transition: opacity 0.5s ease-in-out;
      z-index: 2;
    }

    .beep.active {
      opacity: 1;
      animation: blink 1s infinite;
    }

    @keyframes blink {
      0% { opacity: 1; }
      50% { opacity: 0; }
      100% { opacity: 1; }
    }
  `;

  @property({ type: Boolean }) doorOpen = false;
  @property({ type: Boolean }) heating = false;
  @property({ type: Boolean }) beeping = false;
  @property({ type: Number }) time = 0;

  render() {
    return html`
      <div class="door ${this.doorOpen ? 'open' : ''}"></div>
      <div class="display">${String(this.time).padStart(2, '0')}</div>
      <div class="waves ${this.heating ? 'active' : ''}"></div>
      <div class="beep ${this.beeping ? 'active' : ''}">BEEP!</div>
    `;
  }
}
