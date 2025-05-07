import { LitElement, html, css } from 'lit';
import { customElement, property } from 'lit/decorators.js';

@customElement('microwave-graphic')
export class MicrowaveGraphic extends LitElement {
  @property({ type: Boolean }) doorOpen = false;
  @property({ type: Boolean }) heating = false;
  @property({ type: Number }) time = 0;

  static styles = css`
    :host {
      display: block;
      width: 400px;
      height: 220px;
      position: relative;
      border: 6px solid #444;
      border-radius: 12px;
      background: #eee;
      box-shadow: 0 4px 16px rgba(0,0,0,0.15);
    }
    .door {
      position: absolute;
      top: 10%;
      left: 5%;
      width: 55%;
      height: 80%;
      background: linear-gradient(145deg, #f5f5f5, #ddd);
      border: 3px inset #999;
      transform-origin: left center;
      transition: transform 0.5s ease;
    }
    :host([doorOpen]) .door {
      transform: perspective(300px) rotateY(-75deg);
    }
    .timer {
      position: absolute;
      top: 16px;
      right: 16px;
      width: 72px;
      height: 32px;
      background: #222;
      color: #0f0;
      font-family: monospace;
      font-size: 1.1rem;
      display: flex;
      align-items: center;
      justify-content: center;
      border-radius: 4px;
    }
    .wave {
      position: absolute;
      width: 36px;
      height: 16px;
      border-radius: 50%/60%;
      background: linear-gradient(90deg, #ff5722 60%, transparent);
      opacity: 0;
      animation: wave 1s infinite ease-in-out;
    }
    .wave:nth-child(1) { top: 35%; left: 23%; animation-delay: 0s }
    .wave:nth-child(2) { top: 53%; left: 33%; animation-delay: 0.2s }
    .wave:nth-child(3) { top: 71%; left: 43%; animation-delay: 0.4s }

    @keyframes wave {
      0%   { opacity: 0 }
      50%  { opacity: 1; transform: translateX(8px) }
      100% { opacity: 0; transform: translateX(16px) }
    }
    :host([heating]) .wave { display: block }
    :host(:not([heating])) .wave { display: none }
  `;

  render() {
    const mm = String(Math.floor(this.time/60)).padStart(2,'0');
    const ss = String(this.time%60).padStart(2,'0');
    return html`
      <div class="door"></div>
      <div class="timer">${mm}:${ss}</div>
      <div class="wave"></div>
      <div class="wave"></div>
      <div class="wave"></div>
    `;
  }
}
