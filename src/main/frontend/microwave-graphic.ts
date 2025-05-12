import { LitElement, html, css } from 'lit';
import { customElement, property } from 'lit/decorators.js';

@customElement('microwave-graphic')
export class MicrowaveGraphic extends LitElement {
  static styles = css`
    :host([powerOn]) .door-window { /* maybe full-color glass */ }

    :host {
      display: block;
      flex: 0 0 auto;
      width: 700px;
      height: 500px;
      background: #f0f0f0;
      border: 2px solid #333;
      border-radius: 10px;
      position: relative;
      overflow: hidden;
    }

    .microwave-container {
      position: absolute;
      top: 50%;
      left: 50%;
      transform: translate(-50%, -50%);
      width: 600px;
      height: 370px;
      display: grid;
      grid-template-columns: 2fr 1fr;
      grid-template-rows: auto 1fr;
    }

    .food {
      position: absolute;
      top: 0;
      left: 0;
      width: calc(2 / 3 * 100%);
      height: 100%;
      background: url('/images/chicken+rice.png') center center / cover no-repeat;
      z-index: 1;
      pointer-events: none;
    }

    /* the rotating “door” container */
    .door {
      position: absolute;
      top: 0; left: 0;
      width: calc(2/3 * 100%);
      height: 100%;
      transform-origin: left center;
      transform-style: preserve-3d;
      transition: transform 0.3s ease-in-out;
      z-index: 2;
      /* no background or border here any more */
    }

    /* each “frame” piece is one side of the door */
    .frame {
      position: absolute;
      background: #e5e5e5;
      border: 3px solid #333;
      z-index: 3;
    }

    /* top bar */
    .frame.top {
      top: 0; left: 0;
      width: 100%; height: 25%;
      border-bottom: none;
      border-radius: 6px 6px 0 0;
    }

    /* bottom bar */
    .frame.bottom {
      bottom: 0; left: 0;
      width: 100%; height: 25%;
      border-top: none;
      border-radius: 0 0 6px 6px;
    }

    /* left bar */
    .frame.left {
      top: 25%; left: 0;
      width: 20%; height: 50%;
      border-right: none;
    }

    /* right bar */
    .frame.right {
      top: 25%; right: 0;
      width: 20%; height: 50%;
      border-left: none;
    }

    .door-window {
      position: absolute;
      left: 15%;
      top: 20%;
      width: 70%;
      height: 60%;
    
      /* frosted curved glass */
      background: rgba(255,255,255,0.2);
      background-image:
        linear-gradient(
          rgba(255,255,255,0.15),
          rgba(255,255,255,0.05)
        );
      backdrop-filter: blur(4px);
    
      /* subtle thicker border & depth */
      border: 2px solid rgba(255,255,255,0.6);
      box-shadow:
        inset 0 0 6px rgba(0,0,0,0.2),
        0 1px 2px rgba(0,0,0,0.1);
    
      border-radius: 8px;
      z-index: 3;
      pointer-events: none;
      overflow: hidden;
    }
    
    .door-window::before {
      content: '';
      position: absolute;
      top: 6%;
      left: 12%;
      width: 76%;
      height: 8%;
      background: rgba(255,255,255,0.5);
      transform: skewX(-25deg);
      border-radius: 50%/20%;
      pointer-events: none;
    }
    

    /* red tint on heating */
    .door-window.heating {
      background: rgba(255, 0, 0, 0.18);
      border-color: rgba(229, 62, 62, 0.6);
    }


    /* swing it open as before */
    .door.open {
      transform: rotateY(-90deg);
    }


    .door-handle {
      position: absolute;
      right: 20px;
      top: 50%;
      transform: translateY(-50%);
      width: 30px;
      height: 60px;
      background: #666;
      border-radius: 15px;
    }

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
      z-index: 3;
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
      display: grid;
      grid-template-columns: 1fr 1fr;
      grid-template-rows: 1fr 1fr;
      gap: 8px;
      padding: 8px;
      border: 1px solid #333;
      border-radius: 4px;
      margin: 8px;
      min-width: 120px;
      z-index: 3;
    }

    .controls ::slotted(button) {
      width: 100%;
      height: 100%;
      padding: 0;
      border: none;
      border-radius: 4px;
      cursor: pointer;
      transition: all 0.2s ease;
      background-size: cover;
      background-position: center;
      background-repeat: no-repeat;
    }

    .controls ::slotted(button:hover) {
      transform: translateY(-2px);
      box-shadow: 0 2px 4px rgba(0,0,0,0.2);
    }

    .controls ::slotted(button:active) {
      transform: translateY(0);
      box-shadow: none;
    }
  `;

  @property({ type: Boolean }) doorOpen = false;
  @property({ type: Boolean }) heating = false;
  @property({ type: Boolean }) beeping = false;
  @property({ type: Number }) time = 0;

  private formatClock(): string {
    const now = new Date();
    const hh = String(now.getHours()).padStart(2, '0');
    const mm = String(now.getMinutes()).padStart(2, '0');
    return `${hh}:${mm}`;
  }

  private formatCountdown(seconds: number): string {
    const m = Math.floor(seconds / 60);
    const s = seconds % 60;
    return `${String(m).padStart(2, '0')}:${String(s).padStart(2, '0')}`;
  }

  render() {
    let displayText: string;
    if (this.beeping) {
      displayText = '00:00';
    } else if (this.time > 0) {
      displayText = this.formatCountdown(this.time);
    } else {
      displayText = this.formatClock();
    }

    return html`
    <div class="microwave-container">
      <div class="food"></div>
      <div class="door ${this.doorOpen ? 'open' : ''}">
        <div class="frame top"></div>
        <div class="frame left"></div>
        <div class="frame right"></div>
        <div class="frame bottom"></div>

        <!-- this only becomes the red tint on heating -->
        <div class="door-window${this.heating ? ' heating' : ''}"></div>
        
        <div class="door-handle"></div>
        <div class="waves ${this.heating ? 'active' : ''}"></div>
        <div class="beep ${this.beeping ? 'active' : ''}">BEEP!</div>
      </div>

      <div class="display">${this.time > 0 ? this.formatCountdown(this.time) : this.formatClock()}</div>
      <div class="controls"><slot name="buttons"></slot></div>
    </div>
  `;
  }
}
