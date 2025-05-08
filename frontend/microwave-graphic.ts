// ./frontend/microwave-graphic.ts
import { html, css, LitElement } from 'lit';
import { customElement, property } from 'lit/decorators.js';

@customElement('microwave-graphic')
export class MicrowaveGraphic extends LitElement {
doorOpen: boolean = false;
heating: boolean = false;
beeping: boolean = false;
time: number = 0;

static styles = css`
  .microwave {
    border: 3px solid #444;
    width: 200px;
    height: 150px;
    background-color: #000;
    color: white;
    padding: 1em;
    border-radius: 10px;
    position: relative;
  }

  .door {
    background: #888
    width: 80%;
    height: 100%;
    margin: auto;
    display: flex;
    align-items: center;
    justify-content: center;
    transition: transform 0.3s ease;
  }

  .door.open {
    transform: rotateY(60deg);
  }

  .heating-light {
    position: absolute;
    top: 10px;
    right: 10px;
    width: 15px;
    height: 15px;
    border-radius: 50%;
    background: red;
    opacity: 0.3;
  }

  .heating-light.on {
    opacity: 1;
  }

  .time-display {
    margin-top: 1em;
    font-size: 1.2em;
  }
`;

  render() {
    return html`
    <div class="microwave">
      <div class="door ${this.doorOpen ? 'open' : ''}">
        ${this.doorOpen ? 'Open' : 'Closed'}
      </div>
      <div class="heating-light ${this.heating ? 'on' : ''}"></div>
      <div class="time-display">Time: ${this.time}s</div>
    </div>
  `;
  }
}
