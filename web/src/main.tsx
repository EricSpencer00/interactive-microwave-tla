import React from 'react';
import ReactDOM from 'react-dom/client';
import { App } from './ui/App';
import './styles.css';

const target =
  document.getElementById('microwave-root') ?? document.getElementById('root');

if (target) {
  ReactDOM.createRoot(target).render(
    <React.StrictMode>
      <App />
    </React.StrictMode>,
  );
}
