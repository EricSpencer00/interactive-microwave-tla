import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

// base: './' is important so the same bundle works both standalone and
// when embedded under ai4fm Sphinx's _static/ directory with relative paths.
export default defineConfig({
  plugins: [react()],
  base: './',
  build: {
    outDir: 'dist',
    assetsDir: 'assets',
    rollupOptions: {
      output: {
        // Stable filenames so the Sphinx post can hard-code them.
        entryFileNames: 'assets/index.js',
        chunkFileNames: 'assets/[name].js',
        assetFileNames: 'assets/[name][extname]',
      },
    },
  },
});
