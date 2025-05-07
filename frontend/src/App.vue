<template>
  <vaadin-vertical-layout>
    <vaadin-horizontal-layout>
      <vaadin-button @click="incrementTime">+10s</vaadin-button>
      <vaadin-button @click="startCooking">Start</vaadin-button>
      <vaadin-button @click="pauseCooking">Pause</vaadin-button>
      <vaadin-button @click="resetClock">Reset</vaadin-button>
      <vaadin-button @click="validateFullSpec">Validate Full Spec</vaadin-button>
    </vaadin-horizontal-layout>
    
    <vaadin-text-field
      label="Timer"
      :value="timerDisplay"
      readonly
    ></vaadin-text-field>
    
    <vaadin-text-field
      label="TLA+ Transition Validation"
      :value="tlaCheck"
      readonly
      multiline
    ></vaadin-text-field>
    
    <vaadin-text-field
      label="Full TLA+ Model Check"
      :value="fullTla"
      readonly
      multiline
    ></vaadin-text-field>
  </vaadin-vertical-layout>
</template>

<script>
export default {
  name: 'App',
  data() {
    return {
      timer: 0,
      tlaCheck: '',
      fullTla: ''
    }
  },
  computed: {
    timerDisplay() {
      const minutes = Math.floor(this.timer / 60);
      const seconds = this.timer % 60;
      return `${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`;
    }
  },
  methods: {
    async incrementTime() {
      // TODO: Implement API call
    },
    async startCooking() {
      // TODO: Implement API call
    },
    async pauseCooking() {
      // TODO: Implement API call
    },
    async resetClock() {
      // TODO: Implement API call
    },
    async validateFullSpec() {
      // TODO: Implement API call
    }
  }
}
</script>

<style>
vaadin-vertical-layout {
  padding: 1rem;
  gap: 1rem;
}

vaadin-horizontal-layout {
  gap: 0.5rem;
}

vaadin-text-field {
  width: 100%;
}
</style> 