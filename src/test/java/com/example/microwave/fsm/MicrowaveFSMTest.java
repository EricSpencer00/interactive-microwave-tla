package com.example.microwave.fsm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class MicrowaveFSMTest {
    private MicrowaveFSM fsm;

    @BeforeEach
    void setUp() {
        fsm = new MicrowaveFSM();
    }

    @Test
    void testInitialState() {
        assertEquals(MicrowaveFSM.State.IDLE, fsm.getState());
        assertEquals(0, fsm.getTimer());
    }

    @Test
    void testAddTime() {
        String result = fsm.addTime(10);
        assertNotNull(result);
        assertFalse(result.startsWith("Cannot"));
        assertEquals(10, fsm.getTimer());
    }

    @Test
    void testStartCooking() {
        fsm.addTime(10);
        String result = fsm.startCooking();
        assertNotNull(result);
        assertFalse(result.startsWith("Cannot"));
        assertEquals(MicrowaveFSM.State.COOKING, fsm.getState());
    }

    @Test
    void testCannotStartCookingWithDoorOpen() {
        fsm.openDoor();
        String result = fsm.startCooking();
        assertNotNull(result);
        assertTrue(result.startsWith("Cannot"));
        assertEquals(MicrowaveFSM.State.DOOR_OPEN, fsm.getState());
    }

    @Test
    void testStopClock() {
        fsm.addTime(10);
        fsm.startCooking();
        String result = fsm.stopClock();
        assertNotNull(result);
        assertFalse(result.startsWith("Cannot"));
        assertEquals(MicrowaveFSM.State.PAUSED, fsm.getState());
    }

    @Test
    void testResetClock() {
        fsm.addTime(10);
        String result = fsm.resetClock();
        assertNotNull(result);
        assertFalse(result.startsWith("Cannot"));
        assertEquals(0, fsm.getTimer());
    }

    @Test
    void testTick() {
        fsm.addTime(10);
        fsm.startCooking();
        String result = fsm.tick();
        assertNotNull(result);
        assertFalse(result.startsWith("Cannot"));
        assertEquals(9, fsm.getTimer());
    }

    @Test
    void testDoorOperations() {
        // Test opening door
        String openResult = fsm.openDoor();
        assertNotNull(openResult);
        assertFalse(openResult.startsWith("Cannot"));
        assertEquals(MicrowaveFSM.State.DOOR_OPEN, fsm.getState());

        // Test closing door
        String closeResult = fsm.closeDoor();
        assertNotNull(closeResult);
        assertFalse(closeResult.startsWith("Cannot"));
        assertEquals(MicrowaveFSM.State.IDLE, fsm.getState());
    }
} 