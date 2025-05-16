package com.example.tlamicrowave.service;

import org.springframework.stereotype.Service;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

/**
 * Service for storing and managing the TLA+ verification log.
 * This breaks the circular dependency between MicrowaveService and TlcIntegrationService.
 */
@Service
public class VerificationLogService {
    private static final int MAX_LOG_SIZE = 100; // Keep only last 100 states
    private final Queue<String> verificationLog = new LinkedList<>();
    
    /**
     * Add an entry to the verification log, maintaining the maximum size limit.
     */
    public synchronized void addLogEntry(String entry) {
        verificationLog.add(entry);
        while (verificationLog.size() > MAX_LOG_SIZE) {
            verificationLog.poll();
        }
    }
    
    /**
     * Get a copy of the current verification log.
     */
    public List<String> getVerificationLog() {
        return new ArrayList<>(verificationLog);
    }
    
    /**
     * Check if the verification log is empty.
     */
    public boolean isEmpty() {
        return verificationLog.isEmpty();
    }
    
    /**
     * Clear the verification log.
     */
    public void clear() {
        verificationLog.clear();
    }
} 