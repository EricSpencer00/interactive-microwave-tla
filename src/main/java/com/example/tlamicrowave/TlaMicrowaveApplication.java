package com.example.tlamicrowave;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.scheduling.annotation.EnableScheduling;

@SpringBootApplication
@EnableScheduling
public class TlaMicrowaveApplication {
    public static void main(String[] args) {
        SpringApplication.run(TlaMicrowaveApplication.class, args);
    }
} 