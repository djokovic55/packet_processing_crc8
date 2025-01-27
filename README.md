# Formal Verification of the Packet Processing System

## Table of contents

- [Introduction](#introduction)
- [Run Project](#run-project)
- [System Overview](#system-overview)
- [Formal Testbench Environment](#formal-testbench-overview)
- [State Space Tunneling](#state-space-tunneling)

## Introduction

The packet processing system fully verified with the application of the formal methods. 

## Run Project
- Clone repository
- Run make command
## System Overview

![System Diagram](docs/system_overview.png)

- The described system is an AXI4-based system operating in a single clock domain. 
- The main purpose of the system is packet processing according to given transaction level protocol. 
- It should build packets from incoming raw data and parse incoming packets to extract packet info and possible transmission errors.

## Formal Testbench Overview

## State Space Tunneling
