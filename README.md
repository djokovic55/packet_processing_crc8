# Formal Verification of the Packet Processing System

The packet processing system is fully verified with the application of the formal methods. In this project many complexity reduction techniques (Cutpoints, Blackboxing, Case-splitting, Assume-Guarantees, Inital Value Abstractions) were applied in attempt to achieve the convergence of the main end-to-end property that should exhaustively prove the packet building process. They all made a good progress in terms of better bounded proofs, but never actually resulted in a full proof.

Convergence was achieved with the application of the JasperGold's SST (State Space Tunneling) method which serves to identify good candidates and hence develop new helper assertions. Helper assertion (Assume-Guarantee) reduces the state space for the tool to explore, effectively decomposing the hard problem into smaller, more manageable parts.

## Table of contents

- [Run Project](#run-project)
- [System Overview](#system-overview)
- [Formal Testbench Environment](#formal-testbench-overview)
- [State Space Tunneling](#state-space-tunneling)

## Run Project
1. Clone repository
2. Run make command

## System Overview

![System Diagram](docs/system_overview.png)

- The described system is an AXI4-based system operating in a single clock domain. 
- The main purpose of the system is packet processing according to given transaction level protocol. 
- It should build packets from incoming, raw data and parse incoming packets to extract packet information and possible transmission errors.

## Formal Testbench Overview

## State Space Tunneling
