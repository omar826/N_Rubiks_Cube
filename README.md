# N×N×N Rubik's Cube in Lean 4  

## Overview

This project aims to formally model an **n × n × n Rubik's Cube** and investigate solvability for some special cases using the **Lean 4** proof assistant. Some code leverages and adapts concepts from a prior **3 × 3 × 3 implementation** ([vihdzp/rubik-lean4](https://github.com/vihdzp/rubik-lean4), Apache-2.0 license).

A key aspect of this work involves exploring different modeling strategies. One approach, applied to the general **n × n × n** case and the specific **2 × 2 × 2** cube, represents the cube state concretely using pieces and their associated colored stickers. A second, more abstract approach was employed for the **4 × 4 × 4** cube, viewing its state transformations as permutations acting on numbered pieces, which was motivated by Theorem 3.1 from "The First Law of Cubology for the Rubik's Revenge" (arXiv:1611.07437v1 [math.CO]).

## Goals Achieved
- Model an **n × n × n Rubik's Cube**.
- Model a **2 × 2 × 2 Rubik's Cube** and its moves.
- State and prove necessary and sufficient solvability conditions for a **2 × 2 × 2 Rubik's Cube** under certain assumptions.
- Model a **4 × 4 × 4 Rubik's Cube** and its moves.
- Display the state of the **4 × 4 × 4 Rubik's cube** dynamically for use cases.  
- State and prove necessary and sufficient solvability conditions for a **4 × 4 × 4 Rubik's Cube** under certain assumptions.  

## Future Goals  
- Prove **equivalence** of both approaches to modelling a **Rubik's Cube**.  
- Formally design an **optimal** solving algorithm and prove optimality for a **2 × 2 × 2 Rubik's Cube**.
