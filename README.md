# Formalizing eBPF through Abstract Interpretation  
### Research Track Project – 2025  
**Thomas AROCENA**  
Mines Nancy – Engineering School (2nd year)

---

## Overview

This repository contains the work carried out during my 2025 **Research Track** (one day per week over the academic year), as part of the second year of the engineering curriculum at Mines Nancy.

The project took place at the **LORIA – Laboratoire Lorrain de Recherche en Informatique et ses Applications**, within the team **[MOSEL-VERIDIS](https://www.loria.fr/fr/la-recherche/les-equipes/mosel-veridis/)**, under the supervision of:

- [Stephan Merz](https://members.loria.fr/SMerz/). Senior researcher, Inria
- Ghilain Bergeron. PhD student, Université de Lorraine
- [Vincent Trélat](https://github.com/VTrelat). PhD student, Université de Lorraine

This research project served as my first in-depth exposure to **formal methods**, with a particular focus on the formalization of the **eBPF** language.

---
## Reports & Presentations

The full academic materials are available in french:

- [Final Report](report/rapport.pdf)
- [Long Presentation](report/soutenance.pdf)
- [Short Presentation](report/soutenance-flash.pdf)

---

## Research Context

eBPF (extended Berkeley Packet Filter) is a low-level, safety-critical execution environment embedded in the Linux kernel. Its verifier already performs sophisticated static checks to guarantee safety properties.

The objective of this project was to explore how formal methods and in particular **abstract interpretation** can be used to model and reason about parts of the eBPF language in a mathematically rigorous way.

---

## Research Objectives

The project focused on:

- Understanding the execution semantics of eBPF  
- Formalizing arithmetic and logical operations over bounded 64-bit integers  
- Designing abstract domains suitable for static analysis  
- Studying precision limits induced by abstraction  

Two main abstract domains were investigated:

### 1. Bounded 64-bit Integer Intervals

- Formal definition of interval arithmetic over fixed-width signed integers  
- Handling of overflow and wraparound semantics  
- Sound over-approximation of arithmetic operations  

### 2. Three-Valued (Tristate) Domain

- Modeling binary values with uncertainty: {0, 1, ⊤}  
- Formal propagation rules  
- Logical operation abstraction  

---

## Methodological Approach

The work followed a classical abstract interpretation pipeline:

1. Definition of a concrete semantics fragment  
2. Design of corresponding abstract domains  
3. Formalization of abstract transfer functions

---

## Main Contributions

- Formalization of arithmetic rules over bounded 64-bit intervals  
- Definition of tristate logical propagation rules  
- Structured abstraction of selected eBPF operations  

---



