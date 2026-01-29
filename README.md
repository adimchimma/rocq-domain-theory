# Modernizing Domain Theory Foundations for Quantum Programming Languages

This repository contains Rocq formalizations, proofs, and supporting documents for my senior thesis.  
Main components (after reorganization):
- Modernized domain theory library (`rocq/domain`)
- Enriched category formalization (`rocq/enriched`)
- Optional quantum extensions (`rocq/quantum`)
- Thesis material in `/docs`
## Editor Setup (VS Code + VsRocq)

- Recommended build: use `dune` for compiling and loadpaths.
- Interactive stepping: VsRocq may not inherit Dune’s loadpaths; use `_CoqProject` for the editor.

Steps:
- Ensure `_CoqProject` exists at repo root with `-Q` mappings for all `src/phase*` folders and `-R` mappings for external libs.
	- A minimal `_CoqProject` is already provided.
- Restart Rocq in VS Code:
	- Command Palette → type “Rocq” → run “Rocq: Reset”.
- Then step through files like [src/phase0_foundations/CPO.v](src/phase0_foundations/CPO.v) and imports should resolve.

Notes:
- Dune builds do not read `_CoqProject`; they use the `coq.theory` stanzas and flags defined in Dune files.
- `_CoqProject` is editor-facing only and won’t affect `dune build`.

Build commands:

```bash
cd /mnt/c/Users/mysti/Documents/Research/Undergrad-Thesis/rocq-domain-theory
dune build
```

If VsRocq still cannot resolve logical paths, set `vsrocq.args` in VS Code User Settings to include the same `-Q/-R` mappings, then “Rocq: Reset”.
