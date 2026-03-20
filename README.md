# Modernizing Domain Theory Foundations for Quantum Programming Languages

A machine-verified domain theory library in Rocq (formerly Coq), developed as an
undergraduate thesis. Modernizes Benton, Kennedy & Varming's 2009 library,
formalizes CPO-enriched categories, and proves soundness and adequacy for PCF.

**Toolchain**: Rocq 9.0, Hierarchy Builder (HB) >= 1.5, Dune 3.20

## Repository layout

```
src/
  structures/   Order, CPO, Morphisms, Enriched        (HB mixin/structure declarations)
  theory/       OrderTheory ... DomainEquations         (derived lemmas and constructions)
  instances/    Nat, Discrete, Function, Yoneda, FunLift  (concrete HB instances)
  lang/         PCF_Syntax ... PCF_Adequacy             (PCF language and semantics)
  quantum/      QuantumStructure, qCPO, qCPOProperties  (quantum domain theory)
test/           LiftTests, FixedPointTests, ...         (property tests)
examples/       basic_cpos, enriched_usage, pcf_examples, recursive_domain
docs/           thesis chapters, design decisions
planning/       project tracking
```

### Logical paths

| Prefix | Directory |
|--------|-----------|
| `DomainTheory.Structures` | `src/structures/` |
| `DomainTheory.Theory` | `src/theory/` |
| `DomainTheory.Instances` | `src/instances/` |
| `DomainTheory.Lang` | `src/lang/` |
| `DomainTheory.Quantum` | `src/quantum/` |

## Building

```bash
dune build
```

## Editor setup (VS Code + VsRocq)

`_CoqProject` at the repo root provides `-Q` mappings so VsRocq can resolve
imports for interactive stepping. Dune does **not** read `_CoqProject`; it uses
`coq.theory` stanzas in `dune` files.

If VsRocq cannot resolve paths after opening a file, run
**Command Palette > Rocq: Reset**.

## What's formalized

- **Domain theory** -- preorders, partial orders, omega-CPOs, pointed CPOs, Scott
  continuity, Kleene fixed-point theorem, Scott topology, way-below relation,
  products, sums, lifting (with monad laws), function spaces (CCC structure),
  domain equations via inverse limits of EP-sequences.
- **Enriched categories** -- CPO-enriched categories, locally continuous functors,
  enriched natural transformations (with CPO structure), Yoneda lemma,
  concrete mixed-variance lifted function-space functor.
- **PCF** -- intrinsically typed ANF syntax, big-step CBV operational semantics,
  denotational semantics, soundness, and adequacy (via Benton-Kennedy-Varming
  logical relation). Full convergence correspondence: e converges iff its
  denotation is defined.
- **Quantum domain theory** -- involutive quantales (HB mixin with 15 axioms),
  quantum partial orders, quantum chains and convergence, quantum CPOs,
  bundled Scott-continuous maps, quantum Kleene fixed-point theorem, and
  CPO-enrichment of hom-sets. Based on Kornell, Lindenhovius & Mislove (2024).

~15,700 lines across 35 source files, with 0 Admitted in the main
development (2 documented obstructions in the supplementary LiftMonad.v,
1 justified axiom in DomainEquations.v).

## To be formalized

Planned extensions (stubs in `src/quantum/` and `src/lang/`):

- **Quantum morphisms** -- completely positive trace-preserving (CPTP) maps as
  morphisms of the qCPO category; identity, composition, and quantum continuity.
- **Quantum enrichment** -- hom-objects as qCPOs with quantum-continuous
  composition, extending the CPO-enriched framework in `Enriched.v`.
- **QMiniCore** -- a prototype quantum lambda calculus with linear types, quantum
  gates, and measurement, with denotational semantics targeting qCPOs.

## References

- Benton, Kennedy & Varming, *Some Domain Theory and Denotational Semantics in Coq* (2009)
- Abramsky & Jung, *Domain Theory* (1994)
- Kelly, *Basic Concepts of Enriched Category Theory* (1982)
- Kornell, Lindenhovius & Mislove, *Categories of Quantum CPOs* (2024)
