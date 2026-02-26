# Full Context

## Project Overview
- Modernize the 2009 Benton-Kennedy domain-theory library for Rocq 8.20.
- Build omega-chain enriched category machinery and validate PCF adequacy.
- Stretch goals: formalize qCPO structures and prototype QMini-Core semantics.

## Mathematical Context
- Domain theory foundations: preorders, omega-chains, cpos, continuity, and fixed points.
- Inverse limits and embedding-projection pairs for recursive domain equations.
- Enriched categories: CPO-enriched hom-objects, locally continuous functors, enriched limits.

## Computational Context
- Rocq code is organized in phases (foundations, inverse limits, enrichment, validation, quantum, prototype).
- Several components are scaffolds with axiomatized lubs and admitted lemmas, to be completed.
- Hierarchy-Builder integration provides a structured algebraic/order hierarchy.
- Current builds use Rocq 9.0.0; proposal text targets Rocq 8.20, so version compatibility remains an explicit check.

## Implementation Status Notes
- Phase 1 (enriched + validation), Phase 2 (quantum), and Phase 3 (prototype) modules are mostly stubs intended for later completion.
- Function spaces, sums, and lift still use axiomatized lubs; these need constructive replacements.
- Inverse-limit development has admitted lemmas around iterator monotonicity and embedding/universal properties.
- HB CPO mixins use a lub over arbitrary nat sequences, which may need alignment with chain-based lubs used elsewhere.
- Predomains are currently a thin alias of cpos; discrete/unit cpos are used for simple tests.
- Quantum tests are placeholders and may fail until qCPO structures are implemented.

## Documentation Standards
- Maintain academic rigor and clarity; avoid informal tone or emoji.

## Physics Context (Phase 2)
- Quantum semantics motivation from the Quantum Lambda Calculus and qCPO literature.
- qCPOs aim to model quantum data and Scott-continuous morphisms in a noncommutative setting.
- Current qCPO modules are placeholders awaiting full formalization.

## Key Contributions (Planned)
- Modernized domain theory library compatible with Rocq 8.20.
- Enriched category formalization and inverse-limit theorem in enriched setting.
- PCF soundness and adequacy as validation.
- Stretch: qCPO foundations and QMini-Core semantics prototype.

## Thesis Integration
- Phase 0: foundations and inverse limits (methods + results).
- Phase 1: enriched categories and PCF adequacy (results + discussion).
- Phase 2/3: quantum structures and QMini-Core prototype (optional results).

## Open Questions
- Replace axiomatized lubs in function spaces, sums, and lift with proofs.
- Finish inverse-limit iterator lemmas and compatibility proofs.
- Implement enriched category modules and PCF semantics.
- Align qCPO formalization with "Categories of Quantum CPOs" definitions.
- Decide whether to add CI or a dedicated opam switch for Rocq 8.20 compatibility.
