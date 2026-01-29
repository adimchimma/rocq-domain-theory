
# Milestones (proposal-aligned)

These milestones are copied from the .v3 proposal and adapted to the current repo layout.

## Month 1
- [ ] CPO “hierarchy” compiles under Rocq (current dev is 9.0.0)
- [ ] Phase 0 foundations have ω-**chains** (not arbitrary ω-sequences)

## Month 2
**Milestone 1:** InverseLimit module complete; Hierarchy-Builder integrated
- [ ] Inverse limit construction compiles and is usable
	- `src/phase0_inverse_limit/*`
- [ ] HB layer compiles cleanly
	- `src/phase0_hierarchybuilder/*`

## Month 3
**Milestone 2:** Enriched categories defined; CPO shown to be enriched
- [ ] Enriched category core definitions
	- `src/phase1_enriched/EnrichedCategory.v`
- [ ] Proof that CPO fits the enrichment
	- `src/phase1_enriched/CPOEnriched.v`

## Month 4
**Milestone 3:** Inverse-limit theorem proved in enriched setting
- [ ] Enriched inverse-limit theorem
	- `src/phase1_enriched/EnrichedInverseLimit.v`
- [ ] Recursive equation corollary (“derive D”)
	- `src/phase1_enriched/RecursiveEquations.v`

## Mid-January checkpoint (core thesis complete)
- [ ] Modernized library + enriched categories formalized
- [ ] Decision point documented: proceed to quantum work or deepen core

## Month 5 (stretch)
**Milestone 4:** qCPO category defined; basic axioms proved
- [ ] `src/phase2_quantum/qCPO.v`
- [ ] `src/phase2_quantum/qCPOProperties.v`

## Month 6 (stretch)
**Milestone 5:** Quantum structures partially formalized
- [ ] `src/phase2_quantum/QuantumStructure.v`
- [ ] `src/phase2_quantum/QuantumMorphisms.v`

## Month 7 (stretch)
**Milestone 6:** QMini-Core syntax defined; basic semantics given
- [ ] `src/phase3_prototype/QMiniCore_Syntax.v`
- [ ] `src/phase3_prototype/QMiniCore_Semantics.v`

## Month 8
**Milestone 7:** Begin thesis writing; draft chapters 1–3
- [ ] `docs/thesis/introduction.md`
- [ ] `docs/thesis/background.md`
- [ ] `docs/thesis/methods.md`

## Month 9
**Milestone 8:** Thesis complete; library documented; defense prepared
- [ ] Full thesis draft + bibliography
- [ ] Documentation/tutorial pass
- [ ] Final test/build verification

