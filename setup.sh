#!/bin/bash
# Setup script for rocq-domain-theory project structure

set -e  # Exit on any error

echo "Creating rocq-domain-theory directory structure..."

# Create main directories
mkdir -p docs/{thesis,tutorial}
mkdir -p src/{phase0_foundations,phase0_hierarchybuilder,phase0_inverse_limit,phase1_enriched,phase1_validation,phase2_quantum,phase3_prototype}
mkdir -p test
mkdir -p examples

# Create subdirectories
mkdir -p src/phase3_prototype/examples
mkdir -p examples

# Create dune files
create_dune_root() {
    cat > dune << 'EOF'
(env
 (dev
  (flags (:standard -w -58))))

(dirs src test examples)
EOF
}

create_dune_src() {
    cat > src/dune << 'EOF'
(dirs phase0_foundations phase0_hierarchybuilder phase0_inverse_limit 
      phase1_enriched phase1_validation phase2_quantum phase3_prototype)
EOF
}

create_dune_phase0_f() {
    cat > src/phase0_foundations/dune << 'EOF'
(library
 (name phase0_foundations)
 (public_name rocq-domain-theory.phase0_foundations)
 (synopsis "Basic order theory and CPO definitions"))
EOF
}

create_dune_phase0_hb() {
    cat > src/phase0_hierarchybuilder/dune << 'EOF'
(library
 (name phase0_hierarchybuilder)
 (public_name rocq-domain-theory.phase0_hierarchybuilder)
 (libraries rocq-domain-theory.phase0_foundations)
 (synopsis "Hierarchy-Builder integration for algebraic structures"))
EOF
}

create_dune_phase0_il() {
    cat > src/phase0_inverse_limit/dune << 'EOF'
(library
 (name phase0_inverse_limit)
 (public_name rocq-domain-theory.phase0_inverse_limit)
 (libraries rocq-domain-theory.phase0_foundations rocq-domain-theory.phase0_hierarchybuilder)
 (synopsis "Inverse limit construction and recursive domain equations"))
EOF
}

create_dune_phase1_e() {
    cat > src/phase1_enriched/dune << 'EOF'
(library
 (name phase1_enriched)
 (public_name rocq-domain-theory.phase1_enriched)
 (libraries rocq-domain-theory.phase0_foundations rocq-domain-theory.phase0_hierarchybuilder rocq-domain-theory.phase0_inverse_limit)
 (synopsis "Enriched category theory for programming language semantics"))
EOF
}

create_dune_phase1_v() {
    cat > src/phase1_validation/dune << 'EOF'
(library
 (name phase1_validation)
 (public_name rocq-domain-theory.phase1_validation)
 (libraries phase1_enriched phase0_inverse_limit)
 (synopsis "PCF validation: syntax, semantics, soundness, adequacy"))
EOF
}

create_dune_phase2() {
    cat > src/phase2_quantum/dune << 'EOF'
(library
 (name phase2_quantum)
 (public_name rocq-domain-theory.phase2_quantum)
 (libraries phase1_enriched)
 (synopsis "Quantum CPO structures (stretch goal)"))
EOF
}

create_dune_phase3() {
    cat > src/phase3_prototype/dune << 'EOF'
(library
 (name phase3_prototype)
 (public_name rocq-domain-theory.phase3_prototype)
 (libraries phase2_quantum phase1_validation)
 (synopsis "Quantum language prototype (stretch goal)"))
EOF
}

create_dune_test() {
    cat > test/dune << 'EOF'
(test
 (name test_suite)
 (libraries rocq-domain-theory.phase0_foundations rocq-domain-theory.phase0_hierarchybuilder rocq-domain-theory.phase0_inverse_limit
            rocq-domain-theory.phase1_enriched rocq-domain-theory.phase1_validation))
EOF
}

create_dune_examples() {
    cat > examples/dune << 'EOF'
(executable
 (name examples)
 (libraries rocq-domain-theory.phase0_foundations rocq-domain-theory.phase0_inverse_limit rocq-domain-theory.phase1_enriched 
            rocq-domain-theory.phase1_validation))
EOF
}

# Create initial .v files (empty stubs)
create_stub_v() {
    local file=$1
    local title=$2
    cat > "$file" << EOF
(** $title

    This module is part of the rocq-domain-theory project.
*)

(* Content to be added *)
EOF
}

# Phase 0: Foundations
create_stub_v "src/phase0_foundations/Order.v" "Preorders and partial orders"
create_stub_v "src/phase0_foundations/CPO.v" "Complete partial orders"
create_stub_v "src/phase0_foundations/Continuous.v" "Continuous functions"
create_stub_v "src/phase0_foundations/Pointed.v" "Pointed cpos"
create_stub_v "src/phase0_foundations/Discrete.v" "Discrete cpos"
create_stub_v "src/phase0_foundations/Products.v" "Product constructions"
create_stub_v "src/phase0_foundations/Sums.v" "Sum constructions"
create_stub_v "src/phase0_foundations/FunctionSpaces.v" "Exponential objects"
create_stub_v "src/phase0_foundations/Lift.v" "Lift monad"
create_stub_v "src/phase0_foundations/FixedPoints.v" "Fixed point operators"

# Phase 0: Hierarchy-Builder
create_stub_v "src/phase0_hierarchybuilder/Hierarchies.v" "Algebraic hierarchy"
create_stub_v "src/phase0_hierarchybuilder/Instances.v" "Hierarchy-Builder instances"

# Phase 0: Inverse Limit
create_stub_v "src/phase0_inverse_limit/BiFunctor.v" "Mixed-variance bifunctors"
create_stub_v "src/phase0_inverse_limit/EmbeddingProjection.v" "Embedding-projection pairs"
create_stub_v "src/phase0_inverse_limit/InverseLimit.v" "Inverse limit construction"
create_stub_v "src/phase0_inverse_limit/RecursiveDomains.v" "Solving F(D,D) ≅ D"

# Phase 1: Enriched Categories
create_stub_v "src/phase1_enriched/EnrichedCategory.v" "Enriched category structure"
create_stub_v "src/phase1_enriched/LocallyContinuous.v" "Locally-continuous functors"
create_stub_v "src/phase1_enriched/EnrichedNatTrans.v" "Enriched natural transformations"
create_stub_v "src/phase1_enriched/CPOEnriched.v" "CPO⊥ is enriched"
create_stub_v "src/phase1_enriched/EnrichedInverseLimit.v" "Inverse limit in enriched setting"
create_stub_v "src/phase1_enriched/RecursiveEquations.v" "D ≅ [D → D]⊥"

# Phase 1: Validation
create_stub_v "src/phase1_validation/PCF_Syntax.v" "PCF syntax"
create_stub_v "src/phase1_validation/PCF_Operational.v" "PCF operational semantics"
create_stub_v "src/phase1_validation/PCF_Denotational.v" "PCF denotational semantics"
create_stub_v "src/phase1_validation/PCF_Soundness.v" "PCF soundness proof"
create_stub_v "src/phase1_validation/PCF_Adequacy.v" "PCF adequacy proof"

# Phase 2: Quantum (Stretch)
create_stub_v "src/phase2_quantum/QuantumStructure.v" "Quantum structures"
create_stub_v "src/phase2_quantum/qCPO.v" "qCPO category"
create_stub_v "src/phase2_quantum/QuantumMorphisms.v" "Quantum morphisms"
create_stub_v "src/phase2_quantum/qCPOProperties.v" "qCPO properties"
create_stub_v "src/phase2_quantum/QuantumEnrichment.v" "qCPO enrichment"

# Phase 3: Prototype (Stretch)
create_stub_v "src/phase3_prototype/QMiniCore_Syntax.v" "QMini-Core syntax"
create_stub_v "src/phase3_prototype/QMiniCore_Semantics.v" "QMini-Core semantics"

# Create dune files
echo "Creating dune files..."
cd "$(dirname "$0")" || exit
create_dune_root
create_dune_src
create_dune_phase0_f
create_dune_phase0_hb
create_dune_phase0_il
create_dune_phase1_e
create_dune_phase1_v
create_dune_phase2
create_dune_phase3
create_dune_test
create_dune_examples

# Create stub test and example files
create_stub_v "test/test_suite.v" "Test suite"
create_stub_v "examples/examples.v" "Examples"

# Create documentation stubs
touch docs/thesis/.gitkeep
touch docs/tutorial/.gitkeep

cat > docs/design-decisions.md << 'EOF'
# Design Decisions

This document records architectural choices and rationale.

## Phase Organization

Phases are organized as separate directories to:
- Allow independent compilation and testing
- Make dependencies explicit
- Enable incremental publication (Phase 0 → opam package)
- Keep git history clear

## Dune Configuration

Each phase has its own dune file specifying dependencies.
This enables fine-grained build control.

EOF

cat > docs/migration-notes.md << 'EOF'
# Migration Notes: Coq 8.2 → Rocq 9

This document tracks changes from the 2009 Benton-Kennedy library.

## Key Modernizations

- Universe polymorphism
- Primitive projections
- SProp for strict propositions
- Hierarchy-Builder integration

## Compatibility Issues

(To be filled in as migration occurs)

EOF

echo "✓ Directory structure created successfully!"
echo ""
echo "Next steps:"
echo "1. cd to your repo root"
echo "2. Run: bash setup.sh"
echo "3. Then: dune build"
echo "4. Start editing src/phase0_foundations/ files"