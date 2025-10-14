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

