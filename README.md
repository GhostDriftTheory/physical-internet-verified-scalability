# Physical Internet Verified Scalability

[![Lean CI](https://github.com/GhostDriftTheory/physical-internet-verified-scalability/actions/workflows/lean.yml/badge.svg)](https://github.com/GhostDriftTheory/physical-internet-verified-scalability/actions/workflows/lean.yml)

A Lean 4 formalization of semantic and accountability conditions for verifiable logistics federation.

This repository formalizes structural conditions for packet-only public RELEASE decisions in heterogeneous logistics networks. It does not prove a historical explanation for why the Physical Internet did or did not diffuse, and it does not prove that any named product or vendor technology is uniquely necessary. The formal core studies when public packets are sufficient for exact release, route-independent judgment, linked accountability traces, sequential non-replay, field necessity, trust-only insufficiency, and optimization insufficiency. The development uses Lean 4 with `Std` only; it does not depend on Mathlib.

The main necessity result is compatibility-aware: under explicit compatibility and fiber-comparability assumptions, an exact public release verifier forces both semantic sufficiency and evidence sufficiency. Conversely, if a public packet fiber contains both an acceptable and an unacceptable compatible world, packet-only soundness cannot coexist with local liveness.

## What This Repository Proves

- Canonical decision quotient and its universal property.
- Robust release soundness and maximality among packet-only sound release predicates.
- Compatibility-aware dual sufficiency for exact public release.
- A bridge-condition counterexample showing why compatibility assumptions matter.
- Local-liveness impossibility for mixed public packet fibers.
- Packet-preserving route independence in heterogeneous networks.
- Common-frame zero holonomy for coherent translation systems.
- Common-kernel adapter interoperability and local onboarding.
- Linked accountability traces with state, version, evidence-root, and time links.
- Sequential nonce non-replay from an initial used-nonce state.
- Field necessity counterexamples for accountability packet fields.
- Perfect mutual trust still being insufficient for execution validity.
- Optimization output alone not determining verified adoptability.
- Typed actual-execution safety under explicit physical, resource, and gate assumptions.

## What This Repository Does Not Prove

- The historical cause of Physical Internet stagnation or adoption.
- The uniqueness of GhostDrift, a logistics judgment packet, a responsibility OS, or any named implementation.
- That sensors correctly observed the physical item.
- That cryptographic keys were not leaked.
- Computational hash-collision resistance.
- That execution gates are physically impossible to bypass.
- Complete coverage of real vehicle, warehouse, road, and time constraints.
- Commercial, institutional, legal, or organizational adoption feasibility.
- That total deployment cost is linear.

## Three-Layer Interpretation

Optimization selects a candidate plan.

A decision-semantic kernel makes plans, requirements, versions, and evaluation contexts interpretable across participants. This is not a claim that every participant must use the same business rule; it is a claim that different rules can be interpreted over a shared decision-relevant meaning space.

Accountability verification checks that the required conditions held for the particular execution, including authority, freshness, evidence continuity, and non-replay.

## Main Theorems

| Area | Main theorem | Meaning |
| --- | --- | --- |
| Semantic kernel | `canonical_decision_quotient_sufficient` | Canonical decision quotient preserves all decisions in the family. |
| Dual sufficiency | `exact_supported_release_implies_dual_sufficiency` | Exact public RELEASE requires semantic and evidence sufficiency under bridge conditions. |
| Impossibility | `semantic_mixed_fiber_blocks_soundness_and_local_liveness` | Mixed semantic fibers block packet-only soundness plus local liveness. |
| Routes | `Route.route_decision_independent` | Packet-preserving routes give route-independent decisions. |
| Holonomy | `CommonFrame.common_frame_all_loops_are_identity` | Loops induced by a common frame are identity transformations. |
| Onboarding | `new_member_interoperates_with_all_existing` | Common-kernel adapters yield local onboarding interoperability. |
| Trace | `LinkedTrace.linked_trace_preserves_invariant` | Valid linked traces preserve invariants. |
| Non-replay | `LinkedTrace.trace_nonce_valid_append` | Sequential nonce state supports trace append without replay. |
| Field necessity | `FieldNecessity.every_accountability_field_is_necessary` | Dropping any accountability field creates indistinguishable good/bad worlds. |
| Trust | `perfect_mutual_trust_still_insufficient` | Perfect mutual trust does not identify execution validity. |
| Execution | `executed_world_is_safe` | Typed assumptions connect RELEASE to actual execution safety. |
| Optimization | `optimizer_output_does_not_determine_verified_adoptability` | Optimization output alone does not determine adoptability. |

## Repository Layout

- `PhysicalInternetVerifiedScalability.lean`: the single mathematical formalization file.
- `AxiomAudit.lean`: prints axiom dependencies for selected main theorems; it adds no new mathematics.
- `README.md`: project scope, theorem index, local verification, and trust boundary.
- `lean-toolchain`: fixed Lean toolchain.
- `lakefile.toml`: minimal Lake package.
- `.gitignore`: generated Lean and Lake artifacts.
- `.github/workflows/lean.yml`: GitHub Actions verification workflow.

## Requirements

- `elan`
- Git
- The fixed Lean toolchain in `lean-toolchain`
- No Mathlib dependency

## Local Verification

```bash
lake build
lake env lean PhysicalInternetVerifiedScalability.lean
lake env lean AxiomAudit.lean
```

For warning-as-failure verification:

```bash
lake build --wfail
```

## Continuous Verification

The GitHub Actions workflow runs on pushes, pull requests, and manual dispatch. It performs a Lake build with warnings treated as failures, direct Lean compilation of the core file, direct compilation of the axiom-audit file, placeholder and malformed Markdown-escape scans, Lean checker, nanoda external verification, no-sorry enforcement through the action, and axiom audit output.

## Trust Boundary

Lean proves logical consequences inside the formal model from explicit typed assumptions. The bridge to physical objects, sensors, cryptographic binding, resource modeling, and execution gates remains outside the formal proof and is represented by typed assumptions such as physical binding soundness, resource model soundness, and execution-requires-release.

Built-in Lean principles such as quotient soundness, propositional extensionality, and classical choice may appear in `AxiomAudit.lean` output depending on theorem dependencies. The repository does not introduce user-defined axioms.

## Status

Release: `v1.0.0`.

## Intellectual Property and License

Copyright © 2026 GhostDrift Mathematical Institute. All rights reserved.

No open-source license is granted for this repository.

This repository is made publicly available for inspection, reproducibility,
and verification of the formal results described herein. Except for rights
necessarily granted through GitHub's functionality under the GitHub Terms of
Service, or as otherwise permitted by applicable law, no permission is granted
to reproduce, modify, distribute, sublicense, or create derivative works from
the contents of this repository without prior permission from the applicable
rights holder.

Certain technologies described or formalized in this repository are the
subject of pending Japanese patent applications, including:

- Japanese Patent Application No. 2026-193140
- Japanese Patent Application No. 2026-194930
- Japanese Patent Application No. 2026-196291

Publication of this repository does not grant any patent license, whether
express or implied, to practice any invention claimed in these applications or
in related patent applications.

For licensing or commercial-use inquiries, please contact the applicable rights
holder.
