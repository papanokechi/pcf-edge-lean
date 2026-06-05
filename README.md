# pcf-edge-lean — M9 Newton-edge algebraic core

Lean 4 / Mathlib formalization of the **purely algebraic / finitary core** of the
M9 Newton-edge lemma (PCF Borel-singularity-radius edge lemma).

For a polynomial continued fraction with unit numerator and partial denominator
`b(n) = Σ_{k=0}^d β_k n^k` (degree `d ≥ 2`, `β_d ≠ 0`), the generating function
`F(z) = Σ Q_n z^n` of the Wallis convergent denominators satisfies `P·F = 0` with
`P = 1 − z·b(θ+1) − z²`, `θ = z d/dz`. A slope-`1/d` Newton edge of `P` at `z=0`
yields the edge polynomial `χ_d` and Borel-singularity radius `ξ₀ = d / β_d^{1/d}`.

This project formalizes ONLY the finitary algebra under the edge. The analytic
step "Newton edge ⇒ Borel singularity radius" (Wasow §19 sectorial existence /
Birkhoff–Trjitzinsky Borel summability) is **OUT OF SCOPE** and is encoded as an
explicit axiom `edge_implies_borel_radius` (`H_edge`); it is **NOT** proved.

## Epistemic-status convention

A declaration is **PROVEN** iff its `#print axioms` cone is contained in the
clean set `{propext, Classical.choice, Quot.sound}` **and** contains no `sorryAx`
(and the sources contain zero `sorry` / `admit` / `native_decide`).

A declaration is **PROVEN CONDITIONAL on H_edge** iff it is otherwise clean but
its axiom cone additionally contains `edge_implies_borel_radius` (and the opaque
`borelRadius`). This is expected and correct for the `ξ₀` end statement only.

## What is PROVEN (clean cone, `PcfEdge/Basic.lean`)

| Thm | Name | Statement | Ground truth |
|-----|------|-----------|--------------|
| T1  | `shift_leading_coeff`   | `(p.comp (X + C 1)).coeff p.natDegree = p.leadingCoeff` | G1: `[θ^d] b(θ+1) = β_d` |
| T2  | `edge_poly_closed_form` | `1 - βd*(-(c/d))^d = 1 + (-1)^(d+1)*(βd/d^d)*c^d` | G2: closed form of `χ_d` |
| T3a | `reindex_leading_coeff` | `(p.comp (C α*X + C γ)).coeff d = α^d * p.leadingCoeff` | G4: `lead(b∘φ) = α^d β_d`, γ-free |
| T3b | `xi0_covariance`        | `xi0val d (α^d βd) = α⁻¹ * xi0val d βd` | G3/G4: `ξ₀(b∘φ) = α⁻¹ ξ₀(b)` |

`xi0val d βd := (d:ℝ) / βd ^ ((1:ℝ)/d)` (real `rpow`) encodes `ξ₀`.
G3 (root modulus `|root χ_d| = ξ₀`) is captured for the real positive modulus via
the `rpow` identity T3b; the full complex root-set of `χ_d` is **not** formalized
(see "could not confirm" in the task report).

## The H_edge hypothesis and the conditional end statement

* `axiom borelRadius : ℝ[X] → ℝ` — the analytic Borel singularity radius; OPAQUE
  (not constructed here).
* `axiom edge_implies_borel_radius (p) (hd : 2 ≤ p.natDegree) (hlc : 0 < p.leadingCoeff) :
  borelRadius p = xi0 p` — this is **H_edge** (analytic edge⇒radius, Wasow §19 /
  Birkhoff–Trjitzinsky). NOT proved; visible in the cone of anything using it.
* `theorem borelRadius_covariance` — `borelRadius (b∘φ) = α⁻¹ · borelRadius b` for
  `φ(n)=αn+γ`, `α>0`. **PROVEN CONDITIONAL on H_edge.**

The honest claim recorded here:

> `ξ₀(b) = d / β_d^{1/d}`, and `ξ₀(b∘φ) = α⁻¹·ξ₀(b)` for `φ(n)=αn+γ` — CONDITIONAL
> on the analytic hypothesis `H_edge` (edge ⇒ Borel radius, Wasow §19 /
> Birkhoff–Trjitzinsky), which is an explicit axiom and is NOT proved here.

## Toolchain (pinned)

* Lean: `leanprover/lean4:v4.29.0` (see `lean-toolchain`)
* Mathlib: rev `8a178386ffc0f5fef0b77738bb5449d50efeea95` (inputRev `v4.29.0`, see `lake-manifest.json`)

## Build & verify

```sh
lake exe cache get      # download prebuilt Mathlib oleans (already pulled by `lake update` hook)
lake build              # builds PcfEdge.Basic ; exit code 0
```

Axiom cones (reproduce with a scratch file importing `PcfEdge`):

```lean
#print axioms PcfEdge.shift_leading_coeff      -- {propext, Classical.choice, Quot.sound}
#print axioms PcfEdge.edge_poly_closed_form    -- {propext, Classical.choice, Quot.sound}
#print axioms PcfEdge.reindex_leading_coeff    -- {propext, Classical.choice, Quot.sound}
#print axioms PcfEdge.xi0_covariance           -- {propext, Classical.choice, Quot.sound}
#print axioms PcfEdge.borelRadius_covariance   -- + borelRadius, edge_implies_borel_radius (CONDITIONAL)
```
