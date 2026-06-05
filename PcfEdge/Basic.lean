import Mathlib

/-!
# M9 Newton-edge algebraic core (PCF Borel-singularity-radius edge lemma)

This file formalizes ONLY the purely algebraic / finitary core of the M9
Newton-edge lemma for a polynomial continued fraction with unit numerator and
partial denominator `b(n) = Σ βₖ nᵏ` (degree `d ≥ 2`, leading coeff `β_d ≠ 0`).

The analytic step "Newton edge ⇒ Borel singularity radius" (Wasow §19 /
Birkhoff–Trjitzinsky Borel summability) is **OUT OF SCOPE** and is encoded as
the explicit axiom `edge_implies_borel_radius` (`H_edge`).  It is **NOT** proved.

## Epistemic status
* `shift_leading_coeff` (T1), `edge_poly_closed_form` (T2),
  `reindex_leading_coeff` (T3a), `xi0_covariance` (T3b) are **PROVEN**
  (clean axiom cone, no `sorryAx`).
* `borelRadius_covariance` (the ξ₀ end statement) is **PROVEN CONDITIONAL** on
  `edge_implies_borel_radius`; that axiom appears in its axiom cone by design.

Verified ground truth (independently re-checked in sympy, d = 2..6):
* G1  `[θ^d] b(θ+1) = β_d`
* G2  `1 − β_d·(−(c/d))^d = 1 + (−1)^{d+1}·(β_d/d^d)·c^d`
* G3  every root `c` of `χ_d` has `|c| = d / β_d^{1/d} =: ξ₀`
* G4  `lead(b∘(αn+γ)) = α^d β_d` (γ-free); `ξ₀(b∘φ) = α⁻¹ ξ₀(b)`
-/

namespace PcfEdge

open Polynomial

/-! ## T1 — shift-invariance of the leading coefficient (G1)

`[θ^d] b(θ+1) = β_d`: composition with `X + 1` preserves the top coefficient. -/
theorem shift_leading_coeff {R : Type*} [CommRing R] [IsDomain R] (p : R[X]) :
    (p.comp (X + C 1)).coeff p.natDegree = p.leadingCoeff := by
  have hcomp_nd : (p.comp (X + C 1)).natDegree = p.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hlc : (p.comp (X + C 1)).leadingCoeff = p.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
      (monic_X_add_C (1 : R)).leadingCoeff, one_pow, mul_one]
  calc (p.comp (X + C 1)).coeff p.natDegree
      = (p.comp (X + C 1)).coeff (p.comp (X + C 1)).natDegree := by rw [hcomp_nd]
    _ = (p.comp (X + C 1)).leadingCoeff := rfl
    _ = p.leadingCoeff := hlc

/-! ## T2 — edge polynomial closed form (G2)

`1 − β_d·(−(c/d))^d = 1 + (−1)^{d+1}·(β_d/d^d)·c^d`, stated `d`-free. -/
theorem edge_poly_closed_form {R : Type*} [Field R] [CharZero R] (d : ℕ) (_hd : d ≠ 0)
    (βd c : R) :
    1 - βd * (-(c / (d : R))) ^ d
      = 1 + (-1) ^ (d + 1) * (βd / (d : R) ^ d) * c ^ d := by
  rw [neg_pow, div_pow, pow_succ]
  ring

/-! ## T3a — affine-reindexing leading-coefficient law (G4)

`lead(b∘(αX+γ)) = α^d · β_d`, γ-independent. -/
theorem reindex_leading_coeff {R : Type*} [Field R] (p : R[X]) {d : ℕ}
    (hd : p.natDegree = d) (α γ : R) (hα : α ≠ 0) :
    (p.comp (C α * X + C γ)).coeff d = α ^ d * p.leadingCoeff := by
  have hqnd : (C α * X + C γ).natDegree = 1 := natDegree_linear hα
  have hqlc : (C α * X + C γ).leadingCoeff = α := leadingCoeff_linear hα
  have hcomp_nd : (p.comp (C α * X + C γ)).natDegree = d := by
    rw [natDegree_comp, hqnd, mul_one, hd]
  have hlc : (p.comp (C α * X + C γ)).leadingCoeff = α ^ d * p.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [hqnd]; exact one_ne_zero), hqlc, hd, mul_comm]
  calc (p.comp (C α * X + C γ)).coeff d
      = (p.comp (C α * X + C γ)).coeff (p.comp (C α * X + C γ)).natDegree := by rw [hcomp_nd]
    _ = (p.comp (C α * X + C γ)).leadingCoeff := rfl
    _ = α ^ d * p.leadingCoeff := hlc

/-! ## ξ₀ and its covariance (G3/G4, real positive modulus) -/

/-- The Borel-singularity radius `ξ₀ = d / β_d^{1/d}` (real `rpow`). -/
noncomputable def xi0val (d : ℕ) (βd : ℝ) : ℝ := (d : ℝ) / βd ^ ((1 : ℝ) / (d : ℝ))

/-- T3b — `ξ₀` covariance under affine reindexing: `ξ₀(α^d β_d) = α⁻¹ ξ₀(β_d)`. -/
theorem xi0_covariance (d : ℕ) (hd : d ≠ 0) (α βd : ℝ) (hα : 0 < α) (hβ : 0 < βd) :
    xi0val d (α ^ d * βd) = α⁻¹ * xi0val d βd := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hβr : (0 : ℝ) < βd ^ ((1 : ℝ) / (d : ℝ)) := Real.rpow_pos_of_pos hβ _
  have key : (α ^ d * βd) ^ ((1 : ℝ) / (d : ℝ)) = α * βd ^ ((1 : ℝ) / (d : ℝ)) := by
    rw [Real.mul_rpow (by positivity) hβ.le]
    congr 1
    rw [← Real.rpow_natCast α d, ← Real.rpow_mul hα.le, mul_one_div,
      div_self hdR, Real.rpow_one]
  unfold xi0val
  rw [key]
  field_simp

/-! ## H_edge and the conditional ξ₀ end statement

`borelRadius` is the analytic Borel singularity radius — an **opaque** object;
we do not construct it.  `edge_implies_borel_radius` is the analytic edge⇒radius
step (Wasow §19 / Birkhoff–Trjitzinsky), taken as an **axiom**, NOT proved. -/

/-- ξ₀ attached to a real partial-denominator polynomial. -/
noncomputable def xi0 (p : ℝ[X]) : ℝ := xi0val p.natDegree p.leadingCoeff

/-- The analytic Borel singularity radius of `F(z)` for denominator `p`. OPAQUE. -/
axiom borelRadius : ℝ[X] → ℝ

/-- **H_edge (OUT OF SCOPE, axiom).** For a degree-`≥2` denominator with positive
leading coefficient, the analytic Borel singularity radius equals the
algebraically-computed `ξ₀`.  This is the classical analytic edge⇒radius step
(Wasow §19 sectorial existence / Birkhoff–Trjitzinsky Borel summability); it is
**not** proved here. -/
axiom edge_implies_borel_radius (p : ℝ[X]) (hd : 2 ≤ p.natDegree)
    (hlc : 0 < p.leadingCoeff) : borelRadius p = xi0 p

/-- **ξ₀ end statement (PROVEN CONDITIONAL on `H_edge`).** The Borel singularity
radius transforms as `ξ₀(b∘φ) = α⁻¹ ξ₀(b)` for `φ(n) = αn + γ`, `α > 0`. -/
theorem borelRadius_covariance (p : ℝ[X]) (α γ : ℝ) (hd : 2 ≤ p.natDegree)
    (hlc : 0 < p.leadingCoeff) (hα : 0 < α) :
    borelRadius (p.comp (C α * X + C γ)) = α⁻¹ * borelRadius p := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hqnd : (C α * X + C γ).natDegree = 1 := natDegree_linear hαne
  have hcomp_nd : (p.comp (C α * X + C γ)).natDegree = p.natDegree := by
    rw [natDegree_comp, hqnd, mul_one]
  have hcomp_lc : (p.comp (C α * X + C γ)).leadingCoeff = α ^ p.natDegree * p.leadingCoeff := by
    have := reindex_leading_coeff p (rfl : p.natDegree = p.natDegree) α γ hαne
    rwa [leadingCoeff, hcomp_nd]
  have hd' : p.natDegree ≠ 0 := by omega
  have hlc' : 0 < (p.comp (C α * X + C γ)).leadingCoeff := by
    rw [hcomp_lc]; positivity
  rw [edge_implies_borel_radius (p.comp (C α * X + C γ)) (by rw [hcomp_nd]; exact hd) hlc',
    edge_implies_borel_radius p hd hlc]
  unfold xi0
  rw [hcomp_nd, hcomp_lc, xi0_covariance p.natDegree hd' α p.leadingCoeff hα hlc]

end PcfEdge
