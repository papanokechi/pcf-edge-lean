/-
Axiom-cone reproducibility check for pcf-edge-lean.
Run from the repo root with the pinned toolchain:

    lake env lean cone_check.lean

Expected output (clean cone = {propext, Classical.choice, Quot.sound}):
  'shift_leading_coeff'   depends on axioms: [propext, Classical.choice, Quot.sound]
  'edge_poly_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
  'reindex_leading_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
  'xi0_covariance'        depends on axioms: [propext, Classical.choice, Quot.sound]
  'borelRadius_covariance' depends on axioms:
      [propext, Classical.choice, borelRadius, edge_implies_borel_radius, Quot.sound]
-/
import PcfEdge
open PcfEdge

#print axioms shift_leading_coeff
#print axioms edge_poly_closed_form
#print axioms reindex_leading_coeff
#print axioms xi0_covariance
#print axioms borelRadius_covariance
