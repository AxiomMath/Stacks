module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison

/-!
# The comparison of the two blowups of `Spec R`, as a named isomorphism

`Stacks.Blowup.nonempty_over_iso_blowUpToBase` shows that the affine blowup `Proj` of the Rees
algebra of an ideal `K ⊆ R` and the ideal-sheaf blowup of `Spec R` in the ideal sheaf attached to
`K` agree over `Spec R`, but only as a `Nonempty`. This file names the comparison, so that later
statements can mention it.

## Main results

* `Stacks.Blowup.overIsoBlowUpToBase` and `Stacks.Blowup.affineBlowUpIso`: the comparison over the
  base and as schemes.
* `Stacks.Blowup.overIsoBlowUpToBase_hom_left_comp` and `Stacks.Blowup.affineBlowUpIso_hom_comp`:
  they carry one blowup morphism to the other.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Blowup

variable (R : Type u) [CommRing R] (K : Ideal R)

/-- **The comparison of the two blowups of `Spec R` in `K`, as a named isomorphism over
`Spec R`.** This is `Stacks.Blowup.nonempty_over_iso_blowUpToBase` with a name, so that it can
appear in the statement of a lemma; an `obtain` on the `Nonempty` produces a local variable that
no later statement can mention, and that was the only obstacle to using the comparison rather
than reproving things on each model.

The companion `Stacks.Blowup.overIsoBlowUpToBase_hom_left_comp` records that it carries one
blowup morphism to the other, mirroring `Stacks.Blowup.blowUpOverIso_hom_left_comp`.

**What this does and does not unblock.** Anything that depends only on the isomorphism class of
the blowup over the base — irreducibility, dimension, properness of the total space — transports
along this. Statements about the *exceptional divisor* do not: they need the analogue of
`AlgebraicGeometry.comap_exceptionalIdeal_blowUpIso_hom`, which identifies the two exceptional
ideals along the comparison, and no such lemma exists for this comparison. Proving one is
obstructed by the opacity recorded in the implementation notes above: the morphisms this
isomorphism is built from are introduced by `obtain`, so `Stacks.Blowup.exceptionalIdeal` cannot
be computed along them. -/
noncomputable def overIsoBlowUpToBase :
    Over.mk (toSpec K) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K))) :=
  (nonempty_over_iso_blowUpToBase R K).some

/-- The comparison isomorphism carries the affine blowup morphism to the ideal-sheaf one. -/
theorem overIsoBlowUpToBase_hom_left_comp :
    (overIsoBlowUpToBase R K).hom.left ≫ AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K)) =
      toSpec K :=
  Over.w (overIsoBlowUpToBase R K).hom

/-- The comparison of the two blowups of `Spec R` in `K`, as an isomorphism of schemes. -/
noncomputable def affineBlowUpIso :
    blowUpSpec K ≅
      AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K)) :=
  (Over.forget (Spec (CommRingCat.of R))).mapIso (overIsoBlowUpToBase R K)

/-- The scheme-level comparison carries the affine blowup morphism to the ideal-sheaf one. -/
@[simp]
theorem affineBlowUpIso_hom_comp :
    (affineBlowUpIso R K).hom ≫ AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K)) =
      toSpec K :=
  overIsoBlowUpToBase_hom_left_comp R K

end Stacks.Blowup

end
