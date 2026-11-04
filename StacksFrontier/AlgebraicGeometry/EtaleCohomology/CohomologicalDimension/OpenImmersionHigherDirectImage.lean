module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.StrictHenselizationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleVanishing

/-!
# Higher direct images along an open immersion vanish on the open

Let `j : U ⟶ Y` be a quasi-compact open immersion and `𝓕` an abelian sheaf on `U_ét`. For
`q > 0` the stalk of `R^qj_*𝓕` at a geometric point of `Y` lying over `U` vanishes, so the
higher direct images `R^qj_*𝓕` are supported on the complement of `U`. This is the first
assertion of Interlude I in the proof of Stacks 0F0V.

By Stacks 03Q9 (in the form
`AlgebraicGeometry.isZero_stalk_rightDerived_iff_subsingleton_sheafH`) the stalk is the
cohomology `H^q(U ×_Y Spec(𝒪^{sh}_{Y,ȳ}), p⁻¹𝓕)`. The canonical morphism
`Spec(𝒪^{sh}_{Y,ȳ}) ⟶ Y` lands in the generizations of the image `y` of the point, which lie in the
open `U`; so it factors through `j`, and the base change `U ×_Y Spec(𝒪^{sh}_{Y,ȳ}) ⟶
Spec(𝒪^{sh}_{Y,ȳ})` is an isomorphism. The spectrum of a strictly henselian local ring has no
higher étale cohomology (Stacks 03QO).

## Main results

* `AlgebraicGeometry.isZero_stalk_rightDerived_smallEtalePushforwardAb_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **Higher direct images along an open immersion vanish over the open.** Let `j : U ⟶ Y` be a
quasi-compact open immersion, `𝓕` an abelian sheaf on `U_ét`, `q > 0`, and `s` a geometric point
of `Y` lying over `U`. Then the stalk of `R^qj_*𝓕` at `s` is zero. -/
public theorem isZero_stalk_rightDerived_smallEtalePushforwardAb_of_isOpenImmersion
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] (s : GeometricPoint Y)
    (hs : s.hom (IsLocalRing.closedPoint s.residueField) ∈ Set.range j)
    (F : Sheaf (smallEtaleTopology U) Ab.{u + 1}) (q : ℕ) (hq : 0 < q) :
    IsZero ((smallEtaleStalkAb s.hom).obj
      (((smallEtalePushforwardAb j).rightDerived q).obj F)) := by
  let B := BigEtaleSite.containing Y
  have hS : B.Contains Y := BigEtaleSite.contains_containing _
  refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS j s F q).2 ?_
  -- the strict henselization maps into `U`
  have hrange : Set.range (strictHenselizationToBase B Y hS s) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    have hz : strictHenselizationToBase B Y hS s z ∈
        Set.range (Y.fromSpecStalk (s.hom (IsLocalRing.closedPoint s.residueField))) := by
      rw [strictHenselizationToBase, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [range_fromSpecStalk] at hz
    exact (j.isOpenEmbedding.isOpen_range.stableUnderGeneralization hz) hs
  let e := strictHenselizationBaseChangeToStrictHenselization B hS j s
  have hiso : IsIso e := by
    change IsIso (pullback.snd j (strictHenselizationToBase B Y hS s))
    rw [← IsOpenImmersion.lift_fac j (strictHenselizationToBase B Y hS s) hrange]
    infer_instance
  have := etaleLocalRing_strictHenselian B Y hS s
  exact (sheafHSmallEtalePushforwardAddEquiv e _ q).toEquiv.subsingleton_congr.2
    (Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology
      (↥(etaleLocalRing B Y hS s))
      ((smallEtalePushforwardAb e).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj F)) q hq)

end AlgebraicGeometry

end
