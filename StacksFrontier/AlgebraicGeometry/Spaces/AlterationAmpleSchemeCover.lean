module

public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffinePullback.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AlterationDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.AlterationInProperSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# A scheme cover of an integral proper algebraic space of no larger dimension

Let `Q` be an integral algebraic space, locally Noetherian and proper over an affine object `U`
of the big fppf site.  This file produces a scheme `P` of the site and a proper surjective
morphism `ρ : P ⟶ Q` such that `P` carries an ample invertible module and `dim P ≤ dim Q`.

This is the construction of the second proof of condition (3) in the source's proof of
Stacks 0DN4: Chow's lemma (Stacks 089J) gives a proper surjective `W ⟶ Q` from a scheme
H-quasi-projective over an affine scheme, hence carrying an ample invertible module; an integral
closed subscheme of `W` is an alteration of `Q` (Stacks 0DMN); and an alteration does not raise the
dimension (`AlgebraicGeometry.Space.dimension_le_of_isAlteration`).  The ample module of `W`
restricts to an ample module on the closed subscheme, a closed immersion being affine.

## Main results

* `AlgebraicGeometry.Space.exists_properSurjective_ampleSchemeCover_dimension_le`: the cover.

## References

* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 0DMN](https://stacks.math.columbia.edu/tag/0DMN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A proper surjective scheme cover with an ample invertible module and of no larger
dimension.**  Let `Q` be an integral, locally Noetherian algebraic space proper over an affine
object `U` of the site.  There are an object `P` of the site, a proper surjective
`ρ : P ⟶ Q`, and an ample invertible module on the scheme `P`, with `dim P ≤ dim Q`. -/
theorem exists_properSurjective_ampleSchemeCover_dimension_le (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (hQint : IsIntegralSpace B S hS Q)
    (hQN : HasEtaleLocalProperty B S hS Q (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (q : Q ⟶ yoneda.obj U) (hq : IsProper B S hS q) :
    ∃ (P : BigFppfOver B S hS) (ρ : yoneda.obj P ⟶ Q)
      (L : ((BigFppfOver.toScheme B S hS).obj P).Modules)
      (_ : Stacks.Ample.IsInvertibleModule _ L),
      Stacks.Ample.IsAmple _ L ∧ IsProper B S hS ρ ∧ IsSurjective B S hS ρ ∧
        dimension B S hS (yoneda.obj P) (isAlgebraicSpace_yoneda B S hS P) ≤
          dimension B S hS Q hQ := by
  obtain ⟨W, ρ₀, hρp, hρs, T, t, hT, htq⟩ :=
    exists_properSurjective_hQuasiProjective_schemeCover_of_isProper_toAffine B S hS U hU hQ q hq
  have : IsAffine T := hT
  obtain ⟨L₀, hL₀inv, hL₀amp⟩ := exists_isAmple_of_isHQuasiProjective t htq
  obtain ⟨Y, hYc, -, halt⟩ := exists_isClosedSubspace_isAlteration B S hS
    (isAlgebraicSpace_yoneda B S hS W) hQ hQint ρ₀ hρp hρs
  -- the closed subspace `Y` of the scheme `W` is represented by a closed subscheme `P`
  let hrep := hYc.2.rep
  let P := hrep.pullback (𝟙 (yoneda.obj W))
  have hpb := hrep.isPullback (𝟙 (yoneda.obj W))
  have : IsIso (hrep.fst (𝟙 (yoneda.obj W))) := hpb.isIso_fst_of_isIso
  let e := hrep.fst (𝟙 (yoneda.obj W))
  let r := (BigFppfOver.toScheme B S hS).map (hrep.snd (𝟙 (yoneda.obj W)))
  have hr : _root_.AlgebraicGeometry.IsClosedImmersion r :=
    hYc.2.property (𝟙 (yoneda.obj W)) _ _ hpb
  have : _root_.AlgebraicGeometry.IsAffineHom r := inferInstance
  have hPalg := isAlgebraicSpace_yoneda B S hS P
  have heci : IsClosedImmersion B S hS e := isClosedImmersion_of_isIso B S hS e
  exact ⟨P, e ≫ Y.ι ≫ ρ₀, (Scheme.Modules.pullback r).obj L₀,
    Stacks.InvertiblePullback.isInvertibleModule_pullback r L₀,
    Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom r L₀ hL₀amp,
    isProper_comp B S hS hPalg hYc.1 hQ e (Y.ι ≫ ρ₀)
      (isProper_of_isClosedImmersion B S hS hPalg hYc.1 e heci) halt.isProper,
    isSurjective_comp B S hS (isSurjective_of_isIso B S hS e)
      (isSurjective_of_isProper_of_isDominant B S hS hQ _ halt.isProper halt.isDominant),
    (dimension_le_of_isLocallyQuasiFinite B S hS hPalg hYc.1 e
      (isLocallyQuasiFinite_of_isImmersion B S hS e
        (isImmersion_of_isClosedImmersion B S hS heci))).trans
      (dimension_le_of_isAlteration B S hS hQ hYc.1 hQN _ halt)⟩

end AlgebraicGeometry.Space

end
