module

public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# Inverse images along an open immersion of closed subsets proper over the base

Let `f : X ⟶ Y` be an open immersion of algebraic spaces over a scheme `S`, let `g : Y ⟶ A` be
locally of finite type, and let `T` be a closed subset of `|Y|` proper over `A` (Stacks 0CZD)
which is contained in the image of `|X|`.  Then the inverse image `f⁻¹(T)` is a closed subset of
`|X|` proper over `A`.

The reduced induced subspace `Z` on `T` pulls back along `f` to a subspace `W` of `X`, and the
projection `W ⟶ Z` is a base change of `f`, hence an open immersion; it is surjective on points
by Stacks 03H4, because every point of `Z` lies in the image of `|X|`.  An open immersion
surjective on points is an isomorphism, so `W` is proper over `A`, and the reduced induced
subspace on `f⁻¹(T)` factors through `W` by Stacks 03JJ.  This is the argument of the inverse
image clause of Stacks 0CZG with properness of the base change of `f` replaced by its being an
isomorphism over `T`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_preimage_of_isOpenImmersion`: the inverse image of a
  closed subset proper over the base and contained in the image of an open immersion is proper
  over the base.

## References

* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Inverse image along an open immersion of a closed subset proper over the base.**  If
`f : X ⟶ Y` is an open immersion and the closed subset `T` of `|Y|`, proper over `A`, lies in the
image of `|X|`, then `f⁻¹(T)` is proper over `A`. -/
theorem isProperOver_preimage_of_isOpenImmersion (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (g : Y ⟶ A) (hf : IsOpenImmersion B S hS f)
    (hXft : IsLocallyOfFiniteType B S hS (f ≫ g))
    (hYft : IsLocallyOfFiniteType B S hS g)
    (T : Set (points B S hS Y)) (hT : IsClosed T)
    (hTf : T ⊆ Set.range (pointsMap B S hS X f))
    (hTproper : IsProperOver B S hS hY hA g hYft T hT) :
    IsProperOver B S hS hX hA (f ≫ g) hXft (pointsMap B S hS X f ⁻¹' T)
      (isClosed_preimage_pointsMap B S hS hX hY f hT) := by
  set Z := reducedClosedSubspace B S hS Y hY T hT with hZdef
  have hZalg : IsAlgebraicSpace B S hS Z.toFunctor :=
    hZdef ▸ isAlgebraicSpace_reducedClosedSubspace B S hS Y hY T hT
  set W := Z.preimage f with hWdef
  have hsqW : IsPullback (Z.fromPreimage f) W.ι Z.ι f := Subfunctor.isPullback_preimage f Z
  have hWalg : IsAlgebraicSpace B S hS W.toFunctor :=
    isAlgebraicSpace_of_isPullback hZalg hX hY.isSheaf hY.diagonal_representable hsqW
  -- the projection `W ⟶ Z` is an open immersion surjective on points, hence an isomorphism
  have hoi : IsOpenImmersion B S hS (Z.fromPreimage f) := by
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqW.flip hf
  have hsurj : Function.Surjective (pointsMap B S hS W.toFunctor (Z.fromPreimage f)) := by
    intro z
    have hzT : pointsMap B S hS Z.toFunctor Z.ι z ∈ T := by
      rw [← range_pointsMap_ι_reducedClosedSubspace B S hS Y hY T hT]
      exact ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := hTf hzT
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS hsqW z x hx.symm
    exact ⟨w, hw⟩
  have : IsIso (Z.fromPreimage f) :=
    isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS _ hoi hsurj
  have hbase : IsProper B S hS (Z.fromPreimage f) := isProper_of_isIso B S hS _
  have hWproper : IsProper B S hS (W.ι ≫ (f ≫ g)) := by
    have hcomp := isProper_comp B S hS hWalg hZalg hA (Z.fromPreimage f) (Z.ι ≫ g)
      hbase hTproper
    rwa [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc] at hcomp
  -- the reduced induced subspace on the inverse image of `T` maps to the one on `T`
  have hrange : Set.range (pointsMap B S hS
      (reducedClosedSubspace B S hS X hX (pointsMap B S hS X f ⁻¹' T)
        (isClosed_preimage_pointsMap B S hS hX hY f hT)).toFunctor
      ((reducedClosedSubspace B S hS X hX (pointsMap B S hS X f ⁻¹' T)
        (isClosed_preimage_pointsMap B S hS hX hY f hT)).ι ≫ f)) ⊆ T := by
    rw [pointsMap_comp, Set.range_comp, range_pointsMap_ι_reducedClosedSubspace]
    exact Set.image_preimage_subset _ _
  obtain ⟨u, hu⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS Y hY
    T hT
    (isAlgebraicSpace_reducedClosedSubspace B S hS X hX _
      (isClosed_preimage_pointsMap B S hS hX hY f hT))
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX _
      (isClosed_preimage_pointsMap B S hS hX hY f hT))
    ((reducedClosedSubspace B S hS X hX (pointsMap B S hS X f ⁻¹' T)
      (isClosed_preimage_pointsMap B S hS hX hY f hT)).ι ≫ f)).2 hrange
  exact isProperOver_of_isProper_ι_comp B S hS hX hA (f ≫ g) hXft _
    (isClosed_preimage_pointsMap B S hS hX hY f hT) W hWalg hWproper
    (hsqW.lift u _ hu) (hsqW.lift_snd u _ hu)

end AlgebraicGeometry.Space

end
