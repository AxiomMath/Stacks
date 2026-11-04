module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FibreProductConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Base change of an algebraic space to the completion of a local base ring

Let `A` be a local ring with maximal ideal `𝔪` and let `A^` be its `𝔪`-adic completion. For
an algebraic space `X` over `Spec A` we construct the base change `X ×_{Spec A} Spec A^`: it is
again an algebraic space, it is decent as soon as `X` is, and for Noetherian `A` its projection to
`X` is flat and surjective on points and the base change is locally Noetherian whenever `X` is
locally of finite type over `Spec A`.

## Main definitions

* `AlgebraicGeometry.Space.completionBase`: the object `Spec A^` of the big fppf site over
  `Spec A`, equipped with the morphism induced by `A → A^`.
* `AlgebraicGeometry.Space.completionBaseMap`: the morphism of algebraic spaces represented
  by that structure morphism.
* `AlgebraicGeometry.Space.completionSpace`: the fibre product `X ×_{Spec A} Spec A^`.
* `AlgebraicGeometry.Space.completionProjection`: its projection to `X`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_completionSpace`: the base change is an
  algebraic space.
* `AlgebraicGeometry.Space.isDecentSpace_completionSpace`: the base change of a decent
  algebraic space is decent.
* `AlgebraicGeometry.Space.isFlat_completionProjection`: for Noetherian `A` the projection to
  `X` is flat.
* `AlgebraicGeometry.Space.isSurjective_completionProjection`: for Noetherian `A` the
  projection to `X` is surjective on points.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_completionSpace`: for
  Noetherian `A` the base change of a space locally of finite type over `Spec A` is locally
  Noetherian.

## References

* [Stacks Project, Tag 0BHQ](https://stacks.math.columbia.edu/tag/0BHQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

noncomputable section

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable (hAc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))

/-! ### The completed base -/

/-- The spectrum of the `𝔪`-adic completion of a local ring `A`, regarded as an object of the
big fppf site over `Spec A` through the morphism induced by `A → A^`. -/
def completionBase : BigFppfOver B (Spec (.of A)) hA :=
  Over.mk (B.inclusion.preimage (X := B.obj hAc) (Y := B.obj hA)
    (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))))

/-- The structure morphism of `AlgebraicGeometry.Space.completionBase`, read as a morphism of
the big fppf site over `Spec A` with target the terminal object `Spec A`. -/
private def completionHom :
    completionBase A B hA hAc ⟶ Over.mk (𝟙 (B.obj hA)) :=
  Over.homMk (completionBase A B hA hAc).hom (by simp)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.completionHom` is the
morphism `Spec A^ ⟶ Spec A` induced by `A → A^`. -/
private theorem toScheme_map_completionHom :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map (completionHom A B hA hAc) =
      Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :=
  B.inclusion.map_preimage _

/-- The structure morphism `Spec A^ ⟶ Spec A` as a morphism of algebraic spaces over
`Spec A`. -/
def completionBaseMap :
    yoneda.obj (completionBase A B hA hAc) ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))) :=
  yoneda.map (Over.homMk (completionBase A B hA hAc).hom (by simp))

/-- `AlgebraicGeometry.Space.completionBaseMap` is the Yoneda image of
`AlgebraicGeometry.Space.completionHom`. -/
private theorem completionBaseMap_eq :
    completionBaseMap A B hA hAc = yoneda.map (completionHom A B hA hAc) := rfl

/-- The algebraic space represented by `AlgebraicGeometry.Space.completionBase`. -/
private theorem isAlgebraicSpace_yoneda_completionBase :
    IsAlgebraicSpace B (Spec (.of A)) hA (yoneda.obj (completionBase A B hA hAc)) :=
  isAlgebraicSpace_yoneda B (Spec (.of A)) hA (completionBase A B hA hAc)

omit [IsLocalRing A] in
/-- The algebraic space represented by the terminal object `Spec A` of the site. -/
private theorem isAlgebraicSpace_yoneda_base :
    IsAlgebraicSpace B (Spec (.of A)) hA (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) :=
  isAlgebraicSpace_yoneda B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))

/-! ### The base change -/

variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))

/-- The base change `X ×_{Spec A} Spec A^` of an algebraic space `X` over `Spec A` to the
`𝔪`-adic completion of `A`. -/
def completionSpace : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u :=
  pullback f (completionBaseMap A B hA hAc)

/-- The projection `X ×_{Spec A} Spec A^ ⟶ X` of the completed base change. -/
def completionProjection : completionSpace A B hA hAc f ⟶ X :=
  pullback.fst f (completionBaseMap A B hA hAc)

/-- The base change of an algebraic space over `Spec A` to the completion `Spec A^` is an
algebraic space. -/
theorem isAlgebraicSpace_completionSpace (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) :
    IsAlgebraicSpace B (Spec (.of A)) hA (completionSpace A B hA hAc f) :=
  isAlgebraicSpace_pullback B (Spec (.of A)) hA f (completionBaseMap A B hA hAc) hX
    (isAlgebraicSpace_yoneda_completionBase A B hA hAc) (isAlgebraicSpace_yoneda_base A B hA)

/-- The base change of a decent algebraic space over `Spec A` to the completion `Spec A^` is
decent. -/
theorem isDecentSpace_completionSpace (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXdec : IsDecentSpace B (Spec (.of A)) hA X) :
    IsDecentSpace B (Spec (.of A)) hA (completionSpace A B hA hAc f) :=
  isDecentSpace_pullback B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda_base A B hA)
    (isAlgebraicSpace_yoneda_completionBase A B hA hAc) f (completionBaseMap A B hA hAc) hXdec
    (isDecentSpace_yoneda B (Spec (.of A)) hA (completionBase A B hA hAc))

/-! ### Flatness, surjectivity and local Noetherianity -/

variable [IsNoetherianRing A]

/-- For a Noetherian local ring `A`, the structure morphism `Spec A^ ⟶ Spec A` is a flat
morphism of algebraic spaces over `Spec A`. -/
private theorem isFlat_completionBaseMap :
    IsFlat B (Spec (.of A)) hA (completionBaseMap A B hA hAc) := by
  rw [completionBaseMap_eq]
  refine isFlat_yoneda_map B (Spec (.of A)) hA (completionHom A B hA hAc) ?_
  rw [toScheme_map_completionHom]
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- For a Noetherian local ring `A`, the structure morphism `Spec A^ ⟶ Spec A` is surjective on
points. -/
private theorem isSurjective_completionBaseMap :
    IsSurjective B (Spec (.of A)) hA (completionBaseMap A B hA hAc) := by
  rw [completionBaseMap_eq]
  refine isSurjective_yoneda_map B (Spec (.of A)) hA (completionHom A B hA hAc) ?_
  rw [toScheme_map_completionHom]
  have : Module.FaithfullyFlat A (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson (IsLocalRing.maximalIdeal A)
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  exact ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2

/-- For a Noetherian local ring `A`, the projection `X ×_{Spec A} Spec A^ ⟶ X` of the completed
base change is flat. -/
theorem isFlat_completionProjection (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) :
    IsFlat B (Spec (.of A)) hA (completionProjection A B hA hAc f) :=
  holdsOnEveryEtaleChart_pullback_fst_of_isAlgebraicSpace B (Spec (.of A)) hA
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    Flat.isEtaleLocalOnSourceAndTarget inferInstance
    (isAlgebraicSpace_yoneda_completionBase A B hA hAc) (isAlgebraicSpace_yoneda_base A B hA) hX
    f (completionBaseMap A B hA hAc) (isFlat_completionBaseMap A B hA hAc)

/-- For a Noetherian local ring `A`, the projection `X ×_{Spec A} Spec A^ ⟶ X` of the completed
base change is surjective on points. -/
theorem isSurjective_completionProjection :
    Function.Surjective (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
      (completionProjection A B hA hAc f)) :=
  surjective_pointsMap_of_isPullback B (Spec (.of A)) hA
    (IsPullback.of_hasPullback f (completionBaseMap A B hA hAc)).flip
    (isSurjective_completionBaseMap A B hA hAc)

/-- The base change to `Spec A^` of an algebraic space locally of finite type over the
spectrum of a Noetherian local ring is locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_completionSpace
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f) :
    HasEtaleLocalProperty B (Spec (.of A)) hA (completionSpace A B hA hAc f)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  have hft : IsLocallyOfFiniteType B (Spec (.of A)) hA
      (pullback.snd f (completionBaseMap A B hA hAc)) :=
    holdsOnEveryEtaleChart_pullback_snd_of_isAlgebraicSpace B (Spec (.of A)) hA
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget inferInstance hX
      (isAlgebraicSpace_yoneda_base A B hA) (isAlgebraicSpace_yoneda_completionBase A B hA hAc)
      f (completionBaseMap A B hA hAc) hf
  refine isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of A)) hA
    (isAlgebraicSpace_completionSpace A B hA hAc f hX)
    (isAlgebraicSpace_yoneda_completionBase A B hA hAc)
    (pullback.snd f (completionBaseMap A B hA hAc)) hft ?_
  refine hasEtaleLocalProperty_of_representable B (Spec (.of A)) hA _ _
    (completionBase A B hA hAc) (Iso.refl _) ?_
  show IsLocallyNoetherian
    (Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
  infer_instance

end

end AlgebraicGeometry.Space

end
