module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange

/-!
# Tor amplitude over `f⁻¹𝒪_S` and Tor amplitude over the base, stalkwise

Let `f : X ⟶ S` be a morphism of schemes and `E` an object of `D(𝒪_X)`. Reading `E` as an object
of `D(f⁻¹𝒪_S)` and asking for Tor amplitude in `[a, b]` on the ringed space `(X, f⁻¹𝒪_S)` is the
same as asking that every stalk complex of `E`, read over the local ring `𝒪_{S, f x}`, has Tor
amplitude in `[a, b]`, which is `AlgebraicGeometry.HasTorAmplitudeOver`.

## Main results

* `AlgebraicGeometry.hasTorAmplitudeOver_iff_hasTorAmplitude_derivedScalarRestriction`: the
  equivalence, for every interval.

## Implementation notes

The sheaf side is reduced to the stalks of `f⁻¹𝒪_S` by [Stacks, Tag 09U9]
(`Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff`), and the
coefficient ring is moved to `𝒪_{S, f x}` by
`AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff`. What is left is
the identification, at a representing complex, of the derived stalk read through the
`RingCat`-valued stalk of `𝒪_X` with the stalk complex read through the local ring; that is done
on complexes, by `AlgebraicGeometry.stalkComplexIso` and `ModuleCat.restrictScalarsComp'`, so that
no derived functor of a composite of restrictions of scalars is formed.

## References

* [Stacks Project, Tag 09U9](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- Restriction of scalars along any ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_any''
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along any ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_any''
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along any ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_any''
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The relative stalk complex of a representative is the derived stalk read over the base.**
For `K` representing `E`, the stalk complex of `K` at `x` read over `𝒪_{S, f x}` is, in the
derived category, the derived stalk of `E` through the `RingCat`-valued stalk of `𝒪_X`, read over
`𝒪_{S, f x}` along the stalk map of `f`. -/
def relativeStalkComplexDerivedStalkIso (K : CochainComplex X.Modules ℤ)
    (E : DerivedCategory X.Modules) (e : DerivedCategory.Q.obj K ≅ E) (x : X) :
    DerivedCategory.Q.obj (relativeStalkComplex f K x) ≅
      (ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
            (f.stalkMap x).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E) :=
  DerivedCategory.Q.mapIso
      (((ModuleCat.restrictScalars (f.stalkMap x).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso (stalkComplexIso x K).symm ≪≫
        ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp'.{u} (f.stalkMap x).hom
            (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom
            ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
              (f.stalkMap x).hom) rfl) (ComplexShape.up ℤ)).app _).symm) ≪≫
    ((ModuleCat.restrictScalars.{u}
        ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
          (f.stalkMap x).hom)).mapDerivedCategoryFactors.app _).symm ≪≫
    (ModuleCat.restrictScalars.{u}
        ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
          (f.stalkMap x).hom)).mapDerivedCategory.mapIso
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategoryFactors.app K).symm ≪≫
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.mapIso e)

/-- **Tor amplitude over the base is a pointwise condition on the derived stalks.** An object `E`
of `D(𝒪_X)` has Tor amplitude in `[a, b]` over `S` exactly when, at every point `x`, its derived
stalk read over `𝒪_{S, f x}` has Tor amplitude in `[a, b]`. The representing complex of
`AlgebraicGeometry.HasTorAmplitudeOver` can be any one, by
`AlgebraicGeometry.relativeStalkAmplitude_of_derivedIso`. -/
theorem hasTorAmplitudeOver_iff_forall_derivedStalk (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver f E a b ↔ ∀ x : X,
      HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
        ((ModuleCat.restrictScalars.{u}
            ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
              (f.stalkMap x).hom)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E)) a b := by
  constructor
  · rintro ⟨K, ⟨e⟩, hK⟩ x
    exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (relativeStalkComplexDerivedStalkIso f K E e x) a b
      ((hasTorAmplitudeCanonical_iff_lift _ _ a b).2 (hK x))
  · intro h
    refine ⟨DerivedCategory.Q.objPreimage E, ⟨DerivedCategory.Q.objObjPreimageIso E⟩,
      fun x => (hasTorAmplitudeCanonical_iff_lift _ _ a b).1 ?_⟩
    exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (relativeStalkComplexDerivedStalkIso f _ E (DerivedCategory.Q.objObjPreimageIso E) x).symm
      a b (h x)

/-- **Tor amplitude over `f⁻¹𝒪_S` is Tor amplitude over the base.** An object `E` of `D(𝒪_X)`,
read in `D(f⁻¹𝒪_S)`, has Tor amplitude in `[a, b]` on the ringed space `(X, f⁻¹𝒪_S)` exactly when
it has Tor amplitude in `[a, b]` over `S` in the stalkwise sense of
`AlgebraicGeometry.HasTorAmplitudeOver`.

The left side is read at the stalks of `f⁻¹𝒪_S` by [Stacks, Tag 09U9], the coefficient ring is
moved to `𝒪_{S, f x}` by `Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff`, and the
result is `hasTorAmplitudeOver_iff_forall_derivedStalk`. -/
theorem hasTorAmplitude_derivedScalarRestriction_iff_hasTorAmplitudeOver
    (E : DerivedCategory X.Modules) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
        (RingedSpace.inverseImage S.toRingedSpace f.base)
        ((Scheme.Hom.derivedScalarRestriction f).obj E) a b ↔
      HasTorAmplitudeOver f E a b :=
  ((Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff _ _
      a b).trans (forall_congr' fun x =>
        Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff f x E a b)).trans
    (hasTorAmplitudeOver_iff_forall_derivedStalk f E a b).symm

/-- **Finite Tor dimension over `f⁻¹𝒪_S` is finite Tor dimension over the base.** -/
theorem hasFiniteTorDimension_derivedScalarRestriction_iff (E : DerivedCategory X.Modules) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
        (RingedSpace.inverseImage S.toRingedSpace f.base)
        ((Scheme.Hom.derivedScalarRestriction f).obj E) ↔
      ∃ a b : ℤ, HasTorAmplitudeOver f E a b :=
  exists_congr fun a => exists_congr fun b =>
    hasTorAmplitude_derivedScalarRestriction_iff_hasTorAmplitudeOver f E a b

end AlgebraicGeometry

end
