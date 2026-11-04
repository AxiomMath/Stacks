module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionStalk

/-!
# Relative Tor amplitude of an object of `D(𝒪_X)`, read at the stalks

Let `f : X ⟶ S` be a morphism of schemes and `E` an object of `D(𝒪_X)`. The stalk at `x` of `E`,
read over `f^{-1}𝒪_S` through restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`, is the stalk `E_x`
of `E` as a module over the local ring `𝒪_{X, x}`, read over `𝒪_{S, f x}` along the stalk map of
`f`; this is the stalk spelling of `AlgebraicGeometry.HasTorAmplitudeOver`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.HasTorAmplitudeAtPoint`: `E_x` has Tor amplitude in `[a, b]`
  over `𝒪_{S, f x}`.

## Main results

* `Scheme.Hom.hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff_hasTorAmplitudeAtPoint`:
  the stalk of `E` read over `f^{-1}𝒪_S` against the stalkwise condition.
* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeOver_iff_forall_hasTorAmplitudeAtPoint`:
  `AlgebraicGeometry.HasTorAmplitudeOver` is the same stalkwise condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`E_x` has Tor amplitude in `[a, b]` over `𝒪_{S, f x}`**: the derived stalk of `E` at `x`,
read over the local ring of `S` at `f x` along the stalk map of `f`. -/
def HasTorAmplitudeAtPoint (E : DerivedCategory X.Modules) (x : X) (a b : ℤ) : Prop :=
  HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
    ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.obj E)) a b

/-- `HasTorAmplitudeAtPoint` is invariant under isomorphism in `D(𝒪_X)`: if `E ≅ E'` and `E_x`
has Tor amplitude in `[a, b]` over `𝒪_{S, f x}`, then so does `E'_x`. -/
theorem HasTorAmplitudeAtPoint.of_iso {E E' : DerivedCategory X.Modules} (e : E ≅ E') {x : X}
    {a b : ℤ} (h : HasTorAmplitudeAtPoint f E x a b) : HasTorAmplitudeAtPoint f E' x a b :=
  AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.mapIso
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.mapIso e)) a b h

variable (x : X)

/-- **The stalk of a restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`, over `𝒪_{S, f x}`.** The
stalk at `x` of an `𝒪_X`-module read over `f^{-1}𝒪_S` is its stalk over `𝒪_{X, x}`, read over
`𝒪_{S, f x}` along the stalk map of `f` and then over `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}`. -/
def stalkFunctorScalarRestrictionModulesStalkIso :
    scalarRestriction f ⋙
        SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) x ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x ⋙
        ModuleCat.restrictScalars.{u} (f.stalkMap x).hom ⋙
          ModuleCat.restrictScalars.{u} (inverseImageStalkRingEquiv f x).toRingHom :=
  stalkFunctorScalarRestrictionIso f x ≪≫
    Functor.isoWhiskerLeft _
      (ModuleCat.restrictScalarsComp'.{u}
          (inverseImageStalkRingEquiv f x).toRingHom
          ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
            (f.stalkMap x).hom)
          (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom
          (by
            rw [RingHom.comp_assoc, ← commStalkRingEquiv_comp_ringStalkMap f x]
            ext r
            exact ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm_apply_apply _).symm) ≪≫
        Functor.isoWhiskerRight
          (ModuleCat.restrictScalarsComp'.{u} (f.stalkMap x).hom
            (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom _ rfl) _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (AffineRelativeTorAmplitude.modulesStalkRestrictScalarsFunctorIso X x) _

/-- `E_x` has Tor amplitude in `[a, b]` over `𝒪_{S, f x}` exactly when the relative stalk complex
at `x` of a complex representing `E` does. -/
theorem hasTorAmplitudeAtPoint_Q_iff (K : CochainComplex X.Modules ℤ) (a b : ℤ) :
    HasTorAmplitudeAtPoint f (DerivedCategory.Q.obj K) x a b ↔
      HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
        (DerivedCategory.Q.obj (relativeStalkComplex f K x)) a b :=
  ⟨fun h => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (relativeStalkComplexDerivedIso f K x).symm a b h,
    fun h => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (relativeStalkComplexDerivedIso f K x) a b h⟩

attribute [local instance] commRing_stalk_inverseImage

/-- Restriction of scalars along `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}` is additive. -/
local instance additive_restrictScalars_inverseImageStalkRingEquiv :
    (ModuleCat.restrictScalars.{u} (inverseImageStalkRingEquiv f x).toRingHom).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- **The stalk of `E` read over `f^{-1}𝒪_S`, as a complex.** For `K` a complex of
`𝒪_X`-modules, the derived stalk at `x` of `K` read over `f^{-1}𝒪_S` is the relative stalk
complex of `K` at `x`, read over `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}`. -/
def stalkDerivedScalarRestrictionQIso (K : CochainComplex X.Modules ℤ) :
    (SheafOfModules.stalkFunctor (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.obj
        ((derivedScalarRestriction f).obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{u}
            (inverseImageStalkRingEquiv f x).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (relativeStalkComplex f K x)) :=
  (SheafOfModules.stalkFunctor (structureSheafOfRings.{u}
      (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.mapIso
      ((derivedScalarRestrictionFactors f).app K) ≪≫
    (SheafOfModules.stalkFunctor (structureSheafOfRings.{u}
      (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.Hom.isoOfComponents
        (fun i => (stalkFunctorScalarRestrictionModulesStalkIso f x).app (K.X i))
        (fun i j _ => (stalkFunctorScalarRestrictionModulesStalkIso f x).hom.naturality (K.d i j)))

/-- **Stalks of `E` over `f^{-1}𝒪_S` and over `𝒪_{S, f x}`.** The derived stalk at `x` of `E`
read over `f^{-1}𝒪_S` has Tor amplitude in `[a, b]` over `(f^{-1}𝒪_S)_x` exactly when `E_x` has
Tor amplitude in `[a, b]` over `𝒪_{S, f x}`. -/
theorem hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff_hasTorAmplitudeAtPoint
    (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x))
        ((SheafOfModules.stalkFunctor (structureSheafOfRings.{u}
          (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.obj
          ((derivedScalarRestriction f).obj E)) a b ↔
      HasTorAmplitudeAtPoint f E x a b := by
  let K := DerivedCategory.Q.objPreimage E
  have eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have e₁ := (SheafOfModules.stalkFunctor (structureSheafOfRings.{u}
      (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.mapIso
    ((derivedScalarRestriction f).mapIso eK.symm) ≪≫ stalkDerivedScalarRestrictionQIso f x K
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine HasTorAmplitudeAtPoint.of_iso f eK ((hasTorAmplitudeAtPoint_Q_iff f x K a b).2 ?_)
    exact (AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff
      (inverseImageStalkRingEquiv f x) _ a b).1
      (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₁ a b h)
  · refine AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₁.symm a b ?_
    exact (AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff
      (inverseImageStalkRingEquiv f x) _ a b).2
      ((hasTorAmplitudeAtPoint_Q_iff f x K a b).1 (HasTorAmplitudeAtPoint.of_iso f eK.symm h))

/-- **Tor amplitude over the base is the stalkwise condition.** `E` has Tor amplitude in `[a, b]`
relative to `f`, in the sense of `AlgebraicGeometry.HasTorAmplitudeOver`, exactly when `E_x` has
Tor amplitude in `[a, b]` over `𝒪_{S, f x}` for every `x`. -/
theorem hasTorAmplitudeOver_iff_forall_hasTorAmplitudeAtPoint (E : DerivedCategory X.Modules)
    (a b : ℤ) :
    HasTorAmplitudeOver f E a b ↔ ∀ x : X, HasTorAmplitudeAtPoint f E x a b :=
  ⟨fun ⟨K, ⟨e⟩, hK⟩ x => HasTorAmplitudeAtPoint.of_iso f e
    ((hasTorAmplitudeAtPoint_Q_iff f x K a b).2
      ((hasTorAmplitudeCanonical_iff_lift _ _ a b).2 (hK x))),
    fun h => ⟨DerivedCategory.Q.objPreimage E, ⟨DerivedCategory.Q.objObjPreimageIso E⟩,
      fun x => (hasTorAmplitudeCanonical_iff_lift _ _ a b).1
        ((hasTorAmplitudeAtPoint_Q_iff f x _ a b).1
          (HasTorAmplitudeAtPoint.of_iso f (DerivedCategory.Q.objObjPreimageIso E).symm
            (h x)))⟩⟩

/-- **Stacks 09U9 for an object read over `f⁻¹𝒪_S`.**  `E` read over `f⁻¹𝒪_S` has Tor amplitude
in `[a, b]` exactly when `E_x` has Tor amplitude in `[a, b]` over `𝒪_{S, f x}` for every `x`. -/
theorem hasTorAmplitude_derivedScalarRestriction_iff_forall_hasTorAmplitudeAtPoint
    (E : DerivedCategory X.Modules) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
        (RingedSpace.inverseImage S.toRingedSpace f.base) ((derivedScalarRestriction f).obj E) a b ↔
      ∀ x : X, HasTorAmplitudeAtPoint f E x a b :=
  (Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff _ _ a b).trans
    (forall_congr' fun x =>
      hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff_hasTorAmplitudeAtPoint f x E a b)

/-- **Locally finite Tor dimension over `f⁻¹𝒪_S`, read at the stalks.**  `E` read over
`f⁻¹𝒪_S` locally has finite Tor dimension exactly when `X` has an open covering with a single
interval `[a, b]` on each member bounding the Tor amplitude of `E_y` over `𝒪_{S, f y}` for every
`y` in that member. -/
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_iff_cover_hasTorAmplitudeAtPoint
    (E : DerivedCategory X.Modules) :
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension
        (RingedSpace.inverseImage S.toRingedSpace f.base) ((derivedScalarRestriction f).obj E) ↔
      ∃ (I : Type u) (U : I → TopologicalSpace.Opens X), iSup U = ⊤ ∧
        ∀ i : I, ∃ a b : ℤ, ∀ y : X, y ∈ U i → HasTorAmplitudeAtPoint f E y a b :=
  exists_congr fun _ => exists_congr fun U => and_congr Iff.rfl <| forall_congr' fun i =>
    exists_congr fun a => exists_congr fun b =>
      (Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk _ (U i) _ a b).trans
        (forall_congr' fun y => forall_congr' fun _ =>
          hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff_hasTorAmplitudeAtPoint
            f y E a b)

end AlgebraicGeometry.Scheme.Hom

end
