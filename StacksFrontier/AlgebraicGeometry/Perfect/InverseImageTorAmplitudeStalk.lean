module

public import StacksFrontier.AlgebraicGeometry.Perfect.ChartTorDimensionSectionsCrossing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeStalkwise
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeAffineTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject

/-!
# The two sheaf-side readings of finite Tor dimension over the base agree

Let `f : X ⟶ S` be a morphism of schemes and `E` an object of `D(𝒪_X)`. "`E` has Tor amplitude in
`[a, b]` over `f⁻¹𝒪_S`" has two readings in this development: the ringed-space one of
Stacks 08CG on the inverse-image ringed space `(X, f⁻¹𝒪_S)`, measured against the derived tensor
product of Stacks 06YU, and the stalkwise one of `AlgebraicGeometry.HasTorAmplitudeOver`, which
asks the stalk `E_x`, read over `𝒪_{S, f x}` along the stalk map of `f`, to have Tor amplitude in
`[a, b]` at every point `x`. This file proves that they agree on every open `U` of `X`, which is
`AlgebraicGeometry.Scheme.Hom.ChartTorSpellingsAgree`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff`:
  at a point `y` of `X`, the stalk of `E` read over `f⁻¹𝒪_S` has Tor amplitude in `[a, b]` over
  the stalk of `f⁻¹𝒪_S` exactly when the stalk of `E` read over `𝒪_{S, f y}` does.
* `AlgebraicGeometry.Scheme.Hom.relativeStalkHasTorAmplitude_restrictFunctor_iff`: the stalkwise
  condition is unchanged by restriction to an open subscheme.
* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeOver_comp_iff_of_isOpenImmersion`: nor by
  composing the base morphism with an open immersion.
* `AlgebraicGeometry.Scheme.Hom.chartTorSpellingsAgree`: **the two readings agree on every
  open.**

## Implementation notes

The ringed-space reading is local by Stacks 09U9 on an open subspace,
`Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk`, so both readings are
conditions at the points of `U`, and the content is the comparison at one point `y`. There the
stalk of `E` restricted along `f⁻¹𝒪_S ⟶ 𝒪_X` is the stalk of `E` restricted along the stalk map
`(f⁻¹𝒪_S)_y ⟶ 𝒪_{X, y}` (`AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso`),
and that ring map is the stalk map `𝒪_{S, f y} ⟶ 𝒪_{X, y}` of `f` after the comparison
`(f⁻¹𝒪_S)_y ≅ 𝒪_{S, f y}`
(`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap`), up to the
identification of the `RingCat`-valued stalks with the `CommRingCat`-valued ones
(`SemilinearStalk.commStalkRingEquiv`). Restricting scalars along a ring isomorphism does not move
Tor amplitude.

The stalkwise reading of `E|_U` over the restriction `f.resLE V U e : U ⟶ V` is moved to the
reading of `E` over `f` at the points of `U` by two invariances: changing the base along the open
immersion `V ⟶ S` changes the coefficient rings by the germ isomorphisms of that open immersion,
and the stalk of `E|_U` at a point of `U` is the extension of scalars of the stalk of `E` along
the germ isomorphism of `U ⟶ X` (Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`AlgebraicGeometry.pullbackRelativeStalkObjIso`).

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [The Stacks Project, Lemma 20.48.5 (09U9)](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude
open scoped AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace StacksDraft.TorAmplitude

/-- Canonical Tor amplitude of an object of `D(R)` is invariant under isomorphism. -/
private theorem hasTorAmplitudeCanonical_iff_of_iso {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) (a b : ℤ) :
    HasTorAmplitudeCanonical R K a b ↔ HasTorAmplitudeCanonical R L a b :=
  ⟨hasTorAmplitudeCanonical_of_iso e a b, hasTorAmplitudeCanonical_of_iso e.symm a b⟩

/-- Tor amplitude of the lift of an object of `D(R)` is invariant under isomorphism. -/
private theorem hasTorAmplitudeCanonicalLift_iff_of_iso {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) (a b : ℤ) :
    HasTorAmplitudeCanonicalLift.{u, u, u} K a b ↔ HasTorAmplitudeCanonicalLift.{u, u, u} L a b :=
  ⟨hasTorAmplitudeCanonicalLift_of_iso e a b, hasTorAmplitudeCanonicalLift_of_iso e.symm a b⟩

/-- **Tor amplitude over a ring is unchanged by precomposing the structure map with a ring
isomorphism.** If `ρ = σ ∘ e` with `e` a ring isomorphism, an object restricted along `ρ` has Tor
amplitude in `[a, b]` over the source of `ρ` exactly when, restricted along `σ`, it has Tor
amplitude in `[a, b]` over the source of `σ`. -/
public theorem hasTorAmplitudeCanonical_restrictScalars_comp_ringEquiv_iff
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (σ : R' →+* A) (ρ : R →+* A) (e : R ≃+* R') (h : ρ = σ.comp e.toRingHom)
    (N : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ) :
    HasTorAmplitudeCanonical R ((ModuleCat.restrictScalars ρ).mapDerivedCategory.obj N) a b ↔
      HasTorAmplitudeCanonical R' ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj N) a b := by
  have ei : (ModuleCat.restrictScalars ρ).mapDerivedCategory.obj N ≅
      (ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj N) :=
    ((Functor.mapDerivedCategoryCompIso
      (ModuleCat.restrictScalarsComp'.{u} e.toRingHom σ ρ h).symm).app N).symm
  refine (hasTorAmplitudeCanonical_iff_of_iso ei a b).trans ?_
  exact Stacks.Thickenings.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff' e _ a b

/-- **Extending scalars along a ring isomorphism and restricting along the composite does not
change Tor amplitude**, in either direction. If `τ = ρ ∘ σ` with `ρ` the ring map of an
isomorphism, a complex extended along `ρ` and restricted along `τ` has Tor amplitude in `[a, b]`
exactly when the complex restricted along `σ` does. -/
public theorem hasTorAmplitudeCanonicalLift_restrictScalars_extendScalars_iff
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (σ : R →+* A) (ρ : A →+* B) (τ : R →+* B) (e : A ≃+* B)
    (he : e.toRingHom = ρ) (hτ : τ = ρ.comp σ)
    (Z : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars τ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))) a b ↔
      HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) a b := by
  subst he
  have hiso := DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendRestrictScalarsCompIso σ τ e hτ)
      (ComplexShape.up ℤ)).app Z)
  exact hasTorAmplitudeCanonicalLift_iff_of_iso hiso a b

end StacksDraft.TorAmplitude

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The ringed-space reading at a point -/

/-- The stalk functor of the inverse-image ringed space `(X, f⁻¹𝒪_S)` at a point `y` of `X` is
additive. -/
local instance additive_stalkFunctor_inverseImage_torAmplitude (y : X) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y).Additive :=
  RingedSpace.additive_stalkFunctor (RingedSpace.inverseImage S.toRingedSpace f.base) y

/-- The stalk functor of the inverse-image ringed space `(X, f⁻¹𝒪_S)` at a point `y` of `X`
preserves finite limits. -/
local instance preservesFiniteLimits_stalkFunctor_inverseImage_torAmplitude (y : X) :
    PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y) :=
  RingedSpace.preservesFiniteLimits_stalkFunctor
    (RingedSpace.inverseImage S.toRingedSpace f.base) y

/-- The stalk functor of the inverse-image ringed space `(X, f⁻¹𝒪_S)` at a point `y` of `X`
preserves finite colimits. -/
local instance preservesFiniteColimits_stalkFunctor_inverseImage_torAmplitude (y : X) :
    PreservesFiniteColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y) :=
  RingedSpace.preservesFiniteColimits_stalkFunctor
    (RingedSpace.inverseImage S.toRingedSpace f.base) y

attribute [local instance] commRing_stalk_inverseImage_at

/-- **The stalk of the structural map, against the stalk map of `f`, in `RingCat`.** Through the
identifications of the `RingCat`-valued stalks with the `CommRingCat`-valued ones, the stalk at
`y` of `f⁻¹𝒪_S ⟶ 𝒪_X` is the stalk map of `f` precomposed with `(f⁻¹𝒪_S)_y ≅ 𝒪_{S, f y}`. -/
public theorem commStalkRingEquiv_comp_ringStalkMap_inverseImageRingToStructure (y : X) :
    (SemilinearStalk.commStalkRingEquiv X.presheaf y).toRingHom.comp
        (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom =
      (f.stalkMap y).hom.comp
        ((SemilinearStalk.commStalkRingEquiv
            (RingedSpace.inverseImage S.toRingedSpace f.base).presheaf y).trans
          (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f y).commRingCatIsoToRingEquiv
          ).toRingHom := by
  have hsq := Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap f y
  ext r
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (structureSheafOfRings (RingedSpace.inverseImage S.toRingedSpace f.base)).obj r
  have h1 : (SemilinearStalk.commStalkRingEquiv X.presheaf y)
      ((SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y)
        (TopCat.Presheaf.germ
          (structureSheafOfRings (RingedSpace.inverseImage S.toRingedSpace f.base)).obj
          U y hU s)) =
      X.presheaf.germ U y hU ((AlgebraicGeometry.inverseImageStructureMap f).hom.app _ s) :=
    (congrArg (SemilinearStalk.commStalkRingEquiv X.presheaf y)
      (SemilinearStalk.ringStalkMap_germ (inverseImageRingToStructure f).hom y U hU s)).trans
      (SemilinearStalk.commStalkRingEquiv_germ X.presheaf y U hU _)
  have h2 : (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f y).hom
      ((SemilinearStalk.commStalkRingEquiv
          (RingedSpace.inverseImage S.toRingedSpace f.base).presheaf y)
        (TopCat.Presheaf.germ
          (structureSheafOfRings (RingedSpace.inverseImage S.toRingedSpace f.base)).obj
          U y hU s)) =
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f y).hom
        ((RingedSpace.inverseImage S.toRingedSpace f.base).presheaf.germ U y hU s) :=
    congrArg (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f y).hom
      (SemilinearStalk.commStalkRingEquiv_germ _ y U hU s)
  have h3 : (f.stalkMap y) ((Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f y).hom
        ((RingedSpace.inverseImage S.toRingedSpace f.base).presheaf.germ U y hU s)) =
      X.presheaf.germ U y hU ((AlgebraicGeometry.inverseImageStructureMap f).hom.app _ s) :=
    (congrArg (fun t => t ((RingedSpace.inverseImage S.toRingedSpace f.base).presheaf.germ
        U y hU s)) (congrArg CommRingCat.Hom.hom hsq)).trans
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U y hU
        (AlgebraicGeometry.inverseImageStructureMap f).hom s)
  exact h1.trans (h3.symm.trans (congrArg (f.stalkMap y) h2.symm))

/-- **The stalk of `E` read over `f⁻¹𝒪_S`, against the stalk of `E` read over `𝒪_{S, f y}`.** At
a point `y` of `X`, the stalk at `y` of the restriction of scalars of `E` along `f⁻¹𝒪_S ⟶ 𝒪_X` has
Tor amplitude in `[a, b]` over the stalk of `f⁻¹𝒪_S` exactly when the stalk of `E`, read over the
local ring `𝒪_{S, f y}` along the stalk map of `f`, has Tor amplitude in `[a, b]`. -/
public theorem hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (y : X) (a b : ℤ) :
    HasTorAmplitudeCanonical
        (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y
            ).mapDerivedCategory.obj ((derivedScalarRestriction f).obj E)) a b ↔
      HasTorAmplitudeCanonicalLift.{u, u, u}
        ((ModuleCat.restrictScalars.{u} (f.stalkMap y).hom).mapDerivedCategory.obj
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X y).mapDerivedCategory.obj E)) a b := by
  let eX := SemilinearStalk.commStalkRingEquiv X.presheaf y
  let ψ := SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = eX.toRingHom.comp ψ.hom := ⟨_, rfl⟩
  have iso1 : scalarRestriction f ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) y ⋙
        ModuleCat.restrictScalars.{u} ψ.hom :=
    AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso
      (inverseImageRingToStructure f) y
  have iso2 : AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X y ⋙
        ModuleCat.restrictScalars.{u} eX.toRingHom :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ ((ModuleCat.restrictScalarsId'.{u} (RingHom.id _) rfl).symm ≪≫
        ModuleCat.restrictScalarsComp'.{u} eX.toRingHom eX.symm.toRingHom (RingHom.id _)
          (RingHom.ext fun r => (eX.symm_apply_apply r).symm)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (AffineRelativeTorAmplitude.modulesStalkRestrictScalarsFunctorIso X y) _
  have iso3 : ModuleCat.restrictScalars.{u} eX.toRingHom ⋙ ModuleCat.restrictScalars.{u} ψ.hom ≅
      ModuleCat.restrictScalars.{u} τ :=
    (ModuleCat.restrictScalarsComp'.{u} ψ.hom eX.toRingHom τ hτ).symm
  have iso : scalarRestriction f ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X y ⋙ ModuleCat.restrictScalars.{u} τ :=
    iso1 ≪≫ Functor.isoWhiskerRight iso2 _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ iso3
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have eC : ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((scalarRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars.{u} τ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor X y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents (fun i => iso.app (K.X i))
      (fun i j _ => (iso.hom.naturality (K.d i j)).symm)
  have eA : (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y
          ).mapDerivedCategory.obj ((derivedScalarRestriction f).obj E) ≅
      (ModuleCat.restrictScalars.{u} τ).mapDerivedCategory.obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X y).mapDerivedCategory.obj E) :=
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y
          ).mapDerivedCategory.mapIso
        ((scalarRestriction f).mapDerivedCategory.mapIso eK.symm ≪≫
          (scalarRestriction f).mapDerivedCategoryFactors.app K) ≪≫
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y
          ).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso eC ≪≫
      ((ModuleCat.restrictScalars.{u} τ).mapDerivedCategoryFactors.app _).symm ≪≫
      (ModuleCat.restrictScalars.{u} τ).mapDerivedCategory.mapIso
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor X y).mapDerivedCategoryFactors.app K).symm ≪≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X y).mapDerivedCategory.mapIso eK)
  refine (hasTorAmplitudeCanonical_iff_of_iso eA a b).trans ?_
  refine Iff.trans (hasTorAmplitudeCanonical_restrictScalars_comp_ringEquiv_iff
    (f.stalkMap y).hom τ _
    (hτ.trans (commStalkRingEquiv_comp_ringStalkMap_inverseImageRingToStructure f y)) _ a b) ?_
  exact hasTorAmplitudeCanonical_iff_lift _ _ a b

/-- **The ringed-space reading of finite Tor dimension on an open, at the points of the open.**
For an open `U` of `X`, the restriction of `E` to `U`, read over `f⁻¹𝒪_S`, has finite Tor
dimension at the canonical derived tensor product of Stacks 06YU exactly when there is one
interval `[a, b]` such that at every point `y` of `U` the stalk of `E`, read over `𝒪_{S, f y}`,
has Tor amplitude in `[a, b]`. -/
public theorem chartHasFiniteTorDimension_canonical_iff
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (U : X.Opens) :
    ChartHasFiniteTorDimension f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) E U ↔
      ∃ a b : ℤ, ∀ y : X, y ∈ U → HasTorAmplitudeCanonicalLift.{u, u, u}
        ((ModuleCat.restrictScalars.{u} (f.stalkMap y).hom).mapDerivedCategory.obj
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X y).mapDerivedCategory.obj E)) a b :=
  exists_congr fun a => exists_congr fun b =>
    (Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk
      (RingedSpace.inverseImage S.toRingedSpace f.base) U
      ((derivedScalarRestriction f).obj E) a b).trans
      (forall_congr' fun y => forall_congr' fun _ =>
        hasTorAmplitudeCanonical_stalk_derivedScalarRestriction_iff f E y a b)

/-! ### The stalkwise reading under restriction to an open -/

/-- **Tor amplitude over the base is unchanged by composing the base morphism with an open
immersion.** The representing complex is the same on both sides; the rings over which its stalk
complexes are read change by the germ isomorphisms of the open immersion. -/
public theorem hasTorAmplitudeOver_comp_iff_of_isOpenImmersion {Y Z : Scheme.{u}}
    (g : X ⟶ Y) (d : Y ⟶ Z) [IsOpenImmersion d] (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver (g ≫ d) E a b ↔ HasTorAmplitudeOver g E a b := by
  have key : ∀ (K : CochainComplex X.Modules ℤ) (x : X),
      HasTorAmplitudeCanonicalLift.{u, u, u}
          (DerivedCategory.Q.obj (relativeStalkComplex (g ≫ d) K x)) a b ↔
        HasTorAmplitudeCanonicalLift.{u, u, u}
          (DerivedCategory.Q.obj (relativeStalkComplex g K x)) a b := fun K x =>
    hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff (g.stalkMap x).hom
      (d.stalkMap (g.base x)).hom ((g ≫ d).stalkMap x).hom
      (asIso (d.stalkMap (g.base x))).commRingCatIsoToRingEquiv rfl
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp g d x) _ a b
  exact ⟨fun ⟨K, hK, h⟩ => ⟨K, hK, fun x => (key K x).1 (h x)⟩,
    fun ⟨K, hK, h⟩ => ⟨K, hK, fun x => (key K x).2 (h x)⟩⟩

/-- **The stalkwise reading at a point of an open subscheme.** For an open immersion
`j : V ⟶ X` and a point `y` of `V`, the stalk at `y` of the restriction of `E` along `j`, read
over the base along the stalk map of `j ≫ f`, has Tor amplitude in `[a, b]` exactly when the
stalk of `E` at `j y`, read along the stalk map of `f`, does. -/
public theorem relativeStalkHasTorAmplitude_restrictFunctor_iff {V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (E : DerivedCategory X.Modules) (a b : ℤ) (y : V) :
    HasTorAmplitudeCanonicalLift.{u, u, u}
        ((ModuleCat.restrictScalars.{u} ((j ≫ f).stalkMap y).hom).mapDerivedCategory.obj
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor V y).mapDerivedCategory.obj
            ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E))) a b ↔
      HasTorAmplitudeCanonicalLift.{u, u, u}
        ((ModuleCat.restrictScalars.{u} (f.stalkMap (j.base y)).hom).mapDerivedCategory.obj
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (j.base y)).mapDerivedCategory.obj
            E)) a b := by
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let L := ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have eL : (ModuleCat.restrictScalars.{u} ((j ≫ f).stalkMap y).hom).mapDerivedCategory.obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor V y).mapDerivedCategory.obj
          ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E)) ≅
      DerivedCategory.Q.obj (relativeStalkComplex (j ≫ f) L y) :=
    (ModuleCat.restrictScalars.{u} ((j ≫ f).stalkMap y).hom).mapDerivedCategory.mapIso
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor V y).mapDerivedCategory.mapIso
        ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso eK.symm ≪≫
          (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app K ≪≫
          DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
            (Scheme.Modules.restrictFunctorIsoPullback j) (ComplexShape.up ℤ)).app K))) ≪≫
      (relativeStalkComplexDerivedIso (j ≫ f) L y).symm
  have eM : relativeStalkComplex (j ≫ f) L y ≅
      ((ModuleCat.restrictScalars.{u} ((j ≫ f).stalkMap y).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (j.stalkMap y).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (j.base y)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) :=
    ((ModuleCat.restrictScalars.{u} ((j ≫ f).stalkMap y).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (pullbackRelativeStalkObjIso j y K)
  have eR : DerivedCategory.Q.obj (relativeStalkComplex f K (j.base y)) ≅
      (ModuleCat.restrictScalars.{u} (f.stalkMap (j.base y)).hom).mapDerivedCategory.obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (j.base y)).mapDerivedCategory.obj E) :=
    relativeStalkComplexDerivedIso f K (j.base y) ≪≫
      (ModuleCat.restrictScalars.{u} (f.stalkMap (j.base y)).hom).mapDerivedCategory.mapIso
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (j.base y)).mapDerivedCategory.mapIso eK)
  refine (hasTorAmplitudeCanonicalLift_iff_of_iso (eL ≪≫ DerivedCategory.Q.mapIso eM) a b).trans ?_
  refine Iff.trans (hasTorAmplitudeCanonicalLift_restrictScalars_extendScalars_iff
    (f.stalkMap (j.base y)).hom (j.stalkMap y).hom ((j ≫ f).stalkMap y).hom
    (stalkRingEquivOfIsOpenImmersion j y) rfl (Stacks.ModuleSkyscraper.stalkMap_hom_comp j f y)
    _ a b) ?_
  exact hasTorAmplitudeCanonicalLift_iff_of_iso eR a b

/-- **The stalkwise reading of finite Tor dimension on a chart, at the points of the chart.**
For opens `V ⊆ S` and `U ⊆ f⁻¹(V)`, the restriction of `E` to `U` has finite Tor dimension over
`f.resLE V U e` exactly when there is one interval `[a, b]` such that at every point `y` of `U`
the stalk of `E`, read over `𝒪_{S, f y}`, has Tor amplitude in `[a, b]`. -/
public theorem exists_hasTorAmplitudeOver_resLE_iff (E : DerivedCategory X.Modules)
    {V : S.Opens} {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    (∃ a b : ℤ, HasTorAmplitudeOver (f.resLE V U e)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) a b) ↔
      ∃ a b : ℤ, ∀ y : X, y ∈ U → HasTorAmplitudeCanonicalLift.{u, u, u}
        ((ModuleCat.restrictScalars.{u} (f.stalkMap y).hom).mapDerivedCategory.obj
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X y).mapDerivedCategory.obj E)) a b := by
  refine exists_congr fun a => exists_congr fun b => ?_
  rw [← hasTorAmplitudeOver_comp_iff_of_isOpenImmersion (f.resLE V U e) V.ι,
    Scheme.Hom.resLE_comp_ι, hasTorAmplitudeOver_iff_forall_stalk]
  exact ⟨fun h y hy => (relativeStalkHasTorAmplitude_restrictFunctor_iff f U.ι E a b
      ⟨y, hy⟩).1 (h ⟨y, hy⟩),
    fun h y => (relativeStalkHasTorAmplitude_restrictFunctor_iff f U.ι E a b y).2
      (h y.1 y.2)⟩

/-- **The two sheaf-side readings of finite Tor dimension over the base agree on every chart.**
This is `AlgebraicGeometry.Scheme.Hom.ChartTorSpellingsAgree`: on an open `U ⊆ f⁻¹(V)`, finite Tor
dimension of `E|_U` on the ringed space `(X, f⁻¹𝒪_S)|_U` at the derived tensor product of
Stacks 06YU is finite Tor dimension of `E|_U` over `f.resLE V U e` in the stalkwise sense. Both are
the existence of one interval bounding the Tor amplitude of the stalks of `E` over the local
rings of `S` at the points of `U`. -/
public theorem chartTorSpellingsAgree (E : DerivedCategory X.Modules) (V : S.Opens)
    (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) : ChartTorSpellingsAgree f E V U e :=
  (chartHasFiniteTorDimension_canonical_iff f E U).trans
    (exists_hasTorAmplitudeOver_resLE_iff f E e).symm

end AlgebraicGeometry.Scheme.Hom

end
