module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BoundedBelowComparisonEquivalence
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedModulesEquivalence

/-!
# `RΓ_T` is the right adjoint to the inclusion of `D_T(A)`, bounded-below and unbounded

Let `A` be a Noetherian ring and `T ⊆ Spec(A)` a subset stable under specialization. This file
assembles the comparisons built elsewhere to show that `RΓ_T` — degree-zero sections with
support in `T`, derived, composed with the canonical comparison into the subcategory of objects
with cohomology supported in `T` — is the right adjoint to the inclusion of that subcategory:

* always, on the bounded-below derived category `D^+(A)` (Tag 0EF2's comparison is an
  equivalence unconditionally on a Noetherian ring and specialization-stable `T`);
* when `A` has finite Krull dimension, on the unbounded derived category `D(A)` (Tag 0EF3's
  comparison needs that hypothesis).

Both adjunctions are obtained from the same recipe: the underived adjunction
`inclusion_adj_supportedSectionsFunctor`, transported along the (bounded-below or unbounded)
right derived functor, then transported again along the comparison equivalence with the
ambient subcategory using `Adjunction.ofNatIsoLeft` and `Adjunction.comp`.

The bounded-below case needs an extra step the unbounded case does not: the comparison of
Tag 0EF2 lands in a subcategory of the *unbounded* derived category (cut out by boundedness
below and support), not in Mathlib's `DerivedCategory.Plus`. The functor
`plusToUnboundedComparison` below identifies the two, exactly as in the auxiliary situation of
Tag 0EF4's companion statements.

## Main results

* `Stacks.LocalCohomology.inclusion_adj_derivedSupportedSectionsPlus` — Tag 0EF4,
  `bounded_adjunction`.
* `Stacks.LocalCohomology.inclusion_adj_derivedSupportedSectionsComparison` — Tag 0EF4,
  `unbounded_adjunction`.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-! ## The unbounded adjunction -/

/-- If `e.functor ⋙ F ≅ G` for an equivalence `e`, then `G ⊣ R` gives `F ⊣ R ⋙ e.functor`. -/
private theorem adjunction_of_iso_comp_equivalence {C D E : Type*} [Category C] [Category D]
    [Category E] (e : C ≌ D) {F : D ⥤ E} {G : C ⥤ E} {R : E ⥤ C} (ψ : e.functor ⋙ F ≅ G)
    (adj : G ⊣ R) : Nonempty (F ⊣ R ⋙ e.functor) :=
  ⟨Adjunction.ofNatIsoLeft (Adjunction.comp e.symm.toAdjunction adj)
    ((Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm F ≪≫
      Functor.associator e.inverse e.functor F ≪≫ Functor.isoWhiskerLeft e.inverse ψ).symm⟩

/-- **Stacks Project, Tag 0EF4, unbounded adjunction.** Let `A` be a Noetherian ring of finite
Krull dimension and `T ⊆ Spec(A)` stable under specialization. The composite of `RH⁰_T` with the
comparison into `D_T(A)` is right adjoint to the inclusion `D_T(A) ⥤ D(A)`. -/
@[stacks 0EF4 "unbounded_adjunction"]
theorem inclusion_adj_derivedSupportedSectionsComparison [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) :
    Nonempty
      ((DerivedCategoryB.derivedCategoryB
          (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι ⊣
        (derivedSupportedSections.{u, v} A T ⋙
          supportedModulesComparison.{u, max u v} A T)) := by
  obtain ⟨adjU⟩ := derivedInclusion_adj_derivedSupportedSections.{u, v} A T hT
  have := supportedModulesComparison_isEquivalence.{u, max u v} A T hT hdim
  exact adjunction_of_iso_comp_equivalence
    (supportedModulesComparison.{u, max u v} A T).asEquivalence (Iso.refl _) adjU

/-! ## The bounded-below adjunction -/

/-- The subcategory of Mathlib's bounded-below derived category `D^+(A)` consisting of objects
whose cohomology is supported in `T`, matching the objects of `D_T(A)` that happen to be
bounded below. -/
abbrev supportedPlusProperty :
    ObjectProperty (DerivedCategory.Plus (ModuleCat.{max u v} A)) :=
  fun K => DerivedCategoryB.derivedCategoryB
    (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) K.obj

/-- The comparison from `supportedPlusProperty`, a subcategory of Mathlib's `D^+(A)`, to
`DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty A T)`, the corresponding
subcategory of the unbounded `D(A)`: a bounded-below object of `D^+(A)` is bounded below in
`D(A)` with the same bound. -/
def plusToUnboundedComparison :
    (supportedPlusProperty.{u, v} A T).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBPlus
        (supportModuleProperty.{u, max u v} A T)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty A T)).lift
    ((supportedPlusProperty A T).ι ⋙ DerivedCategory.Plus.ι) (fun X => by
      obtain ⟨n, hn⟩ := X.obj.property
      exact ⟨⟨n, fun i hi => (DerivedCategory.isGE_iff X.obj.obj n).mp hn i hi⟩, X.property⟩)

/-- `plusToUnboundedComparison` hits every object: a bounded-below object of `D(A)` with
cohomology supported in `T` comes from the bounded-below complex witnessing that bound, viewed
in `D^+(A)`. -/
private instance plusToUnboundedComparison_essSurj :
    (plusToUnboundedComparison.{u, v} A T).EssSurj := by
  refine ⟨fun X => ?_⟩
  obtain ⟨n, hn⟩ := X.property.1
  have hGE : X.obj.IsGE n := (DerivedCategory.isGE_iff X.obj n).2 hn
  let Y : DerivedCategory.Plus (ModuleCat.{max u v} A) := ⟨X.obj, ⟨n, hGE⟩⟩
  exact ⟨⟨Y, X.property.2⟩, ⟨(DerivedCategoryB.derivedCategoryBPlus
    (supportModuleProperty A T)).isoMk (Iso.refl X.obj)⟩⟩

private instance plusToUnboundedComparison_faithful :
    (plusToUnboundedComparison.{u, v} A T).Faithful := by
  unfold plusToUnboundedComparison; infer_instance

private instance plusToUnboundedComparison_full :
    (plusToUnboundedComparison.{u, v} A T).Full := by
  unfold plusToUnboundedComparison; infer_instance

/-- `plusToUnboundedComparison` is an equivalence of categories. -/
instance plusToUnboundedComparison_isEquivalence :
    (plusToUnboundedComparison.{u, v} A T).IsEquivalence := { }

/-- `plusToUnboundedComparison` composed with the inclusion of the unbounded subcategory is,
on the nose, the inclusion of `supportedPlusProperty` followed by `DerivedCategory.Plus.ι`: both
are lifts of the same functor. -/
private def plusToUnboundedComparisonCompIso :
    plusToUnboundedComparison.{u, v} A T ⋙
        (DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty.{u, max u v} A T)).ι ≅
      (supportedPlusProperty A T).ι ⋙ DerivedCategory.Plus.ι :=
  (DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty A T)).liftCompιIso _ _

/-- The canonical equivalence of Tag 0EF2, between `D^+(Mod_{A,T})` and the subcategory of the
unbounded `D(A)` cut out by `derivedCategoryBPlus`. -/
def equivPlus [IsNoetherianRing A] (hT : StableUnderSpecialization T) :
    DerivedCategory.Plus (ModulesSupportedIn.{u, max u v} A T) ≌
      (DerivedCategoryB.derivedCategoryBPlus
        (supportModuleProperty.{u, max u v} A T)).FullSubcategory :=
  (Module.exists_supportedModulesDerivedPlusEquivalence.{u, max u v} A T hT).choose

private theorem equivPlus_iso [IsNoetherianRing A] (hT : StableUnderSpecialization T) :
    Nonempty ((equivPlus A T hT).functor ⋙
      (DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty.{u, max u v} A T)).ι ≅
      DerivedCategory.Plus.ι ⋙ (supportModuleProperty A T).ι.mapDerivedCategory) :=
  (Module.exists_supportedModulesDerivedPlusEquivalence.{u, max u v} A T hT).choose_spec

/-- The comparison from `D^+(Mod_{A,T})` to `supportedPlusProperty`, the subcategory of
Mathlib's `D^+(A)` consisting of objects with cohomology supported in `T`: the composite of the
Tag 0EF2 equivalence with the inverse of `plusToUnboundedComparison`. -/
def comparisonPlus [IsNoetherianRing A] (hT : StableUnderSpecialization T) :
    DerivedCategory.Plus (ModulesSupportedIn.{u, max u v} A T) ⥤
      (supportedPlusProperty.{u, v} A T).FullSubcategory :=
  (equivPlus A T hT).functor ⋙ (plusToUnboundedComparison.{u, v} A T).inv

private instance comparisonPlus_isEquivalence [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) :
    (comparisonPlus A T hT).IsEquivalence := by
  unfold comparisonPlus
  infer_instance

/-- `comparisonPlus` composed with the inclusion of `supportedPlusProperty` into `D^+(A)` is
isomorphic to the bounded-below action on derived categories of the inclusion of the Serre
subcategory `Mod_{A,T} ⥤ Mod_A`. -/
theorem comparisonPlus_comp_ι_iso [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) :
    Nonempty (comparisonPlus.{u, v} A T hT ⋙ (supportedPlusProperty A T).ι ≅
      (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategoryPlus) := by
  obtain ⟨he2⟩ := equivPlus_iso.{u, v} A T hT
  let Q := supportedPlusProperty.{u, v} A T
  let P := DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty.{u, max u v} A T)
  let J := plusToUnboundedComparison.{u, v} A T
  let E := J.asEquivalence
  let L := (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).ι
  have hJcomp : J.inv ⋙ (Q.ι ⋙ DerivedCategory.Plus.ι) ≅ P.ι :=
    Functor.isoWhiskerLeft J.inv (plusToUnboundedComparisonCompIso.{u, v} A T).symm ≪≫
    (Functor.associator J.inv J P.ι).symm ≪≫
    Functor.isoWhiskerRight E.counitIso P.ι ≪≫
    Functor.leftUnitor P.ι
  have hinc : (equivPlus.{u, v} A T hT).functor ⋙ (J.inv ⋙ (Q.ι ⋙ DerivedCategory.Plus.ι)) ≅
      (equivPlus.{u, v} A T hT).functor ⋙ P.ι :=
    Functor.isoWhiskerLeft (equivPlus.{u, v} A T hT).functor hJcomp
  have composite_iso : (comparisonPlus.{u, v} A T hT ⋙ Q.ι) ⋙ DerivedCategory.Plus.ι ≅
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι := by
    refine Functor.associator (comparisonPlus.{u, v} A T hT) Q.ι DerivedCategory.Plus.ι ≪≫ ?_
    refine Functor.associator (equivPlus.{u, v} A T hT).functor J.inv
      (Q.ι ⋙ DerivedCategory.Plus.ι) ≪≫ ?_
    exact hinc ≪≫ he2 ≪≫ (Iso.refl (L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι)).symm
  exact ⟨Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι composite_iso⟩

/-- **Stacks Project, Tag 0EF4, bounded adjunction.** Let `A` be a Noetherian ring and
`T ⊆ Spec(A)` stable under specialization. The composite of the bounded-below derived functor of
sections with support in `T` with the comparison into `supportedPlusProperty` is right adjoint
to the inclusion of that subcategory into `D^+(A)`. -/
@[stacks 0EF4 "bounded_adjunction"]
theorem inclusion_adj_derivedSupportedSectionsPlus [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) :
    Nonempty
      ((supportedPlusProperty.{u, v} A T).ι ⊣
        ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
          comparisonPlus.{u, v} A T hT)) := by
  obtain ⟨ψ⟩ := comparisonPlus_comp_ι_iso.{u, v} A T hT
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  have : (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι.Additive :=
    (inclusion_adj_supportedSectionsFunctor.{u, v} A T).left_adjoint_additive
  let adjPlus := Stacks.ComparingTopologies.derivedPlusAdjunction
    (inclusion_adj_supportedSectionsFunctor.{u, v} A T)
  exact adjunction_of_iso_comp_equivalence (comparisonPlus.{u, v} A T hT).asEquivalence ψ adjPlus

end Stacks.LocalCohomology
