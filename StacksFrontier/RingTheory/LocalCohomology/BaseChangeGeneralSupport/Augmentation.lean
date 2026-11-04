module

public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Local cohomology with general support and flat base change

Let `f : A →+* B` be a flat homomorphism of Noetherian rings, let `T ⊆ Spec A` be stable under
specialization and let `T' = (Spec f)⁻¹(T) ⊆ Spec B` be its preimage. Then local cohomology with
support in `T` commutes with derived extension of scalars along `f`:

`RΓ_T(K) ⊗ᴸ_A B = RΓ_{T'}(K ⊗ᴸ_A B)`

naturally in `K`, and compatibly with the augmentations to the identity functor. This is proved
here for bounded-below complexes and for arbitrary complexes.

The canonical comparison map is built by right deriving the degree-zero map
`Γ_T(M) ⊗_A B ⟶ Γ_{T'}(M ⊗_A B)`, which exists because the annihilator of `x` maps into the
annihilator of `b ⊗ x`, so a `T`-supported section stays `T'`-supported. Flatness of `f` makes
extension of scalars left exact, so that this degree-zero comparison can be right derived on the
whole unbounded derived category.

Invertibility is proved first for a closed support `T = V(I)`: there `RΓ_{V(I)}` is the local
cohomology functor of Tag 0955, whose base change along an arbitrary ring map is Tag 0ALZ, and
the augmentation `RΓ_{V(I)} ⟶ id` is the counit of the local cohomology adjunction, so both
sides of the comparison have the same universal property among objects with `I`-power-torsion
cohomology. The general case follows by the filtered colimit of Tag 0EF1: cohomology with
support in `T` is the colimit of cohomology with closed support `V(J) ⊆ T`, extension of scalars
is a left adjoint and so preserves that colimit, the index map `J ↦ JB` is final because `T` is
stable under specialization, and a map in `D(B)` that is invertible on every cohomology module
is invertible.

## Main definitions

* `Stacks.LocalCohomology.sectionsWithSupportInBaseChangeNatTrans` — the degree-zero
  change-of-rings map on supported sections.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInBaseChangeMap` — its right derived
  functor, the canonical base-change comparison on the unbounded derived category.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInAugmentation` and
  `Stacks.LocalCohomology.derivedSectionsWithSupportInPlusAugmentation` — the augmentations
  `RΓ_T ⟶ id` on the unbounded and bounded-below derived categories.
* `Stacks.LocalCohomology.closedSupportIdealMapFunctor` — extension of ideals, read as a map of
  closed-support index categories.

## Main results

* `Stacks.LocalCohomology.derivedSectionsWithSupportInPlusBaseChangeIso` — Tag 0EF5, the
  bounded-below case.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInBaseChangeIso` — Tag 0EF5, the unbounded
  case.
* `Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInBaseChangeMap_closed` — the closed
  support case, for an arbitrary object of the unbounded derived category.
* `Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInBaseChangeMap` — invertibility of
  the canonical comparison for every specialization-stable support.
* `Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology_comp_counit` — the
  augmentation `RΓ_{V(I)} ⟶ id` is the counit of the local cohomology adjunction.

## Implementation notes

Two models of derived sections with support occur. The constructions are carried out for the
degreewise extension of scalars read on derived categories, which for a flat map agrees with
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral` by
`Stacks.LocalCohomology.derivedExtensionScalarsIsoMapDerivedCategory`; the statements are then
transported to the latter, which is the functor the cited base-change results use.

The bounded-below statement is about the bounded-below derived functor
`derivedSectionsWithSupportInPlus`. The library records the comparison with the unbounded
functor only as a `Nonempty` statement, so the isomorphism itself is rebuilt here from the two
universal properties as `derivedSectionsWithSupportInPlusIso`, together with the fact that it
carries one augmentation to the other.

The two spellings `(Spec f)⁻¹(V(I))` and `V(IB)` of a pulled-back closed support are equal but
not identical, and `derivedSectionsWithSupportInInclusion_eqToHom` is the bookkeeping that this
equality entails when the colimit over closed supports on `Spec A` is compared with the one on
`Spec B`.

The hypotheses `ringKrullDim A < ⊤` and `ringKrullDim B < ⊤` of the unbounded case are kept as
the source states them, although the proof given here does not use them: the colimit of Tag
0EF1 is available on the whole unbounded derived category.

## References

* [Stacks Project, Tag 0EF5](https://stacks.math.columbia.edu/tag/0EF5)
* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0EF1](https://stacks.math.columbia.edu/tag/0EF1)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v uB w

namespace Stacks.LocalCohomology

/-- The inclusion of the `T`-supported sections of a module into the module. -/
def sectionsWithSupportInSubtype (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    sectionsWithSupportInFunctor.{u, v} A T ⟶ 𝟭 _ where
  app M := ModuleCat.ofHom (sectionsWithSupportIn A T M).subtype
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- The degreewise inclusion of the complex of `T`-supported sections, on the homotopy
category. -/
def homotopySectionsWithSupportInSubtype (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⟶ 𝟭 _ :=
  Quotient.natTransLift _
    (whiskerRight
      ((sectionsWithSupportInSubtype.{u, v} A T).mapHomologicalComplex (ComplexShape.up ℤ) ≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).hom)
      (HomotopyCategory.quotient _ _))

/-- The canonical augmentation `RΓ_T ⟶ id` on the unbounded derived category, the right derived
functor of the inclusion of `T`-supported sections. -/
def derivedSectionsWithSupportInAugmentation (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) : derivedSectionsWithSupportIn.{u, v} A T ⟶ 𝟭 _ :=
  (derivedSectionsWithSupportIn.{u, v} A T).rightDerivedDesc
    (derivedSectionsWithSupportInUnit.{u, v} A T)
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) (𝟭 _)
    (whiskerRight (homotopySectionsWithSupportInSubtype.{u, v} A T) DerivedCategory.Qh)

/-- The augmentation is the unique map whose composite with the canonical derived unit is the
degreewise inclusion of supported sections. -/
theorem derivedSectionsWithSupportInUnit_comp_augmentation (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    derivedSectionsWithSupportInUnit.{u, v} A T ≫
        whiskerLeft DerivedCategory.Qh (derivedSectionsWithSupportInAugmentation.{u, v} A T) =
      whiskerRight (homotopySectionsWithSupportInSubtype.{u, v} A T) DerivedCategory.Qh :=
  Functor.rightDerived_fac _ _
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _ _

/-- The augmentation is the unique map compatible with the canonical derived unit. -/
theorem derivedSectionsWithSupportInUnit_augmentation (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A))
    (X : HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) :
    (derivedSectionsWithSupportInUnit.{u, v} A T).app X ≫
        (derivedSectionsWithSupportInAugmentation.{u, v} A T).app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((homotopySectionsWithSupportInSubtype.{u, v} A T).app X) :=
  Functor.rightDerived_fac_app _ _ _ _ _ X

section Plus

universe w₂

variable (C : Type w) [CommRing C] (T : Set (PrimeSpectrum C))

/-- The degreewise inclusion of the complex of `T`-supported sections, on the bounded-below
homotopy category. -/
def homotopySectionsWithSupportInPlusSubtype :
    (sectionsWithSupportInFunctor.{w, w₂} C T).mapHomotopyCategoryPlus ⟶ 𝟭 _ where
  app K := ObjectProperty.homMk ((homotopySectionsWithSupportInSubtype.{w, w₂} C T).app K.obj)
  naturality K L φ := by
    ext
    exact (homotopySectionsWithSupportInSubtype.{w, w₂} C T).naturality φ.hom

/-- The canonical augmentation `RΓ_T ⟶ id` on the bounded-below derived category, the right
derived functor of the inclusion of `T`-supported sections. -/
def derivedSectionsWithSupportInPlusAugmentation :
    derivedSectionsWithSupportInPlus.{w, w₂} C T ⟶ 𝟭 _ :=
  letI : EnoughInjectives (ModuleCat.{max w w₂} C) := ModuleCat.enoughInjectives C
  (sectionsWithSupportInFunctor.{w, w₂} C T).rightDerivedFunctorPlus.rightDerivedDesc
    (sectionsWithSupportInFunctor.{w, w₂} C T).rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{max w w₂} C)) (𝟭 _)
    (whiskerRight (homotopySectionsWithSupportInPlusSubtype.{w, w₂} C T) DerivedCategory.Plus.Qh)

/-- Sections with support in `T`, applied to bounded-below complexes and landing in the
unbounded derived category: both derived functors restrict to right derived functors of it. -/
private abbrev plusSectionsWithSupportToUnbounded :
    HomotopyCategory.Plus (ModuleCat.{max w w₂} C) ⥤ DerivedCategory (ModuleCat.{max w w₂} C) :=
  (sectionsWithSupportInFunctor.{w, w₂} C T).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι

/-- The unit of the bounded-below derived functor, pushed into the unbounded derived category. -/
private def plusSectionsUnit : plusSectionsWithSupportToUnbounded.{w, w₂} C T ⟶
    DerivedCategory.Plus.Qh ⋙
      (derivedSectionsWithSupportInPlus.{w, w₂} C T ⋙ DerivedCategory.Plus.ι) :=
  letI : EnoughInjectives (ModuleCat.{max w w₂} C) := ModuleCat.enoughInjectives C
  whiskerRight (sectionsWithSupportInFunctor.{w, w₂} C T).rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι

/-- The unit of the unbounded derived functor, restricted to bounded-below objects. -/
private def unboundedSectionsUnit : plusSectionsWithSupportToUnbounded.{w, w₂} C T ⟶
    DerivedCategory.Plus.Qh ⋙
      (DerivedCategory.Plus.ι ⋙ derivedSectionsWithSupportIn.{w, w₂} C T) :=
  whiskerLeft (HomotopyCategory.Plus.ι (ModuleCat.{max w w₂} C))
    (derivedSectionsWithSupportInUnit.{w, w₂} C T)

/-- A bounded-below complex of injectives is K-injective, so it computes the unbounded derived
functor and the canonical unit is invertible there. -/
private theorem isIso_unboundedSectionsUnit_app_of_injective
    (X : HomotopyCategory.Plus (ModuleCat.{max w w₂} C)) [∀ n : ℤ, Injective (X.obj.as.X n)] :
    IsIso ((unboundedSectionsUnit.{w, w₂} C T).app X) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, CochainComplex.IsStrictlyGE X.obj.as n := by
    have hX := X.property
    rwa [show X.obj = (HomotopyCategory.quotient _ _).obj X.obj.as from rfl,
      HomotopyCategory.plus_quotient_obj_iff] at hX
  have hK : CochainComplex.IsKInjective X.obj.as := CochainComplex.isKInjective_of_injective _ n
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((sectionsWithSupportInFunctor.{w, w₂} C T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (fun L ↦ by
      obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective L
      exact ⟨I, q, hI, hq⟩)).2 DerivedCategory.Qh
      (derivedSectionsWithSupportIn.{w, w₂} C T) (derivedSectionsWithSupportInUnit.{w, w₂} C T)
      X.obj.as hK

private instance isRightDerivedFunctor_unboundedSectionsUnit :
    (DerivedCategory.Plus.ι ⋙ derivedSectionsWithSupportIn.{w, w₂} C T).IsRightDerivedFunctor
      (unboundedSectionsUnit.{w, w₂} C T)
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{max w w₂} C)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (plusSectionsWithSupportToUnbounded.{w, w₂} C T)).isRightDerivedFunctor_of_isIso _
    fun _ ↦ isIso_unboundedSectionsUnit_app_of_injective C T _

private instance isRightDerivedFunctor_plusSectionsUnit :
    (derivedSectionsWithSupportInPlus.{w, w₂} C T ⋙
        DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (plusSectionsUnit.{w, w₂} C T)
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{max w w₂} C)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (plusSectionsWithSupportToUnbounded.{w, w₂} C T)).isRightDerivedFunctor_of_isIso _
    fun _ ↦ by dsimp [plusSectionsUnit]; infer_instance

/-- **Stacks 0EF4, the cohomology calculation, as an isomorphism.** The bounded-below and the
unbounded right derived functors of sections with support in `T` agree on bounded-below
objects; the isomorphism is the one given by the two universal properties. -/
@[no_expose]
def derivedSectionsWithSupportInPlusIso :
    derivedSectionsWithSupportInPlus.{w, w₂} C T ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ derivedSectionsWithSupportIn.{w, w₂} C T :=
  Functor.rightDerivedUnique _ _ (plusSectionsUnit.{w, w₂} C T)
    (unboundedSectionsUnit.{w, w₂} C T) (HomotopyCategory.Plus.quasiIso (ModuleCat.{max w w₂} C))

/-- **The two augmentations agree.** The comparison of the bounded-below and unbounded derived
sections carries the bounded-below augmentation to the unbounded one. -/
theorem derivedSectionsWithSupportInPlusIso_augmentation :
    (derivedSectionsWithSupportInPlusIso.{w, w₂} C T).hom ≫
        whiskerLeft DerivedCategory.Plus.ι
          (derivedSectionsWithSupportInAugmentation.{w, w₂} C T) =
      whiskerRight (derivedSectionsWithSupportInPlusAugmentation.{w, w₂} C T)
        DerivedCategory.Plus.ι := by
  let : EnoughInjectives (ModuleCat.{max w w₂} C) := ModuleCat.enoughInjectives C
  refine Functor.rightDerived_ext _ (plusSectionsUnit.{w, w₂} C T)
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{max w w₂} C)) _ _ _ ?_
  ext X
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [show (derivedSectionsWithSupportInPlusIso.{w, w₂} C T).hom =
      Functor.rightDerivedNatTrans _ _ (plusSectionsUnit.{w, w₂} C T)
        (unboundedSectionsUnit.{w, w₂} C T)
        (HomotopyCategory.Plus.quasiIso (ModuleCat.{max w w₂} C)) (𝟙 _) from rfl,
    Functor.rightDerivedNatTrans_app_assoc, NatTrans.id_app, Category.id_comp]
  have hfac : (sectionsWithSupportInFunctor.{w, w₂} C T).rightDerivedFunctorPlusUnit.app X ≫
      (derivedSectionsWithSupportInPlusAugmentation.{w, w₂} C T).app
        (DerivedCategory.Plus.Qh.obj X) =
      (whiskerRight (homotopySectionsWithSupportInPlusSubtype.{w, w₂} C T)
        DerivedCategory.Plus.Qh).app X :=
    Functor.rightDerived_fac_app _ _
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{max w w₂} C)) _ _ X
  show (derivedSectionsWithSupportInUnit.{w, w₂} C T).app X.obj ≫
      (derivedSectionsWithSupportInAugmentation.{w, w₂} C T).app
        (DerivedCategory.Qh.obj X.obj) =
    DerivedCategory.Plus.ι.map
        ((sectionsWithSupportInFunctor.{w, w₂} C T).rightDerivedFunctorPlusUnit.app X) ≫
      DerivedCategory.Plus.ι.map
        ((derivedSectionsWithSupportInPlusAugmentation.{w, w₂} C T).app
          (DerivedCategory.Plus.Qh.obj X))
  rw [derivedSectionsWithSupportInUnit_augmentation.{w, w₂} C T X.obj, ← Functor.map_comp, hfac]
  rfl

end Plus

section ModelComparison

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

open Dualizing

/-- The unit of `RΓ_{V(I)}` composed with the comparison of the two derived torsion models is
the comparison of their units. -/
private lemma unit_comp_compareIso :
    letI P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    letI : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    derivedSectionsWithSupportInUnit.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) ≫
        whiskerLeft DerivedCategory.Qh
          (derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v} A I hI).hom =
      (Functor.isoWhiskerRight
          (Functor.mapHomotopyCategoryCompIso
            (sectionsWithSupportInFunctorIsoPowerTorsionFunctor.{u, v} A I hI)
            (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
        (Functor.isoWhiskerLeft
          ((Dualizing.powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (ComplexShape.up ℤ))
          (P.ι.mapDerivedCategoryFactorsh).symm).hom ≫
        Functor.whiskerRight (Dualizing.derivedPowerTorsionUnit.{u, v} A I hI)
          P.ι.mapDerivedCategory :=
  Functor.rightDerived_fac _ _
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _ _

/-- On complexes, the identification of the two torsion functors matches their inclusions into
the ambient complex. -/
private lemma compIso_inv_comp_powerTorsionHomotopyInclusion
    (K : HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso
          (sectionsWithSupportInFunctorIsoPowerTorsionFunctor.{u, v} A I hI)
          (ComplexShape.up ℤ)).inv.app K ≫
        (Dualizing.powerTorsionHomotopyInclusion.{u, v} A I).app K =
      (homotopySectionsWithSupportInSubtype.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).app K := by
  obtain ⟨L⟩ := K
  show (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map _ =
    (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map _
  rw [← Functor.map_comp]
  congr 1

/-- The comparison of the two derived torsion models carries the augmentation to the canonical
derived torsion counit. -/
private lemma compareIso_comp_derivedPowerTorsionCounit :
    letI P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    letI : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    (derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v} A I hI).hom ≫
        Dualizing.derivedPowerTorsionCounit.{u, v} A I hI =
      derivedSectionsWithSupportInAugmentation.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A)) := by
  refine Functor.rightDerived_ext _
    (derivedSectionsWithSupportInUnit.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)))
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _ _ _ ?_
  rw [whiskerLeft_comp, ← Category.assoc, unit_comp_compareIso A I hI,
    derivedSectionsWithSupportInUnit_comp_augmentation.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A))]
  ext K
  have hcanon := Dualizing.derivedPowerTorsionCounit_isCanonical.{u, v} A I hI K
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    whiskerRight_app, Category.assoc]
  rw [hcanon, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    compIso_inv_comp_powerTorsionHomotopyInclusion A I hI K]

/-- **The augmentation is the local cohomology counit.** The comparison of Tag 0955 from derived
sections with support in `V(I)` to local cohomology `RΓ_Z` carries the augmentation
`RΓ_{V(I)} ⟶ id` to the counit of the local cohomology adjunction. -/
theorem compareSectionsWithSupportLocalCohomology_comp_counit :
    compareSectionsWithSupportLocalCohomology.{u, v} A I hI ≫
        (Dualizing.localCohomologyAdjunction.{u, max u v} A I hI).counit =
      derivedSectionsWithSupportInAugmentation.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A)) := by
  have hnat : Functor.whiskerRight (Dualizing.compareTorsionFunctors.{u, v} A I hI)
          (Dualizing.derivedPowerTorsionProperty A I hI).ι ≫
        (Dualizing.localCohomologyAdjunction.{u, max u v} A I hI).counit =
      (Functor.isoWhiskerLeft (Dualizing.derivedPowerTorsion.{u, v} A I hI)
          (Dualizing.powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).hom ≫
        Dualizing.derivedPowerTorsionCounit.{u, v} A I hI :=
    NatTrans.ext (funext fun K ↦ Dualizing.compareTorsionFunctors_app_counit.{u, v} A I hI K)
  have hbc : ((Functor.isoWhiskerLeft (Dualizing.derivedPowerTorsion.{u, v} A I hI)
            (Dualizing.powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).inv ≫
          Functor.whiskerRight (Dualizing.compareTorsionFunctors.{u, v} A I hI)
            (Dualizing.derivedPowerTorsionProperty A I hI).ι) ≫
        (Dualizing.localCohomologyAdjunction.{u, max u v} A I hI).counit =
      Dualizing.derivedPowerTorsionCounit.{u, v} A I hI :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (Functor.isoWhiskerLeft (Dualizing.derivedPowerTorsion.{u, v} A I hI)
            (Dualizing.powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).inv ≫ k)
          hnat).trans (Iso.inv_hom_id_assoc _ _))
  refine Eq.trans ?_ (compareIso_comp_derivedPowerTorsionCounit A I hI)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k ↦ (derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v} A I hI).hom ≫ k)
      hbc)

end ModelComparison

section Universal

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **The augmentation is universal.** Over a Noetherian ring, a morphism to `K` from an object
with `I`-power-torsion cohomology factors uniquely through the augmentation
`RΓ_{V(I)}(K) ⟶ K`. -/
theorem bijective_comp_derivedSectionsWithSupportInAugmentation
    (X W : DerivedCategory (ModuleCat.{max u v} A))
    (hW : Dualizing.derivedPowerTorsionProperty A I (Ideal.fg_of_isNoetherianRing I) W) :
    Function.Bijective (fun g : W ⟶ (derivedSectionsWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).obj X ↦
      g ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).app X) := by
  have hfg := Ideal.fg_of_isNoetherianRing (R := A) I
  have := isIso_compareSectionsWithSupportLocalCohomology_app.{u, v} A I hfg X
  have h1 : Function.Bijective
      (fun g : W ⟶ (derivedSectionsWithSupportIn.{u, v} A
          (PrimeSpectrum.zeroLocus (I : Set A))).obj X ↦
        g ≫ (compareSectionsWithSupportLocalCohomology.{u, v} A I hfg).app X) := by
    refine ⟨fun a b h ↦ (cancel_mono _).1 h, fun h ↦
      ⟨h ≫ CategoryTheory.inv ((compareSectionsWithSupportLocalCohomology.{u, v}
        A I hfg).app X), ?_⟩⟩
    show (h ≫ CategoryTheory.inv _) ≫ _ = h
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have h2 := counit_bijective (Dualizing.derivedPowerTorsionProperty A I hfg)
    (Dualizing.localCohomologyAdjunction.{u, max u v} A I hfg) X ⟨W, hW⟩
  have heq : (compareSectionsWithSupportLocalCohomology.{u, v} A I hfg).app X ≫
      (Dualizing.localCohomologyAdjunction.{u, max u v} A I hfg).counit.app X =
      (derivedSectionsWithSupportInAugmentation.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).app X :=
    congrArg (fun α ↦ NatTrans.app α X)
      (compareSectionsWithSupportLocalCohomology_comp_counit.{u, v} A I hfg)
  have hfun : (fun g : W ⟶ (derivedSectionsWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).obj X ↦
      g ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).app X) =
      (fun h ↦ h ≫ (Dualizing.localCohomologyAdjunction.{u, max u v} A I hfg).counit.app X) ∘
        (fun g ↦ g ≫ (compareSectionsWithSupportLocalCohomology.{u, v} A I hfg).app X) := by
    funext g
    simp only [Function.comp_apply]
    exact (congrArg (fun k ↦ g ≫ k) heq).symm.trans (Category.assoc _ _ _).symm
  rw [hfun]
  exact h2.comp h1

end Universal

section AbstractUniversal

variable {C : Type*} [Category C]

/-- A map between two objects universal among maps to `X`, compatible with the two universal
maps, is invertible. -/
lemma isIso_of_universal {X Y Y' : C} (c : Y ⟶ X) (c' : Y' ⟶ X) (m : Y ⟶ Y')
    (hm : m ≫ c' = c)
    (hc : Function.Bijective (fun g : Y' ⟶ Y ↦ g ≫ c))
    (hcY : Function.Injective (fun g : Y ⟶ Y ↦ g ≫ c))
    (hc'Y' : Function.Injective (fun g : Y' ⟶ Y' ↦ g ≫ c')) : IsIso m := by
  obtain ⟨n, hn⟩ := hc.2 c'
  change n ≫ c = c' at hn
  refine ⟨n, ?_, ?_⟩
  · refine hcY ?_
    show (m ≫ n) ≫ c = (𝟙 Y) ≫ c
    rw [Category.assoc, hn, hm, Category.id_comp]
  · refine hc'Y' ?_
    show (n ≫ m) ≫ c' = (𝟙 Y') ≫ c'
    rw [Category.assoc, hm, hn, Category.id_comp]

end AbstractUniversal

end Stacks.LocalCohomology

end
