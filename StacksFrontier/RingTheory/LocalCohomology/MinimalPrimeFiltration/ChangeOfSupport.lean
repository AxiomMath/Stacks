module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.ClosedSupportColimit

/-!
# Changing the support of local cohomology

An inclusion `S ⊆ T` of subsets of the spectrum of a commutative ring `A` induces a map
`H^i_S(K) ⟶ H^i_T(K)` on local cohomology, functorially in the derived object `K`. This file
collects the elementary properties of these maps: they are compatible with the identity and with
composition, and they are compatible with the augmentations to the identity functor. It also
records that local cohomology with support in `T` dies after localizing at a prime outside `T`.

## Main definitions

* `Stacks.LocalCohomology.changeOfSupport` — the map on local cohomology induced by an inclusion
  of supports.
* `Stacks.LocalCohomology.changeOfSupportIsoOfEq` — the isomorphism between the local cohomology
  of two supports with the same underlying set.

## Main results

* `Stacks.LocalCohomology.changeOfSupport_refl`,
  `Stacks.LocalCohomology.changeOfSupport_trans` and
  `Stacks.LocalCohomology.changeOfSupport_trans_apply` — functoriality in the support.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInInclusion_comp_augmentation` — widening the
  support is compatible with the augmentation `RΓ_T ⟶ id`.
* `Stacks.LocalCohomology.localCohomology_localizes_zero_outside_support` — every element of
  `H^i_T(K)` localizes to zero at a prime not in `T`.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- The canonical map on local cohomology induced by an inclusion of supports. -/
def changeOfSupport (A : Type u) [CommRing A] {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    localCohomologyWithSupportIn A S K i ⟶ localCohomologyWithSupportIn A T K i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
    ((derivedSectionsWithSupportInInclusion A h).app K)

/-- The map induced by `S ⊆ S` is the identity. -/
@[simp]
theorem changeOfSupport_refl (A : Type u) [CommRing A] {S : Set (PrimeSpectrum A)} (h : S ⊆ S)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    changeOfSupport A h K i = 𝟙 _ := by
  simp [changeOfSupport]

/-- The maps induced by inclusions of supports compose. -/
@[simp, reassoc]
theorem changeOfSupport_trans (A : Type u) [CommRing A] {R S T : Set (PrimeSpectrum A)}
    (hRS : R ⊆ S) (hST : S ⊆ T) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    changeOfSupport A hRS K i ≫ changeOfSupport A hST K i =
      changeOfSupport A (hRS.trans hST) K i := by
  unfold changeOfSupport
  rw [← Functor.map_comp, ← NatTrans.comp_app, derivedSectionsWithSupportInInclusion_trans]

/-- On the homotopy category, widening the support commutes with the degreewise inclusion of
supported sections into the ambient complex. -/
theorem mapHomotopyCategory_sectionsWithSupportInInclusion_comp_subtype (A : Type u) [CommRing A]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    NatTrans.mapHomotopyCategory (sectionsWithSupportInInclusion.{u, v} A h)
          (ComplexShape.up ℤ) ≫ homotopySectionsWithSupportInSubtype.{u, v} A T =
      homotopySectionsWithSupportInSubtype.{u, v} A S := by
  have hcx : ∀ L : HomologicalComplex (ModuleCat.{max u v} A) (ComplexShape.up ℤ),
      (NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
            (ComplexShape.up ℤ)).app L ≫
          ((NatTrans.mapHomologicalComplex (sectionsWithSupportInSubtype.{u, v} A T)
              (ComplexShape.up ℤ)).app L ≫
            (mapHomologicalComplexIdIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).hom.app L) =
        (NatTrans.mapHomologicalComplex (sectionsWithSupportInSubtype.{u, v} A S)
            (ComplexShape.up ℤ)).app L ≫
          (mapHomologicalComplexIdIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).hom.app L := by
    intro L
    ext n x
    exact congrArg (fun φ => (ModuleCat.Hom.hom φ) x)
      (sectionsWithSupportInInclusion_comp_subtype_app.{u, v} h (L.X n))
  refine NatTrans.ext (funext fun X => ?_)
  change (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map _ =
    (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map _
  rw [← Functor.map_comp]
  exact congrArg _ (hcx X.as)

/-- Widening the support is compatible with the augmentations `RΓ_S ⟶ id` and `RΓ_T ⟶ id`. -/
theorem derivedSectionsWithSupportInInclusion_comp_augmentation (A : Type u) [CommRing A]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    derivedSectionsWithSupportInInclusion.{u, v} A h ≫
        derivedSectionsWithSupportInAugmentation.{u, v} A T =
      derivedSectionsWithSupportInAugmentation.{u, v} A S := by
  refine Functor.rightDerived_ext _ (derivedSectionsWithSupportInUnit.{u, v} A S)
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _ _ _ ?_
  rw [whiskerLeft_comp, ← Category.assoc, derivedSectionsWithSupportInInclusion_fac,
    Category.assoc, derivedSectionsWithSupportInUnit_comp_augmentation,
    derivedSectionsWithSupportInUnit_comp_augmentation, ← whiskerRight_comp,
    mapHomotopyCategory_sectionsWithSupportInInclusion_comp_subtype]

/-- The maps induced by inclusions of supports compose, read on an element. -/
theorem changeOfSupport_trans_apply (A : Type u) [CommRing A] {R S T : Set (PrimeSpectrum A)}
    (hRS : R ⊆ S) (hST : S ⊆ T) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn A R K i) :
    (changeOfSupport A hST K i).hom ((changeOfSupport A hRS K i).hom x) =
      (changeOfSupport A (hRS.trans hST) K i).hom x :=
  congrArg (fun φ => ModuleCat.Hom.hom φ x) (changeOfSupport_trans A hRS hST K i)

/-- Two supports with the same underlying set have the same local cohomology, by the two
inclusions between them. -/
def changeOfSupportIsoOfEq (A : Type u) [CommRing A] {S T : Set (PrimeSpectrum A)} (h : S = T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    localCohomologyWithSupportIn A S K i ≅ localCohomologyWithSupportIn A T K i where
  hom := changeOfSupport A h.subset K i
  inv := changeOfSupport A h.ge K i
  hom_inv_id := by rw [changeOfSupport_trans, changeOfSupport_refl]
  inv_hom_id := by rw [changeOfSupport_trans, changeOfSupport_refl]

/-- The forward map of `changeOfSupportIsoOfEq` is `changeOfSupport` along `S ⊆ T`. -/
@[simp]
theorem changeOfSupportIsoOfEq_hom (A : Type u) [CommRing A] {S T : Set (PrimeSpectrum A)}
    (h : S = T) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    (changeOfSupportIsoOfEq.{u, v} A h K i).hom = changeOfSupport A h.subset K i := rfl

/-- The inverse map of `changeOfSupportIsoOfEq` is `changeOfSupport` along `T ⊆ S`. -/
@[simp]
theorem changeOfSupportIsoOfEq_inv (A : Type u) [CommRing A] {S T : Set (PrimeSpectrum A)}
    (h : S = T) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    (changeOfSupportIsoOfEq.{u, v} A h K i).inv = changeOfSupport A h.ge K i := rfl

/-- Localization of a module map commutes with the canonical map to the localized module. -/
theorem localizedModuleMk_natural {A : Type u} [CommRing A] {M N : ModuleCat.{max u v} A}
    (S : Submonoid A) (f : M ⟶ N) (x : M) :
    (ModuleCat.localizedModuleMkLinearMap N S) (f.hom x) =
      (ModuleCat.localizedModuleMap S f).hom
        ((ModuleCat.localizedModuleMkLinearMap M S) x) := by
  change (ModuleCat.localizedModuleMkLinearMap N S) (f.hom x) =
    (IsLocalizedModule.mapExtendScalars S (ModuleCat.localizedModuleMkLinearMap M S)
      (ModuleCat.localizedModuleMkLinearMap N S) (Localization S) f.hom)
      ((ModuleCat.localizedModuleMkLinearMap M S) x)
  rw [IsLocalizedModule.mapExtendScalars_apply_apply]
  exact (IsLocalizedModule.map_apply S (ModuleCat.localizedModuleMkLinearMap M S)
    (ModuleCat.localizedModuleMkLinearMap N S) f.hom x).symm

/-- Local cohomology with support in `T` vanishes after localizing at a prime outside `T`. -/
theorem localCohomology_localizes_zero_outside_support {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (p : PrimeSpectrum A) (hp : p ∉ T) (x : localCohomologyWithSupportIn A T K i) :
    (ModuleCat.localizedModuleMkLinearMap (localCohomologyWithSupportIn A T K i)
      p.asIdeal.primeCompl) x = 0 := by
  obtain ⟨r, hr, hrx⟩ := Module.notMem_support_iff'.mp
    (fun hx => hp (support_localCohomologyWithSupportIn_subset T K i hx)) x
  exact (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
    (ModuleCat.localizedModuleMkLinearMap _ p.asIdeal.primeCompl)).2 ⟨⟨r, hr⟩, hrx⟩

end Stacks.LocalCohomology

end
