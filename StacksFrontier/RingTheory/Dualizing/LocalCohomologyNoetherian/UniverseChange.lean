module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.DerivedTorsion
public import StacksFrontier.RingTheory.LocalCohomology.TorsionColimit

/-!
# Comparing the two models of local cohomology, and changing the module universe

Over a Noetherian ring `A` with an ideal `I`, this library computes local cohomology supported
on `V(I)` in two ways: as the total right derived functor `RΓ_{V(I)}` of the `V(I)`-supported
sections, and as the termwise `I`-power-torsion subcomplex of a chosen K-injective
representative. This module identifies them, and records how both behave under enlarging the
module universe.

## Main results

* `Stacks.LocalCohomology.derivedSectionsWithSupportInHomologyIsoOfKInjective` — on a K-injective
  complex the derived supported sections are computed termwise.
* `Stacks.LocalCohomology.powerTorsionComplexIsoSectionsWithSupportIn` — for a Noetherian ring
  the two termwise constructions agree complexwise.
* `Stacks.LocalCohomology.localCohomologyWithSupportInHomologyIso` — the two models of local
  cohomology agree in every degree.
* `Stacks.LocalCohomology.localCohomologyUliftIso` — local cohomology of a universe-lifted
  module is the lift of its local cohomology.
* `Stacks.LocalCohomology.localCohomologyShrinkIso` — the same comparison read in the other
  direction, for a module of the large universe that is small.

## Implementation notes

Noetherianity enters only through finite generation of `I`, which is what makes supported
sections agree with the `I`-power-torsion submodule.

The universe-change statements are needed because the two models live in different module
universes: the K-injective model is written in `ModuleCat.{u} A` for `A : Type u`, whereas the
supported-sections model is universe polymorphic in the module. Lifting is harmless: the
universe-lifting functor is exact and preserves injective objects, so it carries a K-injective
resolution to a K-injective resolution and commutes with the formation of homology.

## References

* [Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Dualizing (powerTorsionComplex kInjectiveRepresentative kInjectiveRepresentativeIso
  localCohomology)

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- Lifting the module universe carries the `I`-primary component to the `I`-primary
component. -/
def primaryComponentUliftEquiv (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    I.primaryComponent M ≃ₗ[A] I.primaryComponent (ULift.{v} M) := by
  let e : M ≃ₗ[A] ULift.{v} M := ULift.moduleEquiv.symm
  have hmem (x : M) : x ∈ I.primaryComponent M ↔ e x ∈ I.primaryComponent (ULift.{v} M) := by
    simp only [Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, fun a => by simpa using congrArg e (hn a)⟩,
      fun ⟨n, hn⟩ => ⟨n, fun a => by simpa using congrArg e.symm (hn a)⟩⟩
  refine e.ofSubmodules _ _ (Submodule.ext fun y => ⟨?_, fun hy =>
    ⟨e.symm y, (hmem _).mpr (by simpa using hy), by simp⟩⟩)
  rintro ⟨x, hx, rfl⟩
  exact (hmem x).mp hx

/-- Sections supported in `V(I)` commute with lifting the module universe. -/
def sectionsWithSupportUliftIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) :
    (ModuleCat.uliftFunctor.{v} A).obj
        ((sectionsWithSupportInFunctor.{u, 0} A
          (PrimeSpectrum.zeroLocus (I : Set A))).obj M) ≅
      (sectionsWithSupportInFunctor.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).obj
        ((ModuleCat.uliftFunctor.{v} A).obj M) :=
  LinearEquiv.toModuleIso
    (((ULift.moduleEquiv : ULift.{v} _ ≃ₗ[A] _).trans
        (LinearEquiv.ofEq _ _ (sectionsWithSupportIn_zeroLocus_eq_primaryComponent A I
          (Ideal.fg_of_isNoetherianRing I) (M : Type u)))).trans
      ((primaryComponentUliftEquiv A I (M : Type u)).trans
        (LinearEquiv.ofEq _ _ (sectionsWithSupportIn_zeroLocus_eq_primaryComponent A I
          (Ideal.fg_of_isNoetherianRing I) (ULift.{v} M))).symm))

/-- The universe-lifting comparison on supported sections is natural in the module. -/
lemma sectionsWithSupportUliftIso_naturality (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (ModuleCat.uliftFunctor.{v} A).map
        ((sectionsWithSupportInFunctor.{u, 0} A
          (PrimeSpectrum.zeroLocus (I : Set A))).map f) ≫
      (sectionsWithSupportUliftIso A I N).hom =
    (sectionsWithSupportUliftIso A I M).hom ≫
      (sectionsWithSupportInFunctor.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A))).map
        ((ModuleCat.uliftFunctor.{v} A).map f) :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl)

/-- Sections supported in `V(I)`, applied termwise to a complex, commute with lifting the
module universe. -/
def sectionsWithSupportUliftComplexIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.uliftFunctor.{v} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((sectionsWithSupportInFunctor.{u, 0} A
          (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J) ≅
      ((sectionsWithSupportInFunctor.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.uliftFunctor.{v} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => sectionsWithSupportUliftIso A I (J.X n))
    (fun i j _ => sectionsWithSupportUliftIso_naturality A I (J.d i j))

/-- Lifting the module universe is exact, hence commutes with the homology of a complex. -/
def uliftHomologyIso (A : Type u) [CommRing A] (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) :
    (((ModuleCat.uliftFunctor.{v} A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).homology i ≅
      (ModuleCat.uliftFunctor.{v} A).obj (J.homology i) :=
  letI : (ModuleCat.uliftFunctor.{v} A).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (J.sc i).mapHomologyIso (ModuleCat.uliftFunctor.{v} A)

/-- A module of the universe `max u v` which is small is the universe lift of its small
model. -/
def moduleShrinkUliftIso (R : Type u) [CommRing R] (M : ModuleCat.{max u v} R)
    [Small.{u} M] :
    (ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R (Shrink.{u} M)) ≅ M :=
  LinearEquiv.toModuleIso
    ((ULift.moduleEquiv : ULift.{v} (Shrink.{u} M) ≃ₗ[R] Shrink.{u} M).trans
      (Shrink.linearEquiv R M))

/-- Over a Noetherian ring the termwise `I`-power-torsion subcomplex of a complex is its
subcomplex of sections supported in `V(I)`. -/
def powerTorsionComplexIsoSectionsWithSupportIn (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    powerTorsionComplex A I J ≅
      ((sectionsWithSupportInFunctor.{u, 0} A
        (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          J :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.ofEq _ _ (sectionsWithSupportIn_zeroLocus_eq_primaryComponent A I
      (Ideal.fg_of_isNoetherianRing I) (J.X n)).symm).toModuleIso)
    (fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))

/-- On a K-injective complex representing `K`, local cohomology with support in `T` is the
homology of the termwise supported sections: the derived functor is computed by the
resolution. -/
def derivedSectionsWithSupportInHomologyIsoOfKInjective (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{max u v} A))
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (eK : DerivedCategory.Q.obj J ≅ K)
    [J.IsKInjective] (i : ℤ) :
    localCohomologyWithSupportIn A T K i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        (DerivedCategory.Q.obj
          (((sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)) := by
  let F := sectionsWithSupportInFunctor.{u, v} A T
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := ModuleCat.{max u v} A)
  let hDerived := H.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (fun L => by
      obtain ⟨L', q, hq, hL'⟩ := CochainComplex.exists_quasiIso_isKInjective L
      exact ⟨L', q, hL', hq⟩)
  letI : H.HasPointwiseRightDerivedFunctor W := hDerived.1
  let RF' := H.totalRightDerived (DerivedCategory.Qh (C := ModuleCat.{max u v} A)) W
  let β := H.totalRightDerivedUnit (DerivedCategory.Qh (C := ModuleCat.{max u v} A)) W
  let KJ := (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj J
  letI : IsIso (β.app KJ) := hDerived.2
    (DerivedCategory.Qh (C := ModuleCat.{max u v} A)) RF' β J (by infer_instance)
  let RF := derivedSectionsWithSupportIn.{u, v} A T
  let eR : H.obj KJ ≅ RF.obj (DerivedCategory.Q.obj J) := by
    change H.obj KJ ≅ RF'.obj (DerivedCategory.Q.obj J)
    exact asIso (β.app KJ) ≪≫
      RF'.mapIso ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app J)
  let eH : H.obj KJ ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) := by
    change DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ≅ _
    exact (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    (eH.symm ≪≫ eR ≪≫ RF.mapIso eK).symm

/-- **The two models agree.** Over a Noetherian ring, the `i`-th local cohomology module with
support in `V(I)` is the `i`-th cohomology of the `I`-power-torsion subcomplex of a K-injective
representative. -/
def localCohomologyWithSupportInHomologyIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A)) K i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (localCohomology A I K) :=
  derivedSectionsWithSupportInHomologyIsoOfKInjective.{u, 0} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K (kInjectiveRepresentative A K)
      (kInjectiveRepresentativeIso A K) i ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (DerivedCategory.Q.mapIso
        (powerTorsionComplexIsoSectionsWithSupportIn A I (kInjectiveRepresentative A K))).symm

/-- Local cohomology commutes with lifting the module universe. -/
def localCohomologyUliftIso (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (i : ℤ) :
    localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          ((ModuleCat.uliftFunctor.{v} A).obj M)) i ≅
      (ModuleCat.uliftFunctor.{v} A).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (localCohomology A I ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) := by
  let C₀ := ModuleCat.{u} A
  let C₁ := ModuleCat.{max u v} A
  let U := ModuleCat.uliftFunctor.{v} A
  let K₀ := (DerivedCategory.singleFunctor C₀ 0).obj M
  let hRes := DerivedCategory.Plus.exists_injective_nonempty_iso
    ((DerivedCategory.Plus.singleFunctor C₀ 0).obj M) 0
  let L := Classical.choose hRes
  let hL : L.obj.IsStrictlyGE 0 := Classical.choose (Classical.choose_spec hRes)
  let J₀ := ((InjectiveObject.ι C₀).mapCochainComplexPlus.obj L).obj
  let e₀ : DerivedCategory.Q.obj J₀ ≅ K₀ :=
    DerivedCategory.Plus.ι.mapIso
        (Classical.choice (Classical.choose_spec (Classical.choose_spec hRes))) ≪≫
      (DerivedCategory.Plus.singleFunctorιIso C₀ 0).app M
  let UJ := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj J₀
  haveI hJ₀GE : CochainComplex.IsStrictlyGE J₀ 0 :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := L.obj) (F := InjectiveObject.ι C₀) 0).2 hL
  haveI : ∀ n : ℤ, Injective (J₀.X n) := fun n => by
    change Injective ((InjectiveObject.ι C₀).obj (L.obj.X n))
    infer_instance
  haveI : CochainComplex.IsKInjective J₀ := CochainComplex.isKInjective_of_injective J₀ 0
  haveI : CochainComplex.IsStrictlyGE UJ 0 :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := J₀) (F := U) 0).2 hJ₀GE
  haveI : ∀ n : ℤ, Injective (UJ.X n) := fun n => by
    change Injective (U.obj (J₀.X n))
    infer_instance
  haveI : CochainComplex.IsKInjective UJ := CochainComplex.isKInjective_of_injective UJ 0
  let eK : DerivedCategory.Q.obj UJ ≅ (DerivedCategory.singleFunctor C₁ 0).obj (U.obj M) :=
    (U.mapDerivedCategoryFactors.app J₀).symm ≪≫ U.mapDerivedCategory.mapIso e₀ ≪≫
      (U.mapDerivedCategorySingleFunctor 0).app M
  let eSmall := (localCohomologyWithSupportInHomologyIso A I K₀ i).symm ≪≫
    derivedSectionsWithSupportInHomologyIsoOfKInjective.{u, 0} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K₀ J₀ e₀ i ≪≫
    (DerivedCategory.homologyFunctorFactors C₀ i).app
      (((sectionsWithSupportInFunctor.{u, 0} A
        (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J₀)
  let eBig := derivedSectionsWithSupportInHomologyIsoOfKInjective A
      (PrimeSpectrum.zeroLocus (I : Set A)) _ UJ eK i ≪≫
    (DerivedCategory.homologyFunctorFactors C₁ i).app
      (((sectionsWithSupportInFunctor.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj UJ)
  let eLiftHomology := (uliftHomologyIso A
      (((sectionsWithSupportInFunctor.{u, 0} A
        (PrimeSpectrum.zeroLocus (I : Set A))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J₀) i).symm ≪≫
    HomologicalComplex.homologyMapIso (sectionsWithSupportUliftComplexIso A I J₀) i
  exact eBig ≪≫ (U.mapIso eSmall ≪≫ eLiftHomology).symm

/-- For a module of the large universe which is small, local cohomology is the universe lift of
the local cohomology of its small model. -/
def localCohomologyShrinkIso (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{max u v} R) [Small.{u} M] (i : ℤ) :
    (ModuleCat.uliftFunctor.{v} R).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (localCohomology R I ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (Shrink.{u} M))))) ≅
      localCohomologyWithSupportIn R (PrimeSpectrum.zeroLocus (I : Set R))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) i :=
  (localCohomologyUliftIso R I (ModuleCat.of R (Shrink.{u} M)) i).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso
      ((derivedSectionsWithSupportIn.{u, v} R
        (PrimeSpectrum.zeroLocus (I : Set R))).mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).mapIso
          (moduleShrinkUliftIso R M)))

end Stacks.LocalCohomology

end
