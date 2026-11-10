module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Composition
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.RightAdjoint
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.DerivedLoc
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ChangeOfSupport
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian

/-!
# Cutting a local cohomology class by a principal ideal

Let `A` be a commutative ring and `f : A`. Localization away from `f` is exact, so it induces an
endofunctor of the derived category `D(A)` together with a unit out of the identity; the fibre of
that unit computes local cohomology for the principal ideal `(f)`. Consequently a cohomology class
of `K` killed by `f` lifts along the counit `RΓ_{(f)}(K) ⟶ K`.

Over a Noetherian ring this gives the cutting step of the minimal-prime filtration: a class in
`H^i_{V(I)}(K)` killed by `f` already comes from `H^i_{V(I) ∩ V(f)}(K)`.

## Main results

* `Stacks.LocalCohomology.powerTorsion_of_localization_isZero` — an object of `D(A)` whose
  localization away from `f` vanishes has `(f)`-power-torsion cohomology.
* `Stacks.LocalCohomology.exists_principalLocalCohomology_lift_of_smul_eq_zero` — a cohomology
  class killed by `f` lifts along the counit of the local cohomology adjunction for `(f)`.
* `Stacks.LocalCohomology.exists_iteratedLocalCohomology_to_intersection` — iterated local
  cohomology maps to local cohomology for the join of the two ideals, compatibly with the counits.
* `Stacks.LocalCohomology.exists_closedSupport_principal_lift` — a class in `H^i_{V(I)}(K)` killed
  by `f` lifts to `H^i_{V(I) ∩ V(f)}(K)`.

## Implementation notes

The lift along the counit is extracted from the long exact cohomology sequence of the triangle
whose third term is the derived localization away from `f`: the localization kills the first term,
which therefore has `(f)`-power-torsion cohomology and so factors through local cohomology by
adjunction. The closed-support statement is transported to the model of derived sections with
support in `V(I)` along the comparison of the two models, using the universal property of the
augmentation `RΓ_{V(I)} ⟶ id`.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- A functor into modules sends a composite to the composite of the induced linear maps. -/
private theorem map_comp_apply {C : Type*} [Category C] {R : Type*} [Ring R] (H : C ⥤ ModuleCat R)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (y : H.obj X) :
    (H.map g).hom ((H.map f).hom y) = (H.map (f ≫ g)).hom y := by
  rw [H.map_comp]; rfl

/-- An object of `D(A)` whose localization away from `f` vanishes has `(f)`-power-torsion
cohomology. -/
theorem powerTorsion_of_localization_isZero (A : Type u) [CommRing A] (f : A)
    (X : DerivedCategory (ModuleCat.{max u v} A))
    (hX : IsZero ((derivedLoc.{u, v} f).obj X)) :
    Dualizing.derivedPowerTorsionProperty A (Ideal.span ({f} : Set A))
      (Submodule.fg_span_singleton f) X :=
  (derivedPowerTorsion_iff_loc.{u, v} (Ideal.span ({f} : Set A))
      (Submodule.fg_span_singleton f) {f} (by simp) X).mpr
    fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hX

/-- A cohomology class of `K` killed by `f` lifts along the counit `RΓ_{(f)}(K) ⟶ K` of the local
cohomology adjunction for the principal ideal `(f)`. -/
theorem exists_principalLocalCohomology_lift_of_smul_eq_zero (A : Type u) [CommRing A] (f : A)
    (X : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X) (hx : f • x = 0) :
    ∃ y, ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
      ((Dualizing.localCohomologyAdjunction.{u, max u v} A (Ideal.span ({f} : Set A))
        (Submodule.fg_span_singleton f)).counit.app X)).hom y = x := by
  let F := locFunctor.{u, v} f
  let η := derivedLocUnit.{u, v} f
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i
  obtain ⟨Z, g, h, hdist⟩ := distinguished_cocone_triangle (η.app X)
  let T := (Triangle.mk (η.app X) g h).invRotate
  have hT : T ∈ distTriang _ := inv_rot_of_distTriang _ hdist
  have hzero : IsZero (F.mapDerivedCategory.obj T.obj₁) :=
    Triangle.isZero₁_of_isIso₂ _ (F.mapDerivedCategory.map_distinguished _ hT)
      (derivedLocUnit_map_isIso.{u, v} f X)
  have htor := powerTorsion_of_localization_isZero A f T.obj₁ hzero
  let P := Dualizing.derivedPowerTorsionProperty.{u, max u v} A (Ideal.span ({f} : Set A))
    (Submodule.fg_span_singleton f)
  let W : P.FullSubcategory := ⟨T.obj₁, htor⟩
  let adj := Dualizing.localCohomologyAdjunction.{u, max u v} A (Ideal.span ({f} : Set A))
    (Submodule.fg_span_singleton f)
  let a : T.obj₁ ⟶ P.ι.obj ((Dualizing.localCohomologyFunctor.{u, max u v} A
      (Ideal.span ({f} : Set A)) (Submodule.fg_span_singleton f)).obj X) :=
    P.ι.map ((adj.homEquiv W X) T.mor₁)
  have ha : a ≫ adj.counit.app X = T.mor₁ := (adj.homEquiv W X).symm_apply_apply T.mor₁
  have hxzero : (H.map T.mor₂).hom x = 0 := by
    change (H.map (η.app X)).hom x = 0
    let e := (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F i).app X
    have hinj := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    apply hinj
    change e.hom.hom ((H.map (η.app X)).hom x) = e.hom.hom 0
    rw [map_zero]
    have hu := IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (H.obj X)) ⟨f, Submonoid.mem_powers f⟩
    have hinjf := (Module.End.isUnit_iff _).mp hu |>.1
    apply hinjf
    change f • e.hom.hom ((H.map (η.app X)).hom x) = f • 0
    rw [smul_zero, ← map_smul, ← map_smul, hx, map_zero, map_zero]
  have hex : Function.Exact (H.map T.mor₁).hom (H.map T.mor₂).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (DerivedCategory.HomologySequence.exact₂ T hT i)
  obtain ⟨y, hy⟩ := (hex x).mp hxzero
  refine ⟨(H.map a).hom y, ?_⟩
  exact (map_comp_apply H a _ y).trans ((congrArg (fun φ => (H.map φ).hom y) ha).trans hy)

/-- Iterated local cohomology, first for `I` and then for `J`, maps to local cohomology for
`I ⊔ J`, compatibly with the counits of the adjunctions involved. -/
theorem exists_iteratedLocalCohomology_to_intersection (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I J : Ideal A) (K : DerivedCategory (ModuleCat.{max u v} A)) :
    ∃ φ : (Dualizing.localCohomologyFunctor.{u, max u v} A J (Ideal.fg_of_isNoetherianRing J) ⋙
          (Dualizing.derivedPowerTorsionProperty A J (Ideal.fg_of_isNoetherianRing J)).ι).obj
        ((Dualizing.localCohomologyFunctor.{u, max u v} A I (Ideal.fg_of_isNoetherianRing I) ⋙
          (Dualizing.derivedPowerTorsionProperty A I
            (Ideal.fg_of_isNoetherianRing I)).ι).obj K) ⟶
      (Dualizing.localCohomologyFunctor.{u, max u v} A (I ⊔ J)
          (Ideal.fg_of_isNoetherianRing (I ⊔ J)) ⋙
        (Dualizing.derivedPowerTorsionProperty A (I ⊔ J)
          (Ideal.fg_of_isNoetherianRing (I ⊔ J))).ι).obj K,
      φ ≫ (Dualizing.localCohomologyAdjunction.{u, max u v} A (I ⊔ J)
            (Ideal.fg_of_isNoetherianRing (I ⊔ J))).counit.app K =
        (Dualizing.localCohomologyAdjunction.{u, max u v} A J
              (Ideal.fg_of_isNoetherianRing J)).counit.app
            ((Dualizing.localCohomologyFunctor.{u, max u v} A I
                (Ideal.fg_of_isNoetherianRing I) ⋙
              (Dualizing.derivedPowerTorsionProperty A I
                (Ideal.fg_of_isNoetherianRing I)).ι).obj K) ≫
          (Dualizing.localCohomologyAdjunction.{u, max u v} A I
            (Ideal.fg_of_isNoetherianRing I)).counit.app K := by
  let hI := Ideal.fg_of_isNoetherianRing (R := A) I
  let hJ := Ideal.fg_of_isNoetherianRing (R := A) J
  let P := Dualizing.derivedPowerTorsionProperty.{u, max u v} A (I ⊔ J) (Submodule.FG.sup hI hJ)
  let X : P.FullSubcategory := ⟨_,
    Dualizing.localCohomology_comp_torsion A I J hI hJ
      ((Dualizing.localCohomologyFunctor.{u, max u v} A I hI).obj K)⟩
  let adj := Dualizing.localCohomologyAdjunction.{u, max u v} A (I ⊔ J) (Submodule.FG.sup hI hJ)
  let φ : P.ι.obj X ⟶ K :=
    (Dualizing.localCohomologyAdjunction.{u, max u v} A J hJ).counit.app
        ((Dualizing.localCohomologyFunctor.{u, max u v} A I hI ⋙
          (Dualizing.derivedPowerTorsionProperty A I hI).ι).obj K) ≫
      (Dualizing.localCohomologyAdjunction.{u, max u v} A I hI).counit.app K
  refine ⟨P.ι.map ((adj.homEquiv X K) φ), ?_⟩
  exact (adj.homEquiv X K).symm_apply_apply φ

attribute [local instance] isIso_compareSectionsWithSupportLocalCohomology

/-- Read backwards, the comparison of the two models of local cohomology carries the augmentation
`RΓ_{V(I)} ⟶ id` to the counit of the local cohomology adjunction. -/
theorem compareSectionsWithSupportLocalCohomology_inv_comp_augmentation (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) :
    (asIso (compareSectionsWithSupportLocalCohomology.{u, v} A I hI)).inv ≫
        derivedSectionsWithSupportInAugmentation.{u, v} A
          (PrimeSpectrum.zeroLocus (I : Set A)) =
      (Dualizing.localCohomologyAdjunction.{u, max u v} A I hI).counit := by
  rw [← compareSectionsWithSupportLocalCohomology_comp_counit A I hI]
  exact Iso.inv_hom_id_assoc (asIso (compareSectionsWithSupportLocalCohomology.{u, v} A I hI)) _

/-- **Cutting a class by a principal ideal.** Over a Noetherian ring, a class in `H^i_{V(I)}(K)`
killed by `f` is the image of a class with support in `V(I) ∩ V(f)`. -/
theorem exists_closedSupport_principal_lift (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (f : A) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) K i)
    (hx : f • x = 0) :
    ∃ y : localCohomologyWithSupportIn.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A)) K i,
      (changeOfSupport A Set.inter_subset_left K i).hom y = x := by
  let J := Ideal.span ({f} : Set A)
  let hI := Ideal.fg_of_isNoetherianRing (R := A) I
  let hJ := Ideal.fg_of_isNoetherianRing (R := A) J
  let hS := Ideal.fg_of_isNoetherianRing (R := A) (I ⊔ J)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i
  let eI := (asIso (compareSectionsWithSupportLocalCohomology.{u, v} A I hI)).app K
  let eS := (asIso (compareSectionsWithSupportLocalCohomology.{u, v} A (I ⊔ J) hS)).app K
  let X := (Dualizing.localCohomologyFunctor.{u, max u v} A I hI ⋙
    (Dualizing.derivedPowerTorsionProperty A I hI).ι).obj K
  let W := (Dualizing.localCohomologyFunctor.{u, max u v} A J hJ ⋙
    (Dualizing.derivedPowerTorsionProperty A J hJ).ι).obj X
  let b : W ⟶ X := (Dualizing.localCohomologyAdjunction.{u, max u v} A J hJ).counit.app X
  obtain ⟨z, hz⟩ := exists_principalLocalCohomology_lift_of_smul_eq_zero A f X i
    ((H.map eI.hom).hom x) (by rw [← map_smul, hx, map_zero])
  change (H.map b).hom z = (H.map eI.hom).hom x at hz
  obtain ⟨a, ha⟩ := exists_iteratedLocalCohomology_to_intersection A I J K
  let hSI : PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A) ⊆
    PrimeSpectrum.zeroLocus (I : Set A) := PrimeSpectrum.zeroLocus_anti_mono_ideal le_sup_left
  let inc := (derivedSectionsWithSupportInInclusion.{u, v} A hSI).app K
  have hW : Dualizing.derivedPowerTorsionProperty A I hI W := by
    have ht := Dualizing.localCohomology_comp_torsion A I J hI hJ
      ((Dualizing.localCohomologyFunctor.{u, max u v} A I hI).obj K)
    intro n w
    obtain ⟨k, hk, hkill⟩ := ht n w
    exact ⟨k, hk, fun c hc => hkill c ((pow_le_pow_left' (le_sup_left : I ≤ I ⊔ J) k) hc)⟩
  have hinc : inc ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A))).app K =
      (derivedSectionsWithSupportInAugmentation.{u, v} A
        (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A))).app K :=
    NatTrans.congr_app (derivedSectionsWithSupportInInclusion_comp_augmentation A hSI) K
  have he : ∀ (S : Ideal A) (hS : S.FG),
      ((asIso (compareSectionsWithSupportLocalCohomology.{u, v} A S hS)).app K).inv ≫
        (derivedSectionsWithSupportInAugmentation.{u, v} A
          (PrimeSpectrum.zeroLocus (S : Set A))).app K =
      (Dualizing.localCohomologyAdjunction.{u, max u v} A S hS).counit.app K := fun S hS =>
    NatTrans.congr_app
      (compareSectionsWithSupportLocalCohomology_inv_comp_augmentation.{u, v} A S hS) K
  have key : a ≫ eS.inv ≫ inc = b ≫ eI.inv :=
    (bijective_comp_derivedSectionsWithSupportInAugmentation.{u, v} A I K W hW).injective (by
      simp only [eI, eS, Category.assoc, hinc, he I hI, he (I ⊔ J) hS]
      exact ha)
  have hab : (a ≫ eS.inv) ≫ inc ≫ eI.hom = b := by
    rw [Category.assoc, ← Category.assoc eS.inv, ← Category.assoc a, key, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hresult : ∃ y : localCohomologyWithSupportIn.{u, v} A
      (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A)) K i,
      (changeOfSupport A hSI K i).hom y = x := by
    refine ⟨(H.map (a ≫ eS.inv)).hom z, ?_⟩
    apply (ModuleCat.mono_iff_injective (H.map eI.hom)).mp inferInstance
    exact (map_comp_apply H _ _ _).trans ((map_comp_apply H _ _ _).trans
      ((congrArg (fun φ => (H.map φ).hom z) hab).trans hz))
  have hset : PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A) := by
    rw [PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_span]
  obtain ⟨y, hy⟩ := hresult
  refine ⟨(changeOfSupport A hset.subset K i).hom y, ?_⟩
  change ((changeOfSupport A hset.subset K i ≫
    changeOfSupport A Set.inter_subset_left K i).hom) y = x
  rw [changeOfSupport_trans]
  exact hy

end Stacks.LocalCohomology

end
