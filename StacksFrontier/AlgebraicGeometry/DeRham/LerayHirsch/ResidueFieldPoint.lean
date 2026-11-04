module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.HomologyPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.OnePoint
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# Cohomology of the pulled back structure sheaf at a point

Let `g : S ⟶ W` be a morphism of ringed spaces whose source has at most one point. Then
`Lg^*𝒪_W[-n] ≅ 𝒪_S[-n]` has cohomology only in degree `n`, where it is `Γ(S, 𝒪_S)`. For
`S = Spec K` with `K` a field, read over `K`, this is a line, spanned by the pullback of the class
of `1`. These are the facts about the source `⨁_i 𝒪_Y[-n_i]` of the Leray--Hirsch morphism that the
fibre criterion of [Stacks, Tag 0FMP] consumes, together with the detection of isomorphisms of
`D(𝒪_{Spec K})` by the cohomology of derived global sections.

## Main definitions

* `Stacks.Cohomology.ResidueFieldPoint.derivedPullbackUnitComplexIso`: `Lg^*𝒪_W[-n] ≅ 𝒪_S[-n]`.
* `Stacks.Cohomology.ResidueFieldPoint.restrictToField`: restriction of scalars along
  `K ≅ Γ(Spec K, 𝒪)`.
* `Stacks.Cohomology.ResidueFieldPoint.pointCohomology`: `H^k(Spec K, -)` read over `K`.

## Main results

* `Stacks.Cohomology.ResidueFieldPoint.isZero_cohomologyModule_derivedPullback_unitComplex`.
* `Stacks.Cohomology.ResidueFieldPoint.finrank_cohomologyModule_derivedPullback_unitComplex`.
* `Stacks.Cohomology.ResidueFieldPoint.isIso_of_forall_isIso_pointCohomology`.
* `Stacks.Cohomology.ResidueFieldPoint.exists_lof_eq_smul_homologyPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HomologyPullback Stacks.Cohomology.OnePointDetection

universe u

namespace Stacks.Cohomology.ResidueFieldPoint

attribute [local instance] HasDerivedCategory.standard

section Subsingleton

variable {S W : RingedSpace.{u, u}} (g : S ⟶ W)

/-- `Lg^*(𝒪_W[-n]) ≅ 𝒪_S[-n]`, in the spelling `unitComplex` of the structure sheaf in degree
`n`. -/
def derivedPullbackUnitComplexIso (n : ℤ) :
    (derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n)) ≅
      DerivedCategory.Q.obj (unitComplex S n) :=
  (derivedPullback g).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ n).app _).symm ≪≫
    Stacks.RingedSpace.derivedPullbackShiftedUnitIso g n ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ n).app _

variable [Subsingleton S.carrier]

/-- On a space with at most one point, `H^j(S, Lg^*𝒪_W[-n])` vanishes for `j ≠ n`. -/
theorem isZero_cohomologyModule_derivedPullback_unitComplex {n j : ℤ} (h : j ≠ n) :
    IsZero (cohomologyModule ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n)))
      j) :=
  (isZero_homologySections_single S n j h _).of_iso
    ((DerivedCategory.homologyFunctor _ j).mapIso
      ((baseSections S).mapIso (derivedPullbackUnitComplexIso g n)))

/-- On a space with at most one point, `H^n(S, Lg^*𝒪_W[-n]) ≅ Γ(S, 𝒪_S)`. -/
def cohomologyModuleDerivedPullbackUnitComplexIso (n : ℤ) :
    cohomologyModule ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n))) n ≅
      (sectionsOverOpen S ⊤).obj (SheafOfModules.unit (structureSheafRing S)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      ((baseSections S).mapIso (derivedPullbackUnitComplexIso g n)) ≪≫
    homologySectionsSingleSelfIso S n _

end Subsingleton

section Field

variable (K : Type u) [Field K]

/-- Restriction of scalars from `Γ(Spec K, 𝒪)` to the field `K`. -/
abbrev restrictToField :
    ModuleCat.{u} (baseRing (Spec (CommRingCat.of K)).toRingedSpace) ⥤ ModuleCat.{u} K :=
  ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/-- The ring `Γ(Spec K, 𝒪)`, as a module over itself and read over `K`, is `K`. -/
def globalSectionsLinearEquiv :
    (restrictToField K).obj (ModuleCat.of (baseRing (Spec (CommRingCat.of K)).toRingedSpace)
      (baseRing (Spec (CommRingCat.of K)).toRingedSpace)) ≃ₗ[K] K where
  toFun x := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x
  invFun r := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r
  map_add' x y := map_add (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x y
  map_smul' c x := by
    rw [ModuleCat.restrictScalars.smul_def]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c *
        (show Γ(Spec (CommRingCat.of K), ⊤) from x)) =
        c * (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Spec (CommRingCat.of K), ⊤) from x)
    rw [map_mul]
    congr 1
    exact congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id
  left_inv x := congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id
  right_inv r := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

/-- Global sections of the structure sheaf of `Spec K`, read over `K`, are `K`. -/
def unitSectionsLinearEquiv :
    (restrictToField K).obj ((sectionsOverOpen (Spec (CommRingCat.of K)).toRingedSpace ⊤).obj
      (SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of K)).toRingedSpace))) ≃ₗ[K]
      K :=
  ((restrictToField K).mapIso (Iso.refl _ :
    (sectionsOverOpen (Spec (CommRingCat.of K)).toRingedSpace ⊤).obj
      (SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of K)).toRingedSpace)) ≅
    ModuleCat.of (baseRing (Spec (CommRingCat.of K)).toRingedSpace)
      (baseRing (Spec (CommRingCat.of K)).toRingedSpace))).toLinearEquiv.trans
    (globalSectionsLinearEquiv K)

/-- `H^n(Spec K, Lg^*𝒪_W[-n])`, read over the field `K`, is a line. -/
theorem finrank_cohomologyModule_derivedPullback_unitComplex {W : RingedSpace.{u, u}}
    (g : (Spec (CommRingCat.of K)).toRingedSpace ⟶ W) (n : ℤ) :
    Module.finrank K ((restrictToField K).obj
      (cohomologyModule ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n))) n)) =
      1 :=
  (((restrictToField K).mapIso
      (cohomologyModuleDerivedPullbackUnitComplexIso g n)).toLinearEquiv.trans
    (unitSectionsLinearEquiv K)).finrank_eq.trans (Module.finrank_self K)

/-- `H^k(Spec K, -)`, read over the field `K`. -/
abbrev pointCohomology (k : ℤ) :
    DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of K)).toRingedSpace))
      ⥤ ModuleCat.{u} K :=
  baseSections (Spec (CommRingCat.of K)).toRingedSpace ⋙
    DerivedCategory.homologyFunctor _ k ⋙ restrictToField K

/-- The functor `H^k(Spec K, -)`, read over `K`, is additive. -/
instance pointCohomology_additive (k : ℤ) : (pointCohomology K k).Additive := by
  have : (baseSections (Spec (CommRingCat.of K)).toRingedSpace).Additive :=
    Functor.additive_of_iso (Stacks.Cohomology.SubsingletonSections.derivedSectionsOverOpenIso
      (Spec (CommRingCat.of K)).toRingedSpace ⊤).symm
  dsimp only [pointCohomology]
  infer_instance

/-- **The cohomology of derived global sections on `Spec K` detects isomorphisms.** -/
theorem isIso_of_forall_isIso_pointCohomology
    {A B : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of K)).toRingedSpace))} (φ : A ⟶ B)
    (h : ∀ j : ℤ, IsIso ((pointCohomology K j).map φ)) : IsIso φ := by
  refine isIso_of_forall_isIso_homology_sections _ φ fun j => ?_
  have hj : IsIso ((forget (ModuleCat.{u} K)).map ((pointCohomology K j).map φ)) :=
    inferInstance
  have : IsIso ((forget (ModuleCat.{u} (baseRing (Spec (CommRingCat.of K)).toRingedSpace))).map
      ((DerivedCategory.homologyFunctor _ j).map
        ((baseSections (Spec (CommRingCat.of K)).toRingedSpace).map φ))) := hj
  exact isIso_of_reflects_iso _ (forget (ModuleCat.{u}
    (baseRing (Spec (CommRingCat.of K)).toRingedSpace)))

/-- A module over `Γ(Spec K, 𝒪)` which is a line over `K` has a nonzero element. -/
theorem exists_ne_zero_of_finrank_eq_one
    (M : ModuleCat.{u} (baseRing (Spec (CommRingCat.of K)).toRingedSpace))
    (h : Module.finrank K ((restrictToField K).obj M) = 1) : ∃ y : M, y ≠ 0 :=
  @exists_ne _ (Module.nontrivial_of_finrank_eq_succ h) 0

/-- **A graded vector space which is a line in one degree and zero elsewhere is spanned by any
nonzero vector of that line.** -/
theorem exists_lof_eq_smul_of_finrank_eq_one (P : ℤ → ModuleCat.{u} K) (n : ℤ) (v : P n)
    (hv : v ≠ 0) (hrank : Module.finrank K (P n) = 1) (hz : ∀ j, j ≠ n → Subsingleton (P j))
    (j : ℤ) (x : P j) :
    ∃ c : K, DirectSum.lof K ℤ (fun k => P k) j x = c • DirectSum.lof K ℤ (fun k => P k) n v := by
  by_cases hj : j = n
  · subst hj
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).1 hrank x
    exact ⟨c, by rw [← hc, map_smul]⟩
  · have := hz j hj
    exact ⟨0, by rw [Subsingleton.elim x 0, map_zero, zero_smul]⟩

/-- **On `Spec K` the pulled back unit class spans the cohomology of `Lg^*𝒪_W[-n]`**: the total
cohomology is the line through the pullback of the class of `1`, which sits in degree `n`. -/
theorem exists_lof_eq_smul_homologyPullback {W : RingedSpace.{u, u}}
    (g : (Spec (CommRingCat.of K)).toRingedSpace ⟶ W) (n j : ℤ)
    (x : (restrictToField K).obj
      (cohomologyModule ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n))) j)) :
    ∃ c : K, DirectSum.lof K ℤ (fun k => (restrictToField K).obj (cohomologyModule
        ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n))) k)) j x =
      c • DirectSum.lof K ℤ (fun k => (restrictToField K).obj (cohomologyModule
        ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n))) k)) n
        (homologyPullback g (DerivedCategory.Q.obj (unitComplex W n)) n (unitCycleClass W n)) := by
  have hrank := finrank_cohomologyModule_derivedPullback_unitComplex K g n
  have hy := (exists_ne_zero_of_finrank_eq_one K (cohomologyModule
    ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n))) n) hrank).choose_spec
  refine exists_lof_eq_smul_of_finrank_eq_one K (fun k => (restrictToField K).obj (cohomologyModule
    ((derivedPullback g).obj (DerivedCategory.Q.obj (unitComplex W n))) k)) n _
    (homologyPullback_unitCycleClass_ne_zero g n _ _ hy) hrank (fun j hj => ?_) j x
  exact ModuleCat.isZero_iff_subsingleton.1 ((restrictToField K).map_isZero
    (isZero_cohomologyModule_derivedPullback_unitComplex g hj))

end Field

end Stacks.Cohomology.ResidueFieldPoint
