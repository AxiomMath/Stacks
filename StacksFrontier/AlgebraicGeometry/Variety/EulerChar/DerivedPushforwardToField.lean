module

public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatIndexed
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CotangentAppIso.Basic

/-!
# Cohomology over a field, read off the derived pushforward to the point

Let `K` be a field, let `q : Y ⟶ Spec K` be quasi-compact and quasi-separated and let `M` be a
quasi-coherent `𝒪_Y`-module. The `K`-vector space of global sections of the `n`-th cohomology sheaf
of `Rq_*(M[0])` on the point `Spec K` has the dimension of `H^n(Y, M)`
(`AlgebraicGeometry.cohomologyOverField`), and it is zero in negative degrees. Consequently, for
`q` proper and `M` coherent, the Euler characteristic `χ(Y, M)` of [Stacks, Tag 0BEJ] is the
alternating sum of the dimensions of the global sections of the cohomology sheaves of
`Rq_*(M[0])`. This is the form in which the derived fibre `Li_s^*Rf_*ℱ` of [Stacks, Tag 0BDI]
computes `χ(X_s, ℱ_s)` once base change identifies it with `R(f_s)_*ℱ_s`, which is the first
step of the proof of [Stacks, Tag 0B9T].

## Main results

* `AlgebraicGeometry.finrank_homology_derivedPushforward_eq_finrank_cohomologyOverField`: the
  comparison in degree `n ≥ 0`. The cohomology sheaf of `Rq_*(M[0])` is the higher direct image
  `R^n q_*M` (`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`), whose
  global sections over the affine base are `H^n(Y, M)` ([Stacks, Tag 01XK],
  `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso`).
* `AlgebraicGeometry.finrank_homology_derivedPushforward_of_neg`: negative degrees vanish.
* `AlgebraicGeometry.eulerCharacteristic_eq_finsum_homology_derivedPushforward`: the Euler
  characteristic as an alternating sum over the cohomology sheaves of `Rq_*(M[0])`.

## References

* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- `Rq_*(M[0])` is the bounded-below right derived functor of `q_*` applied to `M[0]`. -/
private theorem nonempty_derivedPushforward_single_iso_rightDerivedFunctorPlus {K : Type u}
    [Field K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) (M : Y.Modules) :
    Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        q.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj M) ≅
      ((modulePushforward q.toLRSHom.toShHom).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj M)).obj) := by
  have hE : ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj M).obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor Y.Modules 0).obj M).IsGE 0
    infer_instance
  open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
  exact Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (modulePushforward q.toLRSHom.toShHom) (derivedPushforward q.toLRSHom.toShHom)
    (derivedPushforwardUnit q.toLRSHom.toShHom)
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj M) 0 hE

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **`Γ(Spec K, H^n(Rq_*(M[0]))) ≅ H^n(Y, M)`** as `K`-vector spaces, for a quasi-compact
quasi-separated `q : Y ⟶ Spec K` and a quasi-coherent `M`. -/
theorem nonempty_homology_derivedPushforward_linearEquiv_cohomologyOverField (K : Type u)
    [Field K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [QuasiCompact q] [QuasiSeparated q]
    (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Nonempty (((moduleSpecΓFunctor (R := .of K)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).obj
          ((derivedPushforward q.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj M)))) ≃ₗ[K]
      cohomologyOverField K q M n) := by
  obtain ⟨e⟩ := nonempty_derivedPushforward_single_iso_rightDerivedFunctorPlus q M
  let e' : (DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).obj
        ((derivedPushforward q.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj M)) ≅
      ((Scheme.Modules.pushforward q).rightDerived n).obj M :=
    (DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).mapIso e ≪≫
      Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat
        (Scheme.Modules.pushforward q) M n
  exact ⟨(eqToIso (Stacks.Conormal.CotangentAppIso.moduleSpecΓFunctor_obj_eq _) ≪≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of K)).inv.hom).mapIso
      ((SheafOfModules.evaluation (Spec (.of K)).ringCatSheaf (op ⊤)).mapIso e' ≪≫
        (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso
          q M n).symm) ≪≫
      (ModuleCat.restrictScalarsComp'App _ _ _
        (by rw [show q.appLE ⊤ ⊤ (by simp) = q.appTop from q.appLE_eq_app (U := ⊤)]; rfl)
        _).symm).toLinearEquiv⟩

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **`dim_K Γ(Spec K, H^n(Rq_*(M[0]))) = dim_K H^n(Y, M)`** for a quasi-compact quasi-separated
`q : Y ⟶ Spec K` and a quasi-coherent `M`. -/
theorem finrank_homology_derivedPushforward_eq_finrank_cohomologyOverField (K : Type u) [Field K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [QuasiCompact q] [QuasiSeparated q]
    (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Module.finrank K ((moduleSpecΓFunctor (R := .of K)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).obj
          ((derivedPushforward q.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj M)))) =
      Module.finrank K (cohomologyOverField K q M n) :=
  (nonempty_homology_derivedPushforward_linearEquiv_cohomologyOverField K q M n).some.finrank_eq

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- The cohomology sheaves of `Rq_*(M[0])` vanish in negative degrees, so their global sections
have dimension zero. -/
theorem finrank_homology_derivedPushforward_of_neg (K : Type u) [Field K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) (M : Y.Modules) (i : ℤ) (hi : i < 0) :
    Module.finrank K ((moduleSpecΓFunctor (R := .of K)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
          ((derivedPushforward q.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj M)))) = 0 := by
  obtain ⟨e⟩ := nonempty_derivedPushforward_single_iso_rightDerivedFunctorPlus q M
  have hN : IsZero ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
        ((derivedPushforward q.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj M))) :=
    (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
        (Scheme.Modules.pushforward q) i hi M).of_iso
      ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).mapIso e)
  have hz : IsZero ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of K)).inv.hom).obj
      ((SheafOfModules.evaluation (Spec (.of K)).ringCatSheaf (op ⊤)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
          ((derivedPushforward q.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj M))))) :=
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of K)).inv.hom).map_isZero
      ((SheafOfModules.evaluation (Spec (.of K)).ringCatSheaf (op ⊤)).map_isZero hN)
  have : Subsingleton ((moduleSpecΓFunctor (R := .of K)).obj
      ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
        ((derivedPushforward q.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj M)))) :=
    (ModuleCat.isZero_iff_subsingleton).1 hz
  exact Module.finrank_zero_of_subsingleton

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **The Euler characteristic of a coherent module on a scheme proper over a field, read off the
derived pushforward to the point.** -/
theorem eulerCharacteristic_eq_finsum_homology_derivedPushforward (K : Type u) [Field K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [IsProper q] (M : Y.Modules) [M.IsCoherent] :
    eulerCharacteristic K q M =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.finrank K ((moduleSpecΓFunctor (R := .of K)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
          ((derivedPushforward q.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj M)))) : ℤ) := by
  have : M.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  set g : ℤ → ℤ := fun i => (i.negOnePow : ℤ) * (Module.finrank K
    ((moduleSpecΓFunctor (R := .of K)).obj
      ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
        ((derivedPushforward q.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj M)))) : ℤ) with hg
  have hsupp : Function.support g ⊆ Set.range (Nat.cast : ℕ → ℤ) := by
    intro i hi
    by_contra hni
    apply hi
    have hneg : i < 0 := by
      by_contra h
      exact hni ⟨i.toNat, Int.toNat_of_nonneg (not_lt.1 h)⟩
    simp only [hg, finrank_homology_derivedPushforward_of_neg K q M i hneg, Nat.cast_zero,
      mul_zero]
  have hrange : ∑ᶠ i ∈ Set.range (Nat.cast : ℕ → ℤ), g i = ∑ᶠ i, g i := by
    rw [← finsum_mem_univ g]
    exact finsum_mem_inter_support_eq' g _ _ fun x hx => ⟨fun _ => trivial, fun _ => hsupp hx⟩
  rw [← hrange, finsum_mem_range Nat.cast_injective, eulerCharacteristic_eq_finsum]
  refine finsum_congr fun n => ?_
  simp only [hg, finrank_homology_derivedPushforward_eq_finrank_cohomologyOverField K q M n,
    Int.coe_negOnePow_natCast]

end AlgebraicGeometry

end
