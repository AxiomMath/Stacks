module

public import StacksFrontier.RingTheory.Koszul.SheafSectionBimoduleTower
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryIsZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionReflectsIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticGlobalSectionsConservative
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitCompatibleFamily

/- Keep the admissible-sequence convention previously supplied by the global instance. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-!
# A quasi-coherent module over the Koszul sheaf with zero derived global sections is zero

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `ℬ = Koszul.liftedPowSheafAlgebra f` be
the sheaf of Koszul differential graded algebras `(K_{n+1})_n` on the chaotic site
`Stacks.LiftedNat`, and let `M` be an object of `QC(ℬ, d)`. The last paragraph of the proof of
Proposition 0GZK shows that `M = 0` as soon as `RΓ(M) = R lim M_n` vanishes: then
`0 = (R lim M_n) ⊗^𝐋_R K_t = R lim (M_n ⊗^𝐋_R K_t) = R lim (M_n ⊗^𝐋_{K_n} K_t)` (Tag 0GZJ), and the
last tower is constant with value `M_t` because `M` is quasi-coherent, so `M_t = 0` for every `t`.

This file carries out that argument, with its first equality — the vanishing of the derived limit
of the tower `n ↦ M_n ⊗^𝐋_R K_t` when `RΓ(M) = 0` — taken as the hypothesis `hT2` of the reduction
`Koszul.isZero_of_qc_of_isZero_derivedGlobalSections_of_baseTower`; everything else is proved:
Tag 0GZJ is `Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance_of_strict`, the
constancy of the second tower is `Koszul.isIso_liftedPowSectionTower_map_zero`, a constant tower
with zero derived limit has zero value
(`CategoryTheory.Pretriangulated.IsDerivedLimit.isZero_obj_zero_of_isZero`), and the derived
sections of `ℬ` jointly detect zero objects
(`SheafOfModules.DifferentialGradedModule.quasiIso_of_forall_isIso_derivedSections_map`).

## Main definitions

* `Koszul.liftedPowBaseTensorTower`: the tower `n ↦ M_n ⊗^𝐋_R K_t` of Tag 0GZJ attached to a right
  differential graded `ℬ`-module.

## Main results

* `Koszul.isZero_sectionClass_of_isZero_liftedPowSectionTower_obj_zero`: if the zeroth term
  `M_0 ⊗^𝐋_{K_t} K_t` of the tower vanishes, so do the sections of `𝓜` over the stage `t - 1`.
* `Chaotic.isZero_derivedClass_of_forall_isZero_sectionClass`, in the namespace
  `SheafOfModules.DifferentialGradedModule`, says that a module over a sheaf of differential
  graded algebras on a chaotic site whose sections are all zero in the derived categories of the
  section algebras is zero in `D(ℬ, d)`.
* `Koszul.isZero_of_qc_of_isZero_derivedGlobalSections_of_baseTower`: **the reduction of the
  last paragraph of the proof of Proposition 0GZK to the vanishing of `R lim (M_n ⊗^𝐋_R K_t)`.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Pretriangulated

universe u

namespace SheafOfModules.DifferentialGradedModule.Chaotic

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [SmallCategory C] {Λ : Type u} [CommRing Λ]
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.PresheafOfModules.constRingSheaf (C := C) Λ))

/-- **A module whose sections are all zero in the derived categories of the section algebras is
zero in `D(A, d)`.** Its zero endomorphism is inverted by every derived sections functor, hence is
a quasi-isomorphism, hence becomes invertible in `D(A, d)`. -/
theorem isZero_derivedClass_of_forall_isZero_sectionClass (M : DifferentialGradedModule.{u, u, u} A)
    (h : ∀ U : Cᵒᵖ, IsZero (sectionClass M U)) : IsZero (derivedClass A M) := by
  have hq : QuasiIso (0 : M ⟶ M).toHomologicalComplex :=
    quasiIso_of_forall_isIso_derivedSections_map A 0 fun U =>
      _root_.DifferentialGradedModule.isIso_of_isZero_endo
        ((h U).of_iso (derivedSectionsIsoSectionClass A U M)) _
  have hW : quasiIsomorphisms.{u, u, u} A ((HomotopyCategory.quotient A).map (0 : M ⟶ M)) :=
    (quasiIsomorphisms_quotient_map_iff 0).2 hq
  have hiso : IsIso ((toDerivedCategory.{u, u, u} A).map
      ((HomotopyCategory.quotient A).map (0 : M ⟶ M))) :=
    Localization.inverts _ (quasiIsomorphisms.{u, u, u} A) _ hW
  refine _root_.DifferentialGradedModule.isZero_of_isIso_zero ?_ hiso
  rw [Functor.map_zero, Functor.map_zero]

end SheafOfModules.DifferentialGradedModule.Chaotic

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule Bimodule

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

attribute [local instance] SheafOfModules.GradedAlgebra.sectionsGOne
  SheafOfModules.GradedAlgebra.sectionsGMul SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra Stacks.SheafOfModules.botWEqualsLocallyBijective

open Stacks Stacks.ChaoticSite

/-- **The tower `n ↦ M_n ⊗^𝐋_R K_t` of Tag 0GZJ** attached to a right differential graded
`ℬ`-module `𝓜`, with `M_n` the sections of `𝓜` over the stage carrying `K_{t+n}`. -/
abbrev liftedPowBaseTensorTower {t : ℕ} (ht : 1 ≤ t)
    (𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f)) :
    ℕᵒᵖ ⥤ derivedCategory' (degreeZero R R) :=
  (powBaseDegreeZeroDerivedTensorTower f t ht
    (liftedPowSectionBimoduleSystem f ht 𝓜).toBimoduleSystem.obj
    (fun n => (liftedPowSectionBimoduleSystem f ht 𝓜).trans (Nat.le_succ n))).tower

/-- The derived category of `R` placed in degree zero has countable products: it is equivalent
to the derived category of `R`-modules. -/
theorem hasProductsOfShape_derivedCategory'_degreeZero :
    HasProductsOfShape ℕ (derivedCategory' (degreeZero R R)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  exact Adjunction.hasLimitsOfShape_of_equivalence
    (degreeZeroDerivedEquivalence (R := R) (S := R) (A := R)).functor

/-- **If the zeroth term `M_0 ⊗^𝐋_{K_t} K_t` of the tower vanishes, so do the sections of `𝓜`
over the stage `t - 1`.** The zeroth term is computed by the plain tensor product, which is `M_0`
itself, and `M_0` is the module of sections over the stage `t - 1` read over `K_t`. -/
theorem isZero_sectionClass_of_isZero_liftedPowSectionTower_obj_zero {t : ℕ} (ht : 1 ≤ t)
    (𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f))
    (h : IsZero ((liftedPowSectionTower f ht 𝓜).obj (op 0))) :
    IsZero (SheafOfModules.DifferentialGradedModule.Chaotic.sectionClass 𝓜
      (liftedPowStage t 0)) := by
  let ι : (powAlgebra f (t + 0)).Hom (powAlgebra f (t + 0)) :=
    powTransition f ht (Nat.le_add_right t 0)
  have hι : ∀ c, ι.toAlgebraHom c = c := fun c =>
    AlgHom.congr_fun (powTransition_self_toAlgebraHom f ht) c
  have hX₀ := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal
    (flip (liftedPowSectionModule f ht 𝓜 0)) _ (leftOrthogonal_restrictedRegularOpp ι hι)
  have h1 : IsZero ((quasiIsomorphisms' (degreeZero R R)).Q.obj
      ((toHomotopyCategory (degreeZero R R)).obj
        (restrictScalars (baseHom (powAlgebra f (t + 0))) (liftedPowSectionModule f ht 𝓜 0)))) :=
    (h.of_iso (derivedTensorPlainIso (flip (liftedPowSectionModule f ht 𝓜 0))
      (restrictedRegularOpp ι) hX₀).symm).of_iso
      ((quasiIsomorphisms' (degreeZero R R)).Q.mapIso ((toHomotopyCategory (degreeZero R R)).mapIso
        (flipRestrictedRegularSelfIso ι hι (liftedPowSectionModule f ht 𝓜 0)))).symm
  have h2 := (isZero_q_obj_iff _).1 h1
  rw [quasiIsoZero_restrictScalars_iff] at h2
  have h3 := (quasiIsoZero_restrictBase_iff (ULift.{u} ℤ) _).2 h2
  have h4 := (quasiIsoZero_iff_of_iso (restrictBaseCounitIso (ULift.{u} ℤ) _ _)).1 h3
  rw [quasiIsoZero_restrictScalars_iff] at h4
  exact (isZero_q_obj_iff _).2 h4

variable {f}

open SheafOfModules.DifferentialGradedModule.Chaotic in
/-- **The reduction of the last paragraph of the proof of Proposition 0GZK.** Let `M` be an object
of `QC(ℬ, d)` with `RΓ(M) = 0`. If for every right differential graded `ℬ`-module `𝓜` with
`RΓ(𝓜) = 0` the tower `n ↦ M_n ⊗^𝐋_R K_t` of Tag 0GZJ has zero derived limit — the equalities
`0 = (R lim M_n) ⊗^𝐋_R K_t = R lim (M_n ⊗^𝐋_R K_t)` of the source — then `M = 0`.

Represent `M` by a module `𝓜`, which satisfies the quasi-coherence condition. For `t = m + 1`,
Tag 0GZJ identifies the derived limit of the tower `n ↦ M_n ⊗^𝐋_{K_{t+n}} K_t` with that of
`n ↦ M_n ⊗^𝐋_R K_t`, which is zero; the first tower is constant by quasi-coherence
(`Koszul.isIso_liftedPowSectionTower_map_zero`), so its value `M_0 ⊗^𝐋_{K_t} K_t` is zero, and that
is the module of sections of `𝓜` over the stage `m`. The derived sections detect zero objects. -/
theorem isZero_of_qc_of_isZero_derivedGlobalSections_of_baseTower
    (hT2 : ∀ {t : ℕ} (ht : 1 ≤ t)
      (𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f)),
      IsZero ((derivedGlobalSections R (liftedPowSheafAlgebra f)).obj
        ((SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u} _).obj
          ((SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient _).obj 𝓜))) →
      ∀ [HasProduct fun n : ℕ => (liftedPowBaseTensorTower f ht 𝓜).obj (op n)]
        (K' : derivedCategory' (degreeZero R R)),
        IsDerivedLimit (liftedPowBaseTensorTower f ht 𝓜) K' → IsZero K')
    {M : SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u}
      (liftedPowSheafAlgebra.{u} f)}
    (hM : SheafOfModules.DifferentialGradedModule.Chaotic.QC _ M)
    (h : IsZero ((derivedGlobalSections R (liftedPowSheafAlgebra f)).obj M)) : IsZero M := by
  obtain ⟨𝓜, h𝓜⟩ := SheafOfModules.DifferentialGradedModule.Chaotic.exists_module_eq _ M
  have hQC := hM 𝓜 h𝓜
  subst h𝓜
  have := hasProductsOfShape_derivedCategory'_degreeZero (R := R)
  refine isZero_derivedClass_of_forall_isZero_sectionClass _ 𝓜 fun U => ?_
  obtain ⟨⟨m⟩⟩ := U
  have ht : 1 ≤ m + 1 := Nat.le_add_left 1 m
  obtain ⟨K, hK⟩ := exists_isDerivedLimit (liftedPowSectionTower f ht 𝓜)
  obtain ⟨K', hK'⟩ := exists_isDerivedLimit (liftedPowBaseTensorTower f ht 𝓜)
  obtain ⟨e⟩ := nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance_of_strict f ht
    (liftedPowSectionBimoduleSystem f ht 𝓜) K K' hK hK'
  have hK0 : IsZero K := (hT2 ht 𝓜 h K' hK').of_iso e
  have hT0 := hK.isZero_obj_zero_of_isZero hK0 (isIso_liftedPowSectionTower_map_zero (ht := ht) hQC)
  exact isZero_sectionClass_of_isZero_liftedPowSectionTower_obj_zero f ht 𝓜 hT0

end Koszul

end
