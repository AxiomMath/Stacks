module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModules
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineToolbox
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic

/-!
# Stabilization of the images of the sections supported in `T`

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf, `T ⊆ V(ℐ)` a subset stable
under specialization and `(ℱ_n)` an object of `Coh(X, ℐ)` satisfying the depth condition of
Stacks, Tag 0EJE on its completed stalks at the points of `T`. Let `ℱ_k → ℱ'_k` be the depth-one
quotient of `ℱ_k` along `T` (Stacks, Tag 0DX3) and `𝒦_k` its kernel, the subsheaf of sections of
`ℱ_k` supported in `T`.

This file proves that the images of the `𝒦_k` in a fixed term `ℱ_n` stabilize, uniformly on `X`:
there are an integer `c` and, for every `n`, a level `m₀ ≥ n` such that for every `k ≥ m₀` and
every point `y`, the stalk at `y` of the image of `𝒦_k → ℱ_n` is that of `𝒦_{m₀} → ℱ_n`, and it is
annihilated by `ℐ_y^c`. On an affine open this is the essential constancy theorem
`Stacks.LocalCohomology.exists_sectionsWithSupportIn_map_eq` (the case `s = 0` of Stacks,
Tag 0EIE) applied to the modules of sections, whose local hypothesis at the points of `T` is
`Stacks.Algebraization.localTorsionProZeroAt_sectionsTower`; the sections of `𝒦_k` over an affine
open are the sections of `ℱ_k` with support in `T`
(`AlgebraicGeometry.ker_sectionsLinearMap_eq_sectionsWithSupportIn`), and stalks are
localizations of sections. A Noetherian scheme is covered by finitely many affine opens, which
makes the constants uniform.

## Main definitions

* `Stacks.Algebraization.supportedImageMap` — the map `𝒦_k → ℱ_n` for `n ≤ k`.

## Main results

* `Stacks.Algebraization.exists_stalk_range_supportedImageMap_eq` — the uniform stabilization.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
open Stacks.ModuleSkyscraper Stacks.ModuleStalkSpecialization Stacks.LocalCohomology

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (F : Stacks.Coherent.CoherentAdicSystems I) (T : Set X) (hT : StableUnderSpecialization T)

/-- Every term of an object of `Coh(X, ℐ)` is coherent. -/
instance isCoherent_coherentAdicSystems_obj (n : ℕᵒᵖ) : (F.obj.obj n).IsCoherent :=
  F.property.1 n.unop

/-- The map from the subsheaf of sections of `ℱ_k` supported in `T` to `ℱ_n`, for `n ≤ k`. -/
def supportedImageMap {n k : ℕ} (h : n ≤ k) :
    kernel (toDepthOneQuotient X T hT (F.obj.obj (op k))) ⟶ F.obj.obj (op n) :=
  kernel.ι (toDepthOneQuotient X T hT (F.obj.obj (op k))) ≫ F.obj.map (homOfLE h).op

/-- The adic inverse system underlying an object of `Coh(X, ℐ)`. -/
abbrev toAdicInverseSystem : AdicInverseSystem.{u} where
  X := X
  I := I
  system := F.obj
  isQuasicoherent n := F.property.isQuasicoherent n.unop
  quotientIso n := F.property.quotientIso n
  quotientIso_hom_comp n := F.property.cokernel_π_comp_quotientIso n

/-- The map on sections over `U` of `supportedImageMap`, valued in the tower of sections. -/
def supportedSectionsMap (U : X.Opens) {n k : ℕ} (h : n ≤ k) :
    Γ(kernel (toDepthOneQuotient X T hT (F.obj.obj (op k))), U) →ₗ[Γ(X, U)]
      (sectionsTower F U).obj (op n) :=
  Scheme.Modules.sectionsLinearMap (supportedImageMap F T hT h) U

section Affine

variable (U : X.affineOpens)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Over an affine open `U`, the transition map `Γ(U, ℱ_{n+1}) → Γ(U, ℱ_n)` is surjective. -/
theorem towerMap_sectionsTower_succ_surjective (n : ℕ) :
    Function.Surjective (towerMap (sectionsTower F U.1) (Nat.le_succ n)) := by
  obtain ⟨e, he⟩ := AdicInverseSystem.sectionsQuotientEquiv (toAdicInverseSystem F) U n
  intro x
  obtain ⟨z, rfl⟩ := e.surjective x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨z, (he z).symm⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Over an affine open `U`, the kernel of the transition map `Γ(U, ℱ_{n+1}) → Γ(U, ℱ_n)` is
`ℐ(U)^{n+1} Γ(U, ℱ_{n+1})`. -/
theorem ker_towerMap_sectionsTower_succ (n : ℕ) :
    LinearMap.ker (towerMap (sectionsTower F U.1) (Nat.le_succ n)) =
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U.1) ((sectionsTower F U.1).obj (op (n + 1)))) := by
  obtain ⟨e, he'⟩ : ∃ e : (Γ(F.obj.obj (op (n + 1)), U.1) ⧸
        (I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U.1) Γ(F.obj.obj (op (n + 1)), U.1))))
          ≃ₗ[Γ(X, U.1)] Γ(F.obj.obj (op n), U.1), ∀ x, e (Submodule.Quotient.mk x) =
          towerMap (sectionsTower F U.1) (Nat.le_succ n) x :=
    AdicInverseSystem.sectionsQuotientEquiv (toAdicInverseSystem F) U n
  apply le_antisymm
  · intro (z : Γ(F.obj.obj (op (n + 1)), U.1)) h0
    have h1 : e (Submodule.Quotient.mk z) = 0 := (he' z).trans h0
    rwa [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
  · intro (z : Γ(F.obj.obj (op (n + 1)), U.1)) hz
    have hz' : z ∈ (I.ideal U ^ (n + 1) •
        (⊤ : Submodule Γ(X, U.1) Γ(F.obj.obj (op (n + 1)), U.1))) := hz
    have h1 : e (Submodule.Quotient.mk z) = 0 := by
      rw [(Submodule.Quotient.mk_eq_zero _).mpr hz', map_zero]
    exact (he' z).symm.trans h1

/-- Over an affine open `U`, the module `Γ(U, ℱ_n)` is finite over `Γ(X, U)`. -/
instance (n : ℕ) : Module.Finite Γ(X, U.1) ((sectionsTower F U.1).obj (op n)) := by
  have : (F.obj.obj (op n)).IsQuasicoherent := F.property.isQuasicoherent n
  have : (F.obj.obj (op n)).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  exact Stacks.AlgebraicGeometry.CoherentFinite.finite_sections (F.obj.obj (op n)) U.2

/-- The sections over an affine open of the subsheaf supported in `T`, mapped to a lower term, are
the image of the sections with support in `T`. -/
theorem range_sectionsLinearMap_supportedImageMap {n k : ℕ} (h : n ≤ k) :
    LinearMap.range (supportedSectionsMap F T hT U.1 h) =
      (sectionsWithSupportIn Γ(X, U.1) (U.2.primesOf T)
        ((sectionsTower F U.1).obj (op k))).map (towerMap (sectionsTower F U.1) h) := by
  have : (F.obj.obj (op k)).IsQuasicoherent := F.property.isQuasicoherent k
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, U.1) := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have : PreservesFiniteLimits E := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hker := Stacks.Coherent.range_map_kernel_ι E (toDepthOneQuotient X T hT (F.obj.obj (op k)))
  have hφ := ker_sectionsLinearMap_eq_sectionsWithSupportIn T
    (toDepthOneQuotient X T hT (F.obj.obj (op k)))
    (depthOneQuotient_spec X T hT (F.obj.obj (op k))) U.2
  have hmem : ∀ w, w ∈ LinearMap.range (E.map (kernel.ι (toDepthOneQuotient X T hT
      (F.obj.obj (op k))))).hom ↔ w ∈ sectionsWithSupportIn Γ(X, U.1) (U.2.primesOf T)
        ((sectionsTower F U.1).obj (op k)) := fun w => by
    rw [hker]
    exact Submodule.ext_iff.mp hφ w
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, (hmem _).mp ⟨w, rfl⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv⟩ := (hmem w).mpr hw
    exact ⟨v, congrArg ((F.obj.map (homOfLE h).op).app U.1) hv⟩

/-- **Stabilization on an affine open**: the essential constancy theorem applied to the modules of
sections over `U`. -/
theorem exists_affine_stabilization (hTY : T ⊆ I.support)
    (h6 : ∀ y ∈ T, ∀ p : PrimeSpectrum (completedLocalRing I y),
      p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      0 < completedStalkDepth I F y p) :
    ∃ (Λ : ∀ n, Submodule Γ(X, U.1) ((sectionsTower F U.1).obj (op n))) (c : ℕ),
      (∀ n, ∀ a ∈ I.ideal U ^ c, ∀ x ∈ Λ n, a • x = 0) ∧
      ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m (h : n ≤ m), m₀ ≤ m →
        LinearMap.range (supportedSectionsMap F T hT U.1 h) = Λ n := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hTI : ∀ q ∈ U.2.primesOf T, I.ideal U ≤ q.asIdeal := by
    intro q hq a ha
    have hyU := U.2.fromSpec_mem q
    have hJ := (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support I _).mpr (hTY hq)
    have hga : (X.presheaf.germ U.1 _ hyU).hom a ∈ maximalIdeal (X.presheaf.stalk _) :=
      hJ (by rw [IdealSheafData.stalk_eq_map_germ I _ U hyU]; exact Ideal.mem_map_of_mem _ ha)
    have := comap_le_primeIdealOf U.2 hyU (maximalIdeal _) (Ideal.mem_comap.mpr hga)
    rwa [U.2.primeIdealOf_fromSpec _ (U.2.fromSpec_mem q)] at this
  have hloc : ∀ q ∈ U.2.primesOf T, LocalTorsionProZeroAt (I.ideal U) (sectionsTower F U.1) q := by
    intro q hq
    have := localTorsionProZeroAt_sectionsTower F U.2 (U.2.fromSpec_mem q) (hTY hq) (h6 _ hq)
    rwa [U.2.primeIdealOf_fromSpec _ (U.2.fromSpec_mem q)] at this
  obtain ⟨Λ, c, hann, hstab⟩ := exists_sectionsWithSupportIn_map_eq (I.ideal U)
    (sectionsTower F U.1) (towerMap_sectionsTower_succ_surjective F U)
    (ker_towerMap_sectionsTower_succ F U) (U.2.primesOf T)
    (U.2.stableUnderSpecialization_primesOf hT) hTI hloc
  refine ⟨Λ, c, hann, fun n => ?_⟩
  obtain ⟨m₀, hnm₀, hm₀⟩ := hstab n
  refine ⟨m₀, hnm₀, fun m h hm => ?_⟩
  rw [range_sectionsLinearMap_supportedImageMap, hm₀ m h hm]

end Affine

section Stalk

variable {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U)

include hU in
/-- **The stalk of the image of the supported subsheaf is the span of the germs of the image of
its sections.** -/
theorem range_stalk_supportedImageMap {n k : ℕ} (h : n ≤ k) :
    LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT h)).hom =
      germSpan F hy n (LinearMap.range (supportedSectionsMap F T hT U h)) := by
  have : (depthOneQuotient X T hT (F.obj.obj (op k))).IsCoherent :=
    (depthOneQuotient_spec X T hT (F.obj.obj (op k))).1
  have : (kernel (toDepthOneQuotient X T hT (F.obj.obj (op k)))).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel _
  have : (kernel (toDepthOneQuotient X T hT (F.obj.obj (op k)))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨s, c, hc, hcs⟩ := exists_germ_smul_eq_germ
      (kernel (toDepthOneQuotient X T hT (F.obj.obj (op k)))) hU hy w
    rw [mem_germSpan_iff F hU hy n]
    refine ⟨_, ⟨s, rfl⟩, c, hc, ?_⟩
    have hcs' : ((X.presheaf.germ U y hy).hom c • w :
        (modulesStalkFunctor X y).obj (kernel (toDepthOneQuotient X T hT (F.obj.obj (op k))))) =
        (kernel (toDepthOneQuotient X T hT (F.obj.obj (op k)))).presheaf.germ U y hy s := hcs
    rw [← map_smul, hcs', modulesStalkFunctor_map_germ]
    rfl
  · rw [germSpan, Submodule.span_le]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨(kernel (toDepthOneQuotient X T hT (F.obj.obj (op k)))).presheaf.germ U y hy s, ?_⟩
    rw [modulesStalkFunctor_map_germ]
    rfl

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The germ span of a submodule annihilated by `ℐ(U)^c` is annihilated by `ℐ_y^c`. -/
theorem smul_eq_zero_of_mem_germSpan {n c : ℕ}
    (W : Submodule Γ(X, U) ((sectionsTower F U).obj (op n)))
    (hW : ∀ a ∈ I.ideal ⟨U, hU⟩ ^ c, ∀ x ∈ W, a • x = 0)
    {v : (modulesStalkFunctor X y).obj (F.obj.obj (op n))} (hv : v ∈ germSpan F hy n W)
    {a : X.presheaf.stalk y} (ha : a ∈ IdealSheafData.stalk I y ^ c) : a • v = 0 := by
  obtain ⟨w, hw, c₀, hc₀, hc₀w⟩ := (mem_germSpan_iff F hU hy n W v).mp hv
  have hle : I.ideal ⟨U, hU⟩ ^ c ≤ (Ideal.torsionOf (X.presheaf.stalk y) _ v).comap
      (X.presheaf.germ U y hy).hom := by
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff]
    obtain ⟨u, hu⟩ := isUnit_germ_of_notMem hU hy hc₀
    have h0 : (X.presheaf.germ U y hy).hom b • (X.presheaf.germ U y hy).hom c₀ • v = 0 := by
      rw [hc₀w, ← sectionGerm_smul, hW b hb w hw]
      exact map_zero _
    rw [← hu, smul_comm] at h0
    exact u.isUnit.smul_eq_zero.mp h0
  have hJc : IdealSheafData.stalk I y ^ c ≤ Ideal.torsionOf (X.presheaf.stalk y) _ v := by
    refine (le_of_eq ?_).trans (Ideal.map_le_iff_le_comap.mpr hle)
    rw [Ideal.map_pow, ← IdealSheafData.stalk_eq_map_germ I y ⟨U, hU⟩ hy]
  exact (Ideal.mem_torsionOf_iff _ a).mp (hJc ha)

end Stalk

/-- **The uniform stabilization of the images of the supported subsheaves.** There are a
monotone `μ` with `n ≤ μ n` and an integer `c` such that at every point `y`, the stalk of the image
of `𝒦_m → ℱ_n` is the same for all `m ≥ μ n`, and is annihilated by `ℐ_y^c`. -/
theorem exists_stalk_range_supportedImageMap_eq (hTY : T ⊆ I.support)
    (h6 : ∀ y ∈ T, ∀ p : PrimeSpectrum (completedLocalRing I y),
      p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      0 < completedStalkDepth I F y p) :
    ∃ (μ : ℕ → ℕ) (hμ : ∀ n, n ≤ μ n) (c : ℕ), Monotone μ ∧
      (∀ n m (h : n ≤ m), μ n ≤ m → ∀ y : X,
        LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT h)).hom =
          LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT (hμ n))).hom) ∧
      (∀ n (y : X), ∀ a ∈ IdealSheafData.stalk I y ^ c,
        ∀ v ∈ LinearMap.range ((modulesStalkFunctor X y).map
          (supportedImageMap F T hT (hμ n))).hom, a • v = 0) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  have hcover : ∀ y : X, ∃ U ∈ s, y ∈ U.1 := fun y => by
    obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
    exact ⟨U, hU, hyU⟩
  choose Λ c hann hstab using fun U : X.affineOpens => exists_affine_stabilization F T hT U hTY h6
  choose m₀ hnm₀ hm₀ using hstab
  let m₁ : ℕ → ℕ := fun n => s.sup (fun U => m₀ U n) ⊔ n
  let μ : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup m₁
  have hm₁μ : ∀ n, m₁ n ≤ μ n := fun n => Finset.le_sup (f := m₁) (Finset.self_mem_range_succ n)
  have hμ : ∀ n, n ≤ μ n := fun n => le_sup_right.trans (hm₁μ n)
  have hμmono : Monotone μ := fun n n' h =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hm₀μ : ∀ U ∈ s, ∀ n, m₀ U n ≤ μ n := fun U hU n =>
    (le_sup_of_le_left (Finset.le_sup (f := fun U => m₀ U n) hU)).trans (hm₁μ n)
  refine ⟨μ, hμ, s.sup c, hμmono, fun n m h hm y => ?_, fun n y a ha v hv => ?_⟩
  · obtain ⟨U, hU, hyU⟩ := hcover y
    rw [range_stalk_supportedImageMap F T hT U.2 hyU h,
      range_stalk_supportedImageMap F T hT U.2 hyU (hμ n),
      hm₀ U n m h ((hm₀μ U hU n).trans hm), hm₀ U n (μ n) (hμ n) (hm₀μ U hU n)]
  · obtain ⟨U, hU, hyU⟩ := hcover y
    rw [range_stalk_supportedImageMap F T hT U.2 hyU (hμ n),
      hm₀ U n (μ n) (hμ n) (hm₀μ U hU n)] at hv
    exact smul_eq_zero_of_mem_germSpan F U.2 hyU (Λ U n) (hann U n) hv
      (Ideal.pow_le_pow_right (Finset.le_sup (f := c) hU) ha)

end Stacks.Algebraization

end
