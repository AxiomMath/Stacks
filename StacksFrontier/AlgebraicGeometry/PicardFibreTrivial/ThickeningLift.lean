module

public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDegreeBound
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Algebraization
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# Lifting sections from the first to a higher infinitesimal quotient

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent ideal sheaf generated, on every affine open, by
the restrictions of finitely many global functions `a₁, …, a_r`, and let `ℱ` be a
quasi-coherent `𝒪_X`-module. Write `ℱ_n = ℱ / ℐ ⁿ ℱ`. This file proves that the restriction
map `H⁰(X, ℱ_k) ⟶ H⁰(X, ℱ_1)` is surjective as soon as

* `H¹(X, ℱ_1) = 0`,
* `H²` vanishes on the subobjects of `ℱ_k ^{⊕ r}`, and
* the `a_i` act by zero on `ℱ_1` and every element of `(a₁, …, a_r) ^ k` acts by zero on
  `ℱ_k`.

This is the step "the transition maps of the tower `H⁰(X_n, ℒ_n)` are surjective" of the proof
of [Stacks, Tag 0E24], done in one go for the whole tower up to `k` by a Nakayama argument on
`H¹(X, ℱ_k)` instead of one graded piece at a time.

## The argument

Let `𝒩` be the kernel of `ℱ_k ⟶ ℱ_1`. Multiplication by the `a_i` gives a map
`Φ : ℱ_k ^{⊕ r} ⟶ ℱ_k` which lands in `𝒩` and is onto `𝒩`: over an affine open a section of
`𝒩` lifts to a section of `ℱ` lying in `ℐ ℱ`, which is a combination of the `a_i`. Its kernel
is a subobject of `ℱ_k ^{⊕ r}`, so its `H²` vanishes and `H¹(Φ)` is surjective onto `H¹(𝒩)`.
Since `H¹(ℱ_1) = 0`, the long exact sequence makes `H¹(𝒩) ⟶ H¹(ℱ_k)` surjective, and composing,
every class of `H¹(ℱ_k)` is `∑ a_i x_i`: the module `M = H¹(ℱ_k)` satisfies `M = 𝔞 M` for
`𝔞 = (a₁, …, a_r)`. Hence `M = 𝔞 ^ k M = 0`, because `𝔞 ^ k` acts by zero on `ℱ_k` and global
functions act on cohomology through their action on the module
(`AlgebraicGeometry.rightDerived_moduleGlobalSections_linear`). Then `H¹(𝒩)`, a quotient of
`M ^{⊕ r}`, vanishes too, and the long exact sequence gives the surjectivity in degree zero.

## Main results

* `Stacks.PicardFibreTrivial.surjective_rightDerived_zero_map_idealPowerQuotientDrop`: the
  surjectivity of `H⁰(X, ℱ_k) ⟶ H⁰(X, ℱ_1)`.

## References

* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Algebraization Stacks.Cohomology.FormalFunctions

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.PicardFibreTrivial

variable {X : Scheme.{u}}

/-- `H ᵖ(X, -)`, in the spelling of the theorem on formal functions. -/
abbrev coh (X : Scheme.{u}) (p : ℕ) : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p

/-- **A global function acts on cohomology through its action on the module.** -/
theorem rightDerived_map_globalSmul (a : Γ(X, ⊤)) (M : X.Modules) (p : ℕ)
    (x : ↥((coh X p).obj M)) : ((coh X p).map (globalSmul a M)).hom x = a • x := by
  have h : (coh X p).map (globalSmul a M) = a • 𝟙 _ := by
    rw [globalSmul_eq_smul_id, CategoryTheory.Functor.map_smul]
    exact congrArg (a • ·) (CategoryTheory.Functor.map_id _ M)
  rw [h]
  rfl

/-- An element of `(v₁, …, v_r) • M` is a combination `∑ vᵢ • cᵢ`. -/
theorem exists_eq_sum_smul_of_mem_span_smul_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {r : ℕ} (v : Fin r → R) {x : M}
    (hx : x ∈ Ideal.span (Set.range v) • (⊤ : Submodule R M)) :
    ∃ c : Fin r → M, x = ∑ i, v i • c i := by
  refine Submodule.smul_induction_on hx (fun b hb m _ => ?_) fun x y hx hy => ?_
  · obtain ⟨d, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hb
    refine ⟨fun i => d i • m, ?_⟩
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
  · obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]⟩

/-- **An element of the image of a biproduct under an additive functor is the sum of its
components.** -/
theorem map_biproduct_total_apply {C : Type*} [Category C] [Preadditive C] {R : Type*} [Ring R]
    (G : C ⥤ ModuleCat.{u} R) [G.Additive] {r : ℕ} (Y : Fin r → C) [HasBiproduct Y]
    (z : G.obj (⨁ Y)) :
    z = ∑ i, (G.map (biproduct.ι Y i)).hom ((G.map (biproduct.π Y i)).hom z) := by
  have h := congrArg (fun φ => (G.map φ).hom z) (biproduct.total (f := Y))
  simp only [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply] using h.symm

/-- An element of a zero module is zero. -/
theorem eq_zero_of_isZero {R : Type*} [Ring R] {M : ModuleCat.{u} R} (h : IsZero M) (x : M) :
    x = 0 :=
  (ModuleCat.isZero_iff_subsingleton.1 h).elim x 0

/-- Sections of a composite. -/
theorem comp_app_apply {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens)
    (x : Γ(M, U)) : (φ ≫ ψ).app U x = ψ.app U (φ.app U x) :=
  rfl

variable (I : X.IdealSheafData) (F : X.Modules)

/-- The projection `ℱ ⟶ ℱ / ℐ ⁿ ℱ`. -/
abbrev quotπ (n : ℕ) : F ⟶ idealPowerQuotient I n F :=
  cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι

/-- Lowering the exponent `ℱ / ℐ ᵐ ℱ ⟶ ℱ / ℐ ⁿ ℱ` is an epimorphism. -/
instance epi_idealPowerQuotientDrop {m n : ℕ} (h : n ≤ m) :
    Epi (idealPowerQuotientDrop I h F) :=
  epi_of_epi_fac (idealPowerQuotientDrop_π I h F)

/-- The sheaf of modules underlying `ℐ ⁿ ℱ` is quasi-coherent. -/
private theorem isQuasicoherent_toSheafOfModules_idealPowerMultiple (n : ℕ) [F.IsQuasicoherent] :
    (idealPowerMultiple I n F).toSheafOfModules.IsQuasicoherent := by
  rw [Stacks.AlgebraicGeometry.IdealPowerComparison.algebraization_idealPowerMultiple_eq]
  exact Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple I n F

/-- **A section of `ℱ / ℐ ᵏ ℱ` over an affine open dying in `ℱ / ℐ ℱ` is a combination of the
generators of `ℐ`.** -/
theorem exists_eq_sum_smul_of_drop_eq_zero [F.IsQuasicoherent] {r : ℕ} (a : Fin r → Γ(X, ⊤))
    (hgen : ∀ U : X.affineOpens,
      I.ideal U ≤ Ideal.span (Set.range fun i => restrictTop (a i) U.1))
    {k : ℕ} (hk : 1 ≤ k) (U : X.affineOpens) (t : Γ(idealPowerQuotient I k F, U.1))
    (ht : (idealPowerQuotientDrop I hk F).app U.1 t = 0) :
    ∃ c : Fin r → Γ(idealPowerQuotient I k F, U.1), t = ∑ i, restrictTop (a i) U.1 • c i := by
  have := isQuasicoherent_toSheafOfModules_idealPowerMultiple I F k
  obtain ⟨s, rfl⟩ : ∃ s : Γ(F, U.1), (quotπ I F k).app U.1 s = t :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X (quotπ I F k) U.1 U.2 t
  have h1 : (quotπ I F 1).app U.1 s = 0 := by
    rw [show quotπ I F 1 = quotπ I F k ≫ idealPowerQuotientDrop I hk F from
      (idealPowerQuotientDrop_π I hk F).symm]
    exact ht
  obtain ⟨x, hx⟩ := exists_app_eq_of_shortExact _ (idealPowerQuotientShortComplex_shortExact I 1 F)
    U.1 s h1
  have hmem : s ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I 1 F).toSubmodule.obj
      (op U.1) := by
    rw [← Stacks.AlgebraicGeometry.IdealPowerComparison.algebraization_idealPowerMultiple_eq, ← hx]
    exact x.2
  rw [Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple, pow_one] at hmem
  obtain ⟨c, rfl⟩ :=
    exists_eq_sum_smul_of_mem_span_smul_top _ (Submodule.smul_mono_left (hgen U) hmem)
  refine ⟨fun i => (quotπ I F k).app U.1 (c i), ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (quotπ I F k).app_smul _ _

/-- **`H⁰(X, ℱ / ℐ ᵏ ℱ) ⟶ H⁰(X, ℱ / ℐ ℱ)` is surjective**, for `ℐ` generated on affine opens
by global functions `a₁, …, a_r` which kill `ℱ / ℐ ℱ` and whose ideal kills `ℱ / ℐ ᵏ ℱ` in its
`k`-th power, as soon as `H¹(X, ℱ / ℐ ℱ) = 0` and `H²` vanishes on the subobjects of
`(ℱ / ℐ ᵏ ℱ) ^{⊕ r}`. -/
theorem surjective_rightDerived_zero_map_idealPowerQuotientDrop [F.IsQuasicoherent]
    {r : ℕ} (a : Fin r → Γ(X, ⊤))
    (hgen : ∀ U : X.affineOpens,
      I.ideal U ≤ Ideal.span (Set.range fun i => restrictTop (a i) U.1))
    (hkill₁ : ∀ i, globalSmul (a i) (idealPowerQuotient I 1 F) = 0)
    {k : ℕ} (hk : 1 ≤ k)
    (hkill : ∀ x ∈ Ideal.span (Set.range a) ^ k, globalSmul x (idealPowerQuotient I k F) = 0)
    (h2 : ∀ (K : X.Modules) (ι : K ⟶ ⨁ fun _ : Fin r => idealPowerQuotient I k F), Mono ι →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 2).obj K))
    (h1 : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
      (idealPowerQuotient I 1 F))) :
    Function.Surjective
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
        (idealPowerQuotientDrop I hk F)).hom := by
  classical
  set Qk := idealPowerQuotient I k F
  set Q1 := idealPowerQuotient I 1 F
  set d := idealPowerQuotientDrop I hk F
  set E := cohomologyDeltaFunctor X
  have : (coh X 1).Additive := E.additive 1
  have := isQuasicoherent_toSheafOfModules_idealPowerMultiple I F k
  have := isQuasicoherent_toSheafOfModules_idealPowerMultiple I F 1
  -- The short exact sequence `0 ⟶ 𝒩 ⟶ ℱ_k ⟶ ℱ_1 ⟶ 0`.
  let S₁ := ShortComplex.mk (kernel.ι d) d (kernel.condition d)
  have hS₁ : S₁.ShortExact := { exact := ShortComplex.exact_kernel d }
  -- Multiplication by the generators.
  let Φ : (⨁ fun _ : Fin r => Qk) ⟶ Qk := biproduct.desc fun i => globalSmul (a i) Qk
  have hΦd : Φ ≫ d = 0 := by
    refine biproduct.hom_ext' _ _ fun i => ?_
    rw [biproduct.ι_desc_assoc, comp_zero, ← comp_globalSmul, hkill₁, comp_zero]
  let Φ' : (⨁ fun _ : Fin r => Qk) ⟶ kernel d := kernel.lift d Φ hΦd
  have hΦ' : Φ' ≫ kernel.ι d = Φ := kernel.lift_ι d Φ hΦd
  -- `Φ'` is onto `𝒩`, checked on the sections over affine opens.
  have hΦepi : Epi Φ' := by
    refine AlgebraicGeometry.epi_of_forall_exists_surjective_app_affineOpen Φ' fun x => ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    refine ⟨V, hV, hxV, fun t => ?_⟩
    have ht : d.app V ((kernel.ι d).app V t) = 0 := by
      rw [← comp_app_apply, kernel.condition]
      rfl
    obtain ⟨c, hc⟩ := exists_eq_sum_smul_of_drop_eq_zero I F a hgen hk ⟨V, hV⟩ _ ht
    refine ⟨∑ i, (biproduct.ι (fun _ : Fin r => Qk) i).app V (c i), ?_⟩
    refine Stacks.AlgebraicGeometry.QcohLimits.injective_app_kernel_ι d V ?_
    rw [← comp_app_apply, hΦ', hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← comp_app_apply, biproduct.ι_desc, globalSmul_app]
  -- The short exact sequence `0 ⟶ 𝒦 ⟶ ℱ_k ^{⊕ r} ⟶ 𝒩 ⟶ 0`.
  let S₂ := ShortComplex.mk (kernel.ι Φ') Φ' (kernel.condition Φ')
  have hS₂ : S₂.ShortExact := { exact := ShortComplex.exact_kernel Φ' }
  -- `H¹(Φ')` is onto `H¹(𝒩)`, because `H²(𝒦) = 0`.
  have hsurj₂ : Function.Surjective ((coh X 1).map Φ').hom := by
    intro w
    have hK := h2 (kernel Φ') (kernel.ι Φ') inferInstance
    exact (ShortComplex.moduleCat_exact_iff _).1 (E.exact_δ₁ hS₂ 1) w
      (eq_zero_of_isZero hK _)
  -- Every class of `H¹(ℱ_k)` is an `𝔞`-combination.
  set J := Ideal.span (Set.range a)
  have hM : ∀ x : (coh X 1).obj Qk, x ∈ J • (⊤ : Submodule Γ(X, ⊤) ((coh X 1).obj Qk)) := by
    intro x
    have hx0 : ((coh X 1).map d).hom x = 0 := eq_zero_of_isZero h1 _
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1 (E.exact_map hS₁ 1) x hx0
    obtain ⟨z, rfl⟩ := hsurj₂ w
    have hxz : x = ((coh X 1).map Φ).hom z := by
      rw [← hw, ← hΦ', CategoryTheory.Functor.map_comp]
      rfl
    rw [hxz, map_biproduct_total_apply (coh X 1) _ z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← CategoryTheory.Functor.map_comp,
      biproduct.ι_desc, rightDerived_map_globalSmul]
    exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) trivial
  -- Hence `H¹(ℱ_k) = 𝔞 ᵏ H¹(ℱ_k) = 0`.
  have hJk : ∀ x : (coh X 1).obj Qk, x = 0 := by
    intro x
    have htop : ∀ n : ℕ, (⊤ : Submodule Γ(X, ⊤) ((coh X 1).obj Qk)) ≤ J ^ n • ⊤ := by
      intro n
      induction n with
      | zero => rw [pow_zero, Submodule.one_smul]
      | succ n ih =>
        rw [pow_succ', Submodule.mul_smul]
        exact fun y _ => Submodule.smul_mono le_rfl ih (hM y)
    have hbot : J ^ k • (⊤ : Submodule Γ(X, ⊤) ((coh X 1).obj Qk)) = ⊥ := by
      rw [eq_bot_iff, Submodule.smul_le]
      intro c hc y _
      rw [Submodule.mem_bot, ← rightDerived_map_globalSmul, hkill c hc,
        CategoryTheory.Functor.map_zero]
      rfl
    have hx := htop k (Submodule.mem_top (x := x))
    rw [hbot] at hx
    exact (Submodule.mem_bot _).1 hx
  -- Then `H¹(𝒩)`, a quotient of `H¹(ℱ_k) ^{⊕ r}`, vanishes.
  have hN : ∀ w : (coh X 1).obj (kernel d), w = 0 := by
    intro w
    obtain ⟨z, rfl⟩ := hsurj₂ w
    rw [map_biproduct_total_apply (coh X 1) _ z,
      Finset.sum_eq_zero fun i _ => by rw [hJk (((coh X 1).map (biproduct.π _ i)).hom z), map_zero],
      map_zero]
  intro y
  exact (ShortComplex.moduleCat_exact_iff _).1 (E.exact_δ₁ hS₁ 0) y (hN _)

end Stacks.PicardFibreTrivial

end
