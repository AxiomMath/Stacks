module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# Derived complete modules over a principal ideal

Let `f` be a nonzerodivisor in a commutative ring `A`. An `A`-module is derived complete with
respect to `(f)` exactly when it admits a short exact presentation by `f`-adically complete
modules on which multiplication by `f` is injective.

## Main definitions

* `PrincipalAdicPresentation.seriesToCompletion`: the `f`-adic series `∑ fᵏ zₖ`, as a linear map
  to the `f`-adic completion.
* `PrincipalAdicPresentation.completionLift`: the factorization of a surjection `F ↠ M` through
  the `f`-adic completion of `F`, available when `f` acts bijectively on the recurrence of `M`.

## Main results

* `isDerivedCompleteModule_iff_exists_shortExact_isAdicComplete`: derived complete modules for a
  principal ideal are characterised by short exact presentations with complete, `f`-torsion-free
  terms.

## Implementation notes

The source's sequence `0 ⟶ K ⟶ L ⟶ M ⟶ 0` is represented by a `ShortComplex.ShortExact` in
`ModuleCat A`; that a term has zero `f`-torsion is injectivity of `LinearMap.lsmul A _ f`. The
ring and all three modules lie in the same universe, so a free presentation and its completion
fit in the module category. The forward construction takes the `f`-adic completion `L` of a free
presentation `F ↠ M` and factors the presentation through it: a series `∑ fᵏ zₖ` is sent to the
value at `0` of the unique solution of the recurrence `aₙ - f · aₙ₊₁ = g zₙ` in `M`, which exists
because `M` is derived complete at `f`
(`DerivedCompleteRecurrence.isDerivedCompleteModule_iff_forall_bijective_recurrence`). The kernel
`K` of that factorisation is derived complete because the derived complete modules are closed
under kernels, and it is separated because it embeds in `L`, so Stacks 091T makes it adically
complete. The converse is closure under cokernels.

## References

* [The Stacks Project, Tag 09AT](https://stacks.math.columbia.edu/tag/09AT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u v

namespace PrincipalAdicPresentation

open DerivedCompleteRecurrence

attribute [local instance] KoszulCompletion.derivedCountableProducts

section Algebra

variable {A : Type*} [CommRing A] {F M : Type*} [AddCommGroup F] [Module A F]
  [AddCommGroup M] [Module A M]

/-- A linear map commutes with the recurrence operator `aₙ ↦ aₙ - f · aₙ₊₁`. -/
lemma recurrence_comp {N : Type*} [AddCommGroup N] [Module A N] (f : A)
    (g : F →ₗ[A] N) (z : ℕ → F) :
    recurrence f (g ∘ z) = g ∘ recurrence f z := by
  funext n
  simp [recurrence_apply, map_sub, map_smul]

/-- The recurrence operator fixes a sequence supported in degree `0`. -/
lemma recurrence_single (f : A) (m : M) :
    recurrence f (Pi.single 0 m : ℕ → M) = Pi.single 0 m := by
  funext n
  rw [recurrence_apply]
  rcases n with _ | n <;> simp

/-- Lying in `(f)ⁿ · M` is divisibility by `fⁿ`. -/
lemma mem_span_singleton_pow_smul_top_iff (f : A) (n : ℕ) (x : F) :
    x ∈ (Ideal.span {f}) ^ n • (⊤ : Submodule A F) ↔ ∃ y : F, f ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- Congruence modulo `(f)ⁿ · M` is divisibility of the difference by `fⁿ`. -/
lemma smodEq_span_singleton_pow_iff (f : A) (n : ℕ) (x y : F) :
    x ≡ y [SMOD (Ideal.span {f}) ^ n • (⊤ : Submodule A F)] ↔ ∃ z : F, f ^ n • z = x - y := by
  rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff]

/-- The partial sums `∑_{k < n} fᵏ zₖ` of a series, as an `f`-adic Cauchy sequence. -/
def partialSums (f : A) :
    (ℕ → F) →ₗ[A] AdicCompletion.AdicCauchySequence (Ideal.span {f}) F where
  toFun z := AdicCompletion.AdicCauchySequence.mk _ _
    (fun n => ∑ k ∈ Finset.range n, f ^ k • z k) (fun n => by
      rw [smodEq_span_singleton_pow_iff, Finset.sum_range_succ, sub_add_cancel_left]
      exact ⟨-z n, by simp⟩)
  map_add' z w := by
    apply AdicCompletion.AdicCauchySequence.ext
    intro n
    simp only [AdicCompletion.AdicCauchySequence.add_apply]
    simp [AdicCompletion.AdicCauchySequence.mk, Finset.sum_add_distrib]
  map_smul' r z := by
    apply AdicCompletion.AdicCauchySequence.ext
    intro n
    simp only [AdicCompletion.AdicCauchySequence.smul_apply, RingHom.id_apply]
    simp [AdicCompletion.AdicCauchySequence.mk, Finset.smul_sum, smul_comm r]

/-- The `n`-th partial sum of a series. -/
lemma partialSums_apply (f : A) (z : ℕ → F) (n : ℕ) :
    partialSums f z n = ∑ k ∈ Finset.range n, f ^ k • z k := rfl

/-- The `f`-adic series `∑ fᵏ zₖ`, as an element of the `f`-adic completion. -/
def seriesToCompletion (f : A) :
    (ℕ → F) →ₗ[A] AdicCompletion (Ideal.span {f}) F :=
  AdicCompletion.mk _ _ ∘ₗ partialSums f

/-- The `n`-th component of `∑ fᵏ zₖ` is the class of its `n`-th partial sum. -/
lemma seriesToCompletion_apply_val (f : A) (z : ℕ → F) (n : ℕ) :
    (seriesToCompletion f z).val n =
      Submodule.Quotient.mk (∑ k ∈ Finset.range n, f ^ k • z k) := rfl

/-- Every element of the `f`-adic completion is a series `∑ fᵏ zₖ`. -/
lemma seriesToCompletion_surjective (f : A) :
    Function.Surjective (seriesToCompletion (F := F) f) := by
  intro ξ
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective _ _ ξ
  have hx (n : ℕ) : ∃ d : F, f ^ n • d = x (n + 1) - x n := by
    rw [← smodEq_span_singleton_pow_iff]
    exact ((AdicCompletion.isAdicCauchy_iff _ _ _).1 x.property n).symm
  choose d hd using hx
  let z : ℕ → F := fun k => if k = 0 then x 1 else d k
  have hsum (n : ℕ) : ∑ k ∈ Finset.range (n + 1), f ^ k • z k = x (n + 1) := by
    induction n with
    | zero => simp [z]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [z, Nat.succ_ne_zero, ite_false, hd]
      abel
  refine ⟨z, AdicCompletion.ext fun n => ?_⟩
  rw [seriesToCompletion_apply_val, AdicCompletion.mk_apply_coe]
  rcases n with _ | n
  · apply (Submodule.Quotient.eq _).2
    simp
  · rw [hsum]
    rfl

/-- If multiplication by `f` is injective, so is multiplication by `fⁿ`. -/
lemma pow_smul_injective {f : A} (hF : Function.Injective (LinearMap.lsmul A F f))
    (n : ℕ) : Function.Injective (fun x : F => f ^ n • x) := by
  induction n with
  | zero => intro x y h; simpa using h
  | succ n ih =>
    intro x y h
    apply hF
    apply ih
    simpa [pow_succ, mul_smul] using h

/-- A series vanishing in the completion is the recurrence of a sequence vanishing at `0`. -/
lemma recurrence_exists_of_seriesToCompletion_eq_zero {f : A}
    (hF : Function.Injective (LinearMap.lsmul A F f)) {z : ℕ → F}
    (hz : seriesToCompletion f z = 0) :
    ∃ y : ℕ → F, y 0 = 0 ∧ z = recurrence f (-y) := by
  have hy (n : ℕ) : ∃ y : F, f ^ n • y = ∑ k ∈ Finset.range n, f ^ k • z k := by
    have := congrArg (fun ξ => ξ.val n) hz
    simp only [seriesToCompletion_apply_val, AdicCompletion.val_zero, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero] at this
    exact (mem_span_singleton_pow_smul_top_iff f n _).1 this
  choose y hy using hy
  refine ⟨y, by simpa using hy 0, funext fun n => ?_⟩
  rw [recurrence_apply]
  have h := hy (n + 1)
  rw [Finset.sum_range_succ, ← hy n, pow_succ, mul_smul, ← smul_add] at h
  have hinj := pow_smul_injective hF n h
  simp only [Pi.neg_apply, smul_neg]
  rw [hinj]
  abel

/-- Given `f` acting bijectively on the recurrence of `M`, the linear map sending a series
`∑ fᵏ zₖ` over `F` to the value at `0` of the solution of the recurrence with right side
`g ∘ z`. -/
def seriesLift {f : A} (hM : Function.Bijective (recurrence (M := M) f))
    (g : F →ₗ[A] M) : (ℕ → F) →ₗ[A] M :=
  LinearMap.proj 0 ∘ₗ (LinearEquiv.ofBijective _ hM).symm.toLinearMap ∘ₗ
    LinearMap.compLeft g ℕ

/-- The series lift is the value at `0` of the solution of the recurrence. -/
lemma seriesLift_apply {f : A} (hM : Function.Bijective (recurrence (M := M) f))
    (g : F →ₗ[A] M) (z : ℕ → F) :
    seriesLift hM g z = (LinearEquiv.ofBijective _ hM).symm (g ∘ z) 0 := rfl

/-- The series lift kills every series that already vanishes in the completion. -/
lemma ker_seriesToCompletion_le {f : A} (hF : Function.Injective (LinearMap.lsmul A F f))
    (hM : Function.Bijective (recurrence (M := M) f)) (g : F →ₗ[A] M) :
    LinearMap.ker (seriesToCompletion (F := F) f) ≤ LinearMap.ker (seriesLift hM g) := by
  intro z hz
  obtain ⟨y, hy0, rfl⟩ := recurrence_exists_of_seriesToCompletion_eq_zero hF hz
  rw [LinearMap.mem_ker, seriesLift_apply, ← recurrence_comp]
  have heq : (LinearEquiv.ofBijective _ hM).symm (recurrence f (g ∘ (-y))) = g ∘ (-y) :=
    (LinearEquiv.ofBijective _ hM).symm_apply_apply _
  rw [heq]
  simp [hy0]

/-- The factorization of `g : F → M` through the `f`-adic completion of `F`. -/
def completionLift {f : A}
    (hF : Function.Injective (LinearMap.lsmul A F f))
    (hM : Function.Bijective (recurrence (M := M) f)) (g : F →ₗ[A] M) :
    AdicCompletion (Ideal.span {f}) F →ₗ[A] M :=
  let q : ((ℕ → F) ⧸ LinearMap.ker (seriesToCompletion (F := F) f)) →ₗ[A] M :=
    (LinearMap.ker (seriesToCompletion (F := F) f)).liftQ (seriesLift hM g)
      (ker_seriesToCompletion_le hF hM g)
  let e : ((ℕ → F) ⧸ LinearMap.ker (seriesToCompletion (F := F) f)) ≃ₗ[A]
      AdicCompletion (Ideal.span {f}) F :=
    LinearMap.quotKerEquivOfSurjective (seriesToCompletion (F := F) f)
      (seriesToCompletion_surjective (F := F) f)
  q ∘ₗ e.symm.toLinearMap

/-- On a series, the factorization computes the series lift. -/
lemma completionLift_seriesToCompletion {f : A}
    (hF : Function.Injective (LinearMap.lsmul A F f))
    (hM : Function.Bijective (recurrence (M := M) f)) (g : F →ₗ[A] M) (z : ℕ → F) :
    completionLift hF hM g (seriesToCompletion (F := F) f z) = seriesLift hM g z := by
  simp only [completionLift, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The factorization through the completion is surjective whenever `g` is. -/
lemma completionLift_surjective {f : A}
    (hF : Function.Injective (LinearMap.lsmul A F f))
    (hM : Function.Bijective (recurrence (M := M) f)) {g : F →ₗ[A] M}
    (hg : Function.Surjective g) : Function.Surjective (completionLift hF hM g) := by
  intro m
  obtain ⟨x, rfl⟩ := hg m
  refine ⟨seriesToCompletion (F := F) f (Pi.single 0 x), ?_⟩
  rw [completionLift_seriesToCompletion, seriesLift_apply]
  have hc : (g ∘ (Pi.single 0 x : ℕ → F)) = Pi.single 0 (g x) := by
    funext n
    rcases n with _ | n <;> simp
  rw [hc, (LinearEquiv.ofBijective _ hM).symm_apply_eq.2 (recurrence_single f (g x)).symm]
  simp

/-- The source's torsion-freeness argument: `f` acts injectively on the `f`-adic completion of
an `f`-torsion-free module. -/
lemma adicCompletion_smul_injective {f : A}
    (hF : Function.Injective (LinearMap.lsmul A F f)) :
    Function.Injective (LinearMap.lsmul A (AdicCompletion (Ideal.span {f}) F) f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective _ _ ξ
  apply AdicCompletion.ext
  intro n
  have h := congrArg (fun η => η.val (n + 1)) hξ
  simp only [LinearMap.lsmul_apply, AdicCompletion.val_smul, Pi.smul_apply,
    AdicCompletion.mk_apply_coe, AdicCompletion.val_zero, Pi.zero_apply, Submodule.mkQ_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨y, hy⟩ := (mem_span_singleton_pow_smul_top_iff f (n + 1) _).1 h
  rw [pow_succ', mul_smul] at hy
  have hy' : f ^ n • y = x (n + 1) := hF hy
  have hc := (AdicCompletion.isAdicCauchy_iff _ _ _).1 x.property n
  rw [SModEq.sub_mem] at hc
  rw [AdicCompletion.mk_apply_coe, AdicCompletion.val_zero, Pi.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  have hmem : x (n + 1) ∈ (Ideal.span {f}) ^ n • (⊤ : Submodule A F) :=
    (mem_span_singleton_pow_smul_top_iff f n _).2 ⟨y, hy'⟩
  simpa using Submodule.add_mem _ hc hmem

end Algebra

/-- Multiplication by `f` acting injectively on `A` acts injectively on a free module. -/
lemma finsupp_smul_injective {A : Type*} [CommRing A] {f : A}
    (hf : Function.Injective (LinearMap.lsmul A A f)) (X : Type*) :
    Function.Injective (LinearMap.lsmul A (X →₀ A) f) := by
  intro x y hxy
  ext m
  apply hf
  simpa using congrArg (fun z : X →₀ A => z m) hxy

/-- A module embedding into an `I`-adically Hausdorff module is separated for the `I`-adic
filtration. -/
lemma iInf_pow_smul_top_eq_bot_of_injective {A : Type*} [CommRing A] (I : Ideal A)
    {N P : Type*} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    [IsHausdorff I P] (g : N →ₗ[A] P) (hg : Function.Injective g) :
    ⨅ n : ℕ, I ^ n • (⊤ : Submodule A N) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  apply hg
  rw [map_zero, ← Submodule.mem_bot A, ← (inferInstance : IsHausdorff I P).iInf_pow_smul]
  rw [Submodule.mem_iInf] at hx ⊢
  intro n
  have hmap := Submodule.mem_map_of_mem (f := g) (hx n)
  rw [Submodule.map_smul''] at hmap
  exact Submodule.smul_mono le_rfl le_top hmap

/-- An `f`-adically complete module is derived complete at `(f)`. -/
private lemma completeModules_of_isAdicComplete {A : Type u} [CommRing A] (f : A)
    (K : ModuleCat.{u} A) (hK : IsAdicComplete (Ideal.span {f}) K) :
    completeModules.{u, u} (Ideal.span {f}) K :=
  ((isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
    A (Ideal.span {f}) (Submodule.fg_span_singleton f) K).mp hK).1

private lemma isDerivedCompleteModule_of_exists_shortExact_isAdicComplete
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{u} A)
    (h : ∃ (K L : ModuleCat.{u} A) (i : K ⟶ L) (p : L ⟶ M) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧
        IsAdicComplete (Ideal.span {f}) K ∧
        IsAdicComplete (Ideal.span {f}) L ∧
        Function.Injective (LinearMap.lsmul A K f) ∧
        Function.Injective (LinearMap.lsmul A L f)) :
    IsDerivedCompleteModule (Ideal.span {f}) M := by
  obtain ⟨K, L, i, p, w, hS, hK, hL, -, -⟩ := h
  have : Epi p := hS.epi_g
  exact ObjectProperty.prop_of_isColimit_cokernelCofork
    (P := completeModules.{u, u} (Ideal.span {f})) hS.gIsCokernel
    (completeModules_of_isAdicComplete f K hK) (completeModules_of_isAdicComplete f L hL)

/-- **Stacks 09AT.** Let `f` be a nonzerodivisor in a commutative ring `A`. An `A`-module `M` is
derived complete with respect to `(f)` if and only if it occurs as the cokernel in a short exact
sequence `0 ⟶ K ⟶ L ⟶ M ⟶ 0`, where `K` and `L` are `f`-adically complete and multiplication by
`f` is injective on both. -/
@[stacks 09AT]
theorem isDerivedCompleteModule_iff_exists_shortExact_isAdicComplete
    (A : Type u) [CommRing A] (f : A)
    (hf : Function.Injective (LinearMap.lsmul A A f)) (M : ModuleCat.{u} A) :
    letI : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
      moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedCompleteModule (Ideal.span {f}) M ↔
      ∃ (K L : ModuleCat.{u} A) (i : K ⟶ L) (p : L ⟶ M) (w : i ≫ p = 0),
        (ShortComplex.mk i p w).ShortExact ∧
          IsAdicComplete (Ideal.span {f}) K ∧
          IsAdicComplete (Ideal.span {f}) L ∧
          Function.Injective (LinearMap.lsmul A K f) ∧
          Function.Injective (LinearMap.lsmul A L f) := by
  refine ⟨fun hM => ?_, isDerivedCompleteModule_of_exists_shortExact_isAdicComplete A f M⟩
  have hfg : (Ideal.span {f}).FG := Submodule.fg_span_singleton f
  have hMb : Function.Bijective (recurrence (M := M) f) :=
    (isDerivedCompleteModule_iff_forall_bijective_recurrence (Ideal.span {f}) M).mp hM f
      (Ideal.mem_span_singleton_self f)
  let F := M →₀ A
  have hF : Function.Injective (LinearMap.lsmul A F f) := finsupp_smul_injective hf M
  let g : F →ₗ[A] M := Finsupp.linearCombination A id
  have hg : Function.Surjective g := fun m => ⟨Finsupp.single m 1, by
    simp only [g]
    exact (Finsupp.linearCombination_single A (v := (id : M → M)) 1 m).trans (one_smul A m)⟩
  let φ := completionLift hF hMb g
  let L : ModuleCat.{u} A := ModuleCat.of A (AdicCompletion (Ideal.span {f}) F)
  let K : ModuleCat.{u} A := ModuleCat.of A (LinearMap.ker φ)
  let i : K ⟶ L := ModuleCat.ofHom (LinearMap.ker φ).subtype
  let p : L ⟶ M := ModuleCat.ofHom φ
  have w : i ≫ p = 0 := by
    ext x
    exact x.2
  have hS : (ShortComplex.mk i p w).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact LinearMap.exact_subtype_ker_map φ
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 (completionLift_surjective hF hMb hg)
  have hLc : IsAdicComplete (Ideal.span {f}) L :=
    AdicCompletion.isAdicComplete (M := F) hfg
  have hLi : Function.Injective (LinearMap.lsmul A L f) :=
    adicCompletion_smul_injective (F := F) hF
  have hKi : Function.Injective (LinearMap.lsmul A K f) := fun _ _ hxy =>
    Subtype.val_injective (hLi (congrArg Subtype.val hxy))
  have hKd' := ObjectProperty.prop_of_isLimit_kernelFork
    (P := completeModules.{u, u} (Ideal.span {f})) hS.fIsKernel
    (completeModules_of_isAdicComplete f L hLc) hM
  have hKd : completeModules.{u, u} (Ideal.span {f}) K := by
    simpa only [KernelFork.ofι, Fork.ofι_pt] using hKd'
  have hKs : ⨅ n : ℕ, (Ideal.span {f}) ^ n • (⊤ : Submodule A K) = ⊥ :=
    have : IsHausdorff (Ideal.span {f}) L := hLc.toIsHausdorff
    iInf_pow_smul_top_eq_bot_of_injective (Ideal.span {f}) (LinearMap.ker φ).subtype
      Subtype.val_injective
  have hKc : IsAdicComplete (Ideal.span {f}) K :=
    (isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
      A (Ideal.span {f}) hfg K).mpr ⟨hKd, hKs⟩
  exact ⟨K, L, i, p, w, hS, hKc, hLc, hKi, hLi⟩

end PrincipalAdicPresentation

end

end
