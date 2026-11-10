module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.Functions

/-!
# Ideal-power torsion modules

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` an `R`-module. The module `M` is
*`I`-power torsion* when every `m ∈ M` is annihilated by some positive power of `I`, and
*`f`-power torsion* for `f ∈ R` when every `m ∈ M` is annihilated by some positive power of `f`.

For a finitely generated `I` this condition is detected by the support: `M` is `I`-power torsion
exactly when `Supp(M) ⊆ V(I)`, so the class of `I`-power torsion modules depends only on the
closed subset `V(I) ⊆ Spec(R)`. Two further finiteness consequences are recorded here: the
vanishing of the `I`-torsion submodule `M[I]` propagates to every power `M[Iⁿ]` and is equivalent
to injectivity of `M → ∏ᵢ M_{fᵢ}` for a finite generating family of `I`; and the quotient of a
module by its `I`-primary component has no nonzero `I`-torsion, whence `I`-power torsion modules
are closed under extensions.

## Main definitions

* `IsIPowerTorsion`: every element is annihilated by some positive power of an ideal.
* `IsElementPowerTorsion`: every element is annihilated by some positive power of an element.

## Main results

* `isIPowerTorsion_iff_support_subset`: an `R`-module is `I`-power torsion if and only if its
  support is contained in `V(I)`.
* `torsionBySet_eq_bot_iff_powers_eq_bot_iff_bigLambda_injective`: the three equivalent
  characterizations of the vanishing of `M[I]` for a finitely generated `I`.
* `torsionBySet_quotient_primaryComponent_eq_bot_and_isIPowerTorsion_of_exact`: the quotient by
  the `I`-primary component is `I`-torsion free, and `I`-power torsion is stable under extensions.

## References

* [The Stacks Project, Tag 05E6](https://stacks.math.columbia.edu/tag/05E6)
* [The Stacks Project, Tag 05EA](https://stacks.math.columbia.edu/tag/05EA)
* [The Stacks Project, Tag 05EB](https://stacks.math.columbia.edu/tag/05EB)
* [The Stacks Project, Tag 0953](https://stacks.math.columbia.edu/tag/0953)
-/

@[expose] public section

open scoped Pointwise

universe u v v₁ v₂ v₃

/-- An `R`-module `M` is *`I`-power torsion* if for every `m ∈ M` there exists an
integer `n > 0` such that `Iⁿ m = 0`, i.e. `a • m = 0` for every `a ∈ Iⁿ`. -/
@[stacks 05E6]
def IsIPowerTorsion (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M]
    [Module R M] (I : Ideal R) : Prop :=
  ∀ m : M, ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n, a • m = 0

/-- An `R`-module `M` is *`f`-power torsion* if every element is annihilated by some strictly
positive power of `f`. -/
@[stacks 05E6]
def IsElementPowerTorsion (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M]
    [Module R M] (f : R) : Prop :=
  ∀ m : M, ∃ n : ℕ, 0 < n ∧ f ^ n • m = 0

/-- If `m` is killed by some power of `I`, it is killed by some positive power of `I`. -/
private theorem exists_pos_pow_smul_eq_zero {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {I : Ideal R} {m : M} {n : ℕ} (h : ∀ a ∈ I ^ n, a • m = 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n, a • m = 0 :=
  ⟨n + 1, n.succ_pos, fun _ ha => h _ (Ideal.pow_le_pow_right n.le_succ ha)⟩

/-- If `M` is `I`-power torsion, then `Supp(M) ⊆ V(I)`. -/
theorem support_subset_zeroLocus_of_isIPowerTorsion {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {I : Ideal R} (htor : IsIPowerTorsion R M I) :
    Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  intro p hp f hf
  rw [Module.mem_support_iff, ← not_subsingleton_iff_nontrivial,
    LocalizedModule.subsingleton_iff] at hp
  push Not at hp
  obtain ⟨m, hm⟩ := hp
  obtain ⟨n, -, hkill⟩ := htor m
  by_contra hfp
  exact hm (f ^ n) (p.asIdeal.primeCompl.pow_mem hfp n) (hkill _ (Ideal.pow_mem_pow hf n))

/-- If `I` is finitely generated and `Supp(M) ⊆ V(I)`, then `M` is `I`-power torsion. -/
theorem isIPowerTorsion_of_support_subset {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {I : Ideal R}
    (hI : I.FG) (hsupp : Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    IsIPowerTorsion R M I := by
  intro m
  have : Module.Finite R (R ∙ m) := Module.Finite.span_singleton R m
  have hsub := (Module.support_subset_of_injective (R ∙ m).subtype
    (R ∙ m).subtype_injective).trans hsupp
  rw [Module.support_eq_zeroLocus,
    show Module.annihilator R (R ∙ m) = (R ∙ m).annihilator from
      Submodule.toSubMulAction_inj.mp rfl,
    PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsub
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hsub hI
  exact exists_pos_pow_smul_eq_zero fun a ha =>
    (Submodule.mem_annihilator_span_singleton _ _).mp (hn ha)

/-- Let `R` be a commutative ring and let `I ⊆ R` be a finitely generated ideal. Then for every
`R`-module `M`, `M` is `I`-power torsion if and only if `Supp(M) ⊆ V(I)`. -/
@[stacks 0953]
theorem isIPowerTorsion_iff_support_subset
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) :
    IsIPowerTorsion R M I ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) :=
  ⟨support_subset_zeroLocus_of_isIPowerTorsion, isIPowerTorsion_of_support_subset hI⟩

/-- For a finitely generated ideal `I`, `M` is `I`-power torsion if and only if `M_p = 0` for
every prime `p` not containing `I`. -/
theorem isIPowerTorsion_iff_localization_eq_zero
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) :
    IsIPowerTorsion R M I ↔
      ∀ p : PrimeSpectrum R, ¬ I ≤ p.asIdeal →
        ¬ Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := by
  rw [isIPowerTorsion_iff_support_subset R M I hI]
  refine ⟨fun hsub p hp hnt => hp (hsub (Module.mem_support_iff.mpr hnt)), fun h p hp => ?_⟩
  by_contra hle
  exact h p hle (Module.mem_support_iff.mp hp)

/-- If no nonzero element of `M` is annihilated by `I`, the same holds for every positive power
of `I`. -/
theorem torsionBySet_pow_eq_bot
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (h : Submodule.torsionBySet R M (I : Set R) = ⊥) :
    ∀ n : ℕ, 1 ≤ n → Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) = ⊥ := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [← le_bot_iff, ← h]
    intro m hm
    rw [Submodule.mem_torsionBySet_iff] at hm ⊢
    rintro ⟨a, ha⟩
    have ham : a • m ∈ Submodule.torsionBySet R M ((I ^ (1 + k) : Ideal R) : Set R) := by
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨b, hb⟩
      rw [smul_smul]
      refine hm ⟨b * a, ?_⟩
      rw [show 1 + (k + 1) = 1 + k + 1 by omega, pow_succ]
      exact Ideal.mul_mem_mul hb ha
    rwa [ih (by omega)] at ham

/-- For a finite generating family of `I`, the vanishing of `M[I]` is the statement that no
nonzero element of `M` is annihilated by all the generators. -/
theorem torsionBySet_eq_bot_iff_bigPhi_injective
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (t : ℕ) (f : Fin t → R) (hf : I = Ideal.span (Set.range f)) :
    Submodule.torsionBySet R M (I : Set R) = ⊥ ↔
      Function.Injective (bigPhi (M := M) t f) := by
  rw [bigPhi_injective_iff_commonAnnihilator, hf, ← Submodule.torsionBySet_eq_torsionBySet_span,
    Submodule.eq_bot_iff]
  simp [Submodule.mem_torsionBySet_iff]

/-- For a finitely generated ideal `I`, the following are equivalent: no
nonzero element of `M` is annihilated by `I`; the same holds for every positive power of `I`;
and, for every finite generating family of `I`, the canonical map from `M` to the direct sum of
the localizations at those generators is injective. -/
@[stacks 05EA]
theorem torsionBySet_eq_bot_iff_powers_eq_bot_iff_bigLambda_injective
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] (hI : I.FG) :
    (Submodule.torsionBySet R M (I : Set R) = ⊥ ↔
      ∀ n : ℕ, 1 ≤ n → Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) = ⊥) ∧
    ((∀ n : ℕ, 1 ≤ n → Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) = ⊥) ↔
      ∀ (t : ℕ) (f : Fin t → R), I = Ideal.span (Set.range f) →
        Function.Injective (bigLambda (M := M) t f)) := by
  obtain ⟨S, hS⟩ := hI
  obtain ⟨t, f, hf⟩ := S.finite_toSet.fin_embedding
  have hgen : I = Ideal.span (Set.range f) := by rw [hf, hS]
  have hpowers : Submodule.torsionBySet R M (I : Set R) = ⊥ ↔
      ∀ n : ℕ, 1 ≤ n → Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) = ⊥ :=
    ⟨torsionBySet_pow_eq_bot I, fun h ↦ by simpa using h 1 le_rfl⟩
  refine ⟨hpowers, ?_⟩
  rw [← hpowers]
  exact ⟨fun h t' f' hf' ↦ (bigLambda_injective_iff_bigPhi_injective t' f').mpr
    ((torsionBySet_eq_bot_iff_bigPhi_injective I t' f' hf').mp h),
    fun h ↦ (torsionBySet_eq_bot_iff_bigPhi_injective I t f hgen).mpr
      ((bigLambda_injective_iff_bigPhi_injective t f).mp (h t f hgen))⟩

/-- An element lies in the `I`-primary component iff some power of `I` kills it. -/
private theorem mem_primaryComponent_iff_forall_smul_eq_zero
    {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M] {x : M} :
    x ∈ Ideal.primaryComponent M I ↔ ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
  simp [Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff]

/-- If `I` is finitely generated and every `a ∈ I` moves `x` into the `I`-primary component,
then `x` already lies in the `I`-primary component. -/
theorem mem_primaryComponent_of_smul_mem
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {M : Type v} [AddCommGroup M] [Module R M] (x : M)
    (hx : ∀ a ∈ I, a • x ∈ Ideal.primaryComponent M I) :
    x ∈ Ideal.primaryComponent M I := by
  have hrad : I ≤ (Ideal.torsionOf R M x).radical := by
    intro a ha
    obtain ⟨n, hn⟩ := mem_primaryComponent_iff_forall_smul_eq_zero.mp (hx a ha)
    refine Ideal.mem_radical_iff.mpr ⟨n + 1, ?_⟩
    rw [Ideal.mem_torsionOf_iff, pow_succ, mul_smul]
    exact hn _ (Ideal.pow_mem_pow ha n)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hI
  exact mem_primaryComponent_iff_forall_smul_eq_zero.mpr ⟨n, fun a ha ↦
    (Ideal.mem_torsionOf_iff x a).mp (hn ha)⟩

/-- For a finitely generated ideal `I`, the quotient of `M` by its `I`-primary component has no
nonzero elements annihilated by `I`. -/
theorem torsionBySet_quotient_primaryComponent_eq_bot
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Submodule.torsionBySet R (M ⧸ (Ideal.primaryComponent M I)) (I : Set R) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := (Ideal.primaryComponent M I).mkQ_surjective q
  exact (Submodule.Quotient.mk_eq_zero _).mpr <| mem_primaryComponent_of_smul_mem I hI x
    fun a ha ↦ (Submodule.Quotient.mk_eq_zero _).mp <|
      (Submodule.mem_torsionBySet_iff _ _).mp hq ⟨a, ha⟩

/-- For a finitely generated ideal `I`, the quotient of any module by its
`I`-primary component has no nonzero elements annihilated by `I`. Moreover, in a short exact
sequence, if the first and third modules are `I`-power torsion, then so is the middle module. -/
@[stacks 05EB]
theorem torsionBySet_quotient_primaryComponent_eq_bot_and_isIPowerTorsion_of_exact
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    (∀ (M : Type v) [AddCommGroup M] [Module R M],
      Submodule.torsionBySet R (M ⧸ (Ideal.primaryComponent M I)) (I : Set R) = ⊥) ∧
    ∀ (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
      [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
      [AddCommGroup M₃] [Module R M₃]
      (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
        IsIPowerTorsion R M₁ I →
        IsIPowerTorsion R M₃ I →
        IsIPowerTorsion R M₂ I := by
  refine ⟨torsionBySet_quotient_primaryComponent_eq_bot I hI, ?_⟩
  intro M₁ M₂ M₃ _ _ _ _ _ _ f g hf hfg hg hM₁ hM₃ m
  obtain ⟨n, hn, hgn⟩ := hM₃ (g m)
  have hmq : (Ideal.primaryComponent M₂ I).mkQ m ∈
      Submodule.torsionBySet R (M₂ ⧸ Ideal.primaryComponent M₂ I)
        ((I ^ n : Ideal R) : Set R) := by
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨a, ha⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨y, hy_eq⟩ : a • m ∈ f.range := by
      rw [← hfg.linearMap_ker_eq, LinearMap.mem_ker, map_smul]
      exact hgn a ha
    change a • m ∈ Ideal.primaryComponent M₂ I
    rw [← hy_eq]
    obtain ⟨k, hk, hy⟩ := hM₁ y
    refine mem_primaryComponent_iff_forall_smul_eq_zero.mpr ⟨k, fun b hb ↦ ?_⟩
    rw [← map_smul]
    simpa using congrArg f (hy b hb)
  rw [torsionBySet_pow_eq_bot I (torsionBySet_quotient_primaryComponent_eq_bot I hI M₂) n hn] at hmq
  obtain ⟨k, hk⟩ := mem_primaryComponent_iff_forall_smul_eq_zero.mp
    ((Submodule.Quotient.mk_eq_zero _).mp hmq)
  exact exists_pos_pow_smul_eq_zero hk

end
