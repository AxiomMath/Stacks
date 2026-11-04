module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedCounit

/-!
# Stacks 0AEU fails without finite presentation of `Z ⟶ X`

Stacks 0AEU (spaces-pushouts, "Lemma 0AEU") says: let `f : Y ⟶ X` be a morphism of algebraic
spaces and `Z ⟶ X` a closed immersion such that `f^{-1}Z ⟶ Z` is an isomorphism and `f` is flat
along `f^{-1}Z`; then `Lf^*Rf_*Q ⟶ Q` is an isomorphism for every `Q ∈ D_QCoh(𝒪_Y)` supported on
`|f^{-1}Z|`. The source's proof uses that the ideal of `Z` is finitely generated (it passes from
being supported on `V(IB)` to being `IB`-power torsion), and the statement is false without that
hypothesis. This file proves the ring-theoretic counterexample; this is why
`AlgebraicGeometry.Space.SupportedDerivedCounitIsIso` carries the hypothesis
`IsFinitePresentation B S hS Z.ι`.

## The counterexample

Let `K = ℚ((t^ℚ))` be the field of Hahn series over `ℚ` with exponents in `ℚ`, `v` its valuation
and `A = {v ≥ 0}` its valuation ring. Its maximal ideal `I = {v > 0}` satisfies `I = I²` (so it is
not finitely generated), and every element of `I` has a power in `gA`, where `g = t¹`. Let
`B = A ⊕ Iε` be the trivial square-zero extension of `A` by the `A`-module `I`, and `M = B / gB`.

* `B` is flat over `A`: it is torsion free and `A` is a Bézout domain (Stacks 0539).
* `A / I ⟶ B / IB` is bijective, since `IB = I ⊕ I²ε = I ⊕ Iε`.
* `Supp M ⊆ V(IB)`: every element of `IB` has a power in `gB`.
* The action map `M ⊗_A B ⟶ M` is not injective: `[1] ⊗ gε - [gε] ⊗ 1` is a nonzero element
  of its kernel, detected by the pairing `(a + xε, b + yε) ↦ a • y mod gI`, with values in
  `I / gI`, in which `g` is not zero.

Geometrically, `X = Spec A`, `Z = V(I) ⊆ X` (a closed immersion, not of finite presentation),
`Y = Spec B`, `f : Y ⟶ X` the flat morphism, so that `f^{-1}Z = Spec(B/IB) ⟶ Z` is an isomorphism,
and `Q = M~` placed in degree `0`, a quasi-coherent module (finitely presented, even) whose support
lies in `|f^{-1}Z|`. Since `f` is affine, `Rf_*Q` is the quasi-coherent module of the `A`-module
`M`, and since `f` is flat, `Lf^*Rf_*Q` is the module of `M ⊗_A B`; the counit
`Lf^*Rf_*Q ⟶ Q` is the module of the action map `M ⊗_A B ⟶ M`, which is not an isomorphism. So
the conclusion of Stacks 0AEU fails for `f`, `Z` and `Q`, and all its hypotheses other than the
finite presentation of `Z ⟶ X` hold.

With `IB`-power torsion (`IsIPowerTorsion`) in place of the support condition, the action map is
bijective for every flat `A ⟶ B` that is bijective modulo `I`
(`IPowerTorsion.bijective_actionMap_of_isIPowerTorsion`, Stacks 05E9): the counterexample `M` is
supported on `V(IB)` but is not `IB`-power torsion
(`IPowerTorsion.SupportCounterexample.not_isIPowerTorsion`).

## Main results

* `IPowerTorsion.exists_not_bijective_actionMap_of_support_subset`: there are a flat ring map
  `A ⟶ B`, an ideal `I ⊆ A` with `A / I ⟶ B / IB` bijective, and a finite `B`-module `M` with
  `Supp M ⊆ V(IB)` for which the action map `M ⊗_A B ⟶ M` is not bijective.
* `IPowerTorsion.SupportCounterexample.not_bijective_actionMap`: the general mechanism, for a
  domain `A`, an ideal `I ∌ 1` and `0 ≠ g ∈ I`.

## Implementation notes

Only the ring-level statement is proved. The space-level negation of
`AlgebraicGeometry.Space.SupportedDerivedCounitIsIso` with the finite presentation hypothesis
removed would need, in addition, the identification of the derived counit of the small étale ringed
topoi of `Spec B ⟶ Spec A` at a quasi-coherent module with the action map of global sections, which
the library does not have.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
-/

@[expose] public noncomputable section

open TensorProduct

namespace IPowerTorsion.SupportCounterexample

/-! ### The valuation ring of a `ℚ`-valued valuation -/

section Valuation

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℚ))

/-- The valuation ring `{x ∈ K : 0 ≤ v x}` of a `ℚ`-valued additive valuation. -/
def integers : ValuationSubring K where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, v.map_mul] at ha hb ⊢
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [v.map_neg] using ha
  mem_or_inv_mem' x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hx)
    change 0 ≤ v x ∨ 0 ≤ v x⁻¹
    rw [v.map_inv, ← hq, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    rcases le_total 0 q with h | h
    · exact Or.inl (WithTop.coe_nonneg.2 h)
    · exact Or.inr (WithTop.coe_nonneg.2 (neg_nonneg.2 h))

/-- An element `x` lies in `integers v` exactly when `0 ≤ v x`. -/
theorem mem_integers {x : K} : x ∈ integers v ↔ 0 ≤ v x := Iff.rfl

/-- The maximal ideal `{a : 0 < v a}` of `integers v`. -/
def maxIdeal : Ideal (integers v) where
  carrier := {a | 0 < v (a : K)}
  add_mem' {a b} ha hb := lt_of_lt_of_le (lt_min ha hb) (v.map_add (a : K) b)
  zero_mem' := by simp
  smul_mem' c a ha := by
    change 0 < v ((c : K) * a)
    rw [v.map_mul]
    exact Right.add_pos_of_nonneg_of_pos c.2 ha

/-- `a` lies in `maxIdeal v` exactly when `0 < v a`. -/
theorem mem_maxIdeal {a : integers v} : a ∈ maxIdeal v ↔ 0 < v (a : K) := Iff.rfl

/-- `1` does not lie in `maxIdeal v`. -/
theorem one_notMem_maxIdeal : (1 : integers v) ∉ maxIdeal v := by
  simp [mem_maxIdeal]

variable {v}

/-- A nonzero element of the maximal ideal has a positive rational valuation. -/
private theorem exists_pos_val_eq_of_mem_maxIdeal {a : integers v} (ha : a ∈ maxIdeal v)
    (ha0 : a ≠ 0) : ∃ q : ℚ, 0 < q ∧ v (a : K) = q := by
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 (by simpa using ha0 : (a : K) ≠ 0))
  rw [mem_maxIdeal, ← hq, WithTop.coe_pos] at ha
  exact ⟨q, ha, hq.symm⟩

/-- If `v (g) = 1`, every element of the maximal ideal has a power in `g • integers v`. -/
theorem exists_pow_eq_mul_of_mem_maxIdeal {g a : integers v} (hg : v (g : K) = 1)
    (ha : a ∈ maxIdeal v) : ∃ (n : ℕ) (c : integers v), a ^ n = g * c := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨1, 0, by simp⟩
  have hgK : (g : K) ≠ 0 := v.ne_top_iff.1 (by simp [hg])
  obtain ⟨q, hq0, hq⟩ := exists_pos_val_eq_of_mem_maxIdeal ha ha0
  obtain ⟨n, hn⟩ := Archimedean.arch (1 : ℚ) hq0
  have hc : 0 ≤ v ((a : K) ^ n * (g : K)⁻¹) := by
    rw [v.map_mul, v.map_inv, v.map_pow, hg, hq, ← WithTop.coe_nsmul,
      ← WithTop.coe_one, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
      WithTop.coe_nonneg]
    linarith
  refine ⟨n, ⟨_, hc⟩, ?_⟩
  ext
  push_cast
  field_simp

variable (hv : ∀ q : ℚ, ∃ x : K, v x = q)
include hv

/-- When every rational number is a value of `v`, the maximal ideal is idempotent: every element
is a product of two elements of it. -/
theorem exists_mul_eq_of_mem_maxIdeal {x : integers v} (hx : x ∈ maxIdeal v) :
    ∃ c ∈ maxIdeal v, ∃ y ∈ maxIdeal v, c * y = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, zero_mem _, 0, zero_mem _, mul_zero 0⟩
  obtain ⟨q, hq0, hq⟩ := exists_pos_val_eq_of_mem_maxIdeal hx hx0
  obtain ⟨c, hc⟩ := hv (q / 2)
  have hc0 : c ≠ 0 := v.ne_top_iff.1 (by simp [hc])
  have hcpos : 0 < v c := by
    rw [hc, WithTop.coe_pos]
    linarith
  have hy : v ((x : K) * c⁻¹) = ((q / 2 : ℚ) : WithTop ℚ) := by
    rw [v.map_mul, v.map_inv, hc, hq, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add]
    congr 1
    ring
  have hypos : 0 < v ((x : K) * c⁻¹) := by
    rw [hy, WithTop.coe_pos]
    linarith
  refine ⟨⟨c, hcpos.le⟩, hcpos, ⟨(x : K) * c⁻¹, hypos.le⟩, hypos, ?_⟩
  ext
  push_cast
  field_simp

/-- When every rational number is a value of `v`, the maximal ideal contains an element of
valuation `1`. -/
theorem exists_mem_maxIdeal_eq_one : ∃ g ∈ maxIdeal v, v (g : K) = 1 := by
  obtain ⟨g, hg⟩ := hv 1
  have h0 : (0 : WithTop ℚ) ≤ v g := by
    rw [hg]
    exact_mod_cast zero_le_one
  refine ⟨⟨g, h0⟩, ?_, hg⟩
  rw [mem_maxIdeal, hg]
  exact_mod_cast zero_lt_one

end Valuation

/-! ### The square-zero extension `A ⊕ Iε` -/

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Over a domain `A`, the `A`-module `A ⊕ Iε` is torsion free. -/
theorem torsion_trivSqZeroExt_eq_bot [IsDomain A] :
    Submodule.torsion A (TrivSqZeroExt A I) = ⊥ := by
  refine eq_bot_iff.2 fun p hp ↦ ?_
  obtain ⟨⟨a, ha⟩, hap⟩ := (Submodule.mem_torsion_iff p).1 hp
  have h1 := congrArg TrivSqZeroExt.fst hap
  have h2 := congrArg (fun q : TrivSqZeroExt A I ↦ ((q.snd : I) : A)) hap
  simp only [Submonoid.mk_smul, TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul,
    TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, Submodule.coe_smul, ZeroMemClass.coe_zero,
    mul_eq_zero, nonZeroDivisors.ne_zero ha, false_or] at h1 h2
  rw [Submodule.mem_bot]
  ext
  · exact h1
  · simpa using h2

/-- Over a Bézout domain `A`, the `A`-module `A ⊕ Iε` is flat. -/
theorem flat_trivSqZeroExt [IsDomain A] [IsBezout A] : Module.Flat A (TrivSqZeroExt A I) :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (torsion_trivSqZeroExt_eq_bot I)

variable {I}

/-- If every element of `I` is a product of two elements of `I`, then `A / I ⟶ B / IB` is
bijective for `B = A ⊕ Iε`. -/
theorem bijective_quotientMap (hsq : ∀ x ∈ I, ∃ c ∈ I, ∃ y ∈ I, c * y = x) :
    Function.Bijective (Ideal.quotientMap (I.map (algebraMap A (TrivSqZeroExt A I)))
      (algebraMap A (TrivSqZeroExt A I)) Ideal.le_comap_map) := by
  refine ⟨Ideal.quotientMap_injective' fun a ha ↦ ?_, fun b ↦ ?_⟩
  · have h := Ideal.mem_map_of_mem (TrivSqZeroExt.fstHom A A I : TrivSqZeroExt A I →+* A)
      (Ideal.mem_comap.1 ha)
    rw [Ideal.map_map] at h
    have hid : (TrivSqZeroExt.fstHom A A I : TrivSqZeroExt A I →+* A).comp
        (algebraMap A (TrivSqZeroExt A I)) = RingHom.id A := by
      ext c
      simp
    rwa [hid, Ideal.map_id] at h
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨Ideal.Quotient.mk I b.fst, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    obtain ⟨c, hc, y, hy, hcy⟩ := hsq _ b.snd.2
    have : algebraMap A _ b.fst - b =
        -(algebraMap A (TrivSqZeroExt A I) c * TrivSqZeroExt.inr ⟨y, hy⟩) := by
      ext
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr, hcy]
    rw [this]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc))

variable (I) in
/-- The module `M = B / gB` over `B = A ⊕ Iε`. -/
abbrev quot (g : A) : Type _ :=
  TrivSqZeroExt A I ⧸ Ideal.span {algebraMap A (TrivSqZeroExt A I) g}

/-- If every element of `I` has a power in `gA`, then the support of the `B`-module `B / gB`,
where `B = A ⊕ Iε`, lies in `V(IB)`. -/
theorem support_subset_zeroLocus (g : A) (hrad : ∀ a ∈ I, ∃ (n : ℕ) (c : A), a ^ n = g * c) :
    Module.support (TrivSqZeroExt A I) (quot I g) ⊆
      PrimeSpectrum.zeroLocus
        (I.map (algebraMap A (TrivSqZeroExt A I)) : Set (TrivSqZeroExt A I)) := by
  intro p hp
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.1 hp
  have hle : I.map (algebraMap A (TrivSqZeroExt A I)) ≤
      (Ideal.span {algebraMap A (TrivSqZeroExt A I) g}).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨n, c, hc⟩ := hrad a ha
    refine ⟨n, ?_⟩
    rw [← map_pow, hc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rw [PrimeSpectrum.mem_zeroLocus]
  intro b hb
  obtain ⟨n, hn⟩ := hle hb
  refine p.isPrime.mem_of_pow_mem n (hm ?_)
  rw [Submodule.mem_annihilator_span_singleton]
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hn

variable (I) in
/-- The `A`-module `I / gI`. -/
abbrev modG (g : A) : Type _ := I ⧸ LinearMap.range (LinearMap.lsmul A I g)

variable (I) in
/-- The `A`-bilinear pairing `(a + xε, b + yε) ↦ a • y mod gI` on `A ⊕ Iε`. -/
def pairing (g : A) : TrivSqZeroExt A I →ₗ[A] TrivSqZeroExt A I →ₗ[A] modG I g :=
  ((LinearMap.lsmul A I).compl₁₂ (TrivSqZeroExt.fstHom A A I).toLinearMap
    (TrivSqZeroExt.sndHom A I)).compr₂ (Submodule.mkQ _)

/-- `pairing I g u w` is the class of `u.fst • w.snd` in `I / gI`. -/
theorem pairing_apply (g : A) (u w : TrivSqZeroExt A I) :
    pairing I g u w = Submodule.Quotient.mk (u.fst • w.snd) := rfl

/-- `pairing I g u` vanishes for `u ∈ gB`. -/
theorem pairing_eq_zero (g : A) {u : TrivSqZeroExt A I}
    (hu : u ∈ Ideal.span {algebraMap A (TrivSqZeroExt A I) g}) : pairing I g u = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  refine LinearMap.ext fun w ↦ ?_
  rw [pairing_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨b.fst • w.snd, ?_⟩
  simp [TrivSqZeroExt.algebraMap_eq_inl, smul_smul, mul_comm]

variable (I) in
/-- The pairing descended to `B / gB`. -/
def pairingQuot (g : A) : quot I g →ₗ[A] TrivSqZeroExt A I →ₗ[A] modG I g :=
  ((Ideal.span {algebraMap A (TrivSqZeroExt A I) g}).restrictScalars A).liftQ (pairing I g)
      (fun _ hu ↦ pairing_eq_zero g hu) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv A _).symm.toLinearMap

/-- `pairingQuot I g` at the class of `u` is `pairing I g u`. -/
theorem pairingQuot_mk (g : A) (u : TrivSqZeroExt A I) :
    pairingQuot I g (Ideal.Quotient.mk _ u) = pairing I g u := rfl

/-- For a domain `A`, an ideal `I` with `1 ∉ I` and `0 ≠ g ∈ I`, `B = A ⊕ Iε` and `M = B / gB`,
the action map `M ⊗_A B ⟶ M` is not bijective. -/
theorem not_bijective_actionMap [IsDomain A] {g : A} (hgI : g ∈ I) (hg0 : g ≠ 0)
    (h1 : (1 : A) ∉ I) : ¬ Function.Bijective (actionMap A (TrivSqZeroExt A I) (quot I g)) := by
  intro h
  let e : TrivSqZeroExt A I := TrivSqZeroExt.inr ⟨g, hgI⟩
  let x : quot I g ⊗[A] TrivSqZeroExt A I :=
    Ideal.Quotient.mk _ 1 ⊗ₜ e - Ideal.Quotient.mk _ e ⊗ₜ 1
  have hx : actionMap A (TrivSqZeroExt A I) (quot I g) x = 0 := by
    simp [x, actionMap, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have h2 := congrArg (TensorProduct.lift (pairingQuot I g)) (h.1 (hx.trans (map_zero _).symm))
  rw [map_zero, map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul, pairingQuot_mk,
    pairingQuot_mk, pairing_apply, pairing_apply, sub_eq_zero] at h2
  simp only [e, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_one, one_smul, zero_smul, Submodule.Quotient.mk_zero] at h2
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 h2
  have hgy : g * (y : A) = g * 1 := by simpa using congrArg Subtype.val hy
  exact h1 (mul_left_cancel₀ hg0 hgy ▸ y.2)

/-- With `I ⊆ A` idempotent and `B = A ⊕ Iε`, the `B`-module `B / gB` is not `IB`-power
torsion, although it is supported on `V(IB)` (`support_subset_zeroLocus`), whenever `A` is a
Bézout domain, `1 ∉ I` and `0 ≠ g ∈ I`. -/
theorem not_isIPowerTorsion [IsDomain A] [IsBezout A]
    (hsq : ∀ x ∈ I, ∃ c ∈ I, ∃ y ∈ I, c * y = x) {g : A} (hgI : g ∈ I) (hg0 : g ≠ 0)
    (h1 : (1 : A) ∉ I) :
    ¬ IsIPowerTorsion (TrivSqZeroExt A I) (quot I g) (I.map (algebraMap A (TrivSqZeroExt A I))) :=
  fun h ↦ not_bijective_actionMap hgI hg0 h1
    (bijective_actionMap_of_isIPowerTorsion A (TrivSqZeroExt A I) I (flat_trivSqZeroExt I)
      (bijective_quotientMap hsq) (quot I g) h)

/-! ### The Hahn series instance -/

/-- The valuation of the field `ℚ((t^ℚ))` of Hahn series with rational exponents. -/
abbrev hahnVal : AddValuation (HahnSeries ℚ ℚ) (WithTop ℚ) := HahnSeries.addVal ℚ ℚ

/-- Every rational number is a value of the valuation of `ℚ((t^ℚ))`. -/
theorem exists_hahnVal_eq (q : ℚ) : ∃ x, hahnVal x = q :=
  ⟨HahnSeries.single q 1, by simp⟩

end IPowerTorsion.SupportCounterexample

namespace IPowerTorsion

open SupportCounterexample in
/-- **Stacks 0AEU fails without finite presentation, at the ring level.** There are a flat ring
map `A ⟶ B`, an ideal `I ⊆ A` with `A / I ⟶ B / IB` bijective, and a finite `B`-module `M`
whose support lies in `V(IB)`, such that the action map `M ⊗_A B ⟶ M` (the counit
`Lf^*Rf_*M~ ⟶ M~` for `f : Spec B ⟶ Spec A`) is not bijective. Here `A` is the valuation ring
of `ℚ((t^ℚ))`, `I` its maximal ideal (which is not finitely generated), `B = A ⊕ Iε` and
`M = B / t¹B`; see the module docstring. -/
theorem exists_not_bijective_actionMap_of_support_subset :
    ∃ (A B M : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : AddCommGroup M)
      (_ : Module B M) (_ : Module A M) (_ : IsScalarTower A B M) (I : Ideal A),
      Module.Flat A B ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map) ∧
      Module.Finite B M ∧
      Module.support B M ⊆ PrimeSpectrum.zeroLocus (I.map (algebraMap A B) : Set B) ∧
      ¬ Function.Bijective (actionMap A B M) := by
  obtain ⟨g, hgI, hg⟩ := exists_mem_maxIdeal_eq_one exists_hahnVal_eq
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
  exact ⟨integers hahnVal, TrivSqZeroExt _ (maxIdeal hahnVal), quot (maxIdeal hahnVal) g,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, maxIdeal hahnVal, flat_trivSqZeroExt _,
    bijective_quotientMap fun _ hx ↦ exists_mul_eq_of_mem_maxIdeal exists_hahnVal_eq hx,
    inferInstance, support_subset_zeroLocus g fun _ ha ↦ exists_pow_eq_mul_of_mem_maxIdeal hg ha,
    not_bijective_actionMap hgI hg0 (one_notMem_maxIdeal _)⟩

end IPowerTorsion
