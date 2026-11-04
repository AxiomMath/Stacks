module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the twisted thickenings of the exceptional divisor of a blowup

This file formalizes Stacks Project Tag 0GA7, the first lemma of the section
*A bit of uniformity, III* of the chapter *Local Cohomology* (Tag 0GA6).

## The Situation of Tag 0GA6

Fix a Noetherian ring `A` and an ideal `I ⊆ A`. Let `p : X → Spec(A)` be the blowing up of
`Spec(A)` in `I`, that is, `X = Proj(⨁_{n ≥ 0} Iⁿ)`, let `Y = X ×_{Spec A} Spec(A/I)` be the
exceptional divisor and let `Yₙ = nY` for `n ≥ 1`. Then `Y` is an effective Cartier divisor
with `𝒪_X(1) = 𝒪_X(-Y)`, and `Y = Proj(S)` for `S = Gr_I(A) = ⨁_{n ≥ 0} Iⁿ/Iⁿ⁺¹`. The
integer `d = d(S)` is the maximum of the dimensions of the fibres of `p` (and `0` if
`X = ∅`); the integer `q₀ = q(S)` is the smallest integer `≥ 0` such that for all `q ≥ q(S)`
one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ d` and `H⁰(Y, 𝒪_Y(q)) = I^q/I^{q+1}`.

Tag 0GA7 then asserts, with `q₀ = q(S)` and `d = d(S)`:

1. for `n ≥ 1`, `q ≥ q₀` and `i > 0` we have `Hⁱ(X, 𝒪_{Yₙ}(q)) = 0`;
2. for `n ≥ 1` and `q ≥ q₀` we have `H⁰(X, 𝒪_{Yₙ}(q)) = I^q/I^{q+n}`;
3. for `q ≥ q₀` and `i > 0` we have `Hⁱ(X, 𝒪_X(q)) = 0`;
4. for `q ≥ q₀` we have `H⁰(X, 𝒪_X(q)) = I^q`.

## What is formalized here, and what is assumed

**Where Tag 0GA7 is registered.** Not in this file. The four theorems below each state ONE of
the tag's four clauses, and each binds `S : Situation A I`, a structure carrying the cohomology
groups and both long exact sequences as fields. A registration here would therefore be a
component registration resting on a stand-in structure, which is twice over not what the tag
asserts. The tag is registered once, on
`Stacks.LocalCohomology.UniformityIII.blowupHmod_of_qS_le`
(`BitUniformityIII/BlowupSituation.lean`), which states all four clauses at `q₀ = q(S)` (the
integer `Stacks.LocalCohomology.UniformityIII.qS`) for the blowup's own `A`-module-valued
cohomology under `[IsNoetherianRing A]` alone.

The structure is no longer merely hypothetical: `Stacks.LocalCohomology.UniformityIII`
`.blowupSituationOf` inhabits it for every Noetherian `A`, every ideal `I` and every `q₀` with
the defining property of `q(S)`, so the four
theorems below do hold of the blowup — the point of moving the tag is that their *signatures*
still mention `S`, and faithfulness is read off a signature.

The geometric half of the Situation — the blowup, the twisting sheaves `𝒪_X(q)`, the
thickenings `Yₙ`, and the long exact cohomology sequences they produce — was not, when this
file was written, available in a form that lets the four clauses be stated about the actual
sheaves. Accordingly the
cohomology groups and the comparison maps are carried as the *data* of a structure
`Stacks.LocalCohomology.UniformityIII.Situation`, together with exactly those properties of
them that the section of the Stacks Project establishes before stating the lemma. Every field
of that structure is annotated with the geometric fact it stands for. The four clauses are
then theorems about such a `Situation`, proved by the argument of the Stacks Project: they are
*not* among the hypotheses.

Concretely, the structure supplies the groups `Hⁱ(X, 𝒪_{Yₙ}(q))` and `Hⁱ(X, 𝒪_X(q))` as
`A`-modules, the canonical comparison maps `I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))` and
`I^q → H⁰(X, 𝒪_X(q))`, the long exact sequences of the two short exact sequences
`0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0` and
`0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`, the defining property of `q(S)` (the case `n = 1`),
the vanishing of `Hⁱ` above the fibre dimension `d`, and Serre's theorem on `X` in the form
that `Hⁱ(X, 𝒪_X(q)) = 0` for `i > 0` and `q ≫ 0` and `H⁰(X, 𝒪_X(q)) = I^q` for `q ≫ 0`.

The subquotients `I^q/I^{q+n}` and the exact sequence
`0 → I^{q+1}/I^{q+1+n} → I^q/I^{q+1+n} → I^q/I^{q+1} → 0` used in the proof of clause (2) are
built and proved here, not assumed.

`Stacks.LocalCohomology.UniformityIII.topSituation` exhibits a `Situation` for `I = ⊤`, the
degenerate case with which the Stacks proof opens, so the hypotheses are consistent.

That witness is degenerate: for `I = ⊤` every subquotient `I^q/I^{q+n}` vanishes, so all four
clauses are statements about zero modules there.
`Stacks.LocalCohomology.UniformityIII.affineSituation` exhibits a `Situation` in which they are
not: the case `d(S) = 0`, `q(S) = 0` in which the blowing up is an isomorphism, so that
`Hⁱ(X, 𝒪_{Yₙ}(q))` and `Hⁱ(X, 𝒪_X(q))` are concentrated in degree `0` with values `I^q/I^{q+n}`
and `I^q`. For `I ≠ ⊤` the module `H⁰(Y, 𝒪_Y) = A/I` it produces is nontrivial, by
`Stacks.LocalCohomology.UniformityIII.nontrivial_affineSituation_Hdiv`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.powQuot`: the subquotient `I^q/I^{q+n}` of `A`.
* `Stacks.LocalCohomology.UniformityIII.powQuotLe`: the map `I^q/I^{q+n} → I^{q'}/I^{q'+n}`
  for `q' ≤ q`, which is the twisting-down map on sections.
* `Stacks.LocalCohomology.UniformityIII.powQuotSmul`: multiplication by an element of `I^c`,
  as a map `I^q/I^{q+n} → I^{q+c}/I^{q+c+n}`.
* `Stacks.LocalCohomology.UniformityIII.Situation`: the data and standing hypotheses of the
  Situation of Tag 0GA6.
* `Stacks.LocalCohomology.UniformityIII.affineSituation`: the Situation in which the blowing up
  is an isomorphism, with `d(S) = 0` and `q(S) = 0`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.Situation.subsingleton_Hdiv`: clause (1).
* `Stacks.LocalCohomology.UniformityIII.Situation.bijective_cdiv`: clause (2).
* `Stacks.LocalCohomology.UniformityIII.Situation.subsingleton_Hamb`: clause (3).
* `Stacks.LocalCohomology.UniformityIII.Situation.bijective_camb`: clause (4).

## Implementation notes

A cohomology group is "zero" here in the form `Subsingleton`, and an identification
`H⁰(…) = …` is the statement that the canonical comparison map carried by the `Situation` is
bijective; identifying an abstract group with `I^q/I^{q+n}` without reference to a map would
be strictly weaker.

Twists are indexed by `ℕ` rather than `ℤ`. All four clauses only concern `q ≥ q₀ ≥ 0`, and
the proofs only ever pass from `q` to `q + 1`, so nothing is lost.

The ring `A` is assumed Noetherian for faithfulness to the Situation; the argument below
never uses it.

## References

* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
-/

@[expose] public section

universe u

namespace Stacks.LocalCohomology.UniformityIII

section FiveLemma

variable {A : Type u} [CommRing A]

/-- The short five lemma for `A`-modules, in the form used twice below: a map of exact rows
whose outer vertical maps are bijective has bijective middle vertical map. -/
private theorem bijective_of_exact_rows
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    [Module A N₁] [Module A N₂] [Module A N₃]
    (f₁ : M₁ →ₗ[A] M₂) (f₂ : M₂ →ₗ[A] M₃) (g₁ : N₁ →ₗ[A] N₂) (g₂ : N₂ →ₗ[A] N₃)
    (u₁ : M₁ →ₗ[A] N₁) (u₂ : M₂ →ₗ[A] N₂) (u₃ : M₃ →ₗ[A] N₃)
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂)
    (sq₁ : ∀ x, g₁ (u₁ x) = u₂ (f₁ x)) (sq₂ : ∀ x, g₂ (u₂ x) = u₃ (f₂ x))
    (h₁ : Function.Bijective u₁) (h₃ : Function.Bijective u₃) :
    Function.Bijective u₂ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h3 : f₂ x = 0 := h₃.1 (by rw [← sq₂, hx, map_zero, map_zero])
    obtain ⟨m, rfl⟩ := (hf x).1 h3
    have h5 : u₁ m = 0 := hg₁ (by rw [sq₁, hx, map_zero])
    rw [h₁.1 (by rw [h5, map_zero] : u₁ m = u₁ 0), map_zero]
  · intro y
    obtain ⟨m₃, hm₃⟩ := h₃.2 (g₂ y)
    obtain ⟨m₂, rfl⟩ := hf₂ m₃
    obtain ⟨n₁, hn₁⟩ := (hg (y - u₂ m₂)).1 (by rw [map_sub, sq₂, hm₃, sub_self])
    obtain ⟨m₁, rfl⟩ := h₁.2 n₁
    refine ⟨m₂ + f₁ m₁, ?_⟩
    rw [map_add, ← sq₁, hn₁]
    abel

end FiveLemma

section Subquotients

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- `I ^ (q + n)`, viewed as a submodule of `I ^ q`. -/
def powSub (q n : ℕ) : Submodule A (I ^ q : Ideal A) :=
  Submodule.comap (I ^ q : Ideal A).subtype (I ^ (q + n))

/-- The subquotient `I^q/I^{q+n}` of `A`. -/
abbrev powQuot (q n : ℕ) : Type u := (I ^ q : Ideal A) ⧸ powSub I q n

/-- The map `I^{q+1}/I^{q+1+n} → I^q/I^{q+(n+1)}` induced by `I ^ (q + 1) ≤ I ^ q`. -/
def powShift (q n : ℕ) : powQuot I (q + 1) n →ₗ[A] powQuot I q (n + 1) :=
  Submodule.mapQ _ _ (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ q)))
    (by
      rintro ⟨x, hx⟩ hmem
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hmem ⊢
      simpa [show q + 1 + n = q + (n + 1) by omega] using hmem)

/-- The truncation `I^q/I^{q+(n+1)} → I^q/I^{q+1}`. -/
def powTrunc (q n : ℕ) : powQuot I q (n + 1) →ₗ[A] powQuot I q 1 :=
  Submodule.mapQ _ _ LinearMap.id
    (by
      rintro ⟨x, hx⟩ hmem
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hmem ⊢
      exact Ideal.pow_le_pow_right (by omega) hmem)

/-- The inclusion `I^{q+1} ⊆ I^q`. -/
def powIncl (q : ℕ) : (I ^ (q + 1) : Ideal A) →ₗ[A] (I ^ q : Ideal A) :=
  Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ q))

/-- `powShift` sends the class of `x ∈ I^{q+1}` to the class of `x` in `I^q/I^{q+(n+1)}`. -/
@[simp] theorem powShift_mk (q n : ℕ) (x : (I ^ (q + 1) : Ideal A)) :
    powShift I q n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ q)) x) :=
  rfl

/-- `powTrunc` sends the class of `x ∈ I^q` to its class modulo `I^{q+1}`. -/
@[simp] theorem powTrunc_mk (q n : ℕ) (x : (I ^ q : Ideal A)) :
    powTrunc I q n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- The inclusion `I^{q+1} ⊆ I^q` does not change the underlying element of `A`. -/
@[simp] theorem coe_powIncl (q : ℕ) (x : (I ^ (q + 1) : Ideal A)) :
    ((powIncl I q x : (I ^ q : Ideal A)) : A) = (x : A) := rfl

/-- The map `I^q/I^{q+n} → I^{q'}/I^{q'+n}` induced by `I ^ q ≤ I ^ q'` for `q' ≤ q`. For a
coherent module on the blowup it is the canonical map `ℱ(q) → ℱ(q')` of the twists. -/
def powQuotLe {q q' n : ℕ} (h : q' ≤ q) : powQuot I q n →ₗ[A] powQuot I q' n :=
  Submodule.mapQ _ _ (Submodule.inclusion (Ideal.pow_le_pow_right h))
    (by
      rintro ⟨x, hx⟩ hmem
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hmem ⊢
      exact Ideal.pow_le_pow_right (by omega) hmem)

/-- `powQuotLe` sends the class of `x ∈ I^q` to the class of `x` in `I^{q'}/I^{q'+n}`. -/
@[simp] theorem powQuotLe_mk {q q' n : ℕ} (h : q' ≤ q) (x : (I ^ q : Ideal A)) :
    powQuotLe I h (Submodule.Quotient.mk x : powQuot I q n) =
      Submodule.Quotient.mk (Submodule.inclusion (Ideal.pow_le_pow_right h) x) := rfl

/-- Multiplication by an element `a ∈ I^c`, as a map `I^q/I^{q+n} → I^r/I^{r+n}` for
`r = q + c`: multiplication by `a` carries `I^q` into `I^{q+c}` and `I^{q+n}` into
`I^{q+c+n}`. The target exponent is an argument constrained by `q + c = r`, so that no
truncated subtraction appears at the use sites. -/
def powQuotSmul {a : A} {c q r n : ℕ} (ha : a ∈ I ^ c) (hr : q + c = r) :
    powQuot I q n →ₗ[A] powQuot I r n :=
  Submodule.mapQ _ _
    { toFun := fun x => ⟨a * (x : A), by
        have h : a * (x : A) ∈ I ^ c * I ^ q := Ideal.mul_mem_mul ha x.2
        rw [← pow_add] at h
        exact Ideal.pow_le_pow_right (by omega) h⟩
      map_add' := fun x y => by ext; simp [mul_add]
      map_smul' := fun t x => by ext; simp [smul_eq_mul]; ring }
    (by
      rintro ⟨x, hx⟩ hmem
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hmem ⊢
      have h : a * x ∈ I ^ c * I ^ (q + n) := Ideal.mul_mem_mul ha hmem
      rw [← pow_add] at h
      exact Ideal.pow_le_pow_right (by omega) h)

/-- `powQuotSmul` sends the class of `x` to the class of any `y ∈ I^r` with `y = a * x`. -/
theorem powQuotSmul_mk {a : A} {c q r n : ℕ} (ha : a ∈ I ^ c) (hr : q + c = r)
    (x : (I ^ q : Ideal A)) (y : (I ^ r : Ideal A)) (hxy : (y : A) = a * (x : A)) :
    powQuotSmul I ha hr (Submodule.Quotient.mk x : powQuot I q n) =
      Submodule.Quotient.mk y :=
  congrArg Submodule.Quotient.mk (Subtype.ext hxy.symm)

/-- The truncation `I^q/I^{q+(n+1)} → I^q/I^{q+1}` is surjective. -/
theorem powTrunc_surjective (q n : ℕ) : Function.Surjective (powTrunc I q n) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The composite `I^{q+1}/I^{q+1+n} → I^q/I^{q+(n+1)} → I^q/I^{q+1}` is zero. -/
theorem powTrunc_powShift (q n : ℕ) (w : powQuot I (q + 1) n) :
    powTrunc I q n (powShift I q n w) = 0 := by
  induction w using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨z, hz⟩ := z
    rw [powShift_mk, powTrunc_mk, Submodule.Quotient.mk_eq_zero]
    simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion]
    exact Ideal.pow_le_pow_right (by omega) hz

/-- The sequence `I^{q+1}/I^{q+1+n} → I^q/I^{q+1+n} → I^q/I^{q+1}` is exact; together with
`powTrunc_surjective` this is the top row of the diagram in the proof of Tag 0GA7(2). -/
theorem powExact (q n : ℕ) : Function.Exact (powShift I q n) (powTrunc I q n) := by
  intro y
  constructor
  · intro hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      rw [powTrunc_mk, Submodule.Quotient.mk_eq_zero] at hy
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hy
      exact ⟨Submodule.Quotient.mk ⟨x, by simpa using hy⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact powTrunc_powShift I q n z

/-- The sequence `I^{q+1} → I^q → I^q/I^{q+1}` is exact. -/
theorem powExact_incl (q : ℕ) : Function.Exact (powIncl I q) (powSub I q 1).mkQ := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hy
    exact ⟨⟨x, hy⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨z, hz⟩ := z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simpa [powSub] using hz

/-- The quotient map `I^q → I^q/I^{q+1}` is surjective. -/
theorem mkQ_surjective (q : ℕ) : Function.Surjective (powSub I q 1).mkQ :=
  Submodule.mkQ_surjective _

end Subquotients

/-- The data and the standing hypotheses of the Situation of Stacks Tag 0GA6: a Noetherian
ring `A`, an ideal `I ⊆ A`, the blowup `p : X → Spec(A)` of `Spec(A)` in `I`, its exceptional
divisor `Y` with thickenings `Yₙ = nY`, the integers `d = d(S)` and `q₀ = q(S)` attached to
`S = Gr_I(A)`, and the cohomology of the twists of `𝒪_{Yₙ}` and `𝒪_X`.

The scheme `X` and its sheaves do not appear: what appears are the cohomology modules they
produce, the canonical comparison maps out of the subquotients of `A`, and the properties of
these that the section of the Stacks Project establishes before Tag 0GA7 is stated. -/
structure Situation (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) where
  /-- `d = d(S)`, the maximum of the dimensions of the fibres of `p : X → Spec(A)`. -/
  d : ℕ
  /-- `q₀ = q(S)`. -/
  q₀ : ℕ
  /-- `Hdiv n i q` is `Hⁱ(X, 𝒪_{Yₙ}(q))`; only `n ≥ 1` is ever used, and `Y₁ = Y`. -/
  Hdiv : ℕ → ℕ → ℕ → ModuleCat.{u} A
  /-- `Hamb i q` is `Hⁱ(X, 𝒪_X(q))`. -/
  Hamb : ℕ → ℕ → ModuleCat.{u} A
  /-- The canonical map `I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))`. -/
  cdiv : ∀ n q : ℕ, powQuot I q n →ₗ[A] Hdiv n 0 q
  /-- The canonical map `I^q → H⁰(X, 𝒪_X(q))`. -/
  camb : ∀ q : ℕ, (I ^ q : Ideal A) →ₗ[A] Hamb 0 q
  /-- `Hⁱ(X, 𝒪_{Yₙ}(q+1)) → Hⁱ(X, 𝒪_{Y_{n+1}}(q))`, from
  `0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0`. -/
  divα : ∀ n i q : ℕ, Hdiv n i (q + 1) →ₗ[A] Hdiv (n + 1) i q
  /-- `Hⁱ(X, 𝒪_{Y_{n+1}}(q)) → Hⁱ(X, 𝒪_Y(q))`, from the same short exact sequence. -/
  divβ : ∀ n i q : ℕ, Hdiv (n + 1) i q →ₗ[A] Hdiv 1 i q
  /-- The connecting map `Hⁱ(X, 𝒪_Y(q)) → Hⁱ⁺¹(X, 𝒪_{Yₙ}(q+1))`. -/
  divδ : ∀ n i q : ℕ, Hdiv 1 i q →ₗ[A] Hdiv n (i + 1) (q + 1)
  /-- Exactness of the long exact sequence at `Hⁱ(X, 𝒪_{Y_{n+1}}(q))`. -/
  div_exact_mid : ∀ n i q, 1 ≤ n → Function.Exact (divα n i q) (divβ n i q)
  /-- Exactness of the long exact sequence at `Hⁱ(X, 𝒪_Y(q))`. -/
  div_exact_right : ∀ n i q, 1 ≤ n → Function.Exact (divβ n i q) (divδ n i q)
  /-- The long exact sequence begins with an injection in degree `0`. -/
  div_injective : ∀ n q, 1 ≤ n → Function.Injective (divα n 0 q)
  /-- The left-hand square of the diagram in the proof of Tag 0GA7(2). -/
  div_sq_left : ∀ n q, 1 ≤ n → ∀ x,
    divα n 0 q (cdiv n (q + 1) x) = cdiv (n + 1) q (powShift I q n x)
  /-- The right-hand square of the diagram in the proof of Tag 0GA7(2). -/
  div_sq_right : ∀ n q, 1 ≤ n → ∀ x,
    divβ n 0 q (cdiv (n + 1) q x) = cdiv 1 q (powTrunc I q n x)
  /-- Half of the definition of `q(S)`: `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ d` and `q ≥ q(S)`. -/
  base_vanishing : ∀ i q, 1 ≤ i → i ≤ d → q₀ ≤ q → Subsingleton (Hdiv 1 i q)
  /-- The other half: `H⁰(Y, 𝒪_Y(q)) = I^q/I^{q+1}` for `q ≥ q(S)`. -/
  base_sections : ∀ q, q₀ ≤ q → Function.Bijective (cdiv 1 q)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`, since `d` bounds the fibre dimensions. -/
  div_vanishing_gt : ∀ n i q, d < i → Subsingleton (Hdiv n i q)
  /-- `Hⁱ(X, 𝒪_X(q+1)) → Hⁱ(X, 𝒪_X(q))`, from `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`. -/
  ambα : ∀ i q : ℕ, Hamb i (q + 1) →ₗ[A] Hamb i q
  /-- `Hⁱ(X, 𝒪_X(q)) → Hⁱ(X, 𝒪_Y(q))`, from the same short exact sequence. -/
  ambβ : ∀ i q : ℕ, Hamb i q →ₗ[A] Hdiv 1 i q
  /-- The connecting map `Hⁱ(X, 𝒪_Y(q)) → Hⁱ⁺¹(X, 𝒪_X(q+1))`. -/
  ambδ : ∀ i q : ℕ, Hdiv 1 i q →ₗ[A] Hamb (i + 1) (q + 1)
  /-- Exactness of the long exact sequence at `Hⁱ(X, 𝒪_X(q))`. -/
  amb_exact_mid : ∀ i q, Function.Exact (ambα i q) (ambβ i q)
  /-- Exactness of the long exact sequence at `Hⁱ(X, 𝒪_Y(q))`. -/
  amb_exact_right : ∀ i q, Function.Exact (ambβ i q) (ambδ i q)
  /-- The long exact sequence begins with an injection in degree `0`. -/
  amb_injective : ∀ q, Function.Injective (ambα 0 q)
  /-- `I^{q+1} → I^q → H⁰(X, 𝒪_X(q))` agrees with `I^{q+1} → H⁰(X, 𝒪_X(q+1)) → H⁰(X, 𝒪_X(q))`. -/
  amb_sq_left : ∀ q x, ambα 0 q (camb (q + 1) x) = camb q (powIncl I q x)
  /-- `I^q → H⁰(X, 𝒪_X(q)) → H⁰(X, 𝒪_Y(q))` is reduction `I^q → I^q/I^{q+1}`. -/
  amb_sq_right : ∀ q x, ambβ 0 q (camb q x) = cdiv 1 q ((powSub I q 1).mkQ x)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`. -/
  amb_vanishing_gt : ∀ i q, d < i → Subsingleton (Hamb i q)
  /-- Serre vanishing on `X`: `Hⁱ(X, 𝒪_X(q)) = 0` for `i > 0` and `q` large. -/
  amb_serre : ∀ i, 1 ≤ i → ∃ N, ∀ q, N ≤ q → Subsingleton (Hamb i q)
  /-- Serre's computation of the sections: `H⁰(X, 𝒪_X(q)) = I^q` for `q` large. -/
  amb_serre_sections : ∃ N, ∀ q, N ≤ q → Function.Bijective (camb q)

namespace Situation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} (S : Situation A I)

/-- **Stacks Project, Tag 0GA7, clause (1).** In the Situation of Tag 0GA6, for `n ≥ 1`,
`q ≥ q₀ = q(S)` and `i > 0` we have `Hⁱ(X, 𝒪_{Yₙ}(q)) = 0`.

The cohomology groups, the long exact sequence of
`0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0` and the defining property of `q(S)` are
carried by `S`; the statement for general `n` is the induction of the Stacks proof. -/
theorem subsingleton_Hdiv {n i q : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hq : S.q₀ ≤ q) :
    Subsingleton (S.Hdiv n i q) := by
  by_cases hd : S.d < i
  · exact S.div_vanishing_gt n i q hd
  replace hd : i ≤ S.d := by omega
  have key : ∀ m : ℕ, 1 ≤ m → ∀ r : ℕ, S.q₀ ≤ r → Subsingleton (S.Hdiv m i r) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun r hr => S.base_vanishing i r hi hd hr
    | succ m hm ih =>
      intro r hr
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨x, rfl⟩ := (S.div_exact_mid m i r hm y).1
        (@Subsingleton.elim _ (S.base_vanishing i r hi hd hr) _ _)
      rw [@Subsingleton.elim _ (ih (r + 1) (by omega)) x 0, map_zero]
  exact key n hn q hq

/-- **Stacks Project, Tag 0GA7, clause (2).** In the Situation of Tag 0GA6, for `n ≥ 1` and
`q ≥ q₀ = q(S)` the canonical map `I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))` is bijective.

The case `n = 1` is the definition of `q(S)`, carried by `S`; the general case is the
induction of the Stacks proof, whose inductive step is the short five lemma applied to the
commutative diagram there, with top row
`0 → I^{q+1}/I^{q+1+n} → I^q/I^{q+1+n} → I^q/I^{q+1} → 0`. -/
theorem bijective_cdiv {n q : ℕ} (hn : 1 ≤ n) (hq : S.q₀ ≤ q) :
    Function.Bijective (S.cdiv n q) := by
  have key : ∀ m : ℕ, 1 ≤ m → ∀ r : ℕ, S.q₀ ≤ r → Function.Bijective (S.cdiv m r) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun r hr => S.base_sections r hr
    | succ m hm ih =>
      intro r hr
      exact bijective_of_exact_rows (powShift I r m) (powTrunc I r m)
        (S.divα m 0 r) (S.divβ m 0 r) (S.cdiv m (r + 1)) (S.cdiv (m + 1) r) (S.cdiv 1 r)
        (powExact I r m) (powTrunc_surjective I r m)
        (S.div_injective m r hm) (S.div_exact_mid m 0 r hm)
        (S.div_sq_left m r hm) (S.div_sq_right m r hm)
        (ih (r + 1) (by omega)) (S.base_sections r hr)
  exact key n hn q hq

/-- The transition map `Hⁱ(X, 𝒪_X(q+1)) → Hⁱ(X, 𝒪_X(q))` is surjective for `i > 0` and
`q ≥ q₀`, because the next term `Hⁱ(X, 𝒪_Y(q))` of the long exact sequence vanishes. -/
theorem surjective_ambα {i q : ℕ} (hi : 1 ≤ i) (hq : S.q₀ ≤ q) :
    Function.Surjective (S.ambα i q) := fun y =>
  (S.amb_exact_mid i q y).1 (@Subsingleton.elim _ (S.subsingleton_Hdiv le_rfl hi hq) _ _)

/-- **Stacks Project, Tag 0GA7, clause (3).** In the Situation of Tag 0GA6, for `q ≥ q₀` and
`i > 0` we have `Hⁱ(X, 𝒪_X(q)) = 0`.

The transition maps `Hⁱ(X, 𝒪_X(q+1)) → Hⁱ(X, 𝒪_X(q))` are surjective for `q ≥ q₀` by
clause (1) and the long exact sequence of `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`, and the
source vanishes once `q` is large by Serre vanishing on `X`. -/
theorem subsingleton_Hamb {i q : ℕ} (hi : 1 ≤ i) (hq : S.q₀ ≤ q) :
    Subsingleton (S.Hamb i q) := by
  obtain ⟨N, hN⟩ := S.amb_serre i hi
  refine Nat.decreasingInduction' (P := fun r => Subsingleton (S.Hamb i r))
    (fun r _ hr h => ?_) (Nat.le_add_right q N) (hN (q + N) (Nat.le_add_left N q))
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, rfl⟩ := S.surjective_ambα hi (by omega) y
  rw [@Subsingleton.elim _ h x 0, map_zero]

/-- **Stacks Project, Tag 0GA7, clause (4).** In the Situation of Tag 0GA6, for `q ≥ q₀` the
canonical map `I^q → H⁰(X, 𝒪_X(q))` is bijective.

Descending induction from the range where Serre's theorem already identifies the sections:
the short five lemma applied to the map from `0 → I^{q+1} → I^q → I^q/I^{q+1} → 0` into the
long exact sequence of `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0` carries the identification from
`q + 1` down to `q`, using clause (2) for `n = 1` on the right. -/
theorem bijective_camb {q : ℕ} (hq : S.q₀ ≤ q) : Function.Bijective (S.camb q) := by
  have step : ∀ r, S.q₀ ≤ r → Function.Bijective (S.camb (r + 1)) →
      Function.Bijective (S.camb r) := fun r hr hb =>
    bijective_of_exact_rows (powIncl I r) (powSub I r 1).mkQ
      (S.ambα 0 r) (S.ambβ 0 r) (S.camb (r + 1)) (S.camb r) (S.cdiv 1 r)
      (powExact_incl I r) (mkQ_surjective I r)
      (S.amb_injective r) (S.amb_exact_mid 0 r)
      (S.amb_sq_left r) (S.amb_sq_right r) hb (S.base_sections r hr)
  obtain ⟨N, hN⟩ := S.amb_serre_sections
  exact Nat.decreasingInduction' (P := fun r => Function.Bijective (S.camb r))
    (fun r _ hr => step r (by omega)) (Nat.le_add_right q N) (hN (q + N) (Nat.le_add_left N q))

end Situation

section TopWitness

variable (A : Type u) [CommRing A]

/-- Every power of the unit ideal is the unit ideal. -/
theorem top_pow_eq_top (k : ℕ) : (⊤ : Ideal A) ^ k = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ih]

/-- For the unit ideal every subquotient `I^q/I^{q+n}` is zero. -/
theorem subsingleton_powQuot_top (q n : ℕ) :
    Subsingleton (powQuot (⊤ : Ideal A) q n) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero]
    simp [powSub, top_pow_eq_top]

/-- For the unit ideal the inclusion `I^q ⊆ A` is a bijection. -/
theorem bijective_subtype_top_pow (q : ℕ) :
    Function.Bijective ((⊤ : Ideal A) ^ q : Ideal A).subtype :=
  ⟨Subtype.coe_injective, fun a => ⟨⟨a, by simp [top_pow_eq_top]⟩, rfl⟩⟩

/-- The Situation of Tag 0GA6 for `I = A`, the case the proof of Tag 0GA7 disposes of first:
the blowup `X` is `Spec(A)` itself, the exceptional divisor is empty, so every
`Hⁱ(X, 𝒪_{Yₙ}(q))` vanishes, `Hⁱ(X, 𝒪_X(q))` vanishes for `i > 0` and
`H⁰(X, 𝒪_X(q)) = A = I^q`. It witnesses that the hypotheses of `Situation` are consistent. -/
def topSituation [IsNoetherianRing A] : Situation A (⊤ : Ideal A) where
  d := 0
  q₀ := 0
  Hdiv _ _ _ := ModuleCat.of A PUnit
  Hamb i _ := match i with
    | 0 => ModuleCat.of A A
    | _ + 1 => ModuleCat.of A PUnit
  cdiv _ _ := 0
  camb _ := Submodule.subtype _
  divα _ _ _ := 0
  divβ _ _ _ := 0
  divδ _ _ _ := 0
  div_exact_mid _ _ _ _ _ :=
    ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  div_exact_right _ _ _ _ _ :=
    ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  div_injective _ _ _ _ _ _ := Subsingleton.elim _ _
  div_sq_left _ _ _ _ := Subsingleton.elim _ _
  div_sq_right _ _ _ _ := Subsingleton.elim _ _
  base_vanishing _ _ _ _ _ := inferInstanceAs (Subsingleton PUnit)
  base_sections q _ :=
    ⟨fun _ _ _ => @Subsingleton.elim _ (subsingleton_powQuot_top A q 1) _ _,
      fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  div_vanishing_gt _ _ _ _ := inferInstanceAs (Subsingleton PUnit)
  ambα i _ := match i with
    | 0 => LinearMap.id
    | _ + 1 => 0
  ambβ _ _ := 0
  ambδ _ _ := 0
  amb_exact_mid i q := by
    rcases i with _ | i
    · exact fun y => ⟨fun _ => ⟨y, rfl⟩, fun _ => Subsingleton.elim _ _⟩
    · exact fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  amb_exact_right _ _ _ :=
    ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  amb_injective _ _ _ h := h
  amb_sq_left _ _ := rfl
  amb_sq_right _ _ := Subsingleton.elim _ _
  amb_vanishing_gt i q h := by
    rcases i with _ | i
    · exact absurd h (lt_irrefl 0)
    · exact inferInstanceAs (Subsingleton PUnit)
  amb_serre i hi := ⟨0, by
    rcases i with _ | i
    · omega
    · exact fun _ _ => inferInstanceAs (Subsingleton PUnit)⟩
  amb_serre_sections := ⟨0, fun q _ => bijective_subtype_top_pow A q⟩

end TopWitness

section AffineWitness

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The map `I^{q+1}/I^{q+1+n} → I^q/I^{q+(n+1)}` is injective, because an element of
`I^{q+1}` lying in `I^{q+(n+1)}` lies in `I^{(q+1)+n}`. -/
theorem powShift_injective (q n : ℕ) : Function.Injective (powShift I q n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨z, hz⟩ := z
    rw [powShift_mk, Submodule.Quotient.mk_eq_zero] at hx
    simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype,
      Submodule.coe_inclusion] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    simpa [powSub, show q + 1 + n = q + (n + 1) by omega] using hx

/-- `A/I` is nontrivial when `I ≠ ⊤`; this is the subquotient `I⁰/I¹`. -/
theorem nontrivial_powQuot_zero_one (hI : I ≠ ⊤) : Nontrivial (powQuot I 0 1) := by
  refine ⟨Submodule.Quotient.mk ⟨1, by simp⟩, 0, ?_⟩
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype, zero_add, pow_one]
  exact fun h1 => hI ((Ideal.eq_top_iff_one I).2 h1)

/-- The Situation of Tag 0GA6 in the case `d(S) = 0` and `q(S) = 0`, in which the blowing up
`p : X → Spec(A)` is an isomorphism — for instance when `I = (f)` is generated by a single
nonzerodivisor, so that `𝒪_X(q) = I^q𝒪_X` and `Y = Spec(A/I)` is affine. All cohomology is then
concentrated in degree `0`, with `H⁰(X, 𝒪_{Yₙ}(q)) = I^q/I^{q+n}` and `H⁰(X, 𝒪_X(q)) = I^q`,
and the long exact sequences degenerate to the exact sequences
`0 → I^{q+1}/I^{q+1+n} → I^q/I^{q+1+n} → I^q/I^{q+1} → 0` and
`0 → I^{q+1} → I^q → I^q/I^{q+1} → 0` of `powExact` and `powExact_incl`.

Unlike `topSituation` this witness is not degenerate: for `I ≠ ⊤` the module
`H⁰(Y, 𝒪_Y) = A/I` is nontrivial, see `nontrivial_affineSituation_Hdiv`. -/
def affineSituation [IsNoetherianRing A] : Situation A I where
  d := 0
  q₀ := 0
  Hdiv n i q := match i with
    | 0 => ModuleCat.of A (powQuot I q n)
    | _ + 1 => ModuleCat.of A PUnit
  Hamb i q := match i with
    | 0 => ModuleCat.of A (I ^ q : Ideal A)
    | _ + 1 => ModuleCat.of A PUnit
  cdiv _ _ := LinearMap.id
  camb _ := LinearMap.id
  divα n i q := match i with
    | 0 => powShift I q n
    | _ + 1 => 0
  divβ n i q := match i with
    | 0 => powTrunc I q n
    | _ + 1 => 0
  divδ _ _ _ := 0
  div_exact_mid n i q _ := match i with
    | 0 => powExact I q n
    | _ + 1 => fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  div_exact_right n i q _ := match i with
    | 0 => fun y => ⟨fun _ => powTrunc_surjective I q n y, fun _ => Subsingleton.elim _ _⟩
    | _ + 1 => fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  div_injective n q _ := powShift_injective I q n
  div_sq_left _ _ _ _ := rfl
  div_sq_right _ _ _ _ := rfl
  base_vanishing i q hi hid _ := absurd (hi.trans hid) (by omega)
  base_sections _ _ := ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩
  div_vanishing_gt n i q hi := match i, hi with
    | _ + 1, _ => inferInstanceAs (Subsingleton PUnit)
  ambα i q := match i with
    | 0 => powIncl I q
    | _ + 1 => 0
  ambβ i q := match i with
    | 0 => (powSub I q 1).mkQ
    | _ + 1 => 0
  ambδ _ _ := 0
  amb_exact_mid i q := match i with
    | 0 => powExact_incl I q
    | _ + 1 => fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  amb_exact_right i q := match i with
    | 0 => fun y => ⟨fun _ => mkQ_surjective I q y, fun _ => Subsingleton.elim _ _⟩
    | _ + 1 => fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  amb_injective q := Submodule.inclusion_injective _
  amb_sq_left _ _ := rfl
  amb_sq_right _ _ := rfl
  amb_vanishing_gt i q hi := match i, hi with
    | _ + 1, _ => inferInstanceAs (Subsingleton PUnit)
  amb_serre i hi := ⟨0, match i, hi with
    | _ + 1, _ => fun _ _ => inferInstanceAs (Subsingleton PUnit)⟩
  amb_serre_sections := ⟨0, fun _ _ => ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩⟩

/-- `affineSituation` is not degenerate: for `I ≠ ⊤` the module `H⁰(Y, 𝒪_Y) = A/I` it supplies
is nontrivial, so the four clauses of Tag 0GA7 are not statements about zero modules there. -/
theorem nontrivial_affineSituation_Hdiv [IsNoetherianRing A] (hI : I ≠ ⊤) :
    Nontrivial ((affineSituation I).Hdiv 1 0 0) :=
  nontrivial_powQuot_zero_one I hI

end AffineWitness

end Stacks.LocalCohomology.UniformityIII

end
