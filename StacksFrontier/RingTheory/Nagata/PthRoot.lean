module

import Mathlib.RingTheory.AdicCompletion.Noetherian

public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# `p`-th roots descend from the completion of a Nagata local domain

Let `(A, 𝔪)` be a local domain which is a Nagata ring and of characteristic a prime `p`, and let
`A^ = lim_n A ⧸ 𝔪ⁿ` be its completion. An element of `A` which becomes a `p`-th power in `A^` is
already a `p`-th power in `A`.

The proof is by contradiction. Let `α ∈ A^` with `α ^ p = a` and suppose `a` is not a
`p`-th power in `A`. Then `a` is not a `p`-th power in the fraction field `K` either: if
`(b / c) ^ p = a` with `b, c ∈ A` and `c ≠ 0`, then `b ^ p = a * c ^ p`, so `b` and `α * c` have
equal `p`-th powers in the reduced ring `A^` (reduced by Lemma 0331) and hence are equal, whence
`c ∣ b` in `A` and `b / c` is a `p`-th root of `a` in `A`. So `X ^ p - a` is irreducible over `K`,
and `B = A[X] ⧸ (X ^ p - a)` is a domain: division with remainder by a monic polynomial is
available over `A` itself, so `B` injects into the field `K[X] ⧸ (X ^ p - a)`. Moreover `B` is
local, because
`b ↦ b ^ p` maps `B` into `A` (characteristic `p`), so a nonunit of `B` is one whose `p`-th power
lies in `𝔪`; and `B` is Nagata by Proposition 0334, being of finite type over `A`, hence
analytically unramified by Lemma 0331. That is the contradiction: writing `𝔫` for the maximal ideal
of `B`, the element `β - α` of `B^ = lim_n B ⧸ 𝔫ⁿ` is a `p`-th root of `0`, so it vanishes; but
`𝔫 ^ N ⊆ 𝔪B` for some `N`, so `β` would then lie in `A + 𝔪B`, which the coefficient of `β` in the
canonical representative of degree `< p` forbids: that `A`-linear form is `1` on `β`, is `0` on
`A`, and carries `𝔪B` into `𝔪`.

## Main results

* `IsNagataRing.exists_pow_eq_iff_exists_pow_eq_adicCompletion`: an element of a Nagata local
  domain of characteristic `p ≠ 0` is a `p`-th power if and only if it is one in the completion.

## Implementation notes

*The comparison map of completions.* The proof needs the ring map `A^ → B^` induced by `A → B`
along `𝔪 ↦ 𝔫`, which Mathlib's `AdicCompletion` API does not provide for a map of rings (only
`AdicCompletion.map`, for a linear map of modules over a fixed ring). It is built here as
`mapAdicCompletion`, from `AdicCompletion.liftRingHom` applied to the compatible family
`A^ → A ⧸ 𝔪ⁿ → B ⧸ 𝔫ⁿ`; the compatibility of the projections `A^ → A ⧸ 𝔪ⁿ` with the transition
maps is `AdicCompletion.factorPow_evalₐ`. `mapAdicCompletion` is a general fact about adic
completions, stated for an arbitrary ideal and an arbitrary algebra.

*`B` is a domain by division with remainder, not by a basis computation.*
`dvd_of_map_dvd_map` says that a polynomial over a domain `A` which a monic `f` divides over the
fraction field is already divisible by `f` over `A`, because `f` is monic; hence
`A[X] ⧸ (f) → K[X] ⧸ (f)` is injective, which is `isDomain_adjoinRoot_of_monic`. Both
are general facts about monic polynomials over a domain and neither is in Mathlib.

*Why the completion of `B` is compared with `𝔪`-adic data at a single level.* Rather than
identifying `B^` with `A^ ⊗_A B`, which would need the completion of `B` along `𝔪B` to be compared
with the completion along `𝔫`, the argument evaluates the vanishing nilpotent at one level `N` with
`𝔫 ^ N ⊆ 𝔪B`, obtained from `𝔫 ⊆ √(𝔪B)` (a nonunit of `B` has its `p`-th power in `𝔪`) by
`Ideal.exists_pow_le_of_le_radical_of_fg`. This is the same contradiction with fewer prerequisites.

## References

* [Stacks Project, Tag 09E2](https://stacks.math.columbia.edu/tag/09E2)
* [Stacks Project, Tag 0331](https://stacks.math.columbia.edu/tag/0331)
* [Stacks Project, Tag 0334](https://stacks.math.columbia.edu/tag/0334)
-/

@[expose] public section

namespace Stacks.Nagata.PthRootDescent

open Polynomial IsLocalRing _root_.AdicCompletion

/-! ### Comparison maps between adic completions -/

/-- If `I` maps into `J` then `I ^ n` maps into `J ^ n`. -/
theorem pow_le_comap_pow {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {I : Ideal A} {J : Ideal B} (h : Ideal.map (algebraMap A B) I ≤ J) (n : ℕ) :
    I ^ n ≤ Ideal.comap (algebraMap A B) (J ^ n) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact pow_le_pow_left' h n

/-- The composite `AdicCompletion I A → A ⧸ I ^ n → B ⧸ J ^ n`, for an ideal `I` of `A` whose
image is contained in the ideal `J` of `B`. -/
noncomputable def quotientMapEvalₐ {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (J : Ideal B) (h : Ideal.map (algebraMap A B) I ≤ J) (n : ℕ) :
    AdicCompletion I A →+* B ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) (algebraMap A B) (pow_le_comap_pow h n)).comp (evalₐ I n).toRingHom

/-- `quotientMapEvalₐ I J h n` sends `y` to the image under `A ⧸ I ^ n → B ⧸ J ^ n` of the
`n`-th component of `y`. -/
theorem quotientMapEvalₐ_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (J : Ideal B) (h : Ideal.map (algebraMap A B) I ≤ J) (n : ℕ)
    (y : AdicCompletion I A) :
    quotientMapEvalₐ I J h n y =
      Ideal.quotientMap (J ^ n) (algebraMap A B) (pow_le_comap_pow h n) (evalₐ I n y) := rfl

/-- The maps `quotientMapEvalₐ I J h n` are compatible with the transition maps
`B ⧸ J ^ n → B ⧸ J ^ m` for `m ≤ n`. -/
theorem factorPow_comp_quotientMapEvalₐ {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) (J : Ideal B) (h : Ideal.map (algebraMap A B) I ≤ J) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (quotientMapEvalₐ I J h n)
      = quotientMapEvalₐ I J h m := by
  ext y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (evalₐ I n y)
  have hm : evalₐ I m y = Ideal.Quotient.mk (I ^ m) x := by
    rw [← factorPow_evalₐ I hle y, ← hx, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  simp only [RingHom.coe_comp, Function.comp_apply, quotientMapEvalₐ_apply]
  rw [hm, ← hx, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]

/-- The ring map `AdicCompletion I A → AdicCompletion J B` induced by `algebraMap A B`, for an
ideal `I` of `A` whose image is contained in the ideal `J` of `B`. -/
noncomputable def mapAdicCompletion {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (J : Ideal B) (h : Ideal.map (algebraMap A B) I ≤ J) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J (quotientMapEvalₐ I J h)
    (fun hle => factorPow_comp_quotientMapEvalₐ I J h hle)

/-- The `n`-th component of `mapAdicCompletion I J h y` is the image under
`A ⧸ I ^ n → B ⧸ J ^ n` of the `n`-th component of `y`. -/
theorem evalₐ_mapAdicCompletion {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {I : Ideal A} {J : Ideal B} (h : Ideal.map (algebraMap A B) I ≤ J) (n : ℕ)
    (y : AdicCompletion I A) :
    evalₐ J n (mapAdicCompletion I J h y) =
      Ideal.quotientMap (J ^ n) (algebraMap A B) (pow_le_comap_pow h n) (evalₐ I n y) :=
  AdicCompletion.evalₐ_liftRingHom J (quotientMapEvalₐ I J h)
    (fun hle => factorPow_comp_quotientMapEvalₐ I J h hle) n y

/-- `mapAdicCompletion I J h` is compatible with the canonical maps `A → A^` and `B → B^`. -/
theorem mapAdicCompletion_of {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {I : Ideal A} {J : Ideal B} (h : Ideal.map (algebraMap A B) I ≤ J) (x : A) :
    mapAdicCompletion I J h (algebraMap A (AdicCompletion I A) x) =
      algebraMap B (AdicCompletion J B) (algebraMap A B x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_mapAdicCompletion]
  show Ideal.quotientMap (J ^ n) (algebraMap A B) _ (evalₐ I n (of I A x)) =
    evalₐ J n (of J B (algebraMap A B x))
  rw [evalₐ_of, evalₐ_of, Ideal.quotientMap_mk]

/-! ### Divisibility descends from the completion -/

/-- If `b = α * c` in the completion of a local ring `A`, with `b, c ∈ A`, then `c ∣ b` in `A`.
This is the faithful flatness of `A → A^` in the only case the argument uses; the proof is Krull's
intersection theorem for the `A`-module `A ⧸ cA`. -/
private theorem dvd_of_algebraMap_adicCompletion_eq {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {b c : A} {α : AdicCompletion (maximalIdeal A) A}
    (h : algebraMap A (AdicCompletion (maximalIdeal A) A) b =
      α * algebraMap A (AdicCompletion (maximalIdeal A) A) c) : c ∣ b := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine IsHausdorff.haus
    (inferInstance : IsHausdorff (maximalIdeal A) (A ⧸ Ideal.span {c})) _ fun n => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) n α)
  have hn : b - x * c ∈ maximalIdeal A ^ n := by
    have h' := congrArg (evalₐ (maximalIdeal A) n) h
    rw [show algebraMap A (AdicCompletion (maximalIdeal A) A) b = of _ A b from rfl,
      show algebraMap A (AdicCompletion (maximalIdeal A) A) c = of _ A c from rfl,
      evalₐ_of, map_mul, evalₐ_of, ← hx] at h'
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, h']
    ring
  rw [SModEq.zero]
  have hb : (Ideal.Quotient.mk (Ideal.span {c})) b
      = (b - x * c) • (1 : A ⧸ Ideal.span {c}) := by
    have hc : algebraMap A (A ⧸ Ideal.span {c}) (x * c) = 0 := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self c)
    rw [Algebra.smul_def, mul_one, map_sub, hc, sub_zero]
    rfl
  rw [hb]
  exact Submodule.smul_mem_smul hn Submodule.mem_top

/-! ### The ring `B = A[X] ⧸ (X ^ p - a)` -/

/-- The root of `X ^ p - a` in `A[X] ⧸ (X ^ p - a)` is a `p`-th root of `a`. -/
theorem root_pow_eq {A : Type*} [CommRing A] {p : ℕ} (a : A) :
    (AdjoinRoot.root (X ^ p - C a)) ^ p = algebraMap A (AdjoinRoot (X ^ p - C a)) a := by
  have h : AdjoinRoot.mk (X ^ p - C a) (X ^ p - C a) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact h

/-- `A → A[X] ⧸ (X ^ p - a)` is injective: a constant polynomial divisible by a polynomial of
positive degree is zero. -/
theorem algebraMap_adjoinRoot_injective {A : Type*} [CommRing A] [IsDomain A] {p : ℕ}
    (hp : p ≠ 0) (a : A) :
    Function.Injective (algebraMap A (AdjoinRoot (X ^ p - C a))) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at hx
  have hlt : (C x).degree < (X ^ p - C a).degree := by
    rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.pos_of_ne_zero hp)
  simpa using eq_zero_of_dvd_of_degree_lt hx hlt

/-- `A[X] ⧸ (X ^ p - a)` has characteristic `p` when `A` does. -/
private theorem charP_adjoinRoot {A : Type*} [CommRing A] [IsDomain A] {p : ℕ} [CharP A p]
    (hp : p ≠ 0) (a : A) : CharP (AdjoinRoot (X ^ p - C a)) p :=
  charP_of_injective_algebraMap (algebraMap_adjoinRoot_injective hp a) p

/-- The completion of a Noetherian local ring of characteristic `p` has characteristic `p`. -/
private theorem charP_adicCompletion {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {p : ℕ} [CharP A p] : CharP (AdicCompletion (maximalIdeal A) A) p :=
  charP_of_injective_algebraMap (AdicCompletion.of_injective (maximalIdeal A) A) p

/-- If `b ^ p` comes from a unit `u` of `A`, then `b` is a unit. -/
private theorem isUnit_of_pow_eq_algebraMap {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {p : ℕ} (hp : p ≠ 0) {b : B} {u : A} (hu : b ^ p = algebraMap A B u) (h : IsUnit u) :
    IsUnit b :=
  (isUnit_pow_iff hp).mp (by rw [hu]; exact h.map _)

/-- Characteristic `p`: the `p`-th power of an element of `A[X] ⧸ (X ^ p - a)` lies in `A`. -/
theorem exists_pow_eq_algebraMap {A : Type*} [CommRing A] [IsDomain A] {p : ℕ}
    [Fact p.Prime] [CharP A p] (a : A) (b : AdjoinRoot (X ^ p - C a)) :
    ∃ x : A, b ^ p = algebraMap A (AdjoinRoot (X ^ p - C a)) x := by
  have := charP_adjoinRoot (Fact.out : p.Prime).ne_zero a
  have hb : b ∈ Algebra.adjoin A ({AdjoinRoot.root (X ^ p - C a)} : Set _) := by
    rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨a, by rw [hy]; exact root_pow_eq a⟩
  | algebraMap y => exact ⟨y ^ p, by rw [map_pow]⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, hu⟩ := hy
    obtain ⟨v, hv⟩ := hz
    exact ⟨u + v, by rw [add_pow_char, hu, hv, map_add]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, hu⟩ := hy
    obtain ⟨v, hv⟩ := hz
    exact ⟨u * v, by rw [mul_pow, hu, hv, map_mul]⟩

/-- An element of `A` is a unit if and only if it is one in `A[X] ⧸ (X ^ p - a)`. -/
theorem isUnit_algebraMap_iff {A : Type*} [CommRing A] [IsDomain A] {p : ℕ}
    [Fact p.Prime] [CharP A p] (a : A) (x : A) :
    IsUnit (algebraMap A (AdjoinRoot (X ^ p - C a)) x) ↔ IsUnit x := by
  refine ⟨fun hx => ?_, fun hx => hx.map _⟩
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨v, hv⟩ := exists_pow_eq_algebraMap a y
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h : algebraMap A (AdjoinRoot (X ^ p - C a)) (x ^ p * v) =
      algebraMap A (AdjoinRoot (X ^ p - C a)) 1 := by
    rw [map_mul, map_pow, ← hv, map_one, ← mul_pow, hy, one_pow]
  have h1 : x ^ p * v = 1 := algebraMap_adjoinRoot_injective hp a h
  exact (isUnit_pow_iff hp).mp (isUnit_iff_exists_inv.mpr ⟨v, h1⟩)

/-- `A[X] ⧸ (X ^ p - a)` is a local ring: its nonunits are the `b` with `b ^ p ∈ 𝔪`. -/
theorem isLocalRing_adjoinRoot {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    {p : ℕ} [Fact p.Prime] [CharP A p] (a : A) : IsLocalRing (AdjoinRoot (X ^ p - C a)) := by
  have : Nontrivial (AdjoinRoot (X ^ p - C a)) :=
    (algebraMap_adjoinRoot_injective (Fact.out : p.Prime).ne_zero a).nontrivial
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have := charP_adjoinRoot hp a
  refine IsLocalRing.of_nonunits_add fun b c hb hc hbc => ?_
  obtain ⟨u, hu⟩ := exists_pow_eq_algebraMap a b
  obtain ⟨v, hv⟩ := exists_pow_eq_algebraMap a c
  have hu' : ¬ IsUnit u := fun h => hb (isUnit_of_pow_eq_algebraMap hp hu h)
  have hv' : ¬ IsUnit v := fun h => hc (isUnit_of_pow_eq_algebraMap hp hv h)
  have huv : IsUnit (u + v) := by
    rw [← isUnit_algebraMap_iff a, map_add, ← hu, ← hv, ← add_pow_char]
    exact hbc.pow p
  exact (mem_maximalIdeal (u + v)).mp
    (Ideal.add_mem _ ((mem_maximalIdeal u).mpr hu') ((mem_maximalIdeal v).mpr hv')) huv

/-- The root of `X ^ p - a` is not congruent to an element of `A` modulo `𝔪 * B`: the coefficient
of `β` in the canonical representative of degree `< p` is `1`, a unit. -/
theorem root_sub_algebraMap_notMem {A : Type*} [CommRing A] [IsLocalRing A] {p : ℕ}
    (hp : 1 < p) (a : A) (x : A) :
    AdjoinRoot.root (X ^ p - C a) - algebraMap A (AdjoinRoot (X ^ p - C a)) x ∉
      Ideal.map (algebraMap A (AdjoinRoot (X ^ p - C a))) (maximalIdeal A) := by
  intro hmem
  have hmon : (X ^ p - C a).Monic := monic_X_pow_sub_C a (by omega)
  have hdegg : (X ^ p - C a).degree = (p : WithBot ℕ) := degree_X_pow_sub_C (by omega) a
  -- the `β`-coordinate, an `A`-linear map `B → A`
  set c1 : AdjoinRoot (X ^ p - C a) →ₗ[A] A :=
    (Polynomial.lcoeff A 1).comp (AdjoinRoot.modByMonicHom hmon) with hc1
  have hmod : ∀ q : A[X], q.degree < (p : WithBot ℕ) → q %ₘ (X ^ p - C a) = q := fun q hq =>
    (Polynomial.modByMonic_eq_self_iff hmon).2 (hdegg ▸ hq)
  have hroot : c1 (AdjoinRoot.root (X ^ p - C a)) = 1 := by
    rw [hc1, ← AdjoinRoot.mk_X, LinearMap.comp_apply, AdjoinRoot.modByMonicHom_mk,
      hmod _ (by rw [degree_X]; exact_mod_cast hp)]
    simp
  have hconst : ∀ y : A, c1 (algebraMap A (AdjoinRoot (X ^ p - C a)) y) = 0 := by
    intro y
    rw [hc1, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, LinearMap.comp_apply,
      AdjoinRoot.modByMonicHom_mk,
      hmod _ (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hp.le))]
    simp
  have hmm : c1 (AdjoinRoot.root (X ^ p - C a) -
      algebraMap A (AdjoinRoot (X ^ p - C a)) x) ∈ maximalIdeal A := by
    have hy : AdjoinRoot.root (X ^ p - C a) - algebraMap A (AdjoinRoot (X ^ p - C a)) x
        ∈ (maximalIdeal A • (⊤ : Submodule A (AdjoinRoot (X ^ p - C a)))) := by
      rw [Ideal.smul_top_eq_map]
      exact hmem
    refine Submodule.smul_induction_on hy (fun r hr z _ => ?_) (fun y z hy hz => ?_)
    · rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    · rw [map_add]
      exact Ideal.add_mem _ hy hz
  rw [map_sub, hroot, hconst, sub_zero] at hmm
  exact (notMem_maximalIdeal.mpr isUnit_one) hmm

/-- Division with remainder by a monic polynomial can be carried out over `A` itself, so a
polynomial over a domain `A` which becomes divisible by a monic `f` over the fraction field is
divisible by `f` over `A`. -/
theorem dvd_of_map_dvd_map {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {f g : A[X]} (hf : f.Monic)
    (h : f.map (algebraMap A K) ∣ g.map (algebraMap A K)) : f ∣ g := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hf]
  have hinj : Function.Injective (algebraMap A K) := FaithfulSMul.algebraMap_injective A K
  have hr : f.map (algebraMap A K) ∣ (g %ₘ f).map (algebraMap A K) := by
    rw [eq_sub_of_add_eq (Polynomial.modByMonic_add_div g f), Polynomial.map_sub,
      Polynomial.map_mul]
    exact dvd_sub h (Dvd.intro _ rfl)
  have hdeg : ((g %ₘ f).map (algebraMap A K)).degree < (f.map (algebraMap A K)).degree := by
    rw [hf.degree_map]
    exact lt_of_le_of_lt Polynomial.degree_map_le (Polynomial.degree_modByMonic_lt g hf)
  exact Polynomial.map_injective _ hinj
    (by simpa using Polynomial.eq_zero_of_dvd_of_degree_lt hr hdeg)

/-- A monic polynomial over a domain `A` which is irreducible over the fraction field `K` has
`A[X] ⧸ (f)` a domain: that ring injects into the field `K[X] ⧸ (f)`. -/
theorem isDomain_adjoinRoot_of_monic {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] {f : A[X]} (hf : f.Monic)
    (hirr : Irreducible (f.map (algebraMap A K))) : IsDomain (AdjoinRoot f) := by
  have hfact : Fact (Irreducible (f.map (algebraMap A K))) := ⟨hirr⟩
  set L := AdjoinRoot (f.map (algebraMap A K)) with hL
  have heval : eval₂ (algebraMap A L) (AdjoinRoot.root (f.map (algebraMap A K))) f = 0 := by
    have h0 := AdjoinRoot.eval₂_root (f.map (algebraMap A K))
    rwa [Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq A K L] at h0
  set Φ := AdjoinRoot.lift (algebraMap A L) (AdjoinRoot.root (f.map (algebraMap A K))) heval
    with hΦ
  have key : ∀ g : A[X], Φ (AdjoinRoot.mk f g) =
      AdjoinRoot.mk (f.map (algebraMap A K)) (g.map (algebraMap A K)) := by
    intro g
    conv_rhs => rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
    rw [hΦ, AdjoinRoot.lift_mk]
  refine Function.Injective.isDomain Φ ?_
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
  rw [key g, AdjoinRoot.mk_eq_zero] at hy
  rw [AdjoinRoot.mk_eq_zero]
  exact dvd_of_map_dvd_map hf hy

/-- `A[X] ⧸ (X ^ p - a)` is a domain when `a` is not a `p`-th power in the fraction field: then
`X ^ p - a` is irreducible over the fraction field. -/
theorem isDomain_adjoinRoot {A : Type*} [CommRing A] [IsDomain A] {p : ℕ} [Fact p.Prime]
    (a : A) (hK : ∀ y : FractionRing A, y ^ p ≠ algebraMap A (FractionRing A) a) :
    IsDomain (AdjoinRoot (X ^ p - C a)) := by
  have hp : p.Prime := Fact.out
  refine isDomain_adjoinRoot_of_monic (K := FractionRing A) (monic_X_pow_sub_C a hp.ne_zero) ?_
  have hmap : (X ^ p - C a).map (algebraMap A (FractionRing A))
      = X ^ p - C (algebraMap A (FractionRing A) a) := by
    simp
  rw [hmap]
  exact X_pow_sub_C_irreducible_of_prime hp hK

/-! ### The fraction field has no `p`-th root either -/

private theorem forall_pow_ne_fractionRing {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] {p : ℕ} [Fact p.Prime] [CharP A p]
    [IsReduced (AdicCompletion (maximalIdeal A) A)] {a : A}
    {α : AdicCompletion (maximalIdeal A) A}
    (hα : α ^ p = algebraMap A (AdicCompletion (maximalIdeal A) A) a)
    (hcon : ∀ b : A, b ^ p ≠ a) (y : FractionRing A) :
    y ^ p ≠ algebraMap A (FractionRing A) a := by
  have : CharP (AdicCompletion (maximalIdeal A) A) p := charP_adicCompletion
  intro hy
  obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors A) y
  have hc0 : (c : A) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have h1 : b ^ p = a * (c : A) ^ p := by
    refine FaithfulSMul.algebraMap_injective A (FractionRing A) ?_
    rw [map_pow, ← hbc, mul_pow, hy, map_mul, map_pow]
  have h2 : algebraMap A (AdicCompletion (maximalIdeal A) A) b =
      α * algebraMap A (AdicCompletion (maximalIdeal A) A) (c : A) := by
    refine sub_eq_zero.mp (IsNilpotent.eq_zero ⟨p, ?_⟩)
    rw [sub_pow_char, ← map_pow, h1, mul_pow, hα, map_mul, map_pow, sub_self]
  obtain ⟨d, hd⟩ := dvd_of_algebraMap_adicCompletion_eq h2
  refine hcon d ?_
  have hcd : ((c : A) * d) ^ p = (c : A) ^ p * a := by rw [← hd, h1, mul_comm]
  rw [mul_pow] at hcd
  exact mul_left_cancel₀ (pow_ne_zero p hc0) hcd

/-! ### A `p`-th root in the completion makes the completion of `A[X] ⧸ (X ^ p - a)` nonreduced -/

/-- **A `p`-th root in the completion gives a nonreduced completion.** Let `(A, 𝔪)` be a
Noetherian local domain of characteristic a prime `p` and let `a ∈ A` have a `p`-th root `α` in
the completion `A^`. Then the completion of the local ring `B = A[X] ⧸ (X ^ p - a)` is not
reduced: the difference `β - α` of the two `p`-th roots of `a` in `B^` is a nonzero element whose
`p`-th power is zero. It is nonzero because `𝔫 ^ N ⊆ 𝔪B` for some `N`, while the root `β` of
`X ^ p - a` does not lie in `A + 𝔪B`. -/
public theorem _root_.AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq {A : Type*} [CommRing A]
    [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] {p : ℕ} [Fact p.Prime] [CharP A p] {a : A}
    [IsLocalRing (AdjoinRoot (X ^ p - C a))] {α : AdicCompletion (maximalIdeal A) A}
    (hα : α ^ p = algebraMap A (AdicCompletion (maximalIdeal A) A) a) :
    ¬ IsReduced (AdicCompletion (maximalIdeal (AdjoinRoot (X ^ p - C a)))
      (AdjoinRoot (X ^ p - C a))) := by
  intro hBred
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have := charP_adjoinRoot hp a
  have : CharP (AdicCompletion (maximalIdeal (AdjoinRoot (X ^ p - C a)))
      (AdjoinRoot (X ^ p - C a))) p := charP_adicCompletion
  -- `𝔪` maps into `𝔫`, and `𝔫 ^ N ⊆ 𝔪 * B`
  have hmap : Ideal.map (algebraMap A (AdjoinRoot (X ^ p - C a))) (maximalIdeal A) ≤
      maximalIdeal (AdjoinRoot (X ^ p - C a)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_algebraMap_iff]
    exact (mem_maximalIdeal x).mp hx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (J := Ideal.map (algebraMap A (AdjoinRoot (X ^ p - C a))) (maximalIdeal A))
    (fun b hb => by
      refine ⟨p, ?_⟩
      obtain ⟨u, hu⟩ := exists_pow_eq_algebraMap a b
      rw [hu]
      refine Ideal.mem_map_of_mem _ ?_
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact fun hunit => ((mem_maximalIdeal b).mp hb) (isUnit_of_pow_eq_algebraMap hp hu hunit))
    (IsNoetherian.noetherian (maximalIdeal (AdjoinRoot (X ^ p - C a))))
  -- the nilpotent element of `B^`
  set ψ := mapAdicCompletion (maximalIdeal A) (maximalIdeal (AdjoinRoot (X ^ p - C a))) hmap
    with hψ
  set ν := algebraMap (AdjoinRoot (X ^ p - C a)) (AdicCompletion _ (AdjoinRoot (X ^ p - C a)))
    (AdjoinRoot.root (X ^ p - C a)) - ψ α with hν
  have hν0 : ν = 0 := by
    refine IsNilpotent.eq_zero ⟨p, ?_⟩
    rw [hν, sub_pow_char, ← map_pow, root_pow_eq, ← map_pow, hα, hψ, mapAdicCompletion_of,
      sub_self]
  -- evaluate at level `N` to contradict the basis
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) N α)
  have hcongr := congrArg (evalₐ (maximalIdeal (AdjoinRoot (X ^ p - C a))) N) hν0
  rw [hν, map_sub, hψ, evalₐ_mapAdicCompletion, ← hx, Ideal.quotientMap_mk, _root_.map_zero,
    sub_eq_zero] at hcongr
  refine root_sub_algebraMap_notMem (Fact.out : p.Prime).one_lt a x (hN ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact hcongr

/-! ### `p`-th roots descend from the completion -/

/-- An element `a` of a Nagata local domain `A` of characteristic `p ≠ 0` is a `p`-th power in
`A` if and only if it is a `p`-th power in the completion of `A`. -/
public theorem solution {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    (hA : IsNagataRing A) {p : ℕ} [CharP A p] (hp : p ≠ 0) (a : A) :
    (∃ b : A, b ^ p = a) ↔
      ∃ α : AdicCompletion (IsLocalRing.maximalIdeal A) A,
        α ^ p = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a := by
  refine ⟨fun ⟨b, hb⟩ => ⟨algebraMap A (AdicCompletion (maximalIdeal A) A) b, by
    rw [← map_pow, hb]⟩, ?_⟩
  rintro ⟨α, hα⟩
  have : IsNoetherianRing A := hA.1
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero A p).resolve_right hp⟩
  have hred : IsReduced (AdicCompletion (maximalIdeal A) A) :=
    IsAnalyticallyUnramified.of_isNagataRing hA
  by_contra hcon
  rw [not_exists] at hcon
  -- the fraction field has no `p`-th root of `a` either
  have hK := forall_pow_ne_fractionRing hα hcon
  -- so `B` is a Nagata local domain, hence analytically unramified
  have : IsDomain (AdjoinRoot (X ^ p - C a)) := isDomain_adjoinRoot a hK
  have : IsLocalRing (AdjoinRoot (X ^ p - C a)) := isLocalRing_adjoinRoot a
  have hfin := ((isNagataRing_tfae (R := A)).out 1 2).mp hA
  have hBnag : IsNagataRing (AdjoinRoot (X ^ p - C a)) := hfin (AdjoinRoot (X ^ p - C a))
  exact AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq hα
    (IsAnalyticallyUnramified.of_isNagataRing hBnag)

end Stacks.Nagata.PthRootDescent

/-- **Stacks Tag 09E2.** Let `(A, 𝔪)` be a local domain which is a Nagata ring and has
characteristic `p ≠ 0`, and let `A^ = lim_n A ⧸ 𝔪ⁿ` be its completion. An element `a : A` has a
`p`-th root in `A` if and only if it has one in `A^`.

The source also assumes `A` Noetherian, which is the first conjunct of `IsNagataRing A`, and
assumes `p` prime, which follows from `p ≠ 0` because `A` is a domain. The source's
characteristic assumption is on the fraction field of `A`; that is the same condition as
`CharP A p`. -/
@[stacks 09E2 "Stated as a biconditional, the reverse implication being `map_pow` on the \
  completion map. Noetherian is absorbed into `IsNagataRing` (Definition 032R(2)), primality of \
  `p` into `p ≠ 0` over a domain (`CharP.char_is_prime_or_zero`), and the characteristic of \
  `Frac A` is read off `A`. The completion is `AdicCompletion (maximalIdeal A) A` as in Tag 032X."]
public theorem IsNagataRing.exists_pow_eq_iff_exists_pow_eq_adicCompletion {A : Type*}
    [CommRing A] [IsLocalRing A] [IsDomain A] (hA : IsNagataRing A) {p : ℕ} [CharP A p]
    (hp : p ≠ 0) (a : A) :
    (∃ b : A, b ^ p = a) ↔
      ∃ α : AdicCompletion (IsLocalRing.maximalIdeal A) A,
        α ^ p = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a :=
          Stacks.Nagata.PthRootDescent.solution (A := A) (p := p) hA hp a

end
