module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import StacksCore.Tactic.StacksAttribute

/-!
# Annihilators along an exact sequence, before and after reduction modulo an ideal

Let `T → M → N → Q` be an exact sequence of modules over a commutative ring and let `I` be an
ideal annihilating `T` and `Q`. Two elements `f, g ∈ I` then determine a canonical linear map
`N → M`: lift `f • y` to `M` and multiply the lift by `g`. The lift is only unique up to the
image of `T`, and multiplying by `g` kills that ambiguity, so the construction is well defined
and its composite with `M → N` is multiplication by `f * g`.

This has the following consequence for reduction modulo an arbitrary ideal `J`. If a power
`K ^ t` annihilates the two end modules of an exact sequence `0 → T → M → N → Q → 0`, then
`K ^ (2 * t)` annihilates both the kernel and the cokernel of the induced map
`M / J M → N / J N`.

Conversely, for a map `φ : M → N` of `I`-adically complete modules the annihilation of the
kernels and cokernels of all the reductions `M / Iⁿ M → N / Iⁿ N` by one power of `K` recovers
the annihilation of `Ker(φ)` and `Coker(φ)` by a power of `K`: the lift-and-multiply maps
`N / Iⁿ N → M / Iⁿ M` are compatible, so for `f, g ∈ K ^ t` the lifts of `f • y` have
`I`-adically convergent `g`-multiples, whose limit is a preimage of `(f * g) • y`. The two
conditions are therefore equivalent, which is the content of the remarks of Tags 0888 and
08BA.

## Main results

* `Ideal.existsUnique_canonicalMap_of_smul_eq_bot` constructs the lift-and-multiply map and
  identifies its composite with the middle map of the sequence.
* `Ideal.pow_le_annihilator_ker_mapQ_of_exact` annihilates the kernel after reduction.
* `Ideal.pow_le_annihilator_coker_mapQ_of_exact` annihilates the cokernel after reduction.
* `Ideal.pow_le_annihilator_ker_of_forall_mapQ_pow` and
  `Ideal.pow_le_annihilator_coker_of_forall_mapQ_pow` recover the annihilation of the kernel
  and of the cokernel of `φ` from that of the reductions modulo the powers of `I`.
* `Ideal.exists_pow_le_annihilator_ker_and_coker_mapQ_pow_iff` is the resulting equivalence of
  the two annihilation conditions.

## Implementation notes

Only exactness at the two middle terms of the five-term sequence is used, so
`Ideal.existsUnique_canonicalMap_of_smul_eq_bot` is stated for an arbitrary annihilating ideal
`I` rather than for the power `K ^ t` of the source; that makes it applicable to `K ^ t`
directly. The quotients `M / J M` and `N / J N` are represented as quotients by `J • ⊤`, and
their canonical map is `Submodule.mapQ`; the cokernel is the quotient of the target by the
range of that map. The two conclusions of the source are independent and are stated separately.

In the converse direction the family of reductions is indexed by `n : ℕ` and taken modulo
`I ^ (n + 1)`, so its term at `n` is the source's reduction modulo `Iⁿ⁺¹`; the reduction
modulo `I ^ 0` is the zero map and carries no information. The completeness assumptions are
`IsAdicComplete I M` and `IsHausdorff I N`, which is what the limit argument uses: the
kernel statement needs only that `M` is `I`-adically separated, the cokernel statement needs
that `M` is precomplete and that `N` is separated. The source applies this with the ring the
`I`-adic completion of a Noetherian ring and `M`, `N` finite modules over it, which are
`I`-adically complete; annihilation by a power of an ideal of the base is unchanged by passing
to the completion, so no separate hypothesis records that the ideals come from the base.

These statements are about modules over a commutative ring rather than about schemes, so they
live in the `Ideal` namespace.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 08BA](https://stacks.math.columbia.edu/tag/08BA)
-/

@[expose] public section

universe u vT vM vN vQ

namespace Ideal

variable {A : Type u} [CommRing A]
  {T : Type vT} {M : Type vM} {N : Type vN} {Q : Type vQ}
  [AddCommGroup T] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
  [Module A T] [Module A M] [Module A N] [Module A Q]

private lemma smul_eq_zero_of_mem_smul_top_eq_bot {X : Type*} [AddCommGroup X] [Module A X]
    {I : Ideal A} (hI : I • (⊤ : Submodule A X) = ⊥) {c : A} (hc : c ∈ I) (x : X) :
    c • x = 0 := by
  simpa only [hI, Submodule.mem_bot] using
    (Submodule.smul_mem_smul hc (Submodule.mem_top : x ∈ (⊤ : Submodule A X)))

private lemma eq_smul_of_eq_smul_of_exact
    (i : T →ₗ[A] M) (a : M →ₗ[A] N) (hia : Function.Exact i a)
    {f g : A} {y : N} {x x' : M} (hx : a x = f • y) (hx' : a x' = f • y)
    {I : Ideal A} (hT : I • (⊤ : Submodule A T) = ⊥) (hg : g ∈ I) :
    g • x = g • x' := by
  obtain ⟨t, ht⟩ := (hia (x - x')).mp (by simp [map_sub, hx, hx'])
  apply sub_eq_zero.mp
  rw [← smul_sub, ← ht, ← map_smul, smul_eq_zero_of_mem_smul_top_eq_bot hT hg t, map_zero]

private lemma smul_top_eq_bot_of_le_annihilator {X : Type*} [AddCommGroup X] [Module A X]
    {I : Ideal A} (h : I ≤ Module.annihilator A X) : I • (⊤ : Submodule A X) = ⊥ :=
  le_antisymm (Submodule.smul_le.2 fun _ hr x _ => Module.mem_annihilator.mp (h hr) x) bot_le

/-- If all products `f * g` with `f, g ∈ K ^ t` kill `X`, then `K ^ (2 * t)` annihilates `X`. -/
private lemma pow_two_mul_le_annihilator {X : Type*} [AddCommGroup X] [Module A X] (K : Ideal A)
    (t : ℕ) (h : ∀ f ∈ K ^ t, ∀ g ∈ K ^ t, ∀ z : X, (f * g) • z = 0) :
    K ^ (2 * t) ≤ Module.annihilator A X := by
  rw [two_mul, pow_add, Ideal.mul_le]
  exact fun f hf g hg => Module.mem_annihilator.mpr (h f hf g hg)

/-- **Stacks Project, Tag 0888.** In an exact sequence whose two end modules are annihilated by
an ideal `I`, elements `f, g ∈ I` determine a unique linear map `N → M`. Its value at `y` is
`g • x` for any lift `x` of `f • y`, and its composite with `M → N` is multiplication by
`f * g`. -/
@[stacks 0888 "canonical_fg_map"]
theorem existsUnique_canonicalMap_of_smul_eq_bot
    (i : T →ₗ[A] M) (a : M →ₗ[A] N) (q : N →ₗ[A] Q)
    (hia : Function.Exact i a) (haq : Function.Exact a q)
    (I : Ideal A)
    (hT : I • (⊤ : Submodule A T) = ⊥)
    (hQ : I • (⊤ : Submodule A Q) = ⊥)
    {f g : A} (hf : f ∈ I) (hg : g ∈ I) :
    ∃! b : N →ₗ[A] M,
      (∀ (y : N) (x : M), a x = f • y → b y = g • x) ∧
        b.comp a = LinearMap.lsmul A M (f * g) := by
  have hLift (y : N) : ∃ x : M, a x = f • y :=
    (haq (f • y)).mp (by simpa only [map_smul] using
      smul_eq_zero_of_mem_smul_top_eq_bot hQ hf (q y))
  choose x hx using hLift
  have hcompat {y : N} {u v : M} (hu : a u = f • y) (hv : a v = f • y) :
      g • u = g • v := eq_smul_of_eq_smul_of_exact i a hia hu hv hT hg
  let b : N →ₗ[A] M :=
    { toFun := fun y => g • x y
      map_add' := by
        intro y z
        rw [← smul_add]
        exact hcompat (hx _) (by simp [map_add, hx, smul_add])
      map_smul' := by
        intro c y
        change g • x (c • y) = c • (g • x y)
        rw [smul_comm c g]
        exact hcompat (hx _) (by simp [map_smul, hx, smul_smul, mul_comm]) }
  refine ⟨b, ⟨fun y z hz => (hcompat hz (hx y)).symm, ?_⟩, fun c hc => ?_⟩
  · ext z
    change g • x (a z) = (f * g) • z
    calc
      g • x (a z) = g • (f • z) := hcompat (hx _) (by rw [map_smul])
      _ = (f * g) • z := by rw [smul_comm, smul_smul]
  · ext y
    exact hc.1 y (x y) (hx y)

/-- **Stacks Project, Tag 0888.** In an exact five-term sequence whose end modules are
annihilated by `K ^ t`, the power `K ^ (2 * t)` annihilates the kernel of the map induced after
reduction modulo any ideal `J`. -/
@[stacks 0888 "annihilation_mod_ideal"]
lemma pow_le_annihilator_ker_mapQ_of_exact
    (i : T →ₗ[A] M) (a : M →ₗ[A] N) (q : N →ₗ[A] Q)
    (_hi : Function.Injective i) (hia : Function.Exact i a)
    (haq : Function.Exact a q) (_hq : Function.Surjective q)
    (K : Ideal A) (t : ℕ) (_ht : 0 < t)
    (hT : K ^ t ≤ Module.annihilator A T)
    (hQ : K ^ t ≤ Module.annihilator A Q) (J : Ideal A) :
    K ^ (2 * t) ≤ Module.annihilator A
      ↑(LinearMap.ker (Submodule.mapQ (J • (⊤ : Submodule A M))
        (J • (⊤ : Submodule A N)) a
        (Submodule.smul_top_le_comap_smul_top J a))) := by
  let P : Submodule A M := J • (⊤ : Submodule A M)
  let R : Submodule A N := J • (⊤ : Submodule A N)
  let hJ : P ≤ Submodule.comap a R := Submodule.smul_top_le_comap_smul_top J a
  refine pow_two_mul_le_annihilator K t fun f hf g hg => ?_
  obtain ⟨b, hb, hba⟩ :=
    existsUnique_canonicalMap_of_smul_eq_bot i a q hia haq (K ^ t)
      (smul_top_eq_bot_of_le_annihilator hT) (smul_top_eq_bot_of_le_annihilator hQ) hf hg
  have hbJ : R ≤ Submodule.comap b P := by
    refine Submodule.smul_le.2 (fun j hj y hy => ?_)
    rw [Submodule.mem_comap, b.map_smul]
    exact Submodule.smul_mem_smul hj Submodule.mem_top
  intro z
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective P z
  have hz : a x ∈ R := by
    apply (Submodule.Quotient.mk_eq_zero R).mp
    rw [← Submodule.mapQ_apply (h := hJ)]
    exact LinearMap.mem_ker.mp (hx.symm ▸ z.property)
  apply Subtype.ext
  change (f * g) • (z : M ⧸ P) = 0
  rw [← hx]
  calc
    (f * g) • Submodule.Quotient.mk x =
        Submodule.Quotient.mk ((f * g) • x) := (P.mkQ.map_smul _ _).symm
    _ = Submodule.Quotient.mk (b (a x)) :=
        congrArg Submodule.Quotient.mk (LinearMap.congr_fun hb.2 x).symm
    _ = 0 := (Submodule.Quotient.mk_eq_zero P).mpr (hbJ hz)

/-- **Stacks Project, Tag 0888.** In an exact five-term sequence whose end modules are
annihilated by `K ^ t`, the power `K ^ (2 * t)` annihilates the cokernel of the map induced
after reduction modulo any ideal `J`. -/
@[stacks 0888 "annihilation_mod_ideal"]
lemma pow_le_annihilator_coker_mapQ_of_exact
    (i : T →ₗ[A] M) (a : M →ₗ[A] N) (q : N →ₗ[A] Q)
    (_hi : Function.Injective i) (_hia : Function.Exact i a)
    (haq : Function.Exact a q) (_hq : Function.Surjective q)
    (K : Ideal A) (t : ℕ) (_ht : 0 < t)
    (_hT : K ^ t ≤ Module.annihilator A T)
    (hQ : K ^ t ≤ Module.annihilator A Q) (J : Ideal A) :
    K ^ (2 * t) ≤ Module.annihilator A
      (_ ⧸ LinearMap.range
        (Submodule.mapQ (J • (⊤ : Submodule A M)) (J • (⊤ : Submodule A N)) a
          (Submodule.smul_top_le_comap_smul_top J a))) := by
  let P : Submodule A M := J • (⊤ : Submodule A M)
  let R : Submodule A N := J • (⊤ : Submodule A N)
  let hJ : P ≤ Submodule.comap a R := Submodule.smul_top_le_comap_smul_top J a
  refine pow_two_mul_le_annihilator K t fun f hf g hg => ?_
  let c : M ⧸ P →ₗ[A] N ⧸ R := Submodule.mapQ P R a hJ
  intro z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (LinearMap.range c) z
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective R y
  have hfn : q ((f * g) • n) = 0 := by
    rw [q.map_smul, mul_smul, Module.mem_annihilator.mp (hQ hf)]
  obtain ⟨x, hx⟩ := (haq ((f * g) • n)).mp hfn
  have hcx : c (Submodule.Quotient.mk x) =
      (f * g) • Submodule.Quotient.mk n :=
    calc
      c (Submodule.Quotient.mk x) = Submodule.Quotient.mk (a x) :=
        Submodule.mapQ_apply P R a x
      _ = Submodule.Quotient.mk ((f * g) • n) := congrArg _ hx
      _ = (f * g) • Submodule.Quotient.mk n := (R.mkQ.map_smul _ _).symm
  rw [← hy]
  change (f * g) • (LinearMap.range c).mkQ y = 0
  rw [← (LinearMap.range c).mkQ.map_smul, ← hn, ← hcx]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (LinearMap.mem_range.mpr ⟨_, rfl⟩)

/-- An element annihilating the kernel of the reduction `M / J M → N / J N` of `φ` multiplies
every `x` with `φ x ∈ J N` into `J M`. -/
theorem smul_mem_smul_top_of_mem_annihilator_ker_mapQ (J : Ideal A) (φ : M →ₗ[A] N) {g : A}
    (hg : g ∈ Module.annihilator A ↑(LinearMap.ker (Submodule.mapQ (J • (⊤ : Submodule A M))
      (J • (⊤ : Submodule A N)) φ (Submodule.smul_top_le_comap_smul_top J φ))))
    {x : M} (hx : φ x ∈ J • (⊤ : Submodule A N)) : g • x ∈ J • (⊤ : Submodule A M) := by
  have hmem : Submodule.Quotient.mk (p := J • (⊤ : Submodule A M)) x ∈
      LinearMap.ker (Submodule.mapQ (J • (⊤ : Submodule A M)) (J • (⊤ : Submodule A N)) φ
        (Submodule.smul_top_le_comap_smul_top J φ)) := by
    rw [LinearMap.mem_ker, Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hzero : Submodule.Quotient.mk (p := J • (⊤ : Submodule A M)) (g • x) = 0 := by
    simpa [Submodule.Quotient.mk_smul] using
      congrArg Subtype.val (Module.mem_annihilator.mp hg ⟨_, hmem⟩)
  exact (Submodule.Quotient.mk_eq_zero _).mp hzero

/-- An element annihilating the cokernel of the reduction `M / J M → N / J N` of `φ` multiplies
every `y : N` into the image of `φ` modulo `J N`. -/
theorem exists_smodEq_smul_of_mem_annihilator_coker_mapQ (J : Ideal A) (φ : M →ₗ[A] N) {f : A}
    (hf : f ∈ Module.annihilator A (_ ⧸ LinearMap.range (Submodule.mapQ
      (J • (⊤ : Submodule A M)) (J • (⊤ : Submodule A N)) φ
      (Submodule.smul_top_le_comap_smul_top J φ)))) (y : N) :
    ∃ x : M, φ x ≡ f • y [SMOD J • (⊤ : Submodule A N)] := by
  have h0 := Module.mem_annihilator.mp hf
    (Submodule.Quotient.mk (p := LinearMap.range (Submodule.mapQ
      (J • (⊤ : Submodule A M)) (J • (⊤ : Submodule A N)) φ
      (Submodule.smul_top_le_comap_smul_top J φ)))
      (Submodule.Quotient.mk (p := J • (⊤ : Submodule A N)) y))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨w, hw⟩ := h0
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A M)) w
  refine ⟨x, ?_⟩
  rw [SModEq.def, Submodule.Quotient.mk_smul, ← hw]
  exact (Submodule.mapQ_apply (J • (⊤ : Submodule A M)) (J • (⊤ : Submodule A N)) φ x).symm

/-- For an `I`-adically separated module `M`, an ideal annihilating the kernel of every
reduction `M / Iⁿ⁺¹ M → N / Iⁿ⁺¹ N` of a linear map `φ : M → N` annihilates `Ker(φ)`:
a kernel element is killed modulo every power of `I`, hence killed. -/
theorem pow_le_annihilator_ker_of_forall_mapQ_pow (I K : Ideal A) [IsHausdorff I M]
    (φ : M →ₗ[A] N) (t : ℕ)
    (h : ∀ n : ℕ, K ^ t ≤ Module.annihilator A
      ↑(LinearMap.ker (Submodule.mapQ (I ^ (n + 1) • (⊤ : Submodule A M))
        (I ^ (n + 1) • (⊤ : Submodule A N)) φ
        (Submodule.smul_top_le_comap_smul_top _ φ)))) :
    K ^ t ≤ Module.annihilator A ↑(LinearMap.ker φ) := by
  intro f hf
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  change f • (x : M) = 0
  refine IsHausdorff.haus (I := I) ‹_› _ fun n => ?_
  have hx : φ x ∈ I ^ (n + 1) • (⊤ : Submodule A N) := by
    rw [LinearMap.mem_ker.mp x.2]
    exact zero_mem _
  exact SModEq.mono (Submodule.pow_smul_top_le I M (Nat.le_succ n))
    (SModEq.zero.mpr (smul_mem_smul_top_of_mem_annihilator_ker_mapQ _ φ (h n hf) hx))

/-- For a precomplete `M` and an `I`-adically separated `N`, if `K ^ t` annihilates the kernel
and the cokernel of every reduction `M / Iⁿ⁺¹ M → N / Iⁿ⁺¹ N` of a linear map `φ : M → N`, then
`K ^ (2 * t)` annihilates `Coker(φ)`: for `f, g ∈ K ^ t` and `y : N` the lifts `xₙ` of `f • y`
modulo `Iⁿ⁺¹` have `g • xₙ` `I`-adically Cauchy, and `φ` sends its limit to `(f * g) • y`. -/
theorem pow_le_annihilator_coker_of_forall_mapQ_pow (I K : Ideal A)
    [IsPrecomplete I M] [IsHausdorff I N] (φ : M →ₗ[A] N) (t : ℕ)
    (hker : ∀ n : ℕ, K ^ t ≤ Module.annihilator A
      ↑(LinearMap.ker (Submodule.mapQ (I ^ (n + 1) • (⊤ : Submodule A M))
        (I ^ (n + 1) • (⊤ : Submodule A N)) φ
        (Submodule.smul_top_le_comap_smul_top _ φ))))
    (hcoker : ∀ n : ℕ, K ^ t ≤ Module.annihilator A
      (_ ⧸ LinearMap.range (Submodule.mapQ (I ^ (n + 1) • (⊤ : Submodule A M))
        (I ^ (n + 1) • (⊤ : Submodule A N)) φ
        (Submodule.smul_top_le_comap_smul_top _ φ)))) :
    K ^ (2 * t) ≤ Module.annihilator A (N ⧸ LinearMap.range φ) := by
  refine pow_two_mul_le_annihilator K t fun f hf g hg z => ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (LinearMap.range φ) z
  choose x hx using fun n =>
    exists_smodEq_smul_of_mem_annihilator_coker_mapQ _ φ (hcoker n hf) y
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      g • x m ≡ g • x n [SMOD I ^ m • (⊤ : Submodule A M)] := by
    intro m n hmn
    refine SModEq.mono (Submodule.pow_smul_top_le I M (Nat.le_succ m)) ?_
    have hdiff : φ (x n - x m) ∈ I ^ (m + 1) • (⊤ : Submodule A N) := by
      rw [map_sub]
      exact SModEq.sub_mem.mp ((SModEq.mono
        (Submodule.pow_smul_top_le I N (Nat.add_le_add_right hmn 1)) (hx n)).trans (hx m).symm)
    rw [SModEq.sub_mem, ← smul_sub, ← neg_sub, smul_neg]
    exact neg_mem (smul_mem_smul_top_of_mem_annihilator_ker_mapQ _ φ (hker m hg) hdiff)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => g • x n) hcauchy
  have hlimit : φ L = (f * g) • y := by
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro n
    rw [SModEq.sub_mem]
    have h1 : φ (L - g • x n) ∈ I ^ n • (⊤ : Submodule A N) :=
      Submodule.mem_comap.mp (Submodule.smul_top_le_comap_smul_top (I ^ n) φ
        (SModEq.sub_mem.mp (hL n).symm))
    have h2 : g • (φ (x n) - f • y) ∈ I ^ n • (⊤ : Submodule A N) :=
      Submodule.smul_mem _ g (SModEq.sub_mem.mp
        (SModEq.mono (Submodule.pow_smul_top_le I N (Nat.le_succ n)) (hx n)))
    have heq : φ (L - g • x n) + g • (φ (x n) - f • y) = φ L - (f * g) • y := by
      rw [map_sub, map_smul, smul_sub, smul_smul, mul_comm g f]
      abel
    rw [← heq]
    exact add_mem h1 h2
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨L, hlimit⟩

/-- **Stacks Project, Tag 08BA.** For a linear map `φ : M → N` of `I`-adically complete
modules, one positive power of `K` annihilates the kernels and the cokernels of all the
reductions `M / Iⁿ⁺¹ M → N / Iⁿ⁺¹ N` if and only if one positive power of `K` annihilates
`Ker(φ)` and `Coker(φ)`. -/
@[stacks 08BA "equivalence of the annihilation conditions"]
theorem exists_pow_le_annihilator_ker_and_coker_mapQ_pow_iff (I K : Ideal A)
    [IsAdicComplete I M] [IsHausdorff I N] (φ : M →ₗ[A] N) :
    (∃ t : ℕ, 0 < t ∧ ∀ n : ℕ,
        K ^ t ≤ Module.annihilator A
          ↑(LinearMap.ker (Submodule.mapQ (I ^ (n + 1) • (⊤ : Submodule A M))
            (I ^ (n + 1) • (⊤ : Submodule A N)) φ
            (Submodule.smul_top_le_comap_smul_top _ φ))) ∧
        K ^ t ≤ Module.annihilator A
          (_ ⧸ LinearMap.range (Submodule.mapQ (I ^ (n + 1) • (⊤ : Submodule A M))
            (I ^ (n + 1) • (⊤ : Submodule A N)) φ
            (Submodule.smul_top_le_comap_smul_top _ φ)))) ↔
      ∃ t : ℕ, 0 < t ∧ K ^ t ≤ Module.annihilator A ↑(LinearMap.ker φ) ∧
        K ^ t ≤ Module.annihilator A (N ⧸ LinearMap.range φ) := by
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨2 * t, by omega, ?_, ?_⟩
    · exact (Ideal.pow_le_pow_right (by omega : t ≤ 2 * t)).trans
        (pow_le_annihilator_ker_of_forall_mapQ_pow I K φ t fun n => (h n).1)
    · exact pow_le_annihilator_coker_of_forall_mapQ_pow I K φ t (fun n => (h n).1)
        (fun n => (h n).2)
  · rintro ⟨t, ht, hT, hQ⟩
    refine ⟨2 * t, by omega, fun n => ⟨?_, ?_⟩⟩
    · exact pow_le_annihilator_ker_mapQ_of_exact (LinearMap.ker φ).subtype φ
        (LinearMap.range φ).mkQ (Submodule.injective_subtype _)
        (LinearMap.exact_subtype_ker_map φ) (LinearMap.exact_map_mkQ_range φ)
        (Submodule.mkQ_surjective _) K t ht hT hQ (I ^ (n + 1))
    · exact pow_le_annihilator_coker_mapQ_of_exact (LinearMap.ker φ).subtype φ
        (LinearMap.range φ).mkQ (Submodule.injective_subtype _)
        (LinearMap.exact_subtype_ker_map φ) (LinearMap.exact_map_mkQ_range φ)
        (Submodule.mkQ_surjective _) K t ht hT hQ (I ^ (n + 1))

end Ideal
