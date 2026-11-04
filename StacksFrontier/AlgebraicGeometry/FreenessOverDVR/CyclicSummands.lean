module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# Cyclic summands and surjectivity modulo a power of a uniformizer

Let `A` be a discrete valuation ring with uniformizer `π`. In the free module
`(A ⧸ (π ^ (e + 1))) ^ r` the annihilator of `π ^ e` is exactly `π · (A ⧸ (π ^ (e + 1))) ^ r`, so
Nakayama's lemma turns a submodule that generates together with some submodule annihilated by
`π ^ e` into the whole module. A second application of Nakayama lifts surjectivity onto
`(A ⧸ (π ^ (e + 1))) ^ r` to surjectivity onto `A ^ r`. Separately, over a Noetherian module a
single power of `π` annihilates all `π`-power torsion.

These are the module-theoretic ingredients of the last step of [Stacks, Tag 0EXF], in which `e` is
the largest exponent such that `A ⧸ (π ^ e)` occurs as a cyclic summand of a cohomology module of
the structure sheaf.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `mem_span_singleton_smul_top_of_pow_smul_eq_zero`: in `(A ⧸ (π ^ (e + 1))) ^ r` over a domain,
  an element annihilated by `π ^ e` is divisible by `π`.
* `eq_top_of_sup_eq_top_of_pow_smul_eq_bot`: a submodule of `(A ⧸ (π ^ (e + 1))) ^ r` that
  generates together with a submodule annihilated by `π ^ e` is the whole module.
* `range_eq_top_of_sup_pow_smul_top_eq_top`: a linear map into a finite module `N` whose image
  generates together with `π ^ (e + 1) N` is surjective.
* `range_eq_top_of_sup_range_mkQ_comp_eq_top`: a map `M → A ^ r` which becomes surjective modulo
  `π ^ (e + 1)` after adjoining a submodule annihilated by `π ^ e` is already surjective.
* `exists_forall_pow_smul_torsionBy_eq_bot`: one power of `π` annihilates `H[π ^ m]` for every
  `m`, when `H` is a Noetherian module.

## Implementation notes

Freeness over `A ⧸ (π ^ (e + 1))` cannot be dropped from
`eq_top_of_sup_eq_top_of_pow_smul_eq_bot`: for a general finite module annihilated by
`π ^ (e + 1)`, say `A ⧸ (π ^ l)` with `l ≤ e`, the element `π ^ e` annihilates everything, so
taking `T = ⊤` and `S = ⊥` would contradict the conclusion. The free module is spelled
`Fin r → A ⧸ Ideal.span {π} ^ (e + 1)`, and reduction modulo `π ^ (e + 1)` on `Fin r → A` is
spelled `(Ideal.span {π} ^ (e + 1)).mkQ.compLeft (Fin r)`, which sidesteps the mismatch between
`(Fin r → A) ⧸ (π ^ (e + 1) • ⊤)` and `Fin r → A ⧸ (π ^ (e + 1))`.

No `@[stacks 0EXF]` attribute is attached to anything here, and nothing below states any part of
that tag: Tag 0EXF is a statement about proper morphisms with geometrically connected fibres over
the spectrum of a discrete valuation ring, and only its final module-theoretic steps appear here.
The tag itself is carried by
`exists_thickening_exponent_free_of_free_generic_and_thickening` (same namespace), which consumes
the results below. The torsion-exponent result needs no valuation ring at all,
only a Noetherian module.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public section

open scoped Pointwise

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {A : Type*} [CommRing A]

/-- Over a domain, an element of `A ⧸ (π ^ (e + 1))` annihilated by `π ^ e` is `π` times an
element: any lift `a` satisfies `π ^ (e + 1) ∣ π ^ e * a`, and cancelling `π ^ e` gives `π ∣ a`. -/
private theorem exists_smul_eq_of_pow_smul_eq_zero [IsDomain A] {π : A} (hπ : π ≠ 0) {e : ℕ}
    {x : A ⧸ Ideal.span {π} ^ (e + 1)} (hx : π ^ e • x = 0) :
    ∃ y : A ⧸ Ideal.span {π} ^ (e + 1), π • y = x := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (Ideal.span {π} ^ (e + 1)) x
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  rw [smul_eq_mul, pow_succ] at hc
  refine ⟨Submodule.mkQ _ c, ?_⟩
  rw [← map_smul]
  exact congrArg _ (mul_left_cancel₀ (pow_ne_zero e hπ) (by rw [smul_eq_mul, ← hc]; ring))

/-- In the free module `(A ⧸ (π ^ (e + 1))) ^ r` over a domain, an element annihilated by `π ^ e`
lies in `π · (A ⧸ (π ^ (e + 1))) ^ r`, since the annihilator of `π ^ e` in `A ⧸ (π ^ (e + 1))` is
the image of the ideal `(π)`. -/
theorem mem_span_singleton_smul_top_of_pow_smul_eq_zero [IsDomain A] {π : A} (hπ : π ≠ 0)
    {e r : ℕ} {x : Fin r → A ⧸ Ideal.span {π} ^ (e + 1)} (hx : π ^ e • x = 0) :
    x ∈ Ideal.span {π} • (⊤ : Submodule A (Fin r → A ⧸ Ideal.span {π} ^ (e + 1))) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  choose y hy using fun i : Fin r =>
    exists_smul_eq_of_pow_smul_eq_zero hπ (e := e) (x := x i) (congrFun hx i)
  exact ⟨y, Submodule.mem_top, funext hy⟩

/-- Nakayama over a discrete valuation ring with uniformizer `π`: a submodule of a finite module
which generates together with `π · N` is everything. -/
private theorem eq_top_of_sup_smul_top_eq_top [IsDomain A] [IsDiscreteValuationRing A] {π : A}
    (hπ : Irreducible π) {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {S : Submodule A N} (h : S ⊔ Ideal.span {π} • (⊤ : Submodule A N) = ⊤) : S = ⊤ := by
  have hjac : Ideal.span {π} ≤ (⊥ : Ideal A).jacobson := by
    rw [← hπ.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal_le_jacobson ⊥
  exact top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac
    (h.ge.trans (sup_le le_sup_left le_sup_right)))

/-- Over a discrete valuation ring with uniformizer `π`, a submodule `S` of the free module
`(A ⧸ (π ^ (e + 1))) ^ r` is everything once `S` and a submodule annihilated by `π ^ e` generate
it. Freeness matters: all of `A ⧸ (π ^ l)` is annihilated by `π ^ e` as soon as `l ≤ e`. -/
theorem eq_top_of_sup_eq_top_of_pow_smul_eq_bot [IsDomain A] [IsDiscreteValuationRing A] {π : A}
    (hπ : Irreducible π) {e r : ℕ}
    {S T : Submodule A (Fin r → A ⧸ Ideal.span {π} ^ (e + 1))} (hST : S ⊔ T = ⊤)
    (hT : Ideal.span {π} ^ e • T = ⊥) : S = ⊤ := by
  have hTle : T ≤ Ideal.span {π} • (⊤ : Submodule A (Fin r → A ⧸ Ideal.span {π} ^ (e + 1))) := by
    intro x hx
    refine mem_span_singleton_smul_top_of_pow_smul_eq_zero hπ.ne_zero ((Submodule.mem_bot A).1 ?_)
    refine hT.le (Submodule.smul_mem_smul ?_ hx)
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  exact eq_top_of_sup_smul_top_eq_top hπ
    (top_le_iff.1 (hST.ge.trans (sup_le le_sup_left (hTle.trans le_sup_right))))

/-- Nakayama's lemma over a discrete valuation ring with uniformizer `π`: a linear map into a
finite module `N` whose image generates `N` together with `π ^ (e + 1) N` is surjective. -/
theorem range_eq_top_of_sup_pow_smul_top_eq_top [IsDomain A] [IsDiscreteValuationRing A] {π : A}
    (hπ : Irreducible π) {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] {e : ℕ} (φ : M →ₗ[A] N)
    (h : LinearMap.range φ ⊔ Ideal.span {π} ^ (e + 1) • (⊤ : Submodule A N) = ⊤) :
    LinearMap.range φ = ⊤ := by
  have hpow : Ideal.span {π} ^ (e + 1) ≤ Ideal.span {π} := by
    simpa using Ideal.pow_le_pow_right (I := Ideal.span {π}) (Nat.le_add_left 1 e)
  exact eq_top_of_sup_smul_top_eq_top hπ
    (top_le_iff.1 (h.ge.trans (sup_le le_sup_left
      ((Submodule.smul_mono_left hpow).trans le_sup_right))))

/-- A vector in `A ^ r` all of whose entries are divisible by `a` is `a` times a vector, so the
submodule of such vectors is contained in `a · A ^ r`. -/
private theorem pi_span_singleton_le_smul_top (a : A) (r : ℕ) :
    Submodule.pi (Set.univ : Set (Fin r)) (fun _ => Ideal.span {a}) ≤
      Ideal.span {a} • (⊤ : Submodule A (Fin r → A)) := by
  intro x hx
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  choose c hc using fun i : Fin r =>
    Ideal.mem_span_singleton'.1 (Submodule.mem_pi.1 hx i (Set.mem_univ i))
  exact ⟨c, Submodule.mem_top, funext fun i => by simpa [mul_comm] using hc i⟩

/-- For `π` a uniformizer of a discrete valuation ring: if the reduction of `φ : M → A ^ r` modulo
`π ^ (e + 1)` becomes surjective after adjoining a submodule annihilated by `π ^ e`, then `φ`
itself is surjective. -/
theorem range_eq_top_of_sup_range_mkQ_comp_eq_top [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π) {M : Type*} [AddCommGroup M] [Module A M] {e r : ℕ}
    (φ : M →ₗ[A] (Fin r → A)) (T : Submodule A (Fin r → A ⧸ Ideal.span {π} ^ (e + 1)))
    (hT : Ideal.span {π} ^ e • T = ⊥)
    (hsurj : LinearMap.range ((Ideal.span {π} ^ (e + 1)).mkQ.compLeft (Fin r) ∘ₗ φ) ⊔ T = ⊤) :
    LinearMap.range φ = ⊤ := by
  set Ψ := (Ideal.span {π} ^ (e + 1)).mkQ.compLeft (Fin r) with hΨ
  have hrange : LinearMap.range (Ψ ∘ₗ φ) = ⊤ :=
    eq_top_of_sup_eq_top_of_pow_smul_eq_bot hπ hsurj hT
  have hker : LinearMap.ker Ψ ≤ Ideal.span {π} ^ (e + 1) • (⊤ : Submodule A (Fin r → A)) := by
    rw [hΨ, LinearMap.ker_compLeft, Submodule.ker_mkQ, Ideal.span_singleton_pow]
    exact pi_span_singleton_le_smul_top _ r
  have hsup : LinearMap.range φ ⊔
      Ideal.span {π} ^ (e + 1) • (⊤ : Submodule A (Fin r → A)) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨m, hm⟩ : Ψ y ∈ LinearMap.range (Ψ ∘ₗ φ) := hrange ▸ Submodule.mem_top
    have hsub : y - φ m ∈ LinearMap.ker Ψ := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact hm.symm
    rw [← add_sub_cancel (φ m) y]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨m, rfl⟩)
      (Submodule.mem_sup_right (hker hsub))
  exact range_eq_top_of_sup_pow_smul_top_eq_top hπ φ hsup

variable {H : Type*} [AddCommGroup H] [Module A H]

/-- A single power of `π` annihilates every `π`-power torsion submodule of a Noetherian module:
the `π`-power torsion submodule is finitely generated, and the largest exponent needed to kill
its generators kills all of it. -/
theorem exists_forall_pow_smul_torsionBy_eq_bot [IsNoetherian A H] (π : A) :
    ∃ e : ℕ, ∀ m : ℕ, Ideal.span {π} ^ e • Submodule.torsionBy A H (π ^ m) = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (Submodule.torsion' A H (Submonoid.powers π))
  have hchoice : ∀ y : H, ∃ n : ℕ,
      y ∈ Submodule.torsion' A H (Submonoid.powers π) → π ^ n • y = 0 := by
    intro y
    by_cases hy : y ∈ Submodule.torsion' A H (Submonoid.powers π)
    · obtain ⟨⟨a, n, rfl⟩, ha⟩ := hy
      exact ⟨n, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose n hn using hchoice
  have hle : Submodule.torsion' A H (Submonoid.powers π) ≤
      Submodule.torsionBy A H (π ^ s.sup n) := by
    rw [← hs]
    refine Submodule.span_le.2 fun y hy => ?_
    have hsup : n y ≤ s.sup n := Finset.le_sup (Finset.mem_coe.1 hy)
    have hzero : π ^ n y • y = 0 := hn y (hs ▸ Submodule.subset_span hy)
    rw [SetLike.mem_coe, Submodule.mem_torsionBy_iff, ← Nat.sub_add_cancel hsup, pow_add,
      mul_smul, hzero, smul_zero]
  refine ⟨s.sup n, fun m => eq_bot_iff.2 (Submodule.smul_le.2 fun r hr x hx => ?_)⟩
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
  obtain ⟨c, rfl⟩ := hr
  have hx' : x ∈ Submodule.torsion' A H (Submonoid.powers π) :=
    ⟨⟨π ^ m, m, rfl⟩, (Submodule.mem_torsionBy_iff _ x).1 hx⟩
  rw [mul_smul, (Submodule.mem_torsionBy_iff _ x).1 (hle hx'), smul_zero]
  exact Submodule.zero_mem _

end Stacks.AlgebraicGeometry.FreenessOverDVR
