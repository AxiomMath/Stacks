module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Faithfully flat descent of the equational criterion for flatness

Algebra, Lemma 04VX — the equational criterion — says that an `A`-module `M` is flat exactly
when every relation `∑ i, x i • y i = 0` in it *vanishes trivially*: the `y i` factor through a
finite free module on coefficients annihilating `x`.  Mathlib carries that predicate as
`TensorProduct.VanishesTrivially`.

This file proves that vanishing trivially **descends along a faithfully flat base change**:

    `B` faithfully flat over `A`, `x : ι → A`, `y : ι → M`;
    if the base-changed relation vanishes trivially over `B`, it vanishes trivially over `A`.

That is `Stacks.FlatDescent.vanishesTrivially_of_baseChange`, with the same statement in explicit
data as `Stacks.FlatDescent.exists_factorization_of_baseChange`.  No hypothesis on `M` is
needed — in particular not flatness of `M` over `A`, which is what one is usually trying to
prove — and the relation `∑ i, x i • y i = 0` need not be assumed, since it follows from the
conclusion.

## The route

Two steps, split so that each is a single Mathlib fact.

**Flatness descends the coefficients.**  A `B`-certificate for the relation is a matrix
`b : ι → κ → B` with `∑ i, x i • b i k = 0` for every `k`, read in `B` as an `A`-module.  If `B`
is flat over `A`, each such column relation is itself trivial —
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` — which refines the entries of `b` to `A`.
That is `Stacks.FlatDescent.vanishesTrivially_of_algebraMap`, and it needs only flatness.

**Faithful flatness removes the base change.**  For this the predicate is turned into the
vanishing of a single tensor.  Mathlib's
`TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero` does that for a family spanning its
module, which `x : ι → A` does not; but the images `Stacks.FlatDescent.syzGen` of the standard
basis vectors in the quotient `Stacks.FlatDescent.SyzQuot` of `ι →₀ A` by the syzygies of `x` do
span, and for them the side condition is literally `∑ i, a i • x i = 0`.  So

    `VanishesTrivially A x y  ↔  ∑ i, syzGen A x i ⊗ₜ y i = 0`   in `SyzQuot A x ⊗[A] M`,

which is `Stacks.FlatDescent.vanishesTrivially_iff_sum_tmul_syzGen`.  After the first step the
tensor to be killed is `1 ⊗ₜ (∑ i, syzGen A x i ⊗ₜ y i)` up to
`TensorProduct.leftComm`, and `Module.FaithfullyFlat.one_tmul_eq_zero_iff` kills it.

## Implementation notes

The main statement is phrased on `B ⊗[A] M` rather than `M ⊗[A] B`: the predicate needs the
`B`-module structure on the base change, and Mathlib's `TensorProduct.leftModule` puts the
outside action on the *left* factor, with no `Module B (M ⊗[A] B)` instance available.
`Stacks.FlatDescent.exists_factorization_of_baseChange_right` is the `M ⊗[A] B` orientation,
with the `B`-action routed through `TensorProduct.comm`.

## References

* [Stacks Project, Tag 04VX](https://stacks.math.columbia.edu/tag/04VX)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public section

open LinearMap TensorProduct

namespace Stacks.FlatDescent

section Syzygy

variable (R : Type*) [CommRing R] {ι : Type*} [Fintype ι]

/-- The linear functional `v ↦ ∑ i, v i * x i` on `ι →₀ R`. -/
noncomputable def dotHom (x : ι → R) : (ι →₀ R) →ₗ[R] R := Finsupp.linearCombination R x

/-- The quotient of `ι →₀ R` by the module of syzygies of `x`. -/
abbrev SyzQuot (x : ι → R) := (ι →₀ R) ⧸ LinearMap.ker (dotHom R x)

/-- The image of the `i`-th standard basis vector in `SyzQuot R x`. -/
noncomputable def syzGen (x : ι → R) (i : ι) : SyzQuot R x :=
  (LinearMap.ker (dotHom R x)).mkQ (Finsupp.single i 1)

omit [Fintype ι] in
/-- The elements `syzGen R x i` span `SyzQuot R x`. -/
lemma span_range_syzGen (x : ι → R) :
    Submodule.span R (Set.range (syzGen R x)) = ⊤ := by
  have h : syzGen R x = (LinearMap.ker (dotHom R x)).mkQ ∘ Finsupp.basisSingleOne := by
    funext i
    simp [syzGen]
  rw [h, Set.range_comp, Submodule.span_image, Finsupp.basisSingleOne.span_eq,
    Submodule.map_top, Submodule.range_mkQ]

/-- A linear combination `∑ i, a i • syzGen R x i` vanishes in `SyzQuot R x` if and only if
`∑ i, a i • x i = 0` in `R`. -/
lemma sum_smul_syzGen_eq_zero_iff (x a : ι → R) :
    ∑ i, a i • syzGen R x i = 0 ↔ ∑ i, a i • x i = 0 := by
  have h : ∑ i, a i • syzGen R x i
      = (LinearMap.ker (dotHom R x)).mkQ (∑ i, a i • (Finsupp.single i 1 : ι →₀ R)) := by
    simp only [map_sum, map_smul, syzGen]
  rw [h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker, map_sum]
  simp [dotHom]

/-- `TensorProduct.VanishesTrivially R x n` is the vanishing of a single element of
`SyzQuot R x ⊗[R] N`. -/
theorem vanishesTrivially_iff_sum_tmul_syzGen {N : Type*} [AddCommGroup N] [Module R N]
    (x : ι → R) (n : ι → N) :
    VanishesTrivially R x n ↔ ∑ i, syzGen R x i ⊗ₜ[R] n i = 0 := by
  rw [← vanishesTrivially_iff_sum_tmul_eq_zero R (span_range_syzGen R x)]
  exact exists_congr fun _ => exists_congr fun a => exists_congr fun _ =>
    and_congr_right fun _ => forall_congr' fun j =>
      (sum_smul_syzGen_eq_zero_iff R x fun i => a i j).symm

end Syzygy

section Descent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {ι : Type*} [Fintype ι]

/-- **Flat descent of the coefficients.** If `B` is a flat `A`-algebra and `N` is a `B`-module,
then a relation with coefficients `x : ι → A` that vanishes trivially over `B` already
vanishes trivially over `A`. -/
theorem vanishesTrivially_of_algebraMap [Module.Flat A B]
    {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    {x : ι → A} {n : ι → N}
    (h : VanishesTrivially B (fun i => algebraMap A B (x i)) n) :
    VanishesTrivially A x n := by
  obtain ⟨k, b, z, hbz, hb⟩ := h
  have key : ∀ j : Fin k, Module.IsTrivialRelation x fun i => b i j := by
    intro j
    refine Module.Flat.isTrivialRelation_of_sum_smul_eq_zero ?_
    have h' := hb j
    simpa [Algebra.smul_def, mul_comm] using h'
  choose m c w hcw hc using key
  refine .of_fintype (κ := Σ j : Fin k, Fin (m j)) (fun i p => c p.1 i p.2)
      (fun p => w p.1 p.2 • z p.1) ?_ ?_
  · intro i
    rw [Fintype.sum_sigma]
    calc n i = ∑ j, b i j • z j := hbz i
      _ = ∑ j, (∑ l, c j i l • w j l) • z j := by simp_rw [← hcw]
      _ = ∑ j, ∑ l, c j i l • (w j l • z j) := by
          simp_rw [Finset.sum_smul, smul_assoc]
  · rintro ⟨j, l⟩
    simpa [smul_eq_mul, mul_comm] using hc j l

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- **Faithfully flat descent of the equational criterion for flatness.**

Let `B` be a faithfully flat `A`-algebra and `M` an `A`-module. If the relation
`∑ i, x i • y i = 0` vanishes trivially after base change to `B`, then it already
vanishes trivially over `A`. -/
theorem vanishesTrivially_of_baseChange [Module.FaithfullyFlat A B]
    {x : ι → A} {y : ι → M}
    (h : VanishesTrivially B (fun i => algebraMap A B (x i))
          (fun i => (1 : B) ⊗ₜ[A] y i)) :
    VanishesTrivially A x y := by
  have h1 : VanishesTrivially A x (fun i => (1 : B) ⊗ₜ[A] y i) :=
    vanishesTrivially_of_algebraMap h
  rw [vanishesTrivially_iff_sum_tmul_syzGen] at h1 ⊢
  refine (Module.FaithfullyFlat.one_tmul_eq_zero_iff (A := B) A _ _).mp ?_
  rw [tmul_sum]
  have h2 := congrArg (TensorProduct.leftComm A (SyzQuot A x) B M) h1
  simpa using h2

/-- The explicit-data form of faithfully flat descent of the equational criterion. -/
theorem exists_factorization_of_baseChange [Module.FaithfullyFlat A B]
    {κ : Type*} [Fintype κ] {x : ι → A} {y : ι → M}
    (b : ι → κ → B) (a : κ → B ⊗[A] M)
    (hb : ∀ k, ∑ i, algebraMap A B (x i) * b i k = 0)
    (ha : ∀ i, (1 : B) ⊗ₜ[A] y i = ∑ k, b i k • a k) :
    ∃ (κ' : Type) (_ : Fintype κ') (b' : ι → κ' → A) (a' : κ' → M),
      (∀ k, ∑ i, x i * b' i k = 0) ∧ ∀ i, y i = ∑ k, b' i k • a' k := by
  have h : VanishesTrivially B (fun i => algebraMap A B (x i))
      (fun i => (1 : B) ⊗ₜ[A] y i) :=
    .of_fintype b a ha fun k => by simpa [smul_eq_mul, mul_comm] using hb k
  obtain ⟨n, b', a', h1, h2⟩ := vanishesTrivially_of_baseChange h
  exact ⟨Fin n, inferInstance, b', a', fun k => by simpa [smul_eq_mul, mul_comm] using h2 k, h1⟩

/-- The `M ⊗[A] B` orientation of `exists_factorization_of_baseChange`.

Mathlib provides no `Module B (M ⊗[A] B)` instance (`TensorProduct.leftModule` puts the
`B`-action on the *left* factor), so here the `B`-action on `M ⊗[A] B` is written through
`TensorProduct.comm`. -/
theorem exists_factorization_of_baseChange_right [Module.FaithfullyFlat A B]
    {κ : Type*} [Fintype κ] {x : ι → A} {y : ι → M}
    (b : ι → κ → B) (a : κ → M ⊗[A] B)
    (hb : ∀ k, ∑ i, algebraMap A B (x i) * b i k = 0)
    (ha : ∀ i, y i ⊗ₜ[A] (1 : B) =
      ∑ k, (TensorProduct.comm A M B).symm (b i k • TensorProduct.comm A M B (a k))) :
    ∃ (κ' : Type) (_ : Fintype κ') (b' : ι → κ' → A) (a' : κ' → M),
      (∀ k, ∑ i, x i * b' i k = 0) ∧ ∀ i, y i = ∑ k, b' i k • a' k := by
  refine exists_factorization_of_baseChange b (fun k => TensorProduct.comm A M B (a k)) hb ?_
  intro i
  have h := congrArg (TensorProduct.comm A M B) (ha i)
  simpa using h

end Descent

end Stacks.FlatDescent

end
