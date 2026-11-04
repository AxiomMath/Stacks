module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Setup
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of the projective line

For a Weil cohomology theory the total cohomology `H^*(P¹_k)` is one dimensional in degrees `0`
and `2` and zero in every other degree.

The argument is the source's. A rational point `x` of `P¹_k` gives `Δ = pr_1^*x + pr_2^*x` as
divisors on `P¹_k × P¹_k`, so axiom `(C)(a)` and additivity of the cycle class map put the
Künneth coordinates of `γ([Δ])` in the form `γ([x]) ⊗ 1 + 1 ⊗ γ([x])`, a sum of two pure
tensors. On the other hand the Künneth coordinates of `γ([Δ])` read through a basis `e` of
`H^*(P¹_k)` are `∑_j e_j ⊗ e'_j` with the `e'_j` a dual basis up to sign by Stacks 0FHH, hence
linearly independent; a tensor of that shape is not a sum of fewer than `∑_i β_i` pure tensors,
where `β_i = dim_F H^i(P¹_k)`. Therefore `∑_i β_i ≤ 2`. Stacks 0FHF gives `β_0 ≥ 1` and
Poincaré duality, axiom `(A)(b)`, gives `β_0 = β_2`, so `β_0 = β_2 = 1` and `β_1 = 0`; the
remaining degrees vanish because cohomology is concentrated in `[0, 2d]`.

## Main results

* `Stacks.WeilCohomology.linearIndependent_of_pairing_eq_single`: a family dual to another
  family for a pairing, up to nonzero scalars, is linearly independent. This is what turns the
  conclusion of Stacks 0FHH into the hypothesis used here.
* `Stacks.WeilCohomology.finrank_le_card_of_sum_tmul_eq_sum_tmul`: the tensor-rank bound. If
  `∑_j e_j ⊗ e'_j`, with `e` a basis of `U` and `e'` linearly independent, is also a sum of
  `#M` pure tensors, then `dim_F U ≤ #M`.
* `Stacks.WeilCohomology.finrank_le_two_of_sum_tmul_eq_add_tmul`: the case of two pure tensors.
* `Stacks.WeilCohomology.finrank_add_add_le_finrank_directSum`: three distinct graded pieces
  inject into the total direct sum.
* In the namespace `Stacks.WeilCohomology.PoincareDualityPushforwardSetup`, the three
  assertions of the lemma: `finrank_piece_zero_eq_one_of_diagonal_two_tmul` and
  `finrank_piece_two_eq_one_of_diagonal_two_tmul` for degrees `0` and `2`, and
  `subsingleton_piece_of_diagonal_two_tmul` for the vanishing in every other degree.

## Implementation notes

The cohomological data is the Poincaré duality package
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`, the data `(D1)`, `(D3)` and condition
`(A)` of Section 45.9, as elsewhere in this directory. Total cohomology is the direct sum
`⨁ n, H^n(X)`, the source of the Künneth isomorphism
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.kunnethEquiv`, so the Künneth coordinates
of `γ([Δ])` are an element of its tensor square.

`X` is an arbitrary object of `(SmoothProjective k).FullSubcategory` whose recorded dimension is
`1`, and the two further facts about `P¹_k` that the source's proof uses are hypotheses, in the
style of the rest of this directory. The projective line itself is
`AlgebraicGeometry.projectiveLine`, smooth and proper over `k` of relative dimension one by
`AlgebraicGeometry.projectiveLine_smooth`, `AlgebraicGeometry.projectiveLine_isProper` and
`AlgebraicGeometry.projectiveLine_relativeDimension`; promoting it to an object of
`(SmoothProjective k).FullSubcategory` asks for projectivity of the structure morphism in the
sense that subcategory records, which is a separate step from properness.

* `hdiag` combines the two descriptions of the Künneth coordinates of `γ([Δ])`: the
  decomposition `∑_j e_j ⊗ e'_j` through a basis `e` of total cohomology, whose coefficients
  `e'` are linearly independent by Stacks 0FHH, is equal to a sum of two pure tensors. The
  latter is where `P¹_k` enters: it comes from `Δ = pr_1^*x + pr_2^*x` for a rational point `x`,
  additivity of `γ` and axiom `(C)(a)`.
* `hne`, that `H^0(X) ≠ 0`, is Stacks 0FHF for a nonempty `X`.

No separate Tate twist appears; as everywhere in this directory a class of codimension `r` lives
in the graded piece of degree `2r`.

## References

* [Stacks Project, Tag 0FHI](https://stacks.math.columbia.edu/tag/0FHI)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum TensorProduct

universe u v w t s

namespace Stacks.WeilCohomology

section LinearAlgebra

variable {F : Type v} [Field F]

/-- A family `e'` paired diagonally with a family `d` by nonzero scalars, so that
`⟨d j, e' j'⟩ = 0` for `j ≠ j'` and `⟨d j, e' j⟩ ≠ 0`, is linearly independent. -/
theorem linearIndependent_of_pairing_eq_single {U V : Type w} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] {J : Type t} [Finite J] [DecidableEq J]
    (pair : U →ₗ[F] V →ₗ[F] F) (d : J → U) (e' : J → V) (c : J → F) (hc : ∀ j, c j ≠ 0)
    (h : ∀ j j', pair (d j) (e' j') = if j = j' then c j else 0) :
    LinearIndependent F e' := by
  have := Fintype.ofFinite J
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hjj : pair (d j) (e' j) = c j := by rw [h j j]; simp
  have hsum := congrArg (pair (d j)) hg
  rw [map_zero, map_sum] at hsum
  simp only [map_smul] at hsum
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      (fun i _ hij => by simp [h j i, Ne.symm hij]), hjj, smul_eq_mul] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right (hc j)

/-- The tensor-rank bound: a tensor expanding as `∑_j e_j ⊗ e'_j`, with `e` a basis of `U` and
`e'` linearly independent, is not a sum of fewer than `dim_F U` pure tensors. -/
theorem finrank_le_card_of_sum_tmul_eq_sum_tmul {U V : Type w} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] {J : Type t} [Fintype J]
    (e : Module.Basis J F U) (e' : J → V) (hli : LinearIndependent F e')
    {M : Type s} [Fintype M] (a : M → U) (b : M → V)
    (h : ∑ j : J, e j ⊗ₜ[F] e' j = ∑ m : M, a m ⊗ₜ[F] b m) :
    Module.finrank F U ≤ Fintype.card M := by
  classical
  have hmem : ∀ j : J, e' j ∈ Submodule.span F (Set.range b) := by
    intro j
    have hc := congrArg (TensorProduct.lift ((LinearMap.lsmul F V).comp (e.coord j))) h
    rw [map_sum, map_sum] at hc
    simp only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply] at hc
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
        (fun l _ hlj => by
          rw [Module.Basis.coord_apply, Module.Basis.repr_self,
            Finsupp.single_eq_of_ne (Ne.symm hlj), zero_smul]),
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul] at hc
    rw [hc]
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  have : Module.Finite F (Submodule.span F (Set.range b)) :=
    Module.Finite.span_of_finite F (Set.finite_range b)
  calc Module.finrank F U = Fintype.card J := Module.finrank_eq_card_basis e
    _ = Module.finrank F (Submodule.span F (Set.range e')) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank F (Submodule.span F (Set.range b)) :=
        Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 hmem))
    _ ≤ Fintype.card M := finrank_range_le_card b

/-- The tensor-rank bound for two pure tensors: if `∑_j e_j ⊗ e'_j`, with `e` a basis of `U` and
`e'` linearly independent, is a sum of two pure tensors, then `dim_F U ≤ 2`. -/
theorem finrank_le_two_of_sum_tmul_eq_add_tmul {U V : Type w} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] {J : Type t} [Fintype J]
    (e : Module.Basis J F U) (e' : J → V) (hli : LinearIndependent F e')
    (a₁ a₂ : U) (b₁ b₂ : V)
    (h : ∑ j : J, e j ⊗ₜ[F] e' j = a₁ ⊗ₜ[F] b₁ + a₂ ⊗ₜ[F] b₂) :
    Module.finrank F U ≤ 2 := by
  have hcard := finrank_le_card_of_sum_tmul_eq_sum_tmul e e' hli
    (fun m : Fin 2 => if m = 0 then a₁ else a₂) (fun m : Fin 2 => if m = 0 then b₁ else b₂)
    (by rw [h, Fin.sum_univ_two]; simp)
  simpa using hcard

/-- Three distinct graded pieces inject into the total direct sum, so the sum of their
dimensions is at most the dimension of the total space. -/
theorem finrank_add_add_le_finrank_directSum {P : ℤ → Type w} [∀ n, AddCommGroup (P n)]
    [∀ n, Module F (P n)] [Module.Finite F (⨁ n, P n)] (i j l : ℤ)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    [Module.Finite F (P i)] [Module.Finite F (P j)] [Module.Finite F (P l)] :
    Module.finrank F (P i) + Module.finrank F (P j) + Module.finrank F (P l) ≤
      Module.finrank F (⨁ n, P n) := by
  have hzero : ∀ (m n : ℤ) (x : P n), m ≠ n →
      DirectSum.component F ℤ P m (DirectSum.lof F ℤ P n x) = 0 := fun m n x hmn => by
    simp [DirectSum.component.of, Ne.symm hmn]
  set incl : P i × P j × P l →ₗ[F] ⨁ n, P n :=
    (DirectSum.lof F ℤ P i).coprod
      ((DirectSum.lof F ℤ P j).coprod (DirectSum.lof F ℤ P l)) with hincl
  have hleft : ∀ x : P i × P j × P l,
      (DirectSum.component F ℤ P i (incl x), DirectSum.component F ℤ P j (incl x),
        DirectSum.component F ℤ P l (incl x)) = x := by
    rintro ⟨x₁, x₂, x₃⟩
    simp only [hincl, LinearMap.coprod_apply, map_add, DirectSum.component.lof_self,
      hzero i j x₂ hij, hzero i l x₃ hil, hzero j i x₁ (Ne.symm hij), hzero j l x₃ hjl,
      hzero l i x₁ (Ne.symm hil), hzero l j x₂ (Ne.symm hjl), add_zero, zero_add]
  have hinj : Function.Injective incl := fun x y hxy => by
    rw [← hleft x, ← hleft y, hxy]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_prod, ← add_assoc] at hle

end LinearAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

namespace PoincareDualityPushforwardSetup

variable (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
  (X : (SmoothProjective k).FullSubcategory)

/-- Poincaré duality in dimension one pairs degree `0` with degree `2`, so those two graded
pieces have the same dimension. -/
private theorem finrank_piece_zero_eq_finrank_piece_two (hd : S.dimension X = 1) :
    Module.finrank F ((S.H X).piece 0) = Module.finrank F ((S.H X).piece 2) := by
  have := S.finite X 0
  have := S.finite X (2 * (S.dimension X : ℤ) - 0)
  have := S.perfect X 0
  have h := Module.finrank_of_isPerfPair
    ((S.H X).tracePairing (S.dimension X) (S.integration X).toLinearMap 0)
  rwa [show 2 * (S.dimension X : ℤ) - 0 = 2 by omega] at h

/-- The dimensions of the three graded pieces in degrees `0`, `1` and `2` add up to at most `2`,
the tensor-rank bound applied to the Künneth coordinates of the diagonal class. -/
private theorem finrank_piece_sum_le_two {J : Type t} [Fintype J]
    (e : Module.Basis J F (⨁ n : ℤ, (S.H X).piece n))
    (e' : J → ⨁ n : ℤ, (S.H X).piece n) (hli : LinearIndependent F e')
    (a₁ a₂ b₁ b₂ : ⨁ n : ℤ, (S.H X).piece n)
    (hdiag : ∑ j : J, e j ⊗ₜ[F] e' j = a₁ ⊗ₜ[F] b₁ + a₂ ⊗ₜ[F] b₂) :
    Module.finrank F ((S.H X).piece 0) + Module.finrank F ((S.H X).piece 1) +
      Module.finrank F ((S.H X).piece 2) ≤ 2 := by
  have : Module.Finite F (⨁ n : ℤ, (S.H X).piece n) := Module.Finite.of_basis e
  have := S.finite X 0
  have := S.finite X 1
  have := S.finite X 2
  exact le_trans
    (finrank_add_add_le_finrank_directSum (F := F) (P := fun n => (S.H X).piece n) 0 1 2
      (by decide) (by decide) (by decide))
    (finrank_le_two_of_sum_tmul_eq_add_tmul e e' hli a₁ a₂ b₁ b₂ hdiag)

/-- Under the hypotheses of Tag 0FHI, `H^0` is one dimensional and `H^1` is zero dimensional. -/
private theorem finrank_piece_zero_eq_one_and_finrank_piece_one_eq_zero
    (hd : S.dimension X = 1)
    (hne : Nontrivial ((S.H X).piece 0)) {J : Type t} [Fintype J]
    (e : Module.Basis J F (⨁ n : ℤ, (S.H X).piece n))
    (e' : J → ⨁ n : ℤ, (S.H X).piece n) (hli : LinearIndependent F e')
    (a₁ a₂ b₁ b₂ : ⨁ n : ℤ, (S.H X).piece n)
    (hdiag : ∑ j : J, e j ⊗ₜ[F] e' j = a₁ ⊗ₜ[F] b₁ + a₂ ⊗ₜ[F] b₂) :
    Module.finrank F ((S.H X).piece 0) = 1 ∧ Module.finrank F ((S.H X).piece 1) = 0 := by
  have := S.finite X 0
  have := hne
  have hpos : Module.finrank F ((S.H X).piece 0) ≠ 0 := fun h =>
    not_subsingleton _ ((Module.finrank_zero_iff (R := F)).mp h)
  have hsum := S.finrank_piece_sum_le_two X e e' hli a₁ a₂ b₁ b₂ hdiag
  have hdual := S.finrank_piece_zero_eq_finrank_piece_two X hd
  omega

/-- **Stacks Project, Tag 0FHI.** The degree-zero cohomology of a smooth projective scheme of
dimension one with nonvanishing `H^0` whose diagonal class is a sum of two pure tensors in
Künneth coordinates — for the source, `P¹_k` — is one dimensional. -/
@[stacks 0FHI "degree zero is one dimensional, for a dimension one `X` whose diagonal class \
is a sum of two pure tensors; `P¹_k` itself is not constructed in this development"]
theorem finrank_piece_zero_eq_one_of_diagonal_two_tmul (hd : S.dimension X = 1)
    (hne : Nontrivial ((S.H X).piece 0)) {J : Type t} [Fintype J]
    (e : Module.Basis J F (⨁ n : ℤ, (S.H X).piece n))
    (e' : J → ⨁ n : ℤ, (S.H X).piece n) (hli : LinearIndependent F e')
    (a₁ a₂ b₁ b₂ : ⨁ n : ℤ, (S.H X).piece n)
    (hdiag : ∑ j : J, e j ⊗ₜ[F] e' j = a₁ ⊗ₜ[F] b₁ + a₂ ⊗ₜ[F] b₂) :
    Module.finrank F ((S.H X).piece 0) = 1 :=
  (S.finrank_piece_zero_eq_one_and_finrank_piece_one_eq_zero X hd hne e e' hli a₁ a₂ b₁ b₂
    hdiag).1

/-- **Stacks Project, Tag 0FHI.** The degree-two cohomology of a smooth projective scheme of
dimension one with nonvanishing `H^0` whose diagonal class is a sum of two pure tensors in
Künneth coordinates — for the source, `P¹_k` — is one dimensional. -/
@[stacks 0FHI "degree two is one dimensional, for a dimension one `X` whose diagonal class \
is a sum of two pure tensors; `P¹_k` itself is not constructed in this development"]
theorem finrank_piece_two_eq_one_of_diagonal_two_tmul (hd : S.dimension X = 1)
    (hne : Nontrivial ((S.H X).piece 0)) {J : Type t} [Fintype J]
    (e : Module.Basis J F (⨁ n : ℤ, (S.H X).piece n))
    (e' : J → ⨁ n : ℤ, (S.H X).piece n) (hli : LinearIndependent F e')
    (a₁ a₂ b₁ b₂ : ⨁ n : ℤ, (S.H X).piece n)
    (hdiag : ∑ j : J, e j ⊗ₜ[F] e' j = a₁ ⊗ₜ[F] b₁ + a₂ ⊗ₜ[F] b₂) :
    Module.finrank F ((S.H X).piece 2) = 1 :=
  (S.finrank_piece_zero_eq_finrank_piece_two X hd).symm.trans
    (S.finrank_piece_zero_eq_one_of_diagonal_two_tmul X hd hne e e' hli a₁ a₂ b₁ b₂ hdiag)

/-- **Stacks Project, Tag 0FHI.** Outside degrees `0` and `2` the cohomology of a smooth
projective scheme of dimension one with nonvanishing `H^0` whose diagonal class is a sum of two
pure tensors in Künneth coordinates — for the source, `P¹_k` — vanishes. -/
@[stacks 0FHI "vanishing in the other degrees, for a dimension one `X` whose diagonal class \
is a sum of two pure tensors; `P¹_k` itself is not constructed in this development"]
theorem subsingleton_piece_of_diagonal_two_tmul (hd : S.dimension X = 1)
    (hne : Nontrivial ((S.H X).piece 0)) {J : Type t} [Fintype J]
    (e : Module.Basis J F (⨁ n : ℤ, (S.H X).piece n))
    (e' : J → ⨁ n : ℤ, (S.H X).piece n) (hli : LinearIndependent F e')
    (a₁ a₂ b₁ b₂ : ⨁ n : ℤ, (S.H X).piece n)
    (hdiag : ∑ j : J, e j ⊗ₜ[F] e' j = a₁ ⊗ₜ[F] b₁ + a₂ ⊗ₜ[F] b₂)
    (i : ℤ) (h0 : i ≠ 0) (h2 : i ≠ 2) :
    Subsingleton ((S.H X).piece i) := by
  rcases show i < 0 ∨ i = 1 ∨ 2 * (S.dimension X : ℤ) < i by omega with h | h | h
  · exact subsingleton_of_forall_eq 0 fun a => S.bounded X i (Or.inl h) a
  · subst h
    have := S.finite X 1
    exact (Module.finrank_zero_iff (R := F)).mp
      (S.finrank_piece_zero_eq_one_and_finrank_piece_one_eq_zero X hd hne e e' hli a₁ a₂ b₁ b₂
        hdiag).2
  · exact subsingleton_of_forall_eq 0 fun a => S.bounded X i (Or.inr h) a

end PoincareDualityPushforwardSetup

end Stacks.WeilCohomology

end
