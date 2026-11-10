module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethOfIsPullback

/-!
# Homogeneous decompositions in the Künneth tensor product

For smooth projective schemes `X`, `Y` over `k` and a Weil-type cohomology `H^*` given by data
(D0), (D1), (D2'), every element of `H^*(X) ⊗ H^*(Y)` is a finite sum of tensors of homogeneous
bidegrees `(i, j)`, and under (A5) the Künneth isomorphism `H^*(X) ⊗ H^*(Y) ≅ H^*(P)` onto a fibre
product `P` of `X` and `Y` over `Spec(k)` sends a tensor of bidegree `(i, j)` into `H^{i+j}(P)`.

## Main definitions

* `Stacks.WeilDeRham.bigradedPiece`: the image of `H^i(X) ⊗ H^j(Y)` in `H^*(X) ⊗ H^*(Y)`.

## Main results

* `Stacks.WeilDeRham.exists_bigraded_sum`: every tensor is a finite sum of homogeneous ones.
* `Stacks.WeilDeRham.kunnethEquiv_mem_grade_of_mem_bigradedPiece`: the Künneth isomorphism of
  `Stacks.WeilDeRham.kunnethEquivOfIsPullback` sends bidegree `(i, j)` into degree `i + j`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u w

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k] {F : Type w} [Field F] {𝔇 : FirstChernClassData k F}

variable {X Y P : (SmoothProjectiveScheme k).FullSubcategory}

/-- The tensors of bidegree `(i, j)`: the image of `H^i(X) ⊗ H^j(Y)` in `H^*(X) ⊗ H^*(Y)`. -/
def bigradedPiece (X Y : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ) :
    Submodule F (𝔇.H X ⊗[F] 𝔇.H Y) :=
  LinearMap.range (TensorProduct.map (𝔇.grade X i).subtype (𝔇.grade Y j).subtype)

/-- If `x ∈ H^i(X)` and `y ∈ H^j(Y)`, then `x ⊗ y` has bidegree `(i, j)`. -/
theorem tmul_mem_bigradedPiece {i j : ℤ} {x : 𝔇.H X} {y : 𝔇.H Y} (hx : x ∈ 𝔇.grade X i)
    (hy : y ∈ 𝔇.grade Y j) : x ⊗ₜ y ∈ bigradedPiece (𝔇 := 𝔇) X Y i j :=
  ⟨⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩, rfl⟩

/-- Every element of `H^*(X) ⊗ H^*(Y)` is a finite sum of tensors of homogeneous bidegrees. -/
theorem exists_bigraded_sum (z : 𝔇.H X ⊗[F] 𝔇.H Y) :
    ∃ (S : Finset (ℤ × ℤ)) (f : ℤ × ℤ → 𝔇.H X ⊗[F] 𝔇.H Y),
      (∀ s, f s ∈ bigradedPiece (𝔇 := 𝔇) X Y s.1 s.2) ∧ z = ∑ s ∈ S, f s := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    refine ⟨(DFinsupp.support (decompose (𝔇.grade X) a)) ×ˢ
        (DFinsupp.support (decompose (𝔇.grade Y) b)),
      fun s => (decompose (𝔇.grade X) a s.1 : 𝔇.H X) ⊗ₜ (decompose (𝔇.grade Y) b s.2 : 𝔇.H Y),
      fun s => tmul_mem_bigradedPiece (SetLike.coe_mem _) (SetLike.coe_mem _), ?_⟩
    conv_lhs => rw [← sum_support_decompose (𝔇.grade X) a, ← sum_support_decompose (𝔇.grade Y) b]
    rw [TensorProduct.sum_tmul, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_sum]
  | add z z' hz hz' =>
    obtain ⟨S, f, hf, rfl⟩ := hz
    obtain ⟨S', f', hf', rfl⟩ := hz'
    refine ⟨S ∪ S', fun s => (if s ∈ S then f s else 0) + (if s ∈ S' then f' s else 0),
      fun s => Submodule.add_mem _ ?_ ?_, ?_⟩
    · split_ifs
      exacts [hf s, zero_mem _]
    · split_ifs
      exacts [hf' s, zero_mem _]
    · rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
        Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]

variable (hA5 : 𝔇.KunnethAxiom) (p : P ⟶ X) (q : P ⟶ Y)
  (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom Y.obj.hom)

/-- **The Künneth isomorphism respects the grading**: a tensor of bidegree `(i, j)` is sent into
`H^{i+j}(P)`, the isomorphism being `a ⊗ b ↦ p^*a ∪ q^*b`. -/
theorem kunnethEquiv_mem_grade_of_mem_bigradedPiece {i j : ℤ} {w : 𝔇.H X ⊗[F] 𝔇.H Y}
    (hw : w ∈ bigradedPiece (𝔇 := 𝔇) X Y i j) :
    kunnethEquivOfIsPullback p q hP hA5 w ∈ 𝔇.grade P (i + j) := by
  obtain ⟨t, rfl⟩ := hw
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.map_tmul, kunnethEquivOfIsPullback_tmul]
    exact SetLike.GradedMul.mul_mem (𝔇.pull_grade p i _ a.2) (𝔇.pull_grade q j _ b.2)
  | add t t' ht ht' => rw [map_add, map_add]; exact Submodule.add_mem _ ht ht'

end Stacks.WeilDeRham

end
