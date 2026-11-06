module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixTwoTransitive

/-!
# The power of the general linear group moves a pair of rational points of a power of projective
space to any pair with the same coincidence pattern

This file is the exercise of [Stacks, Tag 0AEM] in the shape its contraction step uses. Let `K` be
an algebraically closed field and let `x, y` be two distinct `K`-rational points of `(ℙⁿ_K)^m`. Put

`I = {i | xᵢ = yᵢ} ⊆ {1, …, m}`,

the set of coordinates on which they agree — the set the source's projection `π_I` is taken over.
Then the `m`-th power of the general linear group carries `(x, y)` to *every* pair `(p, q)` of
`K`-rational points with the same coincidence pattern, that is with `pᵢ = qᵢ` exactly for `i ∈ I`.

Those pairs are precisely the `K`-rational points of the fibre product `X ×_{(ℙⁿ_K)^I} X` lying
off every partial diagonal, so this is the statement that the orbit of `(x, y)` under the diagonal
action of `(GL_{n+1})^m` contains all of them.

## Main results

* `AlgebraicGeometry.exists_comp_matrixToAutOver_hom_eq_and_eq` and
  `AlgebraicGeometry.exists_comp_matrixToAutOver_hom_eq`: two-transitivity and transitivity of the
  matrix action, read in the slice category over `Spec K`, where the rational points of a product
  are the families of rational points of its factors.
* `AlgebraicGeometry.exists_comp_powerMatrixAut_hom_eq_and_eq`: **the orbit statement for the
  power.** Given two distinct rational points `x ≠ y` of `(ℙⁿ_K)^m` and a pair `p, q` whose
  coordinates coincide exactly where those of `x` and `y` do, one `m`-tuple of invertible matrices
  carries `x` to `p` and `y` to `q`.

## Implementation notes

The rational points are taken as morphisms out of `Over.mk (𝟙 (Spec K))` in the slice category
over `Spec K`, not as sections of a structure morphism in schemes. The two are the same datum
(`CategoryTheory.Over.w` one way, `CategoryTheory.Over.homMk` the other), but the slice category is
where `(ℙⁿ_K)^m` is a product, so a rational point of the power is a family of rational points of
the factors by `CategoryTheory.Limits.Pi.hom_ext` and nothing has to be said about the points of
the underlying scheme of a fibre product.

The coordinate `j` at which `x` and `y` differ, which exists because `x ≠ y`, is what feeds
transitivity on the coordinates in `I`: `AlgebraicGeometry.exists_comp_matrixToAut_hom_eq` needs a
pair of distinct rational points of `ℙⁿ_K` to start from, and `xⱼ ≠ yⱼ` is one.

## References

* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The matrix action on rational points, read in the slice category -/

section Slice

variable (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)

/-- A morphism of the slice category is carried to another by the matrix action as soon as the
underlying morphisms of schemes are. -/
private theorem comp_matrixToAutOver_hom_eq_of_left (k : Type u) [Field k] (n : ℕ)
    {a c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (projectiveSpaceOverRing n (.of k)).asOver (Spec (.of k))}
    {M : Matrix.GeneralLinearGroup (Fin (n + 1)) k}
    (h : a.left ≫ (projectiveSpaceMatrixToAut k n M).asIso.hom = c.left) :
    a ≫ (projectiveSpaceMatrixToAutOver k n M).asIso.hom = c := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, projectiveSpaceMatrixToAutOver_hom_left]
  exact h

/-- **The matrix action carries any ordered pair of distinct rational points of `ℙⁿ_K` to any
other**, with the rational points read as morphisms out of the terminal object of the slice
category over `Spec K`. -/
theorem exists_comp_matrixToAutOver_hom_eq_and_eq
    (a b c d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K)))
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ M : Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      a ≫ (projectiveSpaceMatrixToAutOver K n M).asIso.hom = c ∧
        b ≫ (projectiveSpaceMatrixToAutOver K n M).asIso.hom = d := by
  obtain ⟨M, h₁, h₂⟩ := exists_comp_matrixToAut_hom_eq_and_eq K n a.left b.left c.left d.left
    (Over.w a) (Over.w b) (Over.w c) (Over.w d)
    (fun h => hab (Over.OverMorphism.ext h)) (fun h => hcd (Over.OverMorphism.ext h))
  exact ⟨M, comp_matrixToAutOver_hom_eq_of_left K n h₁, comp_matrixToAutOver_hom_eq_of_left K n h₂⟩

/-- **The matrix action is transitive on the rational points of `ℙⁿ_K`**, given a pair of distinct
rational points to start from. -/
theorem exists_comp_matrixToAutOver_hom_eq
    {u v : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))} (huv : u ≠ v)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) :
    ∃ M : Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      a ≫ (projectiveSpaceMatrixToAutOver K n M).asIso.hom = b := by
  obtain ⟨M, h⟩ := exists_comp_matrixToAut_hom_eq K n (u := u.left) (v := v.left)
    (Over.w u) (Over.w v) (fun hh => huv (Over.OverMorphism.ext hh)) a.left b.left
    (Over.w a) (Over.w b)
  exact ⟨M, comp_matrixToAutOver_hom_eq_of_left K n h⟩

end Slice

/-! ### The orbit of a pair of rational points of a power -/

section Power

variable (K : Type u) [Field K] [IsAlgClosed K] (n m : ℕ)

/-- **The `m`-th power of the general linear group carries a pair of distinct rational points of
`(ℙⁿ_K)^m` to every pair with the same coincidence pattern.**

This is the group-theoretic content of the exercise in the proof of [Stacks, Tag 0AEM]: with
`I = {i | xᵢ = yᵢ}`, the pairs `(p, q)` of rational points with `pᵢ = qᵢ` exactly for `i ∈ I` are
the rational points of `(ℙⁿ_K)^m ×_{(ℙⁿ_K)^I} (ℙⁿ_K)^m` off every partial diagonal, and all of
them lie in the orbit of `(x, y)`. -/
theorem exists_comp_powerMatrixAut_hom_eq_and_eq
    (x y p q : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ projectiveSpacePowerOver K n m)
    (hxy : x ≠ y)
    (hpat : ∀ i : Fin m,
      (x ≫ Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i =
          y ≫ Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i) ↔
        (p ≫ Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i =
          q ≫ Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i)) :
    ∃ M : Fin m → Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      x ≫ (projectiveSpacePowerMatrixAut K n m M).asIso.hom = p ∧
        y ≫ (projectiveSpacePowerMatrixAut K n m M).asIso.hom = q := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin m,
      x ≫ Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) j ≠
        y ≫ Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) j := by
    by_contra hcon
    push Not at hcon
    exact hxy (Pi.hom_ext _ _ hcon)
  have key : ∀ i : Fin m, ∃ M : Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      (x ≫ Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i) ≫
          (projectiveSpaceMatrixToAutOver K n M).asIso.hom =
            p ≫ Pi.π (fun _ : Fin m =>
              (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i ∧
        (y ≫ Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i) ≫
          (projectiveSpaceMatrixToAutOver K n M).asIso.hom =
            q ≫ Pi.π (fun _ : Fin m =>
              (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i := by
    intro i
    by_cases hi :
        x ≫ Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i =
          y ≫ Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i
    · obtain ⟨M, hM⟩ := exists_comp_matrixToAutOver_hom_eq K n hj
        (x ≫ Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i)
        (p ≫ Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of K)).asOver (Spec (.of K))) i)
      refine ⟨M, hM, ?_⟩
      rw [← hi, hM]
      exact (hpat i).1 hi
    · exact exists_comp_matrixToAutOver_hom_eq_and_eq K n _ _ _ _ hi
        (fun h => hi ((hpat i).2 h))
  choose M hM₁ hM₂ using key
  refine ⟨M, Pi.hom_ext _ _ fun i => ?_, Pi.hom_ext _ _ fun i => ?_⟩
  · rw [Category.assoc, projectiveSpacePowerMatrixAut_hom_π, ← Category.assoc]
    exact hM₁ i
  · rw [Category.assoc, projectiveSpacePowerMatrixAut_hom_π, ← Category.assoc]
    exact hM₂ i

end Power

end AlgebraicGeometry

end
