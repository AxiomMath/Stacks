module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# The Moore complex of a constant cosimplicial object

The Moore complex of [Stacks, Tag 019I] — `AlgebraicTopology.alternatingCofaceMapComplex`, the
alternating sum of the coface maps — of a *constant* cosimplicial object on `X` has every term
equal to `X`, and every coface map equal to the identity, so its differential out of degree `n` is
the alternating sum of `n + 2` copies of the identity:

`d⁰ = 0, d¹ = 𝟙, d² = 0, d³ = 𝟙, …`

Such a complex is therefore `X` in degree `0` and exact in every positive degree, in any abelian
category. They are the columns of the double complex of a cochain complex of constant cosimplicial
objects (`AlgebraicTopology.constantCosimplicialCochainComplex`), which occurs in
[Stacks, Proposition 60.21.3, Tag 07LG].

## Main definitions

* `AlgebraicTopology.constantAlternatingCofaceMapComplex` — the Moore complex of the constant
  cosimplicial object on `X`.

## Main results

* `AlgebraicTopology.constantAlternatingCofaceMapComplex_d` — **its differential is `0` out of an
  even degree and the identity out of an odd one.**
* `AlgebraicTopology.constantAlternatingCofaceMapComplex_d_zero_one` — in particular the
  differential out of degree `0` vanishes, so the degree-`0` cocycles are all of `X`.
* `AlgebraicTopology.constantAlternatingCofaceMapComplex_exactAt` — **it is exact in every
  positive degree.**

## References

* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

/-- **The constant cosimplicial object functor is additive**, the addition of cosimplicial objects
being computed degreewise and the constant object being constant in every degree. -/
public instance cosimplicialObjectConstAdditive :
    (CosimplicialObject.const C).Additive where
  map_add := by intros; ext; simp

/-- **A cochain complex of constant cosimplicial objects**, the constant cosimplicial object
functor applied in each degree.  The row `b` of the double complex of
`AlgebraicTopology.alternatingCofaceMapComplex` applied to this is the original complex again,
independently of `b`, and its columns are the complexes
`AlgebraicTopology.constantAlternatingCofaceMapComplex`. -/
public def constantCosimplicialCochainComplex :
    CochainComplex C ℕ ⥤ CochainComplex (CosimplicialObject C) ℕ :=
  (CosimplicialObject.const C).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The degree `a` of a cochain complex of constant cosimplicial objects is the constant
cosimplicial object on the degree `a`. -/
public theorem constantCosimplicialCochainComplex_obj_X (R : CochainComplex C ℕ) (a : ℕ) :
    (constantCosimplicialCochainComplex.obj R).X a = (CosimplicialObject.const C).obj (R.X a) :=
  rfl

/-- **The Moore complex of the constant cosimplicial object on `X`**: every term is `X` and the
differential out of degree `n` is the alternating sum of `n + 2` copies of the identity, hence
`0` for even `n` and `𝟙` for odd `n` by
`AlgebraicTopology.constantAlternatingCofaceMapComplex_d`. -/
public abbrev constantAlternatingCofaceMapComplex (X : C) : CochainComplex C ℕ :=
  (alternatingCofaceMapComplex C).obj ((CosimplicialObject.const C).obj X)

/-- Every term of the Moore complex of a constant cosimplicial object is the object itself. -/
public theorem constantAlternatingCofaceMapComplex_X (X : C) (n : ℕ) :
    (constantAlternatingCofaceMapComplex X).X n = X := rfl

private theorem constantAlternatingCofaceMapComplex_d_eq (X : C) (n : ℕ) :
    (constantAlternatingCofaceMapComplex X).d n (n + 1) =
      AlternatingCofaceMapComplex.objD ((CosimplicialObject.const C).obj X) n := by
  change (CochainComplex.of _ _ (AlternatingCofaceMapComplex.d_squared _)).d n (n + 1) = _
  exact CochainComplex.of_d
    (fun n : ℕ ↦ ((CosimplicialObject.const C).obj X).obj (.mk n))
    (AlternatingCofaceMapComplex.objD ((CosimplicialObject.const C).obj X)) n

private theorem constantAlternatingCofaceMapComplex_sum_id (X : C) (n : ℕ) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (𝟙 X : X ⟶ X)) = (if Even n then 0 else 𝟙 X) := by
  let φ : ℤ →+ (X ⟶ X) :=
    { toFun := fun z => z • (𝟙 X : X ⟶ X)
      map_zero' := by simp
      map_add' := by intro a b; simp [add_zsmul] }
  calc
    _ = ∑ i : Fin (n + 2), φ ((-1 : ℤ) ^ (i : ℕ)) := rfl
    _ = φ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) := by rw [map_sum]
    _ = φ (if Even (n + 2) then 0 else 1) := by rw [Fin.sum_neg_one_pow]
    _ = if Even n then 0 else 𝟙 X := by
      by_cases hn : Even n <;> simp [φ, hn, Nat.even_add_one]

/-- **The differential of the Moore complex of a constant cosimplicial object is `0` out of an
even degree and the identity out of an odd one.** -/
public theorem constantAlternatingCofaceMapComplex_d (X : C) (n : ℕ) :
    (constantAlternatingCofaceMapComplex X).d n (n + 1) =
      (if Even n then 0 else 𝟙 ((constantAlternatingCofaceMapComplex X).X n)) := by
  rw [constantAlternatingCofaceMapComplex_d_eq]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (𝟙 X : X ⟶ X)) = _
  have hx : (constantAlternatingCofaceMapComplex X).X n = X := rfl
  cases hx
  exact constantAlternatingCofaceMapComplex_sum_id X n

/-- The differential out of an even degree vanishes. -/
public theorem constantAlternatingCofaceMapComplex_d_of_even (X : C) {n : ℕ} (hn : Even n) :
    (constantAlternatingCofaceMapComplex X).d n (n + 1) = 0 := by
  rw [constantAlternatingCofaceMapComplex_d X n, ite_eq_left hn]
  rfl

/-- The differential out of an odd degree is the identity. -/
public theorem constantAlternatingCofaceMapComplex_d_of_not_even (X : C) {n : ℕ}
    (hn : ¬ Even n) : (constantAlternatingCofaceMapComplex X).d n (n + 1) =
      𝟙 ((constantAlternatingCofaceMapComplex X).X n) := by
  rw [constantAlternatingCofaceMapComplex_d X n, ite_eq_right hn]

/-- The differential out of degree `0` vanishes: `d⁰ = δ⁰ - δ¹` and both coface maps of a
constant cosimplicial object are the identity. -/
public theorem constantAlternatingCofaceMapComplex_d_zero_one (X : C) :
    (constantAlternatingCofaceMapComplex X).d 0 1 = 0 :=
  constantAlternatingCofaceMapComplex_d_of_even X ⟨0, rfl⟩

end Preadditive

section Abelian

variable [Abelian C]

/-- **The Moore complex of a constant cosimplicial object is exact in every positive degree.** -/
public theorem constantAlternatingCofaceMapComplex_exactAt (X : C) (n : ℕ) (hn : 0 < n) :
    (constantAlternatingCofaceMapComplex X).ExactAt n := by
  obtain ⟨n, rfl⟩ : ∃ m, m + 1 = n := ⟨n - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' (constantAlternatingCofaceMapComplex X)
    n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  by_cases he : Even n
  · have hf : ((constantAlternatingCofaceMapComplex X).sc' n (n + 1) (n + 1 + 1)).f = 0 :=
      constantAlternatingCofaceMapComplex_d_of_even X he
    have hg : ((constantAlternatingCofaceMapComplex X).sc' n (n + 1) (n + 1 + 1)).g =
        𝟙 ((constantAlternatingCofaceMapComplex X).X (n + 1)) :=
      constantAlternatingCofaceMapComplex_d_of_not_even X (by simp [Nat.even_add_one, he])
    rw [ShortComplex.exact_iff_mono _ hf, hg]
    exact inferInstanceAs (Mono (𝟙 ((constantAlternatingCofaceMapComplex X).X (n + 1))))
  · have hf : ((constantAlternatingCofaceMapComplex X).sc' n (n + 1) (n + 1 + 1)).f =
        𝟙 ((constantAlternatingCofaceMapComplex X).X n) :=
      constantAlternatingCofaceMapComplex_d_of_not_even X he
    have hg : ((constantAlternatingCofaceMapComplex X).sc' n (n + 1) (n + 1 + 1)).g = 0 :=
      constantAlternatingCofaceMapComplex_d_of_even X (by simp [Nat.even_add_one, he])
    rw [ShortComplex.exact_iff_epi _ hg, hf]
    exact inferInstanceAs (Epi (𝟙 ((constantAlternatingCofaceMapComplex X).X n)))

/-- The Moore complex of a constant cosimplicial object is exact in every nonzero degree. -/
public theorem constantAlternatingCofaceMapComplex_exactAt_of_ne_zero (X : C) (n : ℕ)
    (hn : n ≠ 0) : (constantAlternatingCofaceMapComplex X).ExactAt n :=
  constantAlternatingCofaceMapComplex_exactAt X n (by omega)

end Abelian

end AlgebraicTopology

end
