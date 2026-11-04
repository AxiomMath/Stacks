module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# A double coproduct with vanishing off-diagonal terms is the diagonal coproduct

Let `T : ι → ι → C` be a doubly indexed family of objects of a preadditive category and suppose
`T n m` is a zero object whenever `m ≠ n`.  Then the coproduct of `T` over all pairs is the
coproduct of its diagonal:

`∐_{(n, m) ∈ ι × ι} T n m ≅ ∐_{n ∈ ι} T n n`.

## Main definitions

* `CategoryTheory.Limits.sigmaIsoOfIsZeroOffDiagonal`: the isomorphism above.

## Main results

* `CategoryTheory.Limits.ι_comp_sigmaIsoOfIsZeroOffDiagonal_hom` and
  `CategoryTheory.Limits.ι_comp_sigmaIsoOfIsZeroOffDiagonal_inv`: the isomorphism carries the
  `(n, n)`-th inclusion of the double coproduct to the `n`-th inclusion of the diagonal
  coproduct, and conversely.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type w} (T : ι → ι → C)
  (h : ∀ n m, m ≠ n → IsZero (T n m))
  [HasCoproduct fun p : ι × ι => T p.1 p.2] [HasCoproduct fun n => T n n]

/-- The diagonal coproduct included in the double coproduct: on the `n`-th summand it is the
`(n, n)`-th inclusion. -/
def sigmaDiagonalToPairs : (∐ fun n => T n n) ⟶ ∐ fun p : ι × ι => T p.1 p.2 :=
  Sigma.desc fun n => Sigma.ι (fun p : ι × ι => T p.1 p.2) (n, n)

/-- The double coproduct projected to the diagonal coproduct: on the `(n, m)`-th summand it is
the `n`-th inclusion when `m = n` and the zero map otherwise. -/
def sigmaPairsToDiagonal : (∐ fun p : ι × ι => T p.1 p.2) ⟶ ∐ fun n => T n n :=
  letI := Classical.decEq ι
  Sigma.desc fun p => if hp : p.2 = p.1 then
      eqToHom (congrArg (T p.1) hp) ≫ Sigma.ι (fun n => T n n) p.1
    else 0

/-- **A double coproduct whose off-diagonal terms are zero objects is the coproduct of its
diagonal.**

Its components are `sigmaPairsToDiagonal` and `sigmaDiagonalToPairs`. -/
def sigmaIsoOfIsZeroOffDiagonal :
    (∐ fun p : ι × ι => T p.1 p.2) ≅ ∐ fun n => T n n where
  hom := sigmaPairsToDiagonal T
  inv := sigmaDiagonalToPairs T
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun p => ?_
    rw [Category.comp_id, ← Category.assoc, sigmaPairsToDiagonal, Sigma.ι_desc]
    by_cases hp : p.2 = p.1
    · obtain ⟨a, b⟩ := p
      cases hp
      rw [dif_pos (rfl : a = a)]
      simp [sigmaDiagonalToPairs]
    · exact (h p.1 p.2 hp).eq_of_src _ _
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [Category.comp_id, ← Category.assoc, sigmaDiagonalToPairs, Sigma.ι_desc,
      sigmaPairsToDiagonal, Sigma.ι_desc, dif_pos (rfl : n = n)]
    simp

/-- The isomorphism carries the `(n, n)`-th inclusion of the double coproduct to the `n`-th
inclusion of the diagonal coproduct. -/
@[simp] theorem ι_comp_sigmaIsoOfIsZeroOffDiagonal_hom (n : ι) :
    Sigma.ι (fun p : ι × ι => T p.1 p.2) (n, n) ≫ (sigmaIsoOfIsZeroOffDiagonal T h).hom =
      Sigma.ι (fun n => T n n) n := by
  show Sigma.ι (fun p : ι × ι => T p.1 p.2) (n, n) ≫ sigmaPairsToDiagonal T = _
  rw [sigmaPairsToDiagonal, Sigma.ι_desc, dif_pos (rfl : n = n)]
  simp

/-- The inverse of the isomorphism carries the `n`-th inclusion of the diagonal coproduct to the
`(n, n)`-th inclusion of the double coproduct. -/
@[simp] theorem ι_comp_sigmaIsoOfIsZeroOffDiagonal_inv (n : ι) :
    Sigma.ι (fun n => T n n) n ≫ (sigmaIsoOfIsZeroOffDiagonal T h).inv =
      Sigma.ι (fun p : ι × ι => T p.1 p.2) (n, n) := by
  show Sigma.ι (fun n => T n n) n ≫ sigmaDiagonalToPairs T = _
  rw [sigmaDiagonalToPairs, Sigma.ι_desc]

end CategoryTheory.Limits

end
