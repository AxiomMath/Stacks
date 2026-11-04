module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Transport

/-!
# Commutativity transfers along the comparisons

`Stacks.GradedAlgebra.ofComparison` builds a sheaf of graded algebras from a graded algebra of
presheaves of modules and a locally bijective comparison into a prescribed family of sheaves. Its
associativity and unit laws are proved there, by restricting to a cover on which both sides are
comparison images of sections of the presheaf algebra. **Commutativity is not a field of
`SheafOfModules.GradedAlgebra`**, so it is not among them; this file proves it by the same
argument.

The statement is needed because
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, the input of the relative Proj
construction, requires commutativity in *every* pair of degrees, whereas what the symmetric
algebra's construction records is
`SheafOfModules.GradedAlgebra.PairwiseCommutes`, commutation of two degree-*one* generators.

## Main results

* `Stacks.GradedAlgebra.heq_ofComparison_mul_comm`: if the multiplication of the presheaf algebra
  is commutative then so is the multiplication of the transported sheaf algebra.
* `Stacks.GradedAlgebra.heq_sheafify_mul_comm`: the same for the other route to a sheaf of graded
  algebras, `Stacks.GradedAlgebra.sheafify`, which is the one a construction on an arbitrary site
  has to use, there being no prescribed family of sheaves to compare with.

## Implementation notes

The proof is the proof of the `mul_assoc` field of `Stacks.GradedAlgebra.ofComparison`, with
`add_comm` in place of `add_assoc` and two local lifts in place of three: restrict to the
intersection of the two sieves of local lifts, rewrite both products with
`ofComparison_mul_restrict`, and apply the presheaf-level commutativity under the comparison with
`Stacks.heq_apply`. The equality of sheaves that `Stacks.heq_of_isSeparated` consumes is
`congrArg S (add_comm i j)`: the two sides are sections of the pieces of degrees `i + j` and
`j + i`, which are equal but not definitionally so.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)

## Not done here

No tag is claimed: Tag 0FQW defines graded algebras and their morphisms, and this file adds a
property of one construction of them rather than any part of that definition.

Nothing is said about the degree-one generator, about morphisms of graded algebras, or about the
universal property of the symmetric algebra.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PresheafOfModules

namespace Stacks.GradedAlgebra

universe v u t a

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {P : ℤ → PresheafOfModules.{a} R.obj} (A : GradedAlgebra P)
  (S : ℤ → SheafOfModules.{a} R) (u : ∀ n, P n ⟶ (S n).val)
  [∀ n, PresheafOfModules.IsLocallySurjective J (u n)]
  [∀ n, PresheafOfModules.IsLocallyInjective J (u n)]

/-- **Commutativity transfers along the comparisons.** If the multiplication of the presheaf
algebra `A` is commutative in every pair of degrees, then so is the multiplication of the sheaf
algebra `A.ofComparison S u`. -/
public theorem heq_ofComparison_mul_comm
    (hc : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
      HEq ((A.mul i j).app X x y) ((A.mul j i).app X y x))
    (i j : ℤ) (X : C) (a : ((A.ofComparison S u).piece i).val.obj (op X))
    (b : ((A.ofComparison S u).piece j).val.obj (op X)) :
    HEq (((A.ofComparison S u).mul i j).app (op X) a b)
      (((A.ofComparison S u).mul j i).app (op X) b a) := by
  refine heq_of_isSeparated (congrArg S (add_comm i j))
    (J.intersection_covering (cmpSieve_mem (u i) a) (cmpSieve_mem (u j) b)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  refine (heq_of_eq (A.cmpMul_restrict S u i j f.op a b x₀ y₀ hx₀ hy₀)).trans
    (HEq.trans ?_ (heq_of_eq (A.cmpMul_restrict S u j i f.op b a y₀ x₀ hy₀ hx₀)).symm)
  exact heq_apply _ _ (fun n s => Hom.app (u n) (op Y) s) (add_comm i j) (hc i j (op Y) x₀ y₀)

section Sheafify

variable {R₀ : Cᵒᵖ ⥤ RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {Q : ℤ → PresheafOfModules.{a} R₀} (B : GradedAlgebra Q)

/-- **Commutativity transfers along the sheafification units.** The same statement for
`Stacks.GradedAlgebra.sheafify` in place of `Stacks.GradedAlgebra.ofComparison`: the degreewise
sheafification of a commutative graded algebra of presheaves of modules is commutative.

This is the form needed by a construction that sheafifies a sectionwise symmetric algebra on an
arbitrary site, rather than comparing it with a prescribed family of sheaves. -/
public theorem heq_sheafify_mul_comm
    (hc : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (Q i).obj X) (y : (Q j).obj X),
      HEq ((B.mul i j).app X x y) ((B.mul j i).app X y x))
    (i j : ℤ) (X : C) (a : ((B.sheafify α).piece i).val.obj (op X))
    (b : ((B.sheafify α).piece j).val.obj (op X)) :
    HEq (((B.sheafify α).mul i j).app (op X) a b)
      (((B.sheafify α).mul j i).app (op X) b a) := by
  refine heq_of_isSeparated
    (congrArg (fun n : ℤ => (PresheafOfModules.sheafification α).obj (Q n)) (add_comm i j))
    (J.intersection_covering (liftSieve_mem α (Q i) a) (liftSieve_mem α (Q j) b)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  refine (heq_of_eq (B.sheafifyMul_restrict α i j f.op a b x₀ y₀ hx₀ hy₀)).trans
    (HEq.trans ?_ (heq_of_eq (B.sheafifyMul_restrict α j i f.op b a y₀ x₀ hy₀ hx₀)).symm)
  exact heq_apply _ _
    (fun n s => Hom.app (PresheafOfModules.sheafifyUnit α (Q n)) (op Y) s) (add_comm i j)
    (hc i j (op Y) x₀ y₀)

end Sheafify

end Stacks.GradedAlgebra

end
