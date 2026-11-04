module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.CechComplexOfAFiniteFamily

/-!
# The Čech complex of a finite family and colimits of presheaves

Let `E = {U_i → X}` be a finite family of morphisms of a category with finite products whose
iterated fibre products over `X` exist. The Čech complex of Stacks 03AM attached to `E`, as a
functor of the presheaf, preserves colimits: colimits of cochain complexes are computed
degreewise, and the degree-`n` term is the finite product of the values of the presheaf on the
`(n + 1)`-fold fibre products. Consequently a filtered colimit of presheaves of abelian groups
whose Čech complexes are exact in a positive degree has a Čech complex exact in that degree.

## Main results

* `Stacks.CechSite.cechComplexFunctor_comp_eval`: the degree-`n` term of the Čech complex is the
  product of the values on the `(n + 1)`-fold fibre products.
* `Stacks.CechSite.preservesColimitsOfShape_cechComplexFunctor`: the Čech complex of a finite
  family preserves colimits.
* `Stacks.CechSite.exactAt_succ_cechComplex_colimit`: exactness in a positive degree passes to
  filtered colimits.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 00DB](https://stacks.math.columbia.edu/tag/00DB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe j j' w v v' u u'

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]

/-- **The degree-`n` term of the Čech complex, functorially.** It is the product of the values of
the presheaf on the `(n + 1)`-fold fibre products of the family. -/
theorem cechComplexFunctor_comp_eval [HasCoproducts.{w} A] [HasFiniteProducts C] (n : ℕ) :
    cechComplexFunctor (A := A) E ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) n =
      Stacks.Cohomology.CechColimit.piEval (A := A) (Fin (n + 1) → E.I₀)
        (fun i ↦ (∏ᶜ fun a ↦ Over.mk (E.f (i a))).left) :=
  rfl

/-- **The Čech complex of a finite family preserves colimits** of any shape. -/
theorem preservesColimitsOfShape_cechComplexFunctor [HasCoproducts.{w} A] [HasFiniteProducts C]
    [Finite E.I₀] {J : Type j} [Category.{j'} J] [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (cechComplexFunctor (A := A) E) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦ by
    rw [cechComplexFunctor_comp_eval]
    exact Stacks.Cohomology.CechColimit.preservesColimitsOfShape_piEval _ _

/-- **Exactness of the Čech complex in a positive degree passes to filtered colimits.** -/
theorem exactAt_succ_cechComplex_colimit [HasFiniteProducts C] [Finite E.I₀]
    [HasProducts.{w} AddCommGrpCat.{u'}] [HasCoproducts.{w} AddCommGrpCat.{u'}]
    {J : Type j} [Category.{j'} J] [IsFiltered J] [HasColimitsOfShape J AddCommGrpCat.{u'}]
    [PreservesColimitsOfShape J (forget AddCommGrpCat.{u'})]
    (D : J ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u'})) (n : ℕ)
    (h : ∀ i, (cechComplex E (D.obj i)).ExactAt (n + 1)) :
    (cechComplex E (colimit D)).ExactAt (n + 1) := by
  have := preservesColimitsOfShape_cechComplexFunctor (A := AddCommGrpCat.{u'}) E (J := J)
  exact Stacks.Cohomology.CechColimit.exactAt_succ_of_isColimit
    (isColimitOfPreserves (cechComplexFunctor (A := AddCommGrpCat.{u'}) E)
      (colimit.isColimit D)) n h

end Stacks.CechSite
