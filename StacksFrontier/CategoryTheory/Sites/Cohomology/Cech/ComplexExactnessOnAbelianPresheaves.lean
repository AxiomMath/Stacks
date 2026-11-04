module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.CechComplexExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the Čech complex functor on abelian presheaves

Let `C` be a category, let `U` be an object of `C` and let `𝒰 = {U_i → U}_{i ∈ I}` be a family
of morphisms with target `U` whose finite nonempty fibre products exist, as in Stacks 03OL.
Stacks 03OM is the assertion that the Čech complex functor `Č•(𝒰, -)` of that definition is
exact on the category `PAb(C)` of abelian presheaves on `C`.

The content of the statement is that exactness holds on *presheaves*, where it fails on
sheaves: a sequence of abelian presheaves is exact precisely when it is exact after evaluation
at every object of `C`, so in each degree the Čech complex is a product of exact sequences of
abelian groups, and products of abelian groups are exact.

## Main results

* `Stacks.CechSite.cechComplexFunctor_exact`: the Čech complex functor on abelian presheaves
  is exact.

## Implementation notes

`PAb(C)` is the functor category `Cᵒᵖ ⥤ AddCommGrpCat`, and exactness is Mathlib's
`CategoryTheory.Limits.exactFunctor`, the property of preserving finite limits and finite
colimits. Source and target are both abelian categories, so this is the usual notion of an
exact additive functor; in particular `CategoryTheory.ShortComplex.ShortExact.map_of_exact`
turns it into the preservation of short exact sequences which the source argues directly.

Exactness is read off from the definition of the Čech complex functor, which is a composite of
three steps: restriction of a presheaf on `C` to a presheaf on `Over U`, evaluation of the
resulting presheaf on the formal coproducts `U_{i_0} ×_U … ×_U U_{i_p}`, and the
alternating-face-map complex of the resulting cosimplicial object. Restriction and the
alternating-face-map complex are computed termwise, so they are exact as soon as evaluation is;
evaluation at a formal coproduct is a product of evaluations, so it is exact because abelian
groups satisfy `AB4` and `AB4*` in the relevant size. Those three steps are exactly the
instances supplied by `StacksFrontier.CategoryTheory.Sites.CechComplexExactness`, so the only
work left here is to make `AB4*` available in the universe where the products are taken.

The universe of the abelian groups is enlarged to `max w uAb` so that it contains the universe
`w` indexing the products which the Čech complex takes; this is what makes those products, and
the `AB4*` property controlling their exactness, available.

## References

* [Stacks Project, Tag 03OM](https://stacks.math.columbia.edu/tag/03OM)
* [Stacks Project, Tag 03OL](https://stacks.math.columbia.edu/tag/03OL)
* [Stacks Project, Tag 03AQ](https://stacks.math.columbia.edu/tag/03AQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uAb

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

/-- **Stacks Project, Tag 03OM.** The Čech complex functor of Stacks 03OL is exact on the
category `PAb(C)` of abelian presheaves on `C`. -/
@[stacks 03OM]
theorem cechComplexFunctor_exact
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    exactFunctor
      (CategoryTheory.Functor Cᵒᵖ AddCommGrpCat.{max w uAb})
      (CochainComplex AddCommGrpCat.{max w uAb} ℕ)
      (cechComplexFunctor (A := AddCommGrpCat.{max w uAb}) E) := by
  have : AB4StarOfSize.{w} AddCommGrpCat.{max w uAb} := ⟨fun I ↦
    HasExactLimitsOfShape.of_domain_equivalence AddCommGrpCat.{max w uAb}
      (Discrete.equivalence (Equiv.ulift.{uAb} : ULift.{uAb} I ≃ I))⟩
  refine (exactFunctor_iff _).2 ?_
  unfold cechComplexFunctor FormalCoproduct.cochainComplexFunctor
    FormalCoproduct.cosimplicialObjectFunctor
  exact ⟨inferInstance, inferInstance⟩

end Stacks.CechSite
end
