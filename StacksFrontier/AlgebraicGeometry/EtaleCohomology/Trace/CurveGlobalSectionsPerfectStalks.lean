module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Exactness of abelian sheaves on stalks, at every coefficient universe

Let `P` be a conservative family of points of a site relative to a universe `w`. The stalk functor
at a point is exact on abelian sheaves with coefficients in `AddCommGrpCat.{w}`, and a short
complex of such sheaves is exact if and only if all its stalks at the points of `P` are. This is
Stacks 05PP for an arbitrary coefficient universe;
`Stacks.Injectives.exact_iff_forall_sheafFiber_exact` is the case of the universe of the
morphisms of the site. It is the form in which the proof of [Stacks, Tag 03TV] checks the
exactness of a complex of twisted sheaves on the geometric fibre.

## Main results

* `Stacks.StalkExact.sheafFiber_preservesHomology`: stalk functors are exact.
* `Stacks.StalkExact.exact_iff_forall_sheafFiber_exact`: exactness is checked on stalks.

## References

* [Stacks Project, Tag 05PP](https://stacks.math.columbia.edu/tag/05PP)
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.StalkExact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  [HasSheafify J AddCommGrpCat.{w}]

/-- The stalk of an abelian sheaf at a point is additive. -/
instance sheafFiber_additive (Φ : GrothendieckTopology.Point.{w} J) :
    (Φ.sheafFiber (A := AddCommGrpCat.{w})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The stalk functor at a point is exact on abelian sheaves**: it preserves finite limits and
is a left adjoint. -/
instance sheafFiber_preservesHomology (Φ : GrothendieckTopology.Point.{w} J) :
    (Φ.sheafFiber (A := AddCommGrpCat.{w})).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- **Stacks 05PP at every coefficient universe.** A short complex of abelian sheaves is exact if
and only if its stalks at a conservative family of points are exact. -/
theorem exact_iff_forall_sheafFiber_exact
    {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints)
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) :
    S.Exact ↔ ∀ Φ : P.FullSubcategory,
      (S.map (Φ.obj.sheafFiber (A := AddCommGrpCat.{w}))).Exact := by
  refine ⟨fun h Φ => h.map _, fun h => ?_⟩
  rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
  refine (hP.jointlyFaithful AddCommGrpCat.{w}).map_injective fun Φ => ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1
    ((S.leftHomologyData.exact_map_iff Φ.obj.sheafFiber).1 (h Φ))

end Stacks.StalkExact

end
