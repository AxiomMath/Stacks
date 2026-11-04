module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectStalks
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of abelian sheaves is checked on stalks

For a conservative family of points of a site, a short complex of abelian sheaves is exact if
and only if its stalks at the points of the family are exact; this is
`Stacks.StalkExact.exact_iff_forall_sheafFiber_exact`, registered here. If the site has enough
points, a short complex of abelian sheaves is exact if and only if its stalks at all points are
exact.

## Main results

* `Stacks.StalkExact.exact_iff_forall_sheafFiber_exact`: for a conservative family of points,
  exactness of a short complex of abelian sheaves is checked on the stalks at those points.
* `Stacks.StalkExact.exact_iff_forall_sheafFiber_exact_of_hasEnoughPoints`: on a site with enough
  points, exactness of a short complex of abelian sheaves is checked on stalks.

## References

* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
-/

@[expose] public section

add_to_stacks 05V3 "conservative family of points"
  Stacks.StalkExact.exact_iff_forall_sheafFiber_exact

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.StalkExact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  [HasSheafify J AddCommGrpCat.{w}] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- On a site with enough points, a short complex of abelian sheaves is exact if and only if its
stalks at all points are exact. -/
@[stacks 05V3 "enough points"]
theorem exact_iff_forall_sheafFiber_exact_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{w} J] (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) :
    S.Exact ↔ ∀ Φ : J.Point.{w}, (S.map (Φ.sheafFiber (A := AddCommGrpCat.{w}))).Exact := by
  obtain ⟨P, -, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty J
  exact ⟨fun h _ => h.map _,
    fun h => (exact_iff_forall_sheafFiber_exact hP S).mpr fun Φ => h Φ.obj⟩

end Stacks.StalkExact
