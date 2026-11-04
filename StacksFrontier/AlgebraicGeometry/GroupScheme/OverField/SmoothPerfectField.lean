module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Differentials
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.SmoothCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.LocallyFreeDifferentialsPerfectField

/-!
# Smoothness of a reduced group scheme over a perfect field

Let `k` be a perfect field and let `G` be a locally algebraic group scheme over `k`, that is, a
scheme whose structure morphism `f : G ⟶ Spec k` is locally of finite type and which carries a
group object structure in the category of schemes over `Spec k`. If `G` is reduced then `f` is
smooth.

## Main results

* `AlgebraicGeometry.smooth_of_isReduced_groupScheme_of_perfectField`: the structure morphism of a
  reduced locally algebraic group scheme over a perfect field is smooth.

## References

* [Stacks Project, Tag 047P](https://stacks.math.columbia.edu/tag/047P)
* [Stacks Project, Tag 047I](https://stacks.math.columbia.edu/tag/047I)
* [Stacks Project, Tag 04QP](https://stacks.math.columbia.edu/tag/04QP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace AlgebraicGeometry

/-- A sheaf of modules isomorphic to a free sheaf of modules is locally free. -/
private alias isLocallyFree_of_iso_toFree := isLocallyFree_of_iso_free

/-- Let `k` be a perfect field and let `G` be a reduced locally algebraic group scheme over `k`,
that is, a reduced scheme whose structure morphism `f : G ⟶ Spec k` is locally of finite type and
which is a group object over `Spec k`. Then `f` is smooth. -/
@[stacks 047P,
  ega "IV 15.6.10" "special case",
  sga "3 VIIA 8.3" "Smoothness clause",
  sga "3 XII 1.0" "partial",
  sga "3 XV 4.6" "(2), special case"]
theorem smooth_of_isReduced_groupScheme_of_perfectField (k : Type u) [Field k] [PerfectField k]
    (G : Scheme.{u}) (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)]
    [LocallyOfFiniteType f] [IsReduced G] :
    Smooth f := by
  obtain ⟨I, ⟨e⟩⟩ :=
    GroupSchemeDifferentials.exists_free_iso_relativeDifferentials_of_field k G f
  exact smooth_of_isLocallyFree_relativeDifferentials_of_perfectField f
    (isLocallyFree_of_iso_toFree.{u, u, u} e)

end AlgebraicGeometry

end
