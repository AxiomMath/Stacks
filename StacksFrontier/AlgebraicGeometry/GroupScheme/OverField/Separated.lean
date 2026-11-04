module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Separation

/-!
# Group schemes over fields are separated

The underlying scheme of a group scheme over the spectrum of a field is separated.  The
identity section of a group scheme over a field is a closed immersion, because a section of a
morphism to the spectrum of a field always is, so the structure morphism is separated; the
spectrum of a field is terminal in schemes, so the underlying scheme is separated absolutely.

## Main results

* `AlgebraicGeometry.isSeparated_of_groupScheme_over_field` proves that every group scheme over
  a field is separated as a scheme.

## Implementation notes

A group scheme over `Spec k` is represented as a group object in the category of schemes over
`Spec k`.  The conclusion concerns the underlying scheme of this object and is absolute
separatedness, as in the source.

## References

* [Stacks Project, Tag 047L](https://stacks.math.columbia.edu/tag/047L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory MonObj

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 047L.** The underlying scheme of a group scheme over a field is
separated. -/
@[stacks 047L, sga "3 VIB 1.1" "(2), special case", sga "3 VIB 6.2.4", sga "3 VIII 6.5" "partial"]
theorem isSeparated_of_groupScheme_over_field {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : G.X.left.IsSeparated := by
  let : GrpObj (Over.mk G.X.hom) :=
    GrpObj.ofIso (show G.X ≅ Over.mk G.X.hom from Over.isoMk (Iso.refl _))
  let : IsSeparated G.X.hom :=
    (isSeparated_iff_isClosedImmersion_one G.X.hom).2 inferInstance
  exact ⟨by
    simpa using
      (show IsSeparated (G.X.hom ≫ terminal.from (Spec (.of k))) from inferInstance)⟩

end AlgebraicGeometry

end
