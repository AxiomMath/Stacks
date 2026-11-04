module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# Connected colimits of algebra sheaves are colimits of the underlying sheaves of rings

Both halves of Stacks Tag 05JT and all of Stacks Tag 0817 assert that a cocone of algebra
sheaves is colimiting, i.e. a colimit in `CategoryTheory.Under X.sheaf`.  The indexing category
is filtered, hence connected, and for a connected indexing category
`CategoryTheory.Under.forget` *creates* colimits
(`CategoryTheory.Under.createsColimitsOfShapeForgetOfIsConnected`), so it both preserves and
reflects them.  Therefore such an assertion is equivalent to the corresponding assertion about
the underlying sheaves of commutative rings, with the structure morphisms discarded.

This file records that equivalence, which shows that the `CategoryTheory.Under` layer costs
nothing: the whole difficulty of both tags is in the sheaf category.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.isColimit_of_isColimit_forget`: the reflection direction.
* `Stacks.RelativeSpec.AlgebraSheaf.nonempty_isColimit_iff`: both directions, in the
  `Nonempty` form in which Tag 05JT states its colimit assertion.

## Implementation notes

The indexing category is only assumed connected, not filtered: that is all
`CategoryTheory.Under.createsColimitsOfShapeForgetOfIsConnected` needs, and a filtered category
is connected.  No hypothesis on the scheme is used, and no colimits need exist in either
category -- the statements are about a given cocone.

What is *not* reduced by this is the remaining step, which is the real content of both tags: a
filtered colimit of sheaves of commutative rings is the sheafification of the pointwise
colimit, so identifying it with a given sheaf requires knowing that the pointwise colimit is
already a sheaf.  On a quasi-compact and quasi-separated scheme that is where
`CompactSpace X` and `QuasiSeparatedSpace X` enter: sections over an affine open commute with
the filtered colimit.  Nothing here supplies that.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [The Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v w u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}} {K : Type w} [Category.{v} K] [IsConnected K]
  {F : K ⥤ AlgebraSheaf X}

/-- **A cocone of algebra sheaves over a connected diagram is colimiting as soon as the
underlying cocone of sheaves of rings is.**  `CategoryTheory.Under.forget` creates, hence
reflects, colimits of connected shape. -/
def isColimit_of_isColimit_forget (c : Cocone F)
    (hc : IsColimit ((Under.forget X.sheaf).mapCocone c)) : IsColimit c :=
  isColimitOfReflects _ hc

/-- A cocone of algebra sheaves over a connected diagram is colimiting exactly when the
underlying cocone of sheaves of commutative rings is.  This is the form in which the colimit
assertion of Stacks Tag 05JT is stated. -/
theorem nonempty_isColimit_iff (c : Cocone F) :
    Nonempty (IsColimit c) ↔ Nonempty (IsColimit ((Under.forget X.sheaf).mapCocone c)) :=
  ⟨fun ⟨hc⟩ => ⟨isColimitOfPreserves _ hc⟩, fun ⟨hc⟩ => ⟨isColimit_of_isColimit_forget c hc⟩⟩

end Stacks.RelativeSpec.AlgebraSheaf
