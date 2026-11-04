module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductDecomposition

/-!
# Recognising a groupoid scheme as a disjoint union

`AlgebraicGeometry.GroupoidScheme.IsCoproductDecomposition` asks that two morphisms of groupoid
schemes `F₁ : G₁ ⟶ G` and `F₂ : G₂ ⟶ G` induce isomorphisms out of the binary coproducts of the
object schemes and of the arrow schemes. This file produces such a decomposition from data one
can actually check: the four structure morphisms are open immersions, and on object schemes as
well as on arrow schemes the two open ranges are complementary.

That is the shape in which a disjoint union decomposition of a groupoid scheme arises — from a
clopen decomposition of the object scheme which is invariant, so that the induced decomposition
of the arrow scheme is again clopen. In particular it is the shape in which the "Claim" of
[Stacks Project, Tag 0DT9] produces one.

## Main results

* `AlgebraicGeometry.isIso_coprod_desc_of_isCompl`: two open immersions with complementary open
  ranges exhibit their common target as a binary coproduct.
* `AlgebraicGeometry.GroupoidScheme.isCoproductDecomposition_of_isCompl`: **the criterion** —
  complementary open ranges on objects and on arrows give a disjoint union decomposition of a
  groupoid scheme.

## Implementation notes

`AlgebraicGeometry.isIso_coprod_desc_of_isCompl` is a statement about schemes alone and would sit
equally well beside the other properties of binary coproducts of schemes; it is kept here, with
the one result that consumes it, to avoid widening the import surface of a heavily used module.
Mathlib supplies the colimit form, `nonempty_isColimit_binaryCofanMk_of_isCompl`; what is added
is the identification of the canonical morphism out of the chosen coproduct with
`CategoryTheory.Limits.IsColimit.desc`, which is what `IsCoproductDecomposition` is phrased with.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry

/-- **Two open immersions with complementary open ranges exhibit their target as a binary
coproduct.** -/
theorem isIso_coprod_desc_of_isCompl {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (h : IsCompl f.opensRange g.opensRange) :
    IsIso (coprod.desc f g) := by
  have hiso : IsIso ((coprodIsCoprod X Y).desc (BinaryCofan.mk f g)) :=
    ((coprodIsCoprod X Y).nonempty_isColimit_iff_isIso_desc).mp
      (nonempty_isColimit_binaryCofanMk_of_isCompl f g h)
  have heq : coprod.desc f g = (coprodIsCoprod X Y).desc (BinaryCofan.mk f g) :=
    (coprodIsCoprod X Y).uniq (BinaryCofan.mk f g) (coprod.desc f g) <| by
      intro j
      rcases j with ⟨(_ | _)⟩
      · exact coprod.inl_desc f g
      · exact coprod.inr_desc f g
  rw [heq]
  exact hiso

namespace GroupoidScheme

variable {S : Scheme.{u}} {G G₁ G₂ : GroupoidScheme S} (F₁ : GroupoidScheme.Hom G₁ G)
  (F₂ : GroupoidScheme.Hom G₂ G)

/-- **A groupoid scheme is the disjoint union of two groupoid schemes as soon as the two maps on
object schemes and the two maps on arrow schemes are open immersions with complementary open
ranges.** Compatibility of the decomposition with source, target, identity and composition is
already carried by the two morphisms of groupoid schemes. -/
theorem isCoproductDecomposition_of_isCompl
    [IsOpenImmersion F₁.mapObjects.left] [IsOpenImmersion F₂.mapObjects.left]
    [IsOpenImmersion F₁.mapArrows.left] [IsOpenImmersion F₂.mapArrows.left]
    (hobjects : IsCompl F₁.mapObjects.left.opensRange F₂.mapObjects.left.opensRange)
    (harrows : IsCompl F₁.mapArrows.left.opensRange F₂.mapArrows.left.opensRange) :
    IsCoproductDecomposition F₁ F₂ where
  isIso_objects := isIso_coprod_desc_of_isCompl _ _ hobjects
  isIso_arrows := isIso_coprod_desc_of_isCompl _ _ harrows

end GroupoidScheme

end AlgebraicGeometry

end

end
