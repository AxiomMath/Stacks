module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# The schematic locus under preimage along an affine morphism

The schematic locus of an algebraic space (Stacks 03JH) is the largest open subspace which is
a scheme. This file shows that it is monotone under preimage along an affine morphism: the
preimage of the schematic locus of the target is contained in the schematic locus of the
source.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isAffineHom`: an algebraic space affine over a
  scheme is a scheme.
* `AlgebraicGeometry.Space.preimage_schematicLocus_le`: the preimage of the schematic locus
  along an affine morphism of algebraic spaces lies in the schematic locus.

## Implementation notes

Neither statement carries a cardinality hypothesis, and this is the point of the file. In a
limit situation (Stacks 084R) the schematic loci of the stages form a monotone system of open
subspaces by the second result, and that monotonicity is what lets "some stage is a scheme" be
reduced to "the schematic locus of some stage is everything". The reduction is needed for
Stacks 07SR, whose consumers include Zorn chains of closed subspaces whose index set admits no
cardinality bound at all, so a size-bounded form of either statement would be useless there.

Being cardinality-free here does not make that form of Stacks 07SR available: at the time of
writing the obstruction to it is a cardinality-free **Stacks 07SQ for closed-immersion
transitions**, and nothing else. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PointsOfClosedSubspaceInfimum.lean` for why neither the
closed-subspace analogue of Stacks 086V nor Stacks 0827 is in the way.

*The first result.* By Stacks 03WG an affine morphism of algebraic spaces is representable and
representably affine (`AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`, items (1)
and (2)). The base change of `f : F ⟶ G` along the isomorphism `yoneda G.reprX ≅ G` presenting
the target is therefore represented by a scheme, and the projection of that base change to `F`
is an isomorphism because its other leg is, so `F` is representable.

*The second result.* `AlgebraicGeometry.Space.le_schematicLocus` reduces the containment to
showing that `(schematicLocus G).preimage f` is an open subspace of `F` which is a scheme. It
is an open subspace by `AlgebraicGeometry.Space.isOpenSubspace_preimage`, open immersions being
stable under base change, and it is a scheme by the first result applied to its projection
`Subfunctor.fromPreimage f` onto `schematicLocus G`: that projection is the base change of `f`
along `(schematicLocus G).ι` (`CategoryTheory.Subfunctor.isPullback_preimage`), hence affine,
and `schematicLocus G` is a scheme by the unconditional form of Stacks 03JH,
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An algebraic space which is affine over a scheme is a scheme.

By Stacks 03WG an affine morphism of algebraic spaces is representable, so its base change
along the presentation `yoneda G.reprX ≅ G` of the target is represented by a scheme; that
base change has an isomorphism as one leg, hence as the other. -/
theorem isRepresentable_of_isAffineHom (f : F ⟶ G) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hf : IsAffineHom B S hS f) [G.IsRepresentable] :
    F.IsRepresentable := by
  have hconj := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS f hF hG).out 2 1).mp hf
  have hr : yoneda.relativelyRepresentable f := hconj.1
  have hp := hr.isPullback G.reprW.hom
  have : IsIso (hr.fst G.reprW.hom) := hp.isIso_fst_of_isIso
  exact Functor.IsRepresentable.mk' (asIso (hr.fst G.reprW.hom))

/-- **The schematic locus is monotone under preimage along an affine morphism.** The preimage
of the schematic locus of the target of an affine morphism of algebraic spaces is contained in
the schematic locus of the source.

No cardinality hypothesis is needed.

This is not part of the statement of Stacks 03JH, which asserts only that the schematic locus
is an open subspace and is a scheme, so it carries no tag. -/
theorem preimage_schematicLocus_le (f : F ⟶ G) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hf : IsAffineHom B S hS f) :
    (schematicLocus B S hS G).preimage f ≤ schematicLocus B S hS F := by
  obtain ⟨hUopen, hUrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hG
  have hV : IsOpenSubspace B S hS ((schematicLocus B S hS G).preimage f) :=
    isOpenSubspace_preimage B S hS f (schematicLocus B S hS G) hG hF hUopen
  have : (schematicLocus B S hS G).toFunctor.IsRepresentable := hUrep
  refine le_schematicLocus B S hS F ((schematicLocus B S hS G).preimage f) hV ?_
  exact isRepresentable_of_isAffineHom B S hS
    ((schematicLocus B S hS G).fromPreimage f) hV.1 hUopen.1
    (isAffineHom_of_isPullback' B S hS
      (Subfunctor.isPullback_preimage f (schematicLocus B S hS G)).flip hf)

end AlgebraicGeometry.Space

end
