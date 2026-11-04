module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFaithful

/-!
# Faithfulness of `(-)ᵃ` on the slice of a small étale site at an affine chart

The functor `M ↦ Mᵃ` of Tag 03DU appears in this tree on the slice of the small étale site of an
algebraic space `F` at a chart `X`, through
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`: the base is the scheme underlying
`X`, the site is `CategoryTheory.Over X`, and the projection to the schemes over the chart's
scheme is `AlgebraicGeometry.Space.SmallEtale.sliceToOver`.  This file instantiates
`Stacks.Sites.associatedModuleMap_injective` there.

The hypothesis of that result — one object of the site whose structure morphism to the base is
invertible — is met by the terminal object `CategoryTheory.Over.mk (𝟙 X)` of the slice, because
`sliceToOver` is `CategoryTheory.Over.post` of a functor and therefore sends the identity of `X`
to the identity of the chart's scheme.  The remaining hypothesis is that the chart's scheme be
affine, which is exactly the hypothesis under which the essential-surjectivity clause `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj`
is quantified.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.sliceToOver_obj_mk_id_hom`: the slice projection sends the
  terminal object of the slice at `X` to the identity of the chart's scheme.
* `AlgebraicGeometry.Space.SmallEtale.injective_associatedModuleMap_slice`: **the faithfulness
  half of Descent, Lemma 0GN7 on the slice at an affine chart.**  A morphism of quasi-coherent
  modules on the scheme underlying an affine chart is determined by the induced maps on the
  sections of the associated presheaves of modules on the slice.

## Implementation notes

The functor whose `CategoryTheory.Functor.map_id` is used has to be written out:
`sliceToOver` is an `abbrev` for `CategoryTheory.Over.post` of
`AlgebraicGeometry.Space.SmallEtale.toOver _ _ _ _ ⋙ AlgebraicGeometry.BigFppfOver.toScheme _ _ _`
and leaving that composite to unification leaves the functor argument of `map_id` a
metavariable, which does not get solved from the goal.

Fullness is not proved, here or in
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFaithful`; see the implementation notes
there for what it needs.  No `@[stacks]` attribute is claimed: Tag 0GN7 asserts full
faithfulness, over an arbitrary base scheme and for the five topologies of Tag 03DU.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (X : SmallEtale B S hS F)

/-- **The slice projection sends the terminal object of the slice to the identity.**  The object
`CategoryTheory.Over.mk (𝟙 X)` of the slice of the small étale site at `X` is read by
`AlgebraicGeometry.Space.SmallEtale.sliceToOver` as the scheme underlying `X`, over itself by the
identity morphism. -/
public theorem sliceToOver_obj_mk_id_hom :
    ((sliceToOver B S hS F X).obj (Over.mk (𝟙 X))).hom = 𝟙 (chartScheme X) :=
  CategoryTheory.Functor.map_id
    (_root_.AlgebraicGeometry.Space.SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS) X

/-- **The faithfulness half of Descent, Lemma 0GN7 on the slice at an affine chart.**  Let `X` be
an étale chart of an algebraic space whose underlying scheme is affine.  Then a morphism of
quasi-coherent modules on that scheme is determined by the maps it induces on the sections of the
associated presheaves of modules over the objects of the slice of the small étale site at `X`.

This is `Stacks.Sites.associatedModuleMap_injective` with the required object of the site taken
to be `CategoryTheory.Over.mk (𝟙 X)`, whose structure morphism is the identity by
`AlgebraicGeometry.Space.SmallEtale.sliceToOver_obj_mk_id_hom`. -/
public theorem injective_associatedModuleMap_slice [IsAffine (chartScheme X)]
    {M N : (chartScheme X).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Injective fun φ : M ⟶ N =>
      Stacks.Sites.associatedModuleMap (chartScheme X) (sliceToOver B S hS F X) φ :=
  have : CategoryTheory.IsIso ((sliceToOver B S hS F X).obj (Over.mk (𝟙 X))).hom :=
    sliceToOver_obj_mk_id_hom B S hS F X ▸ CategoryTheory.IsIso.id _
  Stacks.Sites.associatedModuleMap_injective (chartScheme X) (sliceToOver B S hS F X)
    (Over.mk (𝟙 X))

end AlgebraicGeometry.Space.SmallEtale

end
