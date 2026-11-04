module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentPresheafTopologies

/-!
# The module `Mᵃ` exists on the slice of the small étale site at a chart, from Tag 03DT alone

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `X` be an
étale chart of `F` with underlying scheme `U`, and let `M` be a quasi-coherent `𝒪_U`-module.
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` is the module `Mᵃ` of Tag 03DU formed
on the slice `Over X`, read as a site of schemes over `U`; it takes as a hypothesis the sheaf
condition `hM` for the presheaf of pullback sections on that slice.

This file discharges that hypothesis from Tag 03DT, exactly as
`AlgebraicGeometry.BigEtaleOver.isSheaf_associatedPresheaf` and
`AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf` do for the two étale sites of a
*scheme*: the slice projection is continuous from the localized small étale topology of `F` to
the localized fpqc topology of the schemes over `U`, so an fpqc sheaf on the schemes over `U`
restricts to a sheaf on the slice.

Continuity of the slice projection was the one missing link.  It needs the projection to
preserve fibre products, and `CategoryTheory.Over.post` of a functor preserving fibre products
is not covered by Mathlib's instance for `CategoryTheory.Over.post`, which asks the functor to
preserve limits of shape `CategoryTheory.WithTerminal WalkingCospan`.  The route taken here is
the connected-limits one instead; see the implementation notes.

## Main results

* `CategoryTheory.Over.preservesLimitsOfShape_post_of_isConnected`: `CategoryTheory.Over.post`
  of a functor preserving connected limits of a given shape preserves them.
* `AlgebraicGeometry.Space.SmallEtale.instPreservesPullbacksSliceToOver`: the slice projection
  of the small étale site of `F` at a chart preserves fibre products.
* `AlgebraicGeometry.Space.SmallEtale.compatiblePreserving_sliceToOver`,
  `AlgebraicGeometry.Space.SmallEtale.coverPreserving_sliceToOver` and
  `AlgebraicGeometry.Space.SmallEtale.instIsContinuousSliceToOver`: the slice projection is
  compatible-preserving, cover preserving and continuous, from the localized small étale
  topology of `F` to the localized fpqc topology of the schemes over the chart's scheme.
* `AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf`: **Tag 03DT for the
  chart's scheme gives the hypothesis `hM` of
  `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`**, so `Mᵃ` exists on the slice with
  no input beyond Tag 03DT.

## Implementation notes

`CategoryTheory.Over.preservesLimitsOfShape_post_of_isConnected` is proved by reflection along
`CategoryTheory.Over.forget`, which *creates* connected limits
(`CategoryTheory.Over.createsLimitsOfShapeForgetOfIsConnected`) and therefore reflects them,
together with `CategoryTheory.Over.post_forget_eq_forget_comp`: the composite of
`CategoryTheory.Over.post G` with the forgetful functor of the target slice is *syntactically*
the forgetful functor of the source slice followed by `G`, so preservation of the composite is
an `inferInstanceAs`.  Mathlib's own instance in
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Over.lean` goes through
`CategoryTheory.WithTerminal` and asks for preservation of limits of shape
`CategoryTheory.WithTerminal J`, which is strictly more than is available here: the tree has
preservation of limits of shape `WalkingCospan` for
`AlgebraicGeometry.Space.SmallEtale.toOver` and for the projection to schemes, and not for the
`CategoryTheory.WithTerminal` form.

The general statement is a `theorem` and not an `instance`: it applies to every
`CategoryTheory.Over.post` and the repository already has Mathlib's instance for the
`CategoryTheory.WithTerminal` route, so only the one specialisation this file needs is
registered as an instance.  It is a candidate for Mathlib.

`AlgebraicGeometry.Space.SmallEtale.compatiblePreserving_sliceToOver` is stated at the universe
`u + 1` of the site objects, because that is the universe at which
`CategoryTheory.Functor.isContinuous_of_coverPreserving` consumes it; the lemma it comes from,
`Stacks.Sites.compatiblePreserving_of_preservesPullbacks`, is universe-polymorphic in that
parameter and the instantiation has to be written out.

Tag 03DT is taken in the spelling the tree already uses for it — the fpqc sheaf condition in
the underlying types for the presheaf of Tag 03DS, which is what
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'` proves — instantiated at the chart's
scheme rather than at `S`.  The conversion to the `AddCommGrpCat`-valued sheaf condition
that `Stacks.Sites.isSheaf_associatedPresheaf_of_isContinuous` wants is
`Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget`, which is already in the tree.

No `@[stacks]` attribute is claimed.  Tag 03DU is the object-level construction, already in the
tree; Tag 03DT is the input and is a hypothesis here; and Tag 03DX, of which this is one step,
is not proved.

## References

* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u v' u'

namespace CategoryTheory.Over

/-- **`CategoryTheory.Over.post` preserves connected limits that the functor preserves.**  For a
connected shape `J`, a functor `G : C ⥤ D` preserving limits of shape `J`, and an object `X` of
`C`, the induced functor `Over X ⥤ Over (G.obj X)` preserves limits of shape `J`.

The forgetful functor of a slice creates, hence reflects, connected limits, and the composite of
`CategoryTheory.Over.post G` with the forgetful functor of the target slice is the forgetful
functor of the source slice followed by `G`.  This is the connected-limits route; Mathlib's
instance for `CategoryTheory.Over.post` instead asks `G` to preserve limits of shape
`CategoryTheory.WithTerminal J`. -/
theorem preservesLimitsOfShape_post_of_isConnected {J : Type w} [Category.{w'} J]
    [IsConnected J] {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (G : C ⥤ D)
    (X : C) [PreservesLimitsOfShape J G] [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (Over.post G (X := X)) := by
  constructor
  intro K
  have h : PreservesLimit K (Over.post G (X := X) ⋙ Over.forget (G.obj X)) :=
    inferInstanceAs (PreservesLimit K (Over.forget X ⋙ G))
  exact Limits.preservesLimit_of_reflects_of_preserves _ (Over.forget (G.obj X))

end CategoryTheory.Over

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (X : SmallEtale B S hS F)

/-! ### Continuity of the slice projection -/

/-- The slice projection of the small étale site of `F` at the chart `X`, read as a category of
schemes over the chart's scheme, preserves fibre products.

This is `CategoryTheory.Over.preservesLimitsOfShape_post_of_isConnected` for the shape
`WalkingCospan`, which is connected, applied to the projection taking a chart to its underlying
scheme; that functor preserves fibre products by
`AlgebraicGeometry.Space.SmallEtale.instPreservesPullbacksToOver` and the corresponding
statement for `AlgebraicGeometry.BigFppfOver.toScheme`. -/
instance instPreservesPullbacksSliceToOver :
    PreservesLimitsOfShape WalkingCospan (sliceToOver B S hS F X) :=
  Over.preservesLimitsOfShape_post_of_isConnected _ _

/-- The slice projection is compatible-preserving for the localized fpqc topology of the schemes
over the chart's scheme: it preserves fibre products, so the lift of a cospan is its fibre
product. -/
theorem compatiblePreserving_sliceToOver : CompatiblePreserving.{u + 1}
    (Scheme.fpqcTopology.{u}.over (chartScheme X)) (sliceToOver B S hS F X) :=
  Stacks.Sites.compatiblePreserving_of_preservesPullbacks _ _

/-- The slice projection carries covering sieves of the localized small étale topology of `F` to
covering sieves of the localized fpqc topology of the schemes over the chart's scheme.

This is `CategoryTheory.CoverPreserving.overPost` applied to the unlocalized statement, which is
`AlgebraicGeometry.Space.SmallEtale.isContinuous_toScheme`. -/
theorem coverPreserving_sliceToOver :
    CoverPreserving ((topology B S hS F).over X)
      (Scheme.fpqcTopology.{u}.over (chartScheme X)) (sliceToOver B S hS F X) :=
  have : (toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).IsContinuous
      (topology B S hS F) Scheme.fpqcTopology.{u} := isContinuous_toScheme B S hS F
  CoverPreserving.overPost (F := toOver B S hS F ⋙ BigFppfOver.toScheme B S hS) X
    (CoverPreserving.of_isContinuous _ _ _)

/-- **The slice projection is continuous.**  An fpqc sheaf on the schemes over the chart's
scheme restricts along the slice projection to a sheaf for the localized small étale topology of
`F`.  This is the conjunction of
`AlgebraicGeometry.Space.SmallEtale.compatiblePreserving_sliceToOver` and
`AlgebraicGeometry.Space.SmallEtale.coverPreserving_sliceToOver`. -/
instance instIsContinuousSliceToOver : (sliceToOver B S hS F X).IsContinuous
    ((topology B S hS F).over X)
    (Scheme.fpqcTopology.{u}.over (chartScheme X)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_sliceToOver B S hS F X)
    (coverPreserving_sliceToOver B S hS F X)

/-! ### The sheaf condition for the associated presheaf on the slice -/

/-- **Tag 03DT for the chart's scheme gives the module sheaf condition on the slice.**  If the
presheaf of pullback sections of Tag 03DS of a quasi-coherent module `M` on the chart's scheme
is an fpqc sheaf on the schemes over that scheme — which is Tag 03DT — then its restriction
along the slice projection is a sheaf for the localized small étale topology of `F`.

This is exactly the hypothesis `hM` of
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`, so the module `Mᵃ` of Tag 03DU
exists on the slice at a chart with no input beyond Tag 03DT.  The hypothesis is the spelling of
Tag 03DT that the tree already carries as `h03DT`, instantiated at the chart's scheme. -/
theorem isSheaf_sliceAssociatedPresheaf (M : (chartScheme X).Modules)
    [M.IsQuasicoherent]
    (h03DT : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over (chartScheme X))
      (quasiCoherentPresheafFunctor (chartScheme X) M ⋙
        CategoryTheory.forget AddCommGrpCat)) :
    Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X)) :=
  Stacks.Sites.isSheaf_associatedPresheaf_of_isContinuous _ M _ _
    (Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _ h03DT)

end AlgebraicGeometry.Space.SmallEtale

end
