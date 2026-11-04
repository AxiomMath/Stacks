module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SharpCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InverseImageChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt

/-!
# The comorphism read through a thickening, on an étale chart

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
and let `c : X ⟶ W` be a morphism.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceCommonTarget.lean` reads the
comorphism of `c` as a morphism of sheaves of rings

`𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)`

whose target depends on `c` only through `i ≫ c`, which is what makes it a common target for the
comorphisms of two morphisms agreeing on the thickening.  That target is not the ordinary direct
image `c_*𝒪_X`, and the development's chart-level reading of sections —
`AlgebraicGeometry.Space.directImageChartProjection`, whose value at `c^♯(b)` is the pullback of
the regular function `b` along the vertical scheme morphism of a diagram of étale charts — is
stated for the ordinary direct image.

This file supplies the missing comparison.  The comorphism read through the thickening is the
ordinary comorphism followed by two factors,

`𝒪_W --c^♯--> c_*𝒪_X --c_*η--> c_*(i_*i^{-1}𝒪_X) --≅--> (i ≫ c)_*(i^{-1}𝒪_X)`,

and **both factors are invertible**: the second is the comparison of iterated direct images,
whose inverse `AlgebraicGeometry.Space.pushforwardRingSheafCompInv` is proved with both
round-trip equations, and the first is the direct image of the unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X`,
which is an isomorphism because `Z ⊂ X` is a thickening
(`AlgebraicGeometry.Space.isIso_thickeningRingUnit`).  So the two readings determine one another,
and the chart projection transports across them.

## Main definitions

* `AlgebraicGeometry.Space.thickeningRingUnitIso`: the unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` of a
  thickening, bundled as an isomorphism.
* `AlgebraicGeometry.Space.thickeningLiftComparison`: the comparison
  `c_*𝒪_X ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` of the two targets, and
  `AlgebraicGeometry.Space.thickeningLiftComparisonInv` its inverse for a thickening.

## Main results

* `AlgebraicGeometry.Space.structureSharpThroughThickening_eq_comp`: the comorphism read through
  the thickening is the ordinary comorphism followed by the comparison.
* `AlgebraicGeometry.Space.thickeningLiftComparison_comp_inv` and
  `AlgebraicGeometry.Space.thickeningLiftComparisonInv_comp_hom`: **the comparison of the two
  targets is invertible for a thickening.**
* `AlgebraicGeometry.Space.structureSharpThroughThickening_comp_comparisonInv`: the ordinary
  comorphism is recovered from the comorphism read through the thickening.
* `AlgebraicGeometry.Space.structureSharpThroughThickening_comp_pushforwardRingSheafCompInv`:
  **the comorphism read through the thickening, transported back across the comparison of
  iterated direct images alone**, which needs no hypothesis on `Z`.
* `AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening`: **the
  chart projection of the comorphism read through the thickening is the unit at the chartwise
  pullback of the regular function.**
* `AlgebraicGeometry.Space.chartDiagramPullback_eq_of_directImageChartProjection`: the same read
  as a determination of the chartwise pullback, the unit being injective on the sections over an
  étale chart of a thickening.
* `AlgebraicGeometry.Space.eq_structureSharpThroughThickening_of_directImageChartProjection`:
  **the comorphism read through the thickening is the only morphism `𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)`
  with those chart projections.**  With the computation above this is a complete chart-level
  description of it, in both directions.

## Implementation notes

**The invertibility of the unit is passed as an explicit argument at every call.**  As the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalModuleInverseImageKernel.lean` record,
instance resolution for `CategoryTheory.IsIso` at a morphism of sheaves of rings on the small
étale site does not terminate; here it does not even find the invertibility of the unit
when that is placed in the local context by `letI` or `haveI`.  So
`AlgebraicGeometry.Space.thickeningRingUnitIso` is built by `CategoryTheory.asIso` with the
instance supplied positionally, and the direct image of the unit is handled as
`CategoryTheory.Functor.mapIso` of that isomorphism, whose `hom` is the direct image of the unit
by `rfl`.

**The two reassociations are proved at an abstract category**, where the terms are small; this is
the precaution the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` describe for the
same composites.  In particular `rw [Category.assoc]` on the geometric terms is a deterministic
`whnf` timeout here.

**Why there is no statement that two morphisms with equal comorphisms read through the thickening
have equal comorphisms.**  It is not type-correct: `structureSharp c` and `structureSharp c'` have
`c_*𝒪_X` and `c'_*𝒪_X` for their targets, and these differ.  That is exactly why the development
indexes the common target by a morphism `e` out of the thickening, and why the cancellation is
stated above as the composite with the inverse rather than as an implication between equations.

**No `@[stacks]` attribute is placed.**  What is proved here is a comparison of two readings of
[Stacks Project, Tag 03G8] internal to this development, not a statement of the Stacks project.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), iterated
  direct images.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this comparison
  is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

/-- Cancelling the right factor of a three-fold composite against a right inverse. -/
private theorem comp_comp_cancel {Cc : Type*} [Category Cc] {A Bb D E : Cc} (a : A ⟶ Bb)
    (b : Bb ⟶ D) (k : D ⟶ E) (k' : E ⟶ D) (hk : k ≫ k' = 𝟙 D) :
    (a ≫ b ≫ k) ≫ k' = a ≫ b :=
  calc (a ≫ b ≫ k) ≫ k' = a ≫ b ≫ k ≫ k' := by simp only [Category.assoc]
    _ = a ≫ b := by rw [hk, Category.comp_id]

/-- The composite of two composites of mutually inverse pairs is the identity. -/
private theorem comp_pair_cancel {Cc : Type*} [Category Cc] {A Bb D : Cc} (a : A ⟶ Bb)
    (b : Bb ⟶ D) (b' : D ⟶ Bb) (a' : Bb ⟶ A) (hb : b ≫ b' = 𝟙 Bb) (ha : a ≫ a' = 𝟙 A) :
    (a ≫ b) ≫ b' ≫ a' = 𝟙 A := by
  rw [Category.assoc, ← Category.assoc b, hb, Category.id_comp, ha]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The comparison of the two targets -/

/-- **The unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` of a thickening, as an isomorphism.**  It is invertible
by `AlgebraicGeometry.Space.isIso_thickeningRingUnit`, which is the equivalence of the two small
étale topoi of a thickening read at the structure sheaf. -/
noncomputable def thickeningRingUnitIso (hZ : IsThickening B S hS X Z.1) :
    structureRingSheaf B S hS X ≅
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z))).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  @asIso _ _ _ _ (thickeningRingUnit B S hS Z) (isIso_thickeningRingUnit B S hS Z hZ)

/-- `AlgebraicGeometry.Space.thickeningRingUnitIso` is the unit. -/
theorem thickeningRingUnitIso_hom (hZ : IsThickening B S hS X Z.1) :
    (thickeningRingUnitIso B S hS Z hZ).hom = thickeningRingUnit B S hS Z := rfl

/-- **The comparison `c_*𝒪_X ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` of the target of the ordinary comorphism
with the target of the comorphism read through the thickening:** the direct image of the unit
`η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` of `i^{-1} ⊣ i_*` followed by the comparison of iterated direct
images. -/
noncomputable def thickeningLiftComparison (c : X ⟶ W) :
    structureRingSheafDirectImage B S hS c ⟶ thickeningLiftRingSheaf B S hS Z c :=
  (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
      (thickeningRingUnit B S hS Z) ≫
    pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- **The comorphism of `c` read through the thickening is the ordinary comorphism followed by
the comparison of the two targets.**  This is the definition of
`AlgebraicGeometry.Space.structureSharpThroughThickening` with its last two factors packaged as
the comparison of iterated direct images. -/
theorem structureSharpThroughThickening_eq_comp (c : X ⟶ W) :
    structureSharpThroughThickening B S hS Z c =
      structureSharp B S hS c ≫ thickeningLiftComparison B S hS Z c := rfl

/-- **The inverse of the comparison of the two targets, for a thickening:** the comparison of
iterated direct images in the other direction, followed by the inverse of the direct image of the
unit. -/
noncomputable def thickeningLiftComparisonInv (c : X ⟶ W) (hZ : IsThickening B S hS X Z.1) :
    thickeningLiftRingSheaf B S hS Z c ⟶ structureRingSheafDirectImage B S hS c :=
  pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) ≫
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).mapIso
      (thickeningRingUnitIso B S hS Z hZ)).inv

/-- **The comparison of the two targets is invertible for a thickening**, first round trip. -/
theorem thickeningLiftComparison_comp_inv (c : X ⟶ W) (hZ : IsThickening B S hS X Z.1) :
    thickeningLiftComparison B S hS Z c ≫ thickeningLiftComparisonInv B S hS Z c hZ = 𝟙 _ :=
  comp_pair_cancel _ _ _ _
    (pushforwardRingSheafCompHom_comp_inv B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).mapIso
      (thickeningRingUnitIso B S hS Z hZ)).hom_inv_id)

/-- **The comparison of the two targets is invertible for a thickening**, second round trip. -/
theorem thickeningLiftComparisonInv_comp_hom (c : X ⟶ W) (hZ : IsThickening B S hS X Z.1) :
    thickeningLiftComparisonInv B S hS Z c hZ ≫ thickeningLiftComparison B S hS Z c = 𝟙 _ :=
  comp_pair_cancel _ _ _ _
    (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).mapIso
      (thickeningRingUnitIso B S hS Z hZ)).inv_hom_id)
    (pushforwardRingSheafCompInv_comp_hom B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))

/-- **The ordinary comorphism of `c`, recovered from the comorphism read through the
thickening.**  So no information is lost in reading the comorphism in the common target of the
morphisms agreeing on the thickening. -/
theorem structureSharpThroughThickening_comp_comparisonInv (c : X ⟶ W)
    (hZ : IsThickening B S hS X Z.1) :
    structureSharpThroughThickening B S hS Z c ≫ thickeningLiftComparisonInv B S hS Z c hZ =
      structureSharp B S hS c :=
  comp_cancel_right (structureSharp B S hS c) (thickeningLiftComparison B S hS Z c)
    (thickeningLiftComparisonInv B S hS Z c hZ)
    (thickeningLiftComparison_comp_inv B S hS Z c hZ)

/-! ### The transport of the chart projection -/

/-- **The comorphism read through the thickening, transported back across the comparison of
iterated direct images**, is the ordinary comorphism followed by the direct image of the unit.
This is the half of the comparison which needs no hypothesis on `Z`: the comparison of iterated
direct images is invertible for any closed subspace. -/
theorem structureSharpThroughThickening_comp_pushforwardRingSheafCompInv (c : X ⟶ W) :
    structureSharpThroughThickening B S hS Z c ≫
        pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharp B S hS c ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
          (thickeningRingUnit B S hS Z) :=
  comp_comp_cancel _ _ _ _
    (pushforwardRingSheafCompHom_comp_inv B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))

/-- **The comorphism read through the thickening, transported back across the comparison of
iterated direct images, read on a section.**  Both readings of the chart projection below are
this equation followed by the chart-level computation of the ordinary comorphism. -/
theorem app_pushforwardRingSheafCompInv_structureSharpThroughThickening (c : X ⟶ W)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj V)) :
    (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
          (structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z))).hom.app V
        ((structureSharpThroughThickening B S hS Z c).hom.app V b) =
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
          (thickeningRingUnit B S hS Z)).hom.app V
        ((structureSharp B S hS c).hom.app V b) := by
  show (structureSharpThroughThickening B S hS Z c ≫
      pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V b =
    (structureSharp B S hS c ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
        (thickeningRingUnit B S hS Z)).hom.app V b
  exact ringSheafHom_congr_app_apply
    (structureSharpThroughThickening_comp_pushforwardRingSheafCompInv B S hS Z c) V b

/-- **The chart projection of the comorphism read through the thickening is the unit at the
chartwise pullback of the regular function.**

For a commutative diagram `d` of étale scheme charts over `c : X ⟶ W` and a regular function `b`
on the chart `d.V` of `W`, the value of the comorphism read through the thickening at `b`,
transported back across the comparison of iterated direct images and projected to the chart `d.U`
of `X`, is the image under the unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` of the pullback of `b` along the
vertical scheme morphism `d.g`.

So, through the identification of the sections of `i_*i^{-1}𝒪_X` over `d.U` with the regular
functions `Γ(d.U, ⊤)` — which is `AlgebraicGeometry.Space.bijective_thickeningRingUnit_app` for a
thickening — the chart projection of the comorphism read through the thickening is pullback of
regular functions along `d.g`, exactly as the chart projection of the ordinary comorphism is by
`AlgebraicGeometry.Space.directImageChartProjection_structureSharpSet_chartDiagram`. -/
theorem directImageChartProjection_structureSharpThroughThickening (c : X ⟶ W)
    (d : ChartDiagram B S hS X.1 W.1 c.hom)
    (b : (structureSetSheaf B S hS W).obj.obj (op d.V)) :
    (directImageChartProjection B S hS c d.V
          (StructuredArrow.mk (Y := op d.U)
            (baseChangeArrowOfChartDiagram B S hS c d).op)).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj
          ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).obj
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
        ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).hom.app (op d.V)
          ((structureSharpThroughThickening B S hS Z c).hom.app (op d.V) b)) =
      (thickeningRingUnit B S hS Z).hom.app (op d.U)
        ((chartDiagramPullback B S hS c d).hom b) := by
  rw [app_pushforwardRingSheafCompInv_structureSharpThroughThickening B S hS Z c (op d.V) b]
  exact (app_chartDiagramPullback_eq_directImageChartProjection B S hS c d
    (thickeningRingUnit B S hS Z) b).symm

/-- **The chart projection of the comorphism read through the thickening determines the chartwise
pullback of the regular function.**  A regular function on the chart `d.U` of `X` whose image
under the unit is that chart projection is the pullback of `b` along the vertical scheme morphism
of the diagram: the unit is injective on the sections over every étale chart of a thickening, by
`AlgebraicGeometry.Space.bijective_thickeningRingUnit_app`. -/
theorem chartDiagramPullback_eq_of_directImageChartProjection (c : X ⟶ W)
    (hZ : IsThickening B S hS X Z.1) (d : ChartDiagram B S hS X.1 W.1 c.hom)
    (b : (structureSetSheaf B S hS W).obj.obj (op d.V))
    (x : ToType ((structureRingSheaf B S hS X).obj.obj (op d.U)))
    (hx : (thickeningRingUnit B S hS Z).hom.app (op d.U) x =
      (directImageChartProjection B S hS c d.V
            (StructuredArrow.mk (Y := op d.U)
              (baseChangeArrowOfChartDiagram B S hS c d).op)).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj
            ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
              (subspaceInclusion B S hS X Z))).obj
              (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
          ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
              (structureRingSheafInverseImage B S hS
                (subspaceInclusion B S hS X Z))).hom.app (op d.V)
            ((structureSharpThroughThickening B S hS Z c).hom.app (op d.V) b))) :
    x = (chartDiagramPullback B S hS c d).hom b :=
  (bijective_thickeningRingUnit_app B S hS Z hZ (op d.U)).1
    (hx.trans (directImageChartProjection_structureSharpThroughThickening B S hS Z c d b))

/-! ### The chart projections determine the comorphism -/

/-- **The chart projection of the comorphism read through the thickening, at an arbitrary index
of the limit of chart sections**, rather than at one coming from a diagram of étale scheme
charts: it is the unit at the chartwise pullback of the regular function.  This is the form in
which the joint injectivity of the chart projections consumes the computation. -/
theorem directImageChartProjection_structureSharpThroughThickening_chartPullback (c : X ⟶ W)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : (structureSetSheaf B S hS W).obj.obj (op V)) :
    (directImageChartProjection B S hS c V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj
          ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).obj
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
        ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).hom.app (op V)
          ((structureSharpThroughThickening B S hS Z c).hom.app (op V) b)) =
      (thickeningRingUnit B S hS Z).hom.app j.right (chartPullback B S hS c V j b) := by
  rw [app_pushforwardRingSheafCompInv_structureSharpThroughThickening B S hS Z c (op V) b]
  exact (app_chartPullback_eq_directImageChartProjection B S hS c V j
    (thickeningRingUnit B S hS Z) b).symm

/-- **The comorphism read through the thickening is the only morphism
`𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` with those chart projections.**

A morphism of sheaves of rings into a direct image is determined by its chart projections, by
`AlgebraicGeometry.Space.directImageChartProjection_ringSheafHom_ext`; the transport across the
comparison of iterated direct images is invertible, so no information is lost in reading the
chart projections there.

Together with
`AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening_chartPullback`
this describes the comorphism read through the thickening completely at the level of étale scheme
charts: it is the unique morphism whose chart projections are the unit at pullback of regular
functions. -/
theorem eq_structureSharpThroughThickening_of_directImageChartProjection (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (h : ∀ (V : SmallEtale B S hS W.1)
        (j : StructuredArrow (op (chartBaseChange B S hS c V))
          (comparisonFunctor B S hS X).op)
        (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))),
      (directImageChartProjection B S hS c V j).app
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj
            ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
              (subspaceInclusion B S hS X Z))).obj
              (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
          ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
              (structureRingSheafInverseImage B S hS
                (subspaceInclusion B S hS X Z))).hom.app (op V) (a.hom.app (op V) b)) =
        (thickeningRingUnit B S hS Z).hom.app j.right (chartPullback B S hS c V j b)) :
    a = structureSharpThroughThickening B S hS Z c :=
  cancel_right_of_comp_id a (structureSharpThroughThickening B S hS Z c)
    (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (pushforwardRingSheafCompInv_comp_hom B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (directImageChartProjection_ringSheafHom_ext B S hS c _ _ fun V j x =>
      (h V j x).trans
        (directImageChartProjection_structureSharpThroughThickening_chartPullback
          B S hS Z c V j x).symm)

end AlgebraicGeometry.Space

end
