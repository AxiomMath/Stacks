module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.TwistedStageSpaces

/-!
# The morphism of the sharpness counterexample

The two affine formal algebraic spaces of
`StacksFrontier.AlgebraicGeometry.FormalSpace.TwistedStageSpaces` are presented over the *same*
index, so the morphism between them of Stacks 0CBE — the second sense of the warning of
Stacks 0AN7 — is the colimit of a natural transformation of the two presentations rather than a
reindexing.

At a stage the morphism is the inclusion of a target stage ring into the source stage ring as
the ring component of the dual numbers, `TrivSqZeroExt.inlHom`. Its naturality is exactly
`Stacks.Coherent.dualMap_inl`: a transition of the source system carries the ring component to
the ring component, no twist entering there. That one lemma is the whole content of this file —
the twist obstructs McQuillan's criterion for the source, not the existence of the morphism.

## Main definitions

* `Stacks.Coherent.stageInclusion`: the morphism at a stage, in the big affine fppf category.
* `Stacks.Coherent.stageInclusionNatTrans`: the natural transformation of the two presentations.
* `Stacks.Coherent.sourceToTarget`: the morphism of affine formal algebraic spaces.

## Main results

* `Stacks.Coherent.colimitι_comp_sourceToTarget`: the morphism restricted to a stage of the
  source is the stage inclusion followed by the corresponding stage of the target, which is the
  form the cartesian stage squares need.

## Implementation notes

There is no `colimMap` for diagrams into `BigAffineFppf`, so the natural transformation is
whiskered into the sheaf category first, `Functor.whiskerRight`, and
`CategoryTheory.Limits.colimMap` is applied there; both spaces are *defined* as those colimits,
so the result has the right type on the nose. This is the same-index special case of the
`colimit.desc`-of-a-reindexed-cocone pattern of
`StacksFrontier/AlgebraicGeometry/FormalSpace/FormalSpectrum.lean`, which needs the extra
generality because its two diagrams are indexed by the weak ideals of two different rings.

The triangle making the stage inclusion a morphism *over the base* is definitional:
`Stacks.Coherent.dualLamProj` is by construction `TrivSqZeroExt.inlHom` composed with
`Stacks.Coherent.lamProj`, which is precisely what the triangle asserts after `Spec`.
-/

@[expose] public noncomputable section

namespace Stacks.Coherent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FormalSpace

universe u

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]
variable (B : BigFppfSite.{u}) (hcard : Cardinal.mk (Lam I) < B.cutoff)

/-- The ring map including a target stage ring into the source stage ring as the ring component
of the dual numbers. -/
abbrev stageInl (b : I) : StageRing b →+* DualStage b :=
  TrivSqZeroExt.inlHom (StageRing b) (StageRing b)

include hcard in
/-- The morphism of the counterexample at a stage: the inclusion of the target stage into the
source stage as the ring component of the dual numbers, as a morphism of affine schemes over the
base. The triangle over the base holds because `Stacks.Coherent.dualLamProj` is by construction
this inclusion composed with `Stacks.Coherent.lamProj`. -/
def stageInclusion (hcnt : ∀ a : I, (Set.Iio a).Countable) (b : I) :
    sourceBigAffineObject B hcard hcnt b ⟶ targetBigAffineObject B hcard b :=
  ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (stageInl b)))) (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (stageInl b)) ≫
          Spec.map (CommRingCat.ofHom (lamProj b))
        = Spec.map (CommRingCat.ofHom (dualLamProj b))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl))

include hcard in
/-- The natural transformation of the two presentations whose colimit is the morphism of the
counterexample. Naturality is `Stacks.Coherent.dualMap_inl`. -/
def stageInclusionNatTrans (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    sourceBigAffineDiagram B hcard hcnt ⟶ targetBigAffineDiagram B hcard where
  app s := stageInclusion B hcard hcnt s.down
  naturality {s t} f := by
    have h : s ≤ t := leOfHom f
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (dualMap hcnt (show s.down ≤ t.down from h))) ≫
        Spec.map (CommRingCat.ofHom (stageInl t.down))
      = Spec.map (CommRingCat.ofHom (stageInl s.down)) ≫
        Spec.map (CommRingCat.ofHom (stageRingMap (show s.down ≤ t.down from h)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (RingHom.ext fun x ↦
      dualMap_inl hcnt (show s.down ≤ t.down from h) x)

include hcard in
/-- **The morphism of the counterexample**, as a morphism of affine formal algebraic spaces: the
colimit of the stage inclusions. -/
def sourceToTarget (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    sourceSpace B hcard hcnt ⟶ targetSpace B hcard :=
  colimMap (Functor.whiskerRight (stageInclusionNatTrans B hcard hcnt)
    (BigAffineFppf.inclusion B (baseScheme I) (contains_baseScheme B hcard) ⋙
      Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B (baseScheme I) (contains_baseScheme B hcard))))

include hcard in
/-- The morphism restricted to a stage of the source is the stage inclusion followed by the
corresponding stage of the target. This is the form the cartesian stage squares need. -/
theorem colimitι_comp_sourceToTarget (hcnt : ∀ a : I, (Set.Iio a).Countable) (s : Index I) :
    colimit.ι (sourceBigAffineDiagram B hcard hcnt ⋙
        BigAffineFppf.inclusion B (baseScheme I) (contains_baseScheme B hcard) ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B (baseScheme I) (contains_baseScheme B hcard))) s ≫
      sourceToTarget B hcard hcnt
    = (BigAffineFppf.inclusion B (baseScheme I) (contains_baseScheme B hcard) ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B (baseScheme I) (contains_baseScheme B hcard))).map
          ((stageInclusionNatTrans B hcard hcnt).app s) ≫
      colimit.ι (targetBigAffineDiagram B hcard ⋙
        BigAffineFppf.inclusion B (baseScheme I) (contains_baseScheme B hcard) ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B (baseScheme I) (contains_baseScheme B hcard))) s :=
  ι_colimMap _ s

end Stacks.Coherent

end
