module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.CategoryTheory.Sites.Representable.MapsFromRepresentable
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact

/-!
# Stability properties of thickenings of schemes

Thickenings of schemes are stable under base change, are the intersection of the closed
immersions with the surjective morphisms, and are local at the target for the fpqc
precoverage.  These are the inputs the stage-map statements for an affine formal algebraic
space need.

## Main results

* `AlgebraicGeometry.FormalSpace.isThickening_isStableUnderBaseChange`,
  `AlgebraicGeometry.FormalSpace.isThickening_eq_inf` and
  `AlgebraicGeometry.FormalSpace.isThickening_isLocalAtTarget_fpqc`.

That each stage of a directed presentation of an affine formal algebraic space maps
representably to the colimit, and that the stage map is a thickening after every represented
base change, are `AlgebraicGeometry.FormalSpace.relativelyRepresentable_colimitι` and
`AlgebraicGeometry.FormalSpace.isThickening_colimitι`, proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage` and re-exported here.

## Implementation notes

The presentation is made explicit rather than extracted from the existential
predicate for affine formal algebraic spaces. The isomorphism to `X` records the
chosen identification with the colimit. The second result uses the relative
morphism property along sheafified Yoneda; this property includes
representability, while the first result records that assertion separately. The
set-theoretic condition on the colimit is not needed for either assertion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v u w w₁ w₂

namespace AlgebraicGeometry.FormalSpace

/-- Thickenings of schemes are stable under arbitrary base change: a thickening is a
surjective closed immersion, and both halves are stable under base change. -/
theorem isThickening_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) := by
  refine ⟨fun sq hg ↦ ⟨IsClosedImmersion.isStableUnderBaseChange.of_isPullback sq hg.1, ?_⟩⟩
  exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Surjective.{u}) sq ⟨hg.2⟩).surj

/-- Being a thickening is a conjunction of two morphism properties. -/
theorem isThickening_eq_inf :
    (show MorphismProperty Scheme.{u} from @Stacks.Thickenings.IsThickening) =
      (show MorphismProperty Scheme.{u} from @IsClosedImmersion) ⊓ @Surjective := by
  ext X Y f
  exact ⟨fun h ↦ ⟨h.1, ⟨h.2⟩⟩, fun h ↦ ⟨h.1, h.2.surj⟩⟩

/-- Being a thickening is fpqc local on the target, since being a closed immersion and
being surjective both are. -/
theorem isThickening_isLocalAtTarget_fpqc :
    (show MorphismProperty Scheme.{u} from
        @Stacks.Thickenings.IsThickening).IsLocalAtTarget Scheme.fpqcPrecoverage := by
  rw [isThickening_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

private instance thickening_respectsIso :
    MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    have : IsClosedImmersion f := hf.1
    have : Surjective f := ⟨hf.2⟩
    exact ⟨inferInstance, (inferInstance : Surjective (e.hom ≫ f)).surj⟩
  · intro X Y Z e f hf
    have : IsClosedImmersion f := hf.1
    have : Surjective f := ⟨hf.2⟩
    exact ⟨inferInstance, (inferInstance : Surjective (f ≫ e.hom)).surj⟩

end AlgebraicGeometry.FormalSpace

end
