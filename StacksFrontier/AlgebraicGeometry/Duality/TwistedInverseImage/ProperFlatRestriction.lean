module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical

/-!
# The twisted inverse image of a flat proper morphism commutes with restriction to opens

Let `Y` be quasi-compact and quasi-separated, `f : X ⟶ Y` proper, flat and of finite presentation,
and `V ⊆ Y` a quasi-compact open with inverse image `U`. The canonical map `(j')^* ∘ a ⟶ a' ∘ j^*`
of [Stacks, Tag 0A9L] is invertible on `D^+_QCoh(𝒪_Y)` ([Stacks, Tag 0A9P] (1)).

## Main results

* `Stacks.Duality.isPerfect_derivedPushforward_of_isCompactObject_of_flat` — `Rf_*` of a compact
  object is perfect.
* `Stacks.Duality.isPseudoCoherent_derivedPushforward_of_isCompactObject_of_flat` — `Rf_*` of a
  compact object is pseudo-coherent.
* `Stacks.Duality.isIso_twistedInverseImageRestrictionMap_app_of_flat` — the map
  `(j')^* ∘ a ⟶ a' ∘ j^*` is invertible on `D^+_QCoh(𝒪_Y)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open OpenImmersion Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f] [AlgebraicGeometry.QuasiCompact j]

/-- **`Rf_*` of a compact object is perfect** for `f` proper, flat and of finite presentation
over a quasi-compact quasi-separated scheme. -/
theorem isPerfect_derivedPushforward_of_isCompactObject_of_flat
    (c : quasiCoherentDerivedCategory X) (hc : IsCompactObject.{u} c) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((derivedPushforward f).obj c.obj) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hP := (PerfectApproximation.isPerfect_standard_iff c.obj).2
    (isPerfect_of_isCompactObject c hc)
  have hrel := @Scheme.Hom.isPerfectRelativeTo_canonical_of_isPerfect X Y f _ _ c.obj hP
  exact (isPerfect_derivedPushforward_iff_standard f c.obj).1
    (isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat f c.obj hrel)

/-- **`Rf_*` of a compact object is pseudo-coherent** for `f` proper, flat and of finite
presentation over a quasi-compact quasi-separated scheme. -/
theorem isPseudoCoherent_derivedPushforward_of_isCompactObject_of_flat
    (c : quasiCoherentDerivedCategory X) (hc : IsCompactObject.{u} c) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) ((derivedPushforward f).obj c.obj) :=
  Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect _
    (isPerfect_derivedPushforward_of_isCompactObject_of_flat f c hc)

/-- Let `Y` be a quasi-compact and quasi-separated scheme, `f : X ⟶ Y` a proper, flat morphism of
finite presentation, and `j : V ⟶ Y` a quasi-compact open immersion with base change
`j' : U ⟶ X`. The map `(j')^* ∘ a ⟶ a' ∘ j^*` of [Stacks, Tag 0A9L] is invertible on
`D^+_QCoh(𝒪_Y)`. -/
@[stacks 0A9P "(1): f flat and of finite presentation"]
theorem isIso_twistedInverseImageRestrictionMap_app_of_flat (sq : IsPullback j' f' f j)
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
    haveI : CompactSpace U := compactSpace_of_isPullback sq
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    haveI : QuasiSeparatedSpace U := j'.isOpenEmbedding.quasiSeparatedSpace
    IsIso ((twistedInverseImageRestrictionMap j' f' f j
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
      (isQuasicoherent_homology_derivedRestrict j) (isQuasicoherent_homology_derivedRestrict j')
      sq).app K) :=
  isIso_twistedInverseImageRestrictionMap_app_of_isPseudoCoherent j' f' f j sq
    (isPseudoCoherent_derivedPushforward_of_isCompactObject_of_flat f) K hK

end Stacks.Duality
