module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.AmpleFamilyRelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.Approximation.Basic
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.CompletelyDecomposed
public import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up and ample families of invertible modules: the reduction to finite type over `ℤ`

A quasi-compact quasi-separated scheme `X` receives a morphism `f : Y ⟶ X` which is of finite
presentation, proper and completely decomposed and whose source carries an ample family of
invertible modules; this is [Stacks, Tag 0GTU], stated and proved in
`StacksFrontier/AlgebraicGeometry/BlowupAmpleFamily/Noetherian.lean`. This file proves the first
paragraph of the source's proof: the reduction of the statement to a base of finite type over
`ℤ`.

## Main results

* `Stacks.BlowupAmpleFamily.exists_isAmpleFamily_of_isAffineHom`: the source of an affine
  morphism inherits an ample family of invertible modules from its target. This is the affine
  case of [Stacks, Tag 0GTQ].
* `Stacks.BlowupAmpleFamily.exists_isAffineHom_finiteType_target`: a quasi-compact
  quasi-separated scheme admits an affine morphism to a scheme of finite type over `ℤ`. This is
  the consequence of [Stacks, Tag 01ZA] that the source's proof opens with.
* `exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_finiteTypeCase`: the
  conclusion of Tag 0GTU for `X`, from the same conclusion for every scheme of finite type
  over `ℤ`.

## The argument

The source's proof has two paragraphs. The first reduces the statement to a base of finite type
over `ℤ`, and that reduction is what is proved here.

Absolute Noetherian approximation ([Stacks, Tag 01ZA],
`AlgebraicGeometry.LimitFPObjectDescent.finiteTypeSchemeApproximation`) writes `X` as the limit
of an inverse system with affine transition morphisms whose stages are of finite type over `ℤ`.
Every projection out of such a limit is affine ([Stacks, Tag 01YX] part (1),
`AlgebraicGeometry.EventualLimit.isAffineHom_π_app`), so any one stage `X₀` is the target of an
affine morphism `g : X ⟶ X₀`; this is `exists_isAffineHom_finiteType_target`.

Given `f₀ : Y₀ ⟶ X₀` with the four desired properties, set `Y = X ×_{X₀} Y₀` and let `f` be the
projection `pullback.snd f₀ g : Y ⟶ X`. Then

* `f` is of finite presentation, because local finite presentation, quasi-compactness and
  quasi-separatedness of a morphism are each stable under base change
  ([Stacks, Tag 01TS], `AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange`
  and the corresponding Mathlib instances for the other two);
* `f` is proper, by [Stacks, Tag 01W4],
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`;
* `f` is completely decomposed, by [Stacks, Tag 0GTK],
  `AlgebraicGeometry.isCompletelyDecomposed_pullback`;
* `Y` has an ample family of invertible modules, because `pullback.fst f₀ g : Y ⟶ Y₀` is the base
  change of the affine morphism `g` and so is affine, and an ample family transfers along an
  affine morphism.

## Implementation notes

**The finite-type case is an argument, not an assumption of Tag 0GTU.** The reduction is stated
for an arbitrary proof `hFiniteTypeCase` of the conclusion over every scheme of finite type over
`ℤ`; that case is the source's second paragraph and is proved in
`StacksFrontier/AlgebraicGeometry/BlowupAmpleFamily/Noetherian.lean`, which feeds it to the
reduction. Finite type over `ℤ` is spelled, as in
`AlgebraicGeometry.LimitFPObjectDescent.FiniteTypeSchemeApproximation`, by
`LocallyOfFiniteType (terminal.from X₀)` together with `QuasiCompact (terminal.from X₀)`; those
are exactly the two fields of that structure, so the reduction applies to a stage of the
approximation without further work.

**The hypotheses on `X`.** An ample family of invertible modules forces its
scheme to be quasi-compact (clause (1) of [Stacks, Tag 0FXR]), and a completely decomposed
morphism is surjective, so the conclusion already implies that `X` is quasi-compact.

**The affine case of Tag 0GTQ is proved rather than assumed.** `𝒪_X` is ample relative to a
quasi-affine morphism ([Stacks, Tag 0891],
`Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule`), an affine
morphism is quasi-affine (`Stacks.QuasiAffineSource.isQuasiAffineHom_of_isAffineHom`), and
[Stacks, Tag 0GTP], `Stacks.AmpleFamilyRelativeAmple.exists_isAmpleFamily`, turns an ample
family on the target together with a relatively ample invertible module into an ample family on
the source. Tag 0GTQ itself asserts the conclusion for a quasi-affine morphism, which is
strictly more general than the affine case `exists_isAmpleFamily_of_isAffineHom` needed here.

**Finite presentation of a morphism** is `AlgebraicGeometry.FinitePresentation` of
`StacksFrontier/AlgebraicGeometry/Morphisms/FinitePresentationPoint.lean`, the conjunction of
`AlgebraicGeometry.LocallyOfFinitePresentation` with quasi-compactness and quasi-separatedness
of the morphism.

## References

* [Stacks Project, Tag 0GTU](https://stacks.math.columbia.edu/tag/0GTU)
* [Stacks Project, Tag 0GTT](https://stacks.math.columbia.edu/tag/0GTT)
* [Stacks Project, Tag 0GTQ](https://stacks.math.columbia.edu/tag/0GTQ)
* [Stacks Project, Tag 0GTP](https://stacks.math.columbia.edu/tag/0GTP)
* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Tag 0GTK](https://stacks.math.columbia.edu/tag/0GTK)
* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
* [Stacks Project, Tag 01TS](https://stacks.math.columbia.edu/tag/01TS)
* [Stacks Project, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.BlowupAmpleFamily

/-- **The affine case of [Stacks, Tag 0GTQ].** If the target of an affine morphism of schemes
has an ample family of invertible modules, then so does its source.

The structure sheaf of the source is ample relative to the morphism, an affine morphism being
quasi-affine, so this is the case `L = 𝒪_X` of [Stacks, Tag 0GTP]. -/
theorem exists_isAmpleFamily_of_isAffineHom {A B : Scheme.{u}} (g : A ⟶ B) [IsAffineHom g]
    {I : Type v} (N : I → B.Modules) (hN : B.IsAmpleFamily N) :
    ∃ (J : Type v) (M : J → A.Modules), A.IsAmpleFamily M :=
  Stacks.AmpleFamilyRelativeAmple.exists_isAmpleFamily g N hN
    ⟨Stacks.Ample.unitModule A, Stacks.Ample.isInvertibleModule_unit A,
      Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule g
        (Stacks.Ample.unitModule A) (Iso.refl _)⟩

/-- **A quasi-compact quasi-separated scheme is affine over a scheme of finite type over `ℤ`.**
This is the opening move of the Stacks proof of Tag 0GTU: absolute Noetherian approximation
([Stacks, Tag 01ZA]) presents `X` as the limit of an inverse system with affine transitions
whose stages are of finite type over `ℤ`, and the projection to any stage is affine
([Stacks, Tag 01YX] part (1)). -/
theorem exists_isAffineHom_finiteType_target (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (X₀ : Scheme.{u}) (g : X ⟶ X₀), IsAffineHom g ∧
      LocallyOfFiniteType (terminal.from X₀) ∧ QuasiCompact (terminal.from X₀) :=
  let A := AlgebraicGeometry.LimitFPObjectDescent.finiteTypeSchemeApproximation X
  have : ∀ {a b : A.indexTypeᵒᵖ} (t : a ⟶ b), IsAffineHom (A.stages.map t) := A.transition_affine
  let i : A.indexTypeᵒᵖ := Opposite.op (Classical.arbitrary A.indexType)
  ⟨A.stages.obj i, A.projection.app i,
    AlgebraicGeometry.EventualLimit.isAffineHom_π_app A.stages (Cone.mk X A.projection) A.limit i,
    A.stage_locallyOfFiniteType i, A.stage_quasiCompact i⟩

/-- **The reduction in the proof of [Stacks, Tag 0GTU] to a base of finite type over `ℤ`.** Let
`X` be a quasi-compact and quasi-separated scheme. If every scheme of finite type over `ℤ` is the
target of a morphism which is of finite presentation, proper and completely decomposed and whose
source has an ample family of invertible modules, then `X` is the target of such a morphism.

Writing `X` as affine over a scheme `X₀` of finite type over `ℤ` by absolute Noetherian
approximation and pulling a morphism `Y₀ ⟶ X₀` back along `X ⟶ X₀` preserves finite
presentation ([Stacks, Tag 01TS]), properness and complete decomposition ([Stacks, Tag 0GTK]),
while `Y ⟶ Y₀` is affine and so carries the ample family of `Y₀` down to `Y`. Tag 0GTU itself is
`Stacks.BlowupAmpleFamily.exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily`. -/
theorem exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily_of_finiteTypeCase
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hFiniteTypeCase : ∀ X₀ : Scheme.{u}, LocallyOfFiniteType (terminal.from X₀) →
      QuasiCompact (terminal.from X₀) →
      ∃ (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ X₀), FinitePresentation f₀ ∧ IsProper f₀ ∧
        IsCompletelyDecomposed f₀ ∧
        ∃ (J : Type u) (N : J → Y₀.Modules), Y₀.IsAmpleFamily N) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), FinitePresentation f ∧ IsProper f ∧
      IsCompletelyDecomposed f ∧ ∃ (J : Type u) (N : J → Y.Modules), Y.IsAmpleFamily N := by
  obtain ⟨X₀, g, hg, hftX₀, hqcX₀⟩ := exists_isAffineHom_finiteType_target X
  obtain ⟨Y₀, f₀, ⟨hlfp, hqcf, hqsf⟩, hproper, hcd, J, N, hN⟩ := hFiniteTypeCase X₀ hftX₀ hqcX₀
  have hfst : IsAffineHom (pullback.fst f₀ g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback f₀ g).flip hg
  exact ⟨pullback f₀ g, pullback.snd f₀ g, ⟨inferInstance, inferInstance, inferInstance⟩,
    inferInstance, isCompletelyDecomposed_pullback f₀ g hcd,
    exists_isAmpleFamily_of_isAffineHom (pullback.fst f₀ g) N hN⟩

end Stacks.BlowupAmpleFamily

end
