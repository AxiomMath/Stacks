module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# The chart base change of a finite morphism of finite presentation, read on schemes

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` and let `V` be
an étale scheme chart of `Y`.  Base change of charts along `f`,
`AlgebraicGeometry.Space.smallBaseChange`, produces an étale scheme chart `U = V ×_Y X` of `X`
together with its cartesian projection `ψ : U ⟶ V`, a morphism of the big fppf category over
`S`.  This file records that `ψ` is, **as a morphism of schemes**, finite when `f` is finite and
of finite presentation when `f` is of finite presentation.

This is the sentence "`U = V ×_Y X` is a scheme with a surjective étale morphism towards `X` and
a finite morphism `ψ : U ⟶ V` (the base change of `f`)" of the proof of Stacks 0610, in the form
the schemes version of that proof needs it: Stacks 05B4 is a statement about a morphism of
schemes carrying Mathlib's `AlgebraicGeometry.IsFinite` and
`AlgebraicGeometry.FinitePresentation`, whereas finiteness and finite presentation of `f` are
properties of a morphism of *algebraic spaces*.

No affineness of the chart is needed anywhere: the passage from a property of a morphism of
algebraic spaces to the property of the underlying morphism of schemes is made along `yoneda`,
not by testing on affines.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeChartHom` is the cartesian projection `ψ : V ×_Y X ⟶ V` of
  the chart base change, as a morphism of the big fppf category over `S`.

## Main results

* `AlgebraicGeometry.Space.finitePresentation_of_isFinitePresentation_yoneda_map`: a morphism of
  the big fppf category over `S` which represents a morphism of algebraic spaces of finite
  presentation is itself of finite presentation.  This is the converse of
  `AlgebraicGeometry.Space.isFinitePresentation_yoneda_map`.
* `AlgebraicGeometry.Space.isFinite_baseChangeChartHom`: **the chart base change of a finite
  morphism is a finite morphism of schemes.**
* `AlgebraicGeometry.Space.finitePresentation_baseChangeChartHom`: **the chart base change of a
  morphism of finite presentation is a morphism of schemes of finite presentation.**

## Implementation notes

The two transfers are not symmetric, and the asymmetry is in the library rather than in the
mathematics.

For finiteness, `AlgebraicGeometry.Space.IsFinite` is Stacks 03ZP, a condition on the base
changes along maps out of *affine* objects, so the passage to the underlying scheme morphism goes
through the representability criterion of Stacks 03ZQ: first
`AlgebraicGeometry.Space.presheaf_isFinite_of_isFinite`, which needs the morphism to be
relatively representable — automatic for `yoneda.map` — and then
`AlgebraicGeometry.Space.presheaf_yoneda_map_iff`, which is where the affine testing is undone.

For finite presentation, `AlgebraicGeometry.Space.IsFinitePresentation` is Stacks 03XP, part (3),
the conjunction of a chart condition with quasi-compactness and quasi-separatedness; the chart
condition is read off at the identity charts by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`, and the other two conjuncts by
their own transfer lemmas.  Stability of finite presentation under base change is
`AlgebraicGeometry.Space.IsFinitePresentation.of_isPullback`, which asks for all four corners of
the square to be algebraic spaces; the two corners that are not `X` and `Y` are representable,
hence algebraic spaces by `AlgebraicGeometry.Space.isAlgebraicSpace_yoneda`.

The square itself is the representability witness, `hrep.isPullback` of
`CategoryTheory.Functor.relativelyRepresentable`, and the morphism `ψ` is its second projection,
so no fibre product of the bounded category of schemes enters and the two statements below are
about the chosen witness that `AlgebraicGeometry.Space.smallBaseChange` is built from.

## References

* [Stacks Project, Tag 0610](https://stacks.math.columbia.edu/tag/0610)
* [Stacks Project, Tag 05B4](https://stacks.math.columbia.edu/tag/05B4)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the big fppf category over `S` representing a morphism of algebraic spaces
of finite presentation is of finite presentation.**  This is the converse of
`AlgebraicGeometry.Space.isFinitePresentation_yoneda_map`.

Finite presentation of a morphism of algebraic spaces is Stacks 03XP, part (3): locally of
finite presentation, quasi-compact and quasi-separated.  The first conjunct transfers by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`, the étale locality of
`AlgebraicGeometry.LocallyOfFinitePresentation` on source and target, and the other two by the
transfer lemmas of their own tags. -/
theorem finitePresentation_of_isFinitePresentation_yoneda_map
    {a b : BigFppfOver B S hS} (p : a ⟶ b)
    (hp : IsFinitePresentation B S hS (yoneda.map p)) :
    FinitePresentation ((BigFppfOver.toScheme B S hS).map p) :=
  ⟨(holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget p).1 hp.1,
    (presheaf_yoneda_map_iff B S hS (P := @AlgebraicGeometry.QuasiCompact.{u})
        inferInstance p).1
      ((presheaf_quasiCompact_iff_isQuasiCompact B S hS
        (Functor.relativelyRepresentable.map yoneda p)).2 hp.2.1),
    (isQuasiSeparated_yoneda_map_iff B S hS p).1 hp.2.2⟩

variable {X Y : AlgebraicSpaces B S hS}

/-- The cartesian projection `ψ : V ×_Y X ⟶ V` of the base change of a representable morphism
`f : X ⟶ Y` of algebraic spaces along an étale scheme chart `V` of `Y`, as a morphism of the big
fppf category over `S`.

It is the second projection of the chosen representability witness of `f`, which is the morphism
`AlgebraicGeometry.Space.smallBaseChange` is built from, so the source really is the object of
the big fppf category underlying the chart `AlgebraicGeometry.Space.baseChangeChart`. -/
noncomputable abbrev baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (SmallEtale.toOver B S hS X.1).obj (baseChangeChart B S hS f hrep V) ⟶
      (SmallEtale.toOver B S hS Y.1).obj V :=
  hrep.snd V.1.hom

/-- The chart base change is cartesian: the square exhibiting `V ×_Y X` as the fibre product of
the chart `V ⟶ Y` and `f`, which is the representability witness of `f` at `V`. -/
theorem isPullback_baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    IsPullback (hrep.fst V.1.hom) (yoneda.map (baseChangeChartHom B S hS f hrep V))
      f.hom V.1.hom :=
  hrep.isPullback V.1.hom

/-- **The chart base change of a finite morphism is a finite morphism of schemes.**  For `f`
finite and `V` an étale scheme chart of `Y`, the projection `ψ : V ×_Y X ⟶ V` carries
`AlgebraicGeometry.IsFinite` on the underlying morphism of schemes.

Finiteness of `ψ` as a morphism of algebraic spaces is stability of Stacks 03ZP under base
change along the cartesian square; the passage to the underlying morphism of schemes is
Stacks 03ZQ. -/
theorem isFinite_baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (hf : IsFinite B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)) :=
  (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsFinite.{u})
      inferInstance (baseChangeChartHom B S hS f hrep V)).1
    (presheaf_isFinite_of_isFinite _ (Functor.relativelyRepresentable.map yoneda _)
      (isFinite_of_isPullback B S hS (isPullback_baseChangeChartHom B S hS f hrep V) hf))

/-- **The chart base change of a morphism of finite presentation is a morphism of schemes of
finite presentation.**  For `f` of finite presentation and `V` an étale scheme chart of `Y`, the
projection `ψ : V ×_Y X ⟶ V` carries `AlgebraicGeometry.FinitePresentation` on the underlying
morphism of schemes.

Finite presentation of `ψ` as a morphism of algebraic spaces is
`AlgebraicGeometry.Space.IsFinitePresentation.of_isPullback`, whose hypotheses on the two
remaining corners of the square are met because both are representable; the passage to the
underlying morphism of schemes is
`AlgebraicGeometry.Space.finitePresentation_of_isFinitePresentation_yoneda_map`. -/
theorem finitePresentation_baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (V : SmallEtale B S hS Y.1) :
    FinitePresentation
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)) :=
  finitePresentation_of_isFinitePresentation_yoneda_map B S hS _
    (IsFinitePresentation.of_isPullback B S hS
      (isAlgebraicSpace_yoneda B S hS _) X.2 (isAlgebraicSpace_yoneda B S hS _) Y.2
      (isPullback_baseChangeChartHom B S hS f hrep V) hfp)

end AlgebraicGeometry.Space

end
