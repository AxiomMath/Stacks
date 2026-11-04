module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite

/-!
# Extending finiteness from a dense open subspace

A flat proper morphism of algebraic spaces which is finite over a dense open subspace of its
target is finite, provided it is locally of finite presentation or the open immersion is
quasi-compact.

## Main results

* `AlgebraicGeometry.Space.isFinite_of_isFinite_over_dense_open` is **Stacks 0B4J**.

## Implementation notes

Finiteness is turned into a relative-dimension statement in both directions. A finite morphism
is locally quasi-finite (Stacks 04NY), and a morphism locally of finite type is locally
quasi-finite exactly when its relative dimension vanishes at every point of its source (Stacks
04NV); so the hypothesis over the dense open subspace says that the restricted morphism has
relative dimension `≤ 0`. Stacks 0878 extends that bound from the dense open subspace to the
whole target, under the same disjunctive hypothesis, and Stacks 04NV reads the extended bound
back as local quasi-finiteness of `f`. A proper locally quasi-finite morphism is finite, which
is the implication (2) ⇒ (1) of Stacks 0A4X.

This is the argument of the source, whose first two steps are exactly Stacks 0878 and Stacks
04NV. The source finishes by using representability to reduce to the case of schemes, Stacks
0B48; here the algebraic-space statement that a proper locally quasi-finite morphism is finite
is already available, so no reduction is needed.

Being locally of finite type, which both applications of Stacks 04NV need, is not an extra
hypothesis: it is part of properness. For the restricted morphism it is the base change of that
along the open immersion, Stacks 03XH.

## References

* [Stacks Project, Tag 0B4J](https://stacks.math.columbia.edu/tag/0B4J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A flat morphism of algebraic spaces over `S` which is locally of finite type and finite
over an open subspace of its target has relative dimension `≤ 0` over that open subspace.

This is the hypothesis of Stacks 0B4J in the form Stacks 0878 consumes. -/
theorem hasRelativeDimensionLE_zero_pullback_snd_of_isFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hfinite : IsFinite B S hS (pullback.snd f V.ι)) :
    HasRelativeDimensionLE 0 B S hS (pullback.snd f V.ι) := by
  have hlftV : IsLocallyOfFiniteType B S hS (pullback.snd f V.ι) :=
    IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f V.ι).flip hX hY hlft
  have hqfV : IsLocallyQuasiFinite B S hS (pullback.snd f V.ι) :=
    (isQuasiFinite_of_isFinite B S hS (pullback.snd f V.ι)
      (isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY) hV.1 hfinite).1
  intro x
  refine ⟨0, le_rfl, ?_⟩
  have h := (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
    (pullback.snd f V.ι) hlftV).1 hqfV x
  simpa using h

/-- A morphism of algebraic spaces over `S` which is locally of finite type and of relative
dimension `≤ 0` is locally quasi-finite.

This is the conclusion of Stacks 0878 in the form the final step of Stacks 0B4J consumes. -/
theorem isLocallyQuasiFinite_of_hasRelativeDimensionLE_zero (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hdim : HasRelativeDimensionLE 0 B S hS f) :
    IsLocallyQuasiFinite B S hS f :=
  (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS f hlft).2 fun x ↦ by
    obtain ⟨e, he, h⟩ := hdim x
    rw [Nat.le_zero.mp he] at h
    simpa using h

/-- **Stacks 0B4J.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is flat
and proper. Let `V` be an open subspace of `Y` whose points are dense in the points of `Y` and
such that the base change `X_V ⟶ V` of `f` is finite. If moreover `f` is locally of finite
presentation or the open immersion `V ⟶ Y` is quasi-compact, then `f` is finite. -/
@[stacks 0B4J]
theorem isFinite_of_isFinite_over_dense_open
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hproper : IsProper B S hS f)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)))
    (hfinite : IsFinite B S hS (pullback.snd f V.ι))
    (hfin : IsLocallyOfFinitePresentation B S hS f ∨ IsQuasiCompact B S hS V.ι) :
    IsFinite B S hS f := by
  have hlft : IsLocallyOfFiniteType B S hS f := hproper.2.1.1
  have hdim : HasRelativeDimensionLE 0 B S hS f :=
    relativeDimensionLE_of_dense_open B S hS hX hY f V hV hVdense hflat hlft 0
      (hasRelativeDimensionLE_zero_pullback_snd_of_isFinite B S hS hX hY f V hV hlft hfinite) hfin
  exact isFinite_of_isProper_of_isLocallyQuasiFinite B S hS hX hY f hproper
    (isLocallyQuasiFinite_of_hasRelativeDimensionLE_zero B S hS f hlft hdim)

end AlgebraicGeometry.Space

end
