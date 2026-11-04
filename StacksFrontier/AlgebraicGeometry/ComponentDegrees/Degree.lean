module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a locally free sheaf on a one-dimensional component

Let `f : X ⟶ Spec k` be proper with `topologicalKrullDim X ≤ 1` and let `E` be a finite locally
free sheaf of rank `r` on `X`. Stacks Tag 0AYW asserts

`curveDegree k f hdim E r = ∑ᶠ ξ, componentMultiplicity X ξ * componentDegree k f hdim E r ξ`

where the sum runs over the generic points of the one-dimensional components of `X`. This file
constructs the summand `componentDegree` appearing on the right, by discharging the three data
obligations needed to form it: properness of the component over `k`, its dimension bound, and
the rank of the restricted sheaf.

## Main definitions

* `Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree`: the degree of the restriction of
  `E` to the reduced one-dimensional component indexed by `ξ`.

## Main results

* `Stacks.AlgebraicGeometry.ComponentDegrees.isFiniteLocallyFreeOfRank_pullback_reducedComponentι`:
  the restriction of a finite locally free sheaf of rank `r` to a reduced component is again
  finite locally free of rank `r`. This is the third data obligation of Tag 0AYW.
* `Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp`: a reduced
  one-dimensional component of a scheme proper over `k` is a curve over `k` in the sense of
  Tag 0A23.

## Implementation notes

`componentDegree` applies `AlgebraicGeometry.curveDegree` with its properness, dimension and
rank arguments given positionally, since none of the three can be synthesized from the component
alone: they are consequences of the hypotheses on `X` proved in `Basic` and `Rank`.

The instance `(SheafOfModules.pushforward i.toRingCatSheafHom).IsRightAdjoint` is produced from
Mathlib's `Scheme.Modules.pullbackPushforwardAdjunction` rather than left to typeclass search —
Mathlib itself needs a transparency option to find it, and none is used here. The class
is `Prop`-valued, so this cannot disagree with the instance baked into `Scheme.Modules.pullback`;
the identification of `(Scheme.Modules.pullback i).obj E` with
`(SheafOfModules.pullback i.toRingCatSheafHom).obj E` is definitional.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.AlgebraicGeometry.ComponentDegrees

universe u

/-- The restriction of a finite locally free sheaf of rank `r` to a reduced one-dimensional
component is again finite locally free of rank `r`. This is the third data obligation carried by
the conclusion of Stacks Tag 0AYW. -/
theorem isFiniteLocallyFreeOfRank_pullback_reducedComponentι {X : Scheme.{u}}
    (ξ : genericPointsOne X) (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank := by
  have : (SheafOfModules.pushforward.{u}
      (reducedComponentι X ξ).toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (reducedComponentι X ξ)).isRightAdjoint
  exact rankPullbackData (reducedComponentι X ξ).base
    (reducedComponentι X ξ).toRingCatSheafHom E rank inferInstance

/-- A reduced one-dimensional component of a scheme proper over a field is a curve over that
field. -/
theorem isCurve_reducedComponentι_comp (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X) :
    IsCurve k (reducedComponentι X ξ ≫ f) := by
  have : IsProper (reducedComponentι X ξ ≫ f) := isProper_reducedComponentι_comp k f ξ
  refine (isCurve_iff k (reducedComponentι X ξ ≫ f)).2
    ⟨?_, topologicalKrullDim_reducedComponent X ξ⟩
  exact { toIsIntegral := isIntegral_reducedComponent X ξ
          toIsSeparated := inferInstance
          toLocallyOfFiniteType := inferInstance
          toQuasiCompact := inferInstance }

/-- The degree of the restriction of a finite locally free sheaf of rank `rank` to the reduced
one-dimensional component indexed by `ξ`. This is the summand on the right-hand side of
Stacks Tag 0AYW. -/
noncomputable def componentDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (ξ : genericPointsOne X) : ℤ :=
  @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
    (isProper_reducedComponentι_comp k f ξ) (topologicalKrullDim_reducedComponent_le X hX ξ)
    ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank
    (isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E rank)

/-- The defining formula for `componentDegree`: it is the difference of Euler characteristics on
the component, once the coherence instances are supplied. -/
theorem componentDegree_eq_eulerCharacteristic_sub (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (ξ : genericPointsOne X)
    (hE : ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E).IsCoherent)
    (hO : (SheafOfModules.unit (reducedComponent X ξ).ringCatSheaf).IsCoherent) :
    componentDegree k f hX E rank ξ =
      @eulerCharacteristic k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
          (isProper_reducedComponentι_comp k f ξ)
          ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) hE -
        (rank : ℤ) * @eulerCharacteristic k _ (reducedComponent X ξ)
          (reducedComponentι X ξ ≫ f) (isProper_reducedComponentι_comp k f ξ)
          (SheafOfModules.unit (reducedComponent X ξ).ringCatSheaf) hO :=
  rfl

end Stacks.AlgebraicGeometry.ComponentDegrees

end
