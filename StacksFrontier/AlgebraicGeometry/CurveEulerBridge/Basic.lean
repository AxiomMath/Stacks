module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Degree

/-!
# Degree as a difference of Euler characteristics, with no coherence hypothesis

Let `X` be a scheme proper over a field `k`. Then `X` is locally Noetherian, so by
[Stacks, Tag 01XZ] its structure sheaf and every finite locally free sheaf on it are coherent.
Consequently the degree `AlgebraicGeometry.curveDegree` of [Stacks, Tag 0AYR] of a finite locally
free sheaf of constant rank is the difference of Euler characteristics
`AlgebraicGeometry.eulerCharacteristic` ([Stacks, Tag 0BEJ]) with no coherence hypothesis, on the
nose and on each reduced one-dimensional component.

## Main results

* `Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field`: a
  scheme proper over a field is locally Noetherian.
* `Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`: on a scheme proper over a field
  the structure sheaf is coherent.
* `Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank`: on a
  scheme proper over a field a finite locally free sheaf of constant rank is coherent.
* `Stacks.AlgebraicGeometry.CurveEulerBridge.curveDegree_eq_eulerCharacteristic_sub`: the degree
  of [Stacks, Tag 0AYR] is the difference of Euler characteristics, with no coherence
  hypothesis.
* `Stacks.AlgebraicGeometry.CurveEulerBridge.componentDegree_eq_eulerCharacteristic_sub`: the
  same for the summand on the right-hand side of [Stacks, Tag 0AYW].

## Implementation notes

`SheafOfModules.IsFiniteLocallyFree` is written with its universes explicit, as
`SheafOfModules.IsFiniteLocallyFree.{u, u, u}`: elaborated from the module alone its three
universe parameters default to `0`, and the application to `E : X.Modules` is then a universe
mismatch rather than a failed instance search.

`SheafOfModules.IsCoherent` here is the class of Stacks Tag 01BW, the one
`AlgebraicGeometry.eulerCharacteristic` takes and Tag 01XZ produces; it does not unify with
`Stacks.SheafOfModules.IsCoherent`.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

public section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ComponentDegrees

namespace Stacks.AlgebraicGeometry.CurveEulerBridge

universe u

/-- A scheme proper over a field is locally Noetherian: a proper morphism is locally of finite
type, and the spectrum of a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_isProper_over_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- **The structure sheaf of a scheme proper over a field is coherent.** -/
theorem isCoherent_unit (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] :
    (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isProper_over_field k f
  CoherentKernel.structureSheaf_isCoherent X

/-- **A finite locally free sheaf of constant rank on a scheme proper over a field is
coherent.** -/
theorem isCoherent_of_isFiniteLocallyFreeOfRank (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] : E.IsCoherent :=
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isProper_over_field k f
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E rank
  CoherentKernel.isCoherent_of_isFiniteLocallyFree X E

/-- **The degree of [Stacks, Tag 0AYR] is the difference of Euler characteristics**, with no
coherence hypothesis: properness over the field supplies both coherence instances. -/
theorem curveDegree_eq_eulerCharacteristic_sub (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    curveDegree k f hdim E rank =
      @eulerCharacteristic k _ X f _ E (isCoherent_of_isFiniteLocallyFreeOfRank k f E rank) -
        (rank : ℤ) * @eulerCharacteristic k _ X f _ (SheafOfModules.unit X.ringCatSheaf)
          (isCoherent_unit k f) :=
  rfl

/-- **The summand on the right-hand side of [Stacks, Tag 0AYW] is a difference of Euler
characteristics on the component**, with no coherence hypothesis: the component is itself proper
over the field, and the restriction of a finite locally free sheaf of rank `rank` is again finite
locally free of rank `rank`, so both coherence instances are available there too. -/
theorem componentDegree_eq_eulerCharacteristic_sub (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] (ξ : genericPointsOne X) :
    componentDegree k f hdim E rank ξ =
      @eulerCharacteristic k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
          (isProper_reducedComponentι_comp k f ξ)
          ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E)
          (@isCoherent_of_isFiniteLocallyFreeOfRank k _ (reducedComponent X ξ)
            (reducedComponentι X ξ ≫ f) (isProper_reducedComponentι_comp k f ξ)
            ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank
            (isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E rank)) -
        (rank : ℤ) * @eulerCharacteristic k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
          (isProper_reducedComponentι_comp k f ξ)
          (SheafOfModules.unit (reducedComponent X ξ).ringCatSheaf)
          (@isCoherent_unit k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
            (isProper_reducedComponentι_comp k f ξ)) :=
  rfl

end Stacks.AlgebraicGeometry.CurveEulerBridge
