module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Impurities
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange

/-!
# Impurities descend along a pointed base change

Let `ℱ` be a finite type quasi-coherent module on a scheme of finite type over `S`, let
`(S', s') → (S, s)` be a morphism of pointed schemes and let `ℱ_{S'}` be the pullback of `ℱ` to
the base change. An impurity of `ℱ_{S'}` above `s'` is already an impurity of `ℱ` above `s`:
its test family `T → S'` is composed with `S' → S`, and the specialization, the chosen point of
the total space and the base change of the total space are all left unchanged.

## Main definitions

* `AlgebraicGeometry.ImpurityDiagram.alongBaseChange` composes the test family of an impurity
  diagram on a pointed base change with the base-change morphism.

## Main results

* `AlgebraicGeometry.isImpurity_alongBaseChange`: that composite diagram is an impurity of the
  original module above the original point whenever the given one is an impurity of the
  base-changed module above the new point.

## Implementation notes

A pointed base change is given by an arbitrary cartesian square together with the equation on
distinguished points, and the base-changed module is specified only up to isomorphism with the
canonical pullback; this is the same presentation as in
`AlgebraicGeometry.isUniversallyPureAlong_iff_forall_baseChange_isPureAlong`.

The composite diagram keeps the test family, the two test points and the base change of the
total space of the given one, so its outer square is the horizontal pasting of the two cartesian
squares and its distinguished-fibre condition is literally that of the given diagram. Only the
membership in the relative assassin has to be transported, which uses that the relative assassin
is invariant under an isomorphism of modules together with the comparison of a pullback along a
composite with the composite of the two pullbacks.

## References

* [Stacks Project, Tag 05J6](https://stacks.math.columbia.edu/tag/05J6)
* [Stacks Project, Tag 05J7](https://stacks.math.columbia.edu/tag/05J7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The impurity diagram over the original base obtained from one over a pointed base change,
by composing its test family with the base-change morphism. -/
abbrev ImpurityDiagram.alongBaseChange {P Q : PrePureSituation.{u}} (g : Q.S ⟶ P.S)
    (hg : g.base Q.s = P.s) (toX : Q.X ⟶ P.X) (hpb : IsPullback toX Q.f P.f g)
    (E : ImpurityDiagram Q) : ImpurityDiagram P where
  T := E.T
  g := E.g ≫ g
  t' := E.t'
  t := E.t
  specializes := E.specializes
  mapsToChosenPoint := by
    rw [← E.mapsToChosenPoint] at hg
    simpa using hg
  X_T := E.X_T
  toX := E.toX ≫ toX
  toT := E.toT
  isPullback := E.isPullback.paste_horiz hpb
  xi := E.xi
  xi_liesOver := E.xi_liesOver

/-- An impurity of the pullback of a module above the distinguished point of a pointed base
change is an impurity of the module itself above the distinguished point of the original
base. -/
public theorem isImpurity_alongBaseChange {P Q : PrePureSituation.{u}} (g : Q.S ⟶ P.S)
    (hg : g.base Q.s = P.s) (toX : Q.X ⟶ P.X) (hpb : IsPullback toX Q.f P.f g)
    (hF : Q.F ≅ (Scheme.Modules.pullback toX).obj P.F)
    (E : ImpurityDiagram Q) (hE : IsImpurity Q E) :
    IsImpurity P (ImpurityDiagram.alongBaseChange g hg toX hpb E) := by
  let D := ImpurityDiagram.alongBaseChange g hg toX hpb E
  let ecomp : D.pulledBack P ≅
      (Scheme.Modules.pullback E.toX).obj ((Scheme.Modules.pullback toX).obj P.F) :=
    ((Scheme.Modules.pullbackComp E.toX toX).app P.F).symm
  let eD : D.pulledBack P ≅ ImpurityDiagram.pulledBack Q E :=
    ecomp ≪≫ ((Scheme.Modules.pullback E.toX).mapIso hF).symm
  refine ⟨?_, hE.2⟩
  show E.xi ∈ Stacks.Divisors.relativeAssassin E.toT (D.pulledBack P)
  rw [relativeAssassin_eq_of_moduleIso E.toT eD]
  exact hE.1

end AlgebraicGeometry
