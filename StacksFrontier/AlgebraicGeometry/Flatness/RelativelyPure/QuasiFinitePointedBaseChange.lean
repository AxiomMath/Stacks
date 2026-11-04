module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.QuasiFiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Permanence

/-!
# Purity is inherited by a quasi-finite pointed base change

Let `ℱ` be a finite type quasi-coherent module on a scheme of finite type over `S`, let `s` be a
point of `S` and let `(S', s') → (S, s)` be a morphism of pointed schemes which is quasi-finite
at `s'`. If `ℱ` is pure along the fibre over `s`, then its pullback `ℱ_{S'}` is pure along the
fibre over `s'`.

## Main results

* `AlgebraicGeometry.isPureAlong_of_quasiFiniteAt_of_isPureAlong`: purity along a fibre passes
  to a pointed base change which is quasi-finite at the new distinguished point.

## Implementation notes

An impurity of `ℱ_{S'}` above `s'` over an elementary étale neighbourhood of `s'` becomes, after
composing its test family with the base-change morphism, an impurity of `ℱ` above `s`; its test
family is then quasi-finite at the test point, being the composite of an étale morphism with a
morphism quasi-finite at the image of that point. Such a quasi-finite impurity is replaced by
one over an elementary étale neighbourhood of `s`, which purity of `ℱ` along the fibre over `s`
forbids.

A pointed base change is given by an arbitrary cartesian square together with the equation on
distinguished points, and the base-changed module is specified only up to isomorphism with the
canonical pullback; this is the same presentation as in
`AlgebraicGeometry.isUniversallyPureAlong_iff_forall_baseChange_isPureAlong` and in
`AlgebraicGeometry.isImpurity_alongBaseChange`.

## References

* [Stacks Project, Tag 05J7](https://stacks.math.columbia.edu/tag/05J7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05J7.** If a morphism of pointed schemes `(S', s') → (S, s)` is
quasi-finite at `s'` and a finite type quasi-coherent module is pure along the fibre over `s`,
then its pullback to the base change is pure along the fibre over `s'`. -/
@[stacks 05J7]
public theorem isPureAlong_of_quasiFiniteAt_of_isPureAlong {P Q : PrePureSituation.{u}}
    (g : Q.S ⟶ P.S) (hg : g.base Q.s = P.s) (toX : Q.X ⟶ P.X)
    (hpb : IsPullback toX Q.f P.f g)
    (hF : Q.F ≅ (Scheme.Modules.pullback toX).obj P.F)
    (hqf : quasiFiniteAt g Q.s) (hP : IsPureAlong P) :
    IsPureAlong Q := by
  intro D hEt _hElem hImp
  have hqfD : quasiFiniteAt D.g D.t := by
    have := hEt
    exact (forall_quasiFiniteAt_iff D.g).2 ⟨inferInstance, inferInstance⟩ D.t
  have hqfBase : quasiFiniteAt g (D.g.base D.t) := by
    rw [D.mapsToChosenPoint]
    exact hqf
  have hqfComp : quasiFiniteAt (D.g ≫ g) D.t := quasiFiniteAt_comp D.g g D.t hqfD hqfBase
  obtain ⟨D₂, hEt₂, hImp₂, hElem₂⟩ :=
    exists_isImpurity_elementaryEtaleNeighborhood_of_quasiFiniteAt P
      ⟨ImpurityDiagram.alongBaseChange g hg toX hpb D,
        isImpurity_alongBaseChange g hg toX hpb hF D hImp, hqfComp⟩
  exact hP D₂ hEt₂ hElem₂ hImp₂

end AlgebraicGeometry

end
