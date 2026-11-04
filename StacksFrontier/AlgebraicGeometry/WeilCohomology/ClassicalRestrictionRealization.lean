module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRealization
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRestriction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMotive

/-!
# The realization of the restriction of Weil data to varieties

For data (D0)–(D3) satisfying (A), (B), (C), Stacks 0FHL gives a functor
`G : M_k ⥤ graded F-vector spaces` with `h ⋙ G ≅ H^*` (`WeilDataAxioms.motiveFunctor`). On the
restriction of the data to smooth projective varieties (`WeilDataAxioms.toPreClassical`) this is
an identification `H^*(X) = G(h(X))`, natural in the variety `X`.

## Main definitions

* `Stacks.WeilCohomology.WeilDataAxioms.restrictCohomologyIso`: the cohomology functor of the
  restriction is the restriction of the cohomology functor.
* `Stacks.WeilCohomology.WeilDataAxioms.motiveComparison`: `H^*(X) = G(h(X))`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u w

namespace Stacks.WeilCohomology.WeilDataAxioms

open SmoothProjective (toSchemeCat)

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type w} [Field F] [CharZero F]
  (W : WeilDataAxioms k F)

/-- The cohomology `X ↦ H^*(X)` of the restriction of `W` to varieties is the restriction of
the cohomology functor of `W`. -/
def restrictCohomologyIso :
    (toSchemeCat k).op ⋙ W.cohomologyFunctor ≅ W.toPoincarePairingSetup.cohomologyFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    funext n
    ext a
    rfl

/-- **`H^*(X) = G(h(X))`** for the restriction of `W` to varieties and the functor `G` of
Stacks 0FHL, naturally in the variety `X`. -/
def motiveComparison :
    W.toPreClassical.toPoincarePairingSetup.MotiveComparison W.motiveFunctor :=
  PoincarePairingSetup.MotiveComparison.ofIso
    (Functor.isoWhiskerLeft (toSchemeCat k).op
        (WeilData.motiveFunctorCohomologyIso W.poincareDuality W.kunneth W.cycleClassAxiom) ≪≫
      W.restrictCohomologyIso)

end Stacks.WeilCohomology.WeilDataAxioms

end
