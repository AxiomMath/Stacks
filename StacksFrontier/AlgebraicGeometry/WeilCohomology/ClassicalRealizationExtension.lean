module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Variety
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRealization
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMotive

/-!
# The realization of a classical Weil cohomology theory

A classical Weil cohomology theory `H^*` (Stacks 0FGV) extends to data (D0)–(D3) satisfying (A),
(B), (C) on all smooth projective schemes (`ClassicalWeilCohomologyTheory.toWeilDataAxioms`, the
first step of Stacks 0FH2), which give a functor `G : M_k ⥤ graded F-vector spaces` with
`h ⋙ G ≅ H^*` (Stacks 0FHL, `WeilDataAxioms.motiveFunctor`). This file restricts that
identification to varieties: `H^*(X) = G(h(X))` naturally in the smooth projective variety `X`,
as a `PoincarePairingSetup.MotiveComparison`.

## Main definitions

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.motiveFunctor`: the functor `G`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.motiveComparison`: `H^*(X) = G(h(X))`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.WeilCohomology.ChowMotiveCat (h)

universe u v

namespace Stacks.WeilCohomology.ClassicalWeilCohomologyTheory

open SmoothProjective (toSchemeCat)

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-- The functor `G : M_k ⥤ graded F-vector spaces` of a classical Weil cohomology theory: that of
Stacks 0FHL for its extension to all smooth projective schemes. -/
abbrev motiveFunctor : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F) :=
  T.toWeilDataAxioms.motiveFunctor

/-- The cohomology of the extension restricted to varieties is the classical cohomology,
`H^n_ext(X) ≅ H^n(X)`, naturally in `X`. -/
def restrictCohomologyIso :
    (toSchemeCat k).op ⋙ T.toWeilDataAxioms.cohomologyFunctor ≅
      T.toPre.toPoincarePairingSetup.cohomologyFunctor :=
  NatIso.ofComponents (fun X ↦ GradedObject.isoMk _ _ fun n ↦
      (T.varietyGradeEquiv X.unop n).toModuleIso) fun {X Y} f ↦ by
    funext n
    ext a
    exact T.varietyGradeEquiv_pullDeg f.unop n a

/-- **`H^*(X) = G(h(X))`** for a smooth projective variety `X`, naturally in `X`. -/
def motiveComparison : T.toPre.toPoincarePairingSetup.MotiveComparison T.motiveFunctor :=
  PoincarePairingSetup.MotiveComparison.ofIso
    (Functor.isoWhiskerLeft (toSchemeCat k).op
        (WeilData.motiveFunctorCohomologyIso T.toWeilDataAxioms.poincareDuality
          T.toWeilDataAxioms.kunneth T.toWeilDataAxioms.cycleClassAxiom) ≪≫
      T.restrictCohomologyIso)

end Stacks.WeilCohomology.ClassicalWeilCohomologyTheory

end
