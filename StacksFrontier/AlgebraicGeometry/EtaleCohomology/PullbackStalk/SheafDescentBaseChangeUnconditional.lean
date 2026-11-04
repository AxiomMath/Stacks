module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentUnconditional

/-!
# SheafDescentBaseChangeUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u v' u'

namespace AlgebraicGeometry

/-- The small étale sheaf descent functor is an equivalence exactly when the canonical descent
functor of the small étale sheaf pseudofunctor is. -/
public theorem isEquivalence_smallEtaleSheafDescentFunctor_iff_general
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence ↔
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
        (fun _ : Unit ↦ f)).IsEquivalence := by
  have he :
      ((eqToHom ((smallEtaleSheafPullbackSystemGeneral B).fiber Y).symm).toFunctor).IsEquivalence :=
    isEquivalence_toFunctor_eqToHom _
  constructor
  · intro hyp
    dsimp [smallEtaleSheafDescentFunctorGeneral] at hyp
    exact Functor.isEquivalence_of_comp_left
      (eqToHom ((smallEtaleSheafPullbackSystemGeneral B).fiber Y).symm).toFunctor _
  · intro hyp
    dsimp [smallEtaleSheafDescentFunctorGeneral]
    infer_instance

end AlgebraicGeometry

end
