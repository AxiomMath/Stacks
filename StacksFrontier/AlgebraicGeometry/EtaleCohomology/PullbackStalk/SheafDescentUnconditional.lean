module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SmallEtaleSheafAdjPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# Descent data of small étale sheaves

The pullback pseudofunctor of small étale sheaves over a big étale site, obtained from the
adjunction pseudofunctor without coherence hypotheses, and the functor sending a small étale
sheaf to its canonical descent datum along a morphism.

These are stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent`, stated beside the ones
there: over more general coefficient universes, or with inputs carried there as hypotheses
discharged.

## Main definitions

* `AlgebraicGeometry.smallEtaleSheafPullbackSystemGeneral`: the canonically coherent pullback
  pseudofunctor of small étale sheaves.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctorGeneral`: the functor sending a small étale
  sheaf to its canonical descent datum along a morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v u' v'

namespace AlgebraicGeometry

attribute [local implicit_reducible] smallEtaleBaseChange

/-- The canonically coherent pullback pseudofunctor of small étale sheaves: the inverse-image
part of `AlgebraicGeometry.smallEtaleSheafAdjPseudofunctor`. -/
public noncomputable def smallEtaleSheafPullbackSystemGeneral
    (B : BigEtaleSite.{u}) : SmallEtaleSheafPullbackSystem B :=
  ⟨(smallEtaleSheafAdjPseudofunctor B).comp Bicategory.Adj.forget₁, fun _ => rfl, fun _ => rfl,
    by intro X Y Z f g; rfl⟩

/-- The functor sending a small étale sheaf to its canonical descent datum. -/
public noncomputable def smallEtaleSheafDescentFunctorGeneral
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)) ⥤
      (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.DescentData
        (fun _ : Unit ↦ f) :=
  (eqToHom ((smallEtaleSheafPullbackSystemGeneral B).fiber Y).symm).toFunctor ⋙
    (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData (fun _ : Unit ↦ f)

end AlgebraicGeometry

namespace CategoryTheory.Pseudofunctor.DescentData

end CategoryTheory.Pseudofunctor.DescentData

namespace AlgebraicGeometry

end AlgebraicGeometry

end
