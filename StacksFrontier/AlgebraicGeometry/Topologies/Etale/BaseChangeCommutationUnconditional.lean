module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation
import all StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# BaseChangeCommutationUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry

/-- For a cartesian square in a big étale site, restriction to the small étale site of `S'`
followed by base change along `f` is base change along `f'` followed by restriction to the
small étale site of `T'`. -/
public noncomputable def smallEtaleCartesianIndexIsoGeneral
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T' T S' S : B.Scheme}
    (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) :
    smallEtaleToBigEtaleFunctor B S' S g ⋙ Over.pullback f ≅
      smallEtaleBaseChange B f' ⋙ smallEtaleToBigEtaleFunctor B T' T g' :=
  smallEtaleCartesianIndexIso B g' f' f g h

end AlgebraicGeometry
