module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexAssociator
public import StacksFrontier.Homology.MapHomologicalComplexBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorBraided

/-!
# The braiding coherence of the total tensor comparison of a pullback

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The comparison

`Tot(f^*K ⊗_{𝒪_X} f^*L) ≅ f^*Tot(K ⊗_{𝒪_Y} L)`

of total tensor complexes assembled from [Stacks, Tag 01CD] is compatible with the symmetry
constraint of the monoidal structure on cochain complexes given by the total tensor product: the
Koszul symmetry, whose sign on the summand of bidegree `(p, q)` is `(-1)^(p * q)`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_braiding`: the braiding
  coherence of the comparison of total tensor complexes.

## Implementation notes

The comparison at a pair of complexes is the inverse tensorator of the monoidal lift of `f^*` to
complexes (`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu_eq_tensorator`), so the
coherence is the braiding clause of `CategoryTheory.Functor.LaxBraided` for that lift,
`CategoryTheory.Functor.mapHomologicalComplexTensorator_braiding`. The Koszul symmetry
`CochainComplex.symmetricCategory` is a local instance, so that `β_` on cochain complexes means it.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pullback `f^*` as a braided monoidal functor: its monoidal part is
`Stacks.Cohomology.DerivedPullbackTensor.liftMonoidal` and its braiding clause is that of
`Stacks.PullbackSheafTensor.liftLaxBraided`. -/
@[instance_reducible] local instance liftBraided :
    (StacksDraft.KFlat.modulePullback f).Braided :=
  letI := Stacks.PullbackSheafTensor.liftLaxBraided f
  { toMonoidal := liftMonoidal f
    braided := Functor.LaxBraided.braided }

/-- The braiding coherence of the comparison of total tensor complexes: for cochain
complexes `K, L` of `𝒪_Y`-modules the square

```
f^*K ⊗ f^*L ⟶ f^*Tot(K ⊗ L)
     |                |
     | β              | f^*β
     v                v
f^*L ⊗ f^*K ⟶ f^*Tot(L ⊗ K)
```

commutes, the horizontal arrows being the comparison of [Stacks, Tag 01CD] assembled on total
complexes and `β` the Koszul symmetry of the total tensor product. -/
theorem pullbackTensorComplexIso_braiding
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMu f K L ≫ (pullbackComplex f).map (β_ K L).hom =
      (β_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)).hom ≫
        pullbackTensorComplexMu f L K := by
  simp only [pullbackTensorComplexMu_eq_tensorator]
  exact Functor.mapHomologicalComplexTensorator_braiding
    (StacksDraft.KFlat.modulePullback f) K L

end Stacks.Cohomology.DerivedPullbackTensor

end
