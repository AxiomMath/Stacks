module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence

/-!
# The associativity coherence of the total tensor comparison of a pullback

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The comparison

`Tot(f^*K ⊗_{𝒪_X} f^*L) ≅ f^*Tot(K ⊗_{𝒪_Y} L)`

of total tensor complexes assembled from [Stacks, Tag 01CD] is compatible with the associator of
the monoidal structure on cochain complexes given by the total tensor product.  This file states
that compatibility, unconditionally.

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence` states
the two *unit* coherences the same way, and its implementation notes record that the associativity
coherence "is available the same way"; this file is that sentence carried out.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu`: the inverse comparison at a
  pair of complexes, with its source read at the monoidal spelling `⊗` of the total tensor
  product rather than at `Stacks.SheafOfModules.Tensor.tensorComplex`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_associator`: **the
  associativity coherence of the comparison of total tensor complexes**, with no hypothesis.
* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu_eq_tensorator`: the comparison
  so read is the tensorator of the monoidal lift of `f^*` to complexes.

## Implementation notes

**No total complex is taken apart here.**  The comparison at a pair of complexes is the inverse
tensorator of the monoidal lift of `f^*` to complexes
(`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_eq_tensorator`, which rests on
`Stacks.PullbackSheafTensor.monoidal`), so the coherence is the `associativity` clause of
`CategoryTheory.Functor.Monoidal` for that lift —
`CategoryTheory.Functor.mapHomologicalComplexTensorator_associativity`.  That clause is where the
summandwise computation with the antidiagonal inclusions happens, and it is already proved.

**Why `pullbackTensorComplexMu` exists.**  The two spellings of the total tensor complex —
`Stacks.SheafOfModules.Tensor.tensorComplex`, which the type of
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso` is written at, and `⊗`
of `CategoryTheory.MonoidalCategory`, which the associator and the tensorator are written at —
are the same object, but identifying them is a conversion check that the `HomologicalComplex`
instance arguments make expensive, and `getColimitCocone` is not exposed, so the check cannot be
finished by unfolding.  Stated directly, with four occurrences of the comparison and an
associator, the coherence exceeds the default elaboration budget.  `pullbackTensorComplexMu` pays
for the identification **once**, in the ascribed type of a definition; the coherence is then an
equation all of whose terms are already at the monoidal spelling, and its proof is one `simp only`
and that clause.  No heartbeat option is set.

**The instances are re-attributed, not re-declared.**  The monoidal structure on `Mod(𝒪_Z)`, on
complexes, and the monoidal lift of `f^*` are the `local instance`s of
`...DerivedPullback.PullbackTensorMonoidalLift` and
`...DerivedPullback.PullbackTensorComplexCoherence`.  A second copy of any of them would be a
second instance term, and the statements of the two files this one builds on mention the first;
so they are brought into scope by `attribute [local instance]` on the existing names.

## What this does *not* give

This is the **complex-level** coherence.  The derived-level statement — that the comparison of
[Stacks, Tag 079U] carries the associator of `D(𝒪_Y)` to that of `D(𝒪_X)`, i.e.
`Stacks.Cohomology.DerivedRelativeCupProduct.PullbackTensorComparisonAssociative` — needs this
together with a second input which the tree does **not** have: the compatibility of the K-flat
comparison of [Stacks, Tag 06YU] with the associator of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`.  That is the clause of
[Stacks, Tag 0FPT] recorded as absent in the "What this file does not contain" section of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseat.lean` and again in the
notes of `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Associativity.lean`.  With
both in hand the descent is
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat` applied to
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_of_kFlat`, exactly as
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` descends the composition
law.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison of total tensor complexes, read at the monoidal spelling of the total
tensor product.**  `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso` has
its source written with the bifunctor `Stacks.SheafOfModules.Tensor.tensorComplex`, while the
associator and the tensorator are written with `⊗`; the two are the same object, and this is the
inverse comparison with the second spelling ascribed, so that a statement combining it with the
associator pays for the identification once rather than once per occurrence. -/
def pullbackTensorComplexMu
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackComplex f).obj K ⊗ (pullbackComplex f).obj L ⟶ (pullbackComplex f).obj (K ⊗ L) :=
  (pullbackTensorComplexIsoOfIsIso f K L).inv

/-- `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu` is the inverse comparison
of total tensor complexes itself, with no transport. -/
theorem pullbackTensorComplexMu_eq
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMu f K L = (pullbackTensorComplexIsoOfIsIso f K L).inv :=
  rfl

/-- **`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu` is the tensorator of the
monoidal lift of `f^*` to complexes.** -/
theorem pullbackTensorComplexMu_eq_tensorator
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMu f K L =
      (Functor.mapHomologicalComplexTensorator
        (StacksDraft.KFlat.modulePullback f) K L).hom :=
  congrArg Iso.inv (pullbackTensorComplexIso_eq_tensorator f K L)

/-- **The associativity coherence of the comparison of total tensor complexes.**  For cochain
complexes `K, L, M` of `𝒪_Y`-modules the square

```
(f^*K ⊗ f^*L) ⊗ f^*M ⟶ f^*Tot(K ⊗ L) ⊗ f^*M ⟶ f^*Tot(Tot(K ⊗ L) ⊗ M)
         |                                              |
         | α                                            | f^*α
         v                                              v
f^*K ⊗ (f^*L ⊗ f^*M) ⟶ f^*K ⊗ f^*Tot(L ⊗ M) ⟶ f^*Tot(K ⊗ Tot(L ⊗ M))
```

commutes, the unlabelled arrows being the comparison of [Stacks, Tag 01CD] assembled on total
complexes in one or the other tensor factor and `α` the associator of the total tensor product.
This is the associativity axiom of `CategoryTheory.Functor.Monoidal` for the monoidal lift of
`f^*` to complexes, read through the identification of the comparison with the tensorator. -/
theorem pullbackTensorComplexIso_associator
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMu f K L ▷ (pullbackComplex f).obj M ≫
        pullbackTensorComplexMu f (K ⊗ L) M ≫
          (pullbackComplex f).map (α_ K L M).hom =
      (α_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M)).hom ≫
        (pullbackComplex f).obj K ◁ pullbackTensorComplexMu f L M ≫
          pullbackTensorComplexMu f K (L ⊗ M) := by
  simp only [pullbackTensorComplexMu_eq_tensorator]
  exact Functor.mapHomologicalComplexTensorator_associativity
    (StacksDraft.KFlat.modulePullback f) K L M

end Stacks.Cohomology.DerivedPullbackTensor

end
