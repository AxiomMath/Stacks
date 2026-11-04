module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorMonoidalLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal

/-!
# The unit coherences of the total tensor comparison of a pullback

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The comparison
`Tot(f^*K ⊗_{𝒪_X} f^*L) ≅ f^*Tot(K ⊗_{𝒪_Y} L)` of total tensor complexes assembled from
[Stacks, Tag 01CD] is compatible with the associator and the two unitors of the monoidal
structure on complexes, with the unit supplied by `ν : f^*𝒪_Y ≅ 𝒪_X`.

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorMonoidalLift` derives
those coherences from the unitality clauses of a monoidal structure on `f^*` whose oplax
tensorator is the comparison of [Stacks, Tag 01CD] and whose oplax unit is `ν`, taking the
structure as a parameter and the two prescriptions as hypotheses.
`Stacks.PullbackSheafTensor.monoidal` is such a structure, at the monoidal product the lift is
stated at, so this file supplies it and states the coherences unconditionally.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.isComparisonTensorator_sheafTensor` and
  `isComparisonUnit_sheafTensor`: the oplax tensorator of `Stacks.PullbackSheafTensor.monoidal`
  is the comparison of [Stacks, Tag 01CD] and its lax unit is `ν⁻¹`.
* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_rightUnitor` and
  `..._leftUnitor`: **the two unit coherences of the comparison of total tensor complexes**,
  with no hypothesis.
* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_eq_tensorator`: the
  comparison at a pair of complexes is the inverse tensorator of the monoidal lift of `f^*`.
* `Stacks.Cohomology.DerivedPullbackTensor.epsilon_pullbackComplex_zero`: the complex-level
  unit comparison of `f^*` in degree zero, in terms of `ν`.

## Implementation notes

**The monoidal structure is named, not synthesized.** `Stacks.PullbackSheafTensor.monoidal` is
stated for `Stacks.RingedSpace.pullbackFunctor` over
`Stacks.RingedSpace.structureRingSheaf`, and the lift asks for a structure on
`StacksDraft.KFlat.modulePullback` over `Stacks.SheafOfModules.Tensor.ringSheaf`.  The two are
the same functor between the same categories, and the passage is a conversion check, not a
syntactic match: `attribute [local instance] Stacks.PullbackSheafTensor.monoidal` does *not*
fire on the goal the lift presents, and `liftMonoidal` below — the same structure with its type
ascribed at the spelling the lift asks for — does.

**Why `Abelian` is supplied by hand.**  `Mod(𝒪_Z)` is abelian by
`SheafOfModules.instAbelian`, and instance search finds it unaided in the lift's own file.  The
import of `Stacks.PullbackSheafTensor.monoidal` reaches
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence`, which enlarges the
instance surface past the default search size, and then that instance — and with it
`HasZeroObject`, the monoidal structure on complexes, and everything the lift's statements are
spelled at — is no longer found.  `abelianModulesSheafTensor` names it, which keeps the search
short enough for the rest to follow.  The lift's own instances are re-attributed rather than
re-declared: a second copy of each would be a second instance term, and the lift's statements
mention the first.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

section Coherence

variable (Z : RingedSpace.{u, u})

/-- `Mod(𝒪_Z)` is abelian; see the implementation notes for why it is named here. -/
@[instance_reducible] local instance abelianModulesSheafTensor :
    Abelian (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  _root_.SheafOfModules.instAbelian (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)

attribute [local instance] monoidalModules symmetricModules monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The monoidal structure on `f^*` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal`, with its type
ascribed at the spelling of the functor and of the ring sheaf the lift to complexes asks for. -/
@[instance_reducible] local instance liftMonoidal :
    (StacksDraft.KFlat.modulePullback f).Monoidal :=
  Stacks.PullbackSheafTensor.monoidal f

/-- **The oplax tensorator of the monoidal structure carried by `f^*` is the comparison of
[Stacks, Tag 01CD].** -/
theorem isComparisonTensorator_sheafTensor : IsComparisonTensorator f := fun _ _ => rfl

/-- **The lax unit of the monoidal structure carried by `f^*` is the inverse of the comparison
`ν : f^*𝒪_Y ≅ 𝒪_X` of the structure sheaves.** -/
theorem isComparisonUnit_sheafTensor : IsComparisonUnit f := rfl

/-- **The comparison of total tensor complexes of [Stacks, Tag 079U] is the inverse tensorator
of the monoidal lift of `f^*` to complexes.** -/
theorem pullbackTensorComplexIso_eq_tensorator
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexIsoOfIsIso f K L =
      (Functor.mapHomologicalComplexTensorator (StacksDraft.KFlat.modulePullback f) K L).symm :=
  pullbackTensorComplexIsoOfIsIso_eq f (isComparisonTensorator_sheafTensor f) K L

/-- **The right unit coherence of the comparison of total tensor complexes.**  With the unit
supplied by the complex-level unit comparison of `f^*`, the comparison
`Tot(f^*K ⊗_{𝒪_X} f^*𝒪_Y[0]) ⟶ f^*Tot(K ⊗_{𝒪_Y} 𝒪_Y[0])` is compatible with the right unitors
of the two categories of complexes. -/
theorem pullbackTensorComplexIso_rightUnitor
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (ρ_ ((pullbackComplex f).obj K)).hom =
      (pullbackComplex f).obj K ◁ ε (pullbackComplex f) ≫
        (pullbackTensorComplexIsoOfIsIso f K
            (𝟙_ (CochainComplex
              (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))).inv ≫
          (pullbackComplex f).map (ρ_ K).hom :=
  pullbackTensorComplexIsoOfIsIso_rightUnitor f (isComparisonTensorator_sheafTensor f) K

/-- **The left unit coherence of the comparison of total tensor complexes**, obtained the same
way. -/
theorem pullbackTensorComplexIso_leftUnitor
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (λ_ ((pullbackComplex f).obj K)).hom =
      ε (pullbackComplex f) ▷ (pullbackComplex f).obj K ≫
        (pullbackTensorComplexIsoOfIsIso f
            (𝟙_ (CochainComplex
              (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)) K).inv ≫
          (pullbackComplex f).map (λ_ K).hom :=
  pullbackTensorComplexIsoOfIsIso_leftUnitor f (isComparisonTensorator_sheafTensor f) K

/-- **The unit comparison of the monoidal lift of `f^*` to complexes is `ν` in degree zero.**
Both identifications of the degree-zero term of a single-degree complex are inserted: the unit
of the complexes is `𝒪[0]`, not `𝒪`. -/
theorem epsilon_pullbackComplex_zero :
    (ε (pullbackComplex f)).f 0 ≫ (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))).hom ≫
        (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).inv :=
  epsilon_pullbackComplex_f_zero f (isComparisonUnit_sheafTensor f)

end Coherence

end Stacks.Cohomology.DerivedPullbackTensor

end
