module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit

/-!
# The right unit coherence of the total tensor comparison, without monoidal notation

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_rightUnitor` states the right
unit coherence of the comparison `f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)` of total tensor
complexes in the notation of `SheafOfModules.monoidalCategorySheafTensor` and
`HomologicalComplex.monoidalCategory`: `ρ_`, `◁` and `𝟙_`.  Everything that consumes it works
instead at the spellings of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality` —
`Stacks.DerivedTensor.RingedSite.tensorComplexRightUnitorNatIso`,
`Stacks.DerivedTensor.RingedSite.unitComplex` and `HomologicalComplex.mapBifunctorMap` — because
those are the spellings the derived tensor product of [Stacks, Tag 06YU] is stated at.  This file
restates the coherence there.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackUnitComplexIso`: the complex-level unit
  comparison `𝒪_X[0] ≅ f^*(𝒪_Y[0])`, which is `CategoryTheory.Functor.Monoidal.εIso` of the
  monoidal lift of `f^*` to complexes, with its type ascribed at
  `Stacks.DerivedTensor.RingedSite.unitComplex`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_rightUnitorPlain`: **the
  right unit coherence of the comparison of total tensor complexes**, with the two unitors
  written as components of `tensorComplexRightUnitorNatIso` and the whiskering as
  `HomologicalComplex.mapBifunctorMap`.

## Implementation notes

The two spellings of each of the three ingredients are equal by `rfl` and not syntactically, so
the whole content of this file is a conversion check: `𝟙_` of the complexes is
`unitComplex` because `𝟙_` of `Mod(𝒪)` is `SheafOfModules.unit`, `ρ_` is the component of
`MonoidalCategory.rightUnitorNatIso` and `tensorComplexRightUnitorNatIso` *is* that natural
isomorphism, and `◁` of the induced monoidal structure on complexes is
`HomologicalComplex.mapBifunctorMap` with an identity in the first slot.  The monoidal
structures are named by the local instances of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorMonoidalLift` and
`...PullbackTensorComplexCoherence` rather than re-declared, so that the statements below are
about the same terms those files are about.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

section Plain

attribute [local instance] HasDerivedCategory.standard

variable (Z : RingedSpace.{u, u})

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The complex-level unit comparison of `f^*`**, `𝒪_X[0] ≅ f^*(𝒪_Y[0])`.  This is
`CategoryTheory.Functor.Monoidal.εIso` of the monoidal lift of `f^*` to cochain complexes, with
its source and target ascribed at `Stacks.DerivedTensor.RingedSite.unitComplex` rather than at
`𝟙_`; the two are equal by `rfl`, and the ascription is what makes the statements below
rewritable against the derived tensor product. -/
def pullbackUnitComplexIso :
    Stacks.DerivedTensor.RingedSite.unitComplex (Stacks.RingedSpace.toRingedSite X) ≅
      (pullbackComplex f).obj
        (Stacks.DerivedTensor.RingedSite.unitComplex (Stacks.RingedSpace.toRingedSite Y)) :=
  Functor.Monoidal.εIso (pullbackComplex f)

/-- **The right unit coherence of the comparison of total tensor complexes**, at the spellings of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality`: the
comparison of [Stacks, Tag 079U] on complexes, preceded by the complex-level unit comparison in
the right tensor factor and followed by `f^*` of the right unitor of total tensor complexes on
`Y`, is the right unitor of total tensor complexes on `X`.

This is `pullbackTensorComplexIso_rightUnitor` read through the three identifications described
in the implementation notes. -/
theorem pullbackTensorComplexIso_rightUnitorPlain
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackUnitComplexIso f).hom
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ) ≫
        (pullbackTensorComplexIsoOfIsIso f K
            (Stacks.DerivedTensor.RingedSite.unitComplex
              (Stacks.RingedSpace.toRingedSite Y))).inv ≫
          (pullbackComplex f).map
            ((Stacks.DerivedTensor.RingedSite.tensorComplexRightUnitorNatIso
              (Stacks.RingedSpace.toRingedSite Y)).app K).hom =
      ((Stacks.DerivedTensor.RingedSite.tensorComplexRightUnitorNatIso
        (Stacks.RingedSpace.toRingedSite X)).app ((pullbackComplex f).obj K)).hom :=
  (pullbackTensorComplexIso_rightUnitor f K).symm

end Plain

/-! ### The coherence under the localization functor

The three legs are separated here rather than where they are needed, because separating them is
exactly what the ambient instances of the section above prevent.  `Functor.map_comp` matches a
term `Q.map (u ≫ v)` only if the *object* arguments of `Q.map` are spelled the way the source and
target of `u ≫ v` are, and after the coherence above has been substituted they are not: the
`Q.map` is spelled at `Tot(- ⊗_𝒪 𝒪[0])`, which is where the unitor of
`tensorComplexRightUnitorNatIso` lives, and the composite at
`HomologicalComplex.mapBifunctor`.  So the split is performed in term mode, where only a
conversion check is owed, and in a section whose local instances are just the derived category's.
-/

section Localized

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`pullbackTensorComplexIso_rightUnitorPlain` in `D(𝒪_X)`, with the three legs separated.**
The right unitor of total tensor complexes on `X`, read in the derived category, is the
complex-level unit comparison in the right tensor factor, then the comparison of total tensor
complexes of [Stacks, Tag 079U], then `f^*` of the right unitor on `Y`. -/
theorem Q_map_tensorComplexRightUnitor_pullback
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    DerivedCategory.Q.map
        ((tensorComplexRightUnitorNatIso (Stacks.RingedSpace.toRingedSite X)).app
          ((pullbackComplex f).obj K)).hom =
      DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
              (pullbackUnitComplexIso f).hom
              (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (pullbackTensorComplexIsoOfIsIso f K
              (unitComplex (Stacks.RingedSpace.toRingedSite Y))).inv ≫
            DerivedCategory.Q.map ((pullbackComplex f).map
              ((tensorComplexRightUnitorNatIso (Stacks.RingedSpace.toRingedSite Y)).app
                  K).hom) := by
  refine Eq.trans (congrArg DerivedCategory.Q.map
    (pullbackTensorComplexIso_rightUnitorPlain f K).symm) ?_
  refine Eq.trans (DerivedCategory.Q.map_comp _ _) ?_
  exact congrArg (fun φ => DerivedCategory.Q.map _ ≫ φ) (DerivedCategory.Q.map_comp _ _)

end Localized

end Stacks.Cohomology.DerivedPullbackTensor

end
