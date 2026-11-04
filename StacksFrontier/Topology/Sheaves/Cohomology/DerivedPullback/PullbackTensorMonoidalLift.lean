module

public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor

/-!
# The total tensor comparison of a pullback is a tensorator

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Two constructions produce the
comparison `f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)` of total tensor complexes:

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso`, which assembles the
  degreewise comparison of [Stacks, Tag 01CD] by `CategoryTheory.Functor.mapBifunctorTotalIso`;
* the tensorator `CategoryTheory.Functor.mapHomologicalComplexTensorator` of the lift of a
  monoidal functor to complexes with the total tensor product.

This file identifies them.  The identification is what makes the unit coherence of the
comparison a consequence of the `CategoryTheory.Functor.Monoidal` axioms instead of a
computation with total complexes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso_inv_eq`: **the inverse
  of the comparison at a pair of complexes is the tensorator `μ` of `f^*` on complexes**, with
  `pullbackTensorComplexIsoOfIsIso_eq` the same identification read on the isomorphisms and
  `pullbackTensorComplexNatIso_inv_app_eq` on the bifunctorial comparison.
* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso_rightUnitor`: **the
  right unit coherence of the comparison**, with the unit supplied by the complex-level unit
  comparison of `f^*`, and `..._leftUnitor` the left unit coherence.  Both are a unitality
  clause of `CategoryTheory.Functor.Monoidal` for the lift, read through the identification; the
  associativity coherence is available the same way.
* `Stacks.Cohomology.DerivedPullbackTensor.epsilon_pullbackComplex_f_zero`: the complex-level
  unit comparison of `f^*` in degree zero, in terms of `ν : f^*𝒪_Y ≅ 𝒪_X`.

## Implementation notes

**The monoidal structure on `Mod(𝒪_Z)`.** The statements below are read at
`SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf` *definitionally*, and whose unit is
`SheafOfModules.unit`.  That is forced: `pullbackTensorComplexNatIso` is
`CategoryTheory.Functor.mapBifunctorTotalIso` at the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, the tensorator is the same construction at
`MonoidalCategory.curriedTensor`, and only for the re-seated structure are the two the same
term.  The ring sheaf is spelled `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`, through
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules`, for the same reason: that is the
spelling the total tensor complex and the degreewise pullback of a complex are stated at, and
the one at which the monoidal structure synthesizes.

**Why the tensorator datum is a hypothesis.** The monoidal structure of `f^*` whose oplax
tensorator is the comparison of [Stacks, Tag 01CD] is
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, and it is stated at a *different*
monoidal structure on `Mod(𝒪_Z)`, namely `Stacks.SheafOfModules.Strict.monoidalCategory`.  The
two agree on objects, on the unit and on the associator — all three by `rfl` — and differ on
the two whiskerings and on the two unitors, the unitors because the underlying localized
structures are built with different unit objects.  So `pullbackComparisonMonoidal` is not
available at the structure used here, and the monoidal structure of `f^*` enters below as a
parameter whose tensorator and unit are prescribed by `IsComparisonTensorator` and
`IsComparisonUnit`.  Both hold by `rfl` for any structure built with the comparison of
[Stacks, Tag 01CD] as its `μIso.inv`.

Such a structure at the re-seated tensor product **does** exist in this development:
`Stacks.PullbackSheafTensor.monoidal`, of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackSheafTensorMonoidal.lean`, is stated at
`SheafOfModules.monoidalCategorySheafTensor` — the structure used here — and it is obtained from
the module-level coherences of [Stacks, Tag 01CD] directly rather than by identifying the
re-seated and the strict structures, so the identification this note once called for is not
needed.  It is not imported here, because importing it is what the downstream file
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorComplexCoherence.lean`
does: that file supplies it to the statements below and so states their conclusions
unconditionally.  The parametrization is kept so that this file's statements remain usable at any
other such structure.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

section Monoidal

variable (Z : RingedSpace.{u, u})

/-- The monoidal structure on `Mod(𝒪_Z)` whose tensor product is the tensor product sheaf. -/
@[instance_reducible] local instance monoidalModules :
    MonoidalCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.monoidalCategorySheafTensor Z.sheaf

/-- The symmetry of that structure. -/
@[instance_reducible] local instance symmetricModules :
    SymmetricCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.symmetricCategorySheafTensor Z.sheaf

/-- That structure is additive in each variable. -/
local instance monoidalPreadditiveModules :
    MonoidalPreadditive (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.monoidalPreadditiveSheafTensor Z.sheaf

/-- That structure is closed. -/
@[instance_reducible] local instance monoidalClosedModules :
    MonoidalClosed (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  SheafOfModules.monoidalClosedSheafTensor Z.sheaf

/-- The coproducts over the antidiagonals that form the tensor product of two graded objects of
`𝒪_Z`-modules exist. -/
local instance hasTensorModules :
    ∀ A B : GradedObject ℤ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z),
      GradedObject.HasTensor A B :=
  fun _ _ => inferInstance

/-- The total tensor product of complexes of `𝒪_Z`-modules. -/
@[instance_reducible] local instance monoidalComplexes :
    MonoidalCategory
      (CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :=
  HomologicalComplex.monoidalCategory _ _

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [(StacksDraft.KFlat.modulePullback f).Monoidal]

/-- The hypothesis that the oplax tensorator of the monoidal structure carried by `f^*` is the
comparison morphism of [Stacks, Tag 01CD]. -/
abbrev IsComparisonTensorator : Prop :=
  ∀ A B : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y,
    δ (StacksDraft.KFlat.modulePullback f) A B = (comparisonAppIso f A B).hom

/-- The degreewise comparison fed to `mapBifunctorTotalIso` by the tensorator of the lift is the
degreewise comparison of [Stacks, Tag 01CD]. -/
theorem mapHomologicalComplexTensorComparison_eq (hδ : IsComparisonTensorator f)
    (A B : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) :
    Functor.mapHomologicalComplexTensorComparison (StacksDraft.KFlat.modulePullback f) A B =
      comparisonAppIso f A B :=
  Iso.ext (hδ A B)

/-- The inverse of the degreewise comparison of [Stacks, Tag 01CD] is the tensorator of the
monoidal structure carried by `f^*`. -/
theorem comparisonAppIso_inv_eq (hδ : IsComparisonTensorator f)
    (A B : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) :
    (comparisonAppIso f A B).inv = μ (StacksDraft.KFlat.modulePullback f) A B :=
  congrArg Iso.inv (mapHomologicalComplexTensorComparison_eq f hδ A B).symm

/-- **The comparison of total tensor complexes is the tensorator of `f^*` on complexes**, read
on the inverse: both are determined on the summands of `Tot(f^*K ⊗_{𝒪_X} f^*L)`, and on the
summand indexed by `(p, q)` both are the inverse of the degreewise comparison of
[Stacks, Tag 01CD] followed by `f^*` of the inclusion. -/
theorem pullbackTensorComplexIsoOfIsIso_inv_eq (hδ : IsComparisonTensorator f)
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexIsoOfIsIso f K L).inv = μ (pullbackComplex f) K L := by
  have : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  refine (Stacks.Cohomology.DerivedPullbackTensor.ι_pullbackTensorComplexIsoOfIsIso_inv
    f K L p q n hpq).trans ?_
  refine Eq.trans ?_ (Functor.ι_mapHomologicalComplexTensorator_hom
    (StacksDraft.KFlat.modulePullback f) K L p q n hpq).symm
  exact congrArg (fun φ => φ ≫ (StacksDraft.KFlat.modulePullback f).map
      (HomologicalComplex.ιMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ)
        p q n hpq))
    (comparisonAppIso_inv_eq f hδ (K.X p) (L.X q))

/-- **The comparison of total tensor complexes of [Stacks, Tag 079U] is the inverse tensorator
of the monoidal lift of `f^*` to complexes.** -/
theorem pullbackTensorComplexIsoOfIsIso_eq (hδ : IsComparisonTensorator f)
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexIsoOfIsIso f K L =
      (Functor.mapHomologicalComplexTensorator (StacksDraft.KFlat.modulePullback f) K L).symm :=
  Iso.ext ((Iso.inv_eq_inv _ _).mp (pullbackTensorComplexIsoOfIsIso_inv_eq f hδ K L))

/-- **The bifunctorial comparison of total tensor complexes of [Stacks, Tag 079U], at a pair of
complexes, is the tensorator of `f^*` on complexes.** -/
theorem pullbackTensorComplexNatIso_inv_app_eq (hδ : IsComparisonTensorator f)
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso f).inv.app (K, L) = μ (pullbackComplex f) K L :=
  pullbackTensorComplexIsoOfIsIso_inv_eq f hδ K L

/-! ### The unit comparison -/

/-- The hypothesis that the lax unit of the monoidal structure carried by `f^*` is the inverse of
the comparison `ν : f^*𝒪_Y ≅ 𝒪_X` of the structure sheaves. -/
abbrev IsComparisonUnit : Prop :=
  ε (StacksDraft.KFlat.modulePullback f) =
    (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).inv

/-- **The unit comparison of the monoidal lift of `f^*` to complexes is `ν` in degree zero.**
Both identifications of the degree-zero term of a single-degree complex are inserted, which is
the only shape the statement can take: the unit of the complexes is `𝒪[0]`, not `𝒪`. -/
theorem epsilon_pullbackComplex_f_zero (hε : IsComparisonUnit f) :
    (ε (pullbackComplex f)).f 0 ≫ (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))).hom ≫
        (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).inv := by
  refine (Functor.mapHomologicalComplexUnitIso_hom_f_zero
    (StacksDraft.KFlat.modulePullback f)).trans ?_
  exact congrArg (fun φ => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))).hom ≫ φ) hε

/-! ### The coherences of the comparison, free from the monoidal axioms -/

/-- **The right unit coherence of the comparison of total tensor complexes.**  With the unit
supplied by the complex-level unit comparison of `f^*`, the comparison
`Tot(f^*K ⊗_{𝒪_X} f^*𝒪_Y[0]) ⟶ f^*Tot(K ⊗_{𝒪_Y} 𝒪_Y[0])` is compatible with the right unitors
of the two categories of complexes.  This is the right unitality axiom of
`CategoryTheory.Functor.Monoidal` for the monoidal lift, read through the identification of the
comparison with the tensorator: no total complex is taken apart here. -/
theorem pullbackTensorComplexIsoOfIsIso_rightUnitor (hδ : IsComparisonTensorator f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (ρ_ ((pullbackComplex f).obj K)).hom =
      (pullbackComplex f).obj K ◁ ε (pullbackComplex f) ≫
        (pullbackTensorComplexIsoOfIsIso f K
            (𝟙_ (CochainComplex
              (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))).inv ≫
          (pullbackComplex f).map (ρ_ K).hom := by
  rw [pullbackTensorComplexIsoOfIsIso_inv_eq f hδ]
  exact Functor.mapHomologicalComplexTensorator_right_unitality
    (StacksDraft.KFlat.modulePullback f) K

/-- **The left unit coherence of the comparison of total tensor complexes**, obtained the same
way. -/
theorem pullbackTensorComplexIsoOfIsIso_leftUnitor (hδ : IsComparisonTensorator f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (λ_ ((pullbackComplex f).obj K)).hom =
      ε (pullbackComplex f) ▷ (pullbackComplex f).obj K ≫
        (pullbackTensorComplexIsoOfIsIso f
            (𝟙_ (CochainComplex
              (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)) K).inv ≫
          (pullbackComplex f).map (λ_ K).hom := by
  rw [pullbackTensorComplexIsoOfIsIso_inv_eq f hδ]
  exact Functor.mapHomologicalComplexTensorator_left_unitality
    (StacksDraft.KFlat.modulePullback f) K

end Monoidal

end Stacks.Cohomology.DerivedPullbackTensor

end
