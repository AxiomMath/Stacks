module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# The derived projection-formula map along a composite

Let `j : X'' ⟶ X'` and `i : X' ⟶ X` be morphisms of ringed spaces, `E ∈ D(𝒪_{X''})` and
`K ∈ D(𝒪_X)`. The projection-formula map of [Stacks, Tag 0B53] along `j ≫ i`,

`R(j ≫ i)_*E ⊗^L K ⟶ R(j ≫ i)_*(E ⊗^L L(j ≫ i)^*K)`,

is the one along `i` at `(Rj_*E, K)` followed by `Ri_*` of the one along `j` at `(E, Li^*K)`, read
through the composition isomorphisms `Rj_* ⋙ Ri_* ≅ R(j ≫ i)_*` and `Li^* ⋙ Lj^* ≅ L(j ≫ i)^*`.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_comp`: the factorization at
  `j ≫ i`.
* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_comp_of_comp_eq`: the same,
  for a morphism `k` given together with a proof of `j ≫ i = k`.

## Implementation notes

The composition isomorphisms are
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` (the uniqueness
isomorphism of right adjoints) and
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` (Stacks 0D5S). The statement
is the abstract `CategoryTheory.adjunctionTensorMap_comp_ofNatIso` at the three derived
adjunctions, whose two inputs are the identification of the adjunction along `j ≫ i` with the
composite adjunction, `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp`,
and the compatibility of the comparison of [Stacks, Tag 079U] with composition,
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp`.

Like the projection-formula map itself, everything here lives at the standard model
`HasDerivedCategory.standard`, installed for each declaration only. No tensor factors are swapped:
the pushforward always sits in the left factor.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

variable {X'' X' X : RingedSpace.{u, u}} (j : X'' ⟶ X') (i : X' ⟶ X)
  [HasSheafify (Opens.grothendieckTopology X''.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X''.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The projection-formula map along a composite.** For morphisms of ringed spaces
`j : X'' ⟶ X'` and `i : X' ⟶ X`, `E ∈ D(𝒪_{X''})` and `K ∈ D(𝒪_X)`, the projection-formula map of
[Stacks, Tag 0B53] along `i` at `(Rj_*E, K)`, followed by `Ri_*` of the one along `j` at
`(E, Li^*K)`, by the composition isomorphism `Ri_*Rj_* ≅ R(j ≫ i)_*` and by
`R(j ≫ i)_*` of the composition isomorphism `Lj^*Li^*K ≅ L(j ≫ i)^*K` in the second tensor factor,
is the composition isomorphism `Ri_*Rj_*E ≅ R(j ≫ i)_*E` in the first tensor factor followed by
the projection-formula map along `j ≫ i` at `(E, K)`.

The composition isomorphisms are `derivedPushforwardCompIso j i` and
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical j i`. Stated at the standard
model `HasDerivedCategory.standard`, the model of `projectionFormulaMap`, installed for this
declaration only. -/
theorem projectionFormulaMap_comp
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'')))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    projectionFormulaMap i ((derivedPushforward j).obj E) K ≫
        (derivedPushforward i).map (projectionFormulaMap j E ((derivedPullback i).obj K)) ≫
        (derivedPushforwardCompIso j i).hom.app _ ≫
        (derivedPushforward (j ≫ i)).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X''.sheaf).obj E).map
            ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical j i).hom.app K)) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          ((derivedPushforwardCompIso j i).hom.app E)).app K ≫
        projectionFormulaMap (j ≫ i) E K := by
  have h := adjunctionTensorMap_comp_ofNatIso (derivedAdjunction i) (derivedAdjunction j)
    (derivedAdjunction (j ≫ i))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical j i)
    (derivedPushforwardCompIso j i)
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X''.sheaf))
    (pullbackTensorComparison i) (pullbackTensorComparison j) (pullbackTensorComparison (j ≫ i))
    (derivedAdjunction_comp j i)
    (fun P Q => NatTrans.congr_app
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp j i) (P, Q)) E K
  exact (congrArg (fun t => projectionFormulaMap i ((derivedPushforward j).obj E) K ≫
      (derivedPushforward i).map (projectionFormulaMap j E ((derivedPullback i).obj K)) ≫
      (derivedPushforwardCompIso j i).hom.app _ ≫ (derivedPushforward (j ≫ i)).map t)
        (uncurry_map_id_left _ _ _).symm).trans
    (h.trans (congrArg (· ≫ projectionFormulaMap (j ≫ i) E K) (uncurry_map_id_right _ _ _)))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The projection-formula map along a composite `k = j ≫ i`.** `projectionFormulaMap_comp` for a
morphism `k` given together with a proof of `j ≫ i = k`: the composition isomorphisms
`derivedPushforwardCompIso j i` and
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical j i` are transported along it
by `eqToIso`. Stated at the standard model `HasDerivedCategory.standard`, the model of
`projectionFormulaMap`, installed for this declaration only. -/
theorem projectionFormulaMap_comp_of_comp_eq (k : X'' ⟶ X) (hk : j ≫ i = k)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'')))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    projectionFormulaMap i ((derivedPushforward j).obj E) K ≫
        (derivedPushforward i).map (projectionFormulaMap j E ((derivedPullback i).obj K)) ≫
        (derivedPushforwardCompIso j i ≪≫
          eqToIso (congrArg (fun h : X'' ⟶ X => derivedPushforward h) hk)).hom.app _ ≫
        (derivedPushforward k).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X''.sheaf).obj E).map
            ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical j i ≪≫
              eqToIso (congrArg (fun h : X'' ⟶ X => derivedPullback h) hk)).hom.app K)) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          ((derivedPushforwardCompIso j i ≪≫
            eqToIso (congrArg (fun h : X'' ⟶ X => derivedPushforward h) hk)).hom.app E)).app K ≫
        projectionFormulaMap k E K := by
  subst hk
  simp only [eqToIso_refl, Iso.trans_refl]
  exact projectionFormulaMap_comp j i E K

end Stacks.Cohomology.DerivedProjectionFormula

end
