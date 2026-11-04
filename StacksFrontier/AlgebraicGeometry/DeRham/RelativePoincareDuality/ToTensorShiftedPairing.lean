module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.ShiftedPairingTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftFlipApp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwoField
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The canonical map to the total tensor complex and shifted pairings

Let `Z` be a ringed space. For cochain complexes `K`, `L` of `𝒪_Z`-modules the canonical map
`QK ⊗^L QL ⟶ Q(Tot(K ⊗ L))` of [Stacks, Tag 06YU] commutes with the shifts in both variables
(`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorCommShift₂`). This file turns that
compatibility into an equation of pairings: for a map of complexes `g : Tot(K ⊗ L) ⟶ M`, the
shift (`CategoryTheory.Functor.shiftedPairing`) of the pairing `QK ⊗^L QL ⟶ QM` it induces is,
through `Q(K[n]) ≅ (QK)[n]` and `Q(L[m]) ≅ (QL)[m]`, the pairing induced by the shift of `g` for
the total tensor complex. This is how the proof of [Stacks, Tag 0G8K] computes the shifts of
the pairings of the stupid truncations of the de Rham complex.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.shiftedPairing_toTensor_comp`

## Implementation notes

The derived categories are taken at the standard model (`Stacks.StandardDerivedModel`), where the
compatibility of the canonical map with the shifts is proved. The shifts of the derived tensor
product are those of the field `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂`
of the canonical derived tensor product, which is the transported datum
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int` by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The shift of a pairing for the restriction of `- ⊗^L -` to cochain complexes is the shift for
`- ⊗^L -` preceded by `Q(K[n]) ≅ (QK)[n]` and `Q(L[m]) ≅ (QL)[m]`. -/
theorem shiftedPairing_curriedComplexesDerivedTensor {K L : CochainComplex (ModulesOn Z) ℤ}
    {M : DerivedCategory (ModulesOn Z)}
    (φ : ((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).obj
      (DerivedCategory.Q.obj L) ⟶ M) (n m : ℤ) (h : n + m = 0) :
    letI := derivedTensorCommShift₂Int Z
    letI := curriedComplexesDerivedTensor_commShift₂Int Z
    (curriedComplexesDerivedTensor Z).shiftedPairing φ n m h =
      ((derivedTensorProductFunctor Z.sheaf).map
          ((DerivedCategory.Q.commShiftIso n).hom.app K)).app (DerivedCategory.Q.obj (L⟦m⟧)) ≫
        ((derivedTensorProductFunctor Z.sheaf).obj ((DerivedCategory.Q.obj K)⟦n⟧)).map
          ((DerivedCategory.Q.commShiftIso m).hom.app L) ≫
        (derivedTensorProductFunctor Z.sheaf).shiftedPairing φ n m h :=
  let := derivedTensorCommShift₂Int Z
  (Functor.shiftedPairing_precomp₁ DerivedCategory.Q
      (derivedTensorProductFunctor Z.sheaf ⋙ (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q)
      φ n m h).trans
    (congrArg (_ ≫ ·) (Functor.shiftedPairing_precomp₂ DerivedCategory.Q _ φ n m h))

/-- The shift of a pairing for the curried source of `derivedToTensorNatTrans` is the shift for
the restriction of `- ⊗^L -` to cochain complexes. -/
theorem shiftedPairing_curryComplexesDerivedTensor {K L : CochainComplex (ModulesOn Z) ℤ}
    {M : DerivedCategory (ModulesOn Z)}
    (φ : ((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).obj
      (DerivedCategory.Q.obj L) ⟶ M) (n m : ℤ) (h : n + m = 0) :
    letI := curriedComplexesDerivedTensor_commShift₂Int Z
    letI := curryComplexesDerivedTensor_commShift₂Int Z
    (Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
      (derivedTensorProductFunctor Z.sheaf))).shiftedPairing φ n m h =
      (curriedComplexesDerivedTensor Z).shiftedPairing φ n m h := by
  let := curriedComplexesDerivedTensor_commShift₂Int Z
  let := curryComplexesDerivedTensor_commShift₂Int Z
  have := Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesDerivedTensorIso Z)
  have e := Functor.shiftedPairing_natTrans (curryComplexesDerivedTensorIso Z).hom φ n m h
  have e₁ : ((curryComplexesDerivedTensorIso Z).hom.app K).app L = 𝟙 _ := rfl
  have e₂ : ((curryComplexesDerivedTensorIso Z).hom.app (K⟦n⟧)).app (L⟦m⟧) = 𝟙 _ := rfl
  rw [e₁, e₂] at e
  exact (Category.id_comp _).symm.trans (e.symm.trans
    (congrArg (fun x => (curriedComplexesDerivedTensor Z).shiftedPairing x n m h)
      (Category.id_comp φ)))

/-- The shift of the pairing `Q(g)` for the curried target of `derivedToTensorNatTrans` is `Q` of
the shift of `g` for the total tensor complex. -/
theorem shiftedPairing_curryComplexesTotal_map {K L M : CochainComplex (ModulesOn Z) ℤ}
    (g : ((tensorComplexBifunctorOn Z).obj K).obj L ⟶ M) (n m : ℤ) (h : n + m = 0) :
    letI := curryComplexesTotal_commShift₂Int Z
    (Functor.curry.obj
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) ⋙
        DerivedCategory.Q)).shiftedPairing (DerivedCategory.Q.map g) n m h =
      DerivedCategory.Q.map ((tensorComplexBifunctorOn Z).shiftedPairing g n m h) := by
  let := curryComplexesTotal_commShift₂Int Z
  refine (Functor.shiftedPairing_curryObjUncurryObjComp (tensorComplexBifunctorOn Z)
    DerivedCategory.Q (DerivedCategory.Q.map g) n m h).trans ?_
  exact Functor.shiftedPairing_postcompInt (tensorComplexBifunctorOn Z) DerivedCategory.Q g n m h

/-- The compatibility of `derivedToTensorNatTrans` with the shifts, on a pairing `Q(g)`. -/
theorem shiftedPairing_curryComplexesDerivedTensor_toTensor
    {K L M : CochainComplex (ModulesOn Z) ℤ}
    (g : ((tensorComplexBifunctorOn Z).obj K).obj L ⟶ M) (n m : ℤ) (h : n + m = 0) :
    letI := curryComplexesDerivedTensor_commShift₂Int Z
    (Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
      (derivedTensorProductFunctor Z.sheaf))).shiftedPairing
        ((canonicalDerivedTensorProduct Z.sheaf).toTensor K L ≫ DerivedCategory.Q.map g) n m h =
      (canonicalDerivedTensorProduct Z.sheaf).toTensor (K⟦n⟧) (L⟦m⟧) ≫
        DerivedCategory.Q.map ((tensorComplexBifunctorOn Z).shiftedPairing g n m h) := by
  let := curryComplexesDerivedTensor_commShift₂Int Z
  let := curryComplexesTotal_commShift₂Int Z
  have : NatTrans.CommShift₂Int (Functor.curry.map (derivedToTensorNatTrans Z)) :=
    derivedToTensorCommShift₂ Z
  exact (Functor.shiftedPairing_natTrans (Functor.curry.map (derivedToTensorNatTrans Z))
    (DerivedCategory.Q.map g) n m h).trans
    (congrArg (_ ≫ ·) (shiftedPairing_curryComplexesTotal_map Z g n m h))

/-- **The shift of the pairing induced by a map of complexes `g : Tot(K ⊗ L) ⟶ M` is induced by
the shift of `g`**: through `Q(K[n]) ≅ (QK)[n]` and `Q(L[m]) ≅ (QL)[m]`, the shift
`(QK)[n] ⊗^L (QL)[m] ⟶ QM` of the pairing `QK ⊗^L QL ⟶ Q(Tot(K ⊗ L)) ⟶ QM` is the pairing
`Q(K[n]) ⊗^L Q(L[m]) ⟶ Q(Tot(K[n] ⊗ L[m])) ⟶ QM` of the shift of `g` for the total tensor
complex. This is the compatibility of the canonical map of [Stacks, Tag 06YU] with the shifts,
`derivedToTensorCommShift₂`, read on pairings. -/
theorem shiftedPairing_toTensor_comp {K L M : CochainComplex (ModulesOn Z) ℤ}
    (g : ((tensorComplexBifunctorOn Z).obj K).obj L ⟶ M) (n m : ℤ) (h : n + m = 0) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    ((derivedTensorProductFunctor Z.sheaf).map
        ((DerivedCategory.Q.commShiftIso n).hom.app K)).app (DerivedCategory.Q.obj (L⟦m⟧)) ≫
      ((derivedTensorProductFunctor Z.sheaf).obj ((DerivedCategory.Q.obj K)⟦n⟧)).map
        ((DerivedCategory.Q.commShiftIso m).hom.app L) ≫
      (derivedTensorProductFunctor Z.sheaf).shiftedPairing
        ((canonicalDerivedTensorProduct Z.sheaf).toTensor K L ≫ DerivedCategory.Q.map g) n m h =
    (canonicalDerivedTensorProduct Z.sheaf).toTensor (K⟦n⟧) (L⟦m⟧) ≫
      DerivedCategory.Q.map ((tensorComplexBifunctorOn Z).shiftedPairing g n m h) := by
  have key : ∀ d : (derivedTensorProductFunctor Z.sheaf).CommShift₂Int,
      d = Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int Z.sheaf →
      let := d
      ((derivedTensorProductFunctor Z.sheaf).map
          ((DerivedCategory.Q.commShiftIso n).hom.app K)).app (DerivedCategory.Q.obj (L⟦m⟧)) ≫
        ((derivedTensorProductFunctor Z.sheaf).obj ((DerivedCategory.Q.obj K)⟦n⟧)).map
          ((DerivedCategory.Q.commShiftIso m).hom.app L) ≫
        (derivedTensorProductFunctor Z.sheaf).shiftedPairing
          ((canonicalDerivedTensorProduct Z.sheaf).toTensor K L ≫ DerivedCategory.Q.map g) n m h =
      (canonicalDerivedTensorProduct Z.sheaf).toTensor (K⟦n⟧) (L⟦m⟧) ≫
        DerivedCategory.Q.map ((tensorComplexBifunctorOn Z).shiftedPairing g n m h) := by
    rintro _ rfl
    exact (shiftedPairing_curriedComplexesDerivedTensor Z _ n m h).symm.trans
      ((shiftedPairing_curryComplexesDerivedTensor Z _ n m h).symm.trans
        (shiftedPairing_curryComplexesDerivedTensor_toTensor Z g n m h))
  exact key _ (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq
    Z.sheaf)

end Stacks.Cohomology.DerivedPullbackTensor
