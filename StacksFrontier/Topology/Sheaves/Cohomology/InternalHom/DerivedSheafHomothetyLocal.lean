module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLocality.InvertibilityOnACovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyTranspose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLocality.InvertibleRestriction
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomCounitTransport

/-!
# The homothety is an isomorphism as soon as it is so locally

Let `(T, 𝒪_T)` be a ringed space and `K` an object of `D(𝒪_T)`. If `T` is covered by opens `V`
over each of which the derived endomorphisms `R𝓗om(K|_V, K|_V)` are isomorphic, as an object, to
the structure sheaf in degree zero, then the homothety `𝒪_T ⟶ R𝓗om(K, K)` is an isomorphism.

## Main results

* `Stacks.SheafOfModules.isIso_restrictD_map_derivedSheafHomothety_of_iso_unit`: the restriction
  of the homothety to an open on which the derived endomorphisms are the structure sheaf is an
  isomorphism.
* `Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_iso_unit`: the homothety is an
  isomorphism if the derived endomorphisms are locally the structure sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.SheafOfModules

variable {T : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} T)
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]
  [∀ V : Opens T, HasSheafify ((Opens.grothendieckTopology T).over V) AddCommGrpCat.{u}]
  [∀ V : Opens T, ((Opens.grothendieckTopology T).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens T, (Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over V).O).Additive]
  [∀ V : Opens T, ∀ M,
    ((Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over V).O).obj M).Additive]
  [∀ V : Opens T, ∀ (K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules
      ((ringedSite Rc).over V).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Tensor.sheafTensor.{u, u, u, u, u} ((ringedSite Rc).over V).O) (ComplexShape.up ℤ)]

/-- Let `V ⊆ T` be an open such that `R𝓗om(K|_V, K|_V)` on the slice site over `V` is
isomorphic to the structure sheaf in degree zero. Then the restriction to `V` of the homothety
`𝒪_T ⟶ R𝓗om(K, K)` is an isomorphism. -/
theorem isIso_restrictD_map_derivedSheafHomothety_of_iso_unit
    (K : DerivedCategory (StructureSheafModules Rc)) (V : Opens T)
    (ψ : ((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over V)).obj
          (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) V).obj K))).obj
        ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) V).obj K) ≅
      (DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules
          ((ringedSite Rc).O.over V)) 0).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, u, u} ((ringedSite Rc).O.over V)))) :
    IsIso ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) V).map
      (derivedSheafHomothety Rc K)) := by
  have ha' := Eq.mp (congrArg IsIso (RingedSite.derivedCurryHomEquiv_apply (ringedSite Rc) _ K K
    (derivedSheafHomothety Rc K))) (isIso_derivedCurryHomEquiv_derivedSheafHomothety Rc K)
  exact Stacks.Cohomology.SliceDerivedSheafHom.isIso_restrictD_map_of_isIso_evaluation
    (ringedSite Rc) V K _ ha'
    (fun a b => @MonoidalCategory.comp_comm_tensorUnit _ _ (RingedSite.derivedTensorMonoidal
      ((ringedSite Rc).over V)) a b)
    (Stacks.Cohomology.SliceInvertible.derivedRestrictionUnitIso (ringedSite Rc) V) ψ

/-- Let `Y` be a family of opens covering `T` such that over each `Y i` the derived
endomorphisms `R𝓗om(K|_{Y i}, K|_{Y i})` are isomorphic to the structure sheaf in degree zero.
Then the homothety `𝒪_T ⟶ R𝓗om(K, K)` is an isomorphism. -/
theorem isIso_derivedSheafHomothety_of_iso_unit
    (K : DerivedCategory (StructureSheafModules Rc))
    {ι : Type*} {Y : ι → Opens T} (hY : (Opens.grothendieckTopology T).CoversTop Y)
    (ψ : ∀ i, Nonempty (((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over (Y i))).obj
          (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) (Y i)).obj K))).obj
        ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite Rc) (Y i)).obj K) ≅
      (DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules
          ((ringedSite Rc).O.over (Y i))) 0).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf.{u, u, u}
          ((ringedSite Rc).O.over (Y i)))))) :
    IsIso (derivedSheafHomothety Rc K) :=
  Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor (J := (ringedSite Rc).J) hY _
    fun i => isIso_restrictD_map_derivedSheafHomothety_of_iso_unit Rc K (Y i) (ψ i).some

end Stacks.SheafOfModules

end
