module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionTensorRowComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnitOfSize
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize

/-!
# Quasi-coherent cohomology descends along a first-order thickening

Let `Z ⊂ Y` be a first-order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ Y`, and let `K` be an object of `D(𝒪_Y)` whose derived pullback `Li^*K` lies in
`D_QCoh(𝒪_Z)`. Then `K` lies in `D_QCoh(𝒪_Y)`.

This is the first paragraph of the proof of Stacks 0DL3, for a first-order thickening; the
reduction from a finite-order thickening is
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/DerivedQuasicoherentFiniteOrder.lean`.

## The argument

It is the source's. Represent `K` by a K-flat complex `P` with flat terms (Stacks 06YS), so that
`Li^*K` is represented by `i^*P` (Stacks 06YY, 0G7E). Tensor the short exact sequence

`0 ⟶ 𝓘 ⟶ 𝒪_Y ⟶ i_*𝒪_Z ⟶ 0`

of Stacks 09RP in degree zero (`AlgebraicGeometry.Space.definingIdealShortComplex_shortExact`)
termwise with `P`; the terms of `P` are flat, so the result is a short exact sequence of complexes
and hence a distinguished triangle in `D(𝒪_Y)`. Its middle vertex is `P ⊗ 𝒪_Y = P`. Both outer
vertices are `P ⊗ i_*G` with `G` a quasi-coherent `𝒪_Z`-module: for the right one `G = 𝒪_Z`, and
for the left one `𝓘 ≅ i_*𝒞_{Z/Y}` because `𝓘² = 0`
(`AlgebraicGeometry.Space.firstOrderConormalModuleIso`), with `𝒞_{Z/Y} = i^*𝓘` quasi-coherent.
By the projection formula of Stacks 04G0 read degreewise,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_rowComplex_modulePushforward`, they have
quasi-coherent cohomology, so the middle vertex does too, `D_QCoh` being a triangulated
subcategory.

## Main results

* `Space.qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFirstOrderThickening`:
  for a first-order thickening `Z ⊂ Y`, if `Li^*K` lies in `D_QCoh(𝒪_Z)` then `K` lies in
  `D_QCoh(𝒪_Y)`.

## References

* [Stacks Project, Tag 0DL3](https://stacks.math.columbia.edu/tag/0DL3)
* [Stacks Project, Tag 0DK5](https://stacks.math.columbia.edu/tag/0DK5)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Quasi-coherent cohomology descends along a first-order thickening.** Let `Z ⊂ Y` be a
first-order thickening of algebraic spaces with inclusion `i`, and let `K ∈ D(𝒪_Y)`. If `Li^*K`
has quasi-coherent cohomology sheaves, so does `K`. -/
theorem qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFirstOrderThickening
    {Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS Y.1)
    (hZ : IsFirstOrderThickening B S hS Y Z.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK :
      haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
        (subspaceInclusion B S hS Y Z)
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Z.1.toFunctor Z.2.1).O)))
        ((smallEtaleDerivedModulePullback B S hS (subspaceInclusion B S hS Y Z)).obj K)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (subspaceInclusion B S hS Y Z)
  have := pullbackModules_smallEtaleRingedToposHom_additive B S hS (subspaceInclusion B S hS Y Z)
  have hi : IsClosedImmersion B S hS (subspaceInclusion B S hS Y Z).hom := Z.2.2
  obtain ⟨Kh, hPK, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage K))
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective Kh
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) s hs
  let eK : DerivedCategory.Q.obj P ≅ K :=
    ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫ asIso (DerivedCategory.Qh.map s) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _ ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hpb : ∀ n : ℤ, ((((smallEtaleRingedToposHom B S hS
      (subspaceInclusion B S hS Y Z)).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology n).IsQuasicoherentOnSite := fun n =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso
          ((smallEtaleDerivedModulePullback B S hS (subspaceInclusion B S hS Y Z)).mapIso eK.symm ≪≫
            derivedPullbackObjIsoOfIsKFlat B S hS (subspaceInclusion B S hS Y Z) P hPK) ≪≫
        (DerivedCategory.homologyFunctorFactors _ n).app _) (hK n)
  have hpk := (smallEtaleModuleKFlat_pullbackMapHomotopy B S hS
    (subspaceInclusion B S hS Y Z) _ hPK).1
  have key : ∀ (G : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1), G.IsQuasicoherentOnSite →
      ∀ (M : Modules.{u, u} B S hS Y.1 Y.2),
        (M ≅ (modulePushforward B S hS (subspaceInclusion B S hS Y Z)).obj G) →
        QcohDerived B S hS Y (DerivedCategory.Q.obj
          (@CochainComplex.KFlatBifunctor.rowComplex _ _ _ _ _ _ _ _
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (smallEtaleRingedSite B S hS Y.1 Y.2).O)
            (Stacks.SheafOfModules.Tensor.sheafTensor_additive _) P M)) := by
    intro G hG M e
    rw [qcohDerived_Q_obj_iff]
    intro n
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
        (HomologicalComplex.Hom.isoOfComponents
          (fun n => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (P.X n)).mapIso e)
          (fun n m _ => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).map (P.d n m)).naturality e.hom)).symm)
      (isQuasicoherentOnSite_homology_rowComplex_modulePushforward B S hS
        (subspaceInclusion B S hS Y Z) hi P hpk hpb G hG n)
  have hadd : ∀ n : ℤ,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (P.X n)).Additive := fun n =>
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive _ _
  let Sm := definingIdealShortComplex B S hS Y Z
  have hSm : Sm.ShortExact := definingIdealShortComplex_shortExact B S hS Y Z
  let Sc : ShortComplex (CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :=
    ShortComplex.mk
      (@CochainComplex.KFlatBifunctor.rowComplexMapRight _ _ _ _ _ _ _ _
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)
        (Stacks.SheafOfModules.Tensor.sheafTensor_additive _) P _ _ Sm.f)
      (@CochainComplex.KFlatBifunctor.rowComplexMapRight _ _ _ _ _ _ _ _
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)
        (Stacks.SheafOfModules.Tensor.sheafTensor_additive _) P _ _ Sm.g) (by
      refine HomologicalComplex.hom_ext _ _ fun n => ?_
      change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (P.X n)).map Sm.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (P.X n)).map Sm.g = 0
      rw [← Functor.map_comp, Sm.zero, Functor.map_zero])
  have hSc : Sc.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
    have hex : exactFunctor (Modules.{u, u} B S hS Y.1 Y.2) (Modules.{u, u} B S hS Y.1 Y.2)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).flip.obj (P.X n)) := hPK.2 n
    obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).1 hex
    let e := (Stacks.SheafOfModules.Tensor.sheafTensorBraiding
      (smallEtaleRingedSite B S hS Y.1 Y.2).O).app (P.X n)
    have : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (P.X n)) :=
      @preservesFiniteLimits_of_natIso _ _ _ _ _ _ e.symm hlim
    have : PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (P.X n)) :=
      @preservesFiniteColimits_of_natIso _ _ _ _ _ _ e.symm hcolim
    exact hSm.map_of_exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj (P.X n))
  have hT := DerivedCategory.triangleOfSES_distinguished hSc
  have h₂ := (QcohDerived B S hS Y).ext_of_isTriangulatedClosed₂ _ hT
    (key _ (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (subspaceInclusion B S hS Y Z) _ (isQuasicoherentOnSite_definingIdealSheaf B S hS Y Z))
      _ (firstOrderConormalModuleIso B S hS Z hZ))
    (key _ (SheafOfModules.isQuasicoherentOnSite_unit _) _ (Iso.refl _))
  have h₂' := (qcohDerived_Q_obj_iff B S hS _).1 h₂
  intro n
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
        (HomologicalComplex.Hom.isoOfComponents
          (fun n => (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).app (P.X n))
          (fun n m _ => ((Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).hom.naturality (P.d n m)).symm)) ≪≫
      ((DerivedCategory.homologyFunctorFactors _ n).app P).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso eK) (h₂' n)

end AlgebraicGeometry.Space
