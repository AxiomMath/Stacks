module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportZeroConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactMonoEpi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SurjectiveEtaleFaithful

/-!
# `H⁰_c` of a sheaf trivialized by a finite étale cover of an affine curve vanishes

Let `U` be a smooth curve over a finite field `k` with a compactification `j : U ⟶ Ū`, and let
`f : V ⟶ U` be a connected finite étale cover with `V` affine. If a sheaf `G` of `Λ`-modules on
`U_étale` becomes constant on `V`, then `H⁰_c(U_k̄, G) = 0`. Indeed `G ⟶ f_* f⁻¹ G` is injective
(`f⁻¹` is faithful, `f` being surjective), `H⁰_c(U_k̄, -)` is left exact, `H⁰_c(U_k̄, f_* -)` is
`H⁰_c(V_k̄, -)` computed on the smooth projective compactification `V̄` of `V` over `Ū`
(`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIntegralIso`), and `H⁰_c(V_k̄, M) = 0`
for a constant sheaf on the affine curve `V`
(`Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_isAffine`).

This is the non-projective assertion `H⁰_c(X_k̄, ℱ_ρ) = 0` of [Stacks, Tag 03VL] at a finite level,
granted a trivializing cover.

## Main results

* `Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_zero_of_cover`.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {U V : Scheme.{u}} (fU : U ⟶ Spec (.of k))
  [IsCurve k fU] [Smooth fU] [LocallyOfFiniteType fU] [QuasiCompact fU] [IsSeparated fU]
  (j : CompactificationOf (Over.mk fU)) (f : V ⟶ U) [IsFinite f] [Etale f] [ConnectedSpace V]
  [IsAffine V] (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
  (Λ : Type) [CommRing Λ]

/-- A sheaf placed in degree zero, pushed forward degreewise, is the single complex on the
pushforward. -/
def directImageSingleIso {X Y : Scheme.{u}} (g : X ⟶ Y) (A : EtaleModules.{u, 0} Λ X) :
    (etaleModuleDirectImage.{u, 0} Λ g).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj A, CochainComplex.plus_singleFunctor_obj A⟩ ≅
      ⟨(CochainComplex.singleFunctor _ 0).obj ((etaleModuleDirectImage.{u, 0} Λ g).obj A),
        CochainComplex.plus_singleFunctor_obj _⟩ :=
  ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex
    (etaleModuleDirectImage.{u, 0} Λ g) (ComplexShape.up ℤ) 0).app A)

omit [LocallyOfFiniteType fU] [QuasiCompact fU] [IsSeparated fU] [IsAlgClosed kbar] in
/-- **`H⁰_c(U_k̄, G) = 0`** for a sheaf `G` on a smooth curve `U` which becomes constant on a
connected finite étale cover `f : V ⟶ U` with `V` affine, given the smooth projective
compactification `V̄` of `V` over the compactification of `U`. -/
theorem isZero_compactSupportFrobeniusCohomologyGroup_zero_of_cover [PerfectField k]
    [LocallyOfFiniteType (f ≫ fU)] [QuasiCompact (f ≫ fU)] [IsSeparated (f ≫ fU)]
    (C : CoverCompactification k j.toBase j.immersion f) (G : EtaleModules.{u, 0} Λ U)
    (M : ModuleCat.{u + 1} Λ)
    (e : (etaleModuleInverseImage.{u, 0} Λ f).obj G ≅
      (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :
    IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ fU j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj G, CochainComplex.plus_singleFunctor_obj G⟩ 0) := by
  have hjU : j.immersion ≫ j.toBase = fU := Over.w j.obj.hom
  have : IsIntegral U := IsCurve.toIsVariety.toIsIntegral (k := k) (f := fU)
  have : Surjective f := by
    rw [surjective_iff]
    have : Nonempty V := ConnectedSpace.toNonempty
    exact Set.range_eq_univ.1 (IsClopen.eq_univ
      ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩ (Set.range_nonempty _))
  have : IsFinite C.fb := C.isFinite
  have : IsIntegralHom (show (C.compactification hjU).space ⟶ j.space from C.fb) :=
    (inferInstance : IsIntegralHom C.fb)
  -- `H⁰_c(U_k̄, f_* f⁻¹ G) = H⁰_c(V_k̄, M) = 0`
  let A := (etaleModuleInverseImage.{u, 0} Λ f).obj G
  have hV : IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ (f ≫ fU)
      (C.compactification hjU) kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj A, CochainComplex.plus_singleFunctor_obj A⟩ 0) :=
    (isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_isAffine hjU C kbar Λ M).of_iso
      ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso
        ((compactSupportFrobeniusFunctor.{u, 0} Λ (f ≫ fU) (C.compactification hjU) kbar).mapIso
          (ObjectProperty.isoMk _ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso e))))
  have hU : IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ fU j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj ((etaleModuleDirectImage.{u, 0} Λ f).obj A),
        CochainComplex.plus_singleFunctor_obj _⟩ 0) :=
    hV.of_iso ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((compactSupportFrobeniusCohomologyIntegralIso Λ fU j (f ≫ fU) (C.compactification hjU) f
        C.fb C.hq C.isPullback.flip kbar _) ≪≫
        (compactSupportFrobeniusFunctor.{u, 0} Λ fU j kbar).mapIso
          (directImageSingleIso Λ f A))).symm
  -- `G ⟶ f_* f⁻¹ G` is injective and `H⁰_c` is left exact
  have := faithful_etaleModuleInverseImage_of_surjective Λ f
  let η := (etaleModuleInverseImageAdj.{u, 0} Λ f).unit.app G
  let S := ShortComplex.mk η (cokernel.π η) (cokernel.condition η)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel η) inferInstance inferInstance
  have hS' := hS.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} Λ U)
    (ComplexShape.up ℤ) 0)
  have hneg : IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ fU j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj (cokernel η), CochainComplex.plus_singleFunctor_obj _⟩
        (-1)) := by
    have : CochainComplex.IsStrictlyGE ((CochainComplex.singleFunctor
        (EtaleModules.{u, 0} Λ U) 0).obj (cokernel η)) 0 := by
      show CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (cokernel η)) 0
      infer_instance
    have : (compactSupportFrobeniusCohomology.{u, 0} Λ fU j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj (cokernel η),
          CochainComplex.plus_singleFunctor_obj _⟩).IsGE 0 :=
      isGE_compactSupportFrobeniusFunctor_obj.{u, 0} Λ fU j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj (cokernel η),
          CochainComplex.plus_singleFunctor_obj _⟩ 0
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 (-1) (by omega)
  have hmono := mono_homology_compactSupportFrobeniusFunctor_map_f Λ fU j kbar hS'
    (CochainComplex.plus_singleFunctor_obj _) (CochainComplex.plus_singleFunctor_obj _)
    (CochainComplex.plus_singleFunctor_obj _) (-1) 0 (by omega) hneg
  exact @IsZero.of_mono _ _ _ _ _ _ hmono hU

end Stacks.EtaleCohomology

end
