module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFiniteTorRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

/-!
# `D_ctf` on Mathlib's small étale site is the category of Tag 03TQ

`Stacks.EtaleCohomology.IsCtf` defines `D_ctf(X_étale, Λ)` for sheaves of `Λ`-modules on Mathlib's
small étale site, for an arbitrary ring `Λ`, by representability by bounded complexes of
constructible flat sheaves after inverse image to quasi-compact and quasi-separated schemes. This
file shows that for a Noetherian commutative ring `Λ` and a quasi-compact and quasi-separated
scheme `X` it is the category `D_ctf(X_étale, Λ)` of Tag 03TQ, transported along the identification
`AlgebraicGeometry.SmallEtale.sheafEquiv` of the two presentations of the small étale site. This is
[Stacks, Tag 03TT] read on Mathlib's site.

## Main results

* `Stacks.EtaleCohomology.isRepresentedByConstructibleFlatEtaleComplex_iff`: condition (2) of
  Tag 03TT on Mathlib's site is condition (2) on the small étale site of Stacks 021B for the
  transported object.
* `Stacks.EtaleCohomology.isCtf_iff_exists_constructibleFiniteTor`: the two definitions of
  `D_ctf(X_étale, Λ)` agree on a quasi-compact and quasi-separated scheme.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r d

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

section Transport

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]

/-- The transport to the small étale site of Stacks 021B is an additive functor. -/
instance etaleModulesToSmallEtale_additive : (etaleModulesToSmallEtale B X Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Condition (2) of Tag 03TT on the two presentations of the small étale site.** An object of
`D(X_étale, Λ)` on Mathlib's small étale site is represented by a bounded complex of constructible
flat sheaves exactly when its transport to the small étale site of Stacks 021B is. -/
public theorem isRepresentedByConstructibleFlatEtaleComplex_iff
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)) :
    IsRepresentedByConstructibleFlatEtaleComplex B X Λ K ↔
      IsRepresentedByConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ
        ((etaleModulesToSmallEtale B X Λ).mapDerivedCategory.obj K) := by
  let ε := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)
  let ρ := etaleModulesToSmallEtale B X Λ
  let σ := ε.functor
  have : σ.Additive := Functor.additive_of_preserves_binary_products _
  constructor
  · rintro ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩
    exact ⟨(ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C, a, b,
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff C ρ a).2 ha,
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff C ρ b).2 hb, hC,
      ⟨(ρ.mapDerivedCategoryFactors.app C).symm ≪≫ ρ.mapDerivedCategory.mapIso e⟩⟩
  · rintro ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩
    let C₀ := DerivedCategory.Q.objPreimage K
    let e₀ : DerivedCategory.Q.obj C₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
    let eC₀ : (σ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C₀) ≅ C₀ :=
      HomologicalComplex.Hom.isoOfComponents (fun i => ε.counitIso.app (C₀.X i))
        (fun i j _ => (ε.counitIso.hom.naturality (C₀.d i j)).symm)
    refine ⟨(σ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C, a, b,
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff C σ a).2 ha,
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff C σ b).2 hb,
      fun i => isConstructibleFlatModuleSheaf_congr B X Λ (ε.unitIso.app (C.X i)) (hC i), ⟨?_⟩⟩
    exact (σ.mapDerivedCategoryFactors.app C).symm ≪≫ σ.mapDerivedCategory.mapIso e ≪≫
      σ.mapDerivedCategory.mapIso (ρ.mapDerivedCategory.mapIso e₀.symm ≪≫
        ρ.mapDerivedCategoryFactors.app C₀) ≪≫
      σ.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso eC₀ ≪≫ e₀

end Transport

section Agreement

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

/-- **The two definitions of `D_ctf(X_étale, Λ)` agree.** Let `Λ` be a Noetherian ring and `X` a
quasi-compact and quasi-separated scheme. An object `K` of the derived category of sheaves of
`Λ`-modules on Mathlib's small étale site lies in `D_ctf(X_étale, Λ)` in the sense of
`Stacks.EtaleCohomology.IsCtf` exactly when its transport to the small étale site of Stacks 021B
lies in the category of Tag 03TQ, for any choice `T` of derived tensor products on the slices. -/
public theorem isCtf_iff_exists_constructibleFiniteTor [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj]
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)) :
    IsCtf B X Λ K ↔
      ∃ L : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T,
        Nonempty (L.obj.obj ≅ (etaleModulesToSmallEtale B X Λ).mapDerivedCategory.obj K) :=
  (isCtf_iff_of_qcqs B Λ K).trans ((isRepresentedByConstructibleFlatEtaleComplex_iff B X Λ K).trans
    (exists_constructibleFiniteTor_iff_isRepresentedByConstructibleFlatComplex B X Λ T _).symm)

end Agreement

end Stacks.EtaleCohomology
