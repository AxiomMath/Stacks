module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorProjection

/-!
# Naturality of the top-degree tensor identification (draft)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open DerivedCategory CategoryTheory.Pretriangulated

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

/-- The comparison `Lf^*(M[d]) ⟶ (f^*M)[d]` is natural in `M`. -/
theorem derivedToOrdinaryPullbackSingle_naturality {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {M M' : SheafOfModules.{u} (structureSheafRing Y)} (g : M ⟶ M') (d : ℤ) :
    (derivedPullback f).map ((singleFunctor _ d).map g) ≫ derivedToOrdinaryPullbackSingle f M' d =
      derivedToOrdinaryPullbackSingle f M d ≫
        (singleFunctor _ d).map ((RingedSpaceModuleAdjunction.modulePullback f).map g) := by
  have h1 := (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).hom.naturality g
  have h2 := (derivedPullbackComparison f).naturality
    ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map g)
  have h3 := ((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategorySingleFunctor
    d).hom.naturality g
  have h4 := (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d).inv.naturality
    ((RingedSpaceModuleAdjunction.modulePullback f).map g)
  simp only [Functor.comp_map] at h1 h2 h3 h4
  simp only [derivedToOrdinaryPullbackSingle, Category.assoc]
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, reassoc_of% h2,
    ← Functor.map_comp_assoc Qh, h3, Functor.map_comp_assoc, h4]


/-- The identification `τ^{≥ d} K ≅ (H^d K)[-d]` for `K` living in degrees `≤ d` is natural. -/
theorem truncGEIsoSingleHomology_hom_naturality {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K K' : DerivedCategory C} (α : K ⟶ K') (d : ℤ)
    (hK : TStructure.t.IsLE K d) (hK' : TStructure.t.IsLE K' d) :
    (TStructure.t.truncGE d).map α ≫ (truncGEIsoSingleHomology K' d hK').hom =
      (truncGEIsoSingleHomology K d hK).hom ≫
        (singleFunctor C d).map ((homologyFunctor C d).map α) := by
  have : IsIso ((TStructure.t.truncLTι (d + 1)).app K) :=
    (TStructure.t.isLE_iff_isIso_truncLTι_app d (d + 1) rfl K).1 hK
  have : IsIso ((TStructure.t.truncLTι (d + 1)).app K') :=
    (TStructure.t.isLE_iff_isIso_truncLTι_app d (d + 1) rfl K').1 hK'
  have hι : inv ((TStructure.t.truncLTι (d + 1)).app K) ≫ (TStructure.t.truncLT (d + 1)).map α =
      α ≫ inv ((TStructure.t.truncLTι (d + 1)).app K') := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact ((TStructure.t.truncLTι (d + 1)).naturality α)
  have hφ := (truncGELTIsoHomologyFunctorCompSingleFunctor (C := C) d).hom.naturality α
  simp only [truncGEIsoSingleHomology, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    asIso_inv, Iso.app_hom, Functor.comp_map] at hφ ⊢
  rw [← Category.assoc, ← Functor.map_comp, ← hι, Functor.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg
    (fun x => (TStructure.t.truncGE d).map (inv ((TStructure.t.truncLTι (d + 1)).app K)) ≫ x) hφ

/-- `homologySingleIso` is natural. -/
theorem homologySingleIso_hom_naturality {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {N N' : C} (β : N ⟶ N') (d : ℤ) :
    (homologyFunctor C d).map ((singleFunctor C d).map β) ≫ (homologySingleIso N' d).hom =
      (homologySingleIso N d).hom ≫ β := by
  have h1 := homologyFunctorFactors_hom_naturality ((CochainComplex.singleFunctor C d).map β) d
  have h2 := HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (ComplexShape.up ℤ) d β
  exact Stacks.DegreeZeroTensor.two_sq _ _ _ _ _ _ _ h1 h2

/-- **The identification `H^d(Lf^* K) ≅ f^* H^d(K)` is natural in `K`**, for `K` living in degrees
`≤ d`. -/
theorem derivedPullbackTopDegreeIsoPullback_hom_naturality {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (α : K ⟶ K') (d : ℤ)
    (hK : TStructure.t.IsLE K d) (hK' : TStructure.t.IsLE K' d) :
    (homologyFunctor _ d).map ((derivedPullback f).map α) ≫
        (derivedPullbackTopDegreeIsoPullback f K' d hK').hom =
      (derivedPullbackTopDegreeIsoPullback f K d hK).hom ≫
        (RingedSpaceModuleAdjunction.modulePullback f).map ((homologyFunctor _ d).map α) := by
  let H := homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d
  let L := derivedPullback f
  have h1 : H.map (L.map α) ≫ H.map (L.map ((TStructure.t.truncGEπ d).app K')) =
      H.map (L.map ((TStructure.t.truncGEπ d).app K)) ≫
        H.map (L.map ((TStructure.t.truncGE d).map α)) :=
    Stacks.DegreeZeroTensor.map_sq (L ⋙ H) _ _ _ _ ((TStructure.t.truncGEπ d).naturality α)
  have h2 := Stacks.DegreeZeroTensor.map_sq (L ⋙ H) _ _ _ _
    (truncGEIsoSingleHomology_hom_naturality α d hK hK')
  have h3 := Stacks.DegreeZeroTensor.map_sq H _ _ _ _
    (derivedToOrdinaryPullbackSingle_naturality f ((homologyFunctor _ d).map α) d)
  have h4 := homologySingleIso_hom_naturality
    ((RingedSpaceModuleAdjunction.modulePullback f).map ((homologyFunctor _ d).map α)) d
  simp only [derivedPullbackTopDegreeIsoPullback, derivedPullbackTopDegreeIsoSingle,
    derivedPullbackTopDegreeIso, Stacks.TopDegreeComparison.topDegreeIso,
    homologyDerivedPullbackSingleIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    homologyDerivedPullbackSingleMap, Category.assoc]
  simp only [H, L, Functor.comp_map] at h1 h2 h3 h4
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4]

section

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- The derived-to-ordinary tensor comparison `A[0] ⊗^L F[0] ⟶ (A ⊗ F)[0]` is natural in `F`. -/
theorem tensorSingleToSingle_naturality_right (A : Modules R) {F F' : Modules R} (g : F ⟶ F') :
    ((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g))
        ≫ tensorSingleToSingle R A F' =
      tensorSingleToSingle R A F ≫ DerivedCategory.Q.map
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).map g)) := by
  have h := (canonicalDerivedTensorProduct R).toTensor_naturality (𝟙 (sg R A))
    ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g)
  rw [(DerivedCategory.Q (C := Modules R)).map_id (sg R A),
    (canonicalDerivedTensorProduct R).tensor.map_id (DerivedCategory.Q.obj (sg R A)),
    NatTrans.id_app, Category.id_comp] at h
  have h2 := Stacks.DegreeZeroTensor.map_sq (DerivedCategory.Q (C := Modules R)) _ _ _ _
    (totSingleIsoSingle_hom_naturality_second R A g)
  rw [tensorSingleToSingle, tensorSingleToSingle]
  exact Stacks.DegreeZeroTensor.two_sq _ _ _ _ _ _ _ h h2

/-- The degree-`c` read-off `Hᶜ(A[c] ⊗^L G[0]) ≅ A ⊗ G` is natural in `G`. -/
theorem degreeSingleLeftTensorIso_hom_naturality (A : Modules R) {G G' : Modules R} (g : G ⟶ G')
    (c : ℤ) :
    (DerivedCategory.homologyFunctor (Modules R) c).map
        (((derivedTensorProductFunctor R).obj
          ((DerivedCategory.singleFunctor (Modules R) c).obj A)).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g)))
        ≫ (degreeSingleLeftTensorIso R A G' c).hom =
      (degreeSingleLeftTensorIso R A G c).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).map g := by
  let T := derivedTensorProductFunctor R
  let sg' :=
    DerivedCategory.Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g)
  have h1 : (T.map (singleShiftIso R A c).hom).app (DerivedCategory.Q.obj (sg R G)) ≫
      (T.obj _).map sg' = (T.obj _).map sg' ≫
        (T.map (singleShiftIso R A c).hom).app (DerivedCategory.Q.obj (sg R G')) :=
    ((T.map (singleShiftIso R A c).hom).naturality sg').symm
  have h2 := NatTrans.shift_app_comm (T.flip.map sg') (-c) (DerivedCategory.Q.obj (sg R A))
  have h3 := ((Stacks.HomologyShift.homologyShiftIso (Modules R) (-c) c 0 (by lia)).hom.naturality
    ((T.obj (DerivedCategory.Q.obj (sg R A))).map sg'))
  have h4 := degreeZeroTensorMap_naturality_second R A g
  simp only [Functor.comp_map, Functor.flip_map_app] at h2 h3
  simp only [degreeSingleLeftTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.flip_obj_map, degreeZeroTensorIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Category.assoc ((T.obj _).map sg'), ← h1, Category.assoc,
    ← h2, Functor.map_comp_assoc, Functor.map_comp_assoc, Functor.map_comp_assoc,
    reassoc_of% h3]
  exact congrArg _ (congrArg _ (congrArg _ h4))

end

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `tensorDerivedPullbackToSingle` is natural in the module on the base. -/
theorem tensorDerivedPullbackToSingle_naturality
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {G G' : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)} (g : G ⟶ G') :
    ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F)).map
        ((derivedPullback f.toLRSHom.toShHom).map ((singleFunctor _ 0).map g)) ≫
        tensorDerivedPullbackToSingle f F G' =
      tensorDerivedPullbackToSingle f F G ≫ (singleFunctor _ 0).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).map
          ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map g)) := by
  have h1 := derivedToOrdinaryPullbackSingle_naturality f.toLRSHom.toShHom g 0
  have h2 := tensorSingleToSingle_naturality_right X.toRingedSpace.sheaf F
    ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map g)
  have h3 := Stacks.DegreeZeroTensor.map_sq ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F)) _ _ _ _ h1
  rw [tensorDerivedPullbackToSingle, tensorDerivedPullbackToSingle]
  exact Stacks.DegreeZeroTensor.two_sq _ _ _ _ _ _ _ h3 h2

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
