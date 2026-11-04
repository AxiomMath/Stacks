module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.Mates

/-!
# The comparison of a pasted square, on the generators of a flat localization

The Tag 065Z comparison of the outer rectangle of two stacked squares of rings, read on cohomology
and on the generators `1 ⊗ m` of a flat localization:
`RingTheory.TorIndependence.squareComparison_pasted_flatComp_inv`,
`RingTheory.TorIndependence.derivedRestrictScalarsSquareIso_homologyIso_apply`,
`RingTheory.TorIndependence.squareComparison_unit_one_tmul` and
`RingTheory.TorIndependence.squareComparison_pasted_unit_one_tmul`, with the generator lemmas
`RingTheory.TorIndependence.flatDerivedHomologyIso_comp_inv_app_one_tmul`,
`RingTheory.TorIndependence.unit_comp_restrictHomologyIso_apply` and
`RingTheory.TorIndependence.flatDerivedHomologyIso_inv_app_one_tmul_map`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp totalDerivedExtensionScalarsComp_comparison
  derivedExtensionScalarsAdjunction)
open scoped TensorProduct ChangeOfRings

universe u w v₁ v₂ v₃ u₁ u₂ u₃

/-! ### The comparison of a pasted square, on the generators of a flat localization -/

namespace RingTheory.TorIndependence

section Composite

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [HasDerivedCategory.{u} (ModuleCat.{u} C)]

/-- **Derived extension of scalars along a flat map composes with its degreewise comparison.**
For `p : A → B` and `ε : B → C` flat, the identification of derived extension of scalars along
`ε ∘ p` with the degreewise functor is the composition isomorphism of derived extension of
scalars, followed by the two identifications along `p` and along `ε`, followed by the composition
isomorphism of degreewise extension of scalars read on derived categories. -/
public theorem flatDerivedExtensionScalarsIso_comp (p : A →+* B) (ε : B →+* C)
    (hp : p.Flat) (hε : ε.Flat) (hv : (ε.comp p).Flat) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hp
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hε
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hv
    (flatDerivedExtensionScalarsIso.{u, u} (ε.comp p) hv).hom =
      (totalDerivedExtensionScalarsComp.{u, u} p ε).inv ≫
        Functor.whiskerRight (flatDerivedExtensionScalarsIso.{u, u} p hp).hom
            (totalDerivedExtensionScalars.{u, u, u} ε).functor ≫
          Functor.whiskerLeft ((ModuleCat.extendScalars.{u, u, u} p).mapDerivedCategory)
              (flatDerivedExtensionScalarsIso.{u, u} ε hε).hom ≫
            (mapDerivedCategoryCompNatIso (ModuleCat.extendScalars.{u, u, u} p)
              (ModuleCat.extendScalars.{u, u, u} ε)
              (ModuleCat.extendScalars.{u, u, u} (ε.comp p))
              (ModuleCat.extendScalarsComp.{u, u} p ε).symm).hom := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hp
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hε
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hv
  have hfac : ∀ {R T : Type u} [CommRing R] [CommRing T]
      [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} T)]
      (f : R →+* T) (hf : f.Flat) (P : CochainComplex (ModuleCat.{u} R) ℤ),
      let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
      (flatDerivedExtensionScalarsIso.{u, u} f hf).hom.app (DerivedCategory.Q.obj P) ≫
          (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app P =
        extendComparisonApp.{u, u} f P := by
    intro R T _ _ _ _ f hf P
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    have hid : (mapHomologicalComplexIsoOfExtendScalars f
          (ModuleCat.extendScalars.{u, u, u} f) (Iso.refl _)).hom.app P =
        CategoryStruct.id _ :=
      CategoryTheory.Functor.map_id _ _
    exact (totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors f
      (ModuleCat.extendScalars.{u, u, u} f) (Iso.refl _) P).trans
      ((congrArg (fun z => extendComparisonApp.{u, u} f P ≫ z) hid).trans (Category.comp_id _))
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (fun P => ?_)
  have hmc : (totalDerivedExtensionScalars.{u, u, u} ε).functor.map
          ((flatDerivedExtensionScalarsIso.{u, u} p hp).hom.app (DerivedCategory.Q.obj P)) ≫
        (totalDerivedExtensionScalars.{u, u, u} ε).functor.map
          ((ModuleCat.extendScalars.{u, u, u} p).mapDerivedCategoryFactors.hom.app P) =
      (totalDerivedExtensionScalars.{u, u, u} ε).functor.map
        (extendComparisonApp.{u, u} p P) := by
    rw [← CategoryTheory.Functor.map_comp, hfac p hp P]
  have hcc : (totalDerivedExtensionScalars.{u, u, u} ε).functor.map
          (extendComparisonApp.{u, u} p P) ≫
        extendComparisonApp.{u, u} ε
            (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.extendScalarsComp.{u, u} p ε).symm (ComplexShape.up ℤ)).hom.app P) =
      (totalDerivedExtensionScalarsComp.{u, u} p ε).hom.app (DerivedCategory.Q.obj P) ≫
        extendComparisonApp.{u, u} (ε.comp p) P :=
    totalDerivedExtensionScalarsComp_comparison.{u, u} p ε P
  have hnat := (flatDerivedExtensionScalarsIso.{u, u} ε hε).hom.naturality
    ((ModuleCat.extendScalars.{u, u, u} p).mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [← Iso.cancel_iso_hom_right _ _
    ((ModuleCat.extendScalars.{u, u, u} (ε.comp p)).mapDerivedCategoryFactors.app P)]
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.app_hom]
  rw [Category.assoc, Category.assoc, Category.assoc,
    mapDerivedCategoryCompNatIso_hom_app_Q (ModuleCat.extendScalars.{u, u, u} p)
      (ModuleCat.extendScalars.{u, u, u} ε) (ModuleCat.extendScalars.{u, u, u} (ε.comp p))
      (ModuleCat.extendScalarsComp.{u, u} p ε).symm P]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id, ← reassoc_of% hnat, reassoc_of% (hfac ε hε
    (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)),
    reassoc_of% hmc, hcc, Iso.inv_hom_id_app_assoc]
  exact hfac (ε.comp p) hv P

end Composite

variable {R A R' A' R₃ A₃ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₃] [CommRing A₃]
  (a : R →+* A) (b : R →+* R') (c : A →+* A') (d : R' →+* A')
  (e : R' →+* R₃) (v : A' →+* A₃) (t : R₃ →+* A₃)
  (sq : c.comp a = d.comp b) (sqb : v.comp d = t.comp e)

/-- The flat composite comparison is the inverse composition isomorphism of derived extension of
scalars, followed by `RingTheory.TorIndependence.flatDerivedHomologyIso` along the flat factor. -/
private theorem flatCompDerivedHomologyIso_eq (he : e.Flat) (n : ℤ) :
    flatCompDerivedHomologyIso.{u, u} b e he n =
      Functor.isoWhiskerRight (totalDerivedExtensionScalarsComp.{u, u} b e).symm
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (totalDerivedExtensionScalars.{u, u, u} b).functor
          (flatDerivedHomologyIso.{u, u} e he n) :=
  rfl

/-- **The inverse of the flat composite comparison at an object.** For `e` flat the comparison
`H^n(N ⊗ᴸ_R A₂) ≅ A₂ ⊗_A H^n(N ⊗ᴸ_R A)` of
`RingTheory.TorIndependence.flatCompDerivedHomologyIso` is the composition isomorphism of derived
extension of scalars followed by `RingTheory.TorIndependence.flatDerivedHomologyIso`, here on
inverses at an object. -/
public theorem flatCompDerivedHomologyIso_app_inv (he : e.Flat) (n : ℤ)
    (N : DerivedCategory (ModuleCat.{u} R)) :
    ((flatCompDerivedHomologyIso.{u, u} b e he n).app N).inv =
      ((flatDerivedHomologyIso.{u, u} e he n).app
          ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj N)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
          ((totalDerivedExtensionScalarsComp.{u, u} b e).hom.app N) := by
  rw [flatCompDerivedHomologyIso_eq]
  dsimp only [Iso.app_inv, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Iso.symm_inv]
  rw [Category.comp_id]

/-- The same reading on the forward maps: the flat composite comparison is the composition
isomorphism of derived extension of scalars read backwards, followed by
`RingTheory.TorIndependence.flatDerivedHomologyIso` along the flat factor. -/
private theorem flatCompDerivedHomologyIso_hom_app (he : e.Flat) (n : ℤ)
    (N : DerivedCategory (ModuleCat.{u} R)) :
    (flatCompDerivedHomologyIso.{u, u} b e he n).hom.app N =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
          ((totalDerivedExtensionScalarsComp.{u, u} b e).inv.app N) ≫
        (flatDerivedHomologyIso.{u, u} e he n).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj N) := by
  rw [flatCompDerivedHomologyIso_eq]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Iso.symm_hom]
  simp only [Category.id_comp]

/-- The component of `RingTheory.TorIndependence.flatDerivedHomologyIso` at an object: the
identification of derived extension of scalars with the degreewise functor, followed by the
homology comparison of that functor. -/
private theorem flatDerivedHomologyIso_hom_app {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    (k : R₁ →+* R₂) (hk : k.Flat) (n : ℤ) (W : DerivedCategory (ModuleCat.{u} R₁)) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hk
    (flatDerivedHomologyIso.{u, u} k hk n).hom.app W =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R₂) n).map
          ((flatDerivedExtensionScalarsIso.{u, u} k hk).hom.app W) ≫
        ((ModuleCat.extendScalars.{u, u, u} k).mapDerivedCategoryHomologyIso n).hom.app W :=
  rfl

/-- **The flat homology comparison along a composite.** For `b` and `e` flat the comparison
`H^n(N ⊗ᴸ_R R₃) ≅ R₃ ⊗_R H^n(N)` along `e ∘ b` is the flat composite comparison of
`RingTheory.TorIndependence.flatCompDerivedHomologyIso`, followed by the comparison along `b`
extended to `R₃`, followed by the composition isomorphism of degreewise extension of scalars. -/
private theorem flatDerivedHomologyIso_comp_app (hb : b.Flat) (he : e.Flat)
    (hv : (e.comp b).Flat) (n : ℤ) (W : DerivedCategory (ModuleCat.{u} R)) :
    (flatDerivedHomologyIso.{u, u} (e.comp b) hv n).app W =
      (flatCompDerivedHomologyIso.{u, u} b e he n).app W ≪≫
        (ModuleCat.extendScalars.{u, u, u} e).mapIso
            ((flatDerivedHomologyIso.{u, u} b hb n).app W) ≪≫
          ((ModuleCat.extendScalarsComp.{u, u} b e).app
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj W)).symm := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hb
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat he
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hv
  refine Iso.ext ?_
  have hcnat := mapDerivedCategoryCompNatIso_homologyIso_hom_app
    (ModuleCat.extendScalars.{u, u, u} b) (ModuleCat.extendScalars.{u, u, u} e)
    (ModuleCat.extendScalars.{u, u, u} (e.comp b))
    (ModuleCat.extendScalarsComp.{u, u} b e).symm n W
  have hnatDES := (flatDerivedExtensionScalarsIso.{u, u} e he).hom.naturality
    ((flatDerivedExtensionScalarsIso.{u, u} b hb).hom.app W)
  have hnatHI := NatTrans.naturality
    ((ModuleCat.extendScalars.{u, u, u} e).mapDerivedCategoryHomologyIso n).hom
    ((flatDerivedExtensionScalarsIso.{u, u} b hb).hom.app W)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnatHI
  dsimp only [Iso.symm_hom] at hcnat
  have hDES := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map hnatDES
  simp only [CategoryTheory.Functor.map_comp] at hDES
  dsimp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Iso.symm_hom,
    Functor.mapIso_hom, Functor.comp_obj]
  rw [flatDerivedHomologyIso_hom_app (e.comp b) hv n W,
    NatTrans.congr_app (flatDerivedExtensionScalarsIso_comp b e hb he hv) W]
  dsimp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, Functor.comp_obj]
  rw [flatCompDerivedHomologyIso_hom_app b e he n W,
    flatDerivedHomologyIso_hom_app b hb n W,
    flatDerivedHomologyIso_hom_app e he n
      ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj W)]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← hcnat, reassoc_of% hDES, reassoc_of% hnatHI]

/-- **The generator of the flat localization along a composite.** The inverse of the comparison
`H^n(N ⊗ᴸ_R R₃) ≅ R₃ ⊗_R H^n(N)` along `e ∘ b`, evaluated on `1 ⊗ z`, is the inverse of the
comparison along `b` on `1 ⊗ z` followed by the inverse of the comparison along `e` on `1 ⊗ -`,
and then the composition isomorphism of derived extension of scalars. -/
public theorem flatDerivedHomologyIso_comp_inv_app_one_tmul (hb : b.Flat) (he : e.Flat)
    (hv : (e.comp b).Flat) (n : ℤ) (W : DerivedCategory (ModuleCat.{u} R))
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj W) :
    ((flatDerivedHomologyIso.{u, u} (e.comp b) hv n).app W).inv.hom
        ((1 : R₃) ⊗ₜ[R, e.comp b] z) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
          ((totalDerivedExtensionScalarsComp.{u, u} b e).hom.app W)).hom
        (((flatDerivedHomologyIso.{u, u} e he n).app
              ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj W)).inv.hom
          ((1 : R₃) ⊗ₜ[R', e]
            (((flatDerivedHomologyIso.{u, u} b hb n).app W).inv.hom
              ((1 : R') ⊗ₜ[R, b] z)))) := by
  have hinv : ((flatDerivedHomologyIso.{u, u} (e.comp b) hv n).app W).inv =
      (ModuleCat.extendScalarsComp.{u, u} b e).hom.app
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj W) ≫
        (ModuleCat.extendScalars.{u, u, u} e).map
            (((flatDerivedHomologyIso.{u, u} b hb n).app W).inv) ≫
          ((flatCompDerivedHomologyIso.{u, u} b e he n).app W).inv := by
    rw [flatDerivedHomologyIso_comp_app b e hb he hv n W]
    simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Functor.mapIso_inv, Category.assoc]
  refine Eq.trans (ConcreteCategory.congr_hom hinv ((1 : R₃) ⊗ₜ[R, e.comp b] z)) ?_
  refine Eq.trans (congrArg
    (fun q => ((flatCompDerivedHomologyIso.{u, u} b e he n).app W).inv.hom
      (((ModuleCat.extendScalars.{u, u, u} e).map
        (((flatDerivedHomologyIso.{u, u} b hb n).app W).inv)).hom q))
    (ModuleCat.extendScalarsComp_hom_app_one_tmul b e _ z)) ?_
  refine Eq.trans (congrArg
    (fun q => ((flatCompDerivedHomologyIso.{u, u} b e he n).app W).inv.hom q)
    (ModuleCat.ExtendScalars.map_tmul e
      (((flatDerivedHomologyIso.{u, u} b hb n).app W).inv) (1 : R₃)
      ((1 : R') ⊗ₜ[R, b] z))) ?_
  exact ConcreteCategory.congr_hom (flatCompDerivedHomologyIso_app_inv b e he n W) _

section Units

variable {B₁ B₂ B₃ : Type u} [CommRing B₁] [CommRing B₂] [CommRing B₃]

/-- **The unit along a flat composite, read as the two units in succession.** For `p` and `ε`
flat, the unit of the derived change-of-rings adjunction along `ε ∘ p` at `V`, read over `B₁`
through the homology comparison of restriction of scalars and pushed along a morphism `ξ` out of
`V ⊗ᴸ_{B₁} B₃`, is the unit along `p` followed by the unit along `ε` and `ξ`. -/
public theorem unit_comp_restrictHomologyIso_apply (p : B₁ →+* B₂) (ε : B₂ →+* B₃)
    (hp : p.Flat) (hε : ε.Flat) (hv : (ε.comp p).Flat) (n : ℤ)
    (V : DerivedCategory (ModuleCat.{u} B₁)) (Y : DerivedCategory (ModuleCat.{u} B₃))
    (ξ : (totalDerivedExtensionScalars.{u, u, u} (ε.comp p)).functor.obj V ⟶ Y)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).obj V) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₃) n).map ξ).hom
        ((((ModuleCat.restrictScalars.{u} (ε.comp p)).mapDerivedCategoryHomologyIso n).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} (ε.comp p)).functor.obj V)).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).map
            ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B₁ B₃ _ _ (ε.comp p) _ _
              (totalDerivedExtensionScalars.{u, u, u} (ε.comp p)).functor
              (totalDerivedExtensionScalars.{u, u, u} (ε.comp p)).comparison
              (totalDerivedExtensionScalars.{u, u, u} (ε.comp p)).isLeftDerived).unit.app V)).hom
            z)) =
      (((ModuleCat.restrictScalars.{u} ε).mapDerivedCategoryHomologyIso n).hom.app Y).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₂) n).map
            ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B₂ B₃ _ _ ε _ _
                  (totalDerivedExtensionScalars.{u, u, u} ε).functor
                  (totalDerivedExtensionScalars.{u, u, u} ε).comparison
                  (totalDerivedExtensionScalars.{u, u, u} ε).isLeftDerived).unit.app
                ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj V) ≫
              (ModuleCat.restrictScalars.{u} ε).mapDerivedCategory.map
                ((totalDerivedExtensionScalarsComp.{u, u} p ε).hom.app V ≫ ξ))).hom
          ((((ModuleCat.restrictScalars.{u} p).mapDerivedCategoryHomologyIso n).hom.app
                ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj V)).hom
            (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).map
              ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B₁ B₂ _ _ p _ _
                (totalDerivedExtensionScalars.{u, u, u} p).functor
                (totalDerivedExtensionScalars.{u, u, u} p).comparison
                (totalDerivedExtensionScalars.{u, u, u} p).isLeftDerived).unit.app V)).hom
              z))) := by
  have hnat := NatTrans.naturality
    ((ModuleCat.restrictScalars.{u} ε).mapDerivedCategoryHomologyIso n).hom
    ((totalDerivedExtensionScalarsComp.{u, u} p ε).hom.app V ≫ ξ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  refine Eq.trans (congrArg
    (fun q => ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₃) n).map ξ).hom q)
    (flatDerivedHomologyIso_inv_app_one_tmul.{u, u} (ε.comp p) hv n V z).symm) ?_
  refine Eq.trans (congrArg
    (fun q => ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₃) n).map ξ).hom q)
    (flatDerivedHomologyIso_comp_inv_app_one_tmul p ε hp hε hv n V z)) ?_
  refine Eq.trans (congrArg
    (fun q => ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₃) n).map ξ).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₃) n).map
        ((totalDerivedExtensionScalarsComp.{u, u} p ε).hom.app V)).hom q))
    (flatDerivedHomologyIso_inv_app_one_tmul.{u, u} ε hε n
      ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj V)
      ((((flatDerivedHomologyIso.{u, u} p hp n).app V)).inv.hom
        ((1 : B₂) ⊗ₜ[B₁, p] z)))) ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (CategoryTheory.Functor.map_comp (DerivedCategory.homologyFunctor (ModuleCat.{u} B₃) n)
      ((totalDerivedExtensionScalarsComp.{u, u} p ε).hom.app V) ξ).symm _) ?_
  refine Eq.trans (ConcreteCategory.congr_hom hnat.symm _) ?_
  refine Eq.trans (congrArg
    (fun q => (((ModuleCat.restrictScalars.{u} ε).mapDerivedCategoryHomologyIso n).hom.app Y).hom q)
    (ConcreteCategory.congr_hom
      (CategoryTheory.Functor.map_comp (DerivedCategory.homologyFunctor (ModuleCat.{u} B₂) n)
        ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B₂ B₃ _ _ ε _ _
            (totalDerivedExtensionScalars.{u, u, u} ε).functor
            (totalDerivedExtensionScalars.{u, u, u} ε).comparison
            (totalDerivedExtensionScalars.{u, u, u} ε).isLeftDerived).unit.app
          ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj V))
        ((ModuleCat.restrictScalars.{u} ε).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} p ε).hom.app V ≫ ξ))).symm _)) ?_
  refine congrArg
    (fun q => (((ModuleCat.restrictScalars.{u} ε).mapDerivedCategoryHomologyIso n).hom.app Y).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₂) n).map
          ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B₂ B₃ _ _ ε _ _
                (totalDerivedExtensionScalars.{u, u, u} ε).functor
                (totalDerivedExtensionScalars.{u, u, u} ε).comparison
                (totalDerivedExtensionScalars.{u, u, u} ε).isLeftDerived).unit.app
              ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj V) ≫
            (ModuleCat.restrictScalars.{u} ε).mapDerivedCategory.map
              ((totalDerivedExtensionScalarsComp.{u, u} p ε).hom.app V ≫ ξ))).hom q))
    (flatDerivedHomologyIso_inv_app_one_tmul.{u, u} p hp n V z)

/-- **The generator of a flat localization, moved along a morphism.** For `p` flat the inverse of
the comparison `H^n(W ⊗ᴸ_{B₁} B₂) ≅ B₂ ⊗_{B₁} H^n(W)` on the generator `1 ⊗ H^n(Φ)(z)` is the
generator `1 ⊗ z` pushed along `H^n(Φ ⊗ᴸ B₂)`, the generator itself being computed as the unit of
the derived change-of-rings adjunction along `p`. -/
public theorem flatDerivedHomologyIso_inv_app_one_tmul_map (p : B₁ →+* B₂) (hp : p.Flat) (n : ℤ)
    {V W : DerivedCategory (ModuleCat.{u} B₁)} (Φ : V ⟶ W)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).obj V) :
    ((flatDerivedHomologyIso.{u, u} p hp n).app W).inv.hom
        ((1 : B₂) ⊗ₜ[B₁, p]
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).map Φ).hom z)) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₂) n).map
          ((totalDerivedExtensionScalars.{u, u, u} p).functor.map Φ)).hom
        ((((ModuleCat.restrictScalars.{u} p).mapDerivedCategoryHomologyIso n).hom.app
              ((totalDerivedExtensionScalars.{u, u, u} p).functor.obj V)).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).map
            ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B₁ B₂ _ _ p _ _
              (totalDerivedExtensionScalars.{u, u, u} p).functor
              (totalDerivedExtensionScalars.{u, u, u} p).comparison
              (totalDerivedExtensionScalars.{u, u, u} p).isLeftDerived).unit.app V)).hom z)) := by
  have hnat := NatTrans.naturality (flatDerivedHomologyIso.{u, u} p hp n).inv Φ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  refine Eq.trans (congrArg
    (fun q => ((flatDerivedHomologyIso.{u, u} p hp n).app W).inv.hom q)
    (ModuleCat.ExtendScalars.map_tmul p
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₁) n).map Φ) (1 : B₂) z).symm) ?_
  refine Eq.trans (ConcreteCategory.congr_hom hnat ((1 : B₂) ⊗ₜ[B₁, p] z)) ?_
  exact congrArg
    (fun q => ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₂) n).map
      ((totalDerivedExtensionScalars.{u, u, u} p).functor.map Φ)).hom q)
    (flatDerivedHomologyIso_inv_app_one_tmul.{u, u} p hp n V z)

end Units

section LocalizationAbsorb

variable {C₄ C₅ C₆ : Type u} [CommRing C₄] [CommRing C₅] [CommRing C₆] [Algebra C₄ C₅]
  (S : Submonoid C₄) [IsLocalization S C₅] (g : C₅ →+* C₆)

include S in
/-- **The passage `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` absorbs a unit
followed by a morphism out of the localization.** This is
`RingTheory.TorIndependence.map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app` with a
morphism `μ` out of the localization inserted between the unit and the passage. -/
public theorem map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app_map
    (P : DerivedCategory (ModuleCat.{u} C₄)) {N : DerivedCategory (ModuleCat.{u} C₅)}
    (μ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap C₄ C₅)).functor.obj P ⟶ N) :
    (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap C₄ C₅))).functor.map
          ((derivedExtendRestrictAdjunction (A := C₄) (A₂ := C₅)).unit.app P ≫
            (ModuleCat.restrictScalars.{u} (algebraMap C₄ C₅)).mapDerivedCategory.map μ) ≫
        (restrictScalarsDerivedExtendCompIso.{u, u} S g).hom.app N =
      (totalDerivedExtensionScalarsComp.{u, u} (algebraMap C₄ C₅) g).inv.app P ≫
        (totalDerivedExtensionScalars.{u, u, u} g).functor.map μ := by
  have hnat := NatTrans.naturality (restrictScalarsDerivedExtendCompIso.{u, u} S g).hom μ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hnat, ← Category.assoc,
    map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app S g P]

end LocalizationAbsorb

/-- The two factors of `RingTheory.TorIndependence.cohomologyComparisonMapGeneral`: the
cohomology of the Tag 065Z comparison followed by `φ`, and the identification of the cohomology
of `K'` read over `R'`. -/
theorem cohomologyComparisonMap_eq {R₁ A₁ R₂ A₂ : Type u} [CommRing R₁] [CommRing A₁]
    [CommRing R₂] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₁ R₂] [Algebra R₁ A₂]
    [Algebra A₁ A₂] [Algebra R₂ A₂] [IsScalarTower R₁ A₁ A₂] [IsScalarTower R₁ R₂ A₂]
    (K : DerivedCategory (ModuleCat.{u} A₁)) (K' : DerivedCategory (ModuleCat.{u} A₂))
    (ψ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A₁ A₂)).functor.obj K ⟶ K')
    (n : ℤ) :
    cohomologyComparisonMapGeneral (R := R₁) (R' := R₂) K K' ψ n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R₂) n).map
          ((squareDerivedComparisonGeneral (R := R₁) (A := A₁) (R' := R₂) (A' := A₂)).app K ≫
            (ModuleCat.restrictScalars.{u} (algebraMap R₂ A₂)).mapDerivedCategory.map ψ) ≫
        (((ModuleCat.restrictScalars.{u} (algebraMap R₂ A₂)).mapDerivedCategoryHomologyIso
          n).hom.app K') :=
  rfl

include sq sqb in
/-- **The pasting law of Tag 065Z at an object.** The comparison of the outer rectangle of two
stacked squares of rings, evaluated at a complex, written as the four factors of
`RingTheory.TorIndependence.pastedComparison`: the composition isomorphism of derived extension
of scalars along `R → R' → R₃`, the top square's comparison extended along `R' → R₃`, the bottom
square's comparison, and the composition isomorphism along `A → A' → A₃`. -/
public theorem squareComparison_pasted_app (N₀ : DerivedCategory (ModuleCat.{u} A)) :
    (squareComparison.{u, u} a (e.comp b) (v.comp c) t
          (pastedSquare_comm a b c d e v t sq sqb)).app N₀ =
      (totalDerivedExtensionScalarsComp.{u, u} b e).inv.app
          ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.obj N₀) ≫
        (totalDerivedExtensionScalars.{u, u, u} e).functor.map
            ((squareComparison.{u, u} a b c d sq).app N₀) ≫
          (squareComparison.{u, u} d e v t sqb).app
              ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀) ≫
            (ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map
              ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀) := by
  rw [squareComparison_pasted.{u, u} a b c d e v t sq sqb]
  dsimp only [pastedComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp]

include sq sqb in
/-- **The outer rectangle's comparison against the generators of the flat localization.** For `e`
flat, the inverse of `RingTheory.TorIndependence.flatCompDerivedHomologyIso` followed by the
cohomology of the outer rectangle's Tag 065Z comparison is the cohomology of the *top* square's
comparison, extended along `R' → R₃`, followed by the inverse of
`RingTheory.TorIndependence.flatDerivedHomologyIso` and the cohomology of the *bottom* square's
comparison. -/
public theorem squareComparison_pasted_flatComp_inv (he : e.Flat) (n : ℤ)
    (N₀ : DerivedCategory (ModuleCat.{u} A)) :
    ((flatCompDerivedHomologyIso.{u, u} b e he n).app
            ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.obj N₀)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
          ((squareComparison.{u, u} a (e.comp b) (v.comp c) t
            (pastedSquare_comm a b c d e v t sq sqb)).app N₀) =
      (ModuleCat.extendScalars.{u, u, u} e).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((squareComparison.{u, u} a b c d sq).app N₀)) ≫
        ((flatDerivedHomologyIso.{u, u} e he n).app
            ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj
              ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))).inv ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
            ((squareComparison.{u, u} d e v t sqb).app
                ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀) ≫
              (ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map
                ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀)) := by
  have hnat := (flatDerivedHomologyIso.{u, u} e he n).inv.naturality
    ((squareComparison.{u, u} a b c d sq).app N₀)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [flatCompDerivedHomologyIso_app_inv b e he n,
    squareComparison_pasted_app a b c d e v t sq sqb N₀, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc,
    CategoryTheory.Functor.map_comp]
  dsimp only [Iso.app_inv]
  rw [← reassoc_of% hnat]


include sqb in
/-- **The two readings of the homology comparison around a commuting square of restrictions
agree.** For a commuting square of rings `v ∘ d = t ∘ e`, a complex `X` of `A₃`-modules read over
`R'` has its cohomology compared with the cohomology of `X` in two ways — down the left edge and
down the right edge — and the two agree, under the identification
`RingTheory.TorIndependence.derivedRestrictScalarsSquareIso` of the two readings of `X` over
`R'`. -/
public theorem derivedRestrictScalarsSquareIso_homologyIso_apply (n : ℤ)
    (X : DerivedCategory (ModuleCat.{u} A₃))
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
      ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{u} v).mapDerivedCategory.obj X))) :
    (((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom.app X).hom
        ((((ModuleCat.restrictScalars.{u} e).mapDerivedCategoryHomologyIso n).hom.app
            ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory.obj X)).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((derivedRestrictScalarsSquareIso.{u, u} d v e t sqb).hom.app X)).hom z)) =
      (((ModuleCat.restrictScalars.{u} v).mapDerivedCategoryHomologyIso n).hom.app X).hom
        ((((ModuleCat.restrictScalars.{u} d).mapDerivedCategoryHomologyIso n).hom.app
            ((ModuleCat.restrictScalars.{u} v).mapDerivedCategory.obj X)).hom z) := by
  have hl := mapDerivedCategoryCompNatIso_homologyIso_hom_app
    (ModuleCat.restrictScalars.{u} v) (ModuleCat.restrictScalars.{u} d)
    (ModuleCat.restrictScalars.{u} (v.comp d))
    (ModuleCat.restrictScalarsComp'.{u} d v (v.comp d) rfl).symm n X
  have hr := mapDerivedCategoryCompNatIso_homologyIso_hom_app
    (ModuleCat.restrictScalars.{u} t) (ModuleCat.restrictScalars.{u} e)
    (ModuleCat.restrictScalars.{u} (v.comp d))
    (ModuleCat.restrictScalarsComp'.{u} e t (v.comp d) sqb).symm n X
  have hd : (derivedRestrictScalarsSquareIso.{u, u} d v e t sqb).hom.app X =
      (mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} v)
            (ModuleCat.restrictScalars.{u} d) (ModuleCat.restrictScalars.{u} (v.comp d))
            (ModuleCat.restrictScalarsComp'.{u} d v (v.comp d) rfl).symm).hom.app X ≫
        (mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} t)
            (ModuleCat.restrictScalars.{u} e) (ModuleCat.restrictScalars.{u} (v.comp d))
            (ModuleCat.restrictScalarsComp'.{u} e t (v.comp d) sqb).symm).inv.app X := rfl
  have hmor : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((derivedRestrictScalarsSquareIso.{u, u} d v e t sqb).hom.app X) ≫
        ((ModuleCat.restrictScalars.{u} e).mapDerivedCategoryHomologyIso n).hom.app
            ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory.obj X) ≫
          (ModuleCat.restrictScalars.{u} e).map
              (((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom.app X) ≫
            (ModuleCat.restrictScalarsComp'.{u} e t (v.comp d) sqb).symm.hom.app
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A₃) n).obj X) =
      ((ModuleCat.restrictScalars.{u} d).mapDerivedCategoryHomologyIso n).hom.app
            ((ModuleCat.restrictScalars.{u} v).mapDerivedCategory.obj X) ≫
          (ModuleCat.restrictScalars.{u} d).map
              (((ModuleCat.restrictScalars.{u} v).mapDerivedCategoryHomologyIso n).hom.app X) ≫
            (ModuleCat.restrictScalarsComp'.{u} d v (v.comp d) rfl).symm.hom.app
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A₃) n).obj X) := by
    have hcancel : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((derivedRestrictScalarsSquareIso.{u, u} d v e t sqb).hom.app X) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} t)
                (ModuleCat.restrictScalars.{u} e) (ModuleCat.restrictScalars.{u} (v.comp d))
                (ModuleCat.restrictScalarsComp'.{u} e t (v.comp d) sqb).symm).hom.app X) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} v)
              (ModuleCat.restrictScalars.{u} d) (ModuleCat.restrictScalars.{u} (v.comp d))
              (ModuleCat.restrictScalarsComp'.{u} d v (v.comp d) rfl).symm).hom.app X) := by
      rw [hd, ← CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
        Category.comp_id]
    rw [hr, hl, ← Category.assoc, hcancel]
  exact ConcreteCategory.congr_hom hmor z

include sqb in
/-- **A square on the generators of its flat localization.** For `e` flat, the Tag 065Z
comparison of the square `(R', A', R₃, A₃)` on cohomology, evaluated on the germ generator
`1 ⊗ z` of the `R₃`-localization, is the unit of the derived change-of-rings adjunction along
`A' → A₃` applied to `z` read over `A'`. -/
public theorem squareComparison_unit_one_tmul (he : e.Flat) (n : ℤ)
    (V : DerivedCategory (ModuleCat.{u} A'))
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
      ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj V)) :
    (((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj V)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
          ((squareComparison.{u, u} d e v t sqb).app V)).hom
          (((flatDerivedHomologyIso.{u, u} e he n).app
              ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj V)).inv.hom
            ((1 : R₃) ⊗ₜ[R', e] z))) =
      (((ModuleCat.restrictScalars.{u} v).mapDerivedCategoryHomologyIso n).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj V)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
          ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A' A₃ _ _ v _ _
            (totalDerivedExtensionScalars.{u, u, u} v).functor
            (totalDerivedExtensionScalars.{u, u, u} v).comparison
            (totalDerivedExtensionScalars.{u, u, u} v).isLeftDerived).unit.app V)).hom
          ((((ModuleCat.restrictScalars.{u} d).mapDerivedCategoryHomologyIso n).hom.app V).hom
            z)) := by
  have h1 := flatDerivedHomologyIso_inv_app_one_tmul.{u, u} e he n
    ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj V) z
  have h2 := ((ModuleCat.restrictScalars.{u} e).mapDerivedCategoryHomologyIso n).hom.naturality
    ((squareComparison.{u, u} d e v t sqb).app V)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h2
  have h4 := ((ModuleCat.restrictScalars.{u} d).mapDerivedCategoryHomologyIso n).hom.naturality
    ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A' A₃ _ _ v _ _
      (totalDerivedExtensionScalars.{u, u, u} v).functor
      (totalDerivedExtensionScalars.{u, u, u} v).comparison
      (totalDerivedExtensionScalars.{u, u, u} v).isLeftDerived).unit.app V)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h4
  have key : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R' R₃ _ _ e _ _
            (totalDerivedExtensionScalars.{u, u, u} e).functor
            (totalDerivedExtensionScalars.{u, u, u} e).comparison
            (totalDerivedExtensionScalars.{u, u, u} e).isLeftDerived).unit.app
            ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj V)) ≫
        ((ModuleCat.restrictScalars.{u} e).mapDerivedCategoryHomologyIso n).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} e).functor.obj
              ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj V)) ≫
          (ModuleCat.restrictScalars.{u} e).map
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
              ((squareComparison.{u, u} d e v t sqb).app V)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
            ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A' A₃ _ _ v _ _
              (totalDerivedExtensionScalars.{u, u, u} v).functor
              (totalDerivedExtensionScalars.{u, u, u} v).comparison
              (totalDerivedExtensionScalars.{u, u, u} v).isLeftDerived).unit.app V)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((derivedRestrictScalarsSquareIso.{u, u} d v e t sqb).hom.app
              ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj V)) ≫
          ((ModuleCat.restrictScalars.{u} e).mapDerivedCategoryHomologyIso n).hom.app
            ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory.obj
              ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj V)) := by
    rw [← h2, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      squareComparison_unit.{u, u} d e v t sqb V, CategoryTheory.Functor.map_comp,
      Category.assoc]
  rw [h1]
  refine Eq.trans (congrArg (fun q => (((ModuleCat.restrictScalars.{u} t
      ).mapDerivedCategoryHomologyIso n).hom.app
      ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj V)).hom q)
    (ConcreteCategory.congr_hom key z)) ?_
  refine Eq.trans (derivedRestrictScalarsSquareIso_homologyIso_apply d e v t sqb n
    ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj V)
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
        ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A' A₃ _ _ v _ _
          (totalDerivedExtensionScalars.{u, u, u} v).functor
          (totalDerivedExtensionScalars.{u, u, u} v).comparison
          (totalDerivedExtensionScalars.{u, u, u} v).isLeftDerived).unit.app V))).hom z)) ?_
  exact congrArg (fun q => (((ModuleCat.restrictScalars.{u} v
      ).mapDerivedCategoryHomologyIso n).hom.app
      ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj V)).hom q)
    (ConcreteCategory.congr_hom h4 z)

include sq sqb in
/-- **Two stacked squares on the germ generator of the flat localization of the base.** For `e`
flat, the Tag 065Z comparison of the outer rectangle on cohomology, taken at a morphism `Θ` out
of the merged extension of scalars and evaluated on the germ generator `1 ⊗ m₀` of the
`R₃`-localization, is the unit of the derived change-of-rings adjunction along `A' → A₃` applied
to the top square's comparison of `m₀`, pushed along `Θ`. -/
public theorem squareComparison_pasted_unit_one_tmul (he : e.Flat) (n : ℤ)
    (N₀ : DerivedCategory (ModuleCat.{u} A)) (Y : DerivedCategory (ModuleCat.{u} A₃))
    (Θ : (totalDerivedExtensionScalars.{u, u, u} (v.comp c)).functor.obj N₀ ⟶ Y)
    (m₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
      ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj
        ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.obj N₀))) :
    (((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom.app Y).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
          ((squareComparison.{u, u} a (e.comp b) (v.comp c) t
                (pastedSquare_comm a b c d e v t sq sqb)).app N₀ ≫
            (ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map Θ)).hom
          (((flatCompDerivedHomologyIso.{u, u} b e he n).app
              ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.obj N₀)).inv.hom
            ((1 : R₃) ⊗ₜ[R', e] m₀))) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A₃) n).map
          ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀ ≫ Θ)).hom
        ((((ModuleCat.restrictScalars.{u} v).mapDerivedCategoryHomologyIso n).hom.app
              ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj
                ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
            ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A' A₃ _ _ v _ _
              (totalDerivedExtensionScalars.{u, u, u} v).functor
              (totalDerivedExtensionScalars.{u, u, u} v).comparison
              (totalDerivedExtensionScalars.{u, u, u} v).isLeftDerived).unit.app
              ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))).hom
            ((((ModuleCat.restrictScalars.{u} d).mapDerivedCategoryHomologyIso n).hom.app
                  ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀)).hom
              (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
                ((squareComparison.{u, u} a b c d sq).app N₀)).hom m₀)))) := by
  have hnat_t := NatTrans.naturality
    ((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom
    ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀ ≫ Θ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat_t
  have hmor : ((flatCompDerivedHomologyIso.{u, u} b e he n).app
          ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.obj N₀)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
            ((squareComparison.{u, u} a (e.comp b) (v.comp c) t
                  (pastedSquare_comm a b c d e v t sq sqb)).app N₀ ≫
              (ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map Θ) ≫
          ((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom.app Y =
      (ModuleCat.extendScalars.{u, u, u} e).map
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
              ((squareComparison.{u, u} a b c d sq).app N₀)) ≫
          ((flatDerivedHomologyIso.{u, u} e he n).app
              ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj
                ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))).inv ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
                ((squareComparison.{u, u} d e v t sqb).app
                  ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀)) ≫
              ((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom.app
                  ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj
                    ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀)) ≫
                (ModuleCat.restrictScalars.{u} t).map
                  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A₃) n).map
                    ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀ ≫ Θ)) := by
    rw [CategoryTheory.Functor.map_comp
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n)
        ((squareComparison.{u, u} a (e.comp b) (v.comp c) t
          (pastedSquare_comm a b c d e v t sq sqb)).app N₀)
        ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map Θ),
      Category.assoc,
      reassoc_of% (squareComparison_pasted_flatComp_inv a b c d e v t sq sqb he n N₀),
      CategoryTheory.Functor.map_comp
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n)
        ((squareComparison.{u, u} d e v t sqb).app
          ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))
        ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀))]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n)
        ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀))
        ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map Θ),
      ← CategoryTheory.Functor.map_comp
        ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory)
        ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀) Θ,
      hnat_t]
  refine Eq.trans (ConcreteCategory.congr_hom hmor ((1 : R₃) ⊗ₜ[R', e] m₀)) ?_
  refine Eq.trans (congrArg
    (fun q => ((ModuleCat.restrictScalars.{u} t).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A₃) n).map
          ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀ ≫ Θ))).hom
      ((((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryHomologyIso n).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} v).functor.obj
              ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} R₃) n).map
            ((squareComparison.{u, u} d e v t sqb).app
              ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))).hom
          (((flatDerivedHomologyIso.{u, u} e he n).app
              ((ModuleCat.restrictScalars.{u} d).mapDerivedCategory.obj
                ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀))).inv.hom q))))
    (ModuleCat.ExtendScalars.map_tmul e
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((squareComparison.{u, u} a b c d sq).app N₀)) (1 : R₃) m₀)) ?_
  exact congrArg
    (fun q => ((ModuleCat.restrictScalars.{u} t).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A₃) n).map
        ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app N₀ ≫ Θ))).hom q)
    (squareComparison_unit_one_tmul d e v t sqb he n
      ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj N₀)
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((squareComparison.{u, u} a b c d sq).app N₀)).hom m₀))

end RingTheory.TorIndependence

end
