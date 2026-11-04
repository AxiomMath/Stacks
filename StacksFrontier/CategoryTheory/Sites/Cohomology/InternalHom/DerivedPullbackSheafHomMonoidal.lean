module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackMonoidalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackTensorIsoMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHomTranspose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.MonoidalHomComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.TransposeChangeOfTensor

/-!
# Stacks 07A4 against the tensorator of `f^*` applied termwise, on K-flat models

Let `h` be a morphism of ringed topoi presented by a morphism of sites whose pullback `h^*` is
exact and carries K-flat complexes to K-flat complexes. This file computes, at a pair of K-flat
complexes with flat terms, the pieces that compare the comparison of Stacks 07A4 with the
tensorator of `h^*` applied termwise
(`Stacks.Sheaves.DerivedPullback.pullbackToposMapDerivedMonoidal`), both read through the
comparison of the monoidal tensor product of Stacks 0FPT with the canonical derived tensor
product.

## Main results

* `AlgebraicGeometry.RingedSite.tensorComparison_comp_derivedTensorObjIso`: the two comparisons of
  the tensor product of Stacks 0FPT with the canonical derived tensor product agree.
* `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackTensorIso_inv_app_comp_modelLeft`: the two
  halves of the five-step chain of Stacks 07A4.
* `RingedToposSiteHom.map_monoidalTensorCanonicalIso_inv_comp_pullbackComparisonQ`,
  `monoidalTensorCanonicalIso_hom_comp_modelRight`,
  `monoidalTensorCanonicalIso_hom_comp_comparison_pullback`: the two halves read through the
  monoidal tensor product.
* `RingedToposSiteHom.transportedμ_eq_derivedPullbackTensorIsoInternal_inv_app_model`: on K-flat
  models with flat terms, the tensorator of `h^*` applied termwise, transported to `Lh^*`, is the
  comparison of Stacks 07A4.
* `RingedToposSiteHom.isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal`: the map of
  Stacks 08JF is invertible exactly when the comparison of the monoidal functor `h^*` with the
  derived internal Hom is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  monoidalCategoryMod symmetricCategoryMod CochainComplex.symmetricCategory monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u, u} Z) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

/-- The tensor comparison of Stacks 0FPT with the derived tensor product of Stacks 08J8,
followed by the identification of the latter with the canonical one, is the comparison of
the monoidal tensor product with the canonical derived tensor product. -/
theorem tensorComparison_comp_derivedTensorObjIso (A B : DerivedModules.{u, u, u} Z) :
    ((derivedMonoidalTensorComparison Z).hom.app A).app B ≫ (derivedTensorObjIso Z A B).hom =
      ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.O).hom.app A).app B := by
  rw [derivedMonoidalTensorComparison, interfaceTensorCanonicalIso_eq_derivedTensorFunctorIso,
    derivedTensorObjIso]
  simp [← NatTrans.comp_app]

/-- The inverse form of `tensorComparison_comp_derivedTensorObjIso`. -/
theorem derivedTensorObjIso_inv_comp_tensorComparison_inv (A B : DerivedModules.{u, u, u} Z) :
    (derivedTensorObjIso Z A B).inv ≫ ((derivedMonoidalTensorComparison Z).inv.app A).app B =
      ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.O).inv.app A).app B := by
  rw [derivedMonoidalTensorComparison, interfaceTensorCanonicalIso_eq_derivedTensorFunctorIso,
    derivedTensorObjIso]
  simp [← NatTrans.comp_app]

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (h : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy h).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : h.u.IsMorphismOfSites Y.J X.J) [PreservesFiniteLimits h.pullbackTopos]
  (hF : ∀ K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K →
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      ((h.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

/-- A natural transformation out of the tensor product, read on the uncurried bifunctor. -/
private lemma app_app_comp_uncurry_map {C : Type*} [Category C] [MonoidalCategory C]
    {G : C ⥤ C ⥤ C} (τ : curriedTensor C ⟶ G) {A A' B B' : C} (a : A ⟶ A') (b : B ⟶ B') :
    (τ.app A).app B ≫ (Functor.uncurry.obj G).map ((a, b) : ((A, B) : C × C) ⟶ (A', B')) =
      (a ⊗ₘ b) ≫ (τ.app A').app B' := by
  have h1 := congr_app (τ.naturality a) B
  have h2 := (τ.app A').naturality b
  simp only [curriedTensor_map_app, curriedTensor_obj_map, NatTrans.comp_app] at h1 h2
  rw [Functor.uncurry_obj_map]
  dsimp only
  rw [← reassoc_of% h1, ← h2, tensorHom_def, Category.assoc]

/-- `app_app_comp_uncurry_map` followed by a morphism. -/
private lemma app_app_comp_uncurry_map_assoc {C : Type*} [Category C] [MonoidalCategory C]
    {G : C ⥤ C ⥤ C} (τ : curriedTensor C ⟶ G) {A A' B B' Z : C} (a : A ⟶ A') (b : B ⟶ B')
    (t : (G.obj A').obj B' ⟶ Z) :
    (τ.app A).app B ≫ (Functor.uncurry.obj G).map ((a, b) : ((A, B) : C × C) ⟶ (A', B')) ≫ t =
      (a ⊗ₘ b) ≫ (τ.app A').app B' ≫ t := by
  rw [← Category.assoc, app_app_comp_uncurry_map, Category.assoc]

/-- The comparison of Stacks 07A4 at a pair of models: its inverse followed by the first half of
the five-step chain is the second half. -/
theorem derivedPullbackTensorIso_inv_app_comp_modelLeft
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h hmos).inv.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
      (derivedPullbackTensorModelLeft h hmos K L hK hL hflatK hflatL).hom =
      (derivedPullbackTensorModelRight h hmos K L hK hL hflatK hflatL).hom := by
  have e := derivedPullbackTensorIso_hom_app_model h hmos K L hK hL hflatK hflatL
  rw [← cancel_epi ((Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h hmos).hom.app
      (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)), Iso.hom_inv_id_app_assoc, e,
    derivedPullbackTensorModelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- (r2) The first half of the five-step chain of Stacks 07A4 through the monoidal tensor
product. -/
theorem map_monoidalTensorCanonicalIso_inv_comp_pullbackComparisonQ
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullback h).map
        (((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.O).inv.app
          (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L)) ≫
      (derivedPullback h).map (CochainComplex.KFlatMonoidal.derivedTensorIso
          (Stacks.SheafOfModules.DerivedMonoidal.Mod Y.O)
          (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.O) hK hL).hom ≫
      pullbackComparisonQ h (K ⊗ L) =
    (derivedPullbackTensorModelLeft h hmos K L hK hL hflatK hflatL).hom := by
  have e :=
    Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso_hom_app_app_comp_comparison
      Y.O K L hK hL
  have e' : (((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.O).inv.app
      (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L)) ≫
      (CochainComplex.KFlatMonoidal.derivedTensorIso
          (Stacks.SheafOfModules.DerivedMonoidal.Mod Y.O)
          (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.O) hK hL).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison K L
        hK hL).hom := by
    rw [← e]
    exact Iso.inv_hom_id_app_app_assoc _ _ _ _
  rw [← Functor.map_comp_assoc, e']
  rfl

/-- (r3) Through the monoidal tensor product, the second half of the five-step chain of
Stacks 07A4. -/
theorem monoidalTensorCanonicalIso_hom_comp_modelRight
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    (((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O).hom.app
          ((derivedPullback h).obj (DerivedCategory.Q.obj K))).app
        ((derivedPullback h).obj (DerivedCategory.Q.obj L))) ≫
      (derivedPullbackTensorModelRight h hmos K L hK hL hflatK hflatL).hom =
    (pullbackComparisonQ h K ⊗ₘ pullbackComparisonQ h L) ≫
      (((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O).hom.app
            (DerivedCategory.Q.obj ((KFlatPullback.pullbackComplex h).obj K))).app
        (DerivedCategory.Q.obj ((KFlatPullback.pullbackComplex h).obj L))) ≫
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((KFlatPullback.pullbackComplex h).obj K) ((KFlatPullback.pullbackComplex h).obj L)
        (kFlat_pullbackComplex' h hmos K hK hflatK)
        (kFlat_pullbackComplex' h hmos L hL hflatL)).hom ≫
      DerivedCategory.Q.map (pullbackToposTensorTotalIso h hmos K L).inv := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  exact app_app_comp_uncurry_map_assoc _ _ _ _

/-- (r4) The X-side reading: the canonical K-flat comparison is the monoidal comparison, and the
total comparison of Stacks 07A4 is the inverse tensorator of `f^*` applied termwise. -/
theorem monoidalTensorCanonicalIso_hom_comp_comparison_pullback
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    letI := pullbackToposMonoidal h hmos
    (((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O).hom.app
          (DerivedCategory.Q.obj ((KFlatPullback.pullbackComplex h).obj K))).app
        (DerivedCategory.Q.obj ((KFlatPullback.pullbackComplex h).obj L))) ≫
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((KFlatPullback.pullbackComplex h).obj K) ((KFlatPullback.pullbackComplex h).obj L)
        (kFlat_pullbackComplex' h hmos K hK hflatK)
        (kFlat_pullbackComplex' h hmos L hL hflatL)).hom ≫
      DerivedCategory.Q.map (pullbackToposTensorTotalIso h hmos K L).inv =
    (CochainComplex.KFlatMonoidal.derivedTensorIso
          (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)
          (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O)
          (hF K hK) (hF L hL)).hom ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.μ
          (h.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)) K L) := by
  let := pullbackToposMonoidal h hmos
  have hμ : Functor.LaxMonoidal.μ (h.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)) K L =
      (pullbackToposTensorTotalIso h hmos K L).inv := by
    rw [← cancel_mono (pullbackToposTensorTotalIso h hmos K L).hom, Iso.inv_hom_id]
    exact mapHomologicalComplex_μ_pullbackTopos_comp_pullbackToposTensorTotalIso_hom h hmos K L
  rw [hμ]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso_hom_app_app_comp_comparison
      X.O _ _ (kFlat_pullbackComplex' h hmos K hK hflatK)
      (kFlat_pullbackComplex' h hmos L hL hflatL)))


/-- The assembly of `tensorComparison_derivedPullbackTensorIsoInternal_inv_app`, applied as a
term so that every comparison of spellings is checked in the lemma it comes from. -/
private lemma r1_assemble {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {a b c : D} {x y z : C} (cX : a ⟶ b) (I : b ⟶ P.obj y) (cY : y ⟶ z) (dX : b ⟶ c)
    (Dinv : c ⟶ P.obj x) (dY : x ⟶ y) (mX : a ⟶ c) (mY : x ⟶ z)
    (hI : I = dX ≫ Dinv ≫ P.map dY) (hX : cX ≫ dX = mX) (hY : dY ≫ cY = mY) :
    cX ≫ I ≫ P.map cY = mX ≫ Dinv ≫ P.map mY := by
  rw [hI, ← hX, ← hY, Functor.map_comp]; simp only [Category.assoc]

/-- `RingedSite.tensorComparison_comp_derivedTensorObjIso` at the ringed site of a ringed topos,
with the monoidal tensor product spelled at the structure sheaf of the topos. -/
private theorem tensorComparison_comp_derivedTensorObjIso_toRingedSite
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite X)).hom.app A).app B ≫
      (RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite X) A B).hom =
    ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O).hom.app A).app B :=
  RingedSite.tensorComparison_comp_derivedTensorObjIso (RingedTopos.toRingedSite X) A B

/-- `RingedSite.derivedTensorObjIso_inv_comp_tensorComparison_inv` at the ringed site of a ringed
topos, with the monoidal tensor product spelled at the structure sheaf of the topos. -/
private theorem derivedTensorObjIso_inv_comp_tensorComparison_inv_toRingedSite
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite Y) A B).inv ≫
      ((RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite Y)).inv.app A).app B =
    ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.O).inv.app A).app B :=
  RingedSite.derivedTensorObjIso_inv_comp_tensorComparison_inv (RingedTopos.toRingedSite Y) A B

/-- `derivedPullbackTensorIsoInternal_inv_app` with the inverse of Stacks 07A4 applied at the
pair. -/
private theorem derivedPullbackTensorIsoInternal_inv_app_eq
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackTensorIsoInternal h hmos).inv.app (A, B) =
      (RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite X)
          ((derivedPullback h).obj A) ((derivedPullback h).obj B)).hom ≫
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h hmos).inv.app (A, B) ≫
          (derivedPullback h).map
            (RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite Y) A B).inv := by
  rw [derivedPullbackTensorIsoInternal_inv_app, Iso.app_inv]

/-- (r1) The comparison of Stacks 07A4 read at the derived tensor products of Stacks 08J8,
conjugated by the tensor comparisons of Stacks 0FPT, is the comparison of Stacks 07A4 conjugated
by the comparisons of the monoidal tensor product with the canonical derived tensor product. -/
theorem tensorComparison_derivedPullbackTensorIsoInternal_inv_app
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite X)).hom.app
          ((derivedPullback h).obj A)).app ((derivedPullback h).obj B) ≫
      (derivedPullbackTensorIsoInternal h hmos).inv.app (A, B) ≫
      (derivedPullback h).map
        (((RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite Y)).inv.app
          A).app B) =
    (((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O).hom.app
        ((derivedPullback h).obj A)).app ((derivedPullback h).obj B)) ≫
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h hmos).inv.app (A, B) ≫
      (derivedPullback h).map
        (((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.O).inv.app
          A).app B) :=
  r1_assemble (derivedPullback h) _ _ _ _ _ _ _ _
    (derivedPullbackTensorIsoInternal_inv_app_eq h hmos A B)
    (tensorComparison_comp_derivedTensorObjIso_toRingedSite ((derivedPullback h).obj A)
      ((derivedPullback h).obj B))
    (derivedTensorObjIso_inv_comp_tensorComparison_inv_toRingedSite A B)

/-- The left side of the crux on models: the transported tensorator, followed by the comparison
of `Lf^*(QK ⊗ QL)` with `Q(f^*(K ⊗ L))`. -/
theorem transportedμ_comp_model
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    letI := pullbackToposMapDerivedMonoidal h hmos hF
    letI := pullbackToposMonoidal h hmos
    (((derivedPullbackIsoMapDerived h).hom.app (DerivedCategory.Q.obj K) ⊗ₘ
        (derivedPullbackIsoMapDerived h).hom.app (DerivedCategory.Q.obj L)) ≫
      Functor.LaxMonoidal.μ (pullbackToposMapDerived h) (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) ≫
      (derivedPullbackIsoMapDerived h).inv.app
        (DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L)) ≫
      (derivedPullback h).map (CochainComplex.KFlatMonoidal.derivedTensorIso
          (Stacks.SheafOfModules.DerivedMonoidal.Mod Y.O)
          (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.O) hK hL).hom ≫
        pullbackComparisonQ h (K ⊗ L) =
    (pullbackComparisonQ h K ⊗ₘ pullbackComparisonQ h L) ≫
      (CochainComplex.KFlatMonoidal.derivedTensorIso
          (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)
          (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O)
          (hF K hK) (hF L hL)).hom ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.μ
        (h.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)) K L) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  let := pullbackToposMapDerivedMonoidal h hmos hF
  let := pullbackToposMonoidal h hmos
  rw [← derivedPullbackIsoMapDerived_hom_app_Q h (K ⊗ L), Category.assoc, Category.assoc,
    ← (derivedPullbackIsoMapDerived h).inv.naturality_assoc, Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryMonoidal_μ_Q h.pullbackTopos hF _ _ hK hL,
    ← derivedPullbackIsoMapDerived_hom_app_Q h K, ← derivedPullbackIsoMapDerived_hom_app_Q h L,
    ← tensorHom_comp_tensorHom_assoc]

/-- The assembly of the crux on models, applied as a term. -/
private lemma crux_assemble {D : Type*} [Category D]
    {S₀ S₁ S₂ S₃ S₄ E T₁ T₂ T₃ S₁' S₂' : D}
    (a : S₀ ⟶ S₁) (b : S₁ ⟶ S₂) (c : S₂ ⟶ S₃) (a' : S₀ ⟶ S₁') (b' : S₁' ⟶ S₂') (c' : S₂' ⟶ S₃)
    (t : S₃ ⟶ E) (lft : S₂' ⟶ E) (rgt : S₁' ⟶ E) (x : S₀ ⟶ S₄) (y : S₄ ⟶ T₁) (z : T₁ ⟶ T₂)
    (w : T₂ ⟶ E) (v : S₄ ⟶ T₃) (μ : T₃ ⟶ E) (lhs : S₀ ⟶ S₃)
    (hl : lhs ≫ t = x ≫ v ≫ μ) (r1 : a ≫ b ≫ c = a' ≫ b' ≫ c') (r2 : c' ≫ t = lft)
    (h07 : b' ≫ lft = rgt) (r3 : a' ≫ rgt = x ≫ y ≫ z ≫ w) (r4 : y ≫ z ≫ w = v ≫ μ) :
    lhs ≫ t = (a ≫ b ≫ c) ≫ t := by
  rw [hl, r1, Category.assoc, Category.assoc, r2, h07, r3, r4]

/-- **Stacks 07A4 is the tensorator of `f^*` applied termwise, on models.** At a pair of K-flat
complexes with flat terms, the tensorator of `f^*` applied termwise, transported to `Lf^*`
along `derivedPullbackIsoMapDerived`, is the comparison of Stacks 07A4 read at the derived
tensor products of Stacks 08J8, through the tensor comparisons of Stacks 0FPT. -/
theorem transportedμ_eq_derivedPullbackTensorIsoInternal_inv_app_model
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    letI := pullbackToposMapDerivedMonoidal h hmos hF
    ((derivedPullbackIsoMapDerived h).hom.app (DerivedCategory.Q.obj K) ⊗ₘ
        (derivedPullbackIsoMapDerived h).hom.app (DerivedCategory.Q.obj L)) ≫
      Functor.LaxMonoidal.μ (pullbackToposMapDerived h) (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) ≫
      (derivedPullbackIsoMapDerived h).inv.app (DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L) =
    ((RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite X)).hom.app
          ((derivedPullback h).obj (DerivedCategory.Q.obj K))).app
        ((derivedPullback h).obj (DerivedCategory.Q.obj L)) ≫
      (derivedPullbackTensorIsoInternal h hmos).inv.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
      (derivedPullback h).map
        (((RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite Y)).inv.app
          (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L)) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  let := pullbackToposMapDerivedMonoidal h hmos hF
  have : IsIso (pullbackComparisonQ h (K ⊗ L)) :=
    (flatPullbackIso h hmos (K ⊗ L) (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
      (isFlat_tensorComplex_X Y.O K L hflatK hflatL)).isIso_hom
  rw [← cancel_mono ((derivedPullback h).map (CochainComplex.KFlatMonoidal.derivedTensorIso
          (Stacks.SheafOfModules.DerivedMonoidal.Mod Y.O)
          (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.O) hK hL).hom ≫
        pullbackComparisonQ h (K ⊗ L))]
  exact crux_assemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (transportedμ_comp_model h hmos hF K L hK hL hflatK hflatL)
    (tensorComparison_derivedPullbackTensorIsoInternal_inv_app h hmos _ _)
    (map_monoidalTensorCanonicalIso_inv_comp_pullbackComparisonQ h hmos K L hK hL hflatK hflatL)
    (derivedPullbackTensorIso_inv_app_comp_modelLeft h hmos K L hK hL hflatK hflatL)
    (monoidalTensorCanonicalIso_hom_comp_modelRight h hmos K L hK hL hflatK hflatL)
    (monoidalTensorCanonicalIso_hom_comp_comparison_pullback h hmos hF K L hK hL hflatK hflatL)

/-- **Natural transformations on pairs of objects of `D(O')` are determined on pairs of K-flat
complexes with flat terms**: every object of `D(O')` is isomorphic to the image of such a
complex. -/
theorem natTrans_ext_flatKFlatModels {E : Type*} [Category E]
    {G₁ G₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤ E}
    (α β : G₁ ⟶ G₂)
    (hαβ : ∀ (K L : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
      (_ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
      (_ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
      (_ : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
      (_ : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)),
      α.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
        β.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) :
    α = β := by
  have := flatKFlatModelsQ_isLocalization Y
  have hess := Localization.essSurj (flatKFlatModelsQ Y) (flatKFlatModelsW Y)
  ext ⟨A, B⟩
  obtain ⟨PA, ⟨eA⟩⟩ := hess.mem_essImage A
  obtain ⟨PB, ⟨eB⟩⟩ := hess.mem_essImage B
  let iA : DerivedCategory.Q.obj PA.obj.as ≅ A :=
    ((DerivedCategory.quotientCompQhIso _).app PA.obj.as).symm ≪≫ eA
  let iB : DerivedCategory.Q.obj PB.obj.as ≅ B :=
    ((DerivedCategory.quotientCompQhIso _).app PB.obj.as).symm ≪≫ eB
  let i : ((DerivedCategory.Q.obj PA.obj.as, DerivedCategory.Q.obj PB.obj.as) : _ × _) ≅ (A, B) :=
    Iso.prod iA iB
  rw [← cancel_epi (G₁.map i.hom), α.naturality, β.naturality,
    hαβ _ _ PA.property.1 PB.property.1 PA.property.2 PB.property.2]

/-- The tensorator of `Lf^*` transported from `f^*` applied termwise, against the comparison of
Stacks 07A4 conjugated by the tensor comparisons, as natural transformations. -/
private lemma transportedμ_natTrans_eq :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    letI := pullbackToposMapDerivedMonoidal h hmos hF
    letI : (derivedPullback h).Monoidal :=
      Functor.Monoidal.transport (derivedPullbackIsoMapDerived h).symm
    (RingedSite.monoidalTensorIso (X := RingedTopos.toRingedSite Y)
        (Y := RingedTopos.toRingedSite X) (derivedPullback h)).inv =
      Functor.whiskerLeft ((derivedPullback h).prod (derivedPullback h))
          (Functor.uncurry.map
            (RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite X)).hom) ≫
        (derivedPullbackTensorIsoInternal h hmos).inv ≫
          Functor.whiskerRight (Functor.uncurry.map
            (RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite Y)).inv)
            (derivedPullback h) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  let := pullbackToposMapDerivedMonoidal h hmos hF
  let : (derivedPullback h).Monoidal :=
    Functor.Monoidal.transport (derivedPullbackIsoMapDerived h).symm
  refine natTrans_ext_flatKFlatModels _ _ (fun K L hK hL hflatK hflatL => ?_)
  exact transportedμ_eq_derivedPullbackTensorIsoInternal_inv_app_model h hmos hF K L hK hL
    hflatK hflatL

/-- **The map of Stacks 08JF is invertible exactly when the comparison of the monoidal functor
`f^*` applied termwise is.** For `h` presented by a morphism of sites with `h^*` exact and
preserving K-flat complexes, the canonical map `Lh^* RSheafHom(E, F) ⟶ RSheafHom(Lh^* E, Lh^* F)`
of Stacks 08JF is, up to the isomorphism `Lh^* ≅ h^*` of `derivedPullbackIsoMapDerived`, the
comparison `RingedSite.homComparisonMonoidal` of `h^*` with its monoidal structure
`pullbackToposMapDerivedMonoidal`. -/
theorem isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal
    (E F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    letI := pullbackToposMapDerivedMonoidal h hmos hF
    IsIso (derivedPullbackSheafHomMap h hmos E F) ↔
      IsIso (RingedSite.homComparisonMonoidal (X := RingedTopos.toRingedSite Y)
        (Y := RingedTopos.toRingedSite X) (pullbackToposMapDerived h) E F) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  let := pullbackToposMapDerivedMonoidal h hmos hF
  let : (derivedPullback h).Monoidal :=
    Functor.Monoidal.transport (derivedPullbackIsoMapDerived h).symm
  have : NatTrans.IsMonoidal (derivedPullbackIsoMapDerived h).symm.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport _
  have hnat := transportedμ_natTrans_eq h hmos hF
  have h1 : derivedPullbackSheafHomMap h hmos E F =
      RingedSite.homComparisonMonoidal (X := RingedTopos.toRingedSite Y)
        (Y := RingedTopos.toRingedSite X) (derivedPullback h) E F := by
    rw [derivedPullbackSheafHomMap_eq_homComparison, RingedSite.homComparisonMonoidal]
    refine (Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_changeOfTensor
      _ _ _ _ _ _ _ _ _ (Functor.uncurry.mapIso
        (RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite Y)).symm)
      (Functor.uncurry.mapIso
        (RingedSite.derivedMonoidalTensorComparison (RingedTopos.toRingedSite X)).symm)
      (fun A B C g => ?_) (fun A B C g => ?_) (fun A B => ?_) E F).symm
    · exact RingedSite.monoidalCurryEquiv_apply _ A B C g
    · exact RingedSite.monoidalCurryEquiv_apply _ A B C g
    · exact congr_app hnat (A, B)
  have h2 := RingedSite.homComparisonMonoidal_congr (X := RingedTopos.toRingedSite Y)
    (Y := RingedTopos.toRingedSite X) (derivedPullbackIsoMapDerived h).symm E F
  rw [h1, show RingedSite.homComparisonMonoidal (X := RingedTopos.toRingedSite Y)
      (Y := RingedTopos.toRingedSite X) (derivedPullback h) E F = _ from h2]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

end AlgebraicGeometry.RingedToposSiteHom

end
