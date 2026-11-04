module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineBaseInduction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackNatTransAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompIsoLeftApp

/-!
# Pulling back the comparison datum of a complex

For a morphism of ringed spaces `g' : X' ⟶ X` and a complex `W` of `𝒪_X`-modules, the comparison
`L(g')^*W ⟶ (g')^*W` of the derived with the degreewise pullback is a datum `(W, (g')^*W, φ)` of
the kind the base-change composition `Lg^*Rf_*W ⟶ Rf'_*(g')^*W` is built from. Pulled back along
a commutative square `gZ ≫ j = j' ≫ g'` whose vertical arrows `j`, `j'` have invertible
comparisons (open immersions, for instance), it is isomorphic to the comparison datum of `j^*W`
along `gZ`.

## Main results

* `Stacks.Cohomology.BaseChangeCover.isIso_bc_pullDatum_comparison_iff`: the base-change
  composition at the pulled-back comparison datum is invertible exactly when it is at the
  comparison datum of the pullback.
* `Stacks.Cohomology.BaseChangeCover.isIso_derivedPullbackNatTrans_app_of_isOpenImmersion`: along
  an open immersion the derived pullback of every complex is its degreewise pullback.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.BaseChangeCover

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Presheaf.IsSheaf TopCat.Sheaf

/-- Along an open immersion the derived pullback of every complex is its degreewise pullback. -/
theorem isIso_derivedPullbackNatTrans_app_of_isOpenImmersion {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) [SheafedSpace.IsOpenImmersion f]
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso ((derivedPullbackNatTrans f).app K) := by
  have := isIso_derivedPullbackComparison_of_isOpenImmersion f
  have : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := inferInstance
  dsimp only [derivedPullbackNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- The comparison of the derived with the degreewise pullback, transported along an equality of
morphisms. -/
theorem derivedPullbackNatTrans_app_congr {X Y : RingedSpace.{u, u}} {a b : X ⟶ Y} (e : a = b)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    eqToHom (congrArg (fun q : X ⟶ Y => (derivedPullback q).obj (DerivedCategory.Q.obj W)) e) ≫
        (derivedPullbackNatTrans b).app W =
      (derivedPullbackNatTrans a).app W ≫
        DerivedCategory.Q.map
          (eqToHom (congrArg (fun q : X ⟶ Y => (pullbackComplex q).obj W) e)) := by
  subst e
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- In a category, `A ≫ B = c₁ ≫ E ≫ c₂i ≫ A' ≫ B' ≫ sq` for morphisms satisfying the relations
`h₁`, `h₂`, `h₃`, the retractions `hc`, `hp`, `hT` and the factorization `hsq`. -/
theorem pullDatum_chase {C : Type*} [Category C] {L₀ L₁ L₂ L₃ L₄ D₁ D₂ D₃ D₄ D₅ : C}
    (A : L₀ ⟶ L₁) (B : L₁ ⟶ D₁) (c₁ : L₀ ⟶ L₂) (Na : L₂ ⟶ D₂) (p₁h : D₁ ⟶ D₂) (p₁i : D₂ ⟶ D₁)
    (E : L₂ ⟶ L₃) (c₂i : L₃ ⟶ L₄) (c₂h : L₄ ⟶ L₃) (A' : L₄ ⟶ D₃) (B' : D₃ ⟶ D₄)
    (Nb : L₃ ⟶ D₅) (p₂h : D₄ ⟶ D₅) (T : D₂ ⟶ D₅) (T' : D₅ ⟶ D₂) (sq : D₄ ⟶ D₁)
    (h₁ : c₁ ≫ Na = A ≫ B ≫ p₁h) (h₂ : c₂h ≫ Nb = A' ≫ B' ≫ p₂h) (h₃ : E ≫ Nb = Na ≫ T)
    (hc : c₂i ≫ c₂h = 𝟙 _) (hp : p₁h ≫ p₁i = 𝟙 _) (hT : T ≫ T' = 𝟙 _)
    (hsq : sq = p₂h ≫ T' ≫ p₁i) :
    A ≫ B = c₁ ≫ E ≫ c₂i ≫ A' ≫ B' ≫ sq := by
  have h₂' : c₂i ≫ A' ≫ B' ≫ p₂h = Nb := by rw [← h₂, reassoc_of% hc]
  calc A ≫ B = (A ≫ B ≫ p₁h) ≫ p₁i := by simp only [Category.assoc, hp, Category.comp_id]
    _ = c₁ ≫ (E ≫ Nb) ≫ T' ≫ p₁i := by
        rw [← h₁, h₃, Category.assoc, Category.assoc, reassoc_of% hT]
    _ = c₁ ≫ E ≫ c₂i ≫ A' ≫ B' ≫ sq := by
        rw [hsq, ← h₂']; simp only [Category.assoc]

/-- In a category, `c₁ ≫ E ≫ c₂i ≫ A' ≫ R = pd ≫ R` whenever `L ≫ A' = E ≫ c₂i ≫ A'` and
`pd = c₁ ≫ L ≫ A'`. -/
theorem pullDatum_chase₂ {C : Type*} [Category C] {L₀ L₂ L₃ L₄ D₃ D : C}
    (c₁ : L₀ ⟶ L₂) (E : L₂ ⟶ L₃) (c₂i : L₃ ⟶ L₄) (A' : L₄ ⟶ D₃) (R : D₃ ⟶ D) (L : L₂ ⟶ L₄)
    (pd : L₀ ⟶ D₃) (h₄ : L ≫ A' = E ≫ c₂i ≫ A') (hpd : pd = c₁ ≫ L ≫ A') :
    c₁ ≫ E ≫ c₂i ≫ A' ≫ R = pd ≫ R := by
  rw [hpd, ← reassoc_of% h₄]
  simp only [Category.assoc]

variable {Z' Z X' X : RingedSpace.{u, u}} (gZ : Z' ⟶ Z) (j' : Z' ⟶ X') (j : Z ⟶ X)
  (g' : X' ⟶ X) (w : gZ ≫ j = j' ≫ g')

/-- The degreewise pullback of a complex around a commutative square. -/
def pullbackComplexSquareIso
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (pullbackComplex j').obj ((pullbackComplex g').obj W) ≅
      (pullbackComplex gZ).obj ((pullbackComplex j).obj W) :=
  (Stacks.PullbackTensorComposition.pullbackComplexCompIso j' g').app W ≪≫
    eqToIso (congrArg (fun q : Z' ⟶ X => (pullbackComplex q).obj W) w.symm) ≪≫
    ((Stacks.PullbackTensorComposition.pullbackComplexCompIso gZ j).app W).symm

/-- **The pulled-back comparison datum is the comparison datum of the pullback.** -/
theorem derivedPullback_map_comp_derivedPullbackNatTrans_eq_pullDatum
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (derivedPullback gZ).map ((derivedPullbackNatTrans j).app W) ≫
        (derivedPullbackNatTrans gZ).app ((pullbackComplex j).obj W) =
      pullDatum gZ j' j g' w (DerivedCategory.Q.obj W)
          (DerivedCategory.Q.obj ((pullbackComplex g').obj W))
          ((derivedPullbackNatTrans g').app W) ≫
        (derivedPullbackNatTrans j').app ((pullbackComplex g').obj W) ≫
          DerivedCategory.Q.map (pullbackComplexSquareIso gZ j' j g' w W).hom := by
  have h₁ :=
    DerivedPullbackTensor.derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans
      gZ j W
  have h₂ :=
    DerivedPullbackTensor.derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans
      j' g' W
  have h₃ := derivedPullbackNatTrans_app_congr w W
  have h₄ := derivedPullbackCompIsoLeft_inv_app_comp g' j j' gZ w (DerivedCategory.Q.obj W)
    (DerivedCategory.Q.obj ((pullbackComplex g').obj W)) ((derivedPullbackNatTrans g').app W)
  refine (pullDatum_chase _ _ _ _ _
    (DerivedCategory.Q.map
      ((Stacks.PullbackTensorComposition.pullbackComplexCompIso gZ j).inv.app W))
    _ _ _ _ _ _ _ _
    (DerivedCategory.Q.map
      (eqToHom (congrArg (fun q : Z' ⟶ X => (pullbackComplex q).obj W) w.symm)))
    (DerivedCategory.Q.map (pullbackComplexSquareIso gZ j' j g' w W).hom)
    h₁ h₂ h₃ (Iso.inv_hom_id_app _ _) ?_ ?_ ?_).trans ?_
  · rw [← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app]
    exact DerivedCategory.Q.map_id _
  · rw [← DerivedCategory.Q.map_comp, eqToHom_trans, eqToHom_refl]
    exact DerivedCategory.Q.map_id _
  · rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    refine congrArg DerivedCategory.Q.map ?_
    simp only [pullbackComplexSquareIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
      eqToIso.hom]
  · exact pullDatum_chase₂ _ _ _ _ _ _ _ h₄
      (pullDatum_eq gZ j' j g' w (DerivedCategory.Q.obj W)
        (DerivedCategory.Q.obj ((pullbackComplex g').obj W)) ((derivedPullbackNatTrans g').app W))

/-- **The base-change composition at the pulled-back comparison datum** is invertible exactly when
it is at the comparison datum of the pullback, as soon as the comparisons along the two vertical
arrows of the square are invertible. -/
theorem isIso_bc_pullDatum_comparison_iff {T' T : RingedSpace.{u, u}} (fW' : Z' ⟶ T')
    (fW : Z ⟶ T) (gT : T' ⟶ T) (hq : gZ ≫ fW = fW' ≫ gT)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (hj : IsIso ((derivedPullbackNatTrans j).app W))
    (hj' : IsIso ((derivedPullbackNatTrans j').app ((pullbackComplex g').obj W))) :
    IsIso (derivedBaseChangeMap gZ fW' fW gT hq
        ((derivedPullback j).obj (DerivedCategory.Q.obj W)) ≫
      (derivedPushforward fW').map (pullDatum gZ j' j g' w (DerivedCategory.Q.obj W)
          (DerivedCategory.Q.obj ((pullbackComplex g').obj W))
          ((derivedPullbackNatTrans g').app W))) ↔
    IsIso (derivedBaseChangeMap gZ fW' fW gT hq
        (DerivedCategory.Q.obj ((pullbackComplex j).obj W)) ≫
      (derivedPushforward fW').map
        ((derivedPullbackNatTrans gZ).app ((pullbackComplex j).obj W))) := by
  have hv : IsIso ((derivedPullbackNatTrans j').app ((pullbackComplex g').obj W) ≫
      DerivedCategory.Q.map (pullbackComplexSquareIso gZ j' j g' w W).hom) := inferInstance
  exact @isIso_bc_iff_of_iso _ _ _ _ gZ fW' fW gT hq _ _ _ _ _ _ _ _ hj hv
    (derivedPullback_map_comp_derivedPullbackNatTrans_eq_pullDatum gZ j' j g' w W)

/-- The comparison of the derived with the degreewise pullback is the comparison on the homotopy
category, composed with the isomorphisms `quotient ⋙ Qh ≅ Q` and the commutation of the degreewise
pullback with the quotient functor. -/
theorem derivedPullbackNatTrans_app_eq_comparison {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (derivedPullbackNatTrans h).app W =
      (derivedPullback h).map ((DerivedCategory.quotientCompQhIso _).inv.app W) ≫
        (derivedPullbackComparison h).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map
          (((RingedSpaceModuleAdjunction.modulePullback h).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app W) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app ((pullbackComplex h).obj W) :=
  rfl

/-- **The base-change composition at the comparison datum of `W`** is invertible exactly when it
is at the comparison on the homotopy category of the class of `W`. -/
theorem isIso_bc_derivedPullbackNatTrans_iff {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    IsIso (derivedBaseChangeMap g' f' f g sq (DerivedCategory.Q.obj W) ≫
      (derivedPushforward f').map ((derivedPullbackNatTrans g').app W)) ↔
    IsIso (derivedBaseChangeMap g' f' f g sq
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W)) ≫
      (derivedPushforward f').map ((derivedPullbackComparison g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W))) := by
  have hu : IsIso ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).inv.app W) := inferInstance
  have hv : IsIso ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X')).inv.app
        ((pullbackComplex g').obj W) ≫
      DerivedCategory.Qh.map
        (((RingedSpaceModuleAdjunction.modulePullback g').mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app W)) := inferInstance
  refine @isIso_bc_iff_of_iso _ _ _ _ g' f' f g sq _ _ _ _ _ _ _ _ hu hv ?_
  rw [derivedPullbackNatTrans_app_eq_comparison]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact congrArg (fun t => _ ≫ _ ≫ t) (DerivedCategory.Qh.map_id _) |>.trans
    (congrArg (fun t => _ ≫ t) (Category.comp_id _)) |>.symm

/-- **The comparison datum depends on the complex only up to isomorphism.** -/
theorem isIso_bc_derivedPullbackNatTrans_iff_of_iso {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    {W₁ W₂ : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ}
    (α : W₁ ≅ W₂) :
    IsIso (derivedBaseChangeMap g' f' f g sq (DerivedCategory.Q.obj W₁) ≫
      (derivedPushforward f').map ((derivedPullbackNatTrans g').app W₁)) ↔
    IsIso (derivedBaseChangeMap g' f' f g sq (DerivedCategory.Q.obj W₂) ≫
      (derivedPushforward f').map ((derivedPullbackNatTrans g').app W₂)) := by
  have hu : IsIso (DerivedCategory.Q.map α.hom) := inferInstance
  have hv : IsIso (DerivedCategory.Q.map ((pullbackComplex g').map α.hom)) := inferInstance
  exact @isIso_bc_iff_of_iso _ _ _ _ g' f' f g sq _ _ _ _ _ _ _ _ hu hv
    ((derivedPullbackNatTrans g').naturality α.hom)

/-- The comparison of Stacks 01CD for total tensor complexes, at a pair of complexes. -/
def pullbackMapBifunctorIso {Y Z : RingedSpace.{u, u}} (h : Z ⟶ Y)
    (P G : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackComplex h).obj (HomologicalComplex.mapBifunctor P G
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((pullbackComplex h).obj P) ((pullbackComplex h).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) (ComplexShape.up ℤ) :=
  (Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso h).app (P, G)

end Stacks.Cohomology.BaseChangeCover
