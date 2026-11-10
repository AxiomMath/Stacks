module

public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.MappingCocone
import all StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.TelescopeHom
import all StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.MappingCocone

/-!
# The derived-limit model for `RHom_A(A_f, K)`

This part identifies the Hom complex out of the telescope resolution with the mapping cocone of
the constant product difference, deduces that `RHom_A(A_f, K)` is a derived limit of the constant
tower with transition maps `f`, compares its homology with `Ext_A(A_f, K)`, and reduces Ext
vanishing to vanishing of this derived limit.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace DerivedHomAway

attribute [local instance] instHasExactLimitsOfShapeDiscreteNatModuleCat_stacksFrontier
attribute [local instance] instHasProductsOfShapeNatDerivedCategoryModuleCat_stacksFrontier

private noncomputable def coconeRawFirst
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n) :
    ℕ → I.X (n - 1) :=
  (constantProductXIso A I (n - 1)).hom
    ((biprod.snd :
      ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
        (∏ᶜ fun _ : ℕ => I).X (n - 1)).hom
      ((constantDifferenceCoconeXIso A f I n).hom x))

private noncomputable def coconeRawSecond
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n) :
    ℕ → I.X n :=
  (constantProductXIso A I n).hom
    ((biprod.fst :
      ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
        (∏ᶜ fun _ : ℕ => I).X n).hom
      ((constantDifferenceCoconeXIso A f I n).hom x))

private theorem degree_cast_smul
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (j k : ℤ) (h : j = k) (a : ℤˣ) (x : I.X j) :
    cast (congrArg (fun degree : ℤ => (I.X degree : Type u)) h) (a • x) =
      a • cast (congrArg (fun degree : ℤ => (I.X degree : Type u)) h) x := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem coconeToHom_first_component_cast
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (y : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X (n + 1))
    (index : ℕ) :
    ((telescopeHom_next_index_iso A I n).hom
      ((coconeToHomPairComponentIso A f I (n + 1)).hom y)).1 index =
    (n + 2).negOnePow •
      cast (congrArg (fun degree : ℤ => (I.X degree : Type u))
        (show n + 1 - 1 = n by omega))
        (coconeRawFirst A f I (n + 1) y index) := by
  rw [telescopeHom_next_index_iso_fst]
  change cast (congrArg (fun degree : ℤ => (I.X degree : Type u))
    (show n + 1 - 1 = n by omega))
      (((coconeToHomPairComponentIso A f I (n + 1)).hom y).1 index) = _
  rw [coconeToHomPairComponentIso_fst]
  simpa [coconeRawFirst, add_assoc] using
    degree_cast_smul A I (n + 1 - 1) n (by omega)
      (n + 2).negOnePow (coconeRawFirst A f I (n + 1) y index)

private theorem coconeRawFirst_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n)
    (index : ℕ) :
    cast (congrArg (fun degree : ℤ => (I.X degree : Type u))
      (show n + 1 - 1 = n by omega))
      (coconeRawFirst A f I (n + 1)
        (((CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
          n (n + 1)).hom x) index) =
    -(coconeRawSecond A f I n x index -
        f • coconeRawSecond A f I n x (index + 1) +
      (I.d (n - 1) n).hom (coconeRawFirst A f I n x index)) := by
  unfold coconeRawFirst coconeRawSecond
  rw [constantProductXIso_cast A I (n + 1 - 1) n (by omega)]
  have h := congrArg
    (fun ψ : (CochainComplex.mappingCocone
      (constantProductDifferenceComplex A f I)).X n ⟶
        (∏ᶜ fun _ : ℕ => I).X n =>
      ((constantProductXIso A I n).hom (ψ.hom x)) index)
    (mappingCoconeXIso_d_snd A f I n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_neg, ModuleCat.hom_add,
    LinearMap.neg_apply, LinearMap.add_apply] at h
  rw [h]
  simp only [map_neg, map_add, Pi.neg_apply, Pi.add_apply]
  rw [constantProductDifferenceComplex_point A f I n
    ((biprod.fst :
      ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
        (∏ᶜ fun _ : ℕ => I).X n).hom
      ((constantDifferenceCoconeXIso A f I n).hom x)) index]
  let second : (∏ᶜ fun _ : ℕ => I).X (n - 1) :=
    (biprod.snd :
      ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
        (∏ᶜ fun _ : ℕ => I).X (n - 1)).hom
      ((constantDifferenceCoconeXIso A f I n).hom x)
  have hd : ((constantProductXIso A I n).hom
      (((∏ᶜ fun _ : ℕ => I).d (n - 1) n).hom second)) index =
      (I.d (n - 1) n).hom (((constantProductXIso A I (n - 1)).hom second) index) := by
    exact constantProductXIso_d_at A I (n - 1) n (by omega) second index
  rw [hd]

private theorem signed_raw_normalize
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (v w : I.X n) (r : I.X (n - 1)) :
    (n + 2).negOnePow •
      (-(v - f • w + (I.d (n - 1) n).hom r)) =
    (I.d (n - 1) n).hom ((n + 1).negOnePow • r) +
      (n + 1).negOnePow • (v - f • w) := by
  have hsign (x : I.X n) :
      (n + 2).negOnePow • (-x) = (-(n + 2).negOnePow) • x := by
    simp [Units.smul_def]
  rw [hsign, (coconeSign n).2]
  simp only [Units.smul_def, smul_add, map_zsmul]
  abel

private theorem coconeToHom_first_differential_normalized
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n)
    (index : ℕ) :
    ((telescopeHom_next_index_iso A I n).hom
      ((coconeToHomPairComponentIso A f I (n + 1)).hom
        (((CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
          n (n + 1)).hom x))).1 index =
    (I.d (n - 1) n).hom (((coconeToHomPairComponentIso A f I n).hom x).1 index) +
      (n + 1).negOnePow •
        (((coconeToHomPairComponentIso A f I n).hom x).2 index -
          f • ((coconeToHomPairComponentIso A f I n).hom x).2 (index + 1)) := by
  rw [coconeToHom_first_component_cast]
  rw [coconeRawFirst_differential]
  have hfirst : ((coconeToHomPairComponentIso A f I n).hom x).1 index =
      (n + 1).negOnePow • coconeRawFirst A f I n x index := by
    simpa only [coconeRawFirst] using coconeToHomPairComponentIso_fst A f I n x index
  have hsecond : ((coconeToHomPairComponentIso A f I n).hom x).2 index =
      coconeRawSecond A f I n x index := by
    simpa only [coconeRawSecond] using coconeToHomPairComponentIso_snd A f I n x index
  have hsecondNext : ((coconeToHomPairComponentIso A f I n).hom x).2 (index + 1) =
      coconeRawSecond A f I n x (index + 1) := by
    simpa only [coconeRawSecond] using
      coconeToHomPairComponentIso_snd A f I n x (index + 1)
  rw [signed_raw_normalize A f I n
    (coconeRawSecond A f I n x index)
    (coconeRawSecond A f I n x (index + 1))
    (coconeRawFirst A f I n x index)]
  rw [← hfirst, ← hsecond, ← hsecondNext]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def coconeToHomPairComplexIso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex.mappingCocone (constantProductDifferenceComplex A f I) ≅
      telescopeHom_transport_complex A f I := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => coconeToHomPairComponentIso A f I n) ?_
  intro i j hij
  simp only [ComplexShape.up_Rel] at hij
  subst j
  apply (cancel_mono (telescopeHom_next_index_iso A I i).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let z : (HomComplexR A (telescopeResolution A f) I).X i :=
    (telescopeHom_component_iso A f I i).inv.hom
      ((coconeToHomPairComponentIso A f I i).hom x)
  have hz : (telescopeHom_component_iso A f I i).hom z =
      (coconeToHomPairComponentIso A f I i).hom x := by
    simp [z]
  have hp : (telescopeHom_product_equiv A f I i) z =
      (coconeToHomPairComponentIso A f I i).hom x := by
    change (telescopeHom_component_iso A f I i).hom z = _
    exact hz
  apply Prod.ext
  · funext index
    have ht := transportHom_first_differential A f I i z index
    have hc := coconeToHom_first_differential_normalized A f I i x index
    rw [hz, hp] at ht
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change ((telescopeHom_next_index_iso A I i).hom
      (((telescopeHom_transport_complex A f I).d i (i + 1)).hom
        ((coconeToHomPairComponentIso A f I i).hom x))).1 index =
      ((telescopeHom_next_index_iso A I i).hom
        ((coconeToHomPairComponentIso A f I (i + 1)).hom
          (((CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
            i (i + 1)).hom x))).1 index
    exact ht.trans hc.symm
  · funext index
    have ht := transportHom_second_differential A f I i z index
    have hc := coconeToHom_second_differential A f I i x index
    rw [hz, hp] at ht
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change ((telescopeHom_next_index_iso A I i).hom
      (((telescopeHom_transport_complex A f I).d i (i + 1)).hom
        ((coconeToHomPairComponentIso A f I i).hom x))).2 index =
      ((telescopeHom_next_index_iso A I i).hom
        ((coconeToHomPairComponentIso A f I (i + 1)).hom
          (((CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
            i (i + 1)).hom x))).2 index
    rw [telescopeHom_next_index_iso_snd,
      telescopeHom_next_index_iso_snd]
    exact ht.trans hc.symm

private noncomputable def coconeToHomComplexIso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex.mappingCocone (constantProductDifferenceComplex A f I) ≅
      HomComplexR A (telescopeResolution A f) I :=
  (coconeToHomPairComplexIso A f I).trans
    (telescopeHom_transport_iso A f I).symm

private noncomputable def derivedHomToDifferenceCoconeIso
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (I : CochainComplex (ModuleCat.{u} A) ℤ) [I.IsKInjective]
    (eI : K ≅ DerivedCategory.Q.obj I) :
    DerivedHomAway.derivedHomFromAway A f K ≅
      DerivedCategory.Q.obj
        (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)) :=
  (homTelescopeIso A f K I eI).trans
    (DerivedCategory.Q.mapIso (coconeToHomComplexIso A f I).symm)

/-- The difference map of the constant tower, with the transition map `f • 𝟙` made explicit. -/
private theorem pi_lift_sub_comp_smul_id
    (A : Type u) [CommRing A] (f : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => K) n - Pi.π (fun _ : ℕ => K) (n + 1) ≫ (f • 𝟙 K)) =
    Pi.lift fun n : ℕ => Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1) := by
  apply Pi.hom_ext
  intro n
  simp only [Pi.lift_comp_π, Linear.comp_smul, Category.comp_id]

/-- Every object of the derived category is isomorphic to a K-injective complex. -/
private theorem exists_isKInjective_iso
    (A : Type u) [CommRing A] (K : DerivedCategory (ModuleCat.{u} A)) :
    ∃ I : CochainComplex (ModuleCat.{u} A) ℤ, I.IsKInjective ∧
      Nonempty (K ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨I, comparison, hComparison, hInjective⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage K)
  let := hComparison
  exact ⟨I, hInjective, ⟨(DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    asIso (DerivedCategory.Q.map comparison)⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem differenceCocone_isDerivedLimit
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsDerivedLimit
      (Functor.ofOpSequence (X := fun _ : ℕ => DerivedCategory.Q.obj I)
        (fun _ => f • 𝟙 (DerivedCategory.Q.obj I)))
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I))) := by
  let φ := constantProductDifferenceComplex A f I
  let productIso := constantProductDerivedIso A I
  let triangle := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle φ)
  let difference := Pi.lift (fun index : ℕ =>
    Pi.π (fun _ : ℕ => DerivedCategory.Q.obj I) index -
      f • Pi.π (fun _ : ℕ => DerivedCategory.Q.obj I) (index + 1))
  let p := triangle.mor₁ ≫ productIso.hom
  let δ := productIso.inv ≫ triangle.mor₃
  refine ⟨p, δ, ?_⟩
  have hdist : triangle ∈ distTriang _ := by
    exact DerivedCategory.mappingCocone_triangle_distinguished φ
  have hdiff : productIso.hom ≫ difference = triangle.mor₂ ≫ productIso.hom := by
    change productIso.hom ≫ difference =
      DerivedCategory.Q.map φ ≫ productIso.hom
    have h := constantProductDifferenceDerived_square A f I
    change productIso.inv ≫ DerivedCategory.Q.map φ ≫ productIso.hom = difference at h
    rw [← h]
    simp
  simp only [Functor.ofOpSequence_map_homOfLE_succ]
  erw [pi_lift_sub_comp_smul_id]
  change Triangle.mk p difference δ ∈ distTriang _
  apply isomorphic_distinguished triangle hdist
  exact (Triangle.isoMk triangle (Triangle.mk p difference δ)
    (Iso.refl _) productIso productIso
    (by simp [p, triangle, φ])
    (by simpa [triangle, φ, difference] using hdiff.symm)
    (by simp [δ, triangle])).symm

private theorem derivedLimit_of_objectIso
    (A : Type u) [CommRing A]
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A))
    [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (e : K ≅ L) (hL : IsDerivedLimit F L) : IsDerivedLimit F K := by
  obtain ⟨projection, connecting, distinguished⟩ := hL
  let difference := Pi.lift fun n : ℕ =>
    Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫
        F.map (homOfLE (Nat.le_succ n)).op
  let newProjection := e.hom ≫ projection
  let newConnecting := connecting ≫
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).mapIso e.symm).hom
  refine ⟨newProjection, newConnecting, ?_⟩
  change Triangle.mk newProjection difference newConnecting ∈ distTriang _
  apply isomorphic_distinguished (Triangle.mk projection difference connecting) distinguished
  exact Triangle.isoMk (Triangle.mk newProjection difference newConnecting)
    (Triangle.mk projection difference connecting)
    e (Iso.refl _) (Iso.refl _)
    (by simp [newProjection])
    (by simp)
    (by simp [newConnecting])

private theorem derivedHom_model_isDerivedLimit
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (I : CochainComplex (ModuleCat.{u} A) ℤ) [I.IsKInjective]
    (eI : K ≅ DerivedCategory.Q.obj I) :
    IsDerivedLimit
      (Functor.ofOpSequence (X := fun _ : ℕ => DerivedCategory.Q.obj I)
        (fun _ => f • 𝟙 (DerivedCategory.Q.obj I)))
      (DerivedHomAway.derivedHomFromAway A f K) :=
  derivedLimit_of_objectIso A _ _ _
    (derivedHomToDifferenceCoconeIso A f K I eI)
    (differenceCocone_isDerivedLimit A f I)

set_option backward.isDefEq.respectTransparency false in
private theorem derivedLimit_constantTower_of_iso
    (A : Type u) [CommRing A] (f : A)
    (K L X : DerivedCategory (ModuleCat.{u} A))
    (e : K ≅ L)
    (hL : IsDerivedLimit
      (Functor.ofOpSequence (X := fun _ : ℕ => L) (fun _ => f • 𝟙 L)) X) :
    IsDerivedLimit
      (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)) X := by
  let F := Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)
  let G := Functor.ofOpSequence (X := fun _ : ℕ => L) (fun _ => f • 𝟙 L)
  let productIso := Pi.mapIso (fun _ : ℕ => e)
  let differenceF := Pi.lift fun n : ℕ =>
    Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1)
  let differenceG := Pi.lift fun n : ℕ =>
    Pi.π (fun _ : ℕ => L) n - f • Pi.π (fun _ : ℕ => L) (n + 1)
  have hProjectionF (n : ℕ) :
      differenceF ≫ Pi.π (fun _ : ℕ => K) n =
        Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1) := by
    exact Pi.lift_comp_π _ n
  have hProjectionG (n : ℕ) :
      differenceG ≫ Pi.π (fun _ : ℕ => L) n =
        Pi.π (fun _ : ℕ => L) n - f • Pi.π (fun _ : ℕ => L) (n + 1) := by
    exact Pi.lift_comp_π _ n
  have hProductIso (n : ℕ) :
      productIso.hom ≫ Pi.π (fun _ : ℕ => L) n =
        Pi.π (fun _ : ℕ => K) n ≫ e.hom :=
    Pi.mapIso_hom_π (fun _ : ℕ => e) n
  have hdifference : differenceF ≫ productIso.hom =
      productIso.hom ≫ differenceG := by
    apply Pi.hom_ext
    intro n
    calc
      (differenceF ≫ productIso.hom) ≫ Pi.π (fun _ : ℕ => L) n =
          (differenceF ≫ Pi.π (fun _ : ℕ => K) n) ≫ e.hom := by
        rw [Category.assoc, hProductIso, ← Category.assoc]
      _ = Pi.π (fun _ : ℕ => K) n ≫ e.hom -
          f • (Pi.π (fun _ : ℕ => K) (n + 1) ≫ e.hom) := by
        rw [hProjectionF, Preadditive.sub_comp, Linear.smul_comp]
      _ = (productIso.hom ≫ differenceG) ≫ Pi.π (fun _ : ℕ => L) n := by
        rw [Category.assoc, hProjectionG, Preadditive.comp_sub, Linear.comp_smul]
        rw [hProductIso n, hProductIso (n + 1)]
  obtain ⟨projection, connecting, distinguished⟩ := hL
  let newProjection := projection ≫ productIso.inv
  let newConnecting := productIso.hom ≫ connecting
  refine ⟨newProjection, newConnecting, ?_⟩
  simp only [Functor.ofOpSequence_map_homOfLE_succ] at distinguished ⊢
  erw [pi_lift_sub_comp_smul_id] at distinguished
  erw [pi_lift_sub_comp_smul_id]
  change Triangle.mk newProjection differenceF newConnecting ∈ distTriang _
  apply isomorphic_distinguished (Triangle.mk projection differenceG connecting) distinguished
  exact Triangle.isoMk (Triangle.mk newProjection differenceF newConnecting)
    (Triangle.mk projection differenceG connecting)
    (Iso.refl _) productIso productIso
    (by simp only [Triangle.mk_mor₁, Triangle.mk_obj₁, Iso.refl_hom,
        Category.id_comp, newProjection];
        exact (Category.assoc projection productIso.inv productIso.hom).trans
          (by rw [productIso.inv_hom_id]; exact Category.comp_id projection))
    (by simpa only [Triangle.mk_mor₂] using hdifference)
    (by simp only [Triangle.mk_mor₃, Triangle.mk_obj₁,
        Iso.refl_hom, newConnecting];
        have hm := (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A))
          (1 : ℤ)).map_id X
        rw [hm]
        exact Category.comp_id _)

theorem derivedHomFromAway_isDerivedLimit
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedLimit
      (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K))
      (DerivedHomAway.derivedHomFromAway A f K) := by
  obtain ⟨I, _, ⟨eI⟩⟩ := exists_isKInjective_iso A K
  exact derivedLimit_constantTower_of_iso A f K (DerivedCategory.Q.obj I)
    (DerivedHomAway.derivedHomFromAway A f K) eI
    (derivedHom_model_isDerivedLimit A f K I eI)

private noncomputable def derivedHom_homology_model_iso
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (I : CochainComplex (ModuleCat.{u} A) ℤ) [I.IsKInjective]
    (eI : K ≅ DerivedCategory.Q.obj I) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (DerivedHomAway.derivedHomFromAway A f K) ≅
      (HomComplexR A (telescopeResolution A f) I).homology n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
      (homTelescopeIso A f K I eI) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app
      (HomComplexR A (telescopeResolution A f) I)

private theorem homComplexR_forget_eq
    (A : Type u) [CommRing A]
    (P I : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (HomComplexR A P I) = CochainComplex.HomComplex P I := by
  rfl

private noncomputable def homComplexR_homology_forget_iso
    (A : Type u) [CommRing A]
    (P I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (CochainComplex.HomComplex P I).homology n ≅
      (forget₂ (ModuleCat.{u} A) Ab).obj ((HomComplexR A P I).homology n) :=
  ((HomComplexR A P I).sc n).mapHomologyIso (forget₂ (ModuleCat.{u} A) Ab)

private noncomputable def homComplexR_homologyAddEquiv
    (A : Type u) [CommRing A]
    (P I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ((HomComplexR A P I).homology n : Type u) ≃+
      CochainComplex.HomComplex.CohomologyClass P I n :=
  (homComplexR_homology_forget_iso A P I n).symm.addCommGroupIsoToAddEquiv.trans
    (CochainComplex.HomComplex.homologyAddEquiv P I n)

private abbrev addHomCongr_local {D : Type*} [Category* D] [Preadditive D]
    {X Y X' Y' : D} (sourceIso : X ≅ X') (targetIso : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  (CategoryTheory.Linear.homCongr ℤ sourceIso targetIso).toAddEquiv

private noncomputable def cohomologyClass_derivedAddEquiv
    (A : Type u) [CommRing A]
    (P I : CochainComplex (ModuleCat.{u} A) ℤ) [I.IsKInjective] (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass P I n ≃+
      DerivedCategory.Ext (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) n := by
  let : (I⟦n⟧).IsKInjective := inferInstance
  let homotopy := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let comparison := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  exact CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
    ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective (homotopy.obj P) (I⟦n⟧))).trans
      ((addHomCongr_local (comparison.app P) (comparison.app (I⟦n⟧))).trans
        (addHomCongr_local (Iso.refl _) ((DerivedCategory.Q.commShiftIso n).app I))))

private noncomputable def telescopeCohomologyExtAddEquiv
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (I : CochainComplex (ModuleCat.{u} A) ℤ) [I.IsKInjective]
    (eI : K ≅ DerivedCategory.Q.obj I) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass (telescopeResolution A f) I n ≃+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f))) K n := by
  let augmentation := telescopeResolutionAugmentation A f
  let : QuasiIso augmentation := telescopeResolutionAugmentation_quasiIso A f
  exact (cohomologyClass_derivedAddEquiv A (telescopeResolution A f) I n).trans
    (addHomCongr_local (asIso (DerivedCategory.Q.map augmentation))
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso eI.symm))

theorem derivedHomHomologyExtAddEquiv_nonempty
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty (∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (DerivedHomAway.derivedHomFromAway A f K) : Type u) ≃+
        DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f))) K n) := by
  obtain ⟨I, _, ⟨eI⟩⟩ := exists_isKInjective_iso A K
  refine ⟨fun n => ?_⟩
  let eHom := derivedHom_homology_model_iso A f K I eI n
  let eGroup :
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (DerivedHomAway.derivedHomFromAway A f K) : Type u) ≃+
        ((HomComplexR A (telescopeResolution A f) I).homology n : Type u) :=
    { toFun := eHom.hom
      invFun := eHom.inv
      left_inv := fun a => ConcreteCategory.congr_hom eHom.hom_inv_id a
      right_inv := fun a => ConcreteCategory.congr_hom eHom.inv_hom_id a
      map_add' := fun a b => eHom.hom.hom.map_add a b }
  exact eGroup.trans ((homComplexR_homologyAddEquiv A (telescopeResolution A f) I n).trans
    (telescopeCohomologyExtAddEquiv A f K I eI n))

private theorem isZero_iff_isIso_zero_local {C : Type u} [Category.{w} C]
    [HasZeroMorphisms C] (X : C) : IsZero X ↔ IsIso (0 : X ⟶ X) :=
  ⟨fun h => (isIsoZeroSelfEquiv X).symm ((IsZero.iff_id_eq_zero X).1 h),
    fun h => (IsZero.iff_id_eq_zero X).2 (isIsoZeroSelfEquiv X h)⟩

private theorem isZero_iff_forall_subsingleton_homology_local
    (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{u} A)) :
    IsZero X ↔ ∀ n : ℤ,
      Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X) := by
  rw [isZero_iff_isIso_zero_local, DerivedCategory.isIso_iff]
  refine forall_congr' fun n => ?_
  rw [(DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map_zero,
    ← isZero_iff_isIso_zero_local, ModuleCat.isZero_iff_subsingleton]

theorem extVanishing_iff_isZero_derivedHom
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (∀ n : ℤ, Subsingleton
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f))) K n)) ↔
      IsZero (DerivedHomAway.derivedHomFromAway A f K) := by
  obtain ⟨equivs⟩ := derivedHomHomologyExtAddEquiv_nonempty A f K
  constructor
  · intro hExt
    apply (isZero_iff_forall_subsingleton_homology_local A _).2
    intro n
    constructor
    intro first second
    exact (equivs n).injective (Subsingleton.elim ((equivs n) first) ((equivs n) second))
  · intro hZero n
    have hHom := (isZero_iff_forall_subsingleton_homology_local A _).1 hZero n
    constructor
    intro first second
    apply (equivs n).symm.injective
    exact hHom.elim _ _

private theorem isZero_iff_isIso_difference_local
    {D : Type u} [Category.{w} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
    [Pretriangulated D]
    (F : Functor ℕᵒᵖ D) [HasProduct fun n : ℕ => F.obj ⟨n⟩] (L : D)
    (hL : IsDerivedLimit F L) :
    IsZero L ↔ IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨projection, connecting, distinguished⟩ := hL
  exact (Triangle.mk projection _ connecting).isZero₁_iff_isIso₂ distinguished

private theorem constantTower_difference_eq_local
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ =>
        (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)).obj ⟨n⟩) n -
      Pi.π (fun n : ℕ =>
        (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)).obj ⟨n⟩)
          (n + 1) ≫
        (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)).map
          (homOfLE (Nat.le_succ n)).op) =
      Pi.lift fun n : ℕ =>
        Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1) := by
  simp only [Functor.ofOpSequence_map_homOfLE_succ]
  exact pi_lift_sub_comp_smul_id A f K

theorem rhom_zero_iff_constant_difference_iso
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsZero (DerivedHomAway.derivedHomFromAway A f K) ↔
      IsIso (Pi.lift fun n : ℕ =>
        Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1)) := by
  rw [← constantTower_difference_eq_local A f K]
  exact isZero_iff_isIso_difference_local _ _
    (derivedHomFromAway_isDerivedLimit A f K)

private theorem exists_derivedLimit_zero_iff_difference_iso_local
    {D : Type u} [Category.{w} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
    [Pretriangulated D]
    (F : Functor ℕᵒᵖ D) [HasProduct fun n : ℕ => F.obj ⟨n⟩] :
    (∃ L : D, IsDerivedLimit F L ∧ IsZero L) ↔
      IsIso (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫
            F.map (homOfLE (Nat.le_succ n)).op) := by
  constructor
  · rintro ⟨L, hL, hZero⟩
    exact (isZero_iff_isIso_difference_local F L hL).1 hZero
  · intro hIso
    obtain ⟨L, hL⟩ := exists_isDerivedLimit F
    exact ⟨L, hL, (isZero_iff_isIso_difference_local F L hL).2 hIso⟩

theorem derivedLimitZero_iff_constant_difference_iso
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (∃ L : DerivedCategory (ModuleCat.{u} A),
      IsDerivedLimit
        (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)) L ∧
      IsZero L) ↔
      IsIso (Pi.lift fun n : ℕ =>
        Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1)) := by
  rw [exists_derivedLimit_zero_iff_difference_iso_local,
    constantTower_difference_eq_local]
  exact Iff.rfl

theorem extVanishing_iff_derivedLimitZero
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (∀ n : ℤ, Subsingleton
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f))) K n)) ↔
      ∃ L : DerivedCategory (ModuleCat.{u} A),
        IsDerivedLimit
          (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)) L ∧
        IsZero L :=
  (extVanishing_iff_isZero_derivedHom A f K).trans
    ((rhom_zero_iff_constant_difference_iso A f K).trans
      (derivedLimitZero_iff_constant_difference_iso A f K).symm)

end DerivedHomAway

end
