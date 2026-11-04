module

public import StacksFrontier.Homology.Tor.CrossProduct.System

/-!
# Tor cross products: agreement with the derived product

The cocycle product on two complexes of projective modules agrees with the canonical product
on the cohomology of a derived tensor product (Tag 068H). The comparison goes through
K-projective models, the normalized comparison of lifted tensor complexes, and the
identification of the cycles of the lifted cochain complexes.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.DerivedTensor
open scoped TensorProduct

universe uR uA v w x

noncomputable section

open HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace TorCrossProduct

/-- Lifting scalars along `ULift A ≃+* A` is an equivalence. -/
private lemma isEquivalence_liftScalars (A : Type uA) [CommRing A] :
    (liftScalars.{uR, uA, v} A).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv (R := A) : ULift.{max uR v} A ≃+* A)).isEquivalence_functor

/-- Lifting scalars preserves the projectivity of the terms of a chain complex. -/
private lemma projective_liftScalars_mapHomologicalComplex_X
    {A : Type uA} [CommRing A] (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ)
    [∀ n, Projective (K.X n)] (n : ℕ) :
    Projective ((((liftScalars.{uR, uA, v} A).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).X n) :=
  have := isEquivalence_liftScalars.{uR, uA, v} A
  Functor.projective_obj (liftScalars.{uR, uA, v} A) (K.X n)

private lemma liftedCochain_kFlat
    {A : Type uA} [CommRing A]
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ)
    [∀ n, Projective (K.X n)] : (liftedCochain.{uR, uA, v} A K).KFlat := by
  have := projective_liftScalars_mapHomologicalComplex_X.{uR, uA, v} K
  show CochainComplex.KFlat
    (((((liftScalars.{uR, uA, v} A).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K)).extend ComplexShape.embeddingDownNat)
  exact CochainComplex.KFlat.kFlat_of_flat _ 0

private lemma isIso_liftScalarsTensorMap
    {A : Type uA} [CommRing A] (M N : ModuleCat.{max uR uA v} A) :
    IsIso (liftScalarsTensorMap.{uR, uA, v} A M N) := by
  let B := ULift.{max uR v} A
  let P := (liftScalars.{uR, uA, v} A).obj M
  let Q := (liftScalars.{uR, uA, v} A).obj N
  let : Module A P := M.isModule
  let : Module A Q := N.isModule
  let : SMulCommClass A B P := ⟨fun a b x ↦ smul_comm a b.down x⟩
  let : SMulCommClass B A P := ⟨fun b a x ↦ smul_comm b.down a x⟩
  let : TensorProduct.CompatibleSMul A B P Q :=
    ⟨fun b x y ↦ TensorProduct.smul_tmul b.down x y⟩
  let : TensorProduct.CompatibleSMul B A P Q :=
    ⟨fun a x y ↦ TensorProduct.smul_tmul (ULift.up a : B) x y⟩
  let e : P ⊗[B] Q ≃ₗ[B] P ⊗[A] Q :=
    TensorProduct.equivOfCompatibleSMul A B B P Q
  have he : liftScalarsTensorMap.{uR, uA, v} A M N = e.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  rw [he]
  infer_instance

section KProjectiveModel

attribute [local instance] HasDerivedCategory.standard

variable {B : Type w} [CommRing B]

/-- **A morphism out of a K-projective complex is a chain map.**  For `P₀` K-projective, every
morphism `Q(P₀) ⟶ Q(P)` of the derived category is `Q` of a morphism of complexes. -/
public lemma exists_lift_of_isKProjective (P₀ P : CochainComplex (ModuleCat.{w} B) ℤ)
    [P₀.IsKProjective] (e : DerivedCategory.Q.obj P₀ ⟶ DerivedCategory.Q.obj P) :
    ∃ a : P₀ ⟶ P, DerivedCategory.Q.map a = e := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P₀
    ((HomotopyCategory.quotient _ _).obj P)).2
    ((DerivedCategory.quotientCompQhIso _).hom.app P₀ ≫ e ≫
      (DerivedCategory.quotientCompQhIso _).inv.app P)
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨a, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app P₀),
    ← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

/-- **Equation 15.64.0.1 of Tag 068H holds at a K-projective K-flat pair of complexes**, and not
only at the pair of representatives the construction of
`RingTheory.TorProducts.cohomologyTensorProduct` chose: a morphism out of a K-projective complex
lifts to a chain map, so the chosen representatives can be compared with the given ones. -/
public lemma cohomologyTensorProduct_map_eq_of_isKProjective
    (P₀ Q₀ : CochainComplex (ModuleCat.{w} B) ℤ) [P₀.IsKProjective]
    [Q₀.IsKProjective] (hP₀ : P₀.KFlat) (hQ₀ : Q₀.KFlat) (i j : ℤ)
    (z₀ : P₀.cycles i ⊗ Q₀.cycles j ⟶ (P₀ ⊗ Q₀).cycles (i + j))
    (hz₀ : z₀ ≫ (P₀ ⊗ Q₀).iCycles (i + j) =
      (P₀.iCycles i ⊗ₘ Q₀.iCycles j) ≫ HomologicalComplex.ιTensorObj P₀ Q₀ i j (i + j) rfl) :
    (P₀.homologyπ i ⊗ₘ Q₀.homologyπ j) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat B) i).inv.app P₀ ⊗ₘ
        (DerivedCategory.homologyFunctorFactors (ModuleCat B) j).inv.app Q₀) ≫
      (RingTheory.TorProducts.cohomologyTensorProduct (DerivedCategory.Q.obj P₀)
        (DerivedCategory.Q.obj Q₀) i j).map ≫
      (DerivedCategory.homologyFunctor (ModuleCat B) (i + j)).map
        ((canonicalDerivedTensorProduct B).comparison P₀ Q₀ hP₀ hQ₀).hom ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) (i + j)).hom.app (P₀ ⊗ Q₀) =
    z₀ ≫ (P₀ ⊗ Q₀).homologyπ (i + j) := by
  obtain ⟨P, Q, hP, hQ, eP, eQ, z, hz, hE⟩ :=
    RingTheory.TorProducts.cohomologyTensorProduct_map_cocycles
      (DerivedCategory.Q.obj P₀) (DerivedCategory.Q.obj Q₀) i j
  obtain ⟨a, ha⟩ := exists_lift_of_isKProjective P₀ P eP.inv
  obtain ⟨b, hb⟩ := exists_lift_of_isKProjective Q₀ Q eQ.inv
  have hnat := (canonicalDerivedTensorProduct B).comparison_naturality a b hP₀ hP hQ₀ hQ
  rw [ha, hb] at hnat
  set T := canonicalDerivedTensorProduct B
  have hT : canonicalDerivedTensorProductFunctor B = T.tensor := rfl
  have hiso : IsIso (DerivedCategory.Q.map (HomologicalComplex.tensorHom a b)) := by
    have : IsIso ((T.comparison P₀ Q₀ hP₀ hQ₀).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom a b)) := by
      rw [← hnat]; infer_instance
    exact IsIso.of_isIso_comp_left (T.comparison P₀ Q₀ hP₀ hQ₀).hom _
  have : QuasiIso (HomologicalComplex.tensorHom a b) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hiso
  have hcyc : (HomologicalComplex.cyclesMap a i ⊗ₘ HomologicalComplex.cyclesMap b j) ≫ z =
      z₀ ≫ HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom a b) (i + j) := by
    rw [← cancel_mono ((P ⊗ Q).iCycles (i + j))]
    simp only [Category.assoc, hz]
    rw [tensorHom_comp_tensorHom_assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.cyclesMap_i, ← tensorHom_comp_tensorHom_assoc]
    erw [HomologicalComplex.cyclesMap_i]
    erw [reassoc_of% hz₀]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
      Category.assoc]
  have hleft (X Y : CochainComplex (ModuleCat.{w} B) ℤ) (c : X ⟶ Y)
      (e : DerivedCategory.Q.obj Y ≅ DerivedCategory.Q.obj X)
      (hc : DerivedCategory.Q.map c = e.inv) (k : ℤ) :
      HomologicalComplex.cyclesMap c k ≫ Y.homologyπ k ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat B) k).inv.app Y ≫
        (DerivedCategory.homologyFunctor (ModuleCat B) k).map e.hom =
      X.homologyπ k ≫ (DerivedCategory.homologyFunctorFactors (ModuleCat B) k).inv.app X := by
    rw [← HomologicalComplex.homologyπ_naturality_assoc]
    congr 1
    have := (DerivedCategory.homologyFunctorFactors (ModuleCat B) k).inv.naturality c
    dsimp only [Functor.comp_map] at this
    erw [reassoc_of% this]
    rw [← Functor.map_comp, hc]
    simp
  have hL : (HomologicalComplex.cyclesMap a i ⊗ₘ HomologicalComplex.cyclesMap b j) ≫
      (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat B) i).inv.app P ⊗ₘ
        (DerivedCategory.homologyFunctorFactors (ModuleCat B) j).inv.app Q) ≫
      ((DerivedCategory.homologyFunctor (ModuleCat B) i).map eP.hom ⊗ₘ
        (DerivedCategory.homologyFunctor (ModuleCat B) j).map eQ.hom) =
      (P₀.homologyπ i ⊗ₘ Q₀.homologyπ j) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat B) i).inv.app P₀ ⊗ₘ
        (DerivedCategory.homologyFunctorFactors (ModuleCat B) j).inv.app Q₀) := by
    simp only [tensorHom_comp_tensorHom]
    rw [hleft P₀ P a eP ha, hleft Q₀ Q b eQ hb]
  have hR : (DerivedCategory.homologyFunctor (ModuleCat B) (i + j)).map
        (((canonicalDerivedTensorProductFunctor B).map eP.inv).app (DerivedCategory.Q.obj Q₀) ≫
          ((canonicalDerivedTensorProductFunctor B).obj (DerivedCategory.Q.obj P)).map eQ.inv ≫
          ((canonicalDerivedTensorProduct B).comparison P Q hP hQ).hom) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) (i + j)).hom.app (P ⊗ Q) =
      (DerivedCategory.homologyFunctor (ModuleCat B) (i + j)).map
        ((canonicalDerivedTensorProduct B).comparison P₀ Q₀ hP₀ hQ₀).hom ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) (i + j)).hom.app (P₀ ⊗ Q₀) ≫
      HomologicalComplex.homologyMap (HomologicalComplex.tensorHom a b) (i + j) := by
    rw [hnat]
    rw [Functor.map_comp, Category.assoc]
    erw [DerivedCategory.homologyFunctorFactors_hom_naturality]
  have h1 := (HomologicalComplex.cyclesMap a i ⊗ₘ HomologicalComplex.cyclesMap b j) ≫= hE
  rw [reassoc_of% hcyc, reassoc_of% hL, hR] at h1
  rw [← cancel_mono (HomologicalComplex.homologyMap (HomologicalComplex.tensorHom a b) (i + j))]
  simp only [Category.assoc] at h1 ⊢
  rw [h1, HomologicalComplex.homologyπ_naturality]
  rfl

end KProjectiveModel

section LiftedComparison
variable {A : Type uA} [CommRing A]

private lemma liftScalarsTensorMap_naturality
    {M M' N N' : ModuleCat.{max uR uA v} A} (f : M ⟶ M') (g : N ⟶ N') :
    ((liftScalars.{uR, uA, v} A).map f ⊗ₘ (liftScalars.{uR, uA, v} A).map g) ≫
      liftScalarsTensorMap.{uR, uA, v} A M' N' =
    liftScalarsTensorMap.{uR, uA, v} A M N ≫
      (liftScalars.{uR, uA, v} A).map (moduleTensorMap.{uR, uA, v} f g) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

private lemma liftedCochain_isZero_X
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (i : ℤ)
    (hi : ¬ ∃ n : ℕ, -(n : ℤ) = i) :
    IsZero ((liftedCochain.{uR, uA, v} A K).X i) :=
  isZero_extend_X _ _ i (fun n hn ↦ hi ⟨n, hn⟩)

private def liftedTensorXMap
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (i : ℤ) :
    (liftedCochain.{uR, uA, v} A K ⊗ liftedCochain.{uR, uA, v} A L).X i ⟶
      (liftedCochain.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)).X i :=
  mapBifunctorDesc fun a b h ↦ by
    classical
    by_cases ha : ∃ p : ℕ, -(p : ℤ) = a
    · by_cases hb : ∃ q : ℕ, -(q : ℤ) = b
      · let p := ha.choose
        let q := hb.choose
        have hp : -(p : ℤ) = a := ha.choose_spec
        have hq : -(q : ℤ) = b := hb.choose_spec
        have hk : -((p + q : ℕ) : ℤ) = i := by
          change a + b = i at h
          omega
        exact ((liftedCochainXIso.{uR, uA, v} A K p a hp).hom ⊗ₘ
          (liftedCochainXIso.{uR, uA, v} A L q b hq).hom) ≫
          liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q) ≫
          (liftScalars.{uR, uA, v} A).map
            (ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
              (ComplexShape.down ℕ) p q (p + q) rfl) ≫
          (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)
            (p + q) i hk).inv
      · exact 0
    · exact 0

private lemma ι_liftedTensorXMap
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ)
    (p q k : ℕ) (h : p + q = k) :
    ιTensorObj (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
      (-(p : ℤ)) (-(q : ℤ)) (-(k : ℤ)) (by omega) ≫
        liftedTensorXMap.{uR, uA, v} K L (-(k : ℤ)) =
      ((liftedCochainXIso.{uR, uA, v} A K p (-(p : ℤ)) rfl).hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L q (-(q : ℤ)) rfl).hom) ≫
        liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q) ≫
        (liftScalars.{uR, uA, v} A).map
          (ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
            (ComplexShape.down ℕ) p q k h) ≫
        (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)
          k (-(k : ℤ)) rfl).inv := by
  classical
  subst k
  have hp : ∃ n : ℕ, -(n : ℤ) = -(p : ℤ) := ⟨p, rfl⟩
  have hq : ∃ n : ℕ, -(n : ℤ) = -(q : ℤ) := ⟨q, rfl⟩
  have aux (p' q' : ℕ) (hp' : -(p' : ℤ) = -(p : ℤ))
      (hq' : -(q' : ℤ) = -(q : ℤ)) :
      ((liftedCochainXIso.{uR, uA, v} A K p' (-(p : ℤ)) hp').hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L q' (-(q : ℤ)) hq').hom) ≫
        liftScalarsTensorMap.{uR, uA, v} A (K.X p') (L.X q') ≫
        (liftScalars.{uR, uA, v} A).map
          (ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
            (ComplexShape.down ℕ) p' q' (p' + q') rfl) ≫
        (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)
          (p' + q') (-((p + q : ℕ) : ℤ)) (by omega)).inv =
      ((liftedCochainXIso.{uR, uA, v} A K p (-(p : ℤ)) rfl).hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L q (-(q : ℤ)) rfl).hom) ≫
        liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q) ≫
        (liftScalars.{uR, uA, v} A).map
          (ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
            (ComplexShape.down ℕ) p q (p + q) rfl) ≫
        (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)
          (p + q) (-((p + q : ℕ) : ℤ)) rfl).inv := by
    obtain rfl : p' = p := by omega
    obtain rfl : q' = q := by omega
    rfl
  dsimp only [liftedTensorXMap, ιTensorObj]
  rw [ι_mapBifunctorDesc]
  simp only [dite_eq_left hp, dite_eq_left hq]
  exact aux hp.choose hq.choose hp.choose_spec hq.choose_spec

private lemma liftedTensor_hom_ext
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (i : ℤ)
    {Z : ModuleCat (ULift.{max uR v} A)}
    {f g : (liftedCochain.{uR, uA, v} A K ⊗ liftedCochain.{uR, uA, v} A L).X i ⟶ Z}
    (h : ∀ (p q : ℕ) (hpq : -(p : ℤ) + -(q : ℤ) = i),
      ιTensorObj (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        (-(p : ℤ)) (-(q : ℤ)) i hpq ≫ f =
      ιTensorObj (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        (-(p : ℤ)) (-(q : ℤ)) i hpq ≫ g) : f = g := by
  apply mapBifunctor.hom_ext
  intro a b hab
  by_cases ha : ∃ p : ℕ, -(p : ℤ) = a
  · obtain ⟨p, rfl⟩ := ha
    by_cases hb : ∃ q : ℕ, -(q : ℤ) = b
    · obtain ⟨q, rfl⟩ := hb
      exact h p q hab
    · exact ((tensorLeft _).map_isZero (liftedCochain_isZero_X.{uR, uA, v} L b hb)).eq_of_src _ _
  · exact ((tensorRight _).map_isZero (liftedCochain_isZero_X.{uR, uA, v} K a ha)).eq_of_src _ _

private lemma isIso_liftedTensorXMap_neg
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (n : ℕ) :
    IsIso (liftedTensorXMap.{uR, uA, v} K L (-(n : ℤ))) := by
  let F := liftScalars.{uR, uA, v} A
  have := isEquivalence_liftScalars.{uR, uA, v} A
  let X := (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L
  let hc := isColimitCofanMkObjOfIsColimit (G := F) (P := X.toGradedObject.mapObj
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)
    (f := X.toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)
    (fun x ↦ X.toGradedObject.ιMapObj _ x.1 n x.2) (X.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)
  have (p q : ℕ) : IsIso (liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q)) :=
    isIso_liftScalarsTensorMap.{uR, uA, v} _ _
  let v : F.obj ((chainTensor.{uR, uA, v} K L).X n) ⟶
      (liftedCochain.{uR, uA, v} A K ⊗ liftedCochain.{uR, uA, v} A L).X (-(n : ℤ)) :=
    Cofan.IsColimit.desc hc (fun x ↦
      inv (liftScalarsTensorMap.{uR, uA, v} A (K.X x.1.1) (L.X x.1.2)) ≫
      ((liftedCochainXIso.{uR, uA, v} A K x.1.1 (-(x.1.1 : ℤ)) rfl).inv ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L x.1.2 (-(x.1.2 : ℤ)) rfl).inv) ≫
      ιTensorObj (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        (-(x.1.1 : ℤ)) (-(x.1.2 : ℤ)) (-(n : ℤ))
        (by have := x.2; change x.1.1 + x.1.2 = n at this; omega))
  have hv (p q : ℕ) (h : p + q = n) :
      F.map (ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
        (ComplexShape.down ℕ) p q n h) ≫ v =
      inv (liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q)) ≫
      ((liftedCochainXIso.{uR, uA, v} A K p (-(p : ℤ)) rfl).inv ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L q (-(q : ℤ)) rfl).inv) ≫
      ιTensorObj (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega) :=
    Cofan.IsColimit.fac hc _ ⟨⟨p, q⟩, h⟩
  let E := liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L) n (-(n : ℤ)) rfl
  refine ⟨⟨E.hom ≫ v, ?_, ?_⟩⟩
  · apply liftedTensor_hom_ext.{uR, uA, v} K L (-(n : ℤ))
    intro p q hpq
    have h : p + q = n := by omega
    simp only [← Category.assoc, ι_liftedTensorXMap.{uR, uA, v} K L p q n h]
    simp only [Category.assoc, E, Iso.inv_hom_id_assoc]
    rw [hv p q h]
    simp only [IsIso.hom_inv_id_assoc, tensorHom_comp_tensorHom_assoc,
      Iso.hom_inv_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    erw [Category.comp_id]
  · rw [← cancel_epi E.inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
    apply Cofan.IsColimit.hom_ext hc
    rintro ⟨⟨p, q⟩, h⟩
    dsimp only [Cofan.mk_ι_app, Cofan.inj]
    show F.map (ιMapBifunctor K L _ _ p q n h) ≫ v ≫
      liftedTensorXMap.{uR, uA, v} K L (-(n : ℤ)) = _
    rw [reassoc_of% (hv p q h), ι_liftedTensorXMap.{uR, uA, v} K L p q n h]
    simp only [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
      tensorHom_id, id_whiskerRight, Category.id_comp, IsIso.inv_hom_id_assoc]
    rfl


private lemma liftedTensor_isZero_X
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (i : ℤ)
    (hi : ¬ ∃ n : ℕ, -(n : ℤ) = i) :
    IsZero ((liftedCochain.{uR, uA, v} A K ⊗ liftedCochain.{uR, uA, v} A L).X i) := by
  rw [IsZero.iff_id_eq_zero]
  refine liftedTensor_hom_ext.{uR, uA, v} K L i fun p q hpq ↦ absurd ⟨p + q, ?_⟩ hi
  push_cast; omega

private lemma isIso_liftedTensorXMap
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (i : ℤ) :
    IsIso (liftedTensorXMap.{uR, uA, v} K L i) := by
  by_cases hi : ∃ n : ℕ, -(n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hi
    exact isIso_liftedTensorXMap_neg.{uR, uA, v} K L n
  · exact (liftedTensor_isZero_X.{uR, uA, v} K L i hi).isIso
      (liftedCochain_isZero_X.{uR, uA, v} (chainTensor.{uR, uA, v} K L) i hi) _

private lemma liftScalarsTensorMap_naturality_left
    {M M' : ModuleCat.{max uR uA v} A} (f : M ⟶ M')
    (N : ModuleCat.{max uR uA v} A) :
    ((liftScalars.{uR, uA, v} A).map f ▷ (liftScalars.{uR, uA, v} A).obj N) ≫
      liftScalarsTensorMap.{uR, uA, v} A M' N =
    liftScalarsTensorMap.{uR, uA, v} A M N ≫
      (liftScalars.{uR, uA, v} A).map
        (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).map f).app N) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

private lemma liftScalarsTensorMap_naturality_right
    (M : ModuleCat.{max uR uA v} A) {N N' : ModuleCat.{max uR uA v} A} (g : N ⟶ N') :
    ((liftScalars.{uR, uA, v} A).obj M ◁ (liftScalars.{uR, uA, v} A).map g) ≫
      liftScalarsTensorMap.{uR, uA, v} A M N' =
    liftScalarsTensorMap.{uR, uA, v} A M N ≫
      (liftScalars.{uR, uA, v} A).map
        (((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj M).map g) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

private lemma liftedCochain_d_eq
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (p q : ℕ) :
    (liftedCochain.{uR, uA, v} A K).d (-(p : ℤ)) (-(q : ℤ)) =
      (liftedCochainXIso.{uR, uA, v} A K p (-(p : ℤ)) rfl).hom ≫
        (liftScalars.{uR, uA, v} A).map (K.d p q) ≫
        (liftedCochainXIso.{uR, uA, v} A K q (-(q : ℤ)) rfl).inv :=
  extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl

private lemma liftedTensorXMap_d₁
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (p q n : ℕ) :
    mapBifunctor.d₁ (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        (curriedTensor _) (ComplexShape.up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) ≫
        liftedTensorXMap.{uR, uA, v} K L (-(n : ℤ)) =
      ((liftedCochainXIso.{uR, uA, v} A K p (-(p : ℤ)) rfl).hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L q (-(q : ℤ)) rfl).hom) ≫
        liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q) ≫
        (liftScalars.{uR, uA, v} A).map
          (mapBifunctor.d₁ K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
            (ComplexShape.down ℕ) p q n) ≫
        (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)
          n (-(n : ℤ)) rfl).inv := by
  cases p with
  | zero =>
    try simp only [Nat.cast_zero, neg_zero]
    have hz : (liftedCochain.{uR, uA, v} A K).d 0 1 = 0 :=
      (liftedCochain_isZero_X.{uR, uA, v} K 1 (by rintro ⟨n, hn⟩; omega)).eq_of_tgt _ _
    erw [mapBifunctor.d₁_eq_zero K L _ _ 0 q n (by simp),
      mapBifunctor.d₁_eq' (liftedCochain.{uR, uA, v} A K)
        (liftedCochain.{uR, uA, v} A L) _ _ (show (ComplexShape.up ℤ).Rel 0 1 by decide)]
    simp [hz]
  | succ p =>
    have hp : (ComplexShape.down ℕ).Rel (p + 1) p := by simp
    have hp' : (ComplexShape.up ℤ).Rel (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) := by
      show -((p + 1 : ℕ) : ℤ) + 1 = -(p : ℤ); omega
    by_cases h : p + q = n
    · rw [mapBifunctor.d₁_eq _ _ _ _ hp' _ _ (by change -(p : ℤ) + -(q : ℤ) = -(n : ℤ); omega),
        mapBifunctor.d₁_eq _ _ _ _ hp _ _ h]
      simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (-((p + 1 : ℕ) : ℤ), -(q : ℤ)) = 1 from rfl,
        show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p + 1, q) = 1 from rfl,
        one_smul, Functor.map_comp, Category.assoc]
      rw [ι_liftedTensorXMap.{uR, uA, v} K L p q n h]
      rw [liftedCochain_d_eq.{uR, uA, v} K (p + 1) p]
      rw [← reassoc_of% (liftScalarsTensorMap_naturality_left.{uR, uA, v}
        (K.d (p + 1) p) (L.X q))]
      simp only [curriedTensor_map_app, whiskerRight_comp_tensorHom_assoc,
        tensorHom_comp_whiskerRight_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ hp' _ _ (by
          show -(p : ℤ) + -(q : ℤ) ≠ -(n : ℤ); omega),
        mapBifunctor.d₁_eq_zero' _ _ _ _ hp _ _ h]
      simp


private lemma liftedTensorXMap_d₂
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (p q n : ℕ) :
    mapBifunctor.d₂ (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        (curriedTensor _) (ComplexShape.up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) ≫
        liftedTensorXMap.{uR, uA, v} K L (-(n : ℤ)) =
      ((liftedCochainXIso.{uR, uA, v} A K p (-(p : ℤ)) rfl).hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L q (-(q : ℤ)) rfl).hom) ≫
        liftScalarsTensorMap.{uR, uA, v} A (K.X p) (L.X q) ≫
        (liftScalars.{uR, uA, v} A).map
          (mapBifunctor.d₂ K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
            (ComplexShape.down ℕ) p q n) ≫
        (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)
          n (-(n : ℤ)) rfl).inv := by
  cases q with
  | zero =>
    try simp only [Nat.cast_zero, neg_zero]
    have hz : (liftedCochain.{uR, uA, v} A L).d 0 1 = 0 :=
      (liftedCochain_isZero_X.{uR, uA, v} L 1 (by rintro ⟨n, hn⟩; omega)).eq_of_tgt _ _
    erw [mapBifunctor.d₂_eq_zero K L _ _ p 0 n (by simp),
      mapBifunctor.d₂_eq' (liftedCochain.{uR, uA, v} A K)
        (liftedCochain.{uR, uA, v} A L) _ _ (-(p : ℤ))
        (show (ComplexShape.up ℤ).Rel 0 1 by decide)]
    simp [hz]
  | succ q =>
    have hq : (ComplexShape.down ℕ).Rel (q + 1) q := by simp
    have hq' : (ComplexShape.up ℤ).Rel (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) := by
      show -((q + 1 : ℕ) : ℤ) + 1 = -(q : ℤ); omega
    by_cases h : p + q = n
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ hq' _ (by change -(p : ℤ) + -(q : ℤ) = -(n : ℤ); omega),
        mapBifunctor.d₂_eq _ _ _ _ _ hq _ h]
      have hs : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (-(p : ℤ), -((q + 1 : ℕ) : ℤ)) =
          ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (p, q + 1) := by
        show (-1 : ℤˣ) ^ (-(p : ℤ)) = (-1 : ℤˣ) ^ p
        simp
      rw [hs]
      simp only [Linear.units_smul_comp, Functor.map_units_smul, Linear.comp_units_smul,
        Functor.map_comp, Category.assoc]
      congr 1
      rw [ι_liftedTensorXMap.{uR, uA, v} K L p q n h]
      rw [liftedCochain_d_eq.{uR, uA, v} L (q + 1) q]
      rw [← reassoc_of% (liftScalarsTensorMap_naturality_right.{uR, uA, v}
        (K.X p) (L.d (q + 1) q))]
      simp only [curriedTensor_obj_map, whiskerLeft_comp_tensorHom_assoc,
        tensorHom_comp_whiskerLeft_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ hq' _ (by
          show -(p : ℤ) + -(q : ℤ) ≠ -(n : ℤ); omega),
        mapBifunctor.d₂_eq_zero' _ _ _ _ _ hq _ h]
      simp

private lemma liftedTensorXMap_comm
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (i j : ℤ)
    (h : (ComplexShape.up ℤ).Rel i j) :
    liftedTensorXMap.{uR, uA, v} K L i ≫
        (liftedCochain.{uR, uA, v} A (chainTensor.{uR, uA, v} K L)).d i j =
      (liftedCochain.{uR, uA, v} A K ⊗ liftedCochain.{uR, uA, v} A L).d i j ≫
        liftedTensorXMap.{uR, uA, v} K L j := by
  by_cases hi : ∃ k : ℕ, -(k : ℤ) = i
  · obtain ⟨k, rfl⟩ := hi
    cases k with
    | zero =>
      have hj : j = 1 := by change -(0 : ℤ) + 1 = j at h; omega
      clear h
      subst j
      exact (liftedCochain_isZero_X.{uR, uA, v} (chainTensor.{uR, uA, v} K L) 1
        (by rintro ⟨n, hn⟩; omega)).eq_of_tgt _ _
    | succ k =>
      have hj : j = -(k : ℤ) := by change -((k + 1 : ℕ) : ℤ) + 1 = j at h; omega
      clear h
      subst j
      apply liftedTensor_hom_ext.{uR, uA, v} K L (-(k + 1 : ℕ))
      intro p q hpq'
      have hpq : p + q = k + 1 := by omega
      rw [← Category.assoc, ι_liftedTensorXMap.{uR, uA, v} K L p q (k + 1) hpq]
      rw [liftedCochain_d_eq.{uR, uA, v} (chainTensor.{uR, uA, v} K L) (k + 1) k]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Functor.map_comp_assoc, mapBifunctor.d_eq]
      erw [mapBifunctor.d_eq (liftedCochain.{uR, uA, v} A K)
        (liftedCochain.{uR, uA, v} A L) (curriedTensor _) (ComplexShape.up ℤ)]
      simp only [Preadditive.comp_add, Preadditive.add_comp, ιTensorObj,
        mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc,
        mapBifunctor.ι_D₂_assoc, Functor.map_add]
      rw [liftedTensorXMap_d₁.{uR, uA, v}, liftedTensorXMap_d₂.{uR, uA, v}]
  · exact (liftedTensor_isZero_X.{uR, uA, v} K L i hi).eq_of_src _ _

private noncomputable def liftedComparison
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) :
    LiftedTensorComparison.{uR, uA, v} A K L := by
  haveI (i : ℤ) : IsIso (liftedTensorXMap.{uR, uA, v} K L i) :=
    isIso_liftedTensorXMap.{uR, uA, v} K L i
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ asIso (liftedTensorXMap.{uR, uA, v} K L i))
    (liftedTensorXMap_comm.{uR, uA, v} K L), ?_⟩
  intro p q k h
  change ιTensorObj _ _ _ _ _ _ ≫ liftedTensorXMap.{uR, uA, v} K L (-(k : ℤ)) ≫ _ = _
  rw [reassoc_of% (ι_liftedTensorXMap.{uR, uA, v} K L p q k h)]
  simp only [Iso.inv_hom_id, Category.comp_id]


end LiftedComparison
section LiftedCycles
variable {A : Type uA} [CommRing A]

private def liftedCochainCyclesIso
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (n : ℕ) (i : ℤ)
    (h : -(n : ℤ) = i) :
    (liftedCochain.{uR, uA, v} A K).cycles i ≅
      (liftScalars.{uR, uA, v} A).obj (K.cycles n) := by
  have := isEquivalence_liftScalars.{uR, uA, v} A
  exact (((liftScalars.{uR, uA, v} A).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).extendCyclesIso ComplexShape.embeddingDownNat h ≪≫
    (K.sc n).mapCyclesIso (liftScalars.{uR, uA, v} A)

private lemma liftedCochainCyclesIso_hom_iCycles
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (n : ℕ) (i : ℤ)
    (h : -(n : ℤ) = i) :
    (liftedCochainCyclesIso.{uR, uA, v} K n i h).hom ≫
        (liftScalars.{uR, uA, v} A).map (K.iCycles n) =
      (liftedCochain.{uR, uA, v} A K).iCycles i ≫
        (liftedCochainXIso.{uR, uA, v} A K n i h).hom := by
  dsimp only [liftedCochainCyclesIso, Iso.trans_hom]
  rw [Category.assoc]
  erw [ShortComplex.mapCyclesIso_hom_iCycles]
  exact extendCyclesIso_hom_iCycles _ _ h

private lemma homologyπ_mapHomologyIso_hom
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (F : C ⥤ D) [F.Additive] [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapCyclesIso_eq F, h.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (h.map F).homologyπ_comp_homologyIso_hom]
  congr 1
  show F.map h.π ≫ F.map h.homologyIso.inv =
    F.map h.cyclesIso.inv ≫ F.map S.homologyπ
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  symm
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h.homologyπ_comp_homologyIso_hom]
  simp

private lemma homologyπ_liftedCochainHomologyIso_hom
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (n : ℕ) (i : ℤ)
    (h : -(n : ℤ) = i) :
    (liftedCochain.{uR, uA, v} A K).homologyπ i ≫
        (liftedCochainHomologyIso.{uR, uA, v} A K n i h).hom =
      (liftedCochainCyclesIso.{uR, uA, v} K n i h).hom ≫
        (liftScalars.{uR, uA, v} A).map (K.homologyπ n) := by
  dsimp only [liftedCochainHomologyIso, liftedCochainCyclesIso, Iso.trans_hom]
  erw [homologyπ_extendHomologyIso_hom_assoc]
  simp only [Category.assoc]
  congr 1
  exact homologyπ_mapHomologyIso_hom (K.sc n) (liftScalars.{uR, uA, v} A)

end LiftedCycles

section Agreement
attribute [local instance] HasDerivedCategory.standard
variable {A : Type uA} [CommRing A]

private lemma liftedCochain_isKProjective
    (K : ChainComplex (ModuleCat.{max uR uA v} A) ℕ)
    [∀ n, Projective (K.X n)] : (liftedCochain.{uR, uA, v} A K).IsKProjective := by
  have := projective_liftScalars_mapHomologicalComplex_X.{uR, uA, v} K
  show CochainComplex.IsKProjective
    ((((liftScalars.{uR, uA, v} A).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).extend ComplexShape.embeddingDownNat)
  infer_instance

private lemma liftedComparison_ι_hom
    {K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ}
    (t : LiftedTensorComparison.{uR, uA, v} A K L) (n m : ℕ) (i j k : ℤ)
    (hi : -(n : ℤ) = i) (hj : -(m : ℤ) = j) (hk : -((n + m : ℕ) : ℤ) = k) :
    ιTensorObj (liftedCochain.{uR, uA, v} A K) (liftedCochain.{uR, uA, v} A L)
        i j k (by omega) ≫ t.iso.hom.f k ≫
        (liftedCochainXIso.{uR, uA, v} A (chainTensor.{uR, uA, v} K L) (n + m) k hk).hom =
      ((liftedCochainXIso.{uR, uA, v} A K n i hi).hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L m j hj).hom) ≫
      liftScalarsTensorMap.{uR, uA, v} A (K.X n) (L.X m) ≫
      (liftScalars.{uR, uA, v} A).map
        (ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
          (ComplexShape.down ℕ) n m (n + m) rfl) := by
  subst i
  subst j
  subst k
  exact t.ι_hom n m (n + m) rfl

public section

lemma chainHomologyProduct_agreesWith068H
    {K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ}
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)] {n m : ℕ}
    (c : ChainHomologyProduct.{uR, uA, v} A K L n m) : c.AgreesWith068H := by
  let B := ULift.{max uR v} A
  let F := liftScalars.{uR, uA, v} A
  let P := liftedCochain.{uR, uA, v} A K
  let Q := liftedCochain.{uR, uA, v} A L
  let V := chainTensor.{uR, uA, v} K L
  let W := liftedCochain.{uR, uA, v} A V
  let i := -(n : ℤ)
  let j := -(m : ℤ)
  let k := i + j
  have hk : -((n + m : ℕ) : ℤ) = k := by dsimp [k, i, j]; omega
  let t := liftedComparison.{uR, uA, v} K L
  have hP := liftedCochain_kFlat.{uR, uA, v} K
  have hQ := liftedCochain_kFlat.{uR, uA, v} L
  have : P.IsKProjective := liftedCochain_isKProjective.{uR, uA, v} K
  have : Q.IsKProjective := liftedCochain_isKProjective.{uR, uA, v} L
  obtain ⟨z, hz, hπ⟩ := c.maps_cycles
  let zc : P.cycles i ⊗ Q.cycles j ⟶ W.cycles k :=
    ((liftedCochainCyclesIso.{uR, uA, v} K n i rfl).hom ⊗ₘ
      (liftedCochainCyclesIso.{uR, uA, v} L m j rfl).hom) ≫
      liftScalarsTensorMap.{uR, uA, v} A (K.cycles n) (L.cycles m) ≫
      F.map z ≫ (liftedCochainCyclesIso.{uR, uA, v} V (n + m) k hk).inv
  have hc : zc ≫ W.iCycles k =
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫ ιTensorObj P Q i j k rfl ≫ t.iso.hom.f k := by
    rw [← cancel_mono (liftedCochainXIso.{uR, uA, v} A V (n + m) k hk).hom]
    have ht : ιTensorObj P Q i j k rfl ≫ t.iso.hom.f k ≫
        (liftedCochainXIso.{uR, uA, v} A V (n + m) k hk).hom =
      ((liftedCochainXIso.{uR, uA, v} A K n i rfl).hom ⊗ₘ
        (liftedCochainXIso.{uR, uA, v} A L m j rfl).hom) ≫
      liftScalarsTensorMap.{uR, uA, v} A (K.X n) (L.X m) ≫
      F.map (ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
        (ComplexShape.down ℕ) n m (n + m) rfl) :=
      liftedComparison_ι_hom.{uR, uA, v} t n m i j k rfl rfl hk
    dsimp only [zc]
    simp only [Category.assoc]
    rw [ht, ← liftedCochainCyclesIso_hom_iCycles.{uR, uA, v} V (n + m) k hk,
      Iso.inv_hom_id_assoc, ← F.map_comp, hz, F.map_comp]
    rw [← reassoc_of% (liftScalarsTensorMap_naturality.{uR, uA, v} (K.iCycles n) (L.iCycles m))]
    simp only [tensorHom_comp_tensorHom_assoc]
    rw [liftedCochainCyclesIso_hom_iCycles.{uR, uA, v},
      liftedCochainCyclesIso_hom_iCycles.{uR, uA, v}]
  let z₀ : (P.cycles i ⊗ Q.cycles j : ModuleCat B) ⟶
      (P ⊗ Q : CochainComplex (ModuleCat B) ℤ).cycles k :=
    zc ≫ cyclesMap t.iso.inv k
  have hz₀ : z₀ ≫ (P ⊗ Q : CochainComplex (ModuleCat B) ℤ).iCycles k =
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫ ιTensorObj P Q i j k rfl := by
    dsimp only [z₀]
    rw [Category.assoc, cyclesMap_i, ← Category.assoc, hc]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f]
    erw [Category.comp_id]
  refine ⟨hP, hQ, t, ?_⟩
  have hpair := cohomologyTensorProduct_map_eq_of_isKProjective P Q hP hQ i j z₀ hz₀
  have : Epi (P.homologyπ i ⊗ₘ Q.homologyπ j) := by
    apply (ModuleCat.epi_iff_surjective _).2
    exact TensorProduct.map_surjective
      ((ModuleCat.epi_iff_surjective (P.homologyπ i)).1 inferInstance)
      ((ModuleCat.epi_iff_surjective (Q.homologyπ j)).1 inferInstance)
  rw [← cancel_epi (P.homologyπ i ⊗ₘ Q.homologyπ j)]
  show (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
      ((liftedCochainHomologyIso.{uR, uA, v} A K n i rfl).hom ⊗ₘ
        (liftedCochainHomologyIso.{uR, uA, v} A L m j rfl).hom) ≫
      liftScalarsTensorMap.{uR, uA, v} A (K.homology n) (L.homology m) ≫ F.map c.map =
    (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ _
  rw [reassoc_of% hpair]
  show _ = z₀ ≫ (P ⊗ Q : CochainComplex (ModuleCat B) ℤ).homologyπ k ≫ homologyMap t.iso.hom k ≫
    (liftedCochainHomologyIso.{uR, uA, v} A V (n + m) k hk).hom
  rw [homologyπ_naturality_assoc]
  dsimp only [z₀, zc]
  simp only [Category.assoc]
  rw [← cyclesMap_comp_assoc, Iso.inv_hom_id]
  rw [cyclesMap_id, Category.id_comp]
  rw [homologyπ_liftedCochainHomologyIso_hom.{uR, uA, v}]
  dsimp only [V, F]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← hπ, Functor.map_comp]
  rw [tensorHom_comp_tensorHom_assoc,
    homologyπ_liftedCochainHomologyIso_hom.{uR, uA, v},
    homologyπ_liftedCochainHomologyIso_hom.{uR, uA, v},
    ← tensorHom_comp_tensorHom_assoc]
  rw [reassoc_of% (liftScalarsTensorMap_naturality.{uR, uA, v} (K.homologyπ n) (L.homologyπ m))]

end

end Agreement

end TorCrossProduct

end
