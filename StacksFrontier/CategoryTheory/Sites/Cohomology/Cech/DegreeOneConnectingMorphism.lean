module

public import StacksFrontier.Algebra.Homology.DerivedCategory.HorseshoeConnectingMorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeOneInjectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.CocycleFormula
public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# The degree-one Čech comparison and connecting morphisms

Let `(C, K)` be a site, `𝒰 = {U_i → U}` a covering family and `0 → S₁ → S₂ → S₃ → 0` a short
exact sequence of abelian sheaves. Let `z` be a Čech `1`-cocycle of `S₁` which is the Čech
coboundary of a degree-zero cochain `b` of `S₂`, and let `q` be the section of `S₃` over `U`
glued from the images of `b`. This file proves that the comparison `Ȟ¹(𝒰, S₁) → H¹(U, S₁)` of
Stacks 03AX sends the class of `z` to the image of `q` under the connecting morphism
`H⁰(U, S₃) → H¹(U, S₁)`
(`Stacks.CechSite.cechCohomologyToCohomology_one_cls_eq_rightDerivedPlusδ`).

The proof computes both sides on a resolution of the short exact sequence by a short exact
sequence `0 → I₁ → I₂ → I₃ → 0` of injective resolutions. The comparison of 03AX is computed on
the Čech bicomplex of `I₁` as the map `β` induced by `S₁ → I₁⁰` followed by the inverse of the
augmentation `α`, and a degree-zero element of the bicomplex whose two differentials are the
image of `z` and the restriction of a section `x` of `I₁¹` exhibits the class of `z` as minus the
class of `x` (`Stacks.CechSite.liftCycles_homologyπ_homologyMap_eq_neg`). The connecting
morphism is computed by the snake lemma on the degreewise sections of the resolving sequence
(`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionHomologyIso_conj_rightDerivedPlusδ`), and
the two computations are matched through the splittings of the resolving sequence.

## Main results

* `HigherDirectImagePresheaf.toRightDerived_comp_resolutionDerivedComparison_hom`: the comparison
  `F(I) → RF(M[0])` of an injective resolution is inverse to the identification used by
  `resolutionHomologyIso`.
* `Stacks.CechSite.cechCohomologyToCohomology_one_app_comp_resolutionHomologyIso_hom`: the
  degree-one comparison of 03AX, computed on an injective resolution.
* `Stacks.CechSite.cechCohomologyToCohomology_one_cls_eq_rightDerivedPlusδ`: the comparison is
  compatible with connecting morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HigherDirectImagePresheaf

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

omit [EnoughInjectives A] in
/-- The morphism `resolutionSingleHom I` is the augmentation `I.ι'` of the injective resolution. -/
theorem resolutionSingleHom_eq_ι' {M : A} (I : InjectiveResolution M) :
    resolutionSingleHom I = I.ι' := rfl

omit [EnoughInjectives A] in
/-- The component at `M` of `singlePlusToCochainQuotientIso` is the identity in the homotopy
category. -/
theorem ι_map_singlePlusToCochainQuotientIso_hom_app (M : A) :
    (HomotopyCategory.Plus.ι A).map (singlePlusToCochainQuotientIso.hom.app M) = 𝟙 _ := by
  rw [singlePlusToCochainQuotientIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  show (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp

omit [EnoughInjectives A] in
/-- The identification `resolutionDerivedIso I` is the quasi-isomorphism `I.plusQIso` followed by
the inverse of `DerivedCategory.Plus.qhQIso` on the resolution. -/
theorem resolutionDerivedIso_hom_eq {M : A} (I : InjectiveResolution M) :
    (resolutionDerivedIso I).hom =
      I.plusQIso.hom ≫ (DerivedCategory.Plus.qhQIso I.plusObj).inv := by
  apply ObjectProperty.hom_ext
  have h1 := Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app (C := A) 0 M
  rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app] at h1
  have h2 := (DerivedCategory.quotientCompQhIso A).inv.naturality I.ι'
  have h3 : (DerivedCategory.Plus.Qh.map (singlePlusToCochainQuotientIso.hom.app M)).hom = 𝟙 _ := by
    show DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι A).map _) = _
    rw [ι_map_singlePlusToCochainQuotientIso_hom_app]
    exact DerivedCategory.Qh.map_id _
  have h1' : ((Functor.singleFunctorPlusIsoCompQh 0).hom.app M).hom =
      (DerivedCategory.quotientCompQhIso A).inv.app ((CochainComplex.singleFunctor A 0).obj M) :=
    h1
  simp only [resolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom,
    ObjectProperty.FullSubcategory.comp_hom]
  rw [h1', h3, InjectiveResolution.plusQIso_hom_hom]
  exact (whisker_eq _ (Category.id_comp _)).trans h2.symm

/-- The comparison `I.toRightDerived F : F(I) ⟶ RF(M[0])` of an injective resolution, followed by
`resolutionDerivedComparison F I`, is the identity. -/
theorem toRightDerived_comp_resolutionDerivedComparison_hom {M : A} (I : InjectiveResolution M) :
    I.toRightDerived F ≫ (resolutionDerivedComparison F I).hom = 𝟙 _ := by
  have hr : ((DerivedCategory.Plus.qhQIso I.plusObj).hom ≫ I.plusQIso.inv) ≫
      (resolutionDerivedIso I).hom = 𝟙 _ := by
    rw [Category.assoc, resolutionDerivedIso_hom_eq]
    exact (whisker_eq _ (Iso.inv_hom_id_assoc I.plusQIso _)).trans (Iso.hom_inv_id _)
  have hX : F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj I.plusObj) ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.qhQIso I.plusObj).hom ≫
        F.rightDerivedFunctorPlus.map I.plusQIso.inv ≫ (derivedPlusResolutionIso F I).hom =
      𝟙 _ := by
    rw [derivedPlusResolutionIso_hom, ← F.rightDerivedFunctorPlus.map_comp_assoc,
      ← F.rightDerivedFunctorPlus.map_comp_assoc]
    exact (whisker_eq _ ((eq_whisker ((congrArg F.rightDerivedFunctorPlus.map hr).trans
      (F.rightDerivedFunctorPlus.map_id _)) _).trans (Category.id_comp _))).trans
        (IsIso.hom_inv_id _)
  have e : (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A).obj I.plusObj)).hom ≫
      (F.rightDerivedFunctorPlus.map (ObjectProperty.homMk
        ((DerivedCategory.quotientCompQhIso A).hom.app I.cochainComplex))).hom ≫
      (F.rightDerivedFunctorPlus.mapIso I.plusQIso).inv.hom ≫
      DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I).hom = 𝟙 _ := by
    show DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ ≫
      DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ = _
    rw [← DerivedCategory.Plus.ι.map_comp, ← DerivedCategory.Plus.ι.map_comp,
      ← DerivedCategory.Plus.ι.map_comp]
    exact (congrArg DerivedCategory.Plus.ι.map hX).trans (DerivedCategory.Plus.ι.map_id _)
  have reassoc : ∀ {D : Type _} [Category D] {P Q R S T V W : D} (x : P ⟶ Q) (U : Q ⟶ R)
      (R₁ : R ⟶ S) (R₂ : S ⟶ T) (E : T ⟶ V) (y : V ⟶ W),
      (x ≫ U ≫ R₁ ≫ R₂) ≫ E ≫ y = x ≫ (U ≫ R₁ ≫ R₂ ≫ E) ≫ y := by
    intros
    simp only [Category.assoc]
  rw [InjectiveResolution.toRightDerived_eq, resolutionDerivedComparison_hom]
  exact (reassoc _ _ _ _ _ _).trans ((whisker_eq _ ((eq_whisker e _).trans
    (Category.id_comp _))).trans (Iso.inv_hom_id_app _ _))

/-- **The cohomology of `F(I)` computes `RⁿF(M)` through `toRightDerived`**: the comparison
`F(I) ⟶ RF(M[0])` of an injective resolution, followed in cohomology by the identification
`resolutionHomologyIso`, is the canonical identification of the cohomology of `F(I)` read in the
derived category with its cohomology as a complex. -/
theorem homologyMap_toRightDerived_comp_resolutionHomologyIso_hom {M : A}
    (I : InjectiveResolution M) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).map (I.toRightDerived F) ≫
        (resolutionHomologyIso F I n).hom =
      (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app _ ≫
        (homologyFunctorObjIso _ (n : ℤ)).hom ≫ (extendedHomologyTailIso F I.cocomplex n).hom := by
  have h : (DerivedCategory.homologyFunctor B (n : ℤ)).map (I.toRightDerived F) ≫
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I).hom) ≫
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        ((DerivedCategory.quotientCompQhIso B).app ((F.mapHomologicalComplex _).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat))).hom = 𝟙 _ :=
    ((whisker_eq _ ((DerivedCategory.homologyFunctor B (n : ℤ)).map_comp _ _).symm).trans
      ((DerivedCategory.homologyFunctor B (n : ℤ)).map_comp _ _).symm).trans
      ((congrArg (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (toRightDerived_comp_resolutionDerivedComparison_hom F I)).trans
        (CategoryTheory.Functor.map_id _ _))
  exact ((reassoc_of% h) _).trans (Category.id_comp _)

omit [EnoughInjectives A] in
/-- A morphism into the degree-one term of `F` applied to the extension of `K` to `ℤ` that is
killed by the differential is still killed by the differential of `F(K)` after transport through
`extendXIso`. -/
lemma comp_map_extendXIso_hom_comp_d_eq_zero (K : CochainComplex A ℕ) {P : B}
    (ξ : P ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).X 1)
    (hξ : ξ ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).d 1 2 = 0) :
    (ξ ≫ F.map (K.extendXIso ComplexShape.embeddingUpNat (i := 1) (by simp)).hom) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).d 1 2 = 0 := by
  have hd : (K.extend ComplexShape.embeddingUpNat).d 1 2 =
      (K.extendXIso ComplexShape.embeddingUpNat (i := 1) (by simp)).hom ≫ K.d 1 2 ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i := 2) (by simp)).inv :=
    HomologicalComplex.extend_d_eq _ _ (by simp) (by simp)
  have h2 : ξ ≫ F.map ((K.extend ComplexShape.embeddingUpNat).d 1 2) = 0 := hξ
  rw [hd, F.map_comp, F.map_comp] at h2
  have h3 := h2 =≫ F.map (K.extendXIso ComplexShape.embeddingUpNat (i := 2) (by simp)).hom
  rw [Category.assoc, Category.assoc, Category.assoc, ← F.map_comp, Iso.inv_hom_id,
    F.map_id, Category.comp_id, zero_comp] at h3
  rwa [Category.assoc]

omit [EnoughInjectives A] in
/-- **A degree-one class of the extended complex, read in the original one**:
`extendedHomologyTailIso` sends the class of a cycle of `F(K)` extended by zero to the class of
the same cycle in `F(K)`. -/
theorem liftCycles_homologyπ_extendedHomologyTailIso_hom (K : CochainComplex A ℕ) {P : B}
    (ξ : P ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).X 1)
    (hξ : ξ ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).d 1 2 = 0) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).liftCycles ξ 2 (by simp) hξ ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).homologyπ 1 ≫
      (homologyFunctorObjIso _ ((1 : ℕ) : ℤ)).hom ≫ (extendedHomologyTailIso F K 1).hom =
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).liftCycles
        (ξ ≫ F.map (K.extendXIso ComplexShape.embeddingUpNat (i := 1) (by simp)).hom) 2 (by simp)
        (comp_map_extendXIso_hom_comp_d_eq_zero F K ξ hξ) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ 1 := by
  have hφ : (derivedMapExtendIso F ComplexShape.embeddingUpNat K).hom.f 1 ≫
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
        ComplexShape.embeddingUpNat (i := 1) (by simp)).hom =
      F.map (K.extendXIso ComplexShape.embeddingUpNat (i := 1) (by simp)).hom := by
    rw [Stacks.Cohomology.ModulePushforwardComparison.derivedMapExtendIso_hom_f F
      ComplexShape.embeddingUpNat K (i := 1) (by simp), Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hπ := HomologicalComplex.homologyπ_extendHomologyIso_hom
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ComplexShape.embeddingUpNat
    (j := 1) (j' := (1 : ℤ)) (by simp)
  have hi := HomologicalComplex.extendCyclesIso_hom_iCycles
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ComplexShape.embeddingUpNat
    (j := 1) (j' := (1 : ℤ)) (by simp)
  have e2 : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).liftCycles ξ 2 (by simp) hξ ≫
      HomologicalComplex.cyclesMap (derivedMapExtendIso F ComplexShape.embeddingUpNat K).hom 1 ≫
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendCyclesIso
        ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) (by simp)).hom =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).liftCycles
        (ξ ≫ F.map (K.extendXIso ComplexShape.embeddingUpNat (i := 1) (by simp)).hom) 2 (by simp)
        (comp_map_extendXIso_hom_comp_d_eq_zero F K ξ hξ) := by
    refine (cancel_mono (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles 1)).1 ?_
    rw [HomologicalComplex.liftCycles_i, Category.assoc, Category.assoc, hi,
      HomologicalComplex.liftCycles_comp_cyclesMap_assoc, HomologicalComplex.liftCycles_i_assoc,
      Category.assoc, hφ]
  have e1 := HomologicalComplex.homologyπ_naturality
    (derivedMapExtendIso F ComplexShape.embeddingUpNat K).hom 1
  exact (whisker_eq _ ((whisker_eq _ (Category.id_comp _)).trans ((reassoc_of% e1) _))).trans
    ((whisker_eq _ (whisker_eq _ hπ)).trans ((reassoc_of% e2) _))

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.CechSite

section Total

variable {A : Type*} [Category* A] [Abelian A]
  (L : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [L.HasTotal (ComplexShape.up ℤ)]

/-- **Two degree-one cycles mapping into a total complex through its two edges become opposite
in homology** once a degree-zero element of the double complex has the two of them as its
two differentials. -/
lemma liftCycles_homologyπ_homologyMap_eq_neg {B Γ : CochainComplex A ℤ}
    (β : B ⟶ L.total (ComplexShape.up ℤ)) (α : Γ ⟶ L.total (ComplexShape.up ℤ))
    (f₀ : B.X 1 ⟶ (L.X 0).X 1)
    (hβ : β.f 1 = f₀ ≫ L.ιTotal (ComplexShape.up ℤ) 0 1 1 (by simp))
    (g₁ : Γ.X 1 ⟶ (L.X 1).X 0)
    (hα : α.f 1 = g₁ ≫ L.ιTotal (ComplexShape.up ℤ) 1 0 1 (by simp))
    {P : A} (ζ : P ⟶ B.X 1) (hζ : ζ ≫ B.d 1 2 = 0) (ξ : P ⟶ Γ.X 1) (hξ : ξ ≫ Γ.d 1 2 = 0)
    (a : P ⟶ (L.X 0).X 0) (h₁ : a ≫ (L.X 0).d 0 1 = ζ ≫ f₀)
    (h₂ : a ≫ (L.d 0 1).f 0 = ξ ≫ g₁) :
    B.liftCycles ζ 2 (by simp) hζ ≫ B.homologyπ 1 ≫ HomologicalComplex.homologyMap β 1 =
      -(Γ.liftCycles ξ 2 (by simp) hξ ≫ Γ.homologyπ 1 ≫ HomologicalComplex.homologyMap α 1) := by
  rw [eq_neg_iff_add_eq_zero, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.homologyπ_naturality, HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, ← Preadditive.add_comp]
  have hsum : ζ ≫ β.f 1 + ξ ≫ α.f 1 =
      (a ≫ L.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp)) ≫
        (L.total (ComplexShape.up ℤ)).d 0 1 := by
    rw [Category.assoc, total_zero_d, Preadditive.comp_add, ← Category.assoc, h₂,
      ← Category.assoc, h₁, hβ, hα, Category.assoc, Category.assoc, add_comm]
  have hlift : (L.total (ComplexShape.up ℤ)).liftCycles (ζ ≫ β.f 1) 2 (by simp)
        (by rw [Category.assoc, β.comm, ← Category.assoc, hζ, zero_comp]) +
      (L.total (ComplexShape.up ℤ)).liftCycles (ξ ≫ α.f 1) 2 (by simp)
        (by rw [Category.assoc, α.comm, ← Category.assoc, hξ, zero_comp]) =
      (L.total (ComplexShape.up ℤ)).liftCycles
        ((a ≫ L.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp)) ≫
          (L.total (ComplexShape.up ℤ)).d 0 1) 2 (by simp) (by simp) := by
    rw [← cancel_mono ((L.total (ComplexShape.up ℤ)).iCycles 1), Preadditive.add_comp,
      HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i, hsum]
  rw [hlift]
  exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _ rfl

end Total

section Comparison

open Stacks.Cohomology.HigherDirectImagePresheaf Opposite

attribute [local instance] HasDerivedCategory.standard

universe a w v u

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify K Ab.{max a u v w}] [K.WEqualsLocallyBijective Ab.{max a u v w}]
  [EnoughInjectives (Sheaf K Ab.{max a u v w})]
  (hE : Sieve.generate E.presieve₀ ∈ K U)

omit [K.WEqualsLocallyBijective Ab] in
/-- **The degree-one comparison of Stacks 03AX through an injective resolution**: read through
`resolutionHomologyIso`, it is the map induced in first homology by the edge `β` of the Čech
bicomplex, followed by the inverse of the map induced by the other edge `α`. -/
theorem cechCohomologyToCohomology_one_app_comp_resolutionHomologyIso_hom
    {G : Sheaf K Ab.{max a u v w}} (I : InjectiveResolution G) :
    (cechCohomologyToCohomology.{a} K E hE 1).app G ≫
        (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U)) I 1).hom =
      (DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).hom.app
          ((cechComplexIntFunctor.{a} K E).obj G) ≫
        (homologyFunctorObjIso ((cechComplexIntFunctor.{a} K E).obj G) 1).hom ≫
        HomologicalComplex.homologyMap (cechToTotal.{a} K E G I) 1 ≫
        inv (HomologicalComplex.homologyMap (totalAugmentation.{a} K E hE I.cochainComplex) 1) ≫
        (homologyFunctorObjIso _ ((1 : ℕ) : ℤ)).hom ≫
        (extendedHomologyTailIso ((sheafSections K Ab.{max a u v w}).obj (op U))
          I.cocomplex 1).hom := by
  have hc : (cechCohomologyToCohomology.{a} K E hE 1).app G =
      (DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map
        (cechComparison.{a} K E hE G I) := by
    rw [← cechComparison_eq.{a, w, v, u} K E hE G I]
    rfl
  have h1 := DerivedCategory.homologyFunctorFactors_hom_naturality (cechToTotal.{a} K E G I) 1
  have h2 := DerivedCategory.homologyFunctorFactors_hom_naturality
    (totalAugmentation.{a} K E hE I.cochainComplex) 1
  let e := asIso (HomologicalComplex.homologyMap (totalAugmentation.{a} K E hE I.cochainComplex) 1)
  have h3 : (DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map
        (inv (DerivedCategory.Q.map (totalAugmentation.{a} K E hE I.cochainComplex))) ≫
        (DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).hom.app
          ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I.cochainComplex) =
      (DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).hom.app _ ≫ e.inv := by
    rw [Functor.map_inv]
    exact (IsIso.inv_comp_eq _).2 (((whisker_eq _ e.hom_inv_id).trans
      (Category.comp_id _)).symm.trans ((reassoc_of% h2) _).symm)
  rw [hc, cechComparison, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  refine ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ (homologyMap_toRightDerived_comp_resolutionHomologyIso_hom _ I 1))))).trans ?_
  have h4 := (reassoc_of% h3) ((homologyFunctorObjIso _ ((1 : ℕ) : ℤ)).hom ≫
        (extendedHomologyTailIso ((sheafSections K Ab.{max a u v w}).obj (op U))
          I.cocomplex 1).hom)
  have h5 := (reassoc_of% h1) (e.inv ≫ (homologyFunctorObjIso _ ((1 : ℕ) : ℤ)).hom ≫
        (extendedHomologyTailIso ((sheafSections K Ab.{max a u v w}).obj (op U))
          I.cocomplex 1).hom)
  exact (whisker_eq _ h4).trans (h5.trans (whisker_eq _ (Category.id_comp _).symm))

end Comparison

section Classes

open Opposite

attribute [local instance] HasDerivedCategory.standard

universe a w v u

/-- A morphism out of `ℤ` given by an element, followed by a morphism `f`, is the morphism out of
`ℤ` given by the image of that element under `f`. -/
private lemma uliftZMultiplesHom_comp_eq {M N : AddCommGrpCat.{a}} (x : M) (y : N) (f : M ⟶ N)
    (h : f x = y) :
    AddCommGrpCat.ofHom (uliftZMultiplesHom M x) ≫ f =
      AddCommGrpCat.ofHom (uliftZMultiplesHom N y) := by
  ext n
  show f (n.down • x) = n.down • y
  rw [map_zsmul, h]

/-- An element of an abelian group whose image under a morphism vanishes gives a morphism out of
`ℤ` whose composite with that morphism vanishes. -/
lemma uliftZMultiplesHom_comp_eq_zero {M N : AddCommGrpCat.{a}} (x : M) (f : M ⟶ N)
    (h : f x = 0) : AddCommGrpCat.ofHom (uliftZMultiplesHom M x) ≫ f = 0 := by
  ext n
  show f (n.down • x) = 0
  rw [map_zsmul, h, smul_zero]

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U) [HasProducts.{w} Ab.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- A Čech cochain, as a morphism out of `ℤ` into the corresponding term of the Čech complex. -/
noncomputable def cochainHom (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (n : ℕ) (c : cechCochain E F n) :
    AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶ (cechComplex E F).X n :=
  AddCommGrpCat.ofHom (uliftZMultiplesHom ((cechComplex E F).X n)
    ((productAddEquiv (cochainFactor E F n)).symm c))

/-- `cochainHom` turns the Čech differential into composition with the differential of the Čech
complex. -/
lemma cochainHom_comp_d (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (n : ℕ) (c : cechCochain E F n) :
    cochainHom.{a} E F n c ≫ (cechComplex E F).d n (n + 1) =
      cochainHom.{a} E F (n + 1) (cechDifferential E F n c) := by
  refine uliftZMultiplesHom_comp_eq _ _ _ ?_
  apply (productAddEquiv (cochainFactor E F (n + 1))).injective
  refine (cechDifferential_productAddEquiv E F n _).symm.trans ?_
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- `cochainHom` is natural in the presheaf: its composite with the map of Čech complexes induced
by `φ` is `cochainHom` of the cochain pushed forward along `φ`. -/
lemma cochainHom_comp_map {F F' : Cᵒᵖ ⥤ Ab.{max a u v w}} (φ : F ⟶ F') (n : ℕ)
    (c : cechCochain E F n) :
    cochainHom.{a} E F n c ≫ ((cechComplexFunctor E).map φ).f n =
      cochainHom.{a} E F' n (pushCochain E φ n c) := by
  refine uliftZMultiplesHom_comp_eq _ _ _ ?_
  apply (productAddEquiv (cochainFactor E F' n)).injective
  rw [AddEquiv.apply_symm_apply]
  funext k
  exact (cechComplexFunctor_map_f_π_apply E φ n k _).trans
    (congrArg (φ.app _) (congrFun ((productAddEquiv (cochainFactor E F n)).apply_symm_apply c) k))

/-- `cochainHom` is additive in the cochain. -/
lemma cochainHom_add (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (n : ℕ) (c c' : cechCochain E F n) :
    cochainHom.{a} E F n (c + c') = cochainHom.{a} E F n c + cochainHom.{a} E F n c' := by
  ext m
  show m.down • (productAddEquiv _).symm (c + c') =
    m.down • (productAddEquiv _).symm c + m.down • (productAddEquiv _).symm c'
  rw [map_add, smul_add]

/-- `cochainHom` commutes with negation of the cochain. -/
lemma cochainHom_neg (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (n : ℕ) (c : cechCochain E F n) :
    cochainHom.{a} E F n (-c) = -cochainHom.{a} E F n c := by
  ext m
  show m.down • (productAddEquiv _).symm (-c) = -(m.down • (productAddEquiv _).symm c)
  rw [map_neg, smul_neg]

/-- The degree-zero Čech cochain of restrictions of a section over the covered object. -/
noncomputable def augCochain (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (t : F.obj (op U)) :
    cechCochain E F 0 :=
  productAddEquiv (cochainFactor E F 0) (cechAugmentationPre.{a} E F t)

/-- The Čech differential of the cochain of restrictions of a section vanishes. -/
lemma cechDifferential_augCochain (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (t : F.obj (op U)) :
    cechDifferential E F 0 (augCochain.{a} E F t) = 0 := by
  refine (cechDifferential_productAddEquiv E F 0 _).trans ?_
  exact (congrArg (productAddEquiv (cochainFactor E F 1))
    (ConcreteCategory.congr_hom (cechAugmentationPre_comp_d.{a} E F) t)).trans (map_zero _)

omit [HasProducts Ab] in
/-- Pushing the cochain of restrictions of `t` forward along `φ` gives the cochain of
restrictions of `φ t`. -/
lemma pushCochain_augCochain {F F' : Cᵒᵖ ⥤ Ab.{max a u v w}} (φ : F ⟶ F') (t : F.obj (op U)) :
    pushCochain E φ 0 (augCochain.{a} E F t) = augCochain.{a} E F' (φ.app (op U) t) := by
  funext k
  show φ.app _ (Pi.π (cochainFactor E F 0) k (cechAugmentationPre.{a} E F t)) =
    Pi.π (cochainFactor E F' 0) k (cechAugmentationPre.{a} E F' (φ.app (op U) t))
  rw [cechAugmentationPre_π_apply, cechAugmentationPre_π_apply]
  exact (NatTrans.naturality_apply φ ((Over.forget U).map (Over.mkIdTerminal.from
    (∏ᶜ fun b : Fin 1 ↦ Over.mk (E.f (k b))))).op t)

omit [HasProducts Ab] in
/-- `augCochain` commutes with negation of the section. -/
lemma augCochain_neg (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (t : F.obj (op U)) :
    augCochain.{a} E F (-t) = -augCochain.{a} E F t := by
  rw [augCochain, augCochain, map_neg]
  exact map_neg (productAddEquiv (cochainFactor E F 0)) _

/-- The morphism out of `ℤ` given by a section `t`, followed by the Čech augmentation, is
`cochainHom` of the cochain of restrictions of `t`. -/
lemma uliftZMultiplesHom_comp_cechAugmentationPre (F : Cᵒᵖ ⥤ Ab.{max a u v w})
    (t : F.obj (op U)) :
    AddCommGrpCat.ofHom (uliftZMultiplesHom (F.obj (op U)) t) ≫ cechAugmentationPre.{a} E F =
      cochainHom.{a} E F 0 (augCochain.{a} E F t) := by
  refine uliftZMultiplesHom_comp_eq _ _ _ ?_
  rw [augCochain]
  exact ((productAddEquiv (cochainFactor E F 0)).symm_apply_apply _).symm

omit [HasProducts Ab] in
/-- Pushing a cochain forward along the identity does nothing. -/
lemma pushCochain_id (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (n : ℕ) (c : cechCochain E F n) :
    pushCochain E (𝟙 F) n c = c :=
  rfl

omit [HasProducts Ab] in
/-- Pushing a cochain forward along the zero morphism gives zero. -/
lemma pushCochain_zero (F F' : Cᵒᵖ ⥤ Ab.{max a u v w}) (n : ℕ) (c : cechCochain E F n) :
    pushCochain E (0 : F ⟶ F') n c = 0 :=
  rfl

/-- The degree-one cochain of the Čech complex underlying a Čech `1`-cocycle, as a morphism out
of `ℤ`. -/
noncomputable def cocycleHom (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (z : cocycles1 E F) :
    AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶ (cechComplex E F).X 1 :=
  AddCommGrpCat.ofHom (uliftZMultiplesHom ((cechComplex E F).X 1)
    ((productAddEquiv (cochainFactor E F 1)).symm z))

/-- The morphism out of `ℤ` given by a Čech `1`-cocycle is killed by the Čech differential. -/
lemma cocycleHom_comp_d (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (z : cocycles1 E F) :
    cocycleHom.{a} E F z ≫ (cechComplex E F).d 1 2 = 0 :=
  uliftZMultiplesHom_comp_eq_zero _ _ ((productAddEquiv_mem_cocycles1_iff E F _).1
    (by simpa only [AddEquiv.apply_symm_apply] using z.2))

/-- The morphism out of `ℤ` given by a Čech `1`-cocycle of a sheaf `G`, transported through
`cechIntXIsoPre` to the complex `(cechComplexIntFunctor K E).obj G`, is killed by its
differential. -/
lemma cocycleHom_comp_cechIntXIsoPre_inv_comp_d (G : Sheaf K Ab.{max a u v w})
    (z : cocycles1 E G.obj) :
    (cocycleHom.{a} E G.obj z ≫ (cechIntXIsoPre.{a} E G.obj 1 1 (by simp)).inv) ≫
      ((cechComplexIntFunctor.{a} K E).obj G).d 1 2 = 0 := by
  have hd : ((cechComplexIntFunctor.{a} K E).obj G).d 1 2 =
      (cechIntXIsoPre.{a} E G.obj 1 1 (by simp)).hom ≫ (cechComplex E G.obj).d 1 2 ≫
        (cechIntXIsoPre.{a} E G.obj 2 2 (by simp)).inv :=
    cechComplexIntFunctorPre_d.{a} E G.obj 1 1 2 (by simp) (by simp)
  rw [Category.assoc, hd, Iso.inv_hom_id_assoc, reassoc_of% cocycleHom_comp_d, zero_comp]

/-- The degree-one cycle of the integer-graded Čech complex of a sheaf attached to a Čech
`1`-cocycle. -/
noncomputable def intCycleOfCocycle (G : Sheaf K Ab.{max a u v w}) (z : cocycles1 E G.obj) :
    AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶ ((cechComplexIntFunctor.{a} K E).obj G).cycles 1 :=
  ((cechComplexIntFunctor.{a} K E).obj G).liftCycles
    (cocycleHom.{a} E G.obj z ≫ (cechIntXIsoPre.{a} E G.obj 1 1 (by simp)).inv) 2 (by simp)
    (cocycleHom_comp_cechIntXIsoPre_inv_comp_d.{a} K E G z)

open Stacks.Cohomology.HigherDirectImagePresheaf in
/-- **The class of a Čech `1`-cocycle in the degree-one homology of the integer-graded Čech
complex**, read through `Stacks.CechSite.cechH1Equiv`. -/
theorem homologyFunctorFactors_cechH1Equiv_symm_cls (G : Sheaf K Ab.{max a u v w})
    (z : cocycles1 E G.obj) :
    (homologyFunctorObjIso ((cechComplexIntFunctor.{a} K E).obj G) 1).hom
      ((DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).hom.app
        ((cechComplexIntFunctor.{a} K E).obj G) ((cechH1Equiv.{a} K E G).symm (cls E G.obj z))) =
      (intCycleOfCocycle.{a} K E G z ≫
        ((cechComplexIntFunctor.{a} K E).obj G).homologyπ 1) ⟨1⟩ := by
  have key : cechCohomologyOneEquiv E G.obj
      (((cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2 (by simp)
        (cocycleHom_comp_d.{a} E G.obj z) ≫ (cechComplex E G.obj).homologyπ 1) ⟨1⟩) =
      cls E G.obj z := by
    have hm : (cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2 (by simp)
          (cocycleHom_comp_d.{a} E G.obj z) ≫ (cechComplex E G.obj).homologyπ 1 ≫
          ((cechComplex E G.obj).homologyIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
          ((cechComplex E G.obj).sc' 0 1 2).abHomologyIso.hom =
        ((cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2 (by simp)
          (cocycleHom_comp_d.{a} E G.obj z) ≫
          ((cechComplex E G.obj).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
          ((cechComplex E G.obj).sc' 0 1 2).abLeftHomologyData.cyclesIso.hom) ≫
          ((cechComplex E G.obj).sc' 0 1 2).abLeftHomologyData.π := by
      rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc]
      simp only [Category.assoc]
      exact whisker_eq _ (whisker_eq _
        (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _
          ((cechComplex E G.obj).sc' 0 1 2).abLeftHomologyData))
    have hi : (cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2 (by simp)
          (cocycleHom_comp_d.{a} E G.obj z) ≫
          ((cechComplex E G.obj).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
          ((cechComplex E G.obj).sc' 0 1 2).abLeftHomologyData.cyclesIso.hom ≫
          ((cechComplex E G.obj).sc' 0 1 2).abLeftHomologyData.i = cocycleHom.{a} E G.obj z := by
      rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
        HomologicalComplex.cyclesIsoSc'_hom_iCycles]
      exact HomologicalComplex.liftCycles_i _ _ _ _ _
    have hq := ConcreteCategory.congr_hom hm ⟨1⟩
    have hw := ConcreteCategory.congr_hom hi ⟨1⟩
    have h1 : homologyEquivQuotient (cechComplex E G.obj) 0 1 2 (by simp) (by simp)
        (((cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2 (by simp)
          (cocycleHom_comp_d.{a} E G.obj z) ≫ (cechComplex E G.obj).homologyπ 1) ⟨1⟩) =
        QuotientAddGroup.mk (((cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2
          (by simp) (cocycleHom_comp_d.{a} E G.obj z) ≫
          ((cechComplex E G.obj).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
          ((cechComplex E G.obj).sc' 0 1 2).abLeftHomologyData.cyclesIso.hom) ⟨1⟩) := hq
    rw [cechCohomologyOneEquiv, AddEquiv.trans_apply, h1]
    refine (congrArg QuotientAddGroup.mk (Subtype.ext ?_) : _ = cls E G.obj z)
    refine (congrArg (productAddEquiv (cochainFactor E G.obj 1)) (hw.trans ?_)).trans
      (AddEquiv.apply_symm_apply _ _)
    exact one_zsmul _
  have hext : intCycleOfCocycle.{a} K E G z ≫ ((cechComplexIntFunctor.{a} K E).obj G).homologyπ 1 ≫
      ((cechComplex E G.obj).extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) (by simp)).hom =
      (cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2 (by simp)
        (cocycleHom_comp_d.{a} E G.obj z) ≫ (cechComplex E G.obj).homologyπ 1 := by
    have hπ : ((cechComplexIntFunctor.{a} K E).obj G).homologyπ 1 ≫
        ((cechComplex E G.obj).extendHomologyIso ComplexShape.embeddingUpNat
          (j := 1) (j' := (1 : ℤ)) (by simp)).hom =
        ((cechComplex E G.obj).extendCyclesIso ComplexShape.embeddingUpNat
          (j := 1) (j' := (1 : ℤ)) (by simp)).hom ≫ (cechComplex E G.obj).homologyπ 1 :=
      HomologicalComplex.homologyπ_extendHomologyIso_hom _ _ _
    have hi : ((cechComplex E G.obj).extendCyclesIso ComplexShape.embeddingUpNat
          (j := 1) (j' := (1 : ℤ)) (by simp)).hom ≫ (cechComplex E G.obj).iCycles 1 =
        ((cechComplexIntFunctor.{a} K E).obj G).iCycles 1 ≫
          ((cechComplex E G.obj).extendXIso ComplexShape.embeddingUpNat
            (i' := (1 : ℤ)) (i := 1) (by simp)).hom :=
      HomologicalComplex.extendCyclesIso_hom_iCycles _ _ _
    have hc : intCycleOfCocycle.{a} K E G z ≫ ((cechComplex E G.obj).extendCyclesIso
          ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) (by simp)).hom =
        (cechComplex E G.obj).liftCycles (cocycleHom.{a} E G.obj z) 2 (by simp)
          (cocycleHom_comp_d.{a} E G.obj z) := by
      have hl : intCycleOfCocycle.{a} K E G z ≫ ((cechComplexIntFunctor.{a} K E).obj G).iCycles 1 =
          cocycleHom.{a} E G.obj z ≫ (cechIntXIsoPre.{a} E G.obj 1 1 (by simp)).inv :=
        HomologicalComplex.liftCycles_i _ _ _ _ _
      refine (cancel_mono ((cechComplex E G.obj).iCycles 1)).1 ?_
      refine ((Category.assoc _ _ _).trans ((whisker_eq _ hi).trans ?_)).trans
        (HomologicalComplex.liftCycles_i _ _ _ _ _).symm
      exact (Category.assoc _ _ _).symm.trans ((eq_whisker hl _).trans ((Category.assoc _ _ _).trans
        ((whisker_eq _ (Iso.inv_hom_id _)).trans (Category.comp_id _))))
    exact (whisker_eq _ hπ).trans ((Category.assoc _ _ _).symm.trans (eq_whisker hc _))
  have h2 : cechH1Equiv.{a} K E G
      ((DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).inv.app
      ((cechComplexIntFunctor.{a} K E).obj G) ((intCycleOfCocycle.{a} K E G z ≫
        ((cechComplexIntFunctor.{a} K E).obj G).homologyπ 1) ⟨1⟩)) = cls E G.obj z := by
    rw [← key, ← hext]
    refine congrArg (cechCohomologyOneEquiv E G.obj) ?_
    refine (congrArg (ConcreteCategory.hom ((cechComplex E G.obj).extendHomologyIso
      ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) (by simp)).hom)
      (ConcreteCategory.congr_hom
        ((DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).inv_hom_id_app _) _)).trans ?_
    rfl
  rw [← h2]
  exact (congrArg (fun t ↦ (homologyFunctorObjIso ((cechComplexIntFunctor.{a} K E).obj G) 1).hom
      ((DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).hom.app
        ((cechComplexIntFunctor.{a} K E).obj G) t))
      (AddEquiv.symm_apply_apply _ _)).trans
    (ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).inv_hom_id_app _) _)

variable [HasSheafify K Ab.{max a u v w}] [K.WEqualsLocallyBijective Ab.{max a u v w}]
  [EnoughInjectives (Sheaf K Ab.{max a u v w})] (hE : Sieve.generate E.presieve₀ ∈ K U)

omit [K.WEqualsLocallyBijective Ab] in
open Stacks.Cohomology.HigherDirectImagePresheaf in
/-- **The degree-one comparison of Stacks 03AX on the class of a Čech cocycle, through an
injective resolution `I` of `G`.** Let `z` be a Čech `1`-cocycle of `G`, and suppose a
degree-zero element `a` of the Čech bicomplex of `I` has Čech differential the image of `z` in
`I⁰` and resolution differential the restriction of a section `x` of `I¹` over `U`. Then the
image of the class of `z` in `H¹(U, G)`, computed on `I`, is minus the class of `x`. -/
theorem resolutionHomologyIso_cechCohomologyToCohomology_one_cls
    {G : Sheaf K Ab.{max a u v w}} (I : InjectiveResolution G) (z : cocycles1 E G.obj)
    (a : AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶
      ((cechBicomplex.{a} K E I.cochainComplex).X 0).X 0)
    (x : AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.cochainComplex).X 1)
    (hx : x ≫ ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.cochainComplex).d 1 2 = 0)
    (h₁ : a ≫ ((cechBicomplex.{a} K E I.cochainComplex).X 0).d 0 1 =
      (cocycleHom.{a} E G.obj z ≫ (cechIntXIsoPre.{a} E G.obj 1 1 (by simp)).inv) ≫
        ((cechComplexIntFunctor.{a} K E).map I.inclusionZero).f 1)
    (h₂ : a ≫ ((cechBicomplex.{a} K E I.cochainComplex).d 0 1).f 0 =
      x ≫ cechAugmentationInt.{a} K E (I.cochainComplex.X 1)) :
    (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U)) I 1).hom
        ((cechCohomologyToCohomology.{a} K E hE 1).app G
          ((cechH1Equiv.{a} K E G).symm (cls E G.obj z))) =
      -(((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.cochainComplex).liftCycles x 2 (by simp) hx ≫
        ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.cochainComplex).homologyπ 1 ≫
        (homologyFunctorObjIso _ ((1 : ℕ) : ℤ)).hom ≫
        (extendedHomologyTailIso ((sheafSections K Ab.{max a u v w}).obj (op U))
          I.cocomplex 1).hom) ⟨1⟩ := by
  have hC1 := liftCycles_homologyπ_homologyMap_eq_neg (cechBicomplex.{a} K E I.cochainComplex)
    (cechToTotal.{a} K E G I) (totalAugmentation.{a} K E hE I.cochainComplex)
    (((cechComplexIntFunctor.{a} K E).map I.inclusionZero).f 1) rfl
    (cechAugmentationInt.{a} K E (I.cochainComplex.X 1))
    (totalAugmentation_f.{a} K E hE I.cochainComplex 1)
    (cocycleHom.{a} E G.obj z ≫ (cechIntXIsoPre.{a} E G.obj 1 1 (by simp)).inv)
    (cocycleHom_comp_cechIntXIsoPre_inv_comp_d.{a} K E G z) x hx a h₁ h₂
  have hcomp := ConcreteCategory.congr_hom
    (cechCohomologyToCohomology_one_app_comp_resolutionHomologyIso_hom.{a} K E hE I)
    ((cechH1Equiv.{a} K E G).symm (cls E G.obj z))
  have R := homologyFunctorFactors_cechH1Equiv_symm_cls.{a} K E G z
  have step1 := congrArg (ConcreteCategory.hom
    (HomologicalComplex.homologyMap (cechToTotal.{a} K E G I) 1 ≫
      inv (HomologicalComplex.homologyMap (totalAugmentation.{a} K E hE I.cochainComplex) 1) ≫
      (homologyFunctorObjIso _ ((1 : ℕ) : ℤ)).hom ≫
      (extendedHomologyTailIso ((sheafSections K Ab.{max a u v w}).obj (op U))
        I.cocomplex 1).hom)) R
  have step2 := congrArg (fun f ↦ ConcreteCategory.hom (f ≫
      inv (HomologicalComplex.homologyMap (totalAugmentation.{a} K E hE I.cochainComplex) 1) ≫
      (homologyFunctorObjIso _ ((1 : ℕ) : ℤ)).hom ≫
      (extendedHomologyTailIso ((sheafSections K Ab.{max a u v w}).obj (op U))
        I.cocomplex 1).hom) (ULift.up (1 : ℤ) : ULift.{max a u v w} ℤ)) hC1
  refine hcomp.trans (step1.trans (step2.trans ?_))
  dsimp only
  rw [Preadditive.neg_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rfl

omit [K.WEqualsLocallyBijective Ab] in
open Stacks.Cohomology.HigherDirectImagePresheaf in
/-- **The degree-one comparison of Stacks 03AX is compatible with connecting morphisms.** Let
`0 → S₁ → S₂ → S₃ → 0` be a short exact sequence of abelian sheaves, `z` a Čech `1`-cocycle of
`S₁` which becomes the Čech coboundary of a degree-zero cochain `b` of `S₂`, and `q` the section
of `S₃` over `U` glued from the images of `b`. Then the comparison sends the class of `z` to the
image of `q` under the connecting morphism `H⁰(U, S₃) → H¹(U, S₁)`. -/
theorem cechCohomologyToCohomology_one_cls_eq_rightDerivedPlusδ
    (S : ShortComplex (Sheaf K Ab.{max a u v w})) (hS : S.ShortExact)
    (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1))
    (q : S.X₃.obj.obj (op U))
    (hq : augCochain.{a} E S.X₃.obj q = pushCochain E S.g.hom 0 b) :
    (cechCohomologyToCohomology.{a} K E hE 1).app S.X₁
        ((cechH1Equiv.{a} K E S.X₁).symm (cls E S.X₁.obj z)) =
      Stacks.Cohomology.CechDelta.rightDerivedPlusδ
        ((sheafSections K Ab.{max a u v w}).obj (op U)) hS 0
        ((derivedPlusToStandard ((sheafSections K Ab.{max a u v w}).obj (op U)) 0).inv.app S.X₃
          (((sheafSections K Ab.{max a u v w}).obj (op U)).toRightDerivedZero.app S.X₃ q)) := by
  let H := Stacks.Cohomology.RightDerivedDelta.horseshoe hS
  have hdeg : ∀ n, ((ShortComplex.mk H.f H.g H.w).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) n)).ShortExact := fun n ↦
    (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 H.shortExact n
  have hinj : ∀ n, Injective (((ShortComplex.mk H.f H.g H.w).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) n)).X₁) := fun n ↦ H.J₁.injective n
  let sp : ∀ n, ((ShortComplex.mk H.f H.g H.w).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) n)).Splitting := fun n ↦
    have := hinj n; (hdeg n).splittingOfInjective
  -- the augmentations of the three resolutions
  obtain ⟨ι₁, hι₁⟩ : ∃ φ : S.X₁ ⟶ H.J₁.cocomplex.X 0, φ = H.J₁.ι.f 0 := ⟨_, rfl⟩
  obtain ⟨ι₂, hι₂⟩ : ∃ φ : S.X₂ ⟶ H.J₂.cocomplex.X 0, φ = H.J₂.ι.f 0 := ⟨_, rfl⟩
  obtain ⟨ι₃, hι₃⟩ : ∃ φ : S.X₃ ⟶ H.J₃.cocomplex.X 0, φ = H.J₃.ι.f 0 := ⟨_, rfl⟩
  have c₁ : ι₁ ≫ H.f.f 0 = S.f ≫ ι₂ := by
    rw [hι₁, hι₂]
    exact H.comm₁
  have c₂ : ι₂ ≫ H.g.f 0 = S.g ≫ ι₃ := by
    rw [hι₂, hι₃]
    exact H.comm₂
  have d₂ : ι₂ ≫ H.J₂.cocomplex.d 0 1 = 0 := by
    rw [hι₂]
    exact InjectiveResolution.ι_f_zero_comp_complex_d _
  have d₃ : ι₃ ≫ H.J₃.cocomplex.d 0 1 = 0 := by
    rw [hι₃]
    exact InjectiveResolution.ι_f_zero_comp_complex_d _
  obtain ⟨r₀, s₀, fr₀, sg₀, id₀⟩ : ∃ (r : H.J₂.cocomplex.X 0 ⟶ H.J₁.cocomplex.X 0)
      (s : H.J₃.cocomplex.X 0 ⟶ H.J₂.cocomplex.X 0), H.f.f 0 ≫ r = 𝟙 _ ∧
        s ≫ H.g.f 0 = 𝟙 _ ∧ r ≫ H.f.f 0 + H.g.f 0 ≫ s = 𝟙 _ :=
    ⟨(sp 0).r, (sp 0).s, (sp 0).f_r, (sp 0).s_g, (sp 0).id⟩
  obtain ⟨r₁, s₁, fr₁, id₁⟩ : ∃ (r : H.J₂.cocomplex.X 1 ⟶ H.J₁.cocomplex.X 1)
      (s : H.J₃.cocomplex.X 1 ⟶ H.J₂.cocomplex.X 1), H.f.f 1 ≫ r = 𝟙 _ ∧
        r ≫ H.f.f 1 + H.g.f 1 ≫ s = 𝟙 _ :=
    ⟨(sp 1).r, (sp 1).s, (sp 1).f_r, (sp 1).id⟩
  obtain ⟨r₂, fr₂⟩ : ∃ (r : H.J₂.cocomplex.X 2 ⟶ H.J₁.cocomplex.X 2), H.f.f 2 ≫ r = 𝟙 _ :=
    ⟨(sp 2).r, (sp 2).f_r⟩
  -- sections over `U`
  have app : ∀ {P Q : Sheaf K Ab.{max a u v w}} {f g : P ⟶ Q}, f = g →
      ∀ (V : Cᵒᵖ) (t : P.obj.obj V), f.hom.app V t = g.hom.app V t := fun h V t ↦ by rw [h]
  have split : ∀ {P Q R : Sheaf K Ab.{max a u v w}} (f : P ⟶ Q) (g : Q ⟶ R) (r : Q ⟶ P)
      (s : R ⟶ Q), r ≫ f + g ≫ s = 𝟙 Q → ∀ (V : Cᵒᵖ) (t : Q.obj.obj V),
      g.hom.app V t = 0 → f.hom.app V (r.hom.app V t) = t := fun f g r s h V t ht ↦ by
    have h := app h V t
    rw [Sheaf.Hom.add_app] at h
    have h' : f.hom.app V (r.hom.app V t) + s.hom.app V (g.hom.app V t) = t := h
    rwa [ht, map_zero, add_zero] at h'
  let y : (H.J₂.cocomplex.X 0).obj.obj (op U) := s₀.hom.app (op U) (ι₃.hom.app (op U) q)
  have F1 : (H.g.f 0).hom.app (op U) y = ι₃.hom.app (op U) q :=
    app sg₀ _ _
  have h2 : (H.J₃.cocomplex.d 0 1).hom.app (op U) (ι₃.hom.app (op U) q) = 0 :=
    (app d₃ _ q).trans rfl
  have h1 : (H.g.f 1).hom.app (op U) ((H.J₂.cocomplex.d 0 1).hom.app (op U) y) =
      (H.J₃.cocomplex.d 0 1).hom.app (op U) ((H.g.f 0).hom.app (op U) y) :=
    (app (H.g.comm 0 1) _ y).symm
  have hgd : (H.g.f 1).hom.app (op U) ((H.J₂.cocomplex.d 0 1).hom.app (op U) y) = 0 :=
    h1.trans ((congrArg _ F1).trans h2)
  let x₁ : (H.J₁.cocomplex.X 1).obj.obj (op U) :=
    r₁.hom.app (op U) ((H.J₂.cocomplex.d 0 1).hom.app (op U) y)
  have F2 : (H.f.f 1).hom.app (op U) x₁ = (H.J₂.cocomplex.d 0 1).hom.app (op U) y :=
    split _ _ _ _ id₁ _ _ hgd
  have F3 : (H.J₁.cocomplex.d 1 2).hom.app (op U) x₁ = 0 := by
    have hc := app (H.f.comm 1 2) _ x₁
    have hdd := app (H.J₂.cocomplex.d_comp_d 0 1 2) _ y
    have hr := app fr₂ _ ((H.J₁.cocomplex.d 1 2).hom.app (op U) x₁)
    have e : (H.f.f 2).hom.app (op U) ((H.J₁.cocomplex.d 1 2).hom.app (op U) x₁) = 0 := by
      refine hc.symm.trans ?_
      show (H.J₂.cocomplex.d 1 2).hom.app (op U) ((H.f.f 1).hom.app (op U) x₁) = 0
      rw [F2]
      exact hdd
    refine hr.symm.trans ?_
    show r₂.hom.app (op U) ((H.f.f 2).hom.app (op U) _) = 0
    rw [e, map_zero]
  -- the degree-zero cochain `w` of the first resolution
  let v : cechCochain E (H.J₂.cocomplex.X 0).obj 0 :=
    augCochain.{a} E (H.J₂.cocomplex.X 0).obj y - pushCochain E ι₂.hom 0 b
  have W1 : pushCochain E (H.g.f 0).hom 0 v = 0 := by
    have e1 : pushCochain E (H.g.f 0).hom 0 (pushCochain E ι₂.hom 0 b) =
        pushCochain E ι₃.hom 0 (pushCochain E S.g.hom 0 b) := by
      rw [pushCochain_comp, pushCochain_comp]
      exact congrArg (fun φ ↦ pushCochain E φ 0 b) (congrArg (fun φ ↦ φ.hom) c₂)
    simp only [v, map_sub, e1, pushCochain_augCochain.{a}, ← hq]
    rw [F1, sub_self]
  let w : cechCochain E (H.J₁.cocomplex.X 0).obj 0 := pushCochain E r₀.hom 0 v
  have W2 : pushCochain E (H.f.f 0).hom 0 w = v := by
    funext k
    exact split _ _ _ _ id₀ _ _ (congrFun W1 k)
  have N1 : cechDifferential E (H.J₁.cocomplex.X 0).obj 0 (-w) = pushCochain E ι₁.hom 1 z := by
    have dv : cechDifferential E _ 0 v = -pushCochain E (ι₁.hom ≫ (H.f.f 0).hom) 1 z := by
      simp only [v, map_sub, cechDifferential_augCochain.{a}, cechDifferential_pushCochain, hb,
        zero_sub, pushCochain_comp]
      rw [show ι₁.hom ≫ (H.f.f 0).hom = S.f.hom ≫ ι₂.hom from congrArg (·.hom) c₁]
    rw [map_neg, cechDifferential_pushCochain, dv, map_neg, neg_neg, pushCochain_comp,
      show (ι₁.hom ≫ (H.f.f 0).hom) ≫ r₀.hom = ι₁.hom from
        (Category.assoc _ _ _).trans ((whisker_eq _ (congrArg (·.hom) fr₀)).trans
          (Category.comp_id _))]
  have N2 : pushCochain E (H.J₁.cocomplex.d 0 1).hom 0 (-w) =
      -augCochain.{a} E (H.J₁.cocomplex.X 1).obj x₁ := by
    have inj : Function.Injective (pushCochain E (H.f.f 1).hom 0) := fun c c' h ↦ by
      have h' := congrArg (pushCochain E r₁.hom 0) h
      rwa [pushCochain_comp, pushCochain_comp,
        show (H.f.f 1).hom ≫ r₁.hom = 𝟙 _ from congrArg (·.hom) fr₁, pushCochain_id.{a},
        pushCochain_id.{a}] at h'
    apply inj
    rw [map_neg, map_neg, map_neg, pushCochain_comp, pushCochain_augCochain.{a}, F2,
      show (H.J₁.cocomplex.d 0 1).hom ≫ (H.f.f 1).hom =
        (H.f.f 0).hom ≫ (H.J₂.cocomplex.d 0 1).hom from congrArg (·.hom) (H.f.comm 0 1).symm,
      ← pushCochain_comp, W2]
    simp only [v, map_sub, pushCochain_augCochain.{a}, pushCochain_comp]
    rw [show ι₂.hom ≫ (H.J₂.cocomplex.d 0 1).hom = 0 from congrArg (·.hom) d₂, pushCochain_zero.{a},
      sub_zero]
  -- the right-hand side, by the horseshoe computation of the connecting morphism
  have hFR : ((ShortComplex.mk H.f H.g H.w).map (((sheafSections K Ab.{max a u v w}).obj
      (op U)).mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact :=
    H.shortExact_mapSequence _
  have B1 := resolutionHomologyIso_conj_rightDerivedPlusδ
    ((sheafSections K Ab.{max a u v w}).obj (op U)) hS H.J₁ H.J₂ H.J₃ H.f H.g H.w
    H.comm₁ H.comm₂ H.shortExact hFR 0
  have B2 := toRightDerivedZero_comp_resolutionHomologyIso
    ((sheafSections K Ab.{max a u v w}).obj (op U)) H.J₃
  have e1 : Stacks.Cohomology.CechDelta.rightDerivedPlusδ
      ((sheafSections K Ab.{max a u v w}).obj (op U)) hS 0 ≫
      (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U)) H.J₁ (0 + 1)).hom =
      (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U)) H.J₃ 0).hom ≫
        hFR.δ 0 (0 + 1) rfl := by
    rw [← B1, Iso.hom_inv_id_assoc]
  have hx₃ : AddCommGrpCat.ofHom (uliftZMultiplesHom _ (ι₃.hom.app (op U) q)) ≫
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₃.cocomplex).d 0 1 = 0 :=
    uliftZMultiplesHom_comp_eq_zero _ _ h2
  have hδ := hFR.δ_eq 0 1 rfl
    (AddCommGrpCat.ofHom (uliftZMultiplesHom _ (ι₃.hom.app (op U) q))) hx₃
    (AddCommGrpCat.ofHom (uliftZMultiplesHom _ y)) (uliftZMultiplesHom_comp_eq _ _ _ F1)
    (AddCommGrpCat.ofHom (uliftZMultiplesHom _ x₁))
    ((uliftZMultiplesHom_comp_eq _ _ _ F2).trans (uliftZMultiplesHom_comp_eq _ _ _ rfl).symm) 2
    (by simp)
  have R3 : AddCommGrpCat.ofHom (uliftZMultiplesHom _ q) ≫
      H.J₃.toRightDerivedZero' ((sheafSections K Ab.{max a u v w}).obj (op U)) =
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₃.cocomplex).liftCycles
        (AddCommGrpCat.ofHom (uliftZMultiplesHom _ (ι₃.hom.app (op U) q))) 1 (by simp) hx₃ := by
    rw [InjectiveResolution.toRightDerivedZero', HomologicalComplex.comp_liftCycles]
    congr 1
    exact uliftZMultiplesHom_comp_eq _ _ _ (by rw [hι₃]; rfl)
  have RHS : (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U)) H.J₁ 1).hom
      (Stacks.Cohomology.CechDelta.rightDerivedPlusδ
        ((sheafSections K Ab.{max a u v w}).obj (op U)) hS 0
        ((derivedPlusToStandard ((sheafSections K Ab.{max a u v w}).obj (op U)) 0).inv.app S.X₃
          (((sheafSections K Ab.{max a u v w}).obj (op U)).toRightDerivedZero.app S.X₃ q))) =
      (((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₁.cocomplex).liftCycles
        (AddCommGrpCat.ofHom (uliftZMultiplesHom _ x₁)) 2 (by simp)
          (uliftZMultiplesHom_comp_eq_zero _ _ F3) ≫
        ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj H.J₁.cocomplex).homologyπ 1) ⟨1⟩ := by
    have R1 := ConcreteCategory.congr_hom e1
      ((derivedPlusToStandard ((sheafSections K Ab.{max a u v w}).obj (op U)) 0).inv.app S.X₃
        (((sheafSections K Ab.{max a u v w}).obj (op U)).toRightDerivedZero.app S.X₃ q))
    have R2 := ConcreteCategory.congr_hom B2 q
    have R4 := ConcreteCategory.congr_hom hδ ⟨1⟩
    have R5 : (H.J₃.toRightDerivedZero' ((sheafSections K Ab.{max a u v w}).obj (op U)) ≫
        ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj H.J₃.cocomplex).homologyπ 0 ≫ hFR.δ 0 1 rfl) q =
        ((((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj H.J₃.cocomplex).liftCycles
            (AddCommGrpCat.ofHom (uliftZMultiplesHom _ (ι₃.hom.app (op U) q))) 1 (by simp) hx₃) ≫
          ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj H.J₃.cocomplex).homologyπ 0 ≫ hFR.δ 0 1 rfl) ⟨1⟩ := by
      rw [← R3]
      show _ = (H.J₃.toRightDerivedZero' ((sheafSections K Ab.{max a u v w}).obj (op U)) ≫
        ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj H.J₃.cocomplex).homologyπ 0 ≫ hFR.δ 0 1 rfl)
            ((1 : ℤ) • q)
      rw [one_zsmul]
    exact R1.trans ((congrArg (ConcreteCategory.hom (hFR.δ 0 (0 + 1) rfl)) R2).trans
      (R5.trans R4))
  -- the left-hand side, through the integer-graded resolution
  have hincl : H.J₁.inclusionZero = ι₁ ≫ (H.J₁.cochainComplexXIso 0 0 (by simp)).inv := by
    rw [InjectiveResolution.inclusionZero, InjectiveResolution.ι'_f_zero, hι₁, Iso.inv_hom_id_assoc]
  have hd01 : H.J₁.cochainComplex.d 0 1 = (H.J₁.cochainComplexXIso 0 0 (by simp)).hom ≫
      H.J₁.cocomplex.d 0 1 ≫ (H.J₁.cochainComplexXIso 1 1 (by simp)).inv :=
    InjectiveResolution.cochainComplex_d _ _ _ _ _ (by simp) (by simp)
  have hd12 : H.J₁.cochainComplex.d 1 2 = (H.J₁.cochainComplexXIso 1 1 (by simp)).hom ≫
      H.J₁.cocomplex.d 1 2 ≫ (H.J₁.cochainComplexXIso 2 2 (by simp)).inv :=
    InjectiveResolution.cochainComplex_d _ _ _ _ _ (by simp) (by simp)
  let a' : cechCochain E (H.J₁.cochainComplex.X 0).obj 0 :=
    pushCochain E (H.J₁.cochainComplexXIso 0 0 (by simp)).inv.hom 0 (-w)
  have Z1 : cechDifferential E (H.J₁.cochainComplex.X 0).obj 0 a' =
      pushCochain E H.J₁.inclusionZero.hom 1 z := by
    rw [cechDifferential_pushCochain, N1, pushCochain_comp, hincl]
    rfl
  have Z2 : pushCochain E (H.J₁.cochainComplex.d 0 1).hom 0 a' =
      augCochain.{a} E (H.J₁.cochainComplex.X 1).obj
        (-((H.J₁.cochainComplexXIso 1 1 (by simp)).inv.hom.app (op U) x₁)) := by
    rw [pushCochain_comp, show (H.J₁.cochainComplexXIso 0 0 (by simp)).inv.hom ≫
        (H.J₁.cochainComplex.d 0 1).hom = (H.J₁.cocomplex.d 0 1).hom ≫
          (H.J₁.cochainComplexXIso 1 1 (by simp)).inv.hom from by
        rw [hd01]
        exact congrArg (fun φ : H.J₁.cocomplex.X 0 ⟶ H.J₁.cochainComplex.X 1 ↦ φ.hom)
          (Iso.inv_hom_id_assoc (H.J₁.cochainComplexXIso 0 0 (by simp))
            (H.J₁.cocomplex.d 0 1 ≫ (H.J₁.cochainComplexXIso 1 1 (by simp)).inv)),
      ← pushCochain_comp, N2, map_neg, pushCochain_augCochain.{a}, augCochain_neg.{a}]
  let a₀ : AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶
      ((cechBicomplex.{a} K E H.J₁.cochainComplex).X 0).X 0 :=
    cochainHom.{a} E (H.J₁.cochainComplex.X 0).obj 0 a' ≫
      (cechIntXIsoPre.{a} E (H.J₁.cochainComplex.X 0).obj 0 0 (by simp)).inv
  let xz : (H.J₁.cochainComplex.X 1).obj.obj (op U) :=
    -((H.J₁.cochainComplexXIso 1 1 (by simp)).inv.hom.app (op U) x₁)
  have hxz : (H.J₁.cochainComplexXIso 1 1 (by simp)).hom.hom.app (op U) xz = -x₁ := by
    show (H.J₁.cochainComplexXIso 1 1 (by simp)).hom.hom.app (op U)
      (-((H.J₁.cochainComplexXIso 1 1 (by simp)).inv.hom.app (op U) x₁)) = -x₁
    rw [map_neg]
    exact congrArg Neg.neg (ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.hom.app (op U))
      (Iso.inv_hom_id (H.J₁.cochainComplexXIso 1 1 (by simp)))) x₁)
  let x : AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H.J₁.cochainComplex).X 1 :=
    AddCommGrpCat.ofHom (uliftZMultiplesHom _ xz)
  have hx : x ≫ ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj H.J₁.cochainComplex).d 1 2 = 0 := by
    refine uliftZMultiplesHom_comp_eq_zero _ _ ?_
    show (H.J₁.cochainComplex.d 1 2).hom.app (op U) xz = 0
    rw [hd12]
    show (H.J₁.cochainComplexXIso 2 2 (by simp)).inv.hom.app (op U)
      ((H.J₁.cocomplex.d 1 2).hom.app (op U) ((H.J₁.cochainComplexXIso 1 1 (by simp)).hom.hom.app
        (op U) xz)) = 0
    rw [hxz, map_neg, F3, neg_zero, map_zero]
  have hL0d : ((cechBicomplex.{a} K E H.J₁.cochainComplex).X 0).d 0 1 =
      (cechIntXIsoPre.{a} E (H.J₁.cochainComplex.X 0).obj 0 0 (by simp)).hom ≫
        (cechComplex E (H.J₁.cochainComplex.X 0).obj).d 0 1 ≫
        (cechIntXIsoPre.{a} E (H.J₁.cochainComplex.X 0).obj 1 1 (by simp)).inv :=
    cechComplexIntFunctorPre_d.{a} E _ 0 0 1 (by simp) (by simp)
  have hincl1 : ((cechComplexIntFunctor.{a} K E).map H.J₁.inclusionZero).f 1 =
      (cechIntXIsoPre.{a} E S.X₁.obj 1 1 (by simp)).hom ≫
        ((cechComplexFunctor E).map H.J₁.inclusionZero.hom).f 1 ≫
        (cechIntXIsoPre.{a} E (H.J₁.cochainComplex.X 0).obj 1 1 (by simp)).inv :=
    HomologicalComplex.extendMap_f _ _ (by simp)
  have hLd0 : ((cechBicomplex.{a} K E H.J₁.cochainComplex).d 0 1).f 0 =
      (cechIntXIsoPre.{a} E (H.J₁.cochainComplex.X 0).obj 0 0 (by simp)).hom ≫
        ((cechComplexFunctor E).map (H.J₁.cochainComplex.d 0 1).hom).f 0 ≫
        (cechIntXIsoPre.{a} E (H.J₁.cochainComplex.X 1).obj 0 0 (by simp)).inv :=
    HomologicalComplex.extendMap_f _ _ (by simp)
  have h₁ : a₀ ≫ ((cechBicomplex.{a} K E H.J₁.cochainComplex).X 0).d 0 1 =
      (cocycleHom.{a} E S.X₁.obj z ≫ (cechIntXIsoPre.{a} E S.X₁.obj 1 1 (by simp)).inv) ≫
        ((cechComplexIntFunctor.{a} K E).map H.J₁.inclusionZero).f 1 := by
    rw [hL0d, hincl1]
    simp only [a₀, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% cochainHom_comp_d.{a}, Z1, ← reassoc_of% cochainHom_comp_map.{a}]
    rfl
  have h₂ : a₀ ≫ ((cechBicomplex.{a} K E H.J₁.cochainComplex).d 0 1).f 0 =
      x ≫ cechAugmentationInt.{a} K E (H.J₁.cochainComplex.X 1) := by
    rw [hLd0]
    simp only [a₀, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% cochainHom_comp_map.{a}, Z2, cechAugmentationInt, cechAugmentationIntPre,
      ← Category.assoc, ← uliftZMultiplesHom_comp_cechAugmentationPre.{a}]
    rfl
  have CM := resolutionHomologyIso_cechCohomologyToCohomology_one_cls.{a} K E hE H.J₁ z a₀ x hx
    h₁ h₂
  have R3' := liftCycles_homologyπ_extendedHomologyTailIso_hom
    ((sheafSections K Ab.{max a u v w}).obj (op U)) H.J₁.cocomplex x hx
  have hxx : x ≫ ((sheafSections K Ab.{max a u v w}).obj (op U)).map
      (H.J₁.cocomplex.extendXIso ComplexShape.embeddingUpNat (i := 1) (by simp)).hom =
      -AddCommGrpCat.ofHom (uliftZMultiplesHom _ x₁) := by
    ext m
    show (H.J₁.cochainComplexXIso 1 1 (by simp)).hom.hom.app (op U) (m.down • xz) =
      -(m.down • x₁)
    rw [map_zsmul, ← smul_neg]
    exact congrArg (m.down • ·) hxz
  have hlc : ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₁.cocomplex).liftCycles
        (x ≫ ((sheafSections K Ab.{max a u v w}).obj (op U)).map
          (H.J₁.cocomplex.extendXIso ComplexShape.embeddingUpNat (i := 1) (by simp)).hom) 2
        (by simp) (comp_map_extendXIso_hom_comp_d_eq_zero _ H.J₁.cocomplex x hx) =
      -((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₁.cocomplex).liftCycles
        (AddCommGrpCat.ofHom (uliftZMultiplesHom _ x₁)) 2 (by simp)
          (uliftZMultiplesHom_comp_eq_zero _ _ F3) := by
    refine (cancel_mono (HomologicalComplex.iCycles _ 1)).1 ?_
    rw [HomologicalComplex.liftCycles_i, Preadditive.neg_comp, HomologicalComplex.liftCycles_i,
      hxx]
  apply (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U))
    H.J₁ 1).addCommGroupIsoToAddEquiv.injective
  show (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U)) H.J₁ 1).hom _ =
    (resolutionHomologyIso ((sheafSections K Ab.{max a u v w}).obj (op U)) H.J₁ 1).hom _
  refine CM.trans (Eq.trans ?_ RHS.symm)
  have e := congrArg (fun f : AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₁.cocomplex).homology 1 ↦
      ConcreteCategory.hom f (ULift.up (1 : ℤ) : ULift.{max a u v w} ℤ)) R3'
  refine (congrArg Neg.neg e).trans ?_
  refine (congrArg (fun f : AddCommGrpCat.of (ULift.{max a u v w} ℤ) ⟶
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₁.cocomplex).cycles 1 ↦
      -(ConcreteCategory.hom (f ≫ ((((sheafSections K Ab.{max a u v w}).obj
        (op U)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj H.J₁.cocomplex).homologyπ 1)
          (ULift.up (1 : ℤ) : ULift.{max a u v w} ℤ))) hlc).trans ?_
  dsimp only
  rw [Preadditive.neg_comp]
  exact neg_neg _

end Classes

end Stacks.CechSite
