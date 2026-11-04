module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensorProductIsLE
public import StacksFrontier.Homology.Tor.ProZero
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom

/-!
# Comparing the ideal-power tensor tower with the adic quotient tower

Let `I` be an ideal of a Noetherian ring `A` and let `M` be a finite `A`-module. Derived
completion along `I` is the derived limit of the tower `n ↦ K ⊗ᴸ A/Iⁿ`, while the tower that
occurs in Tag 0EEW is the tower of ordinary quotients `n ↦ M/IⁿM`. The two towers are
pro-isomorphic: the derived tensor `M ⊗ᴸ A/Iⁿ` differs from `M/IⁿM` only by the Tor modules
`Torᵢ(M, A/Iⁿ)`, and those form pro-zero systems by Tag 0911.

This file carries that comparison and the auxiliary facts it needs: the identification of the
cohomology of `M ⊗ᴸ A/Iⁿ` with `Torᵢ(M, A/Iⁿ)`, the boundedness of the Koszul tower, and the
transport of the derived-limit property along a map of towers with eventual inverses.

## Main results

* `Dualizing.AdicQuotientComparison.hasEventualInverses_of_comp` — if `φ` and `φ ≫ π` have
  eventual inverses then so does `π`.
* `Dualizing.AdicQuotientComparison.exists_idealPowerTensor_adicQuotient_comparison` — the tower
  `n ↦ (M ⊗ᴸ A/Iⁿ⁺¹)` maps to `n ↦ M/Iⁿ⁺¹M` by a map with eventual inverses.
* `Dualizing.AdicQuotientComparison.isDerivedLimit_tensor_adicQuotient` — consequently a derived
  limit of `n ↦ (C ⊗ᴸ M) ⊗ᴸ A/Iⁿ` is a derived limit of `n ↦ C ⊗ᴸ (M/IⁿM)`.

## References

* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0911](https://stacks.math.columbia.edu/tag/0911)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing.AdicQuotientComparison

/-- The derived category of `A`-modules has countable products indexed by `ℕ`. -/
local instance derivedCategoryHasProductsNat (A : Type u) [CommRing A] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- The forward map of an isomorphism of inverse systems has eventual inverses. -/
private theorem hasEventualInverses_of_iso {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) :
    NoetherianAdicCompletion.HasEventualInverses e.hom := fun n =>
  ⟨n, le_rfl, e.inv.app ⟨n⟩, by simp, by simp⟩

private theorem isDerivedLimit_of_hasEventualInverses
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩]
    (φ : F ⟶ G) (hφ : NoetherianAdicCompletion.HasEventualInverses φ)
    {K : D} (h : IsDerivedLimit F K) : IsDerivedLimit G K := by
  obtain ⟨p, δ, hp⟩ := h
  have hπ : (Pi.lift fun n : ℕ ↦ p ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) = p := by
    apply Pi.hom_ext
    intro n
    simp
  have hp' : NoetherianAdicCompletion.IsDerivedLimitWithProjections F K
      (fun n : ℕ ↦ p ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) := by
    refine ⟨δ, ?_⟩
    simpa only [hπ] using hp
  exact (hp'.comp_of_hasEventualInverses φ hφ).isDerivedLimit

/-- A derived limit of an inverse system `F` is a derived limit of any inverse system isomorphic
to `F`. -/
theorem isDerivedLimit_of_natIso
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩]
    (e : F ≅ G) {K : D} (h : IsDerivedLimit F K) : IsDerivedLimit G K := by
  exact isDerivedLimit_of_hasEventualInverses e.hom
    (hasEventualInverses_of_iso e) h

/-- Any object isomorphic to a derived limit of an inverse system `F` is a derived limit of `F`. -/
theorem isDerivedLimit_of_iso
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K K' : D} (e : K ≅ K') (h : IsDerivedLimit F K) : IsDerivedLimit F K' := by
  obtain ⟨p, δ, hp⟩ := h
  let d := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let t := Triangle.mk p d δ
  let t' := Triangle.mk (e.inv ≫ p) d (δ ≫ e.hom⟦(1 : ℤ)⟧')
  let et : t ≅ t' := Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
    (by simp [t, t']) (by simp [t, t']) (by simp [t, t'])
  exact ⟨_, _, isomorphic_distinguished _ hp _ et.symm⟩

section TensorHomology

open MonoidalCategory


variable {R : Type u} [CommRing R]

attribute [local instance] CochainComplex.DerivedTensor.kFlatHomotopyQ_isLocalization

private def tensorSingleIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    AdicCompletionTor.complexTensorRight R K ≅
      CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ TleftCochain K := by
  have := fun N => AdicCompletionTor.tensorSingleInclusion_isIso N K
  refine NatIso.ofComponents (fun N => asIso (AdicCompletionTor.tensorSingleInclusion N K)) ?_
  intro N N' g
  ext n : 1
  change ((AdicCompletionTor.complexTensorRight R K).map g).f n ≫
      HomologicalComplex.ιMapBifunctor K
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N')
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) n 0 n (add_zero n) =
    HomologicalComplex.ιMapBifunctor K
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 K)
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g)
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).f n
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp [AdicCompletionTor.complexTensorRight, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rfl

private def quotientSystemIso {A : Type u} [CommRing A] (I : Ideal A) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ≅
      AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
      (ChainComplex.single₀ (ModuleCat.{u} A) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q) := by
  let φ : NoetherianAdicCompletion.idealPowerQuotientSystem I ⟶
      AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
      (ChainComplex.single₀ (ModuleCat.{u} A) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q) :=
    NatTrans.ofOpSequence (fun n => 𝟙 _) (by
      intro n
      have h : (NoetherianAdicCompletion.idealPowerQuotientSystem I).map
            (homOfLE (Nat.le_succ n)).op =
          (AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
            (ChainComplex.single₀ (ModuleCat.{u} A) ⋙
              ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q)).map
            (homOfLE (Nat.le_succ n)).op := by
        simp only [Functor.comp_map]
        unfold NoetherianAdicCompletion.idealPowerQuotientSystem
          AdicCompletionTor.idealPowerQuotientModuleSystem
        rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
        rfl
      exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))
  have : ∀ n, IsIso (φ.app n) := fun n => by
    change IsIso (𝟙 _)
    infer_instance
  have := NatIso.isIso_of_isIso_app φ
  exact asIso φ

private def torTowerIso {A : Type u} [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A) (M : ModuleCat.{u} A) (j : ℕ) (q : ℤ)
    (hq : -(j : ℤ) = q) :
    (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) q ≅
        AdicCompletionTor.torIdealPowerSystem I M j :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight (quotientSystemIso I) _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (AdicCompletionTor.idealPowerQuotientModuleSystem I)
      (Functor.associator _ _ _ ≪≫
        AdicCompletionTor.derivedTensorTorIso T M j q (by simpa using hq))


private theorem idealPowerQuotientModuleSystem_map
    {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (h : n ≤ m) :
    (AdicCompletionTor.idealPowerQuotientModuleSystem I).map (homOfLE h).op =
      torProZeroTransition I (Nat.add_le_add_right h 1) := by
  refine NoetherianAdicCompletion.ofOpSequence_map_eq _
    (fun m n h => torProZeroTransition I (Nat.add_le_add_right h 1)) ?_ ?_ m n h
  all_goals
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro a
    rfl

private theorem torIdealPowerSystem_uniform_proZero
    {A : Type u} [CommRing A] (I : Ideal A) (Q : ModuleCat.{u} A)
    (i c : ℕ)
    (hQ : ∀ n : ℕ, c ≤ n → ((Tor (ModuleCat.{u} A) i).obj Q).map
      (torProZeroTransition I (Nat.sub_le n c)) = 0) :
    ∀ n : ℕ, (AdicCompletionTor.torIdealPowerSystem I Q i).map
      (homOfLE (Nat.le_add_right n c)).op = 0 := by
  intro n
  show ((Tor' (ModuleCat.{u} A) i).obj Q).map _ = 0
  rw [idealPowerQuotientModuleSystem_map]
  let e := (Tor_iso_Tor' A i).app Q
  apply (cancel_epi (e.hom.app (torProZeroQuot I (n + c + 1)))).mp
  have hz : ((Tor (ModuleCat.{u} A) i).obj Q).map
      (torProZeroTransition I (Nat.add_le_add_right (Nat.le_add_right n c) 1)) = 0 := by
    have transfer (k m : ℕ) (hk : c ≤ k) (he : k - c = m) (hm : m ≤ k) :
        ((Tor (ModuleCat.{u} A) i).obj Q).map (torProZeroTransition I hm) = 0 := by
      subst m
      exact hQ k hk
    exact transfer (n + c + 1) (n + 1) (by omega) (by omega) _
  refine (e.hom.naturality
    (torProZeroTransition I (Nat.add_le_add_right (Nat.le_add_right n c) 1))).symm.trans ?_
  rw [hz, zero_comp]
  exact comp_zero.symm

private theorem tensorQuotient_homology_proZero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℤ) (hi : i < 0) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
          T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).map
            (homOfLE h).op) = 0 := by
  obtain ⟨j, hj, hji⟩ : ∃ j : ℕ, 0 < j ∧ -(j : ℤ) = i := ⟨(-i).toNat, by omega, by omega⟩
  obtain ⟨c, _, hc⟩ := tor_pro_zero I M hj
  have ht := torIdealPowerSystem_uniform_proZero I M j c hc
  let e := torTowerIso I T M j i hji
  intro n
  refine ⟨n + c, Nat.le_add_right n c, ?_⟩
  apply (cancel_mono (e.hom.app ⟨n⟩)).mp
  have he := e.hom.naturality (homOfLE (Nat.le_add_right n c)).op
  simpa only [Functor.comp_map, ht n, comp_zero, zero_comp] using he

private theorem koszulTensor_homology_isZero_outside
    (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (M : ModuleCat.{u} R) (n : ℕ) (i : ℤ)
    (hi : i < -(r : ℤ) ∨ 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj
        ((NoetherianKoszulProIso.koszulPowerSystem f).obj ⟨n⟩))) := by
  let K := Koszul.seqComplex (fun j => f j ^ (n + 1))
  let E : CochainComplex (ModuleCat.{u} R) ℤ := K.extend ComplexShape.embeddingDownNat
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  let (j : ℕ) : Projective (K.X j) :=
    ModuleCat.projective_of_free ((Pi.basisFun R (Fin r)).exteriorPower j)
  let (j : ℤ) : Module.Flat R (E.X j) := inferInstance
  have hE : E.KFlat := CochainComplex.KFlat.kFlat_of_flat E 0
  let e := (T.tensor.flip.obj (DerivedCategory.Q.obj E)).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M) ≪≫
    (KoszulCompletion.tensorComparisonIso T S E hE).symm
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ i).mapIso e)
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors _ i).app (S ⊗ E))
  apply ShortComplex.isZero_homology_of_isZero_X₂
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = i := by simpa using hpq
    subst q
    have hz : IsZero (E.X i) := by
      by_cases hn : ∃ j : ℕ, -(j : ℤ) = i
      · obtain ⟨j, hj⟩ := hn
        have hgt : r < j := by omega
        have hK : IsZero (K.X j) := by
          apply ModuleCat.isZero_iff_subsingleton.mpr
          apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
            (fun k : Fin r => (Pi.basisFun R (Fin r)) k)
            (Pi.basisFun R (Fin r)).span_eq j
          simpa using hgt
        exact hK.of_iso (K.extendXIso ComplexShape.embeddingDownNat hj)
      · exact K.isZero_extend_X ComplexShape.embeddingDownNat i
          (fun j hj => hn ⟨j, hj⟩)
    exact ((tensorLeft (S.X 0)).map_isZero hz).eq_of_src _ _
  · exact ((tensorRight (E.X q)).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M p hp)).eq_of_src _ _

private def tensorSingleResolutionIso
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R) (M : ModuleCat.{u} R) :
    (ChainComplex.single₀ (ModuleCat.{u} R) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q) ⋙
      T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      AdicCompletionTor.complexTensorRight R (ProjectiveResolution.of M).cochainComplex ⋙
        DerivedCategory.Q := by
  let P := ProjectiveResolution.of M
  let Pc := P.cochainComplex
  have hPc := AdicCompletionTor.cochainComplex_kFlat M
  let eS : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅ DerivedCategory.Q.obj Pc :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M ≪≫
      (asIso (DerivedCategory.Q.map P.π')).symm
  let fac := Localization.fac (TleftCochain Pc ⋙ DerivedCategory.Q)
    (AdicCompletionTor.tensorLeft_inverts Pc hPc)
    DerivedCategory.Q
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerRight AdicCompletionTor.singleExtendIso DerivedCategory.Q) _ ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ DerivedCategory.Q)
      (T.tensor.mapIso eS) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{u} R) 0 ⋙ DerivedCategory.Q)
      (AdicCompletionTor.tensorKFlatIso T Pc hPc) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{u} R) 0) fac ≪≫
    Functor.isoWhiskerRight (AdicCompletionTor.tensorSingleIso Pc).symm DerivedCategory.Q

private theorem tensorQuotient_isLE
    (R : Type u) [CommRing R] (I : Ideal R)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (M : ModuleCat.{u} R) (n : ℕᵒᵖ) :
    ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
      T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj n).IsLE 0 := by
  let e := Functor.isoWhiskerRight (quotientSystemIso I) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (tensorSingleResolutionIso T M)
  let N := (AdicCompletionTor.idealPowerQuotientModuleSystem I).obj n
  let K : CochainComplex (ModuleCat.{u} R) ℤ :=
    (AdicCompletionTor.complexTensorRight R (ProjectiveResolution.of M).cochainComplex).obj N
  have : K.IsStrictlyLE 0 := by
    show CochainComplex.IsStrictlyLE
      ((((tensoringRight _).obj N).mapHomologicalComplex _).obj
        (ProjectiveResolution.of M).cochainComplex) 0
    infer_instance
  have : (DerivedCategory.Q.obj K).IsLE 0 := by infer_instance
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact IsZero.of_iso (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj K) 0 i hi)
    ((DerivedCategory.homologyFunctor _ i).mapIso (e.app n))

private def tensorQuotientSystemIso {A : Type u} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) :
    AdicCompletionTor.adicQuotientSystem I M ≅
      AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙ tensorLeft M := by
  refine NatIso.ofComponents (fun n =>
    (TensorProduct.tensorQuotEquivQuotSMul M (I ^ (n.unop + 1))).symm.toModuleIso) ?_
  intro n m f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  change (TensorProduct.tensorQuotEquivQuotSMul M (I ^ (m.unop + 1))).symm
      (Submodule.Quotient.mk x) =
    (((AdicCompletionTor.idealPowerQuotientModuleSystem I).map f).hom.lTensor M)
      ((TensorProduct.tensorQuotEquivQuotSMul M (I ^ (n.unop + 1))).symm
        (Submodule.Quotient.mk x))
  simp only [TensorProduct.tensorQuotEquivQuotSMul_symm_mk]
  congr 1
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf, idealPowerQuotientModuleSystem_map]
  rfl

private def tensorQuotientHomologyZeroIso (R : Type u) [CommRing R]
    (I : Ideal R) (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (M : ModuleCat.{u} R) :
    (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
      T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0 ≅
      AdicCompletionTor.adicQuotientSystem I M :=
  torTowerIso I T M 0 0 (by simp) ≪≫
    Functor.isoWhiskerLeft _ ((Tor_iso_Tor' R 0).app M).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftDerivedZeroIsoSelf (MonoidalCategory.tensorLeft M)) ≪≫
    (tensorQuotientSystemIso I M).symm

/-! ### The reduction map on degree-zero cohomology

The comparison of the ideal-power tensor tower with the adic quotient tower is produced as an
existential, and the projections it produces are therefore determined only up to an automorphism
of the target tower. For a statement that normalizes the projections of derived completion
against the completion unit, that is not enough: the composite of the canonical map
`M[0] ⟶ M[0] ⊗ᴸ A/Iⁿ⁺¹` with the comparison has to be the quotient map `M ↠ M/Iⁿ⁺¹M` itself.

Rather than compute the comparison, which runs through Tor balancing, this identifies the
comparison *by* that property. The canonical map is surjective on `H⁰` and its target is
annihilated by `Iⁿ⁺¹`, so it induces a surjection `M/Iⁿ⁺¹M ↠ H⁰(M[0] ⊗ᴸ A/Iⁿ⁺¹)`; over a
Noetherian ring with `M` finite, a surjection onto a module abstractly isomorphic to
`M/Iⁿ⁺¹M` is an isomorphism, so that surjection is invertible and its inverse is a comparison
map normalized by construction. -/

/-- The quotient of `R` by a power of `I`, as a short exact sequence of modules. -/
private def idealPowerShortComplex (I : Ideal R) (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (I ^ (n + 1) : Ideal R).subtype)
    (ModuleCat.ofHom (I ^ (n + 1) : Ideal R).mkQ)
    (by ext x; exact (Submodule.Quotient.mk_eq_zero _).2 x.property)

private theorem idealPowerShortComplex_shortExact (I : Ideal R) (n : ℕ) :
    (idealPowerShortComplex I n).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).1 hx⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 (Submodule.subtype_injective _)
  epi_g := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

/-- **The reduction map is surjective on degree-zero cohomology.** Its fibre is
`M[0] ⊗ᴸ Iⁿ⁺¹`, which lives in degrees `≤ 0` because derived tensoring is right `t`-exact, so
the connecting map out of degree zero lands in a zero group. -/
private theorem epi_homologyMap_derivedReductionMap (I : Ideal R)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R) (M : ModuleCat.{u} R) (n : ℕ) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((NoetherianAdicCompletion.derivedReductionMap I T n).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) := by
  have hSC := idealPowerShortComplex_shortExact I n
  have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 1).obj
      ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (idealPowerShortComplex I n).X₁))) := by
    have : ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (idealPowerShortComplex I n).X₁)).IsLE 0 := by
      simpa using CochainComplex.DerivedTensor.isLE_tensor T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (idealPowerShortComplex I n).X₁) 0 0
    exact DerivedCategory.isZero_of_isLE _ 0 1 (by omega)
  have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
          (idealPowerShortComplex I n).g))) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _
      ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).map_distinguished
        _ hSC.singleTriangle_distinguished) 0 1 rfl).2
      (hzero.eq_of_tgt _ _)
  let bi : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (idealPowerShortComplex I n).X₃ ≅
      (NoetherianAdicCompletion.idealPowerQuotientSystem I).obj ⟨n⟩ :=
    DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat
      (ModuleCat.of R (R ⧸ (I ^ (n + 1) : Ideal R))) 0 0 (by simp)).symm
  have hb : NoetherianAdicCompletion.idealPowerQuotientMap I n =
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (idealPowerShortComplex I n).g ≫ bi.hom := rfl
  have hsplit : (NoetherianAdicCompletion.derivedReductionMap I T n).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) =
      T.rightUnitor.inv.app ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≫
        ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
              (idealPowerShortComplex I n).g) ≫
          (T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).map
            bi.hom) := by
    have h : (NoetherianAdicCompletion.derivedReductionMap I T n).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) =
        T.rightUnitor.inv.app ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≫
          (T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).map
            (NoetherianAdicCompletion.idealPowerQuotientMap I n) := rfl
    rw [h, hb]
    exact congrArg _ (Functor.map_comp _ _ _)
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (T.rightUnitor.inv.app ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso
      (T.rightUnitor.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).symm).isIso_hom
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).map bi.hom)) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso
      ((T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).mapIso
        bi)).isIso_hom
  rw [hsplit, Functor.map_comp, Functor.map_comp]
  exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' hepi (IsIso.epi_of_iso _))

/-- **The quotient maps `A ↠ A/Iⁿ⁺¹` form a cone** on `idealPowerQuotientSystem`. -/
private theorem idealPowerQuotientMap_comp_map (I : Ideal R) (n : ℕ) :
    NoetherianAdicCompletion.idealPowerQuotientMap I (n + 1) ≫
        (NoetherianAdicCompletion.idealPowerQuotientSystem I).map (homOfLE (Nat.le_succ n)).op =
      NoetherianAdicCompletion.idealPowerQuotientMap I n := by
  have hle : (I ^ (n + 1 + 1) : Ideal R) ≤ I ^ (n + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1)
  rw [NoetherianAdicCompletion.idealPowerQuotientSystem_map]
  have hnat := AdicCompletionTor.singleExtendIso.inv.naturality
    (NoetherianAdicCompletion.quotientFactor hle)
  have hmkQ := NoetherianAdicCompletion.mkQ_comp_quotientFactor hle
  show (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (I ^ (n + 1 + 1)).mkQ) ≫
      DerivedCategory.Q.map (AdicCompletionTor.singleExtendIso.inv.app _) ≫
        DerivedCategory.Q.map
          ((ChainComplex.single₀ (ModuleCat.{u} R) ⋙
            ComplexShape.embeddingDownNat.extendFunctor _).map
              (NoetherianAdicCompletion.quotientFactor hle)) = _
  rw [← DerivedCategory.Q.map_comp, ← hnat, DerivedCategory.Q.map_comp]
  show _ ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      (NoetherianAdicCompletion.quotientFactor hle) ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp, hmkQ]
  rfl

/-- The tower `n ↦ M[0] ⊗ᴸ A/Iⁿ⁺¹`. -/
private abbrev idealPowerTensorTower (I : Ideal R)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R) (M : ModuleCat.{u} R) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
    T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)

/-- **The reduction maps `K ⟶ K ⊗ᴸ A/Iⁿ⁺¹` form a cone** on the ideal-power tensor tower. -/
private theorem derivedReductionMap_comp_map (I : Ideal R)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℕ) :
    (NoetherianAdicCompletion.derivedReductionMap I T (n + 1)).app X ≫
        (T.tensor.obj X).map ((NoetherianAdicCompletion.idealPowerQuotientSystem I).map
          (homOfLE (Nat.le_succ n)).op) =
      (NoetherianAdicCompletion.derivedReductionMap I T n).app X := by
  simp only [NoetherianAdicCompletion.derivedReductionMap, NatTrans.comp_app,
    Functor.flip_map_app, Category.assoc]
  rw [← Functor.map_comp, idealPowerQuotientMap_comp_map]

variable (I : Ideal R) (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
  (M : ModuleCat.{u} R)

/-- `H⁰` of the reduction map `M[0] ⟶ M[0] ⊗ᴸ A/Iⁿ⁺¹`, read as a map out of `M` itself. -/
private def reductionHomologyUnit (n : ℕ) :
    M ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((idealPowerTensorTower I T M).obj ⟨n⟩) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app M ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((NoetherianAdicCompletion.derivedReductionMap I T n).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))

private theorem epi_reductionHomologyUnit (n : ℕ) : Epi (reductionHomologyUnit I T M n) :=
  epi_comp' (IsIso.epi_of_iso _) (epi_homologyMap_derivedReductionMap I T M n)

/-- The maps of `reductionHomologyUnit` are compatible with the transitions of the tower. -/
private theorem reductionHomologyUnit_comp_map (n : ℕ) :
    reductionHomologyUnit I T M (n + 1) ≫
        (idealPowerTensorTower I T M ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
            (homOfLE (Nat.le_succ n)).op =
      reductionHomologyUnit I T M n := by
  dsimp only [Functor.comp_map]
  rw [reductionHomologyUnit, reductionHomologyUnit, Category.assoc, ← Functor.map_comp]
  exact congrArg _ (congrArg _ (derivedReductionMap_comp_map I T _ n))

/-- The quotient map `M ↠ M/Iⁿ⁺¹M`, with the target read as a term of the adic quotient tower. -/
private def adicQuotientMk (n : ℕ) :
    M ⟶ (AdicCompletionTor.adicQuotientSystem I M).obj ⟨n⟩ :=
  ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule R (M : Type u))).mkQ

private theorem epi_adicQuotientMk (n : ℕ) : Epi (adicQuotientMk I M n) :=
  (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

/-- The quotient maps are compatible with the transitions of the adic quotient tower. -/
private theorem adicQuotientMk_comp_map (n : ℕ) :
    adicQuotientMk I M (n + 1) ≫
        (AdicCompletionTor.adicQuotientSystem I M).map (homOfLE (Nat.le_succ n)).op =
      adicQuotientMk I M n :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- A power of `I` annihilates `M/Iⁿ⁺¹M`. -/
private theorem smul_adicQuotient_eq_zero (n : ℕ) {c : R}
    (hc : c ∈ (I ^ (n + 1) : Ideal R))
    (w : (AdicCompletionTor.adicQuotientSystem I M).obj ⟨n⟩) : c • w = 0 := by
  refine Submodule.Quotient.induction_on _ w ?_
  intro m
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hc Submodule.mem_top)

/-- **The reduction map kills `Iⁿ⁺¹M`.** Its target on `H⁰` is abstractly isomorphic to
`M/Iⁿ⁺¹M`, hence annihilated by `Iⁿ⁺¹`. -/
private theorem adicQuotient_le_ker_reductionHomologyUnit (n : ℕ) :
    (I ^ (n + 1) • (⊤ : Submodule R (M : Type u))) ≤
      LinearMap.ker (reductionHomologyUnit I T M n).hom := by
  set z := (tensorQuotientHomologyZeroIso R I T M).app ⟨n⟩ with hz
  have hinj : Function.Injective (ModuleCat.Hom.hom z.hom) :=
    (ConcreteCategory.bijective_of_isIso z.hom).1
  rw [Submodule.smul_le]
  intro c hc x _
  refine LinearMap.mem_ker.2 (hinj ?_)
  simp only [map_zero, map_smul, smul_adicQuotient_eq_zero I M n hc]

/-- **The reduction map factors through `M/Iⁿ⁺¹M`.** -/
private def adicQuotientToTensorHomology (n : ℕ) :
    (AdicCompletionTor.adicQuotientSystem I M).obj ⟨n⟩ ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
        ((idealPowerTensorTower I T M).obj ⟨n⟩) :=
  ModuleCat.ofHom (Submodule.liftQ _ (reductionHomologyUnit I T M n).hom
    (adicQuotient_le_ker_reductionHomologyUnit I T M n))

private theorem adicQuotientMk_comp_adicQuotientToTensorHomology (n : ℕ) :
    adicQuotientMk I M n ≫ adicQuotientToTensorHomology I T M n =
      reductionHomologyUnit I T M n :=
  ModuleCat.hom_ext (Submodule.liftQ_mkQ _ _ _)

/-- **The factorization is invertible.** It is a surjection onto a module abstractly isomorphic
to `M/Iⁿ⁺¹M`, hence, `M/Iⁿ⁺¹M` being Noetherian, injective by Orzech's theorem. -/
private theorem isIso_adicQuotientToTensorHomology [IsNoetherianRing R] [Module.Finite R M]
    (n : ℕ) : IsIso (adicQuotientToTensorHomology I T M n) := by
  set z := (tensorQuotientHomologyZeroIso R I T M).app ⟨n⟩ with hz
  have : Epi (reductionHomologyUnit I T M n) := epi_reductionHomologyUnit I T M n
  have : Epi (adicQuotientMk I M n) := epi_adicQuotientMk I M n
  have h1 : Epi (adicQuotientMk I M n ≫ adicQuotientToTensorHomology I T M n ≫ z.hom) := by
    rw [← Category.assoc, adicQuotientMk_comp_adicQuotientToTensorHomology]
    exact epi_comp' inferInstance (IsIso.epi_of_iso _)
  have h2 : Epi (adicQuotientToTensorHomology I T M n ≫ z.hom) :=
    epi_of_epi (adicQuotientMk I M n) (adicQuotientToTensorHomology I T M n ≫ z.hom)
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom (adicQuotientToTensorHomology I T M n ≫ z.hom)) :=
    (ModuleCat.epi_iff_surjective _).1 h2
  have : IsNoetherian R ((AdicCompletionTor.adicQuotientSystem I M).obj ⟨n⟩) :=
    inferInstanceAs (IsNoetherian R
      ((M : Type u) ⧸ (I ^ (n + 1) • (⊤ : Submodule R (M : Type u)))))
  have hiso : IsIso (adicQuotientToTensorHomology I T M n ≫ z.hom) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (IsNoetherian.bijective_of_surjective_endomorphism _ hsurj)
  exact IsIso.of_isIso_comp_right _ z.hom

/-- **The normalized comparison on degree-zero cohomology.** The factorizations assemble to a
map of towers: both triangles over the quotient maps `M ↠ M/Iⁿ⁺¹M` commute, and those maps are
epimorphisms. -/
private def adicQuotientToTensorHomologyNatTrans :
    AdicCompletionTor.adicQuotientSystem I M ⟶
      idealPowerTensorTower I T M ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0 :=
  NatTrans.ofOpSequence (fun n ↦ adicQuotientToTensorHomology I T M n) (fun n ↦ by
    haveI : Epi (adicQuotientMk I M (n + 1)) := epi_adicQuotientMk I M (n + 1)
    refine (cancel_epi (adicQuotientMk I M (n + 1))).1 ?_
    have hle : (homOfLE (n.le_add_right 1)).op = (homOfLE (Nat.le_succ n)).op :=
      Subsingleton.elim _ _
    rw [hle, ← Category.assoc, ← Category.assoc, adicQuotientMk_comp_map,
      adicQuotientMk_comp_adicQuotientToTensorHomology,
      adicQuotientMk_comp_adicQuotientToTensorHomology, reductionHomologyUnit_comp_map])

private theorem isIso_adicQuotientToTensorHomologyNatTrans [IsNoetherianRing R]
    [Module.Finite R M] : IsIso (adicQuotientToTensorHomologyNatTrans I T M) := by
  have : ∀ n : ℕᵒᵖ, IsIso ((adicQuotientToTensorHomologyNatTrans I T M).app n) := fun n ↦
    isIso_adicQuotientToTensorHomology I T M n.unop
  exact NatIso.isIso_of_isIso_app _

/-- **The degree-zero comparison of the two towers, normalized by construction.** -/
private def tensorHomologyAdicQuotientNatIso [IsNoetherianRing R] [Module.Finite R M] :
    idealPowerTensorTower I T M ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0 ≅
      AdicCompletionTor.adicQuotientSystem I M :=
  letI := isIso_adicQuotientToTensorHomologyNatTrans I T M
  (asIso (adicQuotientToTensorHomologyNatTrans I T M)).symm

/-- **The normalization.** `H⁰` of the reduction map, followed by the degree-zero comparison, is
the quotient map `M ↠ M/Iⁿ⁺¹M` itself. -/
private theorem reductionHomologyUnit_comp_tensorHomologyAdicQuotientNatIso
    [IsNoetherianRing R] [Module.Finite R M] (n : ℕ) :
    reductionHomologyUnit I T M n ≫
        (tensorHomologyAdicQuotientNatIso I T M).hom.app ⟨n⟩ =
      adicQuotientMk I M n := by
  let := isIso_adicQuotientToTensorHomologyNatTrans I T M
  have h : adicQuotientToTensorHomology I T M n ≫
      (tensorHomologyAdicQuotientNatIso I T M).hom.app ⟨n⟩ =
      𝟙 ((AdicCompletionTor.adicQuotientSystem I M).obj ⟨n⟩) := by
    show (adicQuotientToTensorHomologyNatTrans I T M).app ⟨n⟩ ≫
      (asIso (adicQuotientToTensorHomologyNatTrans I T M)).inv.app ⟨n⟩ = 𝟙 _
    exact congrArg (fun α : AdicCompletionTor.adicQuotientSystem I M ⟶
        AdicCompletionTor.adicQuotientSystem I M ↦ α.app ⟨n⟩)
      (asIso (adicQuotientToTensorHomologyNatTrans I T M)).hom_inv_id
  rw [← adicQuotientMk_comp_adicQuotientToTensorHomology I T M n, Category.assoc, h,
    Category.comp_id]

end TensorHomology

section BoundedTowers

open DerivedCategory

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

open DerivedCategory.TStructure

universe u' v'

private theorem isIso_homologyFunctor_map_truncGEπ (i n : ℤ) (hi : n ≤ i)
    (X : DerivedCategory 𝒜) : IsIso ((homologyFunctor 𝒜 i).map ((t.truncGEπ n).app X)) := by
  have hT := t.triangleLTGE_distinguished n X
  have hmono : Mono ((homologyFunctor 𝒜 i).map ((t.triangleLTGE n).obj X).mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff _ hT i]
    exact (isZero_of_isLE ((t.triangleLTGE n).obj X).obj₁ (n - 1) i (by lia)).eq_zero_of_src _
  have hepi : Epi ((homologyFunctor 𝒜 i).map ((t.triangleLTGE n).obj X).mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) (by lia)]
    exact (isZero_of_isLE ((t.triangleLTGE n).obj X).obj₁ (n - 1) (i + 1) (by lia)).eq_zero_of_tgt _
  exact isIso_of_mono_of_epi ((homologyFunctor 𝒜 i).map ((t.triangleLTGE n).obj X).mor₂)




private theorem boundedTower_to_truncGE_hasEventualInverses
    {F G : ℕᵒᵖ ⥤ DerivedCategory 𝒜} (φ : F ⟶ G)
    (hφ : NoetherianAdicCompletion.HasEventualInverses φ) (a : ℤ)
    (hbound : ∀ n, (F.obj n).IsGE a)
    (hle : ∀ n, (F.obj n).IsLE 0)
    (hGle : ∀ n, (G.obj n).IsLE 0)
    (hneg : ∀ i : ℤ, i < 0 → ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m,
      (homologyFunctor 𝒜 i).map (G.map (homOfLE h).op) = 0) :
    NoetherianAdicCompletion.HasEventualInverses
      (φ ≫ Functor.whiskerLeft G (t.truncGEπ 0)) := by
  have hG (i : ℤ) (hi : i ≠ 0) (n : ℕᵒᵖ) :
      IsZero ((homologyFunctor 𝒜 i).obj ((G ⋙ t.truncGE 0).obj n)) := by
    show IsZero ((homologyFunctor 𝒜 i).obj ((t.truncGE 0).obj (G.obj n)))
    by_cases h : i < 0
    · have : ((t.truncGE 0).obj (G.obj n)).IsGE 0 := t.isGE_truncGE_obj _ 0 0
      exact isZero_of_isGE _ 0 i h
    · have := hGle n
      have : ((t.truncGE 0).obj (G.obj n)).IsLE 0 := by infer_instance
      exact isZero_of_isLE _ 0 i (by omega)
  have hH (i : ℤ) : NoetherianAdicCompletion.HasEventualInverses
      (Functor.whiskerRight (φ ≫ Functor.whiskerLeft G (t.truncGEπ 0))
        (homologyFunctor 𝒜 i)) := by
    rw [Functor.whiskerRight_comp]
    apply (hφ.whiskerRight _).comp
    intro n
    by_cases hi : 0 ≤ i
    · have := isIso_homologyFunctor_map_truncGEπ i 0 hi (G.obj ⟨n⟩)
      refine ⟨n, le_rfl, inv ((homologyFunctor 𝒜 i).map
        ((t.truncGEπ 0).app (G.obj ⟨n⟩))), ?_, ?_⟩ <;> simp
    · obtain ⟨m, hm, hz⟩ := hneg i (by omega) n
      refine ⟨m, hm, 0, ?_, ?_⟩
      · simpa using hz.symm
      · exact (hG i (by omega) ⟨m⟩).eq_of_src _ _
  intro n
  obtain ⟨m, g, e, he₁, he₂⟩ := exists_proInverse_of_proInverse_homology
    (φ ≫ Functor.whiskerLeft G (t.truncGEπ 0)) (min a 0) 0
    (fun i hi n => by
      have := hbound n
      have := hle n
      rcases hi with hi | hi
      · exact isZero_of_isGE _ a i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact isZero_of_isLE _ 0 i hi)
    (fun i hi n => hG i (by omega) n)
    (fun i n => by
      obtain ⟨m, hm, s, hs₁, hs₂⟩ := hH i n.unop
      exact ⟨⟨m⟩, (homOfLE hm).op, s, hs₁, hs₂⟩)
    ⟨n⟩
  exact ⟨m.unop, leOfHom g.unop, e, he₁, he₂⟩

private theorem proZero_of_hasEventualInverses
    {C : Type*} [Category C] [Preadditive C]
    {F G : ℕᵒᵖ ⥤ C} (φ : F ⟶ G)
    (hφ : NoetherianAdicCompletion.HasEventualInverses φ)
    (hG : ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m, G.map (homOfLE h).op = 0) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m, F.map (homOfLE h).op = 0 := by
  intro n
  obtain ⟨m, hm, s, hs, _⟩ := hφ n
  obtain ⟨k, hk, hzero⟩ := hG m
  refine ⟨k, hm.trans hk, ?_⟩
  have he : (homOfLE (hm.trans hk)).op = (homOfLE hk).op ≫ (homOfLE hm).op :=
    Subsingleton.elim _ _
  rw [he, F.map_comp, ← hs, ← Category.assoc, φ.naturality, Category.assoc, hzero]
  simp

end BoundedTowers

/-- **Pro-isomorphisms cancel on the left.** If a map `φ` of inverse systems has eventual
inverses and so does its composite with a second map `π`, then `π` has eventual inverses: an
eventual inverse of `π` at level `n` is obtained from one of `φ ≫ π` at `n` and one of `φ` at the
level it produces. -/
theorem hasEventualInverses_of_comp {C : Type*} [Category C] {F G H : ℕᵒᵖ ⥤ C}
    (φ : F ⟶ G) (π : G ⟶ H) (hφ : NoetherianAdicCompletion.HasEventualInverses φ)
    (hφπ : NoetherianAdicCompletion.HasEventualInverses (φ ≫ π)) :
    NoetherianAdicCompletion.HasEventualInverses π := by
  intro n
  obtain ⟨m₁, hm₁, s₁, ha, hb⟩ := hφπ n
  obtain ⟨m₂, hm₂, s₂, hc, hd⟩ := hφ m₁
  simp only [NatTrans.comp_app] at ha hb
  refine ⟨m₂, hm₁.trans hm₂, H.map (homOfLE hm₂).op ≫ s₁ ≫ φ.app ⟨n⟩, ?_, ?_⟩
  · calc π.app ⟨m₂⟩ ≫ H.map (homOfLE hm₂).op ≫ s₁ ≫ φ.app ⟨n⟩
        = (π.app ⟨m₂⟩ ≫ H.map (homOfLE hm₂).op) ≫ s₁ ≫ φ.app ⟨n⟩ := by
          simp only [Category.assoc]
      _ = (G.map (homOfLE hm₂).op ≫ π.app ⟨m₁⟩) ≫ s₁ ≫ φ.app ⟨n⟩ := by rw [π.naturality]
      _ = ((s₂ ≫ φ.app ⟨m₁⟩) ≫ π.app ⟨m₁⟩) ≫ s₁ ≫ φ.app ⟨n⟩ := by rw [hd]
      _ = s₂ ≫ ((φ.app ⟨m₁⟩ ≫ π.app ⟨m₁⟩) ≫ s₁) ≫ φ.app ⟨n⟩ := by simp only [Category.assoc]
      _ = s₂ ≫ F.map (homOfLE hm₁).op ≫ φ.app ⟨n⟩ := by rw [ha]
      _ = s₂ ≫ φ.app ⟨m₁⟩ ≫ G.map (homOfLE hm₁).op := by rw [φ.naturality]
      _ = (s₂ ≫ φ.app ⟨m₁⟩) ≫ G.map (homOfLE hm₁).op := by simp only [Category.assoc]
      _ = G.map (homOfLE hm₂).op ≫ G.map (homOfLE hm₁).op := by rw [hd]
      _ = G.map (homOfLE (hm₁.trans hm₂)).op := by
          rw [← G.map_comp]
          congr 1
  · simp only [Category.assoc]
    rw [hb, ← H.map_comp]
    congr 1

/-- **The ideal-power tensor tower is pro-isomorphic to the adic quotient tower, by a
comparison normalized against the reduction maps.** For a finite module over a Noetherian ring
the comparison `n ↦ (M ⊗ᴸ A/Iⁿ⁺¹) ⟶ (M/Iⁿ⁺¹M)⟦0⟧` has eventual inverses: the fibres carry only
the Tor modules `Torᵢ(M, A/Iⁿ⁺¹)`, which are pro-zero by Tag 0911. The Koszul tower, which is
bounded below, is used as an intermediary.

The comparison is moreover *normalized*: the canonical map `M[0] ⟶ M[0] ⊗ᴸ A/Iⁿ⁺¹` followed by
it is the quotient map `M ↠ M/Iⁿ⁺¹M` itself. Without that clause the comparison is pinned down
only up to an automorphism of the target tower, and a statement normalizing the projections of
derived completion against the completion unit cannot be transported along it. The normalization
is not obtained by computing the comparison — that runs through Tor balancing — but by
identifying it: on `H⁰` the reduction map is a surjection onto a module abstractly isomorphic to
`M/Iⁿ⁺¹M`, so it factors through `M/Iⁿ⁺¹M` by an endomorphism-of-a-Noetherian-module argument
whose inverse is normalized by construction. -/
theorem exists_idealPowerTensor_adicQuotient_comparison_normalized
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {r : ℕ} (f : Fin r → R) (hf : Ideal.span (Set.range f) = I)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ π : NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
          AdicCompletionTor.adicQuotientSystem I M ⋙
            DerivedCategory.singleFunctor (ModuleCat.{u} R) 0,
      NoetherianAdicCompletion.HasEventualInverses π ∧
        ∀ n : ℕ, (NoetherianAdicCompletion.derivedReductionMap I T n).app
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≫ π.app ⟨n⟩ =
            (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
              (ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule R (M : Type u))).mkQ) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{u} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let F := NoetherianKoszulProIso.koszulPowerSystem f ⋙ T.tensor.obj (S.obj M)
  let G := NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj (S.obj M)
  let φ : F ⟶ G := Functor.whiskerRight
    (NoetherianAdicCompletion.koszulIdealPowerComparison f I hf.symm) (T.tensor.obj (S.obj M))
  have hφ : NoetherianAdicCompletion.HasEventualInverses φ :=
    (NoetherianAdicCompletion.koszulIdealPowerComparison_hasEventualInverses
      f I hf.symm).whiskerRight _
  have hle (n : ℕᵒᵖ) : (F.obj n).IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => koszulTensor_homology_isZero_outside R f T M n.unop i (Or.inr hi)
  have hge (n : ℕᵒᵖ) : (F.obj n).IsGE (-(r : ℤ)) := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => koszulTensor_homology_isZero_outside R f T M n.unop i (Or.inl hi)
  have hGle (n : ℕᵒᵖ) : (G.obj n).IsLE 0 := tensorQuotient_isLE R I T M n
  let ψ := φ ≫ Functor.whiskerLeft G (t.truncGEπ 0)
  have hψ : NoetherianAdicCompletion.HasEventualInverses ψ :=
    boundedTower_to_truncGE_hasEventualInverses φ hφ _ hge hle hGle
      (tensorQuotient_homology_proZero R I T M)
  let η := Functor.whiskerRight (Functor.whiskerLeft G (t.truncGEπ 0)) H
  have (n : ℕᵒᵖ) : IsIso (η.app n) :=
    isIso_homologyFunctor_map_truncGEπ 0 0 le_rfl (G.obj n)
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let eH : (G ⋙ t.truncGE 0) ⋙ H ≅ AdicCompletionTor.adicQuotientSystem I M :=
    (asIso η).symm ≪≫ tensorHomologyAdicQuotientNatIso I T M
  have hLE : ∀ n : ℕᵒᵖ, DerivedCategory.IsLE ((G ⋙ t.truncGE 0).obj n) 0 := fun n => by
    show ((DerivedCategory.TStructure.t.truncGE 0).obj (G.obj n)).IsLE 0
    have := hGle n
    infer_instance
  have hGE : ∀ n : ℕᵒᵖ, DerivedCategory.IsGE ((G ⋙ t.truncGE 0).obj n) 0 := fun n =>
    DerivedCategory.TStructure.t.isGE_truncGE_obj (G.obj n) 0 0
  let isoc := DerivedCategory.isoCompSingleFunctorOfIsLEOfIsGE (G ⋙ t.truncGE 0) 0 hLE hGE
  let e : G ⋙ t.truncGE 0 ≅ AdicCompletionTor.adicQuotientSystem I M ⋙ S :=
    isoc ≪≫ Functor.isoWhiskerRight eH S
  have he := hasEventualInverses_of_iso e
  refine ⟨Functor.whiskerLeft G (t.truncGEπ 0) ≫ e.hom, ?_, ?_⟩
  · refine hasEventualInverses_of_comp φ _ hφ ?_
    rw [← Category.assoc]
    exact hψ.comp he
  · intro n
    set ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
    have hS : ∀ {X Y : ModuleCat.{u} R} (g : X ⟶ Y),
        H.map (S.map g) = ε.hom.app X ≫ g ≫ ε.inv.app Y := fun g =>
      (NatIso.naturality_2 ε g).symm
    have hisoc : H.map (isoc.hom.app ⟨n⟩) = ε.inv.app (H.obj ((G ⋙ t.truncGE 0).obj ⟨n⟩)) :=
      DerivedCategory.homologyFunctor_map_isoCompSingleFunctorOfIsLEOfIsGE_hom_app
        (G ⋙ t.truncGE 0) 0 hLE hGE ⟨n⟩
    have hηinv : η.app ⟨n⟩ ≫ (asIso η).inv.app ⟨n⟩ = 𝟙 _ :=
      congrArg (fun α : (G ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} R))) ⋙ H ⟶
        (G ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} R))) ⋙ H => α.app ⟨n⟩) (asIso η).hom_inv_id
    have hproj : H.map ((Functor.whiskerLeft G (t.truncGEπ 0) ≫ e.hom).app ⟨n⟩) =
        (tensorHomologyAdicQuotientNatIso I T M).hom.app ⟨n⟩ ≫
          ε.inv.app ((AdicCompletionTor.adicQuotientSystem I M).obj ⟨n⟩) := by
      have hsplit : (Functor.whiskerLeft G (t.truncGEπ 0) ≫ e.hom).app ⟨n⟩ =
          (Functor.whiskerLeft G (t.truncGEπ 0)).app ⟨n⟩ ≫
            isoc.hom.app ⟨n⟩ ≫ S.map (eH.hom.app ⟨n⟩) := by
        simp [e]
      have heH : eH.hom.app ⟨n⟩ = (asIso η).inv.app ⟨n⟩ ≫
          (tensorHomologyAdicQuotientNatIso I T M).hom.app ⟨n⟩ := by simp [eH]
      have hηapp : H.map ((Functor.whiskerLeft G (t.truncGEπ 0)).app ⟨n⟩) = η.app ⟨n⟩ := rfl
      rw [hsplit, H.map_comp, H.map_comp, hisoc, hS, heH, hηapp]
      simp only [H, S, t, Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc]
      rw [← Category.assoc, hηinv]
      exact Category.id_comp _
    have hρ : H.map ((NoetherianAdicCompletion.derivedReductionMap I T n).app (S.obj M)) =
        ε.hom.app M ≫ reductionHomologyUnit I T M n := by
      rw [reductionHomologyUnit, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    refine (DerivedCategory.bijective_homologyFunctor_map (𝒜 := ModuleCat.{u} R) 0
      (S.obj M) (S.obj ((AdicCompletionTor.adicQuotientSystem I M).obj ⟨n⟩))
      inferInstance inferInstance inferInstance inferInstance).injective ?_
    show H.map ((NoetherianAdicCompletion.derivedReductionMap I T n).app (S.obj M) ≫
        (Functor.whiskerLeft G (t.truncGEπ 0) ≫ e.hom).app ⟨n⟩) =
      H.map (S.map (ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule R (M : Type u))).mkQ))
    rw [H.map_comp, hproj, hS, hρ]
    simp only [Category.assoc]
    rw [← Category.assoc (reductionHomologyUnit I T M n),
      reductionHomologyUnit_comp_tensorHomologyAdicQuotientNatIso I T M n]
    rfl

/-- **The ideal-power tensor tower is pro-isomorphic to the adic quotient tower.** For a finite
module over a Noetherian ring the comparison `n ↦ (M ⊗ᴸ A/Iⁿ⁺¹) ⟶ (M/Iⁿ⁺¹M)⟦0⟧` has eventual
inverses: the fibres carry only the Tor modules `Torᵢ(M, A/Iⁿ⁺¹)`, which are pro-zero by Tag
0911. The Koszul tower, which is bounded below, is used as an intermediary. -/
theorem exists_idealPowerTensor_adicQuotient_comparison
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {r : ℕ} (f : Fin r → R) (hf : Ideal.span (Set.range f) = I)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ π : NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
          AdicCompletionTor.adicQuotientSystem I M ⋙
            DerivedCategory.singleFunctor (ModuleCat.{u} R) 0,
      NoetherianAdicCompletion.HasEventualInverses π :=
  (exists_idealPowerTensor_adicQuotient_comparison_normalized R I f hf T M).imp
    fun _ => And.left

private def positiveQuotientToQuotient
    (R : Type u) [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R) :
    AdicCompletionTor.adicQuotientSystem I M ⟶
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem R I M :=
  NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ n)))
    (fun n => by
      change ModuleCat.ofHom (AdicCompletion.transitionMap I M _) ≫ _ = _
      unfold AlgebraicGeometry.ProEtale.adicQuotientModuleSystem
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      refine Submodule.Quotient.induction_on _ x ?_
      intro x
      rfl)

private theorem positiveQuotientToQuotient_hasEventualInverses
    (R : Type u) [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R) :
    NoetherianAdicCompletion.HasEventualInverses (positiveQuotientToQuotient R I M) := by
  intro n
  refine ⟨n + 1, Nat.le_succ n, 𝟙 _, ?_, ?_⟩
  · show ModuleCat.ofHom (AdicCompletion.transitionMap I M _) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  · show 𝟙 _ ≫ ModuleCat.ofHom (AdicCompletion.transitionMap I M _) = _
    rw [Category.id_comp]
    exact (Functor.ofOpSequence_map_homOfLE_succ
      (X := fun k : ℕ => ModuleCat.of R (M ⧸ (I ^ k • ⊤ : Submodule R M)))
      (fun k => ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ k))) n).symm

private def tensorAssocFunctorIso (R : Type u) [CommRing R]
    (C M : DerivedCategory (ModuleCat.{u} R)) :
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
    T.tensor.obj ((T.tensor.obj C).obj M) ≅ T.tensor.obj M ⋙ T.tensor.obj C := by
  let h := CochainComplex.DerivedTensor.derivedTensorProduct_associator R
  let a := Classical.choose h
  refine NatIso.ofComponents (a C M) ?_
  intro X Y g
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.comp_map]
    using (Classical.choose_spec h).1 (𝟙 C) (𝟙 M) g

private theorem tensorAssocFunctorIso_hom_app (R : Type u) [CommRing R]
    (C M X : DerivedCategory (ModuleCat.{u} R)) :
    (tensorAssocFunctorIso R C M).hom.app X =
      (Classical.choose (CochainComplex.DerivedTensor.derivedTensorProduct_associator R)
        C M X).hom :=
  rfl

/-- **The reduction maps survive the associativity rewrite.** The canonical map
`C ⊗ᴸ M ⟶ (C ⊗ᴸ M) ⊗ᴸ A/Iⁿ`, followed by associativity, is `C ⊗ᴸ -` applied to the canonical map
`M ⟶ M ⊗ᴸ A/Iⁿ`.

Associativity in the third variable moves the quotient map across, and the unit-associator
coherence `DerivedCategory.Invertible.rightUnitor_inv_comp_associator` moves the right unit; the
two together are exactly what a statement normalizing the projections of the tower
`n ↦ (C ⊗ᴸ M) ⊗ᴸ A/Iⁿ` against the completion unit has to transport. -/
private theorem derivedReductionMap_comp_tensorAssocFunctorIso (R : Type u) [CommRing R]
    (I : Ideal R) (C M : DerivedCategory (ModuleCat.{u} R)) (n : ℕ) :
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
    (NoetherianAdicCompletion.derivedReductionMap I T n).app ((T.tensor.obj C).obj M) ≫
        (tensorAssocFunctorIso R C M).hom.app
          ((NoetherianAdicCompletion.idealPowerQuotientSystem I).obj ⟨n⟩) =
      (T.tensor.obj C).map ((NoetherianAdicCompletion.derivedReductionMap I T n).app M) := by
  intro T
  have hnat := (tensorAssocFunctorIso R C M).hom.naturality
    (NoetherianAdicCompletion.idealPowerQuotientMap I n)
  dsimp only [Functor.comp_map] at hnat
  simp only [NoetherianAdicCompletion.derivedReductionMap, NatTrans.comp_app,
    Functor.flip_map_app, Category.assoc]
  rw [hnat, ← Category.assoc, tensorAssocFunctorIso_hom_app,
    DerivedCategory.Invertible.rightUnitor_inv_comp_associator C M, ← Functor.map_comp]

/-- **The two towers of Stacks 0EEW have the same derived limits.** If `K` is a derived limit of
the tower `n ↦ (C ⊗ᴸ M) ⊗ᴸ A/Iⁿ⁺¹` — which is what derived `I`-adic completion of `C ⊗ᴸ M`
computes — then it is a derived limit of the tower `n ↦ C ⊗ᴸ (M/IⁿM)`. -/
theorem isDerivedLimit_tensor_adicQuotient
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I.FG) (M : ModuleCat.{u} R) [Module.Finite R M]
    (C K : DerivedCategory (ModuleCat.{u} R))
    (hK : let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
      IsDerivedLimit (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj ((T.tensor.obj C).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) K) :
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
    IsDerivedLimit
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem R I M ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ T.tensor.obj C) K := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  obtain ⟨π, hπ⟩ := exists_idealPowerTensor_adicQuotient_comparison R I f hf T M
  have h₁ := isDerivedLimit_of_natIso
    (Functor.isoWhiskerLeft (NoetherianAdicCompletion.idealPowerQuotientSystem I)
      (tensorAssocFunctorIso R C (S.obj M))) hK
  have h₂ := isDerivedLimit_of_hasEventualInverses
    (Functor.whiskerRight π (T.tensor.obj C)) (hπ.whiskerRight (T.tensor.obj C)) h₁
  exact isDerivedLimit_of_hasEventualInverses
    (Functor.whiskerRight (positiveQuotientToQuotient R I M) (S ⋙ T.tensor.obj C))
    ((positiveQuotientToQuotient_hasEventualInverses R I M).whiskerRight _) h₂

/-- The quotient maps onto the positive-index adic quotients refine to those of the full tower. -/
private theorem mkQ_comp_positiveQuotientToQuotient (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) (n : ℕ) :
    adicQuotientMk I M n ≫ (positiveQuotientToQuotient R I M).app ⟨n⟩ =
      ModuleCat.ofHom (I ^ n • (⊤ : Submodule R (M : Type u))).mkQ :=
  ModuleCat.hom_ext <| LinearMap.ext fun _ => rfl

/-- **The two towers of Stacks 0EEW have the same derived limits, with the projections carried
across and normalized.** If `K` is a derived limit of `n ↦ (C ⊗ᴸ M) ⊗ᴸ A/Iⁿ⁺¹` with projections
`p`, and `w` is a map into `K` whose composites with the `p` are the canonical reduction maps,
then `K` is a derived limit of `n ↦ C ⊗ᴸ (M/IⁿM)` with projections whose composites with `w` are
`C ⊗ᴸ -` of the quotient maps `M ↠ M/IⁿM`.

This is the form `Dualizing.isDerivedLimit_completedLocalCohomology` cannot provide: being a
derived limit is a property of the object, so the projections it supplies are determined only up
to an automorphism of the limit, and nothing downstream can identify them. Here the transport is
through `IsDerivedLimitWithProjections.ofNatIso` and
`IsDerivedLimitWithProjections.comp_of_hasEventualInverses`, both of which name the resulting
projections, and every comparison in the chain is normalized: associativity by
`derivedReductionMap_comp_tensorAssocFunctorIso`, the Tor comparison by
`exists_idealPowerTensor_adicQuotient_comparison`, and the reindexing by
`mkQ_comp_positiveQuotientToQuotient`. -/
theorem isDerivedLimitWithProjections_tensor_adicQuotient
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I.FG) (M : ModuleCat.{u} R) [Module.Finite R M]
    (C K : DerivedCategory (ModuleCat.{u} R))
    (p : ∀ n : ℕ, K ⟶ (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj C).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))).obj ⟨n⟩)
    (w : ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj C).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶ K)
    (hK : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj C).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) K p)
    (hw : ∀ n : ℕ, w ≫ p n =
      (NoetherianAdicCompletion.derivedReductionMap I
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) n).app
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj C).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) :
    ∃ q : ∀ n : ℕ, K ⟶ (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem R I M ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj C).obj ⟨n⟩,
      NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem R I M ⋙
            DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
              (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj C) K q ∧
        ∀ n : ℕ, w ≫ q n =
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj C).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
              (ModuleCat.ofHom (I ^ n • (⊤ : Submodule R (M : Type u))).mkQ)) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  obtain ⟨π, hπ, hπnorm⟩ := exists_idealPowerTensor_adicQuotient_comparison_normalized R I f hf T M
  let eassoc := Functor.isoWhiskerLeft (NoetherianAdicCompletion.idealPowerQuotientSystem I)
    (tensorAssocFunctorIso R C (S.obj M))
  have h₁ := hK.ofNatIso eassoc
  have hw₁ : ∀ n : ℕ, w ≫ (p n ≫ eassoc.hom.app ⟨n⟩) =
      (T.tensor.obj C).map
        ((NoetherianAdicCompletion.derivedReductionMap I T n).app (S.obj M)) := by
    intro n
    rw [← Category.assoc, hw n]
    exact derivedReductionMap_comp_tensorAssocFunctorIso R I C (S.obj M) n
  let φ := Functor.whiskerRight π (T.tensor.obj C)
  have h₂ := h₁.comp_of_hasEventualInverses φ (hπ.whiskerRight (T.tensor.obj C))
  have hw₂ : ∀ n : ℕ, w ≫ ((p n ≫ eassoc.hom.app ⟨n⟩) ≫ φ.app ⟨n⟩) =
      (T.tensor.obj C).map (S.map
        (ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule R (M : Type u))).mkQ)) := by
    intro n
    rw [← Category.assoc, hw₁ n]
    show (T.tensor.obj C).map _ ≫ (T.tensor.obj C).map (π.app ⟨n⟩) = _
    rw [← Functor.map_comp, hπnorm n]
    rfl
  let χ := Functor.whiskerRight (positiveQuotientToQuotient R I M) (S ⋙ T.tensor.obj C)
  have h₃ := h₂.comp_of_hasEventualInverses χ
    ((positiveQuotientToQuotient_hasEventualInverses R I M).whiskerRight _)
  refine ⟨_, h₃, fun n => ?_⟩
  rw [← Category.assoc, hw₂ n]
  show (T.tensor.obj C).map (S.map (adicQuotientMk I M n)) ≫
      (T.tensor.obj C).map (S.map ((positiveQuotientToQuotient R I M).app ⟨n⟩)) = _
  rw [← Functor.map_comp, ← Functor.map_comp, mkQ_comp_positiveQuotientToQuotient R I M n]
  rfl

end Dualizing.AdicQuotientComparison

end
