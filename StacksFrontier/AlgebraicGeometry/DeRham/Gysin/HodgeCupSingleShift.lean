module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeBridgeShift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.DerivedLeftUnitorSingle
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductUnit

/-!
# The cup product with a class placed in degree `c`, through the shift

A multiplication `μ : F ⊗ G ⟶ H` of sheaves of modules induces multiplications of complexes
`Tot(F[0] ⊗ G[-c]) ⟶ H[-c]` and `Tot(F[0] ⊗ G[0]) ⟶ H[0]`
(`Stacks.DeRham.GysinCupHodge.singleTensorMult`). Through the identifications
`singleNatShiftIso : G[-c] ≅ G[0][-c]` the first is the shift of the second
(`multiplicationInt_singleTensorMult_shift`), and on cohomology the cup product of Section 0FKU
along the first is `(-1)^{ic}` times the cup product along the second, read through the shift
identifications (`canonicalPairingModule_singleTensorMult_shift`). The sign is the one of
`Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₂`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

/-- Reassociating a composite and replacing two factors. At variables. -/
private lemma chase_L {V : Type*} [Category* V] {P Q₁ Q₂ T U U' W R : V} (a₁ : P ⟶ Q₁)
    (a₂ : Q₁ ⟶ Q₂) (ι : Q₂ ⟶ T) (m : T ⟶ U) (x : U ⟶ U') (s : U' ⟶ W) (t : Q₂ ⟶ R)
    (r : R ⟶ U) (h : ι ≫ m = t ≫ r) :
    a₁ ≫ a₂ ≫ ι ≫ (m ≫ x) ≫ s = a₁ ≫ a₂ ≫ t ≫ r ≫ x ≫ s := by
  rw [← reassoc_of% h]
  simp only [Category.assoc]

/-- Reassociating a composite and replacing two factors. At variables. -/
private lemma chase_R {V : Type*} [Category* V] {P Q₁ Q₂ Q₃ Q₄ T U U' W R : V} (a₁ : P ⟶ Q₁)
    (a₂ : Q₁ ⟶ Q₂) (a₃ : Q₂ ⟶ Q₃) (a₄ : Q₃ ⟶ Q₄) (ι : Q₄ ⟶ T) (m : T ⟶ U) (x : U ⟶ U')
    (s : U' ⟶ W) (t : Q₄ ⟶ R) (r : R ⟶ U) (h : ι ≫ m = t ≫ r) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ ι ≫ (m ≫ x) ≫ s = a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ t ≫ r ≫ x ≫ s := by
  rw [← reassoc_of% h]
  simp only [Category.assoc]

/-- A morphism followed by an isomorphism inverted and the isomorphism. At variables. -/
private lemma comp_inv_hom {V : Type*} [Category* V] {A B C : V} (f : A ⟶ B) (e : C ≅ B) :
    (f ≫ e.inv) ≫ e.hom = f := by
  simp

/-- Solving a square for the inverses of two of its sides. At variables. -/
private lemma inv_chase {V : Type*} [Category* V] {P Q R S W : V} (m : Q ⟶ W) (σ : W ≅ S)
    (T : Q ⟶ P) (Tinv : P ⟶ Q) (Sh : P ⟶ R) (m0 : R ⟶ S) (h : m ≫ σ.hom = T ≫ Sh ≫ m0)
    (hT : Tinv ≫ T = 𝟙 P) : Tinv ≫ m = Sh ≫ m0 ≫ σ.inv := by
  rw [← Category.comp_id m, ← σ.hom_inv_id, ← Category.assoc m, h]
  simp only [Category.assoc]
  rw [← Category.assoc Tinv, hT, Category.id_comp]

/-- The algebra of `canonicalPairingModule_singleTensorMult_shift`, at variables. -/
private lemma pairing_shift_chase {V : Type*} [Category* V] [Preadditive V]
    {P P₁ T₁ T₂ T₃ U₁ U₂ U₃ U₄ W₁ W₂ W₃ : V}
    (L : P ⟶ P₁) (x₁ : P₁ ⟶ T₁) (x₂ : P₁ ⟶ T₂) (x₃ : P₁ ⟶ T₃) (t₁ : T₁ ⟶ U₁) (t₂ : T₂ ⟶ U₂)
    (t₃ : T₃ ⟶ U₃) (mc : U₁ ⟶ W₁) (nσ : U₂ ⟶ U₁) (sh : U₂ ⟶ U₄) (m0s : U₄ ⟶ W₂) (σH : W₂ ⟶ W₁)
    (rt : U₄ ⟶ U₃) (m0 : U₃ ⟶ W₃) (rH : W₂ ≅ W₃) (ε : ℤˣ) (x₃' : P₁ ⟶ T₃) (hx : x₃' = x₃)
    (x₁' : P₁ ⟶ T₁) (hx₁ : x₁' = x₁) (n1 : L ≫ x₂ ≫ t₂ ≫ nσ = L ≫ x₁' ≫ t₁)
    (ch : nσ ≫ mc = sh ≫ m0s ≫ σH)
    (nr : m0s ≫ rH.hom = rt ≫ m0) (sh2 : L ≫ x₂ ≫ t₂ ≫ sh ≫ rt = ε • (L ≫ x₃' ≫ t₃))
    (ε' : ℤˣ) (hε : ε' = ε) (cPMc : T₁ ⟶ W₁) (hc : cPMc = t₁ ≫ mc) (cPM0 : T₃ ⟶ W₃)
    (h0 : cPM0 = t₃ ≫ m0) :
    L ≫ x₁ ≫ cPMc = ε' • (L ≫ x₃ ≫ cPM0 ≫ rH.inv ≫ σH) := by
  subst hx hc h0 hx₁
  rw [hε]
  simp only [Category.assoc]
  have e : m0s = rt ≫ m0 ≫ rH.inv := by rw [← reassoc_of% nr, Iso.hom_inv_id, Category.comp_id]
  have sh2' : L ≫ x₂ ≫ t₂ ≫ sh ≫ rt ≫ m0 ≫ rH.inv ≫ σH =
      (ε • (L ≫ x₃' ≫ t₃)) ≫ m0 ≫ rH.inv ≫ σH := by
    rw [← sh2]
    simp only [Category.assoc]
  rw [← reassoc_of% n1, ch, e]
  simp only [Category.assoc]
  rw [sh2', Linear.units_smul_comp]
  simp only [Category.assoc]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- A sheaf placed in degree `c`, extended by zero, vanishes outside the degree `c`. -/
lemma isZero_singleNat_extend_X
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) (n : ℤ) (hn : n ≠ (c : ℤ)) :
    IsZero (((singleNat N c).extend ComplexShape.embeddingUpNat).X n) :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (c : ℤ) _ n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N c (c : ℤ) rfl))

/-- The degree-`c` component of `singleNatShiftIso` is an identification of objects. -/
lemma singleNatShiftIso_hom_f
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) : ∃ h, (singleNatShiftIso N c).hom.f (c : ℤ) = eqToHom h := by
  have e₁ : ((CochainComplex.singleFunctors _).shiftIso (-(c : ℤ)) (c : ℤ) 0
      (by omega)).symm.hom.app N =
      ((CochainComplex.singleFunctors _).shiftIso (-(c : ℤ)) (c : ℤ) 0 (by omega)).inv.app N := rfl
  simp only [singleNatShiftIso, Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom, e₁,
    Functor.mapIso_hom, Iso.symm_hom, CochainComplex.shiftFunctor_map_f',
    HomologicalComplex.extendSingleIso_hom_f]
  rw [AlgebraicGeometry.SheafOfModules.singleFunctors_shiftIso_inv_app_f _ _ _ _ _ _
    ((HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (c : ℤ) _).trans (by
      show _ = ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N).X ((c : ℤ) + -(c : ℤ))
      rw [add_neg_cancel]
      exact (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) 0 _).symm))]
  simp only [HomologicalComplex.extendSingleIso, HomologicalComplex.mkHomFromSingle,
    HomologicalComplex.mkHomToSingle_f, dif_pos (show (c : ℤ) + -(c : ℤ) = 0 by omega),
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, HomologicalComplex.XIsoOfEq,
    eqToIso.hom, eqToIso.inv, eqToHom_trans, Category.assoc]
  repeat (first | exact ⟨_, rfl⟩ | apply AlgebraicGeometry.SheafOfModules.exists_eqToHom_comp)

/-- **The multiplication of `F[0]` and `G[-c]` is the shift of that of `F[0]` and `G[0]`**,
through `singleNatShiftIso` and the commutation of the total tensor complex with the shift of
the second variable. -/
theorem multiplicationInt_singleTensorMult_shift
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (c : ℕ) :
    multiplicationInt (singleTensorMult μ 0 c c (zero_add c)) ≫ (singleNatShiftIso H c).hom =
      HomologicalComplex.mapBifunctorMap (𝟙 ((singleNat F 0).extend ComplexShape.embeddingUpNat))
          (singleNatShiftIso G c).hom (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ≫
        (CochainComplex.mapBifunctorShift₂Iso ((singleNat F 0).extend ComplexShape.embeddingUpNat)
          ((singleNat G 0).extend ComplexShape.embeddingUpNat)
          (sheafTensor.{u, u, u, u, u} X.sheaf) (-(c : ℤ))).hom ≫
        (multiplicationInt (singleTensorMult μ 0 0 0 rfl))⟦-(c : ℤ)⟧' := by
  ext d : 1
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  by_cases hp : p = ((0 : ℕ) : ℤ)
  swap
  · exact (AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_left
      (isZero_singleNat_extend_X F 0 p hp) _).eq_of_src _ _
  by_cases hq : q = (c : ℤ)
  swap
  · exact (AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_right _
      (isZero_singleNat_extend_X G c q hq)).eq_of_src _ _
  subst hp hq
  obtain rfl : d = ((c : ℕ) : ℤ) := by
    have : ((0 : ℕ) : ℤ) + (c : ℤ) = d := hpq
    omega
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ (-(c : ℤ)) ((0 : ℕ) : ℤ) (c : ℤ)
      (c : ℤ) _ ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) (by omega) (by omega),
    CochainComplex.shiftFunctor_map_f']
  rw [show (((0 : ℕ) : ℤ) * -(c : ℤ)).negOnePow = 1 by simp, one_smul]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  rw [AlgebraicGeometry.SheafOfModules.eqToHom_comp_f_eq
      (multiplicationInt (singleTensorMult μ 0 0 0 rfl)) ((0 : ℕ) : ℤ) _ (by omega)]
  simp only [CochainComplex.ιMapBifunctor, eqToHom_refl, Category.id_comp]
  rw [AlgebraicGeometry.SheafOfModules.ι_multiplicationInt_f_assoc _ 0 0 0 (by simp),
    AlgebraicGeometry.SheafOfModules.ι_multiplicationInt_f_assoc _ c 0 c hpq]
  obtain ⟨h₁, e₁⟩ := singleNatShiftIso_hom_f G c
  obtain ⟨h₂, e₂⟩ := singleNatShiftIso_hom_f H c
  refine (chase_L _ _ _ _ _ _ _ _ (ι_singleTensorMult_f μ 0 c c _ _)).trans
    (Eq.trans ?_ (chase_R _ _ _ _ _ _ _ _ _ _ (ι_singleTensorMult_f μ 0 0 0 _ _)).symm)
  rw [e₁, e₂]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, HomologicalComplex.XIsoOfEq,
    eqToIso.hom, eqToIso.inv]
  have hA : ∀ {P Q : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)} (e : P = Q) (Z : _),
      ∃ h, ((sheafTensor.{u, u, u, u, u} X.sheaf).map (eqToHom e)).app Z = eqToHom h :=
    fun {_ _} e Z => AlgebraicGeometry.SheafOfModules.exists_eqToHom_app
      (AlgebraicGeometry.SheafOfModules.exists_eqToHom_map _ ⟨e, rfl⟩) Z
  have hM : ∀ (Z : _) {P Q : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)} (e : P = Q),
      ∃ h, ((sheafTensor.{u, u, u, u, u} X.sheaf).obj Z).map (eqToHom e) = eqToHom h :=
    fun Z {_ _} e => AlgebraicGeometry.SheafOfModules.exists_eqToHom_map _ ⟨e, rfl⟩
  have tail : ∀ {P : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)} (e : P = F)
      {W : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)} (h' : H = W),
      AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich μ
        (((sheafTensor.{u, u, u, u, u} X.sheaf).map (eqToHom e)).app G ≫ μ ≫ eqToHom h') :=
    fun {P} e {W} h' => AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hA e G)
      (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.post
        (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.self μ) ⟨h', rfl⟩)
  refine AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.eq (f := μ) ?_ ?_
  · exact AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hA _ _)
      (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hM _ _)
        (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hM _ _)
          (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.post (tail _ _)
            (AlgebraicGeometry.SheafOfModules.exists_eqToHom_comp ⟨_, rfl⟩ ⟨_, rfl⟩))))
  · exact AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hM _ _)
      (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hM _ _)
        (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hA _ _)
          (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hM _ _)
            (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.pre (hM _ _)
              (AlgebraicGeometry.SheafOfModules.IsEqToHomSandwich.post (tail _ _)
                (AlgebraicGeometry.SheafOfModules.exists_eqToHom_comp ⟨_, rfl⟩ ⟨_, rfl⟩))))))

/-- The total tensor complex of the identity and of an isomorphism and its inverse. -/
lemma mapBifunctorMap_id_inv_hom
    {K M M' : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ}
    (e : M ≅ M') :
    HomologicalComplex.mapBifunctorMap (𝟙 K) e.inv (sheafTensor.{u, u, u, u, u} X.sheaf)
        (ComplexShape.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 K) e.hom (sheafTensor.{u, u, u, u, u} X.sheaf)
        (ComplexShape.up ℤ) = 𝟙 _ := by
  ext n : 1
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f, Category.comp_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [← Functor.map_comp_assoc, ← HomologicalComplex.comp_f, e.inv_hom_id,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]

open Stacks.Cohomology.DerivedGlobalCupProduct (shiftCohomologyIsoR totalCupPairing) in
/-- **(N-S) The cup product with a class placed in degree `c` is the shifted cup product with
the class placed in degree `0`, up to the sign `(-1)^{ic}`**: for classes `ξ ∈ Hⁱ(RΓ(F[0]))` and
`η ∈ Hʲ(RΓ(G[0]))`, the cup product along `μ` of `ξ` with `η` moved to `Hʲ⁺ᶜ(RΓ(G[-c]))` by the
shift identification and `singleNatShiftIso` is `(-1)^{ic}` times the cup product of `ξ` and
`η`, moved to `Hⁱ⁺ʲ⁺ᶜ(RΓ(H[-c]))` in the same way. -/
theorem canonicalPairingModule_singleTensorMult_shift
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (c : ℕ) (i j a : ℤ)
    (ha : -(c : ℤ) + a = j) (hb : -(c : ℤ) + (i + a) = i + j)
    (ξ : ModuleCat.of (baseRing (baseRingedSpace X.sheaf)) (baseRing (baseRingedSpace X.sheaf)) ⟶
      cohomologyModule (moduleDerived (A := X.sheaf) (singleNat F 0)) i)
    (η : ModuleCat.of (baseRing (baseRingedSpace X.sheaf)) (baseRing (baseRingedSpace X.sheaf)) ⟶
      cohomologyModule (moduleDerived (A := X.sheaf) (singleNat G 0)) j) :
    (λ_ (ModuleCat.of (baseRing (baseRingedSpace X.sheaf))
      (baseRing (baseRingedSpace X.sheaf)))).inv ≫
        (ξ ⊗ₘ (η ≫ (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf)
            ((singleNat G 0).extend ComplexShape.embeddingUpNat)
            (-(c : ℤ)) a j ha).inv ≫
          (DerivedCategory.homologyFunctor _ a).map ((baseSections (baseRingedSpace X.sheaf)).map
            (DerivedCategory.Q.map (singleNatShiftIso G c).inv)))) ≫
        canonicalPairingModule (singleTensorMult μ 0 c c (zero_add c)) i a =
      (i * c).negOnePow • ((λ_ (ModuleCat.of (baseRing (baseRingedSpace X.sheaf))
          (baseRing (baseRingedSpace X.sheaf)))).inv ≫ (ξ ⊗ₘ η) ≫
        canonicalPairingModule (singleTensorMult μ 0 0 0 rfl) i j ≫
        (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf)
            ((singleNat H 0).extend ComplexShape.embeddingUpNat)
            (-(c : ℤ)) (i + a) (i + j) hb).inv ≫
          (DerivedCategory.homologyFunctor _ (i + a)).map
            ((baseSections (baseRingedSpace X.sheaf)).map
              (DerivedCategory.Q.map (singleNatShiftIso H c).inv))) := by
  let F₀ := (singleNat F 0).extend ComplexShape.embeddingUpNat
  let G₀ := (singleNat G 0).extend ComplexShape.embeddingUpNat
  have hK : ∃ n : ℤ, CochainComplex.IsStrictlyGE F₀ n := ⟨0, inferInstance⟩
  have hM : ∃ n : ℤ, CochainComplex.IsStrictlyGE G₀ n := ⟨0, inferInstance⟩
  have n1 := Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_naturality'
    (S := baseRingedSpace X.sheaf)
    (𝟙 F₀) (singleNatShiftIso G c).inv i a ξ
    (η ≫ (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf) G₀ (-(c : ℤ)) a j ha).inv)
  have hx₁ : ((ξ ≫ (DerivedCategory.homologyFunctor _ i).map ((baseSections
      (baseRingedSpace X.sheaf)).map (DerivedCategory.Q.map (𝟙 F₀)))) ⊗ₘ
      ((η ≫ (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf) G₀ (-(c : ℤ)) a j ha).inv) ≫
        (DerivedCategory.homologyFunctor _ a).map ((baseSections (baseRingedSpace X.sheaf)).map
          (DerivedCategory.Q.map (singleNatShiftIso G c).inv)))) =
      ξ ⊗ₘ (η ≫ (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf) G₀ (-(c : ℤ)) a j ha).inv ≫
        (DerivedCategory.homologyFunctor _ a).map ((baseSections (baseRingedSpace X.sheaf)).map
          (DerivedCategory.Q.map (singleNatShiftIso G c).inv))) :=
    congrArg₂ (· ⊗ₘ ·) ((congrArg (ξ ≫ ·)
      (Stacks.Cohomology.DerivedGlobalCupProduct.homology_map_Q_id _ _)).trans
        (Category.comp_id _)) (Category.assoc _ _ _)
  have chc : HomologicalComplex.mapBifunctorMap (𝟙 F₀) (singleNatShiftIso G c).inv
        (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ≫
        multiplicationInt (singleTensorMult μ 0 c c (zero_add c)) =
      (CochainComplex.mapBifunctorShift₂Iso F₀ G₀ (sheafTensor.{u, u, u, u, u} X.sheaf)
          (-(c : ℤ))).hom ≫
        (multiplicationInt (singleTensorMult μ 0 0 0 rfl))⟦-(c : ℤ)⟧' ≫
        (singleNatShiftIso H c).inv :=
    inv_chase _ _ _ _ _ _ (multiplicationInt_singleTensorMult_shift μ c)
      (mapBifunctorMap_id_inv_hom (singleNatShiftIso G c))
  have ch := (Stacks.Cohomology.DerivedGlobalCupProduct.homology_map_Q_comp
    (S := baseRingedSpace X.sheaf) (i + a)
    _ _).symm.trans ((congrArg (fun t => (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace X.sheaf))) (i + a)).map
        ((baseSections (baseRingedSpace X.sheaf)).map (DerivedCategory.Q.map t)))
      chc).trans ((Stacks.Cohomology.DerivedGlobalCupProduct.homology_map_Q_comp
        (S := baseRingedSpace X.sheaf) (i + a)
        _ _).trans (congrArg (_ ≫ ·) (Stacks.Cohomology.DerivedGlobalCupProduct.homology_map_Q_comp
          (S := baseRingedSpace X.sheaf) (i + a) _ _))))
  have nr := Stacks.Cohomology.DerivedGlobalCupProduct.shiftCohomologyIsoR_naturality
    (S := baseRingedSpace X.sheaf)
    (multiplicationInt (singleTensorMult μ 0 0 0 rfl)) (-(c : ℤ)) (i + a) (i + j) hb
  have sh2 := AlgebraicGeometry.SheafOfModules.totalCupPairing_shift₂_of_eq
    (S := baseRingedSpace X.sheaf) F₀ G₀ hK hM
    (-(c : ℤ)) i a j ha ξ
    (η ≫ (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf) G₀ (-(c : ℤ)) a j ha).inv)
  have hx : (ξ ⊗ₘ
      ((η ≫ (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf) G₀ (-(c : ℤ)) a j ha).inv) ≫
      (shiftCohomologyIsoR (S := baseRingedSpace X.sheaf) G₀ (-(c : ℤ)) a j ha).hom)) = ξ ⊗ₘ η :=
    congrArg (ξ ⊗ₘ ·) (comp_inv_hom _ _)
  exact pairing_shift_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx _ hx₁ n1 ch nr sh2 _
    (by rw [mul_neg, Int.negOnePow_neg]) _
    (AlgebraicGeometry.SheafOfModules.canonicalPairingModule_eq _ i a) _
    (AlgebraicGeometry.SheafOfModules.canonicalPairingModule_eq _ i j)

end StandardModel

end Stacks.DeRham.GysinCupHodge
