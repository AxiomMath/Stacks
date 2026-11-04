module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedPerfectShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedShiftClass
public import StacksFrontier.Algebra.Homology.SingleSinglePairingShift

/-!
# Perfect pairings of single complexes in all degrees

For sheaves of `𝒪_X`-modules `M`, `N`, `H` and `φ : M ⊗ N ⟶ H`, if the pairing
`Q(M[0]) ⊗^L Q(N[0]) ⟶ Q(H[0])` induced by `φ` is perfect (every `Z ⊗^L Q(N[0]) ⟶ Q(H[0])` is
`(v ⊗ 1) ≫` it for a unique `v`), then so is the pairing `Q(M[-a]) ⊗^L Q(N[-b]) ⟶ Q(H[-a-b])` for
all `a` and `b`. This gives the perfectness of the wedge product of the graded pieces of the de
Rham complex in the proof of [Stacks, Tag 0G8K] from that of the wedge product of forms in degree
zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (D : RelativeDualitySituation.{u})

/-- **Perfectness of an induced pairing is invariant under isomorphisms** of the paired complexes
and of the target. -/
theorem bijective_pairingPrecomp_toTensor_mapBifunctorMap_comp
    {K K' L L' W W' : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ} (α : K' ⟶ K) (β : L' ⟶ L)
    [IsIso α] [IsIso β] (g : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj K).obj L ⟶ W)
    (γ : W ⟶ W') [IsIso γ]
    (hg : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor K L ≫
        DerivedCategory.Q.map g) Z))
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor K' L' ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap α β
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          (ComplexShape.up ℤ)) ≫ DerivedCategory.Q.map g ≫ DerivedCategory.Q.map γ) Z) := by
  let T := derivedTensorProductFunctor D.X.toRingedSpace.sheaf
  let ψ := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor K L ≫
    DerivedCategory.Q.map g
  have nat := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor_naturality α β
  have hfun : T.pairingPrecomp ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
        K' L' ≫ DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap α β
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          (ComplexShape.up ℤ)) ≫ DerivedCategory.Q.map g ≫ DerivedCategory.Q.map γ) Z =
      (fun t => t ≫ DerivedCategory.Q.map γ) ∘
        (fun t => (T.obj Z).map (DerivedCategory.Q.map β) ≫ t) ∘ T.pairingPrecomp ψ Z ∘
          (fun v => v ≫ DerivedCategory.Q.map α) := by
    funext v
    have e2 := congrArg (· ≫ DerivedCategory.Q.map g ≫ DerivedCategory.Q.map γ) nat.symm
    have n1 := (T.map (DerivedCategory.Q.map α)).naturality (DerivedCategory.Q.map β)
    have n2 := (T.map v).naturality (DerivedCategory.Q.map β)
    refine (congrArg ((T.map v).app _ ≫ ·) ((Category.assoc _ _ _).symm.trans e2)).trans ?_
    have n3 := (T.map (v ≫ DerivedCategory.Q.map α)).naturality (DerivedCategory.Q.map β)
    simp only [Function.comp_apply, Functor.pairingPrecomp, ψ, Functor.map_comp, NatTrans.comp_app,
      Category.assoc] at n3 ⊢
    have n4 := congrArg (· ≫ (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor K L ≫
      DerivedCategory.Q.map g ≫ DerivedCategory.Q.map γ) n3
    simp only [Category.assoc] at n4
    exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (Category.assoc _ _ _)))).trans n4.symm
  rw [hfun]
  exact (Function.Bijective.comp (asIso (DerivedCategory.Q.map γ)).homToEquiv.bijective
    (Function.Bijective.comp
      ((T.obj Z).mapIso (asIso (DerivedCategory.Q.map β))).homFromEquiv.symm.bijective
      (Function.Bijective.comp (hg Z) (asIso (DerivedCategory.Q.map α)).homToEquiv.bijective)))

/-- Perfectness of a pairing is unchanged by composing with an isomorphism of the target. -/
theorem bijective_pairingPrecomp_comp_iff
    {P L W W' : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf}
    (φ : ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj P).obj L ⟶ W) (k : W ⟶ W')
    [IsIso k]
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      (φ ≫ k) Z) ↔
      Function.Bijective
        ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp φ Z) := by
  have e : (derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp (φ ≫ k) Z =
      (fun t => t ≫ k) ∘ (derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp φ Z :=
    funext fun v => (Category.assoc _ _ _).symm
  rw [e]
  exact Function.Bijective.of_comp_iff' (asIso k).homToEquiv.bijective _

/-- Perfectness of a pairing is unchanged by a sign. -/
theorem bijective_pairingPrecomp_units_smul_iff
    {P L W : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf}
    (φ : ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj P).obj L ⟶ W) (ε : ℤˣ)
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      (ε • φ) Z) ↔
      Function.Bijective
        ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp φ Z) := by
  have e : (derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp (ε • φ) Z =
      (fun t => ε • t) ∘ (derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp φ Z :=
    funext fun v => Linear.comp_units_smul _ _ _
  rw [e]
  refine Function.Bijective.of_comp_iff' ?_ _
  refine Function.Involutive.bijective fun t => ?_
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- Perfectness of `φ ≫ ε • (ψ ≫ k)` is that of `φ ≫ ψ`, for a sign `ε` and an isomorphism `k`. -/
theorem bijective_pairingPrecomp_comp_units_smul_comp_iff
    {P L V W W' : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf}
    (φ : ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj P).obj L ⟶ V) (ε : ℤˣ)
    (ψ : V ⟶ W) (k : W ⟶ W') [IsIso k]
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      (φ ≫ (ε • (ψ ≫ k))) Z) ↔
      Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
        (φ ≫ ψ) Z) := by
  rw [Units.smul_def, Preadditive.comp_zsmul, ← Units.smul_def,
    D.bijective_pairingPrecomp_units_smul_iff, ← Category.assoc,
    D.bijective_pairingPrecomp_comp_iff]

/-- **Shifts of perfect pairings of complexes are perfect.** -/
theorem bijective_pairingPrecomp_shiftedPairing_toTensor
    {A B W : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (g : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ W) (a b : ℤ) (hab : a + b = 0)
    (hg : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
        DerivedCategory.Q.map g) Z))
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor (A⟦a⟧) (B⟦b⟧) ≫
        DerivedCategory.Q.map
          ((tensorComplexBifunctorOn D.X.toRingedSpace).shiftedPairing g a b hab)) Z) := by
  let := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
  have key := Stacks.Cohomology.DerivedPullbackTensor.shiftedPairing_toTensor_comp
    D.X.toRingedSpace g a b hab
  have hc := Functor.pairingCompatible_of_eq
    ((DerivedCategory.Q.commShiftIso a).hom.app A) ((DerivedCategory.Q.commShiftIso b).hom.app B)
    key
  refine (Functor.bijective_pairingPrecomp_iff_of_pairingCompatible _ _ hc Z).2 ?_
  exact (Functor.bijective_pairingPrecomp_shiftedPairing_iff
    (derivedTensorProductFunctor D.X.toRingedSpace.sheaf) _ a b hab Z).2 (hg _)

/-- The pairing of `M[-a]` and `N[-b]` induced by `φ`, transported along equalities of degrees. -/
theorem singleSinglePairing_congr {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C] [HasZeroObject C₁] [HasZeroObject C₂]
    [HasZeroObject C] (F : C₁ ⥤ C₂ ⥤ C) [F.Additive] [∀ X₁ : C₁, (F.obj X₁).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      CochainComplex.HasMapBifunctor K₁ K₂ F]
    (M : C₁) (N : C₂) {H : C} (φ : (F.obj M).obj N ⟶ H) (a b a' b' : ℤ) (ha : a = a')
    (hb : b = b') :
    CochainComplex.singleSinglePairing F M N a' b' φ =
      HomologicalComplex.mapBifunctorMap
          (eqToHom (congrArg (fun k => (HomologicalComplex.single C₁ (ComplexShape.up ℤ) k).obj M)
            ha.symm))
          (eqToHom (congrArg (fun k => (HomologicalComplex.single C₂ (ComplexShape.up ℤ) k).obj N)
            hb.symm)) F (ComplexShape.up ℤ) ≫
        CochainComplex.singleSinglePairing F M N a b φ ≫
        eqToHom (congrArg (fun k => (HomologicalComplex.single C (ComplexShape.up ℤ) k).obj H)
          (by rw [ha, hb])) := by
  subst ha hb
  simp

/-- Mapping an equation `a ≫ b ≫ c = ε • (p ≫ k)` of complexes to the derived category. -/
private theorem Q_map_comp_comp_eq_units_smul
    {A B C E F : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ F) (ε : ℤˣ) (p : A ⟶ E) (k : E ⟶ F) (h : a ≫ b ≫ c = ε • (p ≫ k)) :
    DerivedCategory.Q.map a ≫ DerivedCategory.Q.map b ≫ DerivedCategory.Q.map c =
      ε • (DerivedCategory.Q.map p ≫ DerivedCategory.Q.map k) := by
  rw [← Functor.map_comp, ← Functor.map_comp, h, Functor.PairingPushData.map_units_smul,
    Functor.map_comp]

/-- Perfectness of a pairing of complexes transfers along an isomorphism of the variables and the
target, up to a sign and an isomorphism `k` in the derived category. -/
private theorem bijective_pairingPrecomp_toTensor_of_comp_eq_units_smul
    {K K' L L' W W' V : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ} (α : K' ⟶ K) (β : L' ⟶ L)
    [IsIso α] [IsIso β] (g : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj K).obj L ⟶ W)
    (γ : W ⟶ W') [IsIso γ]
    (hg : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor K L ≫
        DerivedCategory.Q.map g) Z))
    (ε : ℤˣ) (p : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj K').obj L' ⟶ V) (k : V ⟶ W')
    [IsIso k]
    (hq : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap α β
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          (ComplexShape.up ℤ)) ≫ DerivedCategory.Q.map g ≫ DerivedCategory.Q.map γ =
        ε • (DerivedCategory.Q.map p ≫ DerivedCategory.Q.map k))
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor K' L' ≫
        DerivedCategory.Q.map p) Z) := by
  have h1 := D.bijective_pairingPrecomp_toTensor_mapBifunctorMap_comp α β g γ hg Z
  have h2 := (congrArg (fun ψ => Function.Bijective
    ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor K' L' ≫ ψ) Z)) hq).mp h1
  exact (D.bijective_pairingPrecomp_comp_units_smul_comp_iff _ _ _ _ Z).1 h2

/-- Shifting the second variable and the target: perfectness of the degree-`(0, 0)` pairing gives
that of the degree-`(0, -m)` pairing. -/
theorem bijective_pairingPrecomp_singleSinglePairing_zero_sub
    (M N H : ModulesOn D.X.toRingedSpace)
    (φ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf).obj
      M).obj N ⟶ H)
    (h0 : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0)).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0)).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N (0) (0) φ)) Z))
    (m : ℤ)
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0)).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 - m)).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N (0) (0 - m) φ)) Z) := by
  let F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf
  have hc := CochainComplex.rightShift_singleSinglePairing F M N 0 0 m φ
  exact D.bijective_pairingPrecomp_toTensor_of_comp_eq_units_smul (𝟙 _)
    (((CochainComplex.singleFunctors _).shiftIso m (0 - m) 0 (by omega)).inv.app N)
    (D.rightShiftedPairingX (CochainComplex.singleSinglePairing F M N 0 0 φ) m)
    (((CochainComplex.singleFunctors _).shiftIso m (0 + 0 - m) (0 + 0) (by omega)).hom.app H)
    (D.bijective_pairingPrecomp_rightShiftedPairingX _ m h0) _ _ _
    (D.Q_map_comp_comp_eq_units_smul _ _ _ _ _ _
      ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans hc)) Z

/-- The shifted pairing of single complexes in the derived category. -/
theorem Q_map_shiftedPairing_singleSinglePairing
    (M N H : ModulesOn D.X.toRingedSpace)
    (φ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf).obj
      M).obj N ⟶ H) (k s : ℤ) :
    let F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf
    let Q := DerivedCategory.Q (C := ModulesOn D.X.toRingedSpace)
    Q.map (HomologicalComplex.mapBifunctorMap
        (((CochainComplex.singleFunctors _).shiftIso s (0 - s) 0 (by omega)).inv.app M)
        (((CochainComplex.singleFunctors _).shiftIso (-s) (k + s) k (by omega)).inv.app N)
        F (ComplexShape.up ℤ)) ≫
      Q.map ((tensorComplexBifunctorOn D.X.toRingedSpace).shiftedPairing
        (CochainComplex.singleSinglePairing F M N 0 k φ) s (-s) (by omega)) ≫ Q.map (𝟙 _) =
      ((0 - s) * (-s)).negOnePow • (Q.map (CochainComplex.singleSinglePairing F M N (0 - s)
        (k + s) φ) ≫ Q.map (eqToHom (congrArg (fun k => (HomologicalComplex.single _
          (ComplexShape.up ℤ) k).obj H) (by omega)))) := by
  intro F Q
  exact D.Q_map_comp_comp_eq_units_smul _ _ _ _ _ _
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans
      (CochainComplex.shiftedPairing_singleSinglePairing F M N 0 k s φ))

/-- Shifting the pairing by `(s, -s)`: perfectness in degrees `(0, k)` gives it in degrees
`(-s, k + s)`. -/
theorem bijective_pairingPrecomp_singleSinglePairing_shift
    (M N H : ModulesOn D.X.toRingedSpace)
    (φ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf).obj
      M).obj N ⟶ H)
    (k : ℤ) (hk : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0)).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (k)).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N (0) (k) φ)) Z))
    (s : ℤ)
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 - s)).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (k + s)).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N (0 - s) (k + s) φ)) Z) := by
  let F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf
  exact D.bijective_pairingPrecomp_toTensor_of_comp_eq_units_smul
    (((CochainComplex.singleFunctors _).shiftIso s (0 - s) 0 (by omega)).inv.app M)
    (((CochainComplex.singleFunctors _).shiftIso (-s) (k + s) k (by omega)).inv.app N)
    ((tensorComplexBifunctorOn D.X.toRingedSpace).shiftedPairing
      (CochainComplex.singleSinglePairing F M N 0 k φ) s (-s) (by omega)) (𝟙 _)
    (D.bijective_pairingPrecomp_shiftedPairing_toTensor _ s (-s) (by omega) hk) _ _ _
    (D.Q_map_shiftedPairing_singleSinglePairing M N H φ k s) Z

/-- Perfectness of the pairing in degrees `(a₀, b₀)` gives it in equal degrees `(a, b)`. -/
theorem bijective_pairingPrecomp_singleSinglePairing_congr
    (M N H : ModulesOn D.X.toRingedSpace)
    (φ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf).obj
      M).obj N ⟶ H)
    (a₀ b₀ a b : ℤ) (ha : a₀ = a) (hb : b₀ = b)
    (hB : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (a₀)).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (b₀)).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N (a₀) (b₀) φ)) Z))
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (a)).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) (b)).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N (a) (b) φ)) Z) := by
  let F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf
  let Q := DerivedCategory.Q (C := ModulesOn D.X.toRingedSpace)
  let tt := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
  have hcg := singleSinglePairing_congr F M N φ a₀ b₀ a b (by omega) (by omega)
  have h1 := D.bijective_pairingPrecomp_toTensor_mapBifunctorMap_comp
    (eqToHom (congrArg (fun k => (HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj M)
      (show a = a₀ by omega)))
    (eqToHom (congrArg (fun k => (HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj N)
      (show b = b₀ by omega)))
    (CochainComplex.singleSinglePairing F M N a₀ b₀ φ)
    (eqToHom (congrArg (fun k => (HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj H)
      (show a₀ + b₀ = a + b by omega))) hB Z
  have hq : Q.map (HomologicalComplex.mapBifunctorMap
        (eqToHom (congrArg (fun k => (HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj M)
          (show a = a₀ by omega)))
        (eqToHom (congrArg (fun k => (HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj N)
          (show b = b₀ by omega))) F (ComplexShape.up ℤ)) ≫
      Q.map (CochainComplex.singleSinglePairing F M N a₀ b₀ φ) ≫
      Q.map (eqToHom (congrArg (fun k => (HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj H)
        (show a₀ + b₀ = a + b by omega))) =
      Q.map (CochainComplex.singleSinglePairing F M N a b φ) :=
    ((congrArg (Q.map _ ≫ ·) (Q.map_comp _ _).symm).trans (Q.map_comp _ _).symm).trans
      (congrArg Q.map hcg.symm)
  exact (congrArg (fun ψ => Function.Bijective
    ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      (tt ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj M)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj N) ≫ ψ) Z)) hq).mp h1

/-- **A pairing of sheaves which is perfect in degree zero is perfect in all degrees**: if the
pairing `Q(M[0]) ⊗^L Q(N[0]) ⟶ Q(H[0])` induced by `φ : M ⊗ N ⟶ H` is perfect, so is
`Q(M[-a]) ⊗^L Q(N[-b]) ⟶ Q(H[-a-b])` for all `a`, `b`. -/
theorem bijective_pairingPrecomp_toTensor_singleSinglePairing
    (M N H : ModulesOn D.X.toRingedSpace)
    (φ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf).obj
      M).obj N ⟶ H)
    (h0 : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N 0 0 φ)) Z))
    (a b : ℤ)
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj M)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj N) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          M N a b φ)) Z) :=
  D.bijective_pairingPrecomp_singleSinglePairing_congr M N H φ (0 - -a)
    (0 - -(a + b) + -a) a b (by omega) (by omega)
    (D.bijective_pairingPrecomp_singleSinglePairing_shift M N H φ (0 - -(a + b))
      (D.bijective_pairingPrecomp_singleSinglePairing_zero_sub M N H φ h0 (-(a + b))) (-a)) Z

end AlgebraicGeometry.RelativeDualitySituation

end
