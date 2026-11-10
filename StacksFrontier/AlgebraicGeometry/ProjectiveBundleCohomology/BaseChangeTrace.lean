module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeTop
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeRows
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPullback

/-!
# The trace of Tag 01XX under base change

Let `b : 𝐏(E') ⟶ 𝐏(E)` be the morphism of projective bundles over `g : S' ⟶ S`, `E' ≅ g^*E`, both
of constant rank `n + 1`. The bottom of the Koszul filtration `π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ 𝒪_S`, the
trace `Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E ≅ 𝒪_S` and `Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨` correspond under the
base change maps to the same identifications for `E'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Sym

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent] (E' : S'.Modules)
  [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **`g^* Sym⁰(E) = Sym⁰(E')` is `g^* 𝒪_S = 𝒪_{S'}`** under `Sym⁰ ≅ 𝒪`. -/
public theorem symmetricSituationPullbackHom_zero_pieceZeroIso :
    (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 0 ≫
        (Stacks.SymGraded.pieceZeroIso E').hom =
      (pullbackFunctor g.toLRSHom.toShHom).map (Stacks.SymGraded.pieceZeroIso E).hom ≫
        (Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).hom := by
  refine Stacks.PullbackTensorCoherence.pullback_hom_ext g.toLRSHom.toShHom fun U x => ?_
  obtain ⟨c, hc⟩ := SheafOfModules.GradedAlgebra.exists_smul_one_of_isoUnit
    (Scheme.Modules.symmetricAlgebra S E) (Stacks.SymGraded.pieceZeroIso E)
    (Stacks.SymGraded.pieceZeroIso_hom_one E) U x
  subst hc
  have h1 := Stacks.RingedSpace.pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom
    (Stacks.RelativeProj.symmetricSituationOfQuasicoherent S E).algebra U.unop
  have h2 := (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).map_one
    (op ((opensMap g.toLRSHom.toShHom).obj U.unop))
  have h3 :=
    Stacks.SymGraded.pieceZeroIso_hom_one E' (op ((opensMap g.toLRSHom.toShHom).obj U.unop))
  have h4 := Stacks.SymGraded.pieceZeroIso_hom_one E U
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine Eq.trans ?_
    (congrArg ((Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).hom.val.app _)
    (pullbackUnit_naturality g.toLRSHom.toShHom _ U _)).symm
  refine Eq.trans ?_
    (Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit g.toLRSHom.toShHom U _).symm
  refine (congrArg (fun t => ((Stacks.SymGraded.pieceZeroIso E').hom.val.app _).hom
    ((((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 0).val.app _).hom t))
    (pullbackUnit_smul g.toLRSHom.toShHom _ U c _)).trans ?_
  refine (congrArg ((Stacks.SymGraded.pieceZeroIso E').hom.val.app _).hom
    ((((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 0).val.app _).hom.map_smul
      _ _)).trans ?_
  refine (((Stacks.SymGraded.pieceZeroIso E').hom.val.app _).hom.map_smul _ _).trans ?_
  refine (congrArg (fun t => @id (S'.ringCatSheaf.obj.obj ((opensMap g.toLRSHom.toShHom).op.obj U))
    (sharp g.toLRSHom.toShHom U c) • ((Stacks.SymGraded.pieceZeroIso E').hom.val.app _).hom
    ((((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 0).val.app _).hom t))
    h1.symm).trans ?_
  refine (congrArg (fun t => @id (S'.ringCatSheaf.obj.obj ((opensMap g.toLRSHom.toShHom).op.obj U))
    (sharp g.toLRSHom.toShHom U c) • ((Stacks.SymGraded.pieceZeroIso E').hom.val.app _).hom t)
    h2).trans ?_
  refine (congrArg (fun t => @id (S'.ringCatSheaf.obj.obj ((opensMap g.toLRSHom.toShHom).op.obj U))
    (sharp g.toLRSHom.toShHom U c) • t) h3).trans ?_
  refine Eq.trans ?_ (congrArg (sharp g.toLRSHom.toShHom U)
    (((Stacks.SymGraded.pieceZeroIso E).hom.val.app U).hom.map_smul c _)).symm
  refine Eq.trans ?_
    (congrArg (fun (t : S.ringCatSheaf.obj.obj U) => sharp g.toLRSHom.toShHom U (c • t)) h4).symm
  change sharp g.toLRSHom.toShHom U c * 1 =
    sharp g.toLRSHom.toShHom U (c * (1 : S.ringCatSheaf.obj.obj U))
  rw [mul_one, mul_one]

/-- The diagram chase behind `koszulBottomIso_baseChange`. -/
private theorem bottom_chase {C C' : Type*} [Category C] [Category C'] (F : C' ⥤ C)
    {P₀ P₁ P₂ P₃ P₄ U Q₂ Q₃ : C} {K M M' K' : C'}
    {top : P₀ ⟶ P₄} {a₁ : P₀ ⟶ P₁} {a₂ : P₁ ⟶ P₂} {a₃ : P₂ ⟶ P₃} {a₄ : P₃ ⟶ P₄}
    {u : P₄ ⟶ U} {s₀ : P₃ ⟶ Q₃} {p' : Q₃ ⟶ U} {tB : P₂ ⟶ Q₂} {z' : Q₂ ⟶ Q₃}
    {bcO : P₁ ⟶ F.obj M} {θ : M ⟶ M'} {r' : F.obj M' ⟶ Q₂} {bcK : P₀ ⟶ F.obj K}
    {kz : K ⟶ M} {kt : K ⟶ K'} {kz' : K' ⟶ M'} {bot' : F.obj K' ⟶ U}
    (hL : top = a₁ ≫ a₂ ≫ a₃ ≫ a₄) (hA : a₄ ≫ u = s₀ ≫ p')
    (hZ : tB ≫ z' = a₃ ≫ s₀) (hT : a₂ ≫ tB = bcO ≫ F.map θ ≫ r')
    (hN : a₁ ≫ bcO = bcK ≫ F.map kz) (hK : kz ≫ θ = kt ≫ kz')
    (hR : bot' = F.map kz' ≫ r' ≫ z' ≫ p') :
    top ≫ u = bcK ≫ F.map kt ≫ bot' := by
  have hK' : F.map kz ≫ F.map θ = F.map kt ≫ F.map kz' := by
    rw [← F.map_comp, ← F.map_comp, hK]
  subst hL hR
  simp only [Category.assoc]
  rw [hA, ← reassoc_of% hZ, reassoc_of% hT, reassoc_of% hN, reassoc_of% hK']

end Sym

section Bottom

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))
  {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1))

/-- The base change map in the indexing by injective resolutions, against the base change map
of `Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChange`. -/
public theorem higherBaseChangeNat_comp_rightDerivedIso {X X' T T' : Scheme.{u}} (f : X ⟶ T)
    (g₀ : T' ⟶ T) (f' : X' ⟶ T') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g₀) (q : ℕ) (F : X.Modules)
    {F' : X'.Modules} (θ : (Scheme.Modules.pullback g').obj F ⟶ F') :
    Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat f g₀ f' g' w q F ≫
        ((Scheme.Modules.pushforward f').rightDerived q).map θ ≫
        (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f') q).hom.app F' =
      (Scheme.Modules.pullback g₀).map
          ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).hom.app F) ≫
        Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChange f g₀ f' g' w q F ≫
        ((Scheme.Modules.pushforward f').rightDerivedPlus (q : ℤ)).map θ := by
  rw [(Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f') q).hom.naturality θ]
  unfold Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

include hfree hfree' in
/-- **The bottom of the Koszul filtration under base change**: `π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ 𝒪_S`
corresponds, under the base change map and `g^* 𝒪_S ≅ 𝒪_{S'}`, to the same isomorphism for
`E'`. -/
public theorem koszulBottomIso_baseChange :
    (pullbackFunctor g.toLRSHom.toShHom).map (koszulBottomIso E hqc D hn hfree).hom ≫
        (Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).hom =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) 0
          (koszulTerm E hqc D 0) ≫
        ((bundlePushforward E' hqc').rightDerived 0).map
          (koszulTermBaseChange g E hqc E' hqc' hE D D' 0).hom ≫
        (koszulBottomIso E' hqc' D' hn hfree').hom := by
  have hL : (Scheme.Modules.pullback g).map (koszulBottomIso E hqc D hn hfree).hom =
      (Scheme.Modules.pullback g).map (((bundlePushforward E hqc).rightDerived 0).map
          (koszulTermZeroIso E hqc D).hom) ≫
        (Scheme.Modules.pullback g).map ((Stacks.DerivedIndexing.rightDerivedIso
          (bundlePushforward E hqc) 0).hom.app _) ≫
        (Scheme.Modules.pullback g).map (zeroIso E hqc D (n := n) (by omega) hfree 0).hom ≫
        (Scheme.Modules.pullback g).map (Stacks.SymGraded.pieceZeroIso E).hom := by
    rw [show (koszulBottomIso E hqc D hn hfree).hom =
      ((bundlePushforward E hqc).rightDerived 0).map (koszulTermZeroIso E hqc D).hom ≫
        (Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqc) 0).hom.app _ ≫
        (zeroIso E hqc D (n := n) (by omega) hfree 0).hom ≫
        (Stacks.SymGraded.pieceZeroIso E).hom from rfl]
    exact ((Scheme.Modules.pullback g).map_comp _ _).trans (congrArg (_ ≫ ·)
      (((Scheme.Modules.pullback g).map_comp _ _).trans (congrArg (_ ≫ ·)
        ((Scheme.Modules.pullback g).map_comp _ _))))
  refine (congrArg (· ≫ _) (rfl : (pullbackFunctor g.toLRSHom.toShHom).map
    (koszulBottomIso E hqc D hn hfree).hom =
      (Scheme.Modules.pullback g).map (koszulBottomIso E hqc D hn hfree).hom)).trans ?_
  have hA : (Scheme.Modules.pullback g).map (Stacks.SymGraded.pieceZeroIso E).hom ≫
      (Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).hom =
      (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app ((0 : ℕ) : ℤ) ≫
        (Stacks.SymGraded.pieceZeroIso E').hom :=
    (symmetricSituationPullbackHom_zero_pieceZeroIso g E E' hE).symm
  have hZ := twistBaseChange_zeroIso g E hqc E' hqc' hE D D' (by omega) hfree hfree' 0
  have hT : (Scheme.Modules.pullback g).map ((Stacks.DerivedIndexing.rightDerivedIso
        (bundlePushforward E hqc) 0).hom.app (D.algebra.piece ((0 : ℕ) : ℤ))) ≫
      twistBaseChange g E hqc E' hqc' hE D D' 0 ((0 : ℕ) : ℤ) =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) 0
          (D.algebra.piece ((0 : ℕ) : ℤ)) ≫
        ((bundlePushforward E' hqc').rightDerived 0).map
          (thetaSharp g E hqc E' hqc' hE D D' ((0 : ℕ) : ℤ)) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E' hqc') 0).hom.app
          (D'.algebra.piece ((0 : ℕ) : ℤ)) :=
    (higherBaseChangeNat_comp_rightDerivedIso _ _ _ _ _ 0 _ _).symm
  have hN := Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat_naturality
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) 0
    (koszulTermZeroIso E hqc D).hom
  have hK := koszulTermZeroIso_pullback_of (bundleBaseChange g E hqc E' hqc' hE)
    (fun d => asIso (thetaSharp g E hqc E' hqc' hE D D' d))
    (tautKernelBaseChange g E hqc E' hqc' hE D D')
  exact bottom_chase ((bundlePushforward E' hqc').rightDerived 0) hL hA hZ hT hN hK rfl

/-- The diagram chase behind `topTraceIso_baseChange`. -/
private theorem trace_chase {C : Type*} [Category C] {A₀ A₁ B₀ B₁ B₂ U Q₁ Q : C}
    {gTi : A₀ ⟶ A₁} {gT : A₁ ⟶ A₀} {gB : A₁ ⟶ B₀} {u : B₀ ⟶ U} {b₁ : A₁ ⟶ Q₁} {b₂ : Q₁ ⟶ Q}
    {B' : Q ⟶ U} {T' : Q ⟶ B₂} {Ti' : B₂ ⟶ Q} {c : A₀ ⟶ B₁} {tm : B₁ ⟶ B₂}
    (hT : gT ≫ c ≫ tm = b₁ ≫ b₂ ≫ T') (hB : gB ≫ u = b₁ ≫ b₂ ≫ B') (hI : gTi ≫ gT = 𝟙 _)
    (hT' : T' ≫ Ti' = 𝟙 _) : gTi ≫ gB ≫ u = c ≫ tm ≫ Ti' ≫ B' := by
  symm
  rw [← Category.id_comp (c ≫ tm ≫ Ti' ≫ B'), ← hI]
  simp only [Category.assoc]
  rw [reassoc_of% hT, reassoc_of% hT', hB]

include hfree hfree' in
/-- **The trace of the Koszul filtration under base change**: `Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E ≅ 𝒪_S`
corresponds, under the base change map, `g^* ⋀ⁿ⁺¹ E ≅ ⋀ⁿ⁺¹ E'` and `g^* 𝒪_S ≅ 𝒪_{S'}`, to the
same isomorphism for `E'`. -/
public theorem topTraceIso_baseChange :
    (pullbackFunctor g.toLRSHom.toShHom).map (topTraceIso E hqc D hn hfree).hom ≫
        (Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).hom =
      Stacks.RingedSpace.comparison g.toLRSHom.toShHom
          (((bundlePushforward E hqc).rightDerived n).obj (negTwist E hqc D (n + 1)))
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) ≫
        tensorMap (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) n
          (negTwist E hqc D (n + 1)) ≫
            ((bundlePushforward E' hqc').rightDerived n).map
              (thetaSharp g E hqc E' hqc' hE D D' (-((n + 1 : ℕ) : ℤ))))
          (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ)).hom ≫
        (topTraceIso E' hqc' D' hn hfree').hom := by
  have hT := (congrArg (· ≫ _) (rfl : (pullbackFunctor g.toLRSHom.toShHom).map
    (koszulTopIso E hqc D hn hfree).hom =
      (Scheme.Modules.pullback g).map (koszulTopIso E hqc D hn hfree).hom)).trans
    (koszulTopIso_baseChange g E hqc E' hqc' hE D D' hfree hfree' hn)
  have hB := koszulBottomIso_baseChange g E hqc E' hqc' hE D D' hn hfree hfree'
  have hI : (pullbackFunctor g.toLRSHom.toShHom).map (koszulTopIso E hqc D hn hfree).inv ≫
      (pullbackFunctor g.toLRSHom.toShHom).map (koszulTopIso E hqc D hn hfree).hom = 𝟙 _ :=
    ((pullbackFunctor g.toLRSHom.toShHom).map_comp _ _).symm.trans
      ((congrArg (pullbackFunctor g.toLRSHom.toShHom).map (Iso.inv_hom_id _)).trans
        ((pullbackFunctor g.toLRSHom.toShHom).map_id _))
  rw [show (topTraceIso E hqc D hn hfree).hom = (koszulTopIso E hqc D hn hfree).inv ≫
    (koszulBottomIso E hqc D hn hfree).hom from rfl]
  refine (congrArg (· ≫ _) (((pullbackFunctor g.toLRSHom.toShHom).map_comp
    (koszulTopIso E hqc D hn hfree).inv (koszulBottomIso E hqc D hn hfree).hom))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact trace_chase hT hB hI (Iso.hom_inv_id _)

include hfree hfree' in
/-- **`Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨` under base change**: the base change map
`g^* Rⁿ π_* 𝒪(-n-1) ⟶ Rⁿ π'_* 𝒪(-n-1)` corresponds to `g^*((⋀ⁿ⁺¹ E)^∨) ≅ (⋀ⁿ⁺¹ E')^∨`, the dual
base-change map along `g^* ⋀ⁿ⁺¹ E ≅ ⋀ⁿ⁺¹ E'`. -/
public theorem topTwistIsoDualDet_baseChange :
    haveI := isFiniteLocallyFree_of_rank E hfree
    haveI := isFiniteLocallyFree_of_rank E' hfree'
    haveI := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E (n + 1)
    haveI :=
      AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E' (n + 1)
    (Scheme.Modules.pullback g).map (topTwistIsoDualDet E hqc D hn hfree).hom ≫
        (pullbackDualIsoOf g (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))
          (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ)) inferInstance).hom =
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) n
          (negTwist E hqc D (n + 1)) ≫
        ((bundlePushforward E' hqc').rightDerived n).map
          (thetaSharp g E hqc E' hqc' hE D D' (-((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E' hqc' D' hn hfree').hom := by
  have := isFiniteLocallyFree_of_rank E hfree
  have := isFiniteLocallyFree_of_rank E' hfree'
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E (n + 1)
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E' (n + 1)
  have := isInvertible_det E hfree
  have := isInvertible_det E' hfree'
  have e : tensorMap (topTwistIsoDualDet E hqc D hn hfree).hom
      (𝟙 (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))) ≫
      dualEvaluation (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) =
      (topTraceIso E hqc D hn hfree).hom :=
    isoDualSheaf_of_tensor_iso_unit_evaluation _ _ _
  have e' : tensorMap (topTwistIsoDualDet E' hqc' D' hn hfree').hom
      (𝟙 (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))) ≫
      dualEvaluation (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ)) =
      (topTraceIso E' hqc' D' hn hfree').hom :=
    isoDualSheaf_of_tensor_iso_unit_evaluation _ _ _
  refine pullbackDualIsoOf_curry g _ _ _ _ ?_
  refine (congrArg (fun t => (pullbackFunctor g.toLRSHom.toShHom).map t ≫
    (Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom).hom) e).trans ?_
  refine (topTraceIso_baseChange g E hqc E' hqc' hE D D' hn hfree hfree').trans ?_
  exact congrArg (fun t => _ ≫ _ ≫ t) e'.symm

end Bottom

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
