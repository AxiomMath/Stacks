module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoRows
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of Tag 01XX under an isomorphism of modules

Let `e : E ≅ E'` be an isomorphism of finite locally free `𝒪_S`-modules of constant rank `n + 1`
and `f : 𝐏(E') ⟶ 𝐏(E)` the induced isomorphism of projective bundles over `S`. The bottom of the
Koszul filtration `π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ 𝒪_S` and the trace `Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨`
correspond under `f` and `e`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section ExteriorZero

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {K : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {K' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier)
    (Osharp := Y.sheaf) K)
  (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) K')
  (l : (pullbackFunctor f).obj K ≅ K')

/-- **`⋀⁰ ≅ 𝒪` under pullback**: the identification of the degree-zero exterior power with the
structure sheaf commutes with `f^*(⋀⁰ K) ≅ ⋀⁰ K'` and `f^* 𝒪_Y ≅ 𝒪_X`. -/
public theorem exteriorPieceZeroIsoUnit_pullback :
    (pullbackFunctor f).map A.exteriorPieceZeroIsoUnit.hom ≫
        (Stacks.PullbackAlgebra.pullbackUnitIso f).hom =
      (extPullbackIso f A A' l 0).hom ≫ A'.exteriorPieceZeroIsoUnit.hom := by
  refine Stacks.PullbackTensorCoherence.pullback_hom_ext f fun U x => ?_
  obtain ⟨r, hr⟩ := A.exists_exterior_eq_smul_one U x
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine (congrArg ((Stacks.PullbackAlgebra.pullbackUnitIso f).hom.val.app _)
    (pullbackUnit_naturality f _ U x)).trans ?_
  refine (Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit f U _).trans ?_
  subst hr
  rw [map_smul, A.exteriorPieceZeroIsoUnit_one, pullbackUnit_smul, map_smul, map_smul,
    extPullbackIso_one, A'.exteriorPieceZeroIsoUnit_one]
  exact (congrArg (sharp f U) (mul_one r)).trans (mul_one _).symm

end ExteriorZero

section LeftUnitor

variable {X X' : Scheme.{u}} (f : X' ⟶ X) {M : X.Modules} {M' : X'.Modules}
  (θ : (Scheme.Modules.pullback f).obj M ≅ M')

/-- **The left unit constraint under pullback**: `f^*(𝒪_X ⊗ M ≅ M)` is `𝒪_{X'} ⊗ M' ≅ M'` under
`f^* 𝒪_X ≅ 𝒪_{X'}` and `θ : f^* M ≅ M'`. -/
public theorem tensorSheafLeftUnitor_pullback :
    (Scheme.Modules.pullback f).map (Stacks.SheafOfModules.tensorSheafLeftUnitor X.sheaf.obj
        (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf).property M).hom ≫
        θ.hom =
      (tensorPullbackIso f.toLRSHom.toShHom
          (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom) θ).hom ≫
        (Stacks.SheafOfModules.tensorSheafLeftUnitor X'.sheaf.obj
          (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X') X'.sheaf).property
          M').hom := by
  refine pullback_tensorSheaf_hom_ext f.toLRSHom.toShHom
    (A := _root_.SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) (B := M)
    fun U r m => ?_
  have h1 := Stacks.SheafOfModules.tensorSheafLeftUnitor_hom_val_app_tmul X.sheaf.obj
    (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf).property M U r m
  have h2 := Stacks.SheafOfModules.tensorSheafLeftUnitor_hom_val_app_tmul X'.sheaf.obj
    (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X') X'.sheaf).property M'
    ((opensMap f.toLRSHom.toShHom).op.obj U)
    ((Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom).hom.val.app _
      (pullbackUnit f.toLRSHom.toShHom _ U r))
    (θ.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom _ U m))
  have h3 := tensorPullbackIso_unit f.toLRSHom.toShHom
    (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom) θ U r m
  have h4 := pullbackUnit_naturality f.toLRSHom.toShHom (Stacks.SheafOfModules.tensorSheafLeftUnitor
    X.sheaf.obj (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf).property
      M).hom U ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf)
        (_root_.SheafOfModules.unit (structureRingSheaf X.toRingedSpace)) M).app U (r ⊗ₜ m))
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine (congrArg (θ.hom.val.app _) (h4.trans (congrArg (pullbackUnit f.toLRSHom.toShHom M U)
    h1))).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (Stacks.SheafOfModules.tensorSheafLeftUnitor X'.sheaf.obj
    (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X') X'.sheaf).property
      M').hom.val.app _ z) h3).symm
  refine Eq.trans ?_ h2.symm
  refine (congrArg (θ.hom.val.app _) (pullbackUnit_smul f.toLRSHom.toShHom M U r m)).trans ?_
  refine ((θ.hom.val.app _).hom.map_smul _ _).trans ?_
  exact congrArg (· • _)
    (Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit f.toLRSHom.toShHom U r).symm

end LeftUnitor

section Koszul

variable {S S' : Scheme.{u}} {E : S.Modules} {E' : S'.Modules} [E.IsQuasicoherent]
  [E'.IsQuasicoherent]
  {hqc : Stacks.SymGraded.IsQuasicoherentPieces E}
  {hqc' : Stacks.SymGraded.IsQuasicoherentPieces E'}
  {D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)}
  {D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')}
  (f : bundle E' hqc' ⟶ bundle E hqc)
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback f).obj (D.algebra.piece d) ≅ D'.algebra.piece d)
  (κ : (Scheme.Modules.pullback f).obj (tautologicalKernel E hqc D) ≅
    tautologicalKernel E' hqc' D')

/-- **The bottom of the Koszul filtration under pullback**: `⋀⁰ K ⊗ 𝒪(0) ≅ 𝒪(0)` corresponds to
the same isomorphism for `E'`, for any identification `κ` of the kernels. -/
public theorem koszulTermZeroIso_pullback_of :
    (Scheme.Modules.pullback f).map (koszulTermZeroIso E hqc D).hom ≫
        (θ ((0 : ℕ) : ℤ)).hom =
      (koszulTermIsoOf f θ κ 0).hom ≫ (koszulTermZeroIso E' hqc' D').hom := by
  have hL := tensorSheafLeftUnitor_pullback f (θ ((0 : ℕ) : ℤ))
  have hE := exteriorPieceZeroIsoUnit_pullback f.toLRSHom.toShHom (kernelAlgebras E hqc D)
    (kernelAlgebras E' hqc' D') κ
  have hT := twist_eqToHom_pullback f θ (show -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by simp)
  have hN := tensorPullbackIso_naturality₂ f.toLRSHom.toShHom (kerExtIsoOf f κ 0)
    (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom) (θ (-((0 : ℕ) : ℤ)))
    (θ ((0 : ℕ) : ℤ)) _ _ _ _ hE hT
  refine (((Scheme.Modules.pullback f).map_comp _ _) =≫ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hL).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hN).trans ?_
  exact Category.assoc _ _ _

end Koszul

section KoszulIso

variable {S : Scheme.{u}} {E E' : S.Modules} [E.IsQuasicoherent] [E'.IsQuasicoherent]
  {hqc : Stacks.SymGraded.IsQuasicoherentPieces E}
  {hqc' : Stacks.SymGraded.IsQuasicoherentPieces E'}
  {D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)}
  {D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')}
  (f : bundle E' hqc' ⟶ bundle E hqc) [IsIso f]
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback f).obj (D.algebra.piece d) ≅ D'.algebra.piece d)
  (hbase : f ≫ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase =
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase)
  (e : E ≅ E')
  (hu : (Scheme.Modules.pullback f).map (tautologicalMap E hqc D) ≫ (θ ((1 : ℕ) : ℤ)).hom =
    (bundlePullbackIso f hbase e).hom ≫ tautologicalMap E' hqc' D')

/-- **The bottom of the Koszul filtration under pullback**, for the kernel identification of an
isomorphism of projective bundles. -/
public theorem koszulTermZeroIso_pullback :
    (Scheme.Modules.pullback f).map (koszulTermZeroIso E hqc D).hom ≫
        (θ ((0 : ℕ) : ℤ)).hom =
      (koszulTermIso f θ (bundlePullbackIso f hbase e) hu 0).hom ≫
        (koszulTermZeroIso E' hqc' D').hom :=
  koszulTermZeroIso_pullback_of f θ _

end KoszulIso

section Sym

variable {S : Scheme.{u}} {E E' : S.Modules} {r : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E r)
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' r)

/-- **`Sym⁰(φ)` is the identity of `𝒪_S`** under `Sym⁰ ≅ 𝒪_S`. -/
public theorem symHom_app_zero_pieceZeroIso (φ : E ⟶ E') :
    (symHom hfree hfree' φ).app 0 ≫ (Stacks.SymGraded.pieceZeroIso E').hom =
      (Stacks.SymGraded.pieceZeroIso E).hom := by
  apply _root_.SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨c, hc⟩ := SheafOfModules.GradedAlgebra.exists_smul_one_of_isoUnit
    (Scheme.Modules.symmetricAlgebra S E) (Stacks.SymGraded.pieceZeroIso E)
    (Stacks.SymGraded.pieceZeroIso_hom_one E) U x
  subst hc
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (congrArg ((Stacks.SymGraded.pieceZeroIso E').hom.val.app U).hom
    ((((symHom hfree hfree' φ).app 0).val.app U).hom.map_smul _ _)).trans ?_
  refine (((Stacks.SymGraded.pieceZeroIso E').hom.val.app U).hom.map_smul _ _).trans ?_
  refine Eq.trans ?_ (((Stacks.SymGraded.pieceZeroIso E).hom.val.app U).hom.map_smul _ _).symm
  exact congrArg (c • ·) ((congrArg ((Stacks.SymGraded.pieceZeroIso E').hom.val.app U)
    ((Scheme.Modules.symmetricAlgebraUnitalHom S φ).map_one U)).trans
    ((Stacks.SymGraded.pieceZeroIso_hom_one E' U).trans
      (Stacks.SymGraded.pieceZeroIso_hom_one E U).symm))

end Sym

/-- The diagram chase behind `koszulBottomIso_iso`. -/
private theorem bottom_chase {C : Type*} [Category C] {A₀ A₁ Ap B B₁ B₂ Cc Cp Z Z' O : C}
    {Φ : A₀ ⟶ B} {k : B ⟶ B₁} {t' : B₁ ⟶ Cc} {r' : Cc ⟶ Cp} {z' : Cp ⟶ Z'} {p' : Z' ⟶ O}
    {t : A₀ ⟶ A₁} {φ₀ : A₁ ⟶ B₂} {m : B ⟶ B₂} {θr : B₂ ⟶ Cc} {r : A₁ ⟶ Ap} {H : Ap ⟶ Cp}
    {z : Ap ⟶ Z} {s : Z ⟶ Z'} {p : Z ⟶ O}
    (e₁ : k ≫ t' = m ≫ θr) (e₂ : t ≫ φ₀ = Φ ≫ m) (e₃ : r ≫ H = φ₀ ≫ θr ≫ r')
    (e₄ : H ≫ z' = z ≫ s) (e₅ : s ≫ p' = p) :
    Φ ≫ k ≫ t' ≫ r' ≫ z' ≫ p' = t ≫ r ≫ z ≫ p := by
  rw [reassoc_of% e₁, ← reassoc_of% e₂, ← reassoc_of% e₃, reassoc_of% e₄, e₅]

/-- A functor sends equal composites to equal composites. -/
private theorem map_comp_congr {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' Cc : C} {f : A ⟶ B} {g : B ⟶ Cc} {f' : A ⟶ B'} {g' : B' ⟶ Cc}
    (h : f ≫ g = f' ≫ g') : F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, h, F.map_comp]

/-- Tensor products of morphisms with equal composites in each factor have equal composites. -/
private theorem tensorMap_comp_congr {Z : RingedSpace.{u, u}}
    {A A₁ A₂ A' B B₁ B₂ B' : _root_.SheafOfModules.{u} (structureRingSheaf Z)}
    {a : A ⟶ A₁} {a' : A₁ ⟶ A'} {c : A ⟶ A₂} {c' : A₂ ⟶ A'}
    {b : B ⟶ B₁} {b' : B₁ ⟶ B'} {d : B ⟶ B₂} {d' : B₂ ⟶ B'}
    (ha : a ≫ a' = c ≫ c') (hb : b ≫ b' = d ≫ d') :
    tensorMap a b ≫ tensorMap a' b' = tensorMap c d ≫ tensorMap c' d' := by
  rw [tensorMap_comp, tensorMap_comp, ha, hb]

section Dual

variable {X : Scheme.{u}}

/-- The evaluation pairing `N^∨ ⊗ N ⟶ 𝒪_X` of a module on a scheme, with `N^∨` the dual of
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`. -/
@[sga "5 IIIB 5.0" "special case"]
public noncomputable abbrev dualEvaluation (N : X.Modules) :
    (Stacks.ProjectionFormula.tensorRightInvertible X N).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.2 N

/-- `dualEvaluation` on a local pure tensor. -/
public theorem dualEvaluation_tensorSheafUnit (N : X.Modules) (U : X.Opensᵒᵖ)
    (φ : (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N).val.obj U) (x : N.val.obj U) :
    (dualEvaluation N).val.app U
        ((PresheafOfModules.tensorSheafUnit (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)
          N).app U (φ ⊗ₜ x)) = (φ.app (op (Over.mk (𝟙 U.unop)))).hom x :=
  Stacks.SheafOfModules.evaluation_tensorPt X.presheaf X.ringCatSheaf.2 N U φ x

/-- **The evaluation pairing is dinatural**: for `u : N' ⟶ N`, pairing `u^∨ φ` with a section
`x` of `N'` is pairing `φ` with `u x`. -/
public theorem dualEvaluation_dualMap {N N' : X.Modules} (u : N' ⟶ N) :
    tensorMap (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u) (𝟙 N') ≫ dualEvaluation N' =
      tensorMap (𝟙 (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)) u ≫
        dualEvaluation N := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf) fun U φ x => ?_
  have h1 : (tensorMap (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u) (𝟙 N')).val.app U
      ((PresheafOfModules.tensorSheafUnit (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)
        N').app U (φ ⊗ₜ x)) =
      (PresheafOfModules.tensorSheafUnit (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N')
        N').app U ((Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u).val.app U φ ⊗ₜ x) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X) (Osharp := X.sheaf)
      (f := Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u) (g := 𝟙 N') (V := U) (x := φ)
      (y := x)
  have h2 : (tensorMap (𝟙 (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)) u).val.app U
      ((PresheafOfModules.tensorSheafUnit (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)
        N').app U (φ ⊗ₜ x)) =
      (PresheafOfModules.tensorSheafUnit (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)
        N).app U (φ ⊗ₜ u.val.app U x) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X) (Osharp := X.sheaf)
      (f := 𝟙 (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)) (g := u) (V := U) (x := φ)
      (y := x)
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine ((congrArg (fun z => (dualEvaluation N').val.app U z) h1).trans
    (dualEvaluation_tensorSheafUnit N' U _ x)).trans ?_
  exact ((congrArg (fun z => (dualEvaluation N).val.app U z) h2).trans
    (dualEvaluation_tensorSheafUnit N U φ _)).symm

/-- `isoDualSheaf_of_tensor_iso_unit` is characterized by the evaluation pairing. -/
public theorem isoDualSheaf_of_tensor_iso_unit_evaluation (N R : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (t : (Stacks.ProjectionFormula.tensorRightInvertible X N).obj R ≅ SheafOfModules.unit _) :
    (Stacks.ProjectionFormula.tensorRightInvertible X N).map
        (isoDualSheaf_of_tensor_iso_unit N R t).hom ≫ dualEvaluation N = t.hom := by
  have hI : IsIso (dualEvaluation N) :=
    Stacks.SheafOfModules.Invertible.isIso_evaluation X.presheaf X.ringCatSheaf.2 N
  exact (congrArg (· ≫ dualEvaluation N) ((Stacks.ProjectionFormula.tensorRightInvertible X
    N).map_preimage _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (t.hom ≫ ·) (@asIso _ _ _ _ _ hI).inv_hom_id).trans (Category.comp_id _)))

/-- **`isoDualSheaf_of_tensor_iso_unit` is natural**: for `a : N ≅ N'` and `b : R ⟶ R'`
compatible with the trivializations `R ⊗ N ≅ 𝒪` and `R' ⊗ N' ≅ 𝒪`, the identifications
`R ≅ N^∨` and `R' ≅ N'^∨` correspond under `b` and the dual of `a⁻¹`. -/
public theorem isoDualSheaf_of_tensor_iso_unit_naturality {N N' R R' : X.Modules}
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N']
    (a : N ≅ N') (b : R ⟶ R')
    (t : (Stacks.ProjectionFormula.tensorRightInvertible X N).obj R ≅ SheafOfModules.unit _)
    (t' : (Stacks.ProjectionFormula.tensorRightInvertible X N').obj R' ≅ SheafOfModules.unit _)
    (h : tensorMap b a.hom ≫ t'.hom = t.hom) :
    (isoDualSheaf_of_tensor_iso_unit N R t).hom ≫
        Stacks.AlgebraicGeometry.ReflexiveModules.dualMap a.inv =
      b ≫ (isoDualSheaf_of_tensor_iso_unit N' R' t').hom := by
  have hI : IsIso (dualEvaluation N') :=
    Stacks.SheafOfModules.Invertible.isIso_evaluation X.presheaf X.ringCatSheaf.2 N'
  apply (Stacks.ProjectionFormula.tensorRightInvertible X N').map_injective
  refine (Iso.cancel_iso_hom_right _ _ (@asIso _ _ _ _ (dualEvaluation N') hI)).mp ?_
  have hP := isoDualSheaf_of_tensor_iso_unit_evaluation N R t
  have hP' := isoDualSheaf_of_tensor_iso_unit_evaluation N' R' t'
  have hD := dualEvaluation_dualMap a.inv
  have hX : tensorMap (isoDualSheaf_of_tensor_iso_unit N R t).hom (𝟙 N') ≫
        tensorMap (𝟙 (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)) a.inv =
      tensorMap (𝟙 R) a.inv ≫ tensorMap (isoDualSheaf_of_tensor_iso_unit N R t).hom (𝟙 N) :=
    tensorMap_comp_congr ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hY : tensorMap (𝟙 R) a.inv ≫ tensorMap b a.hom = tensorMap b (𝟙 N') :=
    (tensorMap_comp (Z := X.toRingedSpace) _ _ _ _).trans
      (congrArg₂ (fun x y => tensorMap (Z := X.toRingedSpace) x y) (Category.id_comp b)
        a.inv_hom_id)
  refine (congrArg (· ≫ _)
    ((Stacks.ProjectionFormula.tensorRightInvertible X N').map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hD).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ dualEvaluation N) hX).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hP).trans ?_
  refine (congrArg (_ ≫ ·) h.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ t'.hom) hY).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _)
    ((Stacks.ProjectionFormula.tensorRightInvertible X N').map_comp _ _)).symm
  exact (congrArg (_ ≫ ·) hP'.symm).trans (Category.assoc _ _ _).symm

/-- The rank-one morphism `L ⊗ A^∨ ⟶ SheafHom(A, L)` of a module on a scheme. -/
public noncomputable abbrev tensorDualMap (A L : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A) ⟶
      Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace A L :=
  Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) A L

/-- `tensorDualMap` on a local pure tensor is the rank-one morphism. -/
public theorem tensorDualMap_tensorSheafUnit (A L : X.Modules) (U : X.Opensᵒᵖ)
    (f : L.val.obj U) (lam : (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A).val.obj U) :
    (tensorDualMap A L).val.app U
        ((PresheafOfModules.tensorSheafUnit L
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A)).app U (f ⊗ₜ lam)) =
      Stacks.SheafOfModules.rankOneHomSection X.sheaf.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) (U := U.unop) f lam :=
  Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) A L U f lam

/-- **The rank-one morphism is natural**: `L ⊗ A^∨ ⟶ SheafHom(A, L)` commutes with `v : L ⟶ L'`
and `u : A' ⟶ A`. -/
public theorem tensorDualMap_naturality {A A' L L' : X.Modules} (u : A' ⟶ A) (v : L ⟶ L') :
    tensorMap v (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u) ≫ tensorDualMap A' L' =
      tensorDualMap A L ≫ Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace u ≫
        Stacks.SheafOfModules.sheafHomMapRight X.toRingedSpace v := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf) fun U f lam => ?_
  have h1 : (tensorMap v (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u)).val.app U
      ((PresheafOfModules.tensorSheafUnit L
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A)).app U (f ⊗ₜ lam)) =
      (PresheafOfModules.tensorSheafUnit L'
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A')).app U
          (v.val.app U f ⊗ₜ (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u).val.app U lam) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X) (Osharp := X.sheaf)
      (f := v) (g := Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u) (V := U) (x := f)
      (y := lam)
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine ((congrArg (fun z => (tensorDualMap A' L').val.app U z) h1).trans
    (tensorDualMap_tensorSheafUnit A' L' U _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace u ≫
    Stacks.SheafOfModules.sheafHomMapRight X.toRingedSpace v).val.app U z)
      (tensorDualMap_tensorSheafUnit A L U f lam)).symm
  refine Stacks.SheafOfModules.internalHom_ext X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) _ _ fun V g => ?_
  have ha := Stacks.SheafOfModules.rankOneHomSection_app X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) ((v.val.app U).hom f)
    ((Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u).val.app U lam) V g
  have hb := congrArg (v.val.app (op V.unop.left)).hom
    (Stacks.SheafOfModules.rankOneHomSection_app X.sheaf.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) f lam V
      (u.val.app (op V.unop.left) g))
  have hd : (v.val.app (op V.unop.left)).hom (Stacks.SheafOfModules.resSection V f) =
      Stacks.SheafOfModules.resSection V ((v.val.app U).hom f) :=
    PresheafOfModules.naturality_apply v.val V.unop.hom.op f
  rw [← hd] at ha
  exact ha.trans (hb.trans ((v.val.app (op V.unop.left)).hom.map_smul _ _)).symm

/-- `SheafHom(A, L) ≅ L ⊗ A^∨` is the inverse of the rank-one morphism. -/
public theorem sheafHomIsoTensorDual_inv (A L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] :
    (sheafHomIsoTensorDual A L).inv = tensorDualMap A L := rfl

/-- **`SheafHom(A, L) ≅ L ⊗ A^∨` is natural** in `L` and in `A`. -/
public theorem sheafHomIsoTensorDual_naturality {A A' L L' : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A'] (u : A' ⟶ A)
    (v : L ⟶ L') :
    (sheafHomIsoTensorDual A L).hom ≫
        tensorMap (Z := X.toRingedSpace) (A := L) (A' := L')
          (B := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A)
          (B' := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A') v
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u) =
      (Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace u ≫
        Stacks.SheafOfModules.sheafHomMapRight X.toRingedSpace v) ≫
        (sheafHomIsoTensorDual A' L').hom :=
  iso_square_inv (sheafHomIsoTensorDual A L).symm (sheafHomIsoTensorDual A' L').symm _ _
    (tensorDualMap_naturality u v).symm

/-- The dual of a morphism is precomposition in the sheaf-hom into the structure sheaf. -/
public theorem dualMap_eq_sheafHomMapLeft {F G : X.Modules} (u : F ⟶ G) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap u =
      Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace
        (B := SheafOfModules.unit (_root_.structureSheaf X.sheaf)) u := rfl

/-- Precomposition in the sheaf-hom is contravariantly functorial. -/
public theorem sheafHomMapLeft_comp {A A' A'' B : X.Modules} (f : A ⟶ A') (g : A' ⟶ A'') :
    Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace (B := B) g ≫
        Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace f =
      Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace (f ≫ g) :=
  _root_.SheafOfModules.hom_ext (Stacks.PresheafOfModules.InternalHom.internalHomMapLeft_comp
    X.presheaf f.val g.val)

/-- The diagram chase behind `dualTensorIso_naturality`. -/
private theorem dnat_chase {C : Type*} [Category C] {P P₁ P₂ Q Q₁ Q₂ R R' : C}
    {i : P ⟶ Q} {s : Q ⟶ R} {T : R ⟶ R'} {l : Q ⟶ Q₁} {r : Q₁ ⟶ Q₂} {s' : Q₂ ⟶ R'}
    {m₁ : P ⟶ P₁} {i₁ : P₁ ⟶ Q₁} {m₂ : P₁ ⟶ P₂} {i' : P₂ ⟶ Q₂} {D : P ⟶ P₂}
    (h1 : s ≫ T = (l ≫ r) ≫ s') (h2 : i ≫ l = m₁ ≫ i₁) (h3 : i₁ ≫ r = m₂ ≫ i')
    (h5 : m₁ ≫ m₂ = D) :
    (i ≫ s) ≫ T = D ≫ i' ≫ s' := by
  rw [Category.assoc, h1, Category.assoc, reassoc_of% h2, reassoc_of% h3, ← h5, Category.assoc]

/-- `dualTensorIso_naturality`, with the duals written as sheaf-homs into the structure sheaf. -/
public theorem dualTensorIso_naturality_aux {G G' N N' : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] (a : G ≅ G')
    (b : N ≅ N') :
    ((Stacks.SheafOfModules.internalHomTensorIso X.toRingedSpace G N
        (SheafOfModules.unit (_root_.structureSheaf X.sheaf))).hom ≫
      (sheafHomIsoTensorDual G (Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace N
        (SheafOfModules.unit (_root_.structureSheaf X.sheaf)))).hom) ≫
        tensorMap (Z := X.toRingedSpace)
          (A := Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace N
            (SheafOfModules.unit (_root_.structureSheaf X.sheaf)))
          (A' := Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace N'
            (SheafOfModules.unit (_root_.structureSheaf X.sheaf)))
          (B := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf G)
          (B' := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf G')
          (Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace
            (B := SheafOfModules.unit (_root_.structureSheaf X.sheaf)) b.inv)
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap a.inv) =
      Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace
          (B := SheafOfModules.unit (_root_.structureSheaf X.sheaf))
          (tensorMap (Z := X.toRingedSpace) a.inv b.inv) ≫
        (Stacks.SheafOfModules.internalHomTensorIso X.toRingedSpace G' N'
          (SheafOfModules.unit (_root_.structureSheaf X.sheaf))).hom ≫
        (sheafHomIsoTensorDual G' (Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace N'
          (SheafOfModules.unit (_root_.structureSheaf X.sheaf)))).hom := by
  have h1 := sheafHomIsoTensorDual_naturality
    (L := Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace N
      (SheafOfModules.unit (_root_.structureSheaf X.sheaf)))
    (L' := Stacks.SheafOfModules.sheafHomSpace X.toRingedSpace N'
      (SheafOfModules.unit (_root_.structureSheaf X.sheaf))) a.inv
    (Stacks.SheafOfModules.sheafHomMapLeft X.toRingedSpace
      (B := SheafOfModules.unit (_root_.structureSheaf X.sheaf)) b.inv)
  have h2 := Stacks.SheafOfModules.internalHomTensorIso_natural_left X.toRingedSpace
    (G := N) (H := SheafOfModules.unit (_root_.structureSheaf X.sheaf)) a.inv
  have h3 := Stacks.SheafOfModules.internalHomTensorIso_natural_middle X.toRingedSpace
    (F := G') (H := SheafOfModules.unit (_root_.structureSheaf X.sheaf)) b.inv
  have h5 := (sheafHomMapLeft_comp (B := SheafOfModules.unit (_root_.structureSheaf X.sheaf))
    (tensorMap (Z := X.toRingedSpace) (𝟙 G') b.inv)
    (tensorMap (Z := X.toRingedSpace) a.inv (𝟙 N))).trans
    (congrArg _ ((tensorMap_comp (Z := X.toRingedSpace)
      _ _ _ _).trans (congrArg₂ _ (Category.id_comp _) (Category.comp_id _))))
  exact dnat_chase h1 h2 h3 h5

/-- **`(G ⊗ N)^∨ ≅ N^∨ ⊗ G^∨` is natural** in isomorphisms of `G` and `N`. -/
public theorem dualTensorIso_naturality {G G' N N' : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] (a : G ≅ G')
    (b : N ≅ N') :
    (dualTensorIso G N).hom ≫
        tensorMap (Z := X.toRingedSpace)
          (A := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)
          (A' := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N')
          (B := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf G)
          (B' := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf G')
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap b.inv)
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap a.inv) =
      Stacks.AlgebraicGeometry.ReflexiveModules.dualMap
          (tensorMap (Z := X.toRingedSpace) a.inv b.inv) ≫
        (dualTensorIso G' N').hom := by
  rw [dualMap_eq_sheafHomMapLeft b.inv, dualMap_eq_sheafHomMapLeft
    (tensorMap (Z := X.toRingedSpace) a.inv b.inv)]
  exact dualTensorIso_naturality_aux a b

end Dual

section Concrete

variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  [E.IsQuasicoherent] [E'.IsQuasicoherent]
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree'))

local notation "hqE" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E
local notation "hqE'" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E'

/-- `bundlePullbackIso` for the isomorphism of projective bundles induced by `e`. -/
public theorem bundlePullbackIso_eq : bundlePullbackIso (bundleMap hfree hfree' e)
      (bundleMap_comp_toBase hfree hfree' e) e =
    pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e) E ≪≫
      (Scheme.Modules.pullback (relativeProj
        (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqE')).toBase).mapIso e := rfl

/-- The tautological surjections correspond, in the form of the Koszul transport. -/
public theorem tautologicalMap_pullback' :
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map (tautologicalMap E hqE D) ≫
        (twistPullbackIso hfree hfree' e D D' ((1 : ℕ) : ℤ)).hom =
      (bundlePullbackIso (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) e).hom ≫
        tautologicalMap E' hqE' D' := by
  rw [bundlePullbackIso_eq, Iso.trans_hom, Functor.mapIso_hom]
  exact (tautologicalMap_pullback hfree hfree' e D D').trans (Category.assoc _ _ _).symm

/-- The multiplication of the twists under pullback, in the form of the Koszul transport. -/
public theorem twistPullbackIso_twistMul' (i j : ℤ) :
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map (twistMul D i j) ≫
        (twistPullbackIso hfree hfree' e D D' (i + j)).hom =
      (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' i) (twistPullbackIso hfree hfree' e D D' j)).hom ≫
        twistMul D' i j :=
  (twistPullbackIso_twistMul hfree hfree' e D D' i j).trans (Category.assoc _ _ _).symm

/-- **The bottom of the Koszul filtration `π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ 𝒪_S` is compatible with `e`.** -/
public theorem koszulBottomIso_iso (hn : 1 ≤ n) :
    (bundleComparison (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) 0
        (koszulTerm E hqE D 0)).hom ≫
      ((bundlePushforward E' hqE').rightDerived 0).map
        (koszulTermIso (bundleMap hfree hfree' e) (twistPullbackIso hfree hfree' e D D')
          (bundlePullbackIso (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) e)
          (tautologicalMap_pullback' hfree hfree' e D D') 0).hom ≫
      (koszulBottomIso E' hqE' D' hn hfree').hom =
    (koszulBottomIso E hqE D hn hfree).hom := by
  have hTZ := koszulTermZeroIso_pullback (bundleMap hfree hfree' e)
    (twistPullbackIso hfree hfree' e D D') (bundleMap_comp_toBase hfree hfree' e) e
    (tautologicalMap_pullback' hfree hfree' e D D')
  have hN := directImageComparisonApp_naturality _ _
    (Scheme.Modules.pullback (bundleMap hfree hfree' e))
    (pushforwardPullbackIso (bundleMap hfree hfree' e) _ _
      (bundleMap_comp_toBase hfree hfree' e)) 0 (koszulTermZeroIso E hqE D).hom
  have hQ := higherDirectImageZeroIso_naturality hfree hfree' e D D' hn 0
  have hP := symHom_app_zero_pieceZeroIso hfree hfree' e.hom
  have hM := higherDirectImageIsoMap_zero hfree hfree' e D D' 0
  have hR := ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward
    (relativeProj (bundleAlgebra E' hfree')).toBase) 0).hom.naturality
    (twistPullbackIso hfree hfree' e D D' ((0 : ℕ) : ℤ)).hom)
  have hZ : higherDirectImageZeroIso E hfree D hn 0 = zeroIso E hqE D (by omega) hfree 0 := rfl
  have hZ' : higherDirectImageZeroIso E' hfree' D' hn 0 = zeroIso E' hqE' D' (by omega) hfree' 0 :=
    rfl
  rw [hZ, hZ', ← hM] at hQ
  refine bottom_chase (H := higherDirectImageIsoMap hfree hfree' e D D' 0 ((0 : ℕ) : ℤ))
    (map_comp_congr _ hTZ.symm) hN ?_ hQ hP
  show _ ≫ (((Stacks.DerivedIndexing.rightDerivedIso _ 0).app _).inv ≫ _ ≫
    ((Stacks.DerivedIndexing.rightDerivedIso _ 0).app _).hom) ≫ _ = _
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Iso.hom_inv_id_assoc _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) hR.symm

/-- **The trace `Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E ≅ 𝒪_S` is compatible with `e`.** -/
public theorem topTraceIso_iso (hn : 1 ≤ n) :
    tensorMap ((bundleComparison (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) n
          (negTwist E hqE D (n + 1))).hom ≫
        ((bundlePushforward E' hqE').rightDerived n).map
          (twistPullbackIso hfree hfree' e D D' (-((n + 1 : ℕ) : ℤ))).hom)
        (Scheme.Modules.exteriorPowerMap e.hom ((n + 1 : ℕ) : ℤ)) ≫
      (topTraceIso E' hqE' D' hn hfree').hom =
    (topTraceIso E hqE D hn hfree).hom := by
  have hT := koszulTopIso_pullback (bundleMap hfree hfree' e) (twistPullbackIso hfree hfree' e D D')
    (bundleMap_comp_toBase hfree hfree' e) e (tautologicalMap_pullback' hfree hfree' e D D')
    (twistPullbackIso_twistMul' hfree hfree' e D D') hn hfree hfree'
  have hB := koszulBottomIso_iso hfree hfree' e D D' hn
  have hI := iso_square_inv (koszulTopIso E hqE D hn hfree) (koszulTopIso E' hqE' D' hn hfree')
    _ _ (hT.trans (Category.assoc _ _ _).symm)
  show _ ≫ (koszulTopIso E' hqE' D' hn hfree').inv ≫ (koszulBottomIso E' hqE' D' hn hfree').hom =
    (koszulTopIso E hqE D hn hfree).inv ≫ (koszulBottomIso E hqE D hn hfree).hom
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hI.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans hB)

/-- **The trace `Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨` is compatible with `e`**: under the map induced by
`e` on `Rⁿ π_* 𝒪(-n-1)` and the dual of `⋀ⁿ⁺¹ e⁻¹`. -/
public theorem topTwistIsoDualDet_iso (hn : 1 ≤ n) :
    (topTwistIsoDualDet E hqE D hn hfree).hom ≫
        Stacks.AlgebraicGeometry.ReflexiveModules.dualMap
          (Scheme.Modules.exteriorPowerMap e.inv ((n + 1 : ℕ) : ℤ)) =
      ((bundleComparison (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) n
          (negTwist E hqE D (n + 1))).hom ≫
        ((bundlePushforward E' hqE').rightDerived n).map
          (twistPullbackIso hfree hfree' e D D' (-((n + 1 : ℕ) : ℤ))).hom) ≫
      (topTwistIsoDualDet E' hqE' D' hn hfree').hom := by
  have := isInvertible_det E hn hfree
  have := isInvertible_det E' hn hfree'
  exact isoDualSheaf_of_tensor_iso_unit_naturality
    (N := Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))
    (N' := Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))
    ((Scheme.Modules.exteriorPowerFunctor S ((n + 1 : ℕ) : ℤ)).mapIso e) _
    (topTraceIso E hqE D hn hfree) (topTraceIso E' hqE' D' hn hfree')
    (topTraceIso_iso hfree hfree' e D D' hn)

/-- `Sym^d(e) : Sym^d(E) ≅ Sym^d(E')`. -/
public def symIso (d : ℤ) :
    (bundleAlgebra E hfree).piece d ≅ (bundleAlgebra E' hfree').piece d where
  hom := (symHom hfree hfree' e.hom).app d
  inv := (symHom hfree' hfree e.inv).app d
  hom_inv_id := by rw [symHom_app_comp, e.hom_inv_id, symHom_app_id]
  inv_hom_id := by rw [symHom_app_comp, e.inv_hom_id, symHom_app_id]

/-- **The map `SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S) ⟶ SheafHom(Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E', 𝒪_S)`
induced by `e`**: the dual of `Sym^{-n-1-d}(e⁻¹) ⊗ ⋀ⁿ⁺¹(e⁻¹)`. -/
public def topRowTargetMap (d : ℤ) : topRowTarget E hqE n d ⟶ topRowTarget E' hqE' n d :=
  Stacks.AlgebraicGeometry.ReflexiveModules.dualMap
    (tensorMap (Z := S.toRingedSpace) (symIso hfree hfree' e (-(n : ℤ) - 1 - d)).inv
      (Scheme.Modules.exteriorPowerMap e.inv ((n + 1 : ℕ) : ℤ)))

/-- The comparison `Rⁿ p_* M ⟶ Rⁿ p'_* f^* M` in the indexing `Functor.rightDerivedPlus` is natural
in `M`. -/
public theorem higherDirectImagePullback_naturality (q : ℕ) {M M' : (bundle E hqE).Modules}
    (φ : M ⟶ M') :
    ((bundlePushforward E hqE).rightDerivedPlus (q : ℤ)).map φ ≫
        higherDirectImagePullback (bundleMap hfree hfree' e) _ _
          (bundleMap_comp_toBase hfree hfree' e) (q : ℤ) M' =
      higherDirectImagePullback (bundleMap hfree hfree' e) _ _
          (bundleMap_comp_toBase hfree hfree' e) (q : ℤ) M ≫
        ((bundlePushforward E' hqE').rightDerivedPlus (q : ℤ)).map
          ((Scheme.Modules.pullback (bundleMap hfree hfree' e)).map φ) := by
  have h1 := ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqE) q).inv.naturality φ)
  have h2 := directImageComparisonApp_naturality _ _
    (Scheme.Modules.pullback (bundleMap hfree hfree' e))
    (pushforwardPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e))
    q φ
  have h3 := ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E' hqE') q).hom.naturality
    ((Scheme.Modules.pullback (bundleMap hfree hfree' e)).map φ))
  show _ ≫ ((Stacks.DerivedIndexing.rightDerivedIso _ q).app M').inv ≫ _ ≫ _ =
    (((Stacks.DerivedIndexing.rightDerivedIso _ q).app M).inv ≫ _ ≫ _) ≫ _
  exact paste_three _ _ _ _ _ _ _ _ _ _ h1 h2 h3

/-- `(Sym^k E)^∨ ≅ (Sym^k E')^∨`, the dual of `Sym^k(e⁻¹)`. -/
public abbrev symDualIso (k : ℕ) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((bundleAlgebra E' hfree').piece (k : ℤ)) :=
  ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S).mapIso
    (symIso hfree hfree' e (k : ℤ)).op).symm

/-- The comparison of higher direct images in the two indexings. -/
public theorem higherDirectImagePullback_rightDerivedIso (q : ℕ) {M : (bundle E hqE).Modules}
    {M' : (bundle E' hqE').Modules}
    (x : (Scheme.Modules.pullback (bundleMap hfree hfree' e)).obj M ⟶ M') :
    higherDirectImagePullback (bundleMap hfree hfree' e) _ _
        (bundleMap_comp_toBase hfree hfree' e) (q : ℤ) M ≫
      ((bundlePushforward E' hqE').rightDerivedPlus (q : ℤ)).map x ≫
      ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E' hqE') q).app M').inv =
    ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqE) q).app M).inv ≫
      (bundleComparison (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) q M).hom ≫
      ((bundlePushforward E' hqE').rightDerived q).map x := by
  have h :=
    ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E' hqE') q).inv.naturality x)
  show (((Stacks.DerivedIndexing.rightDerivedIso _ q).app M).inv ≫ _ ≫
    ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _).hom) ≫ _ = _
  simp only [Category.assoc]
  refine congrArg (_ ≫ _ ≫ ·) ((congrArg (_ ≫ ·) h).trans ?_)
  exact Iso.hom_inv_id_app_assoc
    (Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E' hqE') q)
    _ _

/-- The diagram chase behind `topRowTraceStep_iso`. -/
private theorem trace_chase {C : Type*} [Category C] {A A' B Cc D P Q Q' : C}
    {a : A ⟶ B} {t : B ⟶ Cc} {δ : Cc ⟶ D} {c' : B ⟶ P} {r' : P ⟶ Q} {t' : Q ⟶ D} {c : A ⟶ A'}
    {m : A' ⟶ P} {r : A' ⟶ Q'} {a' : Q' ⟶ Q}
    (hT : t ≫ δ = (c' ≫ r') ≫ t') (hN : a ≫ c' = c ≫ m) (hE : m ≫ r' = r ≫ a') :
    (a ≫ t) ≫ δ = (c ≫ r) ≫ a' ≫ t' := by
  rw [Category.assoc, hT, ← Category.assoc, ← Category.assoc, hN, Category.assoc c,
    hE]
  simp only [Category.assoc]

/-- **The trace step of the row `q = n` is compatible with `e`.** -/
public theorem topRowTraceStep_iso (hn : 1 ≤ n) (k : ℕ) :
    tensorMap (((bundlePushforward E hqE).rightDerived n).map
          (eqToHom (congrArg D.algebra.piece
            (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E hqE D hn hfree).hom)
        (𝟙 (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          ((bundleAlgebra E hfree).piece (k : ℤ)))) ≫
      tensorMap (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap
          (Scheme.Modules.exteriorPowerMap e.inv ((n + 1 : ℕ) : ℤ)))
        (symDualIso hfree hfree' e k).hom =
    tensorMap ((bundleComparison (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) n
          (D.algebra.piece (-(n : ℤ) - 1))).hom ≫
        ((bundlePushforward E' hqE').rightDerived n).map
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1)).hom)
        (symDualIso hfree hfree' e k).hom ≫
      tensorMap (((bundlePushforward E' hqE').rightDerived n).map
          (eqToHom (congrArg D'.algebra.piece
            (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E' hqE' D' hn hfree').hom)
        (𝟙 (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          ((bundleAlgebra E' hfree').piece (k : ℤ)))) := by
  have hT := topTwistIsoDualDet_iso hfree hfree' e D D' hn
  have hN := directImageComparisonApp_naturality _ _
    (Scheme.Modules.pullback (bundleMap hfree hfree' e))
    (pushforwardPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)) n
    (eqToHom (congrArg D.algebra.piece (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ))))
  have hE := twist_eqToHom_pullback (bundleMap hfree hfree' e)
    (twistPullbackIso hfree hfree' e D D')
    (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ))
  have hX := trace_chase hT hN
    (map_comp_congr _ hE)
  exact tensorMap_comp_congr hX ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **The dual of the reindexing of `Sym ⊗ ⋀ⁿ⁺¹` is compatible with `e`.** -/
public theorem dualReindex_iso {i j : ℤ} (h : i = j) :
    ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S).mapIso
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
          (eqToIso (congrArg (bundleAlgebra E hfree).piece h))).op).symm.hom ≫
      Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (X := S)
        (F := (Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).obj
          ((bundleAlgebra E' hfree').piece j))
        (G := (Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj ((bundleAlgebra E hfree).piece j))
        (tensorMap (Z := S.toRingedSpace)
          (symIso hfree hfree' e j).inv (Scheme.Modules.exteriorPowerMap e.inv ((n + 1 : ℕ) : ℤ))) =
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (X := S)
        (F := (Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).obj
          ((bundleAlgebra E' hfree').piece i))
        (G := (Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj ((bundleAlgebra E hfree).piece i))
        (tensorMap (Z := S.toRingedSpace)
          (symIso hfree hfree' e i).inv (Scheme.Modules.exteriorPowerMap e.inv ((n + 1 : ℕ) : ℤ))) ≫
      ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor S).mapIso
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).mapIso
          (eqToIso (congrArg (bundleAlgebra E' hfree').piece h))).op).symm.hom := by
  subst h
  simp only [eqToIso_refl, Functor.mapIso_refl]
  show Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (𝟙 _) ≫ _ =
    _ ≫ Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (𝟙 _)
  exact ((congrArg (· ≫ _) (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_id _)).trans
    (Category.id_comp _)).trans ((Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_id _).symm))

/-- **`(Sym^k E ⊗ ⋀ⁿ⁺¹ E)^∨ ≅ (⋀ⁿ⁺¹ E)^∨ ⊗ (Sym^k E)^∨` is compatible with `e`.** -/
public theorem dualTensorIso_iso (k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((bundleAlgebra E hfree).piece (k : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((bundleAlgebra E' hfree').piece (k : ℤ))] :
    (dualTensorIso ((bundleAlgebra E hfree).piece (k : ℤ))
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).inv ≫
      Stacks.AlgebraicGeometry.ReflexiveModules.dualMap
        (tensorMap (Z := S.toRingedSpace)
          (symIso hfree hfree' e (k : ℤ)).inv
          (Scheme.Modules.exteriorPowerMap e.inv ((n + 1 : ℕ) : ℤ))) =
    tensorMap (Z := S.toRingedSpace)
        (A := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)))
        (A' := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ)))
        (B := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          ((bundleAlgebra E hfree).piece (k : ℤ)))
        (B' := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          ((bundleAlgebra E' hfree').piece (k : ℤ)))
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap
          (Scheme.Modules.exteriorPowerMap e.inv ((n + 1 : ℕ) : ℤ)))
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (symIso hfree hfree' e (k : ℤ)).inv) ≫
      (dualTensorIso ((bundleAlgebra E' hfree').piece (k : ℤ))
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).inv := by
  have h := dualTensorIso_naturality (symIso hfree hfree' e (k : ℤ))
    ((Scheme.Modules.exteriorPowerFunctor S ((n + 1 : ℕ) : ℤ)).mapIso e)
  exact iso_square_inv _ _ _ _ h

end Concrete

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
