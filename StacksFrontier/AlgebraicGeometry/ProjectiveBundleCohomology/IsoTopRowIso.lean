module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoTopRow
public import StacksCore.Tactic.StacksAttribute

/-!
# The row `q = n` of Tag 01XX under an isomorphism of modules

Let `e : E ≅ E'` be an isomorphism of finite locally free `𝒪_S`-modules of constant rank `n + 1`,
`n ≥ 1`. The identifications `Rⁿ π_* 𝒪_{𝐏(E)}(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` of
[Stacks, Tag 01XX] for `E` and `E'` correspond under the map induced by `e` on `Rⁿ π_*` and the
dual of `Sym^{-n-1-d}(e⁻¹) ⊗ ⋀ⁿ⁺¹(e⁻¹)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap dualFunctor)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Unfold

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {n : ℕ} (hn : 1 ≤ n)
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))

/-- The row `q = n` for `d ≤ -n - 1` as a composite. -/
public theorem topRowIso_hom_of_le {d : ℤ} (h : d ≤ -(n : ℤ) - 1) :
    (topRowIso E hqc D hn hfree d).hom =
      ((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).map
          (twistPairingCurry E hqc D (-(n : ℤ) - 1 - d).toNat d (-(n : ℤ) - 1) (by omega)) ≫
        (higherDirectImageSheafHomIso E hqc D hn hfree _ d (by omega)).hom := by
  rw [topRowIso, dif_pos h]
  rfl

end Unfold

section ProjectionGeneric

variable {X X' T : Scheme.{u}} (f : X' ⟶ X) [IsIso f] (p : X ⟶ T) (p' : X' ⟶ T)
  (hbase : f ≫ p = p')

/-- **The projection formula** `R^q p_*(F ⊗ p^* G) ≅ R^q p_* F ⊗ G`, between tensor products of
`Stacks.SheafOfModules.Tensor.sheafTensor`, for `G` finite locally free. -/
public def projectionFormulaTensorIso (G : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] (F : X.Modules) (q : ℕ) :
    ((Scheme.Modules.pushforward p).rightDerived q).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback p).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj
        (((Scheme.Modules.pushforward p).rightDerived q).obj F)).obj G :=
  projectionFormulaDeltaApp p G F q

/-- The comparison of higher direct images along `f` in the two indexings. -/
public theorem higherDirectImagePullback_rightDerivedIso_of (q : ℕ) (M : X.Modules)
    (M' : X'.Modules)
    (x : (Scheme.Modules.pullback f).obj M ⟶ M') :
    higherDirectImagePullback f p p' hbase (q : ℤ) M ≫
        ((Scheme.Modules.pushforward p').rightDerivedPlus (q : ℤ)).map x ≫
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p') q).app M').inv =
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p) q).app M).inv ≫
        (directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q M).hom ≫
        ((Scheme.Modules.pushforward p').rightDerived q).map x := by
  have h := ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p')
    q).inv.naturality x)
  show (((Stacks.DerivedIndexing.rightDerivedIso _ q).app M).inv ≫ _ ≫
    ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _).hom) ≫ _ = _
  simp only [Category.assoc]
  refine congrArg (_ ≫ _ ≫ ·) ((congrArg (_ ≫ ·) h).trans ?_)
  exact Iso.hom_inv_id_app_assoc
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p') q)
    _ _

/-- The diagram chase behind `higherDirectImagePullback_projectionFormula`. -/
private theorem projection_chase {C : Type*} [Category C] {P P' Q Q' U U' V V' : C}
    {h : P ⟶ P'} {r : P' ⟶ Q} {i' : Q ⟶ Q'} {i : P ⟶ U} {c : U ⟶ U'} {s : U' ⟶ Q'}
    {pr : U ⟶ V} {a : V ⟶ V'} {pr' : Q' ⟶ V'} {P₁ : U ⟶ V} {P₂ : Q' ⟶ V'}
    (hB₁ : h ≫ r ≫ i' = i ≫ c ≫ s) (hB₂ : pr ≫ a = c ≫ s ≫ pr') (hp : P₁ = pr)
    (hp' : P₂ = pr') :
    h ≫ r ≫ i' ≫ P₂ = i ≫ P₁ ≫ a := by
  rw [hp, hp', hB₂, ← reassoc_of% hB₁]

variable {G G' : T.Modules} [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G'] (g : G ≅ G')

/-- The projection formulas of `p` and `p'` correspond, between tensor products of
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
public theorem projectionFormulaTensorIso_pullback (q : ℕ) {F : X.Modules}
    {F' : X'.Modules} (θ : (Scheme.Modules.pullback f).obj F ≅ F') :
    (projectionFormulaTensorIso p G F q).hom ≫
      tensorMap ((directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q F).hom ≫
          ((Scheme.Modules.pushforward p').rightDerived q).map θ.hom) g.hom =
    (directImageComparisonApp p p' (Scheme.Modules.pullback f)
      (pushforwardPullbackIso f p p' hbase) q
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback p).obj G))).hom ≫
      ((Scheme.Modules.pushforward p').rightDerived q).map
        (tensorPullbackIso f.toLRSHom.toShHom θ (pullbackPullbackIso' f p p' hbase g)).hom ≫
      (projectionFormulaTensorIso p' G' F' q).hom :=
  projectionFormulaDeltaApp_pullback_iso f p p' hbase g q θ

/-- **The projection formulas of `p` and `p'` correspond under the comparison of higher direct
images along `f`**, in the indexing of `Functor.rightDerivedPlus`, along `f^* F ≅ F'` and
`G ≅ G'`. -/
public theorem higherDirectImagePullback_projectionFormula (q : ℕ) {F : X.Modules}
    {F' : X'.Modules} (θ : (Scheme.Modules.pullback f).obj F ≅ F') :
    higherDirectImagePullback f p p' hbase (q : ℤ)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback p).obj G)) ≫
      ((Scheme.Modules.pushforward p').rightDerivedPlus (q : ℤ)).map
        (tensorPullbackIso f.toLRSHom.toShHom θ (pullbackPullbackIso' f p p' hbase g)).hom ≫
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p') q).app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj F').obj
          ((Scheme.Modules.pullback p').obj G'))).inv ≫
      (projectionFormulaTensorIso p' G' F' q).hom =
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p) q).app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback p).obj G))).inv ≫
      (projectionFormulaTensorIso p G F q).hom ≫
      tensorMap ((directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q F).hom ≫
          ((Scheme.Modules.pushforward p').rightDerived q).map θ.hom) g.hom :=
  projection_chase
    (higherDirectImagePullback_rightDerivedIso_of f p p' hbase q
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback p).obj G))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj F').obj
        ((Scheme.Modules.pullback p').obj G'))
      (tensorPullbackIso f.toLRSHom.toShHom θ (pullbackPullbackIso' f p p' hbase g)).hom)
    (projectionFormulaTensorIso_pullback f p p' hbase g q θ) rfl rfl

end ProjectionGeneric

section Concrete

variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree'))

local notation "hqE" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E
local notation "hqE'" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E'

/-- The diagram chase behind `topRowDual_iso`. -/
private theorem dual_chase {C : Type*} [Category C] {P P' Q Q' R₀ R₁ R₂ R₃ : C}
    {a : P ⟶ Q} {b : Q ⟶ Q'} {t : P ⟶ P'} {u : P' ⟶ Q'} {δ' : Q' ⟶ R₁} {δ : P' ⟶ R₀}
    {v : R₀ ⟶ R₁} {v' : R₀ ⟶ R₁} {r : R₀ ⟶ R₂} {r' : R₁ ⟶ R₃} {m : R₂ ⟶ R₃}
    (hC : t ≫ u = a ≫ b) (hD : δ ≫ v = u ≫ δ') (hv : v = v') (hE : r ≫ m = v' ≫ r') :
    a ≫ b ≫ δ' ≫ r' = t ≫ δ ≫ r ≫ m := by
  rw [← Category.assoc a, ← hC, Category.assoc, ← Category.assoc u, ← hD, hv, Category.assoc, ← hE]

variable (hn : 1 ≤ n) (k : ℕ) {d : ℤ} (hkd : (k : ℤ) = -(n : ℤ) - 1 - d)
  [hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((bundleAlgebra E hfree).piece (k : ℤ))]
  [hA' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((bundleAlgebra E' hfree').piece (k : ℤ))]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (dualSheaf ((bundleAlgebra E' hfree').piece (k : ℤ)))]


include hkd in
/-- **The trace, the dual of the tensor product and the reindexing of the row `q = n` are
compatible with `e`.** -/
public theorem topRowDual_iso :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    tensorMap ((bundleComparison (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) n
          (D.algebra.piece (-(n : ℤ) - 1))).hom ≫
        ((bundlePushforward E' hqE').rightDerived n).map
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1)).hom)
        (symDualIso hfree hfree' e k).hom ≫
      tensorMap (((bundlePushforward E' hqE').rightDerived n).map
          (eqToHom (congrArg D'.algebra.piece
            (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E' hqE' D' hn hfree').hom)
        (𝟙 (dualSheaf ((bundleAlgebra E' hfree').piece (k : ℤ)))) ≫
      (dualTensorIso ((bundleAlgebra E' hfree').piece (k : ℤ))
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).inv ≫
      ((dualFunctor S).mapIso
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).mapIso
          (eqToIso (congrArg (bundleAlgebra E' hfree').piece hkd))).op).inv =
    tensorMap (((bundlePushforward E hqE).rightDerived n).map
          (eqToHom (congrArg D.algebra.piece
            (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E hqE D hn hfree).hom)
        (𝟙 (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))) ≫
      (dualTensorIso ((bundleAlgebra E hfree).piece (k : ℤ))
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).inv ≫
      ((dualFunctor S).mapIso
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
          (eqToIso (congrArg (bundleAlgebra E hfree).piece hkd))).op).inv ≫
      topRowTargetMap hfree hfree' e d :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  dual_chase (topRowTraceStep_iso hfree hfree' e D D' hn k)
    (dualTensorIso_iso hfree hfree' e k) rfl
    (dualReindex_iso hfree hfree' e hkd)

/-- `f^* π^* Sym^k(E) ≅ π'^* Sym^k(E')`, inverted, as a composite. -/
public theorem pullbackPullbackIso_trans_inv {X X' T : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ T)
    (p' : X' ⟶ T) (hbase : f ≫ p = p') {G G' : T.Modules} (g : G ≅ G') :
    (pullbackPullbackIso f p p' hbase G ≪≫ (Scheme.Modules.pullback p').mapIso g).inv =
      (Scheme.Modules.pullback p').map g.inv ≫ (pullbackPullbackIso f p p' hbase G).inv := by
  rw [Iso.trans_inv, Functor.mapIso_inv]

/-- **The curried multiplication pairing `𝒪(d) ⟶ 𝒪(-n-1) ⊗ π^*((Sym^k E)^∨)` corresponds under
`e`**, `d + k = -n - 1`. -/
public theorem twistPairingCurry_dual_iso (hd : d + k = -(n : ℤ) - 1) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
      (twistPairingCurry E hqE D k d (-(n : ℤ) - 1) hd) ≫
      (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
        (sheafHomIsoTensorDual
          ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
          ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl (D.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E hfree)).toBase ((bundleAlgebra E hfree).piece (k : ℤ))
              hA).symm).hom ≫
        (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1))
          (pullbackPullbackIso' (bundleMap hfree hfree' e)
            (relativeProj (bundleAlgebra E hfree)).toBase
            (relativeProj (bundleAlgebra E' hfree')).toBase
            (bundleMap_comp_toBase hfree hfree' e) (symDualIso hfree hfree' e k))).hom =
      (twistPullbackIso hfree hfree' e D D' d).hom ≫
        (twistPairingCurry E' hqE' D' k d (-(n : ℤ) - 1) hd) ≫
        (sheafHomIsoTensorDual
          ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).obj
          ((bundleAlgebra E' hfree').piece (k : ℤ))) (D'.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
            (Iso.refl (D'.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E' hfree')).toBase
              ((bundleAlgebra E' hfree').piece (k : ℤ)) hA').symm).hom :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  curry_dual_pullback_iso (bundleMap hfree hfree' e) (relativeProj (bundleAlgebra E hfree)).toBase
    (relativeProj (bundleAlgebra E' hfree')).toBase
    (bundleMap_comp_toBase hfree hfree' e) (symIso hfree hfree' e (k : ℤ))
    (symPullbackIso hfree hfree' e (k : ℤ))
    (pullbackPullbackIso_trans_inv (bundleMap hfree hfree' e)
      (relativeProj (bundleAlgebra E hfree)).toBase (relativeProj (bundleAlgebra E' hfree')).toBase
      (bundleMap_comp_toBase hfree hfree' e) (symIso hfree hfree' e (k : ℤ)))
    (symDualIso hfree hfree' e k) (symDualIso_hom hfree hfree' e k)
    (twistPullbackIso hfree hfree' e D D' d) (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1))
    (twistPairing E hqE D k d (-(n : ℤ) - 1) hd) (twistPairing E' hqE' D' k d (-(n : ℤ) - 1) hd)
    (twistPairing_pullback hfree hfree' e D D' k d (-(n : ℤ) - 1) hd)

/-- The curried multiplication pairing of the row `q = n` under `e`, on `Rⁿ π'_*`. -/
public theorem twistPairingCurry_dual_iso_map (hd : d + k = -(n : ℤ) - 1) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
      ((Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
      (twistPairingCurry E hqE D k d (-(n : ℤ) - 1) hd)) ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        ((Scheme.Modules.pullback (bundleMap hfree hfree' e)).map
        (sheafHomIsoTensorDual
          ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
          ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl (D.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E hfree)).toBase ((bundleAlgebra E hfree).piece (k : ℤ))
              hA).symm).hom) ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1))
          (pullbackPullbackIso' (bundleMap hfree hfree' e)
            (relativeProj (bundleAlgebra E hfree)).toBase
            (relativeProj (bundleAlgebra E' hfree')).toBase
            (bundleMap_comp_toBase hfree hfree' e) (symDualIso hfree hfree' e k))).hom =
    ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
      (twistPullbackIso hfree hfree' e D D' d).hom ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
      (twistPairingCurry E' hqE' D' k d (-(n : ℤ) - 1) hd) ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (sheafHomIsoTensorDual
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).obj
        ((bundleAlgebra E' hfree').piece (k : ℤ))) (D'.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
            (Iso.refl (D'.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E' hfree')).toBase
              ((bundleAlgebra E' hfree').piece (k : ℤ)) hA').symm).hom := by
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  have h := congrArg ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
    (twistPairingCurry_dual_iso hfree hfree' e D D' k hd)
  exact ((((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map_comp _ _).trans
      (congrArg (((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map _ ≫ ·)
        (((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map_comp _ _))).symm.trans
    (h.trans ((((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map_comp _ _).trans
      (congrArg (((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map _ ≫ ·)
        (((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map_comp _ _))))

/-- The diagram chase behind `topRowCurry_iso`. -/
private theorem curryRow_chase {C : Type*} [Category C] {P Q W P' Q' W' Z T₁ T₂ : C}
    {a₁ : P ⟶ Q} {a₂ : Q ⟶ W} {h₀ : P ⟶ P'} {h₁ : Q ⟶ Q'} {h₂ : W ⟶ W'} {b₁ : P' ⟶ Q'}
    {b₂ : Q' ⟶ W'} {g : W' ⟶ Z} {t : P' ⟶ T₁} {c' : T₁ ⟶ T₂} {ψ' : T₂ ⟶ Z}
    (N₁ : a₁ ≫ h₁ = h₀ ≫ b₁) (N₂ : a₂ ≫ h₂ = h₁ ≫ b₂) (hA : b₁ ≫ b₂ ≫ g = t ≫ c' ≫ ψ') :
    a₁ ≫ a₂ ≫ h₂ ≫ g = h₀ ≫ t ≫ c' ≫ ψ' := by
  rw [reassoc_of% N₂, reassoc_of% N₁, hA]

/-- **The curried pairing of the row `q = n` is compatible with `e`, on higher direct images.** -/
public theorem topRowCurry_iso (hd : d + k = -(n : ℤ) - 1) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    ((bundlePushforward E hqE).rightDerivedPlus ((n : ℕ) : ℤ)).map
      (twistPairingCurry E hqE D k d (-(n : ℤ) - 1) hd) ≫
      ((bundlePushforward E hqE).rightDerivedPlus ((n : ℕ) : ℤ)).map
        (sheafHomIsoTensorDual
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
        ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl (D.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E hfree)).toBase ((bundleAlgebra E hfree).piece (k : ℤ))
              hA).symm).hom ≫
      higherDirectImagePullback (bundleMap hfree hfree' e) _ _
        (bundleMap_comp_toBase hfree hfree' e)
          ((n : ℕ) : ℤ) _ ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1))
          (pullbackPullbackIso' (bundleMap hfree hfree' e)
            (relativeProj (bundleAlgebra E hfree)).toBase
            (relativeProj (bundleAlgebra E' hfree')).toBase
            (bundleMap_comp_toBase hfree hfree' e) (symDualIso hfree hfree' e k))).hom =
    higherDirectImagePullback (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((n : ℕ) : ℤ) (D.algebra.piece d) ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (twistPullbackIso hfree hfree' e D D' d).hom ≫
        ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (twistPairingCurry E' hqE' D' k d (-(n : ℤ) - 1) hd) ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (sheafHomIsoTensorDual
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).obj
        ((bundleAlgebra E' hfree').piece (k : ℤ))) (D'.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
            (Iso.refl (D'.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E' hfree')).toBase
              ((bundleAlgebra E' hfree').piece (k : ℤ)) hA').symm).hom :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  curryRow_chase (@higherDirectImagePullback_naturality S E E' n hfree hfree' e
    (isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree)
    (isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree') n _ _
      (twistPairingCurry E hqE D k d (-(n : ℤ) - 1) hd))
    (@higherDirectImagePullback_naturality S E E' n hfree hfree' e
    (isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree)
    (isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree') n _ _
      (sheafHomIsoTensorDual
      ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
      ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl (D.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E hfree)).toBase ((bundleAlgebra E hfree).piece (k : ℤ))
              hA).symm).hom)
    (twistPairingCurry_dual_iso_map hfree hfree' e D D' k hd)

/-- `topRowCurry_iso` with the isomorphism `SheafHom(π^* Sym^k E, 𝒪(-n-1)) ≅ 𝒪(-n-1) ⊗
π^*((Sym^k E)^∨)` mapped as an isomorphism. -/
public theorem topRowCurry_iso' (hd : d + k = -(n : ℤ) - 1) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    ((bundlePushforward E hqE).rightDerivedPlus ((n : ℕ) : ℤ)).map
      (twistPairingCurry E hqE D k d (-(n : ℤ) - 1) hd) ≫
      (((bundlePushforward E hqE).rightDerivedPlus ((n : ℕ) : ℤ)).mapIso
        (sheafHomIsoTensorDual
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
        ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl (D.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E hfree)).toBase ((bundleAlgebra E hfree).piece (k : ℤ))
              hA).symm)).hom ≫
      higherDirectImagePullback (bundleMap hfree hfree' e) _ _
        (bundleMap_comp_toBase hfree hfree' e)
          ((n : ℕ) : ℤ) _ ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1))
          (pullbackPullbackIso' (bundleMap hfree hfree' e)
            (relativeProj (bundleAlgebra E hfree)).toBase
            (relativeProj (bundleAlgebra E' hfree')).toBase
            (bundleMap_comp_toBase hfree hfree' e) (symDualIso hfree hfree' e k))).hom =
    higherDirectImagePullback (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((n : ℕ) : ℤ) (D.algebra.piece d) ≫
      ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (twistPullbackIso hfree hfree' e D D' d).hom ≫
        ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
        (twistPairingCurry E' hqE' D' k d (-(n : ℤ) - 1) hd) ≫
      (((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).mapIso
        (sheafHomIsoTensorDual
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).obj
        ((bundleAlgebra E' hfree').piece (k : ℤ))) (D'.algebra.piece (-(n : ℤ) - 1)) ≪≫
          Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
            (Iso.refl (D'.algebra.piece (-(n : ℤ) - 1)))
            (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (bundleAlgebra E' hfree')).toBase
              ((bundleAlgebra E' hfree').piece (k : ℤ)) hA').symm)).hom :=
  topRowCurry_iso hfree hfree' e D D' k hd

include hkd in
/-- The isomorphism of the row `q = n` after the comparison of the two indexings, as a
composite. -/
public theorem topRowTail_hom :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    (higherDirectImageTensorDualIsoNat E hqE hfree k (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
        Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
          (((bundlePushforward E hqE).rightDerived n).mapIso
              (eqToIso (congrArg D.algebra.piece
                (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≪≫
            topTwistIsoDualDet E hqE D hn hfree)
          (Iso.refl (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))) ≪≫
        (dualTensorIso ((bundleAlgebra E hfree).piece (k : ℤ))
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).symm ≪≫
        ((dualFunctor S).mapIso ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
            (eqToIso (congrArg (bundleAlgebra E hfree).piece hkd))).op).symm).hom =
      (projectionFormulaTensorIso (relativeProj (bundleAlgebra E hfree)).toBase
        (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1))
        n).hom ≫
      (tensorMap (((bundlePushforward E hqE).rightDerived n).map
          (eqToHom (congrArg D.algebra.piece
            (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E hqE D hn hfree).hom)
        (𝟙 (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))) : _) ≫
      (dualTensorIso ((bundleAlgebra E hfree).piece (k : ℤ))
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).inv ≫
      ((dualFunctor S).mapIso
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
          (eqToIso (congrArg (bundleAlgebra E hfree).piece hkd))).op).inv := by
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  dsimp only [Iso.trans]
  rfl

/-- The diagram chase behind `topRowProjectionTail_iso`. -/
private theorem projTail_chase {C : Type*} [Category C] {P P' Q Q' U V V' Z' : C}
    {h : P ⟶ P'} {g : P' ⟶ Q} {i' : Q ⟶ Q'} {i : P ⟶ U} {τ' : Q' ⟶ Z'}
    {pf : U ⟶ V} {pf' : Q' ⟶ V'} {a : V ⟶ V'} {x' : V' ⟶ Z'}
    (hT' : τ' = pf' ≫ x') (hII : h ≫ g ≫ i' ≫ pf' = i ≫ pf ≫ a) :
    h ≫ g ≫ i' ≫ τ' = i ≫ pf ≫ a ≫ x' := by
  rw [hT', reassoc_of% hII]

/-- **The projection formula of the row `q = n` is compatible with `e`**, up to the isomorphism
of the row after the comparison of the two indexings. -/
public theorem topRowProjectionTail_iso :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    higherDirectImagePullback (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          ((n : ℕ) : ℤ) (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.presheaf,
            (relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.IsSheaf⟩).obj
            (D.algebra.piece (-(n : ℤ) - 1))).obj
            ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
            (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ))))) ≫
            ((bundlePushforward E' hqE').rightDerivedPlus ((n : ℕ) : ℤ)).map
            (tensorPullbackIso (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1))
          (pullbackPullbackIso' (bundleMap hfree hfree' e)
            (relativeProj (bundleAlgebra E hfree)).toBase
            (relativeProj (bundleAlgebra E' hfree')).toBase
            (bundleMap_comp_toBase hfree hfree' e) (symDualIso hfree hfree' e k))).hom ≫
      ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E' hqE') n).app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(relativeProj (bundleAlgebra E' hfree')).scheme.toRingedSpace.presheaf,
        (relativeProj (bundleAlgebra E' hfree')).scheme.toRingedSpace.IsSheaf⟩).obj
        (D'.algebra.piece (-(n : ℤ) - 1))).obj
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).obj
        (dualSheaf ((bundleAlgebra E' hfree').piece (k : ℤ)))))).inv ≫
        (higherDirectImageTensorDualIsoNat E' hqE' hfree' k (D'.algebra.piece (-(n : ℤ) - 1)) ≪≫
        Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
          (((bundlePushforward E' hqE').rightDerived n).mapIso
              (eqToIso (congrArg D'.algebra.piece
                (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≪≫
            topTwistIsoDualDet E' hqE' D' hn hfree')
          (Iso.refl (dualSheaf ((bundleAlgebra E' hfree').piece (k : ℤ)))) ≪≫
        (dualTensorIso ((bundleAlgebra E' hfree').piece (k : ℤ))
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).symm ≪≫
        ((dualFunctor S).mapIso ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).mapIso
            (eqToIso (congrArg (bundleAlgebra E' hfree').piece hkd))).op).symm).hom =
    ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqE) n).app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.presheaf,
      (relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.IsSheaf⟩).obj
      (D.algebra.piece (-(n : ℤ) - 1))).obj
      ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
      (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))))).inv ≫
      (projectionFormulaTensorIso (relativeProj (bundleAlgebra E hfree)).toBase
      (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) n).hom ≫
      (tensorMap ((bundleComparison (bundleMap hfree hfree' e)
      (bundleMap_comp_toBase hfree hfree' e) n
          (D.algebra.piece (-(n : ℤ) - 1))).hom ≫
        ((bundlePushforward E' hqE').rightDerived n).map
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1)).hom)
        (symDualIso hfree hfree' e k).hom : _) ≫
      (tensorMap (((bundlePushforward E' hqE').rightDerived n).map
          (eqToHom (congrArg D'.algebra.piece
            (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E' hqE' D' hn hfree').hom)
        (𝟙 (dualSheaf ((bundleAlgebra E' hfree').piece (k : ℤ)))) : _) ≫
      (dualTensorIso ((bundleAlgebra E' hfree').piece (k : ℤ))
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).inv ≫
      ((dualFunctor S).mapIso
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).mapIso
          (eqToIso (congrArg (bundleAlgebra E' hfree').piece hkd))).op).inv :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  projTail_chase (topRowTail_hom hfree' D' hn k hkd)
    (higherDirectImagePullback_projectionFormula (bundleMap hfree hfree' e)
      (relativeProj (bundleAlgebra E hfree)).toBase (relativeProj (bundleAlgebra E' hfree')).toBase
      (bundleMap_comp_toBase hfree hfree' e) (symDualIso hfree hfree' e k) n
      (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1)))

/-- The diagram chase behind `topRowDualTail_iso`. -/
private theorem dualTail_chase {C : Type*} [Category C] {P U V V' T₁ T₁' T₂ T₂' Z Z' : C}
    {i : P ⟶ U} {τ : U ⟶ Z} {pf : U ⟶ V} {a : V ⟶ V'} {t : V ⟶ T₁} {δ : T₁ ⟶ T₂}
    {r : T₂ ⟶ Z} {t' : V' ⟶ T₁'} {δ' : T₁' ⟶ T₂'} {r' : T₂' ⟶ Z'} {m : Z ⟶ Z'}
    (hT : τ = pf ≫ t ≫ δ ≫ r) (hIII : a ≫ t' ≫ δ' ≫ r' = t ≫ δ ≫ r ≫ m) :
    i ≫ pf ≫ a ≫ t' ≫ δ' ≫ r' = i ≫ τ ≫ m := by
  rw [hT, hIII]
  simp only [Category.assoc]

include hkd in
/-- **The trace, the dual of the tensor product and the reindexing of the row `q = n` are
compatible with `e`**, after the projection formula. -/
public theorem topRowDualTail_iso :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqE) n).app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.presheaf,
      (relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.IsSheaf⟩).obj
      (D.algebra.piece (-(n : ℤ) - 1))).obj
      ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
      (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))))).inv ≫
      (projectionFormulaTensorIso (relativeProj (bundleAlgebra E hfree)).toBase
      (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) n).hom ≫
      (tensorMap ((bundleComparison (bundleMap hfree hfree' e)
      (bundleMap_comp_toBase hfree hfree' e) n
          (D.algebra.piece (-(n : ℤ) - 1))).hom ≫
        ((bundlePushforward E' hqE').rightDerived n).map
          (twistPullbackIso hfree hfree' e D D' (-(n : ℤ) - 1)).hom)
        (symDualIso hfree hfree' e k).hom : _) ≫
      (tensorMap (((bundlePushforward E' hqE').rightDerived n).map
          (eqToHom (congrArg D'.algebra.piece
            (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≫
        (topTwistIsoDualDet E' hqE' D' hn hfree').hom)
        (𝟙 (dualSheaf ((bundleAlgebra E' hfree').piece (k : ℤ)))) : _) ≫
      (dualTensorIso ((bundleAlgebra E' hfree').piece (k : ℤ))
        (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).inv ≫
      ((dualFunctor S).mapIso
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).mapIso
          (eqToIso (congrArg (bundleAlgebra E' hfree').piece hkd))).op).inv =
    ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqE) n).app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.presheaf,
      (relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.IsSheaf⟩).obj
      (D.algebra.piece (-(n : ℤ) - 1))).obj
      ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
      (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))))).inv ≫
      (higherDirectImageTensorDualIsoNat E hqE hfree k (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
        Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
          (((bundlePushforward E hqE).rightDerived n).mapIso
              (eqToIso (congrArg D.algebra.piece
                (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≪≫
            topTwistIsoDualDet E hqE D hn hfree)
          (Iso.refl (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))) ≪≫
        (dualTensorIso ((bundleAlgebra E hfree).piece (k : ℤ))
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).symm ≪≫
        ((dualFunctor S).mapIso ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
            (eqToIso (congrArg (bundleAlgebra E hfree).piece hkd))).op).symm).hom ≫
              topRowTargetMap hfree hfree' e d :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  dualTail_chase (topRowTail_hom hfree D hn k hkd) (topRowDual_iso hfree hfree' e D D' hn k hkd)

end Concrete

section Final

variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree')) (hn : 1 ≤ n)

local notation "hqE" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E
local notation "hqE'" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E'

/-- The isomorphism of the row `q = n` after the multiplication pairing, as a composite. -/
public theorem higherDirectImageSheafHomIso_hom_eq (k : ℕ) {d : ℤ}
    (hkd : (k : ℤ) = -(n : ℤ) - 1 - d)
    (hd : (k : ℤ) + d = -(n : ℤ) - 1) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isFiniteLocallyFree_piece E hqE hfree k
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _
      (isFiniteLocallyFree_piece E hqE hfree k)
    (higherDirectImageSheafHomIso E hqE D hn hfree k d hd).hom =
      (((bundlePushforward E hqE).rightDerivedPlus ((n : ℕ) : ℤ)).mapIso
        (sheafHomIsoTensorDual
        ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
        ((bundleAlgebra E hfree).piece (k : ℤ))) (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
        Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl (D.algebra.piece (-(n : ℤ) - 1)))
          (Stacks.FundamentalGroup.pullbackDualSheafIso
            (relativeProj (bundleAlgebra E hfree)).toBase ((bundleAlgebra E hfree).piece (k : ℤ))
            (isFiniteLocallyFree_piece E hqE hfree k)).symm)).hom ≫
              ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqE) n).app
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨(relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.presheaf,
              (relativeProj (bundleAlgebra E hfree)).scheme.toRingedSpace.IsSheaf⟩).obj
              (D.algebra.piece (-(n : ℤ) - 1))).obj
              ((Scheme.Modules.pullback (relativeProj (bundleAlgebra E hfree)).toBase).obj
              (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))))).inv ≫
              (higherDirectImageTensorDualIsoNat E hqE hfree k (D.algebra.piece (-(n : ℤ) - 1)) ≪≫
        Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
          (((bundlePushforward E hqE).rightDerived n).mapIso
              (eqToIso (congrArg D.algebra.piece
                (by push_cast; ring : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ)))) ≪≫
            topTwistIsoDualDet E hqE D hn hfree)
          (Iso.refl (dualSheaf ((bundleAlgebra E hfree).piece (k : ℤ)))) ≪≫
        (dualTensorIso ((bundleAlgebra E hfree).piece (k : ℤ))
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).symm ≪≫
        ((dualFunctor S).mapIso ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
            (eqToIso (congrArg (bundleAlgebra E hfree).piece hkd))).op).symm).hom :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isFiniteLocallyFree_piece E hqE hfree k
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _
    (isFiniteLocallyFree_piece E hqE hfree k)
  by dsimp only [higherDirectImageSheafHomIso, bundleAlgebra, bundle, bundlePushforward]; rfl

/-- The diagram chase behind `topRowIso_naturality_of_le`. -/
private theorem row_chase {C : Type*} [Category C] {P P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Q₃ R₁ Z Z' : C}
    {h₀ : P ⟶ P₁} {tw : P₁ ⟶ P₂} {c' : P₂ ⟶ P₃} {ψ' : P₃ ⟶ P₄} {i' : P₄ ⟶ P₅} {τ' : P₅ ⟶ Z'}
    {c : P ⟶ Q₁} {ψ : Q₁ ⟶ Q₂} {i : Q₂ ⟶ Q₃} {τ : Q₃ ⟶ Z} {m : Z ⟶ Z'} {h : Q₂ ⟶ R₁}
    {g : R₁ ⟶ P₄} {x : Q₃ ⟶ Z'}
    (hI : c ≫ ψ ≫ h ≫ g = h₀ ≫ tw ≫ c' ≫ ψ') (hL₁ : h ≫ g ≫ i' ≫ τ' = i ≫ x)
    (hL₂ : i ≫ x = i ≫ τ ≫ m) :
    (h₀ ≫ tw) ≫ c' ≫ ψ' ≫ i' ≫ τ' = (c ≫ ψ ≫ i ≫ τ) ≫ m := by
  simp only [Category.assoc]
  rw [← reassoc_of% hI, hL₁, hL₂]

/-- **[Stacks, Tag 01XX], the row `q = n` for `d ≤ -n - 1` is compatible with isomorphisms**:
under the map `Rⁿ π_* 𝒪_{𝐏(E)}(d) ⟶ Rⁿ π'_* 𝒪_{𝐏(E')}(d)` induced by `e : E ≅ E'` and the dual
of `Sym^{-n-1-d}(e⁻¹) ⊗ ⋀ⁿ⁺¹(e⁻¹)`, the identifications
`Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` for `E` and `E'` correspond. -/
public theorem topRowIso_naturality_of_le {d : ℤ} (h : d ≤ -(n : ℤ) - 1) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    higherDirectImageIsoMap hfree hfree' e D D' (n : ℤ) d ≫ (topRowIso E' hqE' D' hn hfree' d).hom =
      (topRowIso E hqE D hn hfree d).hom ≫ topRowTargetMap hfree hfree' e d := by
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  have hA := isFiniteLocallyFree_piece E hqE hfree (-(n : ℤ) - 1 - d).toNat
  have hA' := isFiniteLocallyFree_piece E' hqE' hfree' (-(n : ℤ) - 1 - d).toNat
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _ hA
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _ hA'
  have hk : (((-(n : ℤ) - 1 - d).toNat : ℕ) : ℤ) = -(n : ℤ) - 1 - d := by omega
  have hd : d + (((-(n : ℤ) - 1 - d).toNat : ℕ) : ℤ) = -(n : ℤ) - 1 := by omega
  have hd' : ((((-(n : ℤ) - 1 - d).toNat : ℕ) : ℤ)) + d = -(n : ℤ) - 1 := by omega
  rw [topRowIso_hom_of_le E hqE D hn hfree h, topRowIso_hom_of_le E' hqE' D' hn hfree' h,
    higherDirectImageIsoMap,
    higherDirectImageSheafHomIso_hom_eq hfree D hn _ hk hd',
    higherDirectImageSheafHomIso_hom_eq hfree' D' hn _ hk hd']
  exact row_chase (topRowCurry_iso' hfree hfree' e D D' _ hd)
    (topRowProjectionTail_iso hfree hfree' e D D' hn _ hk)
    (topRowDualTail_iso hfree hfree' e D D' hn _ hk)

end Final

section Compatible

variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree')) (hn : 1 ≤ n)

local notation "hqE'" => Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E'

/-- **The row `q = n` of Tag 01XX is compatible with isomorphisms**, for every integer `d`: under
the map `Rⁿ π_* 𝒪_{𝐏(E)}(d) ⟶ Rⁿ π'_* 𝒪_{𝐏(E')}(d)` induced by `e : E ≅ E'` and the dual of
`Sym^{-n-1-d}(e⁻¹) ⊗ ⋀ⁿ⁺¹(e⁻¹)`, the identifications
`Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` for `E` and `E'` correspond. -/
public theorem higherDirectImageTopIso_naturality (d : ℤ) :
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
    haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
    higherDirectImageIsoMap hfree hfree' e D D' (n : ℤ) d ≫
        (higherDirectImageTopIso E' hfree' D' hn d).hom =
      (higherDirectImageTopIso E hfree D hn d).hom ≫ topRowTargetMap hfree hfree' e d := by
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  by_cases h : d ≤ -(n : ℤ) - 1
  · exact topRowIso_naturality_of_le hfree hfree' e D D' hn h
  · exact (isZero_topRow_of_le E' hqE' D' hn hfree' (d := d) (by omega)).2.eq_of_tgt _ _

/-- **[Stacks, Tag 01XX]: the identifications of the higher direct images of the twists on a
projective bundle are compatible with isomorphisms between locally free sheaves.** Let
`e : E ≅ E'` be an isomorphism of finite locally free `𝒪_S`-modules of constant rank `n + 1`,
`n ≥ 1`, inducing `𝐏(E') ≅ 𝐏(E)` over `S` and the maps
`R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_* 𝒪_{𝐏(E')}(d)` (`higherDirectImageIsoMap`). For every pair
`(q, d)` of integers:
* `q = 0`, `d ≥ 0`: the identifications `R⁰π_* 𝒪(d) ≅ Sym^d` correspond under `Sym^d(e)`;
* `q = 0`, `d < 0`, and `q ≠ 0, n`: the induced map is zero, between modules that vanish;
* `q = n`: the identifications `Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`
  correspond under the dual of `Sym^{-n-1-d}(e⁻¹) ⊗ ⋀ⁿ⁺¹(e⁻¹)`. -/
@[stacks 01XX "compatibility with isomorphisms between locally free sheaves, every row: for an \
isomorphism e : E ≅ E' of finite locally free modules of constant rank n + 1, n ≥ 1, over an \
arbitrary scheme S, the maps R^q π_* O(d) → R^q π'_* O(d) induced by e and P(E') ≅ P(E) carry \
the identification R^0 π_* O(d) ≅ Sym^d(E) to R^0 π'_* O(d) ≅ Sym^d(E') under Sym^d(e) for \
d ≥ 0, are zero for q = 0, d < 0 and for q ≠ 0, n, and carry R^n π_* O(d) ≅ \
SheafHom(Sym^(-n-1-d)(E) ⊗ ∧^(n+1) E, O_S) to the same identification for E' under the dual of \
Sym^(-n-1-d)(e⁻¹) ⊗ ∧^(n+1)(e⁻¹), for every integer d"]
public theorem higherDirectImage_iso_compatible :
    (∀ d : ℕ, higherDirectImageIsoMap hfree hfree' e D D' 0 d ≫
        (higherDirectImageZeroIso E' hfree' D' hn d).hom =
      (higherDirectImageZeroIso E hfree D hn d).hom ≫ (symHom hfree hfree' e.hom).app (d : ℤ)) ∧
    (∀ d : ℤ, d < 0 → higherDirectImageIsoMap hfree hfree' e D D' 0 d = 0) ∧
    (∀ q d : ℤ, q ≠ 0 → q ≠ n → higherDirectImageIsoMap hfree hfree' e D D' q d = 0) ∧
    (∀ d : ℤ,
      haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
      haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
      higherDirectImageIsoMap hfree hfree' e D D' (n : ℤ) d ≫
          (higherDirectImageTopIso E' hfree' D' hn d).hom =
        (higherDirectImageTopIso E hfree D hn d).hom ≫ topRowTargetMap hfree hfree' e d) :=
  ⟨fun d => (congrArg (· ≫ (higherDirectImageZeroIso E' hfree' D' hn d).hom)
      (higherDirectImageIsoMap_zero hfree hfree' e D D' d)).trans
      (higherDirectImageZeroIso_naturality hfree hfree' e D D' hn d),
    fun _ hd => (isZero_higherDirectImage_zero_of_neg E' hfree' D' hn hd).1.eq_of_tgt _ _,
    fun q d hq0 hqn => (isZero_higherDirectImage_twist E' hfree' D' d q hq0 hqn).eq_of_tgt _ _,
    higherDirectImageTopIso_naturality hfree hfree' e D D' hn⟩

end Compatible

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
