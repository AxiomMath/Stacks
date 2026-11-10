module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeTrace

/-!
# The pairing of the top row of Tag 01XX under base change

Let `b : 𝐏(E') ⟶ 𝐏(E)` be the morphism of projective bundles over `g : S' ⟶ S`, `E' ≅ g^*E`.
The homogeneous-section maps `π^* Sym^k(E) ⟶ 𝒪(k)` correspond under `b`, and so do the
multiplication pairings `𝒪(d) ⊗ π^* Sym^k(E) ⟶ 𝒪(d + k)` and their curried forms
`𝒪(d) ⟶ 𝒪(d + k) ⊗ π^*(Sym^k(E)^∨)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))

/-- `b^* π^* Sym^k(E) ≅ π'^* g^* Sym^k(E) ≅ π'^* Sym^k(E')`. -/
public abbrev symSquareIso (k : ℤ) :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece k)) ≅
      (Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece k) :=
  squarePullbackIso (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) _ ≪≫
    (Scheme.Modules.pullback
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).mapIso
      (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app k)
        (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE k))

/-- **The homogeneous-section maps correspond under base change**: `b^*(π^* Sym^k(E) ⟶ 𝒪(k))`
followed by `θ♯` is `b^* π^* Sym^k(E) ≅ π'^* Sym^k(E')` followed by
`π'^* Sym^k(E') ⟶ 𝒪'(k)`. -/
public theorem psiFlat_baseChange (k : ℕ) :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map (psiFlat E hqc D k) ≫
        thetaSharp g E hqc E' hqc' hE D D' (k : ℤ) =
      (symSquareIso g E hqc E' hqc' hE (k : ℤ)).hom ≫ psiFlat E' hqc' D' k := by
  have key := pullback_homEquiv_symm (bundleBaseChange g E hqc E' hqc' hE) _ _
    (bundleBaseChange_toBase g E hqc E' hqc' hE) (thetaSharp g E hqc E' hqc' hE D D' (k : ℤ))
    (D.ψ k)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)) ≫
      (Scheme.Modules.pushforward g).map
        ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (k : ℤ) ≫ D'.ψ k) ≫
      (Scheme.Modules.pushforwardComp
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase g).hom.app
          (D'.algebra.piece (k : ℤ))) ?_
  · refine key.trans ?_
    have hc := homEquiv_symm_comp_pushforward
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase g
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))
      (D'.algebra.piece (k : ℤ))
      ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (k : ℤ)) (D'.ψ k)
    refine (congrArg (_ ≫ ·) hc).trans ?_
    simp only [symSquareIso, squarePullbackIso, pullbackPullbackIso, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc]
    rfl
  · intro U s
    have hθ := thetaSharp_pbUnit g E hqc E' hqc' hE D D' (k : ℤ)
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
      ((D.ψ k).val.app (op U) s)
    have hψ := congrArg (fun φ => φ.val.app (op U) s) (psi_comp_thetaFlat g E hqc E' hqc' hE D D' k)
    have hsq :=
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso_hom_app_app
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
        (D'.algebra.piece (k : ℤ)) U
    have hr : ∀ (h : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ
          (g ⁻¹ᵁ U) ≤ bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
            ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
        (t : (D'.algebra.piece (k : ℤ)).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
          ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)))),
        (D'.algebra.piece (k : ℤ)).val.presheaf.map (homOfLE h).op t =
          (((Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
            (bundleBaseChange g E hqc E' hqc' hE)
            (bundleBaseChange_toBase g E hqc E' hqc' hE)).hom.app
              (D'.algebra.piece (k : ℤ))).app U) t := fun h t => by
      rw [hsq]
      exact congrArg (fun f => (D'.algebra.piece (k : ℤ)).val.presheaf.map f t)
        (Subsingleton.elim _ _)
    refine (hr _ _).trans ?_
    refine (congrArg _ hθ).trans ?_
    exact hψ


/-- The multiplication pairing is `𝟙 ⊗ ψ♭` followed by the twist multiplication. -/
private theorem twistPairing_eq_tensorMap_comp {S : Scheme.{u}} (E : S.Modules)
    (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
    (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
    (k : ℕ) (d e : ℤ) (he : d + k = e) :
    twistPairing E hqc D k d e he =
      tensorMap (Z := (bundle E hqc).toRingedSpace) (𝟙 (D.algebra.piece d)) (psiFlat E hqc D k) ≫
        twistMul D d k ≫ eqToHom (congrArg D.algebra.piece he) :=
  congrArg (· ≫ twistMul D d k ≫ eqToHom (congrArg D.algebra.piece he))
    (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩)
      (D.algebra.piece d) (psiFlat E hqc D k)).symm

/-- **The multiplication pairing under base change**: `b^*(𝒪(d) ⊗ π^* Sym^k(E) ⟶ 𝒪(e))` followed
by `θ♯` is `b^*(𝒪(d) ⊗ π^* Sym^k(E)) ≅ 𝒪'(d) ⊗ π'^* Sym^k(E')` followed by the pairing of
`𝐏(E')`. -/
public theorem twistPairing_baseChange (k : ℕ) (d e : ℤ) (he : d + k = e) :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
        (twistPairing E hqc D k d e he) ≫ thetaSharp g E hqc E' hqc' hE D D' e =
      (tensorPullbackIsoT (bundleBaseChange g E hqc E' hqc' hE)
          (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' d)
            (isIso_thetaSharp g E hqc E' hqc' hE D D' d))
          (symSquareIso g E hqc E' hqc' hE (k : ℤ))).hom ≫
        twistPairing E' hqc' D' k d e he := by
  refine (congrArg (fun t => (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map t ≫
    thetaSharp g E hqc E' hqc' hE D D' e)
    (twistPairing_eq_tensorMap_comp E hqc D k d e he)).trans
    (Eq.trans ?_ (congrArg (_ ≫ ·) (twistPairing_eq_tensorMap_comp E' hqc' D' k d e he).symm))
  exact pairing_pullbackT (bundleBaseChange g E hqc E' hqc' hE)
      (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' d)
        (isIso_thetaSharp g E hqc E' hqc' hE D D' d))
      (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' (k : ℤ))
        (isIso_thetaSharp g E hqc E' hqc' hE D D' (k : ℤ)))
      (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' (d + (k : ℤ)))
        (isIso_thetaSharp g E hqc E' hqc' hE D D' (d + (k : ℤ))))
      (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' e)
        (isIso_thetaSharp g E hqc E' hqc' hE D D' e))
      (symSquareIso g E hqc E' hqc' hE (k : ℤ)) (psiFlat E hqc D k) (psiFlat E' hqc' D' k)
      (twistMul D d (k : ℤ)) (twistMul D' d (k : ℤ)) (eqToHom (congrArg D.algebra.piece he))
      (eqToHom (congrArg D'.algebra.piece he)) (psiFlat_baseChange g E hqc E' hqc' hE D D' k)
      (thetaSharp_twistMul g E hqc E' hqc' hE D D' d (k : ℤ))
      (twist_eqToHom_pullback (bundleBaseChange g E hqc E' hqc' hE)
        (fun d => @asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' d)
          (isIso_thetaSharp g E hqc E' hqc' hE D D' d)) he)

/-- `b^* π^*(Sym^k(E)^∨) ≅ π'^* g^*(Sym^k(E)^∨) ≅ π'^*(Sym^k(E')^∨)`. -/
public abbrev symDualSquareIso (k : ℤ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece k)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece k)] :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece k))) ≅
      (Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece k)) :=
  squarePullbackIso (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) _ ≪≫
    (Scheme.Modules.pullback
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).mapIso
      (pullbackDualIsoOf g _
        (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app k)
          (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE k)) inferInstance)


private theorem iso_square_swap {C : Type*} [Category C] {A B A' B' : C} (P : A ≅ A')
    (Q : B ≅ B') {Γ : A' ⟶ B'} {R : A ⟶ B} (h : Γ ≫ Q.inv = P.inv ≫ R) :
    P.hom ≫ Γ = R ≫ Q.hom := by
  rw [(Iso.comp_inv_eq Q).mp h]
  simp

section Curry

variable (k : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ))]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ)))]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ)))] in
/-- `b^*(π^*Sym^k(E)^∨ ≅ π^*(Sym^k(E)^∨))` against `π'^* Sym^k(E')^∨ ≅ π'^*(Sym^k(E')^∨)`. -/
public theorem pullbackDualSheafIso_inv_baseChange :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
        (Stacks.FundamentalGroup.pullbackDualSheafIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase _
          inferInstance).inv ≫
        (symDualSquareIso g E hqc E' hqc' hE (k : ℤ)).hom =
      (pullbackDualIsoOf (bundleBaseChange g E hqc E' hqc' hE) _
          (symSquareIso g E hqc E' hqc' hE (k : ℤ)) inferInstance).hom ≫
        (Stacks.FundamentalGroup.pullbackDualSheafIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase _
          inferInstance).inv := by
  have hsq := pullbackDualIsoOf_square
    (N' := (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (k : ℤ))
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))
    (@asIso _ _ _ _ ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (k : ℤ))
      (Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (k : ℤ)))
  have hk0 : (symDualSquareIso g E hqc E' hqc' hE (k : ℤ)).hom ≫
      (Stacks.FundamentalGroup.pullbackDualSheafIso
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase _
        inferInstance).hom =
      ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).mapIso
        (Stacks.FundamentalGroup.pullbackDualSheafIso
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase _
          inferInstance)).hom ≫
        (pullbackDualIsoOf (bundleBaseChange g E hqc E' hqc' hE) _
          (symSquareIso g E hqc E' hqc' hE (k : ℤ)) inferInstance).hom :=
    (Category.assoc _ _ _).trans hsq
  exact iso_square_swap ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).mapIso
    (Stacks.FundamentalGroup.pullbackDualSheafIso
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase _ inferInstance)).symm
    (Stacks.FundamentalGroup.pullbackDualSheafIso
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase _
      inferInstance).symm hk0

/-- **The curried multiplication pairing under base change**: the morphism
`𝒪(d) ⟶ SheafHom(π^* Sym^k(E), 𝒪(e)) ≅ 𝒪(e) ⊗ π^*(Sym^k(E)^∨)` of the top row pulls back along `b`
to the same morphism for `E'`, along `θ♯` and `b^* π^*(Sym^k(E)^∨) ≅ π'^*(Sym^k(E')^∨)`. -/
public theorem twistPairingCurry_baseChange (d e : ℤ) (he : d + k = e) :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
        (twistPairingCurry E hqc D k d e he ≫
          (sheafHomIsoTensorDual _ (D.algebra.piece e)).hom ≫
          tensorMap (Z := (bundle E hqc).toRingedSpace)
            (𝟙 (D.algebra.piece e)) (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase _
              inferInstance).inv) ≫
        (tensorPullbackIsoT (bundleBaseChange g E hqc E' hqc' hE)
          (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' e)
            (isIso_thetaSharp g E hqc E' hqc' hE D D' e))
          (symDualSquareIso g E hqc E' hqc' hE (k : ℤ))).hom =
      thetaSharp g E hqc E' hqc' hE D D' d ≫
        twistPairingCurry E' hqc' D' k d e he ≫
          (sheafHomIsoTensorDual _ (D'.algebra.piece e)).hom ≫
          tensorMap (Z := (bundle E' hqc').toRingedSpace)
            (𝟙 (D'.algebra.piece e)) (Stacks.FundamentalGroup.pullbackDualSheafIso
              (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase _
              inferInstance).inv :=
  curry_dual_pullback (bundleBaseChange g E hqc E' hqc' hE)
    (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' d)
      (isIso_thetaSharp g E hqc E' hqc' hE D D' d))
    (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' e)
      (isIso_thetaSharp g E hqc E' hqc' hE D D' e))
    (symSquareIso g E hqc E' hqc' hE (k : ℤ)) (symDualSquareIso g E hqc E' hqc' hE (k : ℤ))
    _ _ (pullbackDualSheafIso_inv_baseChange g E hqc E' hqc' hE k)
    (twistPairing E hqc D k d e he) (twistPairing E' hqc' D' k d e he)
    (twistPairing_baseChange g E hqc E' hqc' hE D D' k d e he)

end Curry

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
