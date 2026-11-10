module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeKoszul
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DeterminantBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectionFormulaBaseChange

/-!
# The trace of the Koszul filtration under base change

Let `b : 𝐏(E') ⟶ 𝐏(E)` be the morphism of projective bundles over `g : S' ⟶ S`, `E' ≅ g^*E`, both
of constant rank `n + 1`. The last step of the twisted Koszul filtration,
`⋀ⁿ K ⊗ 𝒪(-n) ≅ 𝒪(-n-1) ⊗ π^* ⋀ⁿ⁺¹ E`, pulls back along `b` to the last step for `E'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))
  {n : ℕ} (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1))

/-- `b^* π^* ⋀ᵐ E ≅ π'^* ⋀ᵐ E'` for the base change of projective bundles. -/
public abbrev bundleDetBaseChange (m : ℤ) :=
  detSquareIso (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) g (bundleBaseChange_toBase g E hqc E' hqc' hE) E E' hE m

include hfree hfree' in
/-- **The last step of the twisted Koszul filtration under base change**:
`⋀ⁿ K ⊗ 𝒪(-n) ≅ 𝒪(-n-1) ⊗ π^* ⋀ⁿ⁺¹ E` pulls back along `b` to the same isomorphism for `E'`. -/
public theorem koszulTopStep_baseChange :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
        ((koszulTwistIso E hqc D n).inv ≫
          (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
            (isIso_koszulTwistSequence_g E hqc D hfree)).inv ≫
          (koszulMiddleIso E hqc D (n + 1) (n + 1)).hom) ≫
        (tensorPullbackIso (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom
          (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' (-((n + 1 : ℕ) : ℤ)))
            (isIso_thetaSharp g E hqc E' hqc' hE D D' _))
          (bundleDetBaseChange g E hqc E' hqc' hE ((n + 1 : ℕ) : ℤ))).hom =
      (koszulTermBaseChange g E hqc E' hqc' hE D D' n).hom ≫
        ((koszulTwistIso E' hqc' D' n).inv ≫ (@asIso _ _ _ _ (koszulTwistSequence E' hqc' D' n).g
          (isIso_koszulTwistSequence_g E' hqc' D' hfree')).inv ≫
          (koszulMiddleIso E' hqc' D' (n + 1) (n + 1)).hom) :=
  koszulTopStep_pullback_of (bundleBaseChange g E hqc E' hqc' hE)
    (fun d => asIso (thetaSharp g E hqc E' hqc' hE D D' d))
    (bundlePullbackBaseChange g E hqc E' hqc' hE)
    (tautologicalMap_baseChange g E hqc E' hqc' hE D D')
    (fun i j => thetaSharp_twistMul g E hqc E' hqc' hE D D' i j)
    (tautKernelBaseChange g E hqc E' hqc' hE D D') (tautKernelBaseChange_ι g E hqc E' hqc' hE D D')
    hfree hfree' (bundleDetBaseChange g E hqc E' hqc' hE ((n + 1 : ℕ) : ℤ))
    (detSquareIso_compat _ _ _ g (bundleBaseChange_toBase g E hqc E' hqc' hE) E E' hE _)


/-- The diagram chase behind `koszulTopIso_baseChange`. -/
private theorem topIso_chase {C C' : Type*} [Category C] [Category C'] (F : C' ⥤ C)
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ Q₀ Q₁ : C} {K M N₁ N₂ N₃ K' : C'}
    {top : P₀ ⟶ P₃} {gC : P₀ ⟶ P₁} {gS : P₁ ⟶ P₂} {gP : P₂ ⟶ P₃} {cmp : P₃ ⟶ P₄}
    {tL : P₄ ⟶ P₇} {t₁ : P₄ ⟶ P₅} {t₂ : P₅ ⟶ P₆} {t₃ : P₆ ⟶ P₇}
    {bcK : P₁ ⟶ F.obj K} {bcM : P₂ ⟶ F.obj M} {bs : K ⟶ M} {cs : M ⟶ N₁} {θ₁ : N₁ ⟶ N₂}
    {d₁ : N₂ ⟶ N₃} {kt : K ⟶ K'} {st : K' ⟶ N₃} {pf₁ : F.obj N₁ ⟶ P₅} {pf₂ : F.obj N₂ ⟶ P₆}
    {pf₃ : F.obj N₃ ⟶ P₇} {bc₀ : P₀ ⟶ Q₀} {r₀ : Q₀ ⟶ Q₁} {ch : Q₁ ⟶ F.obj K'} {top' : Q₁ ⟶ P₇}
    (hL : top = gC ≫ gS ≫ gP) (hTL : tL = t₁ ≫ t₂ ≫ t₃)
    (hPF : gP ≫ cmp ≫ t₁ = bcM ≫ F.map cs ≫ pf₁) (hNF : F.map θ₁ ≫ pf₂ = pf₁ ≫ t₂)
    (hNG : pf₂ ≫ t₃ = F.map d₁ ≫ pf₃) (hNat : gS ≫ bcM = bcK ≫ F.map bs)
    (hTS : bs ≫ cs ≫ θ₁ ≫ d₁ = kt ≫ st) (hC : gC ≫ bcK ≫ F.map kt = bc₀ ≫ r₀ ≫ ch)
    (hR : top' = ch ≫ F.map st ≫ pf₃) :
    top ≫ cmp ≫ tL = bc₀ ≫ r₀ ≫ top' := by
  have hPF' : gP ≫ cmp ≫ t₁ ≫ t₂ ≫ t₃ = bcM ≫ F.map cs ≫ F.map θ₁ ≫ F.map d₁ ≫ pf₃ := by
    rw [← hNG, reassoc_of% hNF, ← reassoc_of% hPF]
  have hTS' : F.map bs ≫ F.map cs ≫ F.map θ₁ ≫ F.map d₁ = F.map kt ≫ F.map st := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg F.map hTS
  subst hL hTL hR
  simp only [Category.assoc]
  rw [hPF', reassoc_of% hNat, reassoc_of% hTS', reassoc_of% hC]

/-- Tensoring with the identity on the left is the flipped `sheafTensor` applied to the object. -/
private theorem tensorMap_id_left_eq_app {Z : RingedSpace.{u, u}}
    {A B B' : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z)} (y : B ⟶ B') :
    tensorMap (𝟙 A) y =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.map y).app A :=
  Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) A y

/-- A tensor product of morphisms, split along a composite in the second factor; the last
factor is tensoring `A'` with `y₂`. -/
public theorem tensorMap_split₂ {Z : RingedSpace.{u, u}}
    {A A' B B' B'' : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z)}
    (x : A ⟶ A') (y₁ : B ⟶ B') (y₂ : B' ⟶ B'') :
    tensorMap x (y₁ ≫ y₂) = tensorMap (𝟙 A) y₁ ≫ tensorMap x (𝟙 B') ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.map y₂).app A' := by
  refine Eq.trans ?_ (congrArg (_ ≫ _ ≫ ·) (tensorMap_id_left_eq_app _))
  rw [tensorMap_comp, tensorMap_comp]
  simp

/-- The tensor isomorphism of `koszulTopStep_baseChange`, split into its three factors. -/
public theorem tensorPullbackIso_bundleDet_hom :
    (tensorPullbackIso (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom
        (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' (-((n + 1 : ℕ) : ℤ)))
          (isIso_thetaSharp g E hqc E' hqc' hE D D' _))
        (bundleDetBaseChange g E hqc E' hqc' hE ((n + 1 : ℕ) : ℤ))).hom =
      Stacks.RingedSpace.comparison (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom
          (negTwist E hqc D (n + 1))
          ((Scheme.Modules.pullback (relativeProj
            (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
            (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))) ≫
        tensorMap (𝟙 _) (squarePullbackIso (relativeProj
          (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).hom ≫
      (Stacks.ProjectionFormula.tensorRightInvertible (bundle E' hqc')
          ((Scheme.Modules.pullback (relativeProj
            (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj
            ((Scheme.Modules.pullback g).obj
              (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))))).map
          (thetaSharp g E hqc E' hqc' hE D D' (-((n + 1 : ℕ) : ℤ))) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (bundle E' hqc').toRingedSpace.sheaf).flip.map
          ((Scheme.Modules.pullback (relativeProj
            (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).map
            (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ)).hom)).app (negTwist E' hqc' D' (n + 1)) := by
  have hdsi : (bundleDetBaseChange g E hqc E' hqc' hE ((n + 1 : ℕ) : ℤ)).hom =
      (squarePullbackIso (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).hom ≫
        (Scheme.Modules.pullback (relativeProj
          (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).map
          (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ)).hom := by
    simp [bundleDetBaseChange, detSquareIso, squarePullbackIso, pullbackPullbackIso]
  exact (congrArg (fun t => Stacks.RingedSpace.comparison _ _ _ ≫ tensorMap _ t) hdsi).trans
    (congrArg (Stacks.RingedSpace.comparison _ _ _ ≫ ·) (tensorMap_split₂ _ _ _))


/-- A tensor product of morphisms, split along a composite in the first factor; the last
factor is tensoring `A''` with `y`. -/
public theorem tensorMap_split₁ {Z : RingedSpace.{u, u}}
    {A A' A'' B B' : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z)}
    (x₁ : A ⟶ A') (x₂ : A' ⟶ A'') (y : B ⟶ B') :
    tensorMap (x₁ ≫ x₂) y = tensorMap x₁ (𝟙 B) ≫ tensorMap x₂ (𝟙 B) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.map y).app A'' := by
  refine Eq.trans ?_ (congrArg (_ ≫ _ ≫ ·) (tensorMap_id_left_eq_app _))
  rw [tensorMap_comp, tensorMap_comp]
  simp

include hfree hfree' in
/-- **The trace isomorphism of the Koszul filtration is compatible with base change**: under the
base change maps, `π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E` corresponds to the same
isomorphism for `E'`, along `g^* ⋀ⁿ⁺¹ E ≅ ⋀ⁿ⁺¹ E'`. -/
public theorem koszulTopIso_baseChange (hn : 1 ≤ n) :
    (Scheme.Modules.pullback g).map (koszulTopIso E hqc D hn hfree).hom ≫
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
          (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ)).hom =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
          (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) 0
          (koszulTerm E hqc D 0) ≫
        ((bundlePushforward E' hqc').rightDerived 0).map
          (koszulTermBaseChange g E hqc E' hqc' hE D D' 0).hom ≫
        (koszulTopIso E' hqc' D' hn hfree').hom := by
  have := isFiniteLocallyFree_of_rank E hfree
  have := isFiniteLocallyFree_of_rank E' hfree'
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E (n + 1)
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E' (n + 1)
  have hL := koszulTopIso_hom (E := E) (hqc := hqc) (D := D) hn hfree
  have hR := koszulTopIso_hom (E := E') (hqc := hqc') (D := D') hn hfree'
  have hL' := congrArg (Scheme.Modules.pullback g).map hL
  rw [Functor.map_comp, Functor.map_comp] at hL'
  exact topIso_chase ((bundlePushforward E' hqc').rightDerived n) hL'
    (tensorMap_split₁ _ _ _)
    (projectionFormula_higherBaseChangeNat
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) n (negTwist E hqc D (n + 1)))
    (projectionFormulaDeltaApp_naturality
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      ((Scheme.Modules.pullback g).obj (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))) n
      (thetaSharp g E hqc E' hqc' hE D D' (-((n + 1 : ℕ) : ℤ))))
    (projectionFormulaDeltaApp_naturality_right
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (detBaseIso g E E' hE ((n + 1 : ℕ) : ℤ)).hom (negTwist E' hqc' D' (n + 1)) n)
    (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChangeNat_naturality
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) n _)
    ((congrArg (_ ≫ ·) (tensorPullbackIso_bundleDet_hom g E hqc E' hqc' hE D D'
      (n := n))).symm.trans (koszulTopStep_baseChange g E hqc E' hqc' hE D D' hfree hfree'))
    (koszulChainIso_baseChange g E hqc E' hqc' hE D D' hn hfree hfree' n le_rfl) hR

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
