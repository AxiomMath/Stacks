module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.KoszulTransport
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistMultiplication
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.Tautological

/-!
# The Koszul filtration of a projective bundle under an isomorphism of modules

Let `e : E ≅ E'` be an isomorphism of finite locally free `𝒪_S`-modules of constant rank `n + 1`
and `f : 𝐏(E') ⟶ 𝐏(E)` the induced isomorphism of projective bundles. Pulling back along `f`
carries the twists of `𝐏(E)` to the twists of `𝐏(E')`, compatibly with their multiplication,
the tautological surjection `π^* E ⟶ 𝒪(1)` to the tautological surjection of `𝐏(E')`, and hence
the Koszul filtration of `𝐏(E)` to that of `𝐏(E')`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistPullbackIso`:
  `f^* 𝒪_{𝐏(E)}(d) ≅ 𝒪_{𝐏(E')}(d)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistPullbackIso_twistMul`: compatibility
  with the multiplication of the twists.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-- The component in degree `d` of an isomorphism of sheaves of graded algebras. -/
public def gradedAlgebraIsoApp {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A B : SheafOfModules.GradedAlgebra.{u, u} R} (φ : A ≅ B) (d : ℤ) :
    A.piece d ≅ B.piece d where
  hom := φ.hom.app d
  inv := φ.inv.app d
  hom_inv_id := by
    rw [← SheafOfModules.GradedAlgebra.categoryStruct_comp_app, φ.hom_inv_id,
      SheafOfModules.GradedAlgebra.categoryStruct_id_app]
  inv_hom_id := by
    rw [← SheafOfModules.GradedAlgebra.categoryStruct_comp_app, φ.inv_hom_id,
      SheafOfModules.GradedAlgebra.categoryStruct_id_app]

/-- The twist `𝒪(d)` of a relative `Proj`, as a module on its scheme. -/
public abbrev twistPiece {S : Scheme.{u}} {A : SheafGradedAlgebra S} (D : TwistData A) (d : ℤ) :
    (relativeProj A).scheme.Modules :=
  D.algebra.piece d


variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree'))

/-- **`f^* 𝒪_{𝐏(E)}(d) ≅ 𝒪_{𝐏(E')}(d)`**, for the isomorphism `f : 𝐏(E') ⟶ 𝐏(E)` induced by `e`:
pullback along an open immersion is restriction, and the restricted twists are the twists of
`𝐏(E')` by `bundleTwistIso`. -/
public def twistPullbackIso (d : ℤ) :
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).obj (twistPiece D d) ≅
      twistPiece D' d :=
  ((Scheme.Modules.restrictFunctorIsoPullback (bundleMap hfree hfree' e)).app _).symm ≪≫
    gradedAlgebraIsoApp (bundleTwistIso hfree hfree' e D D') d

/-- `twistPullbackIso` on the pullback of a section: restriction, then `bundleTwistIso`. -/
public theorem twistPullbackIso_pullbackUnit (d : ℤ)
    (U : (relativeProj (bundleAlgebra E hfree)).scheme.Opens)
    (s : (twistPiece D d).val.obj (op U)) :
    (twistPullbackIso hfree hfree' e D D' d).hom.val.app
        (op (bundleMap hfree hfree' e ⁻¹ᵁ U))
        (pullbackUnit (bundleMap hfree hfree' e).toLRSHom.toShHom (twistPiece D d) (op U) s) =
      ((bundleTwistIso hfree hfree' e D D').hom.app d).val.app
        (op (bundleMap hfree hfree' e ⁻¹ᵁ U))
        ((twistPiece D d).val.presheaf.map
          (homOfLE ((bundleMap hfree hfree' e).image_preimage_le U)).op s) := by
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  refine congrArg (((bundleTwistIso hfree hfree' e D D').hom.app d).val.app _) ?_
  refine Eq.trans (congrArg (((Scheme.Modules.restrictFunctorIsoPullback
    (bundleMap hfree hfree' e)).app _).inv.val.app _)
      (Stacks.AlgebraicGeometry.ProjMapCard.pullbackUnit_eq_restrictFunctorIsoPullback
        (bundleMap hfree hfree' e) (twistPiece D d) U s)) ?_
  exact Stacks.SheafOfModules.inv_val_app_hom_val_app
    ((Scheme.Modules.restrictFunctorIsoPullback (bundleMap hfree hfree' e)).app _) _ _

/-- `twistPullbackIso` is multiplicative on pulled-back sections. -/
public theorem twistPullbackIso_mul (i j : ℤ)
    (U : (relativeProj (bundleAlgebra E hfree)).scheme.Opens)
    (x : (twistPiece D i).val.obj (op U)) (y : (twistPiece D j).val.obj (op U)) :
    (twistPullbackIso hfree hfree' e D D' (i + j)).hom.val.app
        (op (bundleMap hfree hfree' e ⁻¹ᵁ U))
        (pullbackUnit (bundleMap hfree hfree' e).toLRSHom.toShHom (twistPiece D (i + j)) (op U)
          ((D.algebra.mul i j).app (op U) x y)) =
      (D'.algebra.mul i j).app (op (bundleMap hfree hfree' e ⁻¹ᵁ U))
        ((twistPullbackIso hfree hfree' e D D' i).hom.val.app (op (bundleMap hfree hfree' e ⁻¹ᵁ U))
          (pullbackUnit (bundleMap hfree hfree' e).toLRSHom.toShHom (twistPiece D i) (op U) x))
        ((twistPullbackIso hfree hfree' e D D' j).hom.val.app (op (bundleMap hfree hfree' e ⁻¹ᵁ U))
          (pullbackUnit (bundleMap hfree hfree' e).toLRSHom.toShHom (twistPiece D j) (op U)
            y)) := by
  refine Eq.trans (twistPullbackIso_pullbackUnit hfree hfree' e D D' (i + j) U _) ?_
  refine Eq.trans (congrArg (((bundleTwistIso hfree hfree' e D D').hom.app (i + j)).val.app _)
    ((D.algebra.mul i j).naturality
      (homOfLE ((bundleMap hfree hfree' e).image_preimage_le U)).op x y)) ?_
  refine Eq.trans ((bundleTwistIso hfree hfree' e D D').hom.map_mul i j _ _ _) ?_
  exact congrArg₂ (fun a b => (D'.algebra.mul i j).app _ a b)
    (twistPullbackIso_pullbackUnit hfree hfree' e D D' i U x).symm
    (twistPullbackIso_pullbackUnit hfree hfree' e D D' j U y).symm

/-- **The identification of the twists is compatible with their multiplication**:
`f^*(𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j))` is `𝒪'(i) ⊗ 𝒪'(j) ⟶ 𝒪'(i + j)` under `twistPullbackIso` and the
comparison of Tag 01CD. -/
public theorem twistPullbackIso_twistMul (i j : ℤ) :
    (pullbackFunctor (bundleMap hfree hfree' e).toLRSHom.toShHom).map (twistMul D i j) ≫
        (twistPullbackIso hfree hfree' e D D' (i + j)).hom =
      Stacks.RingedSpace.comparison (bundleMap hfree hfree' e).toLRSHom.toShHom
          (twistPiece D i) (twistPiece D j) ≫
        tensorMap (twistPullbackIso hfree hfree' e D D' i).hom
          (twistPullbackIso hfree hfree' e D D' j).hom ≫ twistMul D' i j :=
  pullback_mulSheaf (bundleMap hfree hfree' e).toLRSHom.toShHom (A := D.algebra) (B := D'.algebra)
    (fun d => (twistPullbackIso hfree hfree' e D D' d).hom) i j
    (fun U x y => twistPullbackIso_mul hfree hfree' e D D' i j (Opposite.unop U) x y)

/-- The tautological surjection `π^* E ⟶ 𝒪(1)` of the projective bundle of a finite locally free
`E`. -/
public abbrev bundleTautological {F : S.Modules} {r : ℕ}
    (hF : Scheme.Modules.IsFiniteLocallyFreeOfRank F r) (DF : TwistData (bundleAlgebra F hF)) :
    (Scheme.Modules.pullback (relativeProj (bundleAlgebra F hF)).toBase).obj F ⟶
      twistPiece DF ((1 : ℕ) : ℤ) :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank F hF
  tautologicalMap F _ DF

/-- `Sym¹(e)` on the generator. -/
public theorem symHom_gen :
    (Scheme.Modules.symmetricAlgebraGenIso S E).hom ≫ (symHom hfree hfree' e.hom).app 1 =
      e.hom ≫ (Scheme.Modules.symmetricAlgebraGenIso S E').hom :=
  Scheme.Modules.symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom S e.hom

/-- **The tautological surjections correspond**: under `f` and `e`, the tautological map
`π^* E ⟶ 𝒪(1)` of `𝐏(E)` is that of `𝐏(E')`. -/
public theorem tautologicalMap_pullback :
    (Scheme.Modules.pullback (bundleMap hfree hfree' e)).map (bundleTautological hfree D) ≫
        (twistPullbackIso hfree hfree' e D D' ((1 : ℕ) : ℤ)).hom =
      (pullbackPullbackIso (bundleMap hfree hfree' e) _ _ (bundleMap_comp_toBase hfree hfree' e)
          E).hom ≫ (Scheme.Modules.pullback (relativeProj (bundleAlgebra E' hfree')).toBase).map
          e.hom ≫ bundleTautological hfree' D' := by
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E' hfree'
  have key := pullback_homEquiv_symm (bundleMap hfree hfree' e) _ _
    (bundleMap_comp_toBase hfree hfree' e) (twistPullbackIso hfree hfree' e D D' ((1 : ℕ) : ℤ)).hom
    ((Scheme.Modules.symmetricAlgebraGenIso S E).hom ≫ D.ψ 1)
    (e.hom ≫ (Scheme.Modules.symmetricAlgebraGenIso S E').hom ≫ D'.ψ 1) ?_
  · refine key.trans ?_
    have hT : bundleTautological hfree' D' =
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (relativeProj (bundleAlgebra E' hfree')).toBase).homEquiv _ _).symm
          ((Scheme.Modules.symmetricAlgebraGenIso S E').hom ≫ D'.ψ 1) := rfl
    rw [hT]
    exact comp_homEquiv_symm_comp (p' := (relativeProj (bundleAlgebra E' hfree')).toBase)
      (pullbackPullbackIso (bundleMap hfree hfree' e) _ _
          (bundleMap_comp_toBase hfree hfree' e) E).hom e.hom
      ((Scheme.Modules.symmetricAlgebraGenIso S E').hom ≫ D'.ψ 1)
  · intro U s
    refine pullbackUnit_restrict_comp (bundleMap hfree hfree' e) _ _
      (bundleMap_comp_toBase hfree hfree' e)
      ((bundleTwistIso hfree hfree' e D D').hom.app ((1 : ℕ) : ℤ)) _ _ ?_ U s
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Scheme.Modules.symmetricAlgebraGenIso S E).hom ≫ ·)
      (bundleTwistIso_psi hfree hfree' e D D' 1)).trans ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ D'.ψ 1) (symHom_gen hfree hfree' e))).trans (Category.assoc _ _ _)


end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
