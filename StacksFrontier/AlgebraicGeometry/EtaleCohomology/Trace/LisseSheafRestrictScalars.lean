module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# Lisse sheaves and restriction of scalars

Let `X` be a connected scheme of a big étale site with a geometric point `x̄`, `ρ : R →+* S` a
morphism of finite commutative rings, `P` a finite `S`-module and `P'` a finite `R`-module with
continuous actions of `π₁(X, x̄)`. If the underlying finite discrete `π₁`-modules of `P` and `P'`
are identified by `θ`, compatibly with the scalars (multiplication by `ρ(c)` on `P` corresponds to
multiplication by `c` on `P'`), then the lisse sheaf `ℱ_P` of `S`-modules, read as a sheaf of
`R`-modules, is the lisse sheaf `ℱ_{P'}`.

Both sheaves have, by Tag 0DV5 (2), the same underlying abelian sheaf `E⁻¹(P)`, `E` the canonical
equivalence of finite locally constant abelian sheaves with finite discrete `π₁`-modules; and on
it the scalars act, on both sides, as `E⁻¹` of the multiplications. So `E⁻¹(θ)` is `R`-linear.

This is how a lisse sheaf with coefficients in a finite ring `Λ` is compared with a lisse sheaf of
`ℤ/m`-modules, the coefficients over which the cohomology of the Artin–Schreier sheaves is
computed by counting.

## Main definitions

* `Stacks.EtaleCohomology.lisseSheafRestrictScalarsIso`: on the small étale site of Stacks 021B.
* `Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIso`: on Mathlib's small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-- Limits of size `u` of modules in the universe `u + 1`, pinned (the dense subsite equivalence
otherwise leaves a universe constraint unsolved). -/
local instance hasLimitsOfSize_moduleCat_lisseRestrictScalars (Λ : Type) [Ring Λ] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, 0}

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {R S : Type} [CommRing R] [CommRing S] [Finite R] [Finite S] (ρ : R →+* S)
  {P : FiniteTypeContinuousModule.{0, u + 1, u + 1} S (EtaleFundamentalGroup X.1 x)}
  {P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}

/-- The forgetful functor from finite continuous modules to finite discrete modules. -/
local notation "φ" => finiteTypeContinuousModuleForgetAbelian

/-- The canonical equivalence of Tag 0DV5 (2). -/
local notation "𝔈" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

/-- **A scalar-compatible map of the underlying discrete modules gives a map of lisse sheaves of
`R`-modules** `res_ρ ℱ_P ⟶ ℱ_{P'}`: it is `E⁻¹(θ)` on sections. -/
def lisseSheafRestrictScalarsHom (θ : (φ S (EtaleFundamentalGroup X.1 x)).obj P ⟶
      (φ R (EtaleFundamentalGroup X.1 x)).obj P')
    (hθ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P (ρ c)) ≫ θ =
      θ ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P' c)) :
    (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.restrictScalars.{u + 1} ρ)).obj
        ((lisseSheaf B X x S).obj P) ⟶ (lisseSheaf B X x R).obj P' :=
  ObjectProperty.homMk
    { app := fun U => ConcreteCategory.ofHom (C := ModuleCat.{u + 1} R) (show
          (ModuleCat.restrictScalars.{u + 1} ρ).obj (((lisseSheaf B X x S).obj P).obj.obj U) →ₗ[R]
            ((lisseSheaf B X x R).obj P').obj.obj U from
        { toFun := fun s => (((𝔈).inverse.map θ).hom.hom.app U).hom s
          map_add' := fun a b => map_add _ a b
          map_smul' := fun c s => by
            change (((𝔈).inverse.map θ).hom.hom.app U).hom
                ((((𝔈).inverse.map ((φ S _).map
                  (finiteTypeContinuousModuleSMul S P (ρ c)))).hom.hom.app U).hom s) =
              (((𝔈).inverse.map ((φ R _).map
                (finiteTypeContinuousModuleSMul R P' c))).hom.hom.app U).hom
                ((((𝔈).inverse.map θ).hom.hom.app U).hom s)
            have h := congrArg (fun t => (t.hom.hom.app U).hom s)
              ((𝔈).inverse.congr_map (hθ c))
            simp only [Functor.map_comp] at h
            exact h })
      naturality := fun U V f => by
        ext s
        exact congrArg (fun t => t.hom s) (((𝔈).inverse.map θ).hom.hom.naturality f) }

/-- **A scalar-compatible map of the underlying discrete modules gives a map of lisse sheaves of
`R`-modules** `ℱ_{P'} ⟶ res_ρ ℱ_P`. -/
def lisseSheafRestrictScalarsInvHom (θ : (φ R (EtaleFundamentalGroup X.1 x)).obj P' ⟶
      (φ S (EtaleFundamentalGroup X.1 x)).obj P)
    (hθ : ∀ c : R, (φ R _).map (finiteTypeContinuousModuleSMul R P' c) ≫ θ =
      θ ≫ (φ S _).map (finiteTypeContinuousModuleSMul S P (ρ c))) :
    (lisseSheaf B X x R).obj P' ⟶
      (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.restrictScalars.{u + 1} ρ)).obj
        ((lisseSheaf B X x S).obj P) :=
  ObjectProperty.homMk
    { app := fun U => ConcreteCategory.ofHom (C := ModuleCat.{u + 1} R) (show
          ((lisseSheaf B X x R).obj P').obj.obj U →ₗ[R]
            (ModuleCat.restrictScalars.{u + 1} ρ).obj (((lisseSheaf B X x S).obj P).obj.obj U) from
        { toFun := fun s => (((𝔈).inverse.map θ).hom.hom.app U).hom s
          map_add' := fun a b => map_add _ a b
          map_smul' := fun c s => by
            change (((𝔈).inverse.map θ).hom.hom.app U).hom
                ((((𝔈).inverse.map ((φ R _).map
                  (finiteTypeContinuousModuleSMul R P' c))).hom.hom.app U).hom s) =
              (((𝔈).inverse.map ((φ S _).map
                (finiteTypeContinuousModuleSMul S P (ρ c)))).hom.hom.app U).hom
                ((((𝔈).inverse.map θ).hom.hom.app U).hom s)
            have h := congrArg (fun t => (t.hom.hom.app U).hom s)
              ((𝔈).inverse.congr_map (hθ c))
            simp only [Functor.map_comp] at h
            exact h })
      naturality := fun U V f => by
        ext s
        exact congrArg (fun t => t.hom s) (((𝔈).inverse.map θ).hom.hom.naturality f) }

/-- **`res_ρ ℱ_P ≅ ℱ_{P'}`** for an identification `θ` of the underlying finite discrete
`π₁`-modules compatible with the scalars, on the small étale site of Stacks 021B. -/
def lisseSheafRestrictScalarsIso (θ : (φ S (EtaleFundamentalGroup X.1 x)).obj P ≅
      (φ R (EtaleFundamentalGroup X.1 x)).obj P')
    (hθ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P (ρ c)) ≫ θ.hom =
      θ.hom ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P' c)) :
    (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.restrictScalars.{u + 1} ρ)).obj
        ((lisseSheaf B X x S).obj P) ≅ (lisseSheaf B X x R).obj P' where
  hom := lisseSheafRestrictScalarsHom B X x ρ θ.hom hθ
  inv := lisseSheafRestrictScalarsInvHom B X x ρ θ.inv fun c => by
    rw [← cancel_mono θ.hom, Category.assoc, Category.assoc, θ.inv_hom_id, Category.comp_id,
      hθ c, ← Category.assoc, θ.inv_hom_id, Category.id_comp]
  hom_inv_id := by
    ext U s
    have h := congrArg (fun t => (t.hom.hom.app U).hom s)
      (((𝔈).inverse.map_comp θ.hom θ.inv).symm.trans
        ((congrArg (𝔈).inverse.map θ.hom_inv_id).trans ((𝔈).inverse.map_id _)))
    change (((𝔈).inverse.map θ.inv).hom.hom.app U).hom
      ((((𝔈).inverse.map θ.hom).hom.hom.app U).hom s) = s
    exact h
  inv_hom_id := by
    ext U s
    have h := congrArg (fun t => (t.hom.hom.app U).hom s)
      (((𝔈).inverse.map_comp θ.inv θ.hom).symm.trans
        ((congrArg (𝔈).inverse.map θ.inv_hom_id).trans ((𝔈).inverse.map_id _)))
    change (((𝔈).inverse.map θ.hom).hom.hom.app U).hom
      ((((𝔈).inverse.map θ.inv).hom.hom.app U).hom s) = s
    exact h

/-- **`res_ρ ℱ_P ≅ ℱ_{P'}` on Mathlib's small étale site**, for an identification `θ` of the
underlying finite discrete `π₁`-modules compatible with the scalars. Restriction of scalars
commutes on the nose with the restriction along the dense subsite. -/
def lisseEtaleSheafRestrictScalarsIso (θ : (φ S (EtaleFundamentalGroup X.1 x)).obj P ≅
      (φ R (EtaleFundamentalGroup X.1 x)).obj P')
    (hθ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P (ρ c)) ≫ θ.hom =
      θ.hom ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P' c)) :
    (etaleModuleRestrictScalars ρ X.1).obj ((lisseEtaleSheaf B X x S).obj P) ≅
      (lisseEtaleSheaf B X x R).obj P' :=
  let ΦS := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} S)
  let ΦR := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)
  let resB := sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.restrictScalars.{u + 1} ρ)
  (ΦR.counitIso.app _).symm ≪≫
    ΦR.functor.mapIso (Iso.refl (resB.obj (ΦS.inverse.obj (ΦS.functor.obj
        ((lisseSheaf B X x S).obj P)))) ≪≫
      resB.mapIso (ΦS.unitIso.app _).symm ≪≫ lisseSheafRestrictScalarsIso B X x ρ θ hθ)

end Stacks.EtaleCohomology

end
