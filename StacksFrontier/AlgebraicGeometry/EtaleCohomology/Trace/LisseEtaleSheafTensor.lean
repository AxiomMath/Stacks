module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDescDense

/-!
# Tensor pairings of lisse sheaves on Mathlib's small étale site

Let `X` be a connected scheme of a big étale site with a geometric point `x̄`, `Λ` a finite
commutative ring and `μ : P × Q → R` a `π₁(X, x̄)`-equivariant `Λ`-bilinear map of finite
continuous `Λ`-modules. Tag 0DV5 gives a natural bilinear pairing of sections `ℱ_P × ℱ_Q → ℱ_R`
on the small étale category of Stacks 021B (`Stacks.EtaleCohomology.lisseSheafBilinear`). This
file transports it to Mathlib's small étale site, where the lisse sheaves are read
(`Stacks.EtaleCohomology.lisseEtaleSheaf`): the former is a dense subsite of the latter, so the
pairing extends (`CategoryTheory.Sheaf.denseExtensionBilinear`) and defines a morphism of sheaves
`ℱ_P ⊗ ℱ_Q ⟶ ℱ_R` out of the tensor product of `CategoryTheory.Sheaf.monoidalCategory`.

## Main definitions

* `Stacks.EtaleCohomology.lisseEtaleSheafBilinear`: the pairing of sections on Mathlib's site.
* `Stacks.EtaleCohomology.lisseEtaleSheafTensorHom`: the morphism `ℱ_P ⊗ ℱ_Q ⟶ ℱ_R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-- Limits of the size of the site in the large-universe module category, with its universes
fixed. -/
local instance lisseEtaleSheafTensor_hasLimitsOfSize (Λ : Type) [Ring Λ] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, 0}

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]
  {P Q R : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}

variable (μ : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
  (hμ : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
    μ ((P.obj.obj.obj.ρ g).hom a) ((Q.obj.obj.obj.ρ g).hom b) = (R.obj.obj.obj.ρ g).hom (μ a b))

/-- The pairing of sections of `lisseSheafBilinear` on the objects of the small étale category of
Stacks 021B, read through the unit of the equivalence with Mathlib's small étale site. -/
def lisseEtaleSheafSubsiteBilinear (U : (SmallEtale B X.1 X.2)ᵒᵖ) :
    ((lisseEtaleSheaf B X x Λ).obj P).obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U) →ₗ[Λ]
      ((lisseEtaleSheaf B X x Λ).obj Q).obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U) →ₗ[Λ]
        ((lisseEtaleSheaf B X x Λ).obj R).obj.obj
          ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U) :=
  ((lisseSheafBilinear B X x Λ μ hμ U).compl₁₂
      (((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unitInv.app
        ((lisseSheaf B X x Λ).obj P)).hom.app U).hom
      (((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unitInv.app
        ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom).compr₂
    (((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app
      ((lisseSheaf B X x Λ).obj R)).hom.app U).hom

/-- `lisseEtaleSheafSubsiteBilinear` is natural: restricting the pairing of `a` and `b` along
`f : U ⟶ V` gives the pairing of their restrictions. -/
theorem lisseEtaleSheafSubsiteBilinear_naturality {U V : (SmallEtale B X.1 X.2)ᵒᵖ} (f : U ⟶ V)
    (a : ((lisseEtaleSheaf B X x Λ).obj P).obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U))
    (b : ((lisseEtaleSheaf B X x Λ).obj Q).obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)) :
    ((lisseEtaleSheaf B X x Λ).obj R).obj.map ((SmallEtale.toEtaleSite B X.1 X.2).op.map f)
        (lisseEtaleSheafSubsiteBilinear B X x Λ μ hμ U a b) =
      lisseEtaleSheafSubsiteBilinear B X x Λ μ hμ V
        (((lisseEtaleSheaf B X x Λ).obj P).obj.map ((SmallEtale.toEtaleSite B X.1 X.2).op.map f) a)
        (((lisseEtaleSheaf B X x Λ).obj Q).obj.map
          ((SmallEtale.toEtaleSite B X.1 X.2).op.map f) b) := by
  let E := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)
  have key : ∀ {G H : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ)} (φ : G ⟶ H)
      (c : G.obj.obj U), φ.hom.app V (G.obj.map f c) = H.obj.map f (φ.hom.app U c) :=
    fun φ c => ConcreteCategory.congr_hom (φ.hom.naturality f) c
  have hR := key (E.unit.app ((lisseSheaf B X x Λ).obj R))
    (lisseSheafBilinear B X x Λ μ hμ U
      (((E.unitInv.app ((lisseSheaf B X x Λ).obj P)).hom.app U).hom a)
      (((E.unitInv.app ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom b))
  have hP := (key (E.unitInv.app ((lisseSheaf B X x Λ).obj P)) a).symm
  have hQ := (key (E.unitInv.app ((lisseSheaf B X x Λ).obj Q)) b).symm
  have hN := lisseSheafBilinear_naturality B X x Λ μ hμ f
    (((E.unitInv.app ((lisseSheaf B X x Λ).obj P)).hom.app U).hom a)
    (((E.unitInv.app ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom b)
  simp only [Functor.id_obj] at hP hQ
  rw [hP, hQ] at hN
  exact hR.symm.trans
    (congrArg (fun c => ((E.unit.app ((lisseSheaf B X x Λ).obj R)).hom.app V).hom c) hN)
attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

/-- **The pairing of sections `ℱ_P(V) × ℱ_Q(V) → ℱ_R(V)` on Mathlib's small étale site**, extended
from the dense subsite of Stacks 021B. -/
def lisseEtaleSheafBilinear (V : X.1.Etaleᵒᵖ) :
    ((lisseEtaleSheaf B X x Λ).obj P).obj.obj V →ₗ[Λ]
      ((lisseEtaleSheaf B X x Λ).obj Q).obj.obj V →ₗ[Λ]
        ((lisseEtaleSheaf B X x Λ).obj R).obj.obj V :=
  Sheaf.denseExtensionBilinear (SmallEtale.toEtaleSite B X.1 X.2)
    (lisseEtaleSheafSubsiteBilinear B X x Λ μ hμ)
    (fun f a b => lisseEtaleSheafSubsiteBilinear_naturality B X x Λ μ hμ f a b) V

/-- `lisseEtaleSheafBilinear` is natural: restricting the pairing of `a` and `b` along `f : V ⟶ W`
gives the pairing of their restrictions. -/
theorem lisseEtaleSheafBilinear_naturality {V W : X.1.Etaleᵒᵖ} (f : V ⟶ W)
    (a : ((lisseEtaleSheaf B X x Λ).obj P).obj.obj V)
    (b : ((lisseEtaleSheaf B X x Λ).obj Q).obj.obj V) :
    ((lisseEtaleSheaf B X x Λ).obj R).obj.map f (lisseEtaleSheafBilinear B X x Λ μ hμ V a b) =
      lisseEtaleSheafBilinear B X x Λ μ hμ W (((lisseEtaleSheaf B X x Λ).obj P).obj.map f a)
        (((lisseEtaleSheaf B X x Λ).obj Q).obj.map f b) :=
  Sheaf.denseExtensionBilinear_naturality _ _ _ f a b

/-- On the objects of the small étale category of Stacks 021B, `lisseEtaleSheafBilinear` is the
pairing of Tag 0DV5 read through the unit of the equivalence of sites. -/
theorem lisseEtaleSheafBilinear_unit (U : (SmallEtale B X.1 X.2)ᵒᵖ)
    (a : ((lisseSheaf B X x Λ).obj P).obj.obj U) (b : ((lisseSheaf B X x Λ).obj Q).obj.obj U) :
    lisseEtaleSheafBilinear B X x Λ μ hμ ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)
        ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app
          ((lisseSheaf B X x Λ).obj P)).hom.app U).hom a)
        ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app
          ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom b) =
      (((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unit.app
        ((lisseSheaf B X x Λ).obj R)).hom.app U).hom (lisseSheafBilinear B X x Λ μ hμ U a b) := by
  let E := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)
  have h : ∀ (F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ))
      (c : F.obj.obj U), ((E.unitInv.app F).hom.app U).hom (((E.unit.app F).hom.app U).hom c) = c :=
    fun F c => ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun φ => φ.hom) (E.unitIso.hom_inv_id_app F)) U) c
  refine (Sheaf.denseExtensionBilinear_apply _ _ _ U _ _).trans ?_
  show ((E.unit.app ((lisseSheaf B X x Λ).obj R)).hom.app U).hom
    (lisseSheafBilinear B X x Λ μ hμ U
      (((E.unitInv.app ((lisseSheaf B X x Λ).obj P)).hom.app U).hom
        (((E.unit.app ((lisseSheaf B X x Λ).obj P)).hom.app U).hom a))
      (((E.unitInv.app ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom
        (((E.unit.app ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom b))) = _
  rw [h, h]

/-- **The morphism of sheaves `ℱ_P ⊗ ℱ_Q ⟶ ℱ_R` on Mathlib's small étale site** attached to a
`π₁`-equivariant `Λ`-bilinear map `μ : P × Q → R` by Tag 0DV5. -/
def lisseEtaleSheafTensorHom :
    (lisseEtaleSheaf B X x Λ).obj P ⊗ (lisseEtaleSheaf B X x Λ).obj Q ⟶
      (lisseEtaleSheaf B X x Λ).obj R :=
  Sheaf.tensorDesc (lisseEtaleSheafBilinear B X x Λ μ hμ)
    (fun f a b => lisseEtaleSheafBilinear_naturality B X x Λ μ hμ f a b)

end Stacks.EtaleCohomology
