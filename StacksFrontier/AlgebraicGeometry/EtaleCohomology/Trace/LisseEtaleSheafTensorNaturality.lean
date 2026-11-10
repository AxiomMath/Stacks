module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseEtaleSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDescNaturality

/-!
# Adjoint morphisms for tensor pairings of lisse sheaves

Let `μ₁ : P₁ × Q₁ → R` and `μ₂ : P₂ × Q₂ → R` be `π₁(X, x̄)`-equivariant `Λ`-bilinear maps of
finite continuous `Λ`-modules and `a : P₁ ⟶ P₂`, `b : Q₂ ⟶ Q₁` adjoint for them:
`μ₂(a p, q) = μ₁(p, b q)`. Then the morphisms of lisse sheaves `ℱ_a`, `ℱ_b` are adjoint for the
pairings of sheaves `ℱ_{P_i} ⊗ ℱ_{Q_i} ⟶ ℱ_R` that `μ₁`, `μ₂` define on Mathlib's small étale
site (`Stacks.EtaleCohomology.lisseEtaleSheafTensorHom_adjoint`). The pairings of sections of
Tag 0DV5 are natural in each variable (`Stacks.EtaleCohomology.lisseSheafBilinear_map_left`,
`Stacks.EtaleCohomology.lisseSheafBilinear_map_right`), hence so are their extensions from the
dense subsite of Stacks 021B to Mathlib's site
(`Stacks.EtaleCohomology.lisseEtaleSheafBilinear_map_left`,
`Stacks.EtaleCohomology.lisseEtaleSheafBilinear_map_right`), and `tensorDesc` turns this into the
adjointness of the whiskered morphisms. For the dot product of a representation and its
contragredient this is the adjointness of the intertwiners `A` and `Aᵀ` used in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.lisseEtaleSheafTensorHom_adjoint`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-- Limits of the size of the site in the large-universe module category, with its universes
fixed. -/
local instance lisseEtaleSheafTensorNaturality_hasLimitsOfSize (Λ : Type) [Ring Λ] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, 0}

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]

section Subsite

variable
  {P P' Q Q' R : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
  (μ : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
  (hμ : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
    μ ((P.obj.obj.obj.ρ g).asHom.hom a) ((Q.obj.obj.obj.ρ g).asHom.hom b) =
      (R.obj.obj.obj.ρ g).asHom.hom (μ a b))

/-- **The pairing of sections of Tag 0DV5 is natural in the first variable**: on `ℱ_f(s)` for
`f : P' ⟶ P` it is the pairing of `μ ∘ (f × 1)` on `s`. -/
theorem lisseSheafBilinear_map_left (f : P' ⟶ P)
    (μ' : P'.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
    (hμ' : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P'.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
      μ' ((P'.obj.obj.obj.ρ g).asHom.hom a) ((Q.obj.obj.obj.ρ g).asHom.hom b) =
        (R.obj.obj.obj.ρ g).asHom.hom (μ' a b))
    (h : ∀ a b, μ' a b = μ (f.hom.hom.hom.hom.hom a) b) (U : (SmallEtale B X.1 X.2)ᵒᵖ)
    (s : ((lisseSheaf B X x Λ).obj P').obj.obj U) (t : ((lisseSheaf B X x Λ).obj Q).obj.obj U) :
    lisseSheafBilinear B X x Λ μ hμ U ((((lisseSheaf B X x Λ).map f).hom.app U).hom s) t =
      lisseSheafBilinear B X x Λ μ' hμ' U s t :=
  finiteLocallyConstantPairing_map_left (SmallEtale.topology B X.1 X.2)
    (canonicalFiniteLocallyConstantSetsEquivalence B X x)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).map f)
    (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ
    (finiteTypeContinuousModuleBilinearAddHom Λ μ') hμ' h U s t

/-- **The pairing of sections of Tag 0DV5 is natural in the second variable.** -/
theorem lisseSheafBilinear_map_right (f : Q' ⟶ Q)
    (μ' : P.obj.obj.obj.V →ₗ[Λ] Q'.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
    (hμ' : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q'.obj.obj.obj.V),
      μ' ((P.obj.obj.obj.ρ g).asHom.hom a) ((Q'.obj.obj.obj.ρ g).asHom.hom b) =
        (R.obj.obj.obj.ρ g).asHom.hom (μ' a b))
    (h : ∀ a b, μ' a b = μ a (f.hom.hom.hom.hom.hom b)) (U : (SmallEtale B X.1 X.2)ᵒᵖ)
    (s : ((lisseSheaf B X x Λ).obj P).obj.obj U) (t : ((lisseSheaf B X x Λ).obj Q').obj.obj U) :
    lisseSheafBilinear B X x Λ μ hμ U s ((((lisseSheaf B X x Λ).map f).hom.app U).hom t) =
      lisseSheafBilinear B X x Λ μ' hμ' U s t :=
  finiteLocallyConstantPairing_map_right (SmallEtale.topology B X.1 X.2)
    (canonicalFiniteLocallyConstantSetsEquivalence B X x)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).map f)
    (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ
    (finiteTypeContinuousModuleBilinearAddHom Λ μ') hμ' h U s t

/-- The inverse unit of the equivalence of sheaf categories is natural in the lisse sheaf. -/
private theorem unitInv_lisseEtaleSheaf_map (f : P' ⟶ P) (U : (SmallEtale B X.1 X.2)ᵒᵖ)
    (s : ((lisseEtaleSheaf B X x Λ).obj P').obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)) :
    (((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unitInv.app
        ((lisseSheaf B X x Λ).obj P)).hom.app U).hom
      ((((lisseEtaleSheaf B X x Λ).map f).hom.app
        ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)).hom s) =
      (((lisseSheaf B X x Λ).map f).hom.app U).hom
        ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unitInv.app
          ((lisseSheaf B X x Λ).obj P')).hom.app U).hom s) :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U)
    ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).unitInv.naturality
      ((lisseSheaf B X x Λ).map f))) s

/-- The pairing of sections read on the subsite through the unit, natural in the first
variable. -/
theorem lisseEtaleSheafSubsiteBilinear_map_left (f : P' ⟶ P)
    (μ' : P'.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
    (hμ' : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P'.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
      μ' ((P'.obj.obj.obj.ρ g).asHom.hom a) ((Q.obj.obj.obj.ρ g).asHom.hom b) =
        (R.obj.obj.obj.ρ g).asHom.hom (μ' a b))
    (h : ∀ a b, μ' a b = μ (f.hom.hom.hom.hom.hom a) b) (U : (SmallEtale B X.1 X.2)ᵒᵖ)
    (s : ((lisseEtaleSheaf B X x Λ).obj P').obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U))
    (t : ((lisseEtaleSheaf B X x Λ).obj Q).obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)) :
    lisseEtaleSheafSubsiteBilinear B X x Λ μ hμ U
        ((((lisseEtaleSheaf B X x Λ).map f).hom.app
          ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)).hom s) t =
      lisseEtaleSheafSubsiteBilinear B X x Λ μ' hμ' U s t := by
  let E := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)
  change ((E.unit.app ((lisseSheaf B X x Λ).obj R)).hom.app U).hom
      (lisseSheafBilinear B X x Λ μ hμ U
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj P)).hom.app U).hom
          ((((lisseEtaleSheaf B X x Λ).map f).hom.app
            ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)).hom s))
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom t)) =
    ((E.unit.app ((lisseSheaf B X x Λ).obj R)).hom.app U).hom
      (lisseSheafBilinear B X x Λ μ' hμ' U
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj P')).hom.app U).hom s)
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom t))
  rw [unitInv_lisseEtaleSheaf_map B X x Λ f U s,
    lisseSheafBilinear_map_left B X x Λ μ hμ f μ' hμ' h]

/-- The pairing of sections read on the subsite through the unit, natural in the second
variable. -/
theorem lisseEtaleSheafSubsiteBilinear_map_right (f : Q' ⟶ Q)
    (μ' : P.obj.obj.obj.V →ₗ[Λ] Q'.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
    (hμ' : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q'.obj.obj.obj.V),
      μ' ((P.obj.obj.obj.ρ g).asHom.hom a) ((Q'.obj.obj.obj.ρ g).asHom.hom b) =
        (R.obj.obj.obj.ρ g).asHom.hom (μ' a b))
    (h : ∀ a b, μ' a b = μ a (f.hom.hom.hom.hom.hom b)) (U : (SmallEtale B X.1 X.2)ᵒᵖ)
    (s : ((lisseEtaleSheaf B X x Λ).obj P).obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U))
    (t : ((lisseEtaleSheaf B X x Λ).obj Q').obj.obj ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)) :
    lisseEtaleSheafSubsiteBilinear B X x Λ μ hμ U s
        ((((lisseEtaleSheaf B X x Λ).map f).hom.app
          ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)).hom t) =
      lisseEtaleSheafSubsiteBilinear B X x Λ μ' hμ' U s t := by
  let E := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)
  change ((E.unit.app ((lisseSheaf B X x Λ).obj R)).hom.app U).hom
      (lisseSheafBilinear B X x Λ μ hμ U
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj P)).hom.app U).hom s)
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj Q)).hom.app U).hom
          ((((lisseEtaleSheaf B X x Λ).map f).hom.app
            ((SmallEtale.toEtaleSite B X.1 X.2).op.obj U)).hom t))) =
    ((E.unit.app ((lisseSheaf B X x Λ).obj R)).hom.app U).hom
      (lisseSheafBilinear B X x Λ μ' hμ' U
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj P)).hom.app U).hom s)
        (((E.unitInv.app ((lisseSheaf B X x Λ).obj Q')).hom.app U).hom t))
  rw [unitInv_lisseEtaleSheaf_map B X x Λ f U t,
    lisseSheafBilinear_map_right B X x Λ μ hμ f μ' hμ' h]

end Subsite

section Etale

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable
  {P P' Q Q' R : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
  (μ : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
  (hμ : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
    μ ((P.obj.obj.obj.ρ g).asHom.hom a) ((Q.obj.obj.obj.ρ g).asHom.hom b) =
      (R.obj.obj.obj.ρ g).asHom.hom (μ a b))

/-- **The pairing of sections on Mathlib's small étale site is natural in the first variable**:
`μ(ℱ_f s, t) = (μ ∘ (f × 1))(s, t)`, by uniqueness of the extension from the dense subsite. -/
theorem lisseEtaleSheafBilinear_map_left (f : P' ⟶ P)
    (μ' : P'.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
    (hμ' : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P'.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
      μ' ((P'.obj.obj.obj.ρ g).asHom.hom a) ((Q.obj.obj.obj.ρ g).asHom.hom b) =
        (R.obj.obj.obj.ρ g).asHom.hom (μ' a b))
    (h : ∀ a b, μ' a b = μ (f.hom.hom.hom.hom.hom a) b) (V : X.1.Etaleᵒᵖ) :
    (lisseEtaleSheafBilinear B X x Λ μ hμ V).comp
        (((lisseEtaleSheaf B X x Λ).map f).hom.app V).hom =
      lisseEtaleSheafBilinear B X x Λ μ' hμ' V := by
  let G := SmallEtale.toEtaleSite B X.1 X.2
  let φ := (lisseEtaleSheaf B X x Λ).map f
  have hnat : ∀ {W W' : X.1.Etaleᵒᵖ} (g : W ⟶ W')
      (a : ((lisseEtaleSheaf B X x Λ).obj P').obj.obj W)
      (b : ((lisseEtaleSheaf B X x Λ).obj Q).obj.obj W),
      ((lisseEtaleSheaf B X x Λ).obj R).obj.map g
          (lisseEtaleSheafBilinear B X x Λ μ hμ W ((φ.hom.app W).hom a) b) =
        lisseEtaleSheafBilinear B X x Λ μ hμ W'
          ((φ.hom.app W').hom (((lisseEtaleSheaf B X x Λ).obj P').obj.map g a))
          (((lisseEtaleSheaf B X x Λ).obj Q).obj.map g b) := fun {W W'} g a b =>
    (lisseEtaleSheafBilinear_naturality B X x Λ μ hμ g _ b).trans
      (congrArg (fun z => lisseEtaleSheafBilinear B X x Λ μ hμ W' z
          (((lisseEtaleSheaf B X x Λ).obj Q).obj.map g b))
        (ConcreteCategory.congr_hom (φ.hom.naturality g) a).symm)
  have hsub : ∀ (U : (SmallEtale B X.1 X.2)ᵒᵖ)
      (a : ((lisseEtaleSheaf B X x Λ).obj P').obj.obj (G.op.obj U))
      (b : ((lisseEtaleSheaf B X x Λ).obj Q).obj.obj (G.op.obj U)),
      lisseEtaleSheafBilinear B X x Λ μ hμ (G.op.obj U) ((φ.hom.app (G.op.obj U)).hom a) b =
        lisseEtaleSheafSubsiteBilinear B X x Λ μ' hμ' U a b := fun U a b =>
    (Sheaf.denseExtensionBilinear_apply G (lisseEtaleSheafSubsiteBilinear B X x Λ μ hμ)
      (fun g a b => lisseEtaleSheafSubsiteBilinear_naturality B X x Λ μ hμ g a b) U
      ((φ.hom.app (G.op.obj U)).hom a) b).trans
      (lisseEtaleSheafSubsiteBilinear_map_left B X x Λ μ hμ f μ' hμ' h U a b)
  exact (Sheaf.denseExtensionBilinear_eq G (F₁ := ((lisseEtaleSheaf B X x Λ).obj P').obj)
    (F₂ := ((lisseEtaleSheaf B X x Λ).obj Q).obj) (H := (lisseEtaleSheaf B X x Λ).obj R)
    (lisseEtaleSheafSubsiteBilinear B X x Λ μ' hμ')
    (fun g a b => lisseEtaleSheafSubsiteBilinear_naturality B X x Λ μ' hμ' g a b)
    (fun W => (lisseEtaleSheafBilinear B X x Λ μ hμ W).comp (φ.hom.app W).hom)
    (fun g a b => hnat g a b) hsub V).symm

/-- **The pairing of sections on Mathlib's small étale site is natural in the second
variable.** -/
theorem lisseEtaleSheafBilinear_map_right (f : Q' ⟶ Q)
    (μ' : P.obj.obj.obj.V →ₗ[Λ] Q'.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
    (hμ' : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q'.obj.obj.obj.V),
      μ' ((P.obj.obj.obj.ρ g).asHom.hom a) ((Q'.obj.obj.obj.ρ g).asHom.hom b) =
        (R.obj.obj.obj.ρ g).asHom.hom (μ' a b))
    (h : ∀ a b, μ' a b = μ a (f.hom.hom.hom.hom.hom b)) (V : X.1.Etaleᵒᵖ) :
    (lisseEtaleSheafBilinear B X x Λ μ hμ V).compl₂
        (((lisseEtaleSheaf B X x Λ).map f).hom.app V).hom =
      lisseEtaleSheafBilinear B X x Λ μ' hμ' V := by
  let G := SmallEtale.toEtaleSite B X.1 X.2
  let φ := (lisseEtaleSheaf B X x Λ).map f
  have hnat : ∀ {W W' : X.1.Etaleᵒᵖ} (g : W ⟶ W')
      (a : ((lisseEtaleSheaf B X x Λ).obj P).obj.obj W)
      (b : ((lisseEtaleSheaf B X x Λ).obj Q').obj.obj W),
      ((lisseEtaleSheaf B X x Λ).obj R).obj.map g
          (lisseEtaleSheafBilinear B X x Λ μ hμ W a ((φ.hom.app W).hom b)) =
        lisseEtaleSheafBilinear B X x Λ μ hμ W'
          (((lisseEtaleSheaf B X x Λ).obj P).obj.map g a)
          ((φ.hom.app W').hom (((lisseEtaleSheaf B X x Λ).obj Q').obj.map g b)) :=
    fun {W W'} g a b =>
    (lisseEtaleSheafBilinear_naturality B X x Λ μ hμ g a _).trans
      (congrArg (fun z => lisseEtaleSheafBilinear B X x Λ μ hμ W'
          (((lisseEtaleSheaf B X x Λ).obj P).obj.map g a) z)
        (ConcreteCategory.congr_hom (φ.hom.naturality g) b).symm)
  have hsub : ∀ (U : (SmallEtale B X.1 X.2)ᵒᵖ)
      (a : ((lisseEtaleSheaf B X x Λ).obj P).obj.obj (G.op.obj U))
      (b : ((lisseEtaleSheaf B X x Λ).obj Q').obj.obj (G.op.obj U)),
      lisseEtaleSheafBilinear B X x Λ μ hμ (G.op.obj U) a ((φ.hom.app (G.op.obj U)).hom b) =
        lisseEtaleSheafSubsiteBilinear B X x Λ μ' hμ' U a b := fun U a b =>
    (Sheaf.denseExtensionBilinear_apply G (lisseEtaleSheafSubsiteBilinear B X x Λ μ hμ)
      (fun g a b => lisseEtaleSheafSubsiteBilinear_naturality B X x Λ μ hμ g a b) U
      a ((φ.hom.app (G.op.obj U)).hom b)).trans
      (lisseEtaleSheafSubsiteBilinear_map_right B X x Λ μ hμ f μ' hμ' h U a b)
  exact (Sheaf.denseExtensionBilinear_eq G (F₁ := ((lisseEtaleSheaf B X x Λ).obj P).obj)
    (F₂ := ((lisseEtaleSheaf B X x Λ).obj Q').obj) (H := (lisseEtaleSheaf B X x Λ).obj R)
    (lisseEtaleSheafSubsiteBilinear B X x Λ μ' hμ')
    (fun g a b => lisseEtaleSheafSubsiteBilinear_naturality B X x Λ μ' hμ' g a b)
    (fun W => (lisseEtaleSheafBilinear B X x Λ μ hμ W).compl₂ (φ.hom.app W).hom)
    (fun g a b => hnat g a b) hsub V).symm

/-- **Adjoint morphisms of modules give adjoint morphisms of lisse sheaves**: if `a : P' ⟶ P` and
`b : Q ⟶ Q'` satisfy `μ(a p, q) = μ'(p, b q)` for equivariant pairings `μ : P × Q → R`,
`μ' : P' × Q' → R`, then `ℱ_a ▷ ℱ_Q ≫ ℱ_μ = ℱ_{P'} ◁ ℱ_b ≫ ℱ_{μ'}` for the morphisms
`Stacks.EtaleCohomology.lisseEtaleSheafTensorHom` on Mathlib's small étale site. -/
theorem lisseEtaleSheafTensorHom_adjoint (a : P' ⟶ P) (b : Q ⟶ Q')
    (μ' : P'.obj.obj.obj.V →ₗ[Λ] Q'.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
    (hμ' : ∀ (g : EtaleFundamentalGroup X.1 x) (p : P'.obj.obj.obj.V) (q : Q'.obj.obj.obj.V),
      μ' ((P'.obj.obj.obj.ρ g).asHom.hom p) ((Q'.obj.obj.obj.ρ g).asHom.hom q) =
        (R.obj.obj.obj.ρ g).asHom.hom (μ' p q))
    (h : ∀ p q, μ (a.hom.hom.hom.hom.hom p) q = μ' p (b.hom.hom.hom.hom.hom q)) :
    (lisseEtaleSheaf B X x Λ).map a ▷ (lisseEtaleSheaf B X x Λ).obj Q ≫
        lisseEtaleSheafTensorHom B X x Λ μ hμ =
      (lisseEtaleSheaf B X x Λ).obj P' ◁ (lisseEtaleSheaf B X x Λ).map b ≫
        lisseEtaleSheafTensorHom B X x Λ μ' hμ' := by
  let ν : P'.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V :=
    μ.comp a.hom.hom.hom.hom.hom
  have hν : ∀ (g : EtaleFundamentalGroup X.1 x) (p : P'.obj.obj.obj.V) (q : Q.obj.obj.obj.V),
      ν ((P'.obj.obj.obj.ρ g).asHom.hom p) ((Q.obj.obj.obj.ρ g).asHom.hom q) =
        (R.obj.obj.obj.ρ g).asHom.hom (ν p q) := fun g p q => by
    have hc := ConcreteCategory.congr_hom (a.hom.hom.hom.comm g) p
    change μ (a.hom.hom.hom.hom.hom ((P'.obj.obj.obj.ρ g).asHom.hom p)) _ = _
    rw [show a.hom.hom.hom.hom.hom ((P'.obj.obj.obj.ρ g).asHom.hom p) =
      (P.obj.obj.obj.ρ g).asHom.hom (a.hom.hom.hom.hom.hom p) from hc, hμ]
    rfl
  rw [lisseEtaleSheafTensorHom, lisseEtaleSheafTensorHom, Sheaf.whiskerRight_tensorDesc,
    Sheaf.whiskerLeft_tensorDesc]
  have e₁ : ∀ V, (lisseEtaleSheafBilinear B X x Λ μ hμ V).comp
      (((lisseEtaleSheaf B X x Λ).map a).hom.app V).hom = lisseEtaleSheafBilinear B X x Λ ν hν V :=
    lisseEtaleSheafBilinear_map_left B X x Λ μ hμ a ν hν (fun _ _ => rfl)
  have e₂ : ∀ V, (lisseEtaleSheafBilinear B X x Λ μ' hμ' V).compl₂
      (((lisseEtaleSheaf B X x Λ).map b).hom.app V).hom = lisseEtaleSheafBilinear B X x Λ ν hν V :=
    lisseEtaleSheafBilinear_map_right B X x Λ μ' hμ' b ν hν (fun p q => h p q)
  congr 1
  funext V
  exact (e₁ V).trans (e₂ V).symm

end Etale

end Stacks.EtaleCohomology
