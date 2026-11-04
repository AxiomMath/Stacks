module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars

/-!
# Naturality of the comparison of lisse sheaves under restriction of scalars

Let `ρ : R →+* S` be a morphism of finite commutative rings. For finite continuous
`π₁(X, x̄)`-modules `P` over `S` and `P'` over `R` whose underlying finite discrete `π₁`-modules
are identified by a scalar-compatible `θ`, `Stacks.EtaleCohomology.lisseSheafRestrictScalarsIso`
identifies `res_ρ ℱ_P` with `ℱ_{P'}`. This identification is natural: if `f : P₁ ⟶ P₂` and
`f' : P₁' ⟶ P₂'` correspond under `θ₁` and `θ₂` on the underlying discrete modules, then
`res_ρ ℱ_f` corresponds to `ℱ_{f'}`; both are, on sections, the images of the underlying maps of
discrete modules under the equivalence of Tag 0DV5 (2). The same holds on Mathlib's small étale
site, and there multiplication by `c ∈ S` on the sheaf `ℱ_P` is the lisse sheaf of multiplication
by `c` on `P`.

## Main results

* `Stacks.EtaleCohomology.lisseSheafRestrictScalarsHom_naturality`,
  `Stacks.EtaleCohomology.lisseSheafRestrictScalarsIso_hom_naturality`: on the small étale site of
  Stacks 021B.
* `Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIso_hom_naturality`: on Mathlib's small
  étale site.
* `Stacks.EtaleCohomology.etaleModuleSMul_app_lisseEtaleSheaf`: the scalar operations of the lisse
  sheaf are the lisse sheaves of the scalar operations.
* `Stacks.EtaleCohomology.etaleModuleSMul_app_eq_smul_id`: the scalar operations are the scalar
  multiples of the identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-- Limits of size `u` of modules in the universe `u + 1`, pinned (the dense subsite equivalence
otherwise leaves a universe constraint unsolved). -/
local instance hasLimitsOfSize_moduleCat_lisseRestrictScalarsNaturality (Λ : Type) [Ring Λ] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, 0}

variable {B : BigEtaleSite.{u}} {X : B.Scheme} [ConnectedSpace X.1] {x : GeometricPoint X.1}
  {R S : Type} [CommRing R] [CommRing S] [Finite R] [Finite S] (ρ : R →+* S)
  {P₁ P₂ : FiniteTypeContinuousModule.{0, u + 1, u + 1} S (EtaleFundamentalGroup X.1 x)}
  {P₁' P₂' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}

/-- The forgetful functor from finite continuous modules to finite discrete modules. -/
local notation "φ" => finiteTypeContinuousModuleForgetAbelian

/-- **Naturality of `Stacks.EtaleCohomology.lisseSheafRestrictScalarsHom`**: if `f` and `f'`
correspond under `θ₁` and `θ₂` on the underlying discrete modules, then so do `res_ρ ℱ_f` and
`ℱ_{f'}`. -/
theorem lisseSheafRestrictScalarsHom_naturality (f : P₁ ⟶ P₂) (f' : P₁' ⟶ P₂')
    (θ₁ : (φ S (EtaleFundamentalGroup X.1 x)).obj P₁ ⟶ (φ R (EtaleFundamentalGroup X.1 x)).obj P₁')
    (hθ₁ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P₁ (ρ c)) ≫ θ₁ =
      θ₁ ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P₁' c))
    (θ₂ : (φ S (EtaleFundamentalGroup X.1 x)).obj P₂ ⟶ (φ R (EtaleFundamentalGroup X.1 x)).obj P₂')
    (hθ₂ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P₂ (ρ c)) ≫ θ₂ =
      θ₂ ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P₂' c))
    (hf : (φ S _).map f ≫ θ₂ = θ₁ ≫ (φ R _).map f') :
    (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.restrictScalars.{u + 1} ρ)).map
        ((lisseSheaf B X x S).map f) ≫ lisseSheafRestrictScalarsHom B X x ρ θ₂ hθ₂ =
      lisseSheafRestrictScalarsHom B X x ρ θ₁ hθ₁ ≫ (lisseSheaf B X x R).map f' := by
  ext U s
  exact congrArg (fun t => (t.hom.hom.app U).hom s)
    (((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map_comp _ _).symm.trans
      (((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.congr_map hf).trans
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map_comp _ _)))

/-- **Naturality of `Stacks.EtaleCohomology.lisseSheafRestrictScalarsIso`** in the modules and
the identifications. -/
theorem lisseSheafRestrictScalarsIso_hom_naturality (f : P₁ ⟶ P₂) (f' : P₁' ⟶ P₂')
    (θ₁ : (φ S (EtaleFundamentalGroup X.1 x)).obj P₁ ≅ (φ R (EtaleFundamentalGroup X.1 x)).obj P₁')
    (hθ₁ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P₁ (ρ c)) ≫ θ₁.hom =
      θ₁.hom ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P₁' c))
    (θ₂ : (φ S (EtaleFundamentalGroup X.1 x)).obj P₂ ≅ (φ R (EtaleFundamentalGroup X.1 x)).obj P₂')
    (hθ₂ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P₂ (ρ c)) ≫ θ₂.hom =
      θ₂.hom ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P₂' c))
    (hf : (φ S _).map f ≫ θ₂.hom = θ₁.hom ≫ (φ R _).map f') :
    (sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.restrictScalars.{u + 1} ρ)).map
        ((lisseSheaf B X x S).map f) ≫ (lisseSheafRestrictScalarsIso B X x ρ θ₂ hθ₂).hom =
      (lisseSheafRestrictScalarsIso B X x ρ θ₁ hθ₁).hom ≫ (lisseSheaf B X x R).map f' :=
  lisseSheafRestrictScalarsHom_naturality ρ f f' θ₁.hom hθ₁ θ₂.hom hθ₂ hf

/-- A diagram chase along an equivalence `Φ`: if `u₁, u₂ : Φ⁻¹ Aᵢ ⟶ Mᵢ` intertwine `Φ⁻¹ a` and
`m`, then `Φ.counitInv ≫ Φ uᵢ` intertwine `a` and `Φ m`. -/
theorem _root_.CategoryTheory.Equivalence.comp_counitInv_app_comp_functor_map {C D : Type*}
    [Category* C] [Category* D] (Φ : C ≌ D) {A₁ A₂ : D} {M₁ M₂ : C} (a : A₁ ⟶ A₂) (m : M₁ ⟶ M₂)
    (u₁ : Φ.inverse.obj A₁ ⟶ M₁) (u₂ : Φ.inverse.obj A₂ ⟶ M₂)
    (h : Φ.inverse.map a ≫ u₂ = u₁ ≫ m) :
    a ≫ Φ.counitInv.app A₂ ≫ Φ.functor.map u₂ =
      (Φ.counitInv.app A₁ ≫ Φ.functor.map u₁) ≫ Φ.functor.map m := by
  rw [← Φ.counitInv_naturality_assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- **Naturality of `Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIso`** in the modules
and the identifications, on Mathlib's small étale site. -/
theorem lisseEtaleSheafRestrictScalarsIso_hom_naturality (f : P₁ ⟶ P₂) (f' : P₁' ⟶ P₂')
    (θ₁ : (φ S (EtaleFundamentalGroup X.1 x)).obj P₁ ≅ (φ R (EtaleFundamentalGroup X.1 x)).obj P₁')
    (hθ₁ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P₁ (ρ c)) ≫ θ₁.hom =
      θ₁.hom ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P₁' c))
    (θ₂ : (φ S (EtaleFundamentalGroup X.1 x)).obj P₂ ≅ (φ R (EtaleFundamentalGroup X.1 x)).obj P₂')
    (hθ₂ : ∀ c : R, (φ S _).map (finiteTypeContinuousModuleSMul S P₂ (ρ c)) ≫ θ₂.hom =
      θ₂.hom ≫ (φ R _).map (finiteTypeContinuousModuleSMul R P₂' c))
    (hf : (φ S _).map f ≫ θ₂.hom = θ₁.hom ≫ (φ R _).map f') :
    (etaleModuleRestrictScalars ρ X.1).map ((lisseEtaleSheaf B X x S).map f) ≫
        (lisseEtaleSheafRestrictScalarsIso B X x ρ θ₂ hθ₂).hom =
      (lisseEtaleSheafRestrictScalarsIso B X x ρ θ₁ hθ₁).hom ≫
        (lisseEtaleSheaf B X x R).map f' := by
  let ΦS := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} S)
  let resB := sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.restrictScalars.{u + 1} ρ)
  have h : resB.map (ΦS.inverse.map (ΦS.functor.map ((lisseSheaf B X x S).map f))) ≫
      (𝟙 _ ≫ resB.map (ΦS.unitInv.app _) ≫ (lisseSheafRestrictScalarsIso B X x ρ θ₂ hθ₂).hom) =
      (𝟙 _ ≫ resB.map (ΦS.unitInv.app _) ≫ (lisseSheafRestrictScalarsIso B X x ρ θ₁ hθ₁).hom) ≫
        (lisseSheaf B X x R).map f' := by
    rw [Category.id_comp, Category.id_comp, ← CategoryTheory.Functor.map_comp_assoc,
      ΦS.unitInv_naturality ((lisseSheaf B X x S).map f), CategoryTheory.Functor.map_comp_assoc,
      lisseSheafRestrictScalarsIso_hom_naturality ρ f f' θ₁ hθ₁ θ₂ hθ₂ hf, Category.assoc]
    rfl
  exact Equivalence.comp_counitInv_app_comp_functor_map (SmallEtale.sheafEquiv B X.1 X.2
    (ModuleCat.{u + 1} R))
    ((etaleModuleRestrictScalars ρ X.1).map ((lisseEtaleSheaf B X x S).map f))
    ((lisseSheaf B X x R).map f') _ _ h

/-- Multiplication by a scalar `a` on a sheaf of modules on the small étale site is the scalar
multiple `a • 𝟙` of the identity. -/
theorem etaleModuleSMul_app_eq_smul_id {A : Type} [CommRing A] (Z : Scheme.{u}) (a : A)
    (G : EtaleModules.{u, 0} A Z) : (etaleModuleSMul Z a).app G = a • 𝟙 G := by
  apply Sheaf.hom_ext
  ext U y
  rfl

/-- **The scalar operations of a lisse sheaf are the lisse sheaves of the scalar operations**:
multiplication by `c` on `ℱ_P`, on Mathlib's small étale site, is `ℱ` of multiplication by `c`
on `P`. -/
theorem etaleModuleSMul_app_lisseEtaleSheaf
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} S (EtaleFundamentalGroup X.1 x)) (c : S) :
    (etaleModuleSMul X.1 c).app ((lisseEtaleSheaf B X x S).obj P) =
      (lisseEtaleSheaf B X x S).map (finiteTypeContinuousModuleSMul S P c) := by
  let ΦS := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} S)
  apply ΦS.inverse.map_injective
  show _ = ΦS.inverse.map (ΦS.functor.map ((lisseSheaf B X x S).map
    (finiteTypeContinuousModuleSMul S P c)))
  rw [Equivalence.inv_fun_map]
  symm
  refine (Iso.inv_comp_eq (ΦS.unitIso.app _)).2 ?_
  ext V y
  exact ((ΦS.unitIso.app ((lisseSheaf B X x S).obj P)).hom.hom.app V).hom.map_smul c y

end Stacks.EtaleCohomology

end
