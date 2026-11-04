module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkLinear
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModulesPairingNaturality

/-!
# Pairings of lisse sheaves of `Λ`-modules

Let `X` be a connected scheme of a big étale site with a geometric point `x̄`, `Λ` a finite
commutative ring, and `P`, `Q`, `R` finite `Λ`-modules with continuous actions of `π₁(X, x̄)`. A
`π₁`-equivariant `Λ`-bilinear map `μ : P × Q → R` gives, through the equivalence of Tag 0DV5 (3),
a pairing of the sections of the lisse sheaves `ℱ_P × ℱ_Q → ℱ_R`, natural in the étale open and
`Λ`-bilinear. Its biadditive part is the pairing of Tag 0DV5 (2),
`Stacks.ConstantSheaf.finiteLocallyConstantPairing`.

## Main definitions

* `Stacks.EtaleCohomology.finiteTypeContinuousModuleSMul`: multiplication by `c` as an endomorphism
  of a finite continuous `Λ`-module.
* `Stacks.EtaleCohomology.lisseSheafAddPairing`: the biadditive pairing of sections.
* `Stacks.EtaleCohomology.lisseSheafBilinear`: the bilinear pairing of sections.

## Main results

* `Stacks.EtaleCohomology.lisseSheafBilinear_naturality`: the bilinear pairing commutes with
  restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

section SMul

variable (Λ : Type) [CommRing Λ] {G : Type (u + 1)} [Group G] [TopologicalSpace G]

/-- **Multiplication by `c ∈ Λ`** as an endomorphism of a finite `Λ`-module with continuous
`G`-action. -/
def finiteTypeContinuousModuleSMul (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G)
    (c : Λ) : P ⟶ P :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (c • LinearMap.id)
      comm := fun g => by
        ext v
        exact ((P.obj.obj.obj.ρ g).hom.map_smul c v).symm }))

variable [Finite Λ] {P Q R : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G}

/-- A `Λ`-bilinear map of finite continuous modules, as a biadditive map of the underlying
discrete `π₁`-modules. -/
def finiteTypeContinuousModuleBilinearAddHom
    (μ : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V) :
    ((finiteTypeContinuousModuleForgetAbelian Λ G).obj
        P).obj.obj.obj.V →+
      ((finiteTypeContinuousModuleForgetAbelian Λ G).obj
        Q).obj.obj.obj.V →+
      ((finiteTypeContinuousModuleForgetAbelian Λ G).obj
        R).obj.obj.obj.V :=
  AddMonoidHom.mk' (fun a => (μ a).toAddMonoidHom) fun a a' => by
    ext b
    exact LinearMap.map_add₂ μ a a' b

/-- The biadditive map attached to `μ` is `μ`. -/
theorem finiteTypeContinuousModuleBilinearAddHom_apply
    (μ : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V) (a b) :
    finiteTypeContinuousModuleBilinearAddHom Λ μ a b = μ a b :=
  rfl

end SMul

section Pairing

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]
  {P Q R : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}

variable (μ : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V →ₗ[Λ] R.obj.obj.obj.V)
  (hμ : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
    μ ((P.obj.obj.obj.ρ g).hom a) ((Q.obj.obj.obj.ρ g).hom b) = (R.obj.obj.obj.ρ g).hom (μ a b))

/-- The biadditive pairing of sections `ℱ_P(U) × ℱ_Q(U) → ℱ_R(U)` attached to `μ`. -/
abbrev lisseSheafAddPairing (U : (SmallEtale B X.1 X.2)ᵒᵖ) :
    ((lisseSheaf B X x Λ).obj P).obj.obj U →+ ((lisseSheaf B X x Λ).obj Q).obj.obj U →+
      ((lisseSheaf B X x Λ).obj R).obj.obj U :=
  finiteLocallyConstantPairing (SmallEtale.topology B X.1 X.2)
    (canonicalFiniteLocallyConstantSetsEquivalence B X x)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj P)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj Q)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj R)
    (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ U

/-- **The pairing of sections attached to `μ` is `Λ`-linear in the first variable.** -/
theorem lisseSheafAddPairing_smul_left (U : (SmallEtale B X.1 X.2)ᵒᵖ) (c : Λ)
    (a : ((lisseSheaf B X x Λ).obj P).obj.obj U) (b : ((lisseSheaf B X x Λ).obj Q).obj.obj U) :
    lisseSheafAddPairing B X x Λ μ hμ U (c • a) b =
      c • lisseSheafAddPairing B X x Λ μ hμ U a b := by
  let J := SmallEtale.topology B X.1 X.2
  let e := canonicalFiniteLocallyConstantSetsEquivalence B X x
  let φ := finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)
  have hc : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
      (c • μ) ((P.obj.obj.obj.ρ g).hom a) ((Q.obj.obj.obj.ρ g).hom b) =
        (R.obj.obj.obj.ρ g).hom ((c • μ) a b) := fun g a b => by
    simp only [LinearMap.smul_apply, hμ, LinearMap.map_smul]
  show finiteLocallyConstantPairing J e (φ.obj P) (φ.obj Q) (φ.obj R)
        (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ U
      (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J _ e).inverse.map
        (φ.map (finiteTypeContinuousModuleSMul Λ P c))).hom.hom.app U a) b =
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J _ e).inverse.map
        (φ.map (finiteTypeContinuousModuleSMul Λ R c))).hom.hom.app U
      (finiteLocallyConstantPairing J e (φ.obj P) (φ.obj Q) (φ.obj R)
        (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ U a b)
  have hl : ∀ a' b', (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) a' b' =
      (finiteTypeContinuousModuleBilinearAddHom Λ μ)
        ((φ.map (finiteTypeContinuousModuleSMul Λ P c)).hom.hom.hom.hom.hom a') b' := fun a' b' =>
    (LinearMap.map_smul₂ μ c a' b').symm
  have hr : ∀ a' b', (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) a' b' =
      (φ.map (finiteTypeContinuousModuleSMul Λ R c)).hom.hom.hom.hom.hom
        ((finiteTypeContinuousModuleBilinearAddHom Λ μ) a' b') := fun a' b' => rfl
  have h1 := finiteLocallyConstantPairing_map_left J e
      (φ.map (finiteTypeContinuousModuleSMul Λ P c))
      (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ
      (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) hc hl U a b
  have h2 := map_finiteLocallyConstantPairing J e (φ.map (finiteTypeContinuousModuleSMul Λ R c))
      (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ
      (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) hc hr U a b
  rw [h1, h2]

/-- **The pairing of sections attached to `μ` is `Λ`-linear in the second variable.** -/
theorem lisseSheafAddPairing_smul_right (U : (SmallEtale B X.1 X.2)ᵒᵖ) (c : Λ)
    (a : ((lisseSheaf B X x Λ).obj P).obj.obj U) (b : ((lisseSheaf B X x Λ).obj Q).obj.obj U) :
    lisseSheafAddPairing B X x Λ μ hμ U a (c • b) =
      c • lisseSheafAddPairing B X x Λ μ hμ U a b := by
  let J := SmallEtale.topology B X.1 X.2
  let e := canonicalFiniteLocallyConstantSetsEquivalence B X x
  let φ := finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)
  have hc : ∀ (g : EtaleFundamentalGroup X.1 x) (a : P.obj.obj.obj.V) (b : Q.obj.obj.obj.V),
      (c • μ) ((P.obj.obj.obj.ρ g).hom a) ((Q.obj.obj.obj.ρ g).hom b) =
        (R.obj.obj.obj.ρ g).hom ((c • μ) a b) := fun g a b => by
    simp only [LinearMap.smul_apply, hμ, LinearMap.map_smul]
  show finiteLocallyConstantPairing J e (φ.obj P) (φ.obj Q) (φ.obj R)
        (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ U a
      (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J _ e).inverse.map
        (φ.map (finiteTypeContinuousModuleSMul Λ Q c))).hom.hom.app U b) =
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J _ e).inverse.map
        (φ.map (finiteTypeContinuousModuleSMul Λ R c))).hom.hom.app U
      (finiteLocallyConstantPairing J e (φ.obj P) (φ.obj Q) (φ.obj R)
        (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ U a b)
  have hl : ∀ a' b', (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) a' b' =
      (finiteTypeContinuousModuleBilinearAddHom Λ μ) a'
        ((φ.map (finiteTypeContinuousModuleSMul Λ Q c)).hom.hom.hom.hom.hom b') := fun a' b' =>
    ((μ a').map_smul c b').symm
  have hr : ∀ a' b', (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) a' b' =
      (φ.map (finiteTypeContinuousModuleSMul Λ R c)).hom.hom.hom.hom.hom
        ((finiteTypeContinuousModuleBilinearAddHom Λ μ) a' b') := fun a' b' => rfl
  have h1 := finiteLocallyConstantPairing_map_right J e
      (φ.map (finiteTypeContinuousModuleSMul Λ Q c))
      (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ
      (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) hc hl U a b
  have h2 := map_finiteLocallyConstantPairing J e (φ.map (finiteTypeContinuousModuleSMul Λ R c))
      (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ
      (finiteTypeContinuousModuleBilinearAddHom Λ (c • μ)) hc hr U a b
  rw [h1, h2]

/-- **The `Λ`-bilinear pairing of sections `ℱ_P(U) × ℱ_Q(U) → ℱ_R(U)`** attached to a
`π₁`-equivariant `Λ`-bilinear map `μ : P × Q → R` by Tag 0DV5. -/
def lisseSheafBilinear (U : (SmallEtale B X.1 X.2)ᵒᵖ) :
    ((lisseSheaf B X x Λ).obj P).obj.obj U →ₗ[Λ] ((lisseSheaf B X x Λ).obj Q).obj.obj U →ₗ[Λ]
      ((lisseSheaf B X x Λ).obj R).obj.obj U :=
  LinearMap.mk₂ Λ (fun a b => lisseSheafAddPairing B X x Λ μ hμ U a b)
    (fun a a' b => by rw [map_add, AddMonoidHom.add_apply])
    (fun c a b => lisseSheafAddPairing_smul_left B X x Λ μ hμ U c a b)
    (fun a b b' => map_add _ b b')
    (fun c a b => lisseSheafAddPairing_smul_right B X x Λ μ hμ U c a b)

/-- The bilinear pairing of sections is the biadditive one. -/
theorem lisseSheafBilinear_apply (U : (SmallEtale B X.1 X.2)ᵒᵖ)
    (a : ((lisseSheaf B X x Λ).obj P).obj.obj U) (b : ((lisseSheaf B X x Λ).obj Q).obj.obj U) :
    lisseSheafBilinear B X x Λ μ hμ U a b = lisseSheafAddPairing B X x Λ μ hμ U a b :=
  rfl

/-- **The bilinear pairing of sections commutes with restriction.** -/
theorem lisseSheafBilinear_naturality {U V : (SmallEtale B X.1 X.2)ᵒᵖ} (f : U ⟶ V)
    (a : ((lisseSheaf B X x Λ).obj P).obj.obj U) (b : ((lisseSheaf B X x Λ).obj Q).obj.obj U) :
    ((lisseSheaf B X x Λ).obj R).obj.map f (lisseSheafBilinear B X x Λ μ hμ U a b) =
      lisseSheafBilinear B X x Λ μ hμ V (((lisseSheaf B X x Λ).obj P).obj.map f a)
        (((lisseSheaf B X x Λ).obj Q).obj.map f b) :=
  finiteLocallyConstantPairing_naturality (SmallEtale.topology B X.1 X.2)
    (canonicalFiniteLocallyConstantSetsEquivalence B X x)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj P)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj Q)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj R)
    (finiteTypeContinuousModuleBilinearAddHom Λ μ) hμ f a b

end Pairing

end Stacks.EtaleCohomology
