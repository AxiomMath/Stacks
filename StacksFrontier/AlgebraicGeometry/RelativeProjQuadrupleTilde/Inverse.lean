module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Balance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksFrontier.AlgebraicGeometry.ProjQuotientChartIdeal.Basic

/-!
# The comparison `ℳ̃_T ≅ h^*ℳ̃` on one chart: the inverse

On the standard open `D₊(c)` of a chart, we construct the inverse `Ψ : g^*ℳ̃(U) ⟶ ℳ̃_T` of the
comparison `Φ`, sending the pullback of a fraction `x / c^m` to `x ⊗ w^{-m}`, and show that `Φ`
and `Ψ` are mutually inverse.

## Main definitions

* `psi`: The morphism `Ψ : g^*ℳ̃(U) ⟶ ℳ̃_T`.
* `phi`: The comparison `Φ : ℳ̃_T ⟶ g^*ℳ̃(U)`.
* `chartIso`: The isomorphism `ℳ̃_T ≅ g^*ℳ̃(U)` with hom `Φ` and inverse `Ψ`.

## Main results

* `phi_psi`: `Φ ≫ Ψ = 𝟙`.
* `psi_phi`: `Ψ ≫ Φ = 𝟙`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing
attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

section Coherence

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Moving a contraction `κ : A ⟶ 𝟙` past a trivialization `t : 𝟙 ⟶ L'`. -/
theorem contract_triv {X A L' Q P : C} (κ : A ⟶ 𝟙_ C) (σ : 𝟙_ C ⟶ Q) (t : 𝟙_ C ⟶ L')
    (μ : Q ⊗ L' ⟶ P) :
    (ρ_ (X ⊗ A)).inv ≫ ((X ⊗ A) ◁ t) ≫ (α_ X A L').hom ≫ (X ◁ (((κ ≫ σ) ▷ L') ≫ μ)) =
      X ◁ (κ ≫ ((λ_ _).inv ≫ (σ ⊗ₘ t) ≫ μ)) := by
  have h1 : (ρ_ (X ⊗ A)).inv ≫ ((X ⊗ A) ◁ t) ≫ (α_ X A L').hom =
      X ◁ ((ρ_ A).inv ≫ (A ◁ t)) := by monoidal
  rw [reassoc_of% h1, ← MonoidalCategory.whiskerLeft_comp]
  congr 1
  simp only [comp_whiskerRight, Category.assoc]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc, tensorHom_def',
    unitors_inv_equal]
  simp only [Category.assoc]

/-- The abstract shape of the action identity for the pure tensors against a trivialization. -/
theorem act_triv_shape {X A Y L' Lm Q N : C} (act : X ⊗ A ⟶ Y) (t' : 𝟙_ C ⟶ L')
    (PT' : Y ⊗ L' ⟶ N) (PT : X ⊗ Lm ⟶ N) (κ : A ⟶ 𝟙_ C) (σ : 𝟙_ C ⟶ Q) (μ : Q ⊗ L' ⟶ Lm)
    (t : 𝟙_ C ⟶ Lm)
    (hrel : act ▷ L' ≫ PT' = (α_ X A L').hom ≫ X ◁ ((κ ≫ σ) ▷ L' ≫ μ) ≫ PT)
    (h3 : (λ_ _).inv ≫ (σ ⊗ₘ t') ≫ μ = t) :
    act ≫ (ρ_ Y).inv ≫ (Y ◁ t') ≫ PT' = (((ρ_ X).inv ≫ (X ◁ t) ≫ PT) ⊗ₘ κ) ≫ (ρ_ N).hom := by
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, hrel,
    ← Category.assoc (α_ _ _ _).hom, ← Category.assoc (_ ◁ t'), ← Category.assoc (ρ_ _).inv,
    contract_triv, h3, tensorHom_def', Category.assoc, rightUnitor_naturality]
  simp

/-- Composing the pure tensors against a trivialization with a comparison built from the dual
coordinate. -/
theorem untwist_comp {X Lm G N : C} (t : 𝟙_ C ⟶ Lm) (co : Lm ⟶ 𝟙_ C) (PT : X ⊗ Lm ⟶ N)
    (Φ : N ⟶ G) (β : X ⟶ G) (h : PT ≫ Φ = (β ⊗ₘ co) ≫ (ρ_ G).hom) (htc : t ≫ co = 𝟙 _) :
    ((ρ_ X).inv ≫ (X ◁ t) ≫ PT) ≫ Φ = β := by
  rw [Category.assoc, Category.assoc, h, whiskerLeft_comp_tensorHom_assoc, htc, tensorHom_id,
    ← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The dual shape of `untwist_comp`. -/
theorem twist_comp {X Lm G N : C} (t : 𝟙_ C ⟶ Lm) (co : Lm ⟶ 𝟙_ C) (PT : X ⊗ Lm ⟶ N)
    (Ψ : G ⟶ N) (β : X ⟶ G) (h : β ≫ Ψ = (ρ_ X).inv ≫ (X ◁ t) ≫ PT) (hct : co ≫ t = 𝟙 _) :
    ((β ⊗ₘ co) ≫ (ρ_ G).hom) ≫ Ψ = PT := by
  rw [Category.assoc, tensorHom_def', Category.assoc, rightUnitor_naturality_assoc, h,
    Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hct,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

end Coherence

section Chart

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (U : s.base.affineOpens) {d : ℕ} (c : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (w : (LaurentSections.Ring L (op ⊤))ˣ)
  (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        LaurentSections.pw w i)
  (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
    DirectSum.of _ (-1) τ)

/-- The module `ℳ̃_T` of the quadruple, in the spelling of the monoidal structure. -/
abbrev src : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) ψ

/-- **The pure tensors against the trivialization**, `x ↦ x ⊗ w^{-n}`, as a morphism
`f^*ℳ_{nd} ⟶ ℳ̃_T`. -/
def rmor (n : ℤ) : (pullbackFunctor (ringedSpaceHom f)).obj (ℳ.piece (n * d)) ⟶ src ℳ f ψ :=
  (ρ_ ((pullbackFunctor (ringedSpaceHom f)).obj (ℳ.piece (n * d)))).inv ≫
    ((pullbackFunctor (ringedSpaceHom f)).obj (ℳ.piece (n * d)) ◁ LaurentSections.triv w n) ≫
      Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
include hgf hCP hw hw' in
/-- **The pure tensors against the trivialization carry the action of `f^*𝒜_{id}` to
multiplication by `κ_i`.** -/
theorem act_rmor (n : ℤ) (i : ℕ) :
    act f (ℳ.toGradedModule s.mul_comm) (d : ℤ) n i ≫ rmor ℳ f ψ w (n + i) =
      (rmor ℳ f ψ w n ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom := by
  have h2 : ψ.app (i : ℤ) = kappaS U c f hf g hg hgf i ≫
      LaurentSections.secHom ((laurent L).piece i) (LaurentSections.pw w i) :=
    twisting_app_eq U c f hf g hg hgf ψ w hCP i
  have h3 := LaurentSections.secHom_tensor_triv w hw hw' n i
  have hrel := Twisting.relationLeft_pureTensor (ℳ.toGradedModule s.mul_comm) ψ (n, (i : ℤ))
  unfold Twisting.relationRight at hrel
  rw [h2] at hrel
  exact act_triv_shape _ _ _ _ _ _ _ _ hrel h3

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **A morphism identity of the shape `act ≫ γ₂ = (γ₁ ⊗ κ_i) ≫ ρ`, read on sections over `U`.** -/
theorem act_pullbackSection [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} (m : ℤ) (i : ℕ)
    (γ₁ : (pullbackFunctor (ringedSpaceHom f)).obj (ℳ.piece (m * d)) ⟶ N)
    (γ₂ : (pullbackFunctor (ringedSpaceHom f)).obj (ℳ.piece ((m + i) * d)) ⟶ N)
    (h : act f (ℳ.toGradedModule s.mul_comm) (d : ℤ) m i ≫ γ₂ =
      (γ₁ ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom)
    (x : sectionModulePieces ℳ U.1 (m * d)) (a : s.sectionPieces U.1 (i * d))
    (y : sectionModulePieces ℳ U.1 ((m + i) * d))
    (hy : DirectSum.of (sectionModulePieces ℳ U.1) ((m + i) * d) y =
      DirectSum.of (s.sectionPieces U.1) (i * d) a •
        DirectSum.of (sectionModulePieces ℳ U.1) (m * d) x) :
    γ₂.val.app (op ⊤) (Scheme.Modules.pullbackSection f (ℳ.piece ((m + i) * d)) U.1 ⊤ hf y) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        γ₁.val.app (op ⊤) (Scheme.Modules.pullbackSection f (ℳ.piece (m * d)) U.1 ⊤ hf x) := by
  have hyy := DirectSum.of_injective (β := sectionModulePieces ℳ U.1) ((m + i) * d)
    (hy.trans (of_act ℳ U m i x a).symm)
  subst hyy
  have hh : (pullbackFunctor (ringedSpaceHom f)).map
        ((ℳ.toGradedModule s.mul_comm).smulSheaf (m * d) ((i : ℤ) * d) ≫
          eqToHom (congrArg (ℳ.toGradedModule s.mul_comm).piece
            (by ring : m * (d : ℤ) + (i : ℤ) * d = (m + i) * d))) ≫ γ₂ =
        pullbackTensorComparison (ringedSpaceHom f) ((ℳ.toGradedModule s.mul_comm).piece (m * d))
            (s.algebra.piece ((i : ℤ) * d)) ≫
          (γ₁ ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom := by
    refine Eq.trans ?_ (congrArg (fun z => pullbackTensorComparison (ringedSpaceHom f)
      ((ℳ.toGradedModule s.mul_comm).piece (m * d)) (s.algebra.piece ((i : ℤ) * d)) ≫ z) h)
    exact (IsIso.hom_inv_id_assoc (pullbackTensorComparison (ringedSpaceHom f)
      ((ℳ.toGradedModule s.mul_comm).piece (m * d)) (s.algebra.piece ((i : ℤ) * d))) _).symm
  have hL : ((pullbackFunctor (ringedSpaceHom f)).map
        ((ℳ.toGradedModule s.mul_comm).smulSheaf (m * d) ((i : ℤ) * d) ≫
          eqToHom (congrArg (ℳ.toGradedModule s.mul_comm).piece
            (by ring : m * (d : ℤ) + (i : ℤ) * d = (m + i) * d))) ≫
          γ₂).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf
          (AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d))
            U.1 x a)) =
      γ₂.val.app (op ⊤) (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf
        ((eqToHom (congrArg ℳ.piece (by ring : m * d + (i : ℤ) * d = (m + i) * d))).val.app
          (op U.1) ((ℳ.toGradedModule s.mul_comm).smul (m * d) ((i : ℤ) * d) (op U.1) x a))) := by
    change (γ₂).val.app (op ⊤)
      (((Scheme.Modules.pullback f).map
        ((ℳ.toGradedModule s.mul_comm).smulSheaf (m * d) ((i : ℤ) * d) ≫
          eqToHom (congrArg (ℳ.toGradedModule s.mul_comm).piece
            (by ring : m * (d : ℤ) + (i : ℤ) * d = (m + i) * d)))).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf
          (AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d))
            U.1 x a))) = _
    have e1 := Scheme.Modules.pullbackSection_naturality f
      (F := AffineOpenTensorSections.tensorMod (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d)))
      (G := ℳ.piece ((m + i) * d))
      ((ℳ.toGradedModule s.mul_comm).smulSheaf (m * d) ((i : ℤ) * d) ≫
          eqToHom (congrArg (ℳ.toGradedModule s.mul_comm).piece
            (by ring : m * (d : ℤ) + (i : ℤ) * d = (m + i) * d))) U.1 ⊤ hf
      (AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d))
        U.1 x a)
    refine (congrArg (fun z => (γ₂).val.app (op ⊤) z) e1).trans ?_
    have e2 : ((ℳ.toGradedModule s.mul_comm).smulSheaf (m * d) ((i : ℤ) * d) ≫
          eqToHom (congrArg (ℳ.toGradedModule s.mul_comm).piece
            (by ring : m * (d : ℤ) + (i : ℤ) * d = (m + i) * d))).val.app (op U.1)
        (AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d))
          U.1 x a) =
        (eqToHom (congrArg ℳ.piece (by ring : m * d + (i : ℤ) * d = (m + i) * d))).val.app
          (op U.1) ((ℳ.toGradedModule s.mul_comm).smul (m * d) ((i : ℤ) * d) (op U.1) x a) :=
      congrArg (fun z => (eqToHom (congrArg ℳ.piece
          (by ring : m * d + (i : ℤ) * d = (m + i) * d))).val.app (op U.1) z)
        (SheafOfModules.GradedModule.smulSheaf_unit (ℳ.toGradedModule s.mul_comm) _ _ (op U.1) x a)
    exact congrArg (fun z => (γ₂).val.app (op ⊤)
      (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf z)) e2
  have hR : (pullbackTensorComparison (ringedSpaceHom f)
        ((ℳ.toGradedModule s.mul_comm).piece (m * d)) (s.algebra.piece ((i : ℤ) * d)) ≫
          (γ₁ ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom).val.app
        (op ⊤) (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf
          (AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d))
            U.1 x a)) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        γ₁.val.app (op ⊤) (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf x) := by
    change (ρ_ N).hom.val.app (op ⊤)
      ((γ₁ ⊗ₘ kappaS U c f hf g hg hgf i).val.app (op ⊤)
        ((pullbackTensorComparison (ringedSpaceHom f) (ℳ.piece (m * d))
          (s.algebra.piece ((i : ℤ) * d))).val.app (op ⊤)
          (Scheme.Modules.pullbackSection f
            (AffineOpenTensorSections.tensorMod (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d)))
            U.1 ⊤ hf (AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d))
              (s.algebra.piece ((i : ℤ) * d)) U.1 x a)))) = _
    have e1 := pullbackTensorComparison_pullbackSection f (ℳ.piece (m * d))
      (s.algebra.piece ((i : ℤ) * d)) U.1 hf x a
    refine (congrArg (fun z => (ρ_ N).hom.val.app (op ⊤)
      ((γ₁ ⊗ₘ kappaS U c f hf g hg hgf i).val.app (op ⊤) z)) e1).trans ?_
    refine (congrArg (fun z => (ρ_ N).hom.val.app (op ⊤) z)
      (tensorHom_tmul _ _ (op ⊤) _ _)).trans ?_
    refine (rightUnitor_hom_tmul (op ⊤) _ _).trans ?_
    exact congrArg (· • _) (kappa_pullbackSection U c f hf g hg hgf i a)
  have hev := congrArg (fun φ => φ.val.app (op ⊤) (Scheme.Modules.pullbackSection f
    (AffineOpenTensorSections.tensorMod (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d)))
      U.1 ⊤ hf (AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d))
        (s.algebra.piece ((i : ℤ) * d)) U.1 x a))) hh
  exact hL.symm.trans (hev.trans hR)

/-- **`x ↦ x ⊗ w^{-n}` on sections over `U`**, landing in the global sections of `ℳ̃_T`. -/
def rsec (n : ℤ) : sectionModulePieces ℳ U.1 (n * d) →+ (src ℳ f ψ).val.obj (op ⊤) :=
  ((rmor ℳ f ψ w n).val.app (op ⊤)).hom.toAddMonoidHom.comp
    (pullbackSectionHom f (ℳ.piece (n * d)) U.1 ⊤ hf)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- `rsec n x` is the image of the pullback of `x` under `x ↦ x ⊗ w^{-n}`. -/
theorem rsec_apply (n : ℤ) (x : sectionModulePieces ℳ U.1 (n * d)) :
    rsec ℳ U f hf ψ w n x = (rmor ℳ f ψ w n).val.app (op ⊤)
      (Scheme.Modules.pullbackSection f (ℳ.piece (n * d)) U.1 ⊤ hf x) :=
  AddMonoidHom.comp_apply _ _ _

include hgf hCP hw hw' in
/-- **`x ↦ x ⊗ w^{-n}` carries the action of `a ∈ 𝒜_{id}` to multiplication by `g^♯(a / c^i)`.** -/
theorem rsec_smul (n : ℤ) (i : ℕ) (p : ℤ) (hp : n + i = p) (a : s.sectionPieces U.1 (i * d))
    (x : sectionModulePieces ℳ U.1 (n * d)) (y : sectionModulePieces ℳ U.1 (p * d))
    (hy : DirectSum.of (sectionModulePieces ℳ U.1) (p * d) y =
      DirectSum.of (s.sectionPieces U.1) (i * d) a •
        DirectSum.of (sectionModulePieces ℳ U.1) (n * d) x) :
    rsec ℳ U f hf ψ w p y =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        rsec ℳ U f hf ψ w n x := by
  subst hp
  exact act_pullbackSection ℳ U c f hf g hg hgf n i _ _
    (act_rmor ℳ U c f hf g hg hgf ψ w hCP hw hw' n i) x a y hy

/-- The family `e_k = x ↦ x_{kd} ⊗ w^{-k}` on the whole module of sections over `U`, indexed by
the exponent of the denominator. -/
def eFam (k : ℕ) : sectionModule ℳ U.1 →+ (src ℳ f ψ).val.obj (op ⊤) :=
  (rsec ℳ U f hf ψ w (k : ℤ)).comp
    (DFinsupp.evalAddMonoidHom (β := sectionModulePieces ℳ U.1) (((k * d : ℕ) : ℤ)))

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- On the degree `kd` piece, `e_k` agrees with `x ↦ x ⊗ w^{-k}`. -/
theorem eFam_of (k : ℕ) (x : sectionModulePieces ℳ U.1 (((k * d : ℕ) : ℤ))) :
    eFam ℳ U f hf ψ w k (DirectSum.of (sectionModulePieces ℳ U.1) _ x) =
      rsec ℳ U f hf ψ w (k : ℤ) x := by
  change rsec ℳ U f hf ψ w (k : ℤ)
    (DirectSum.of (sectionModulePieces ℳ U.1) (((k * d : ℕ) : ℤ)) x (((k * d : ℕ) : ℤ))) = _
  rw [DirectSum.of_eq_same]

include hgf hCP hw hw' in
/-- `e_p (a • x) = g^♯(a / c^k) • e_n x` for `a ∈ 𝒜_{kd}`, `x` of degree `nd` and
`n + k = p`. -/
theorem eFam_smul (n k p : ℕ) (hp : n + k = p) (a : s.sectionPieces U.1 (k * d))
    (x : sectionModulePieces ℳ U.1 (((n * d : ℕ) : ℤ))) :
    eFam ℳ U f hf ψ w p (DirectSum.of (s.sectionPieces U.1) (k * d) a •
        DirectSum.of (sectionModulePieces ℳ U.1) _ x) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg k a) •
        eFam ℳ U f hf ψ w n (DirectSum.of (sectionModulePieces ℳ U.1) _ x) := by
  obtain ⟨y, hy⟩ : DirectSum.of (s.sectionPieces U.1) (k * d) a •
      DirectSum.of (sectionModulePieces ℳ U.1) _ x ∈
        sectionModuleGrading ℳ U.1 (((p * d : ℕ) : ℤ)) := by
    have h := (sectionModuleGradedSMul ℳ U.1).smul_mem (⟨a, rfl⟩ : DirectSum.of
      (s.sectionPieces U.1) (k * d) a ∈ s.sectionRingGrading U.1 (k * d))
      (mem_sectionModuleGrading_of ℳ U.1 x)
    have hdeg : ((k * d : ℕ) : ℤ) + ((n * d : ℕ) : ℤ) = ((p * d : ℕ) : ℤ) := by
      subst hp; push_cast; ring
    exact hdeg ▸ h
  rw [← hy, eFam_of, eFam_of]
  exact rsec_smul ℳ U c f hf g hg hgf ψ w hCP hw hw' (n : ℤ) k (p : ℤ)
    (by subst hp; push_cast; ring) a x y hy

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- `g^♯(c^k / c^k) = 1`. -/
theorem kappaSec_pow (k : ℕ) (a : s.sectionPieces U.1 (k * d))
    (ha : DirectSum.of (s.sectionPieces U.1) (k * d) a = cHom U.1 c ^ k) :
    kappaSec U c g hg k a = 1 := by
  change g.appLE _ ⊤ hg (Proj.awayToSection _ _ (algFrac U c k a)) = 1
  have h1 : algFrac U c k a = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_one]
    change (Localization.mk (DirectSum.of (s.sectionPieces U.1) (k * d) a)
      (⟨(cHom U.1 c) ^ k, k, rfl⟩ : Submonoid.powers (cHom U.1 c)) : Localization.Away _) = 1
    simp only [ha]
    exact Localization.mk_self (⟨(cHom U.1 c) ^ k, k, rfl⟩ : Submonoid.powers (cHom U.1 c))
  rw [h1, map_one, map_one]

include hgf hCP hw hw' in
/-- The family `e` is compatible with the localization: `e_{n+k}(c^k • x) = e_n x` for `x` of
degree `nd`. -/
theorem eFam_compat (n k : ℕ) (x : sectionModule ℳ U.1)
    (hx : x ∈ sectionModuleGrading ℳ U.1 (((n * d : ℕ) : ℤ))) :
    eFam ℳ U f hf ψ w (n + k) (cHom U.1 c ^ k • x) = eFam ℳ U f hf ψ w n x := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨a, ha⟩ := SetLike.pow_mem_graded k (cHom_mem U.1 c)
  rw [← ha]
  refine (eFam_smul ℳ U c f hf g hg hgf ψ w hCP hw hw' n k (n + k) rfl a x).trans ?_
  rw [kappaSec_pow U c g hg k a ha]
  exact one_smul _ _

/-- **The inverse on sections over `D₊(c)`, on the degree-zero localization**:
`x / c^k ↦ x ⊗ w^{-k}`. -/
def ellLoc : Loc ℳ U.1 c →+ (src ℳ f ψ).val.obj (op ⊤) :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree (s.sectionRingGrading U.1)
    (sectionModuleGrading ℳ U.1)
    (cHom_mem U.1 c) (eFam ℳ U f hf ψ w)
    (eFam_compat ℳ U c f hf g hg hgf ψ w hCP hw hw')

include hgf hCP hw hw' in
/-- **The inverse on the degree-zero localization sends `x / c^m` to `x ⊗ w^{-m}`**, for every
integer `m`. -/
theorem ellLoc_fracElt (m : ℤ) (x : sectionModulePieces ℳ U.1 (m * d)) :
    ellLoc ℳ U c f hf g hg hgf ψ w hCP hw hw' (fracElt ℳ U.1 c m x) = rsec ℳ U f hf ψ w m x := by
  have e : ((m.toNat * d : ℕ) : ℤ) = m.toNat • (d : ℤ) := by simp
  have hmem := e ▸ mem_fracNum ℳ U.1 c m x
  refine (Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction _ _ _ _ _ _ m.toNat _
    hmem (fracElt_val ℳ U.1 c m x)).trans ?_
  obtain ⟨a, ha⟩ := SetLike.pow_mem_graded (ex m) (cHom_mem U.1 c)
  obtain ⟨y, hy⟩ := hmem
  rw [← hy, eFam_of]
  rw [← ha] at hy
  refine (rsec_smul ℳ U c f hf g hg hgf ψ w hCP hw hw' m (ex m) (m.toNat : ℤ)
    (by have := ex_spec m; omega) a x y hy).trans ?_
  rw [kappaSec_pow U c g hg (ex m) a ha]
  exact one_smul _ _

/-- The functions `g^♯` on `T` of the degree-zero fractions. -/
def phiRing : HomogeneousLocalization.Away (s.sectionRingGrading U.1) (cHom U.1 c) →+*
    Γ(T, ⊤) :=
  (g.appLE _ ⊤ hg).hom.comp (Proj.awayToSection _ (cHom U.1 c)).hom

include hgf hCP hw hw' in
/-- The map `ellLoc` is semilinear along `phiRing`: `ellLoc (a • z) = g^♯(a) • ellLoc z`. -/
theorem ellLoc_smul (a : HomogeneousLocalization.Away (s.sectionRingGrading U.1) (cHom U.1 c))
    (z : Loc ℳ U.1 c) :
    ellLoc ℳ U c f hf g hg hgf ψ w hCP hw hw' (a • z) =
      phiRing U c g hg a • ellLoc ℳ U c f hf g hg hgf ψ w hCP hw hw' z := by
  refine Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_smul _ _ _ _ _ (phiRing U c g hg)
    ?_ a z
  rintro m n r x ⟨a, rfl⟩ ⟨x, rfl⟩
  exact eFam_smul ℳ U c f hf g hg hgf ψ w hCP hw hw' n m (m + n) (Nat.add_comm n m) a x

variable (hd : 0 < d)

include hd in
/-- The standard open `D₊(c)` of the chart is affine. -/
theorem isAffineOpen_basicOpen :
    IsAffineOpen (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)) :=
  Proj.isAffineOpen_basicOpen _ _ (cHom_mem U.1 c) hd

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
include hd in
/-- The map from the degree-zero localization to the sections of `ℳ̃(U)` over `D₊(c)` is
bijective. -/
theorem toChart_bijective : Function.Bijective (toChart ℳ U c) :=
  ⟨degreeZeroToSection_injective _ _ (cHom_mem U.1 c) hd,
    degreeZeroToSection_surjective _ _ (cHom_mem U.1 c) hd⟩

/-- The inverse of the fraction map, as a function. -/
def toChartInv (x : (moduleChart ℳ U).val.obj
    (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))) : Loc ℳ U.1 c :=
  Function.surjInv (toChart_bijective ℳ U c hd).2 x

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- `toChartInv` is a right inverse of `toChart`. -/
theorem toChart_toChartInv (x : (moduleChart ℳ U).val.obj
    (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))) :
    toChart ℳ U c (toChartInv ℳ U c hd x) = x :=
  Function.surjInv_eq (toChart_bijective ℳ U c hd).2 x

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- `toChartInv` is a left inverse of `toChart`. -/
theorem toChartInv_toChart (z : Loc ℳ U.1 c) : toChartInv ℳ U c hd (toChart ℳ U c z) = z :=
  (toChart_bijective ℳ U c hd).1 (toChart_toChartInv ℳ U c hd _)

/-- The inverse of the fraction map, as an additive map. -/
def toChartInvHom : (moduleChart ℳ U).val.obj
    (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))) →+ Loc ℳ U.1 c where
  toFun := toChartInv ℳ U c hd
  map_zero' :=
    (toChart_bijective ℳ U c hd).1 ((toChart_toChartInv ℳ U c hd 0).trans (map_zero _).symm)
  map_add' x y :=
    (toChart_bijective ℳ U c hd).1 ((toChart_toChartInv ℳ U c hd (x + y)).trans
      ((congrArg₂ (· + ·) (toChart_toChartInv ℳ U c hd x)
          (toChart_toChartInv ℳ U c hd y)).symm.trans
        (map_add _ _ _).symm))

/-- **The inverse on the sections of `ℳ̃(U)` over `D₊(c)`.** -/
def ell : (moduleChart ℳ U).val.obj (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))
    →+ (src ℳ f ψ).val.obj (op ⊤) :=
  (ellLoc ℳ U c f hf g hg hgf ψ w hCP hw hw').comp (toChartInvHom ℳ U c hd)

/-- On a fraction, `ell` agrees with `ellLoc`. -/
theorem ell_toChart (z : Loc ℳ U.1 c) :
    ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd (toChart ℳ U c z) =
      ellLoc ℳ U c f hf g hg hgf ψ w hCP hw hw' z :=
  (AddMonoidHom.comp_apply _ _ _).trans
    (congrArg (ellLoc ℳ U c f hf g hg hgf ψ w hCP hw hw') (toChartInv_toChart ℳ U c hd z))

include hd in
/-- The map from the degree-zero localization to the functions on `D₊(c)` is bijective. -/
theorem awayToSection_bijective :
    Function.Bijective (Proj.awayToSection (s.sectionRingGrading U.1) (cHom U.1 c)) := by
  have hiso : IsIso (Proj.awayToSection (s.sectionRingGrading U.1) (cHom U.1 c)) :=
    Stacks.ProjQuotientChartIdeal.isIso_awayToSection (𝒜 := s.sectionRingGrading U.1)
      (cHom_mem U.1 c) hd
  exact ConcreteCategory.bijective_of_isIso _

/-- `ell` is semilinear along `g^♯` on the images of fractions. -/
theorem ell_smul_toChart (a : HomogeneousLocalization.Away (s.sectionRingGrading U.1) (cHom U.1 c))
    (z : Loc ℳ U.1 c) :
    ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd
        ((show (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).ringCatSheaf.obj.obj
          (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))) from
          Proj.awayToSection _ _ a) • toChart ℳ U c z) =
      g.appLE _ ⊤ hg (Proj.awayToSection _ _ a) •
        ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd (toChart ℳ U c z) := by
  have e1 : (show (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).ringCatSheaf.obj.obj
        (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))) from
        Proj.awayToSection _ _ a) • toChart ℳ U c z = toChart ℳ U c (a • z) :=
    (map_smul (degreeZeroToSection (s.sectionRingGrading U.1) (sectionModuleGrading ℳ U.1)
      (cHom U.1 c)) a z).symm
  refine (congrArg (ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd) e1).trans ?_
  refine (ell_toChart ℳ U c f hf g hg hgf ψ w hCP hw hw' hd (a • z)).trans ?_
  refine (ellLoc_smul ℳ U c f hf g hg hgf ψ w hCP hw hw' a z).trans ?_
  exact congrArg (fun y => g.appLE _ ⊤ hg (Proj.awayToSection _ _ a) • y)
    (ell_toChart ℳ U c f hf g hg hgf ψ w hCP hw hw' hd z).symm

/-- `ell` is semilinear along `g^♯ : Γ(D₊(c)) → Γ(T)`: `ell (r • x) = g^♯(r) • ell x`. -/
theorem ell_smul (r : Γ(AlgebraicGeometry.Proj (s.sectionRingGrading U.1),
      Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))
    (x : (moduleChart ℳ U).val.obj
      (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))) :
    ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd (r • x) =
      g.appLE _ ⊤ hg r • ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd x := by
  have hs : ∃ a, Proj.awayToSection (s.sectionRingGrading U.1) (cHom U.1 c) a = r :=
    (awayToSection_bijective U c hd).2 r
  have hs' : ∃ z, toChart ℳ U c z = x := (toChart_bijective ℳ U c hd).2 x
  obtain ⟨a, ha⟩ := hs
  obtain ⟨z, hz⟩ := hs'
  subst ha
  subst hz
  exact ell_smul_toChart ℳ U c f hf g hg hgf ψ w hCP hw hw' hd a z

/-- **The inverse `Ψ : g^*ℳ̃(U) ⟶ ℳ̃_T`**, the morphism carrying the pullback of a fraction
`x / c^m` to `x ⊗ w^{-m}`. -/
def psi : tgt ℳ U g ⟶ src ℳ f ψ :=
  AffineOpenHomRecovery.homOfSections g _ hg (moduleChart ℳ U) (isAffineOpen_basicOpen U c hd)
    (src ℳ f ψ) (ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd)
    (ell_smul ℳ U c f hf g hg hgf ψ w hCP hw hw' hd)

/-- **The comparison `Φ : ℳ̃_T ⟶ g^*ℳ̃(U)`**, `x ⊗ l ↦ (w^n · l) · g^*(x / c^n)`, produced by the
universal property of `ℳ̃_T` from the balanced family `b`. -/
def phi : src ℳ f ψ ⟶ tgt ℳ U g :=
  (Twisting.existsUnique_hom (ℳ.toGradedModule s.mul_comm) ψ (tgt ℳ U g)
    (bmap ℳ U c f hf g hg hgf w)
    (bmap_balanced ℳ U c f hf g hg hgf ψ w hCP hw hw' hd)).exists.choose

/-- `Φ` restricted to the pure tensors of degree `n` is `bmap n`. -/
theorem pureTensor_phi (n : ℤ) :
    Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n ≫
        phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd = bmap ℳ U c f hf g hg hgf w n :=
  (Twisting.existsUnique_hom (ℳ.toGradedModule s.mul_comm) ψ (tgt ℳ U g)
    (bmap ℳ U c f hf g hg hgf w)
    (bmap_balanced ℳ U c f hf g hg hgf ψ w hCP hw hw' hd)).exists.choose_spec n

/-- `Φ` composed with `x ↦ x ⊗ w^{-n}` is `betaS n`. -/
theorem rmor_phi (n : ℤ) :
    rmor ℳ f ψ w n ≫ phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd = betaS ℳ U c f hf g hg hgf n :=
  untwist_comp _ _ _ _ _ (pureTensor_phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd n)
    (LaurentSections.triv_coord w hw hw' n)

/-- `Ψ` sends the pullback of the fraction `x / c^n` to `x ⊗ w^{-n}` on global sections. -/
private theorem psi_pullbackSection_fracChart (n : ℤ) (x : sectionModulePieces ℳ U.1 (n * d)) :
    (psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).val.app (op ⊤)
        (Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg (fracChart ℳ U c n x)) =
      rsec ℳ U f hf ψ w n x :=
  (AffineOpenHomRecovery.homOfSections_pullbackSection g _ hg (moduleChart ℳ U)
    (isAffineOpen_basicOpen U c hd) (src ℳ f ψ) (ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd)
    (ell_smul ℳ U c f hf g hg hgf ψ w hCP hw hw' hd) (fracChart ℳ U c n x)).trans
    ((congrArg (ell ℳ U c f hf g hg hgf ψ w hCP hw hw' hd) (fracChart_eq ℳ U c n x)).trans
      ((ell_toChart ℳ U c f hf g hg hgf ψ w hCP hw hw' hd _).trans
        (ellLoc_fracElt ℳ U c f hf g hg hgf ψ w hCP hw hw' n x)))

/-- `Ψ` composed with `betaS n` is `x ↦ x ⊗ w^{-n}`. -/
theorem betaS_psi (n : ℤ) :
    betaS ℳ U c f hf g hg hgf n ≫ psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd = rmor ℳ f ψ w n := by
  refine AffineOpenHomRecovery.hom_ext f U.1 hf (ℳ.piece (n * d)) U.2 (src ℳ f ψ) fun x => ?_
  have e1 := beta_pullbackSection ℳ U c f hf g hg hgf n x
  have e0 := fracPull_apply ℳ U c g hg n x
  exact (congrArg (fun z => (psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).val.app (op ⊤) z)
    (e1.trans e0)).trans (psi_pullbackSection_fracChart ℳ U c f hf g hg hgf ψ w hCP hw hw' hd n x)

/-- `Φ ≫ Ψ` restricts to the identity on the pure tensors of each degree. -/
theorem pureTensor_phi_psi (n : ℤ) :
    Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n ≫
        phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd ≫ psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd =
      Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n := by
  rw [← Category.assoc, pureTensor_phi]
  exact twist_comp _ _ _ _ _ (betaS_psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd n)
    (LaurentSections.coord_triv w hw hw' n)

/-- `Φ ≫ Ψ = 𝟙`. -/
theorem phi_psi :
    phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd ≫ psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd = 𝟙 _ :=
  (Twisting.existsUnique_hom (ℳ.toGradedModule s.mul_comm) ψ (src ℳ f ψ)
    (Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ)
    (Twisting.relationLeft_pureTensor (ℳ.toGradedModule s.mul_comm) ψ)).unique
    (pureTensor_phi_psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd) (fun _ => Category.comp_id _)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
include hd in
/-- Every section of `ℳ̃(U)` over `D₊(c)` is a fraction `x / c^n`, `n ≥ 0`. -/
theorem exists_fracChart (y : (moduleChart ℳ U).val.obj
    (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)))) :
    ∃ (m : ℤ) (x : sectionModulePieces ℳ U.1 (m * d)), fracChart ℳ U c m x = y := by
  have hy : ∃ z, toChart ℳ U c z = y := (toChart_bijective ℳ U c hd).2 y
  obtain ⟨z, hz⟩ := hy
  subst hz
  have hfr := Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree
    (s.sectionRingGrading U.1) (sectionModuleGrading ℳ U.1) (cHom_mem U.1 c) z
  obtain ⟨n, x0, hx0, hz⟩ := hfr
  have e : ((n * d : ℕ) : ℤ) = (n : ℤ) * d := by push_cast; ring
  rw [e] at hx0
  obtain ⟨x, hx⟩ := hx0
  refine ⟨n, x, (fracChart_eq ℳ U c n x).trans (congrArg (toChart ℳ U c) (Subtype.ext ?_))⟩
  rw [fracElt_val_eq ℳ U.1 c (n : ℤ) x n 0 (by simp), pow_zero, one_smul, hx]
  exact hz.symm

/-- `Ψ ≫ Φ = 𝟙`. -/
theorem psi_phi :
    psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd ≫ phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd =
      𝟙 _ := by
  refine AffineOpenHomRecovery.hom_ext g _ hg (moduleChart ℳ U) (isAffineOpen_basicOpen U c hd)
    (tgt ℳ U g) fun y => ?_
  obtain ⟨n, x, rfl⟩ := exists_fracChart ℳ U c hd y
  change (phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).val.app (op ⊤)
    ((psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).val.app (op ⊤)
      (Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg (fracChart ℳ U c n x))) =
    Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg (fracChart ℳ U c n x)
  refine (congrArg (fun z => (phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).val.app (op ⊤) z)
    ((psi_pullbackSection_fracChart ℳ U c f hf g hg hgf ψ w hCP hw hw' hd n x).trans
      (rsec_apply ℳ U f hf ψ w n x))).trans ?_
  have h := congrArg (fun φ => φ.val.app (op ⊤)
    (Scheme.Modules.pullbackSection f (ℳ.piece ((n : ℤ) * d)) U.1 ⊤ hf x))
    (rmor_phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd n)
  exact h.trans (beta_pullbackSection ℳ U c f hf g hg hgf n x)

/-- **Property (1) of the comparison on one chart: `ℳ̃_T ≅ g^*ℳ̃(U)`.** -/
def chartIso : src ℳ f ψ ≅ tgt ℳ U g where
  hom := phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd
  inv := psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd
  hom_inv_id := phi_psi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd
  inv_hom_id := psi_phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd

/-- The hom of `chartIso` restricted to the pure tensors of degree `n` is `bmap n`. -/
theorem pureTensor_chartIso_hom (n : ℤ) :
    Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n ≫
        (chartIso ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).hom = bmap ℳ U c f hf g hg hgf w n :=
  pureTensor_phi ℳ U c f hf g hg hgf ψ w hCP hw hw' hd n

end Chart

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
