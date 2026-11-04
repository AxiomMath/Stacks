module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemOpens
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement

/-!
# Recognising the canonical descent datum of a module, for a system of sheaves of rings

Let `𝓡` be a system of sheaves of rings on the big h category over `S`, let `f i : X i ⟶ U` be
a family admitting chosen fibre products, let `D` be a descent datum for the pseudofunctor of
modules of `𝓡` along `f`, and let `G` be a module on `U` together with isomorphisms
`e i : (f i)^* G ≅ D.obj i`. This file shows that the `e i` form an isomorphism between the
canonical descent datum of `G` and `D` as soon as their transposes `G ⟶ (f i)_* D.obj i` are
compatible with the gluing morphisms of `D` over the chosen fibre products — a condition about
morphisms of modules on `U`, which is where a gluing construction can check it on sections.

## Main results

* `AlgebraicGeometry.BigHOver.RingSheafSystem.pull_map_comp_eq_of_homEquiv`: the compatibility
  over one fibre product, from the condition on transposes.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.comm_toDescentData`: the same against the
  canonical descent datum of the module, in the spelling of the pseudofunctor of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (𝓡 : RingSheafSystem B S hS)

/-- **The compatibility of two morphisms out of restrictions of a module over a fibre product,
from the compatibility of their transposes.** -/
lemma pull_map_comp_eq_of_homEquiv {U X₁ X₂ Y : BigHOver B S hS} (a : X₁ ⟶ U) (b : X₂ ⟶ U)
    (p₁ : Y ⟶ X₁) (p₂ : Y ⟶ X₂) (q : Y ⟶ U) (h₁ : p₁ ≫ a = q) (h₂ : p₂ ≫ b = q)
    (G : SheafOfModules.{u} (𝓡.ring U)) {M₁ : SheafOfModules.{u} (𝓡.ring X₁)}
    {M₂ : SheafOfModules.{u} (𝓡.ring X₂)} (e₁ : (𝓡.pull a.op).obj G ⟶ M₁)
    (e₂ : (𝓡.pull b.op).obj G ⟶ M₂) (φ : (𝓡.pull p₁.op).obj M₁ ⟶ (𝓡.pull p₂.op).obj M₂)
    (hyp : (𝓡.adj a).homEquiv G M₁ e₁ ≫ 𝓡.etaG p₁ a q h₁ M₁ ≫ (𝓡.push q).map φ =
      (𝓡.adj b).homEquiv G M₂ e₂ ≫ 𝓡.etaG p₂ b q h₂ M₂) :
    (𝓡.pull p₁.op).map e₁ ≫ φ =
      (𝓡.compInv a p₁ q h₁ G ≫ 𝓡.compHom b p₂ q h₂ G) ≫ (𝓡.pull p₂.op).map e₂ := by
  rw [← cancel_epi (𝓡.compHom a p₁ q h₁ G), Category.assoc, compHom_compInv_assoc]
  apply ((𝓡.adj q).homEquiv _ _).injective
  have l := 𝓡.homEquiv_mapComp'_hom a p₁ q h₁ e₁ φ
  have r := 𝓡.homEquiv_mapComp'_hom b p₂ q h₂ e₂ (𝟙 _)
  rw [Category.comp_id] at r
  have r' := 𝓡.etaG_comp_push_map p₂ b q h₂ M₂ (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at r'
  rw [l, r, ← 𝓡.etaG_comp_push_map, ← r']
  simpa only [Category.assoc] using hyp

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.pull_map_comp_eq_of_homEquiv` with its conclusion
in the spelling of the pseudofunctor of modules. -/
lemma pull_map_comp_eq_of_homEquiv' {U X₁ X₂ Y : BigHOver B S hS} (a : X₁ ⟶ U) (b : X₂ ⟶ U)
    (p₁ : Y ⟶ X₁) (p₂ : Y ⟶ X₂) (q : Y ⟶ U) (h₁ : p₁ ≫ a = q) (h₂ : p₂ ≫ b = q)
    (G : 𝓡.modulePseudofunctor.obj ⟨op U⟩) {M₁ : 𝓡.modulePseudofunctor.obj ⟨op X₁⟩}
    {M₂ : 𝓡.modulePseudofunctor.obj ⟨op X₂⟩}
    (e₁ : (𝓡.modulePseudofunctor.map a.op.toLoc).toFunctor.obj G ⟶ M₁)
    (e₂ : (𝓡.modulePseudofunctor.map b.op.toLoc).toFunctor.obj G ⟶ M₂)
    (φ : (𝓡.modulePseudofunctor.map p₁.op.toLoc).toFunctor.obj M₁ ⟶
      (𝓡.modulePseudofunctor.map p₂.op.toLoc).toFunctor.obj M₂)
    (hyp : (𝓡.adj a).homEquiv G M₁ e₁ ≫ 𝓡.etaG p₁ a q h₁ M₁ ≫ (𝓡.push q).map φ =
      (𝓡.adj b).homEquiv G M₂ e₂ ≫ 𝓡.etaG p₂ b q h₂ M₂)
    (k₁ : a.op.toLoc ≫ p₁.op.toLoc = q.op.toLoc) (k₂ : b.op.toLoc ≫ p₂.op.toLoc = q.op.toLoc) :
    (𝓡.modulePseudofunctor.map p₁.op.toLoc).toFunctor.map e₁ ≫ φ =
      ((𝓡.modulePseudofunctor.mapComp' a.op.toLoc p₁.op.toLoc q.op.toLoc k₁).inv.toNatTrans.app G ≫
        (𝓡.modulePseudofunctor.mapComp' b.op.toLoc p₂.op.toLoc q.op.toLoc k₂).hom.toNatTrans.app
          G) ≫ (𝓡.modulePseudofunctor.map p₂.op.toLoc).toFunctor.map e₂ := by
  rw [mapComp'_inv_app_eq_compInv _ _ _ _ _ h₁, mapComp'_hom_app_eq_compHom _ _ _ _ _ h₂,
    modulePseudofunctor_map_map, modulePseudofunctor_map_map]
  exact 𝓡.pull_map_comp_eq_of_homEquiv a b p₁ p₂ q h₁ h₂ G e₁ e₂ φ hyp

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.pull_map_comp_eq_of_homEquiv'` against the
canonical descent datum of a module. -/
lemma comm_toDescentData {ι' : Type u} {U : BigHOver B S hS} {X : ι' → BigHOver B S hS}
    (f : ∀ i, X i ⟶ U) (D : 𝓡.modulePseudofunctor.DescentData f)
    (G : 𝓡.modulePseudofunctor.obj ⟨op U⟩) {Y : BigHOver B S hS} (q : Y ⟶ U) {i j : ι'}
    (p₁ : Y ⟶ X i) (p₂ : Y ⟶ X j) (h₁ : p₁ ≫ f i = q) (h₂ : p₂ ≫ f j = q)
    (e₁ : (𝓡.modulePseudofunctor.map (f i).op.toLoc).toFunctor.obj G ⟶ D.obj i)
    (e₂ : (𝓡.modulePseudofunctor.map (f j).op.toLoc).toFunctor.obj G ⟶ D.obj j)
    (hyp : (𝓡.adj (f i)).homEquiv G (D.obj i) e₁ ≫ 𝓡.etaG p₁ (f i) q h₁ (D.obj i) ≫
        (𝓡.push q).map (D.hom q p₁ p₂ h₁ h₂) =
      (𝓡.adj (f j)).homEquiv G (D.obj j) e₂ ≫ 𝓡.etaG p₂ (f j) q h₂ (D.obj j)) :
    (𝓡.modulePseudofunctor.map p₁.op.toLoc).toFunctor.map e₁ ≫ D.hom q p₁ p₂ h₁ h₂ =
      ((𝓡.modulePseudofunctor.toDescentData f).obj G).hom q p₁ p₂ h₁ h₂ ≫
        (𝓡.modulePseudofunctor.map p₂.op.toLoc).toFunctor.map e₂ :=
  𝓡.pull_map_comp_eq_of_homEquiv' (f i) (f j) p₁ p₂ q h₁ h₂ G e₁ e₂ (D.hom q p₁ p₂ h₁ h₂) hyp _ _

end AlgebraicGeometry.BigHOver.RingSheafSystem
