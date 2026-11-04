module

public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import StacksFrontier.CategoryTheory.Bicategory.NaturalTransformation.LocallyDiscrete
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a pseudofunctor along a natural transformation

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat` and let `α : Φ ⟶ Ψ` be a natural
transformation between two functors `C' ⥤ C`. Inverse image along the components `α_a : Φ a ⟶ Ψ a`
is a strong transformation `F.restrict Ψ ⟶ F.restrict Φ` between the two restrictions of `F`
(`CategoryTheory.Pseudofunctor.restrict`): its component at `a` is `α_a^*`, and its naturality
constraint at `φ : b ⟶ a` compares the two factorisations `Ψ(φ)^* ⋙ α_b^*` and `α_a^* ⋙ Φ(φ)^*` of
the inverse image along the common diagonal `α_b ≫ Ψ φ = Φ φ ≫ α_a` of the naturality square.

The typical instance is base change: `Ψ = 𝟭` and `Φ = (- ×_S X)`, with `α` the first projection;
the transformation then sends an object over `U` to its inverse image over `U ×_S X`.

## Main definitions

* `CategoryTheory.Pseudofunctor.restrictNatTrans`: the strong transformation
  `F.restrict Ψ ⟶ F.restrict Φ` induced by `α : Φ ⟶ Ψ`.

## Implementation notes

The two coherences of a strong transformation are proved once for an arbitrary pseudofunctor out
of a strict bicategory, as `mapComp'_inv_comp_mapComp'_hom_whiskerLeft_mapId'` and
`mapComp'_inv_comp_mapComp'_hom_whiskerLeft_mapComp'`, from Mathlib's associativity and unit
constraints of the flexible composition constraint `mapComp'`. No Stacks tag is claimed: this is
bicategorical bookkeeping.
-/

@[expose] public noncomputable section

universe v' u' v u v₁ u₁ w₁ w₂ v₂ u₂

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory

section Strict

variable {B : Type u₁} {D : Type u₂} [Bicategory.{w₁, v₁} B] [Strict B]
  [Bicategory.{w₂, v₂} D] (F : Pseudofunctor B D)

/-- **The unit coherence of the comparison of two factorisations through identities.** If
`u = 𝟙` and `v = 𝟙`, comparing the factorisations `u ≫ x` and `x ≫ v` of `w` and then removing
`v` is removing `u`. -/
lemma mapComp'_inv_comp_mapComp'_hom_whiskerLeft_mapId' {b₀ b₁ : B} (x : b₀ ⟶ b₁)
    (u : b₀ ⟶ b₀) (hu : u = 𝟙 b₀) (v : b₁ ⟶ b₁) (hv : v = 𝟙 b₁) (w : b₀ ⟶ b₁)
    (h₁ : u ≫ x = w) (h₂ : x ≫ v = w) :
    ((F.mapComp' u x w h₁).symm ≪≫ F.mapComp' x v w h₂).hom ≫ F.map x ◁ (F.mapId' v hv).hom =
      (F.mapId' u hu).hom ▷ F.map x ≫ (λ_ _).hom ≫ (ρ_ _).inv := by
  subst hu hv
  obtain rfl : w = x := by simpa using h₁.symm
  rw [mapComp'_id_comp, mapComp'_comp_id, mapId'_eq_mapId, mapId'_eq_mapId]
  simp

/-- **The composition coherence of the comparison of two factorisations.** For two composable
squares `Ψf ≫ A_b = A_a ≫ Φf` and `Ψg ≫ A_c = A_b ≫ Φg` (with diagonals `w_f`, `w_g`) and their
composite square (with diagonal `T`), the comparison for the composite square, followed by the
splitting of `Φ(f ≫ g)`, is the splitting of `Ψ(f ≫ g)` followed by the two comparisons. -/
lemma mapComp'_inv_comp_mapComp'_hom_whiskerLeft_mapComp'
    {Pa Pb Pc Qa Qb Qc : B} (Aa : Pa ⟶ Qa) (Ab : Pb ⟶ Qb) (Ac : Pc ⟶ Qc)
    (Ψf : Pa ⟶ Pb) (Ψg : Pb ⟶ Pc) (Ψfg : Pa ⟶ Pc) (Φf : Qa ⟶ Qb) (Φg : Qb ⟶ Qc)
    (Φfg : Qa ⟶ Qc) (wf : Pa ⟶ Qb) (wg : Pb ⟶ Qc) (T : Pa ⟶ Qc)
    (hΨ : Ψf ≫ Ψg = Ψfg) (hΦ : Φf ≫ Φg = Φfg)
    (h₁f : Ψf ≫ Ab = wf) (h₂f : Aa ≫ Φf = wf) (h₁g : Ψg ≫ Ac = wg) (h₂g : Ab ≫ Φg = wg)
    (h₁ : Ψfg ≫ Ac = T) (h₂ : Aa ≫ Φfg = T) :
    ((F.mapComp' Ψfg Ac T h₁).symm ≪≫ F.mapComp' Aa Φfg T h₂).hom ≫
        F.map Aa ◁ (F.mapComp' Φf Φg Φfg hΦ).hom =
      (F.mapComp' Ψf Ψg Ψfg hΨ).hom ▷ F.map Ac ≫ (α_ _ _ _).hom ≫
        F.map Ψf ◁ ((F.mapComp' Ψg Ac wg h₁g).symm ≪≫ F.mapComp' Ab Φg wg h₂g).hom ≫
        (α_ _ _ _).inv ≫
        ((F.mapComp' Ψf Ab wf h₁f).symm ≪≫ F.mapComp' Aa Φf wf h₂f).hom ▷ F.map Φg ≫
        (α_ _ _ _).hom := by
  have hwfT : wf ≫ Φg = T := by rw [← h₂f, Category.assoc, hΦ, h₂]
  have hwgT : Ψf ≫ wg = T := by rw [← h₁g, ← Category.assoc, hΨ, h₁]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom Aa Φf Φg wf Φfg T h₂f hΦ h₂,
    F.mapComp'₀₂₃_hom Ψf Ab Φg wf wg T h₁f h₂g hwfT]
  simp only [Category.assoc]
  rw [F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_assoc Ψf Ψg Ac Ψfg wg T hΨ h₁g h₁]

end Strict

variable {C : Type u} [Category.{v} C] {C' : Type u₁} [Category.{v₁} C']
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {Φ Ψ : C' ⥤ C}

/-- The unit constraint of the restriction of a pseudofunctor is the flexible unit constraint of
the original one at the image of the identity. -/
lemma restrict_mapId (ι : C' ⥤ C) (a : LocallyDiscrete C'ᵒᵖ) :
    (F.restrict ι).mapId a = F.mapId' (ι.map (𝟙 a.as.unop)).op.toLoc (by simp) := by
  rfl

variable (α : Φ ⟶ Ψ)

/-- In `LocallyDiscrete Cᵒᵖ`, the composite of `Ψ φ` and `α_b` is the diagonal `Φ φ ≫ α_a` of
the naturality square of `α` at `φ`. -/
lemma restrictNatTrans_comp₁ {a b : C'} (φ : b ⟶ a) :
    (Ψ.map φ).op.toLoc ≫ (α.app b).op.toLoc = (Φ.map φ ≫ α.app a).op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, α.naturality]

/-- In `LocallyDiscrete Cᵒᵖ`, the composite of `α_a` and `Φ φ` is the diagonal `Φ φ ≫ α_a` of
the naturality square of `α` at `φ`. -/
lemma restrictNatTrans_comp₂ {a b : C'} (φ : b ⟶ a) :
    (α.app a).op.toLoc ≫ (Φ.map φ).op.toLoc = (Φ.map φ ≫ α.app a).op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp]

/-- The naturality constraint of `CategoryTheory.Pseudofunctor.restrictNatTrans` at `φ : b ⟶ a`:
the two factorisations of the inverse image along the diagonal of the naturality square. -/
@[sga "4 XVII 3.3.3" "special case"]
def restrictNatTransNaturality {a b : C'} (φ : b ⟶ a) :
    F.map (Ψ.map φ).op.toLoc ≫ F.map (α.app b).op.toLoc ≅
      F.map (α.app a).op.toLoc ≫ F.map (Φ.map φ).op.toLoc :=
  (F.mapComp' _ _ _ (restrictNatTrans_comp₁ α φ)).symm ≪≫
    F.mapComp' _ _ _ (restrictNatTrans_comp₂ α φ)

/-- **Inverse image along a natural transformation of the base, as a strong transformation.**
For `α : Φ ⟶ Ψ` between functors `C' ⥤ C`, the components `α_a^*` form a strong transformation
from the restriction of `F` along `Ψ` to its restriction along `Φ`. -/
@[sga "4 XVII 3.3.3" "special case"]
def restrictNatTrans : (F.restrict Ψ).StrongTrans (F.restrict Φ) :=
  strongTransOfIsLocallyDiscrete (F.restrict Ψ) (F.restrict Φ)
    (fun a ↦ F.map (α.app a.as.unop).op.toLoc)
    (fun {_ _} f ↦ F.restrictNatTransNaturality α f.as.unop)
    (fun a ↦ by
      rw [restrict_mapId, restrict_mapId]
      exact F.mapComp'_inv_comp_mapComp'_hom_whiskerLeft_mapId' (α.app a.as.unop).op.toLoc
        (Ψ.map (𝟙 a.as.unop)).op.toLoc (by simp) (Φ.map (𝟙 a.as.unop)).op.toLoc (by simp)
        (Φ.map (𝟙 a.as.unop) ≫ α.app a.as.unop).op.toLoc
        (restrictNatTrans_comp₁ α (𝟙 a.as.unop)) (restrictNatTrans_comp₂ α (𝟙 a.as.unop)))
    (fun {a b c} f g ↦
      F.mapComp'_inv_comp_mapComp'_hom_whiskerLeft_mapComp'
        (α.app a.as.unop).op.toLoc (α.app b.as.unop).op.toLoc (α.app c.as.unop).op.toLoc
        (Ψ.map f.as.unop).op.toLoc (Ψ.map g.as.unop).op.toLoc
        (Ψ.map (g.as.unop ≫ f.as.unop)).op.toLoc
        (Φ.map f.as.unop).op.toLoc (Φ.map g.as.unop).op.toLoc
        (Φ.map (g.as.unop ≫ f.as.unop)).op.toLoc
        (Φ.map f.as.unop ≫ α.app a.as.unop).op.toLoc (Φ.map g.as.unop ≫ α.app b.as.unop).op.toLoc
        (Φ.map (g.as.unop ≫ f.as.unop) ≫ α.app a.as.unop).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Ψ.map_comp])
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Φ.map_comp])
        (restrictNatTrans_comp₁ α f.as.unop) (restrictNatTrans_comp₂ α f.as.unop)
        (restrictNatTrans_comp₁ α g.as.unop) (restrictNatTrans_comp₂ α g.as.unop)
        (restrictNatTrans_comp₁ α (g.as.unop ≫ f.as.unop))
        (restrictNatTrans_comp₂ α (g.as.unop ≫ f.as.unop)))

/-- The component of `F.restrictNatTrans α` at `a` is the inverse image functor along `α_a`. -/
@[simp]
lemma restrictNatTrans_app (a : LocallyDiscrete C'ᵒᵖ) :
    (F.restrictNatTrans α).app a = F.map (α.app a.as.unop).op.toLoc :=
  rfl

/-- The naturality constraint of `F.restrictNatTrans α` at `f` is
`F.restrictNatTransNaturality α f.as.unop`. -/
@[simp]
lemma restrictNatTrans_naturality {a b : LocallyDiscrete C'ᵒᵖ} (f : a ⟶ b) :
    (F.restrictNatTrans α).naturality f = F.restrictNatTransNaturality α f.as.unop :=
  rfl

end CategoryTheory.Pseudofunctor

end
