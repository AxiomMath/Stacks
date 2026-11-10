module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Global sections of a presheaf of sets

The *global sections* of a presheaf of sets `F` on `C` form the set
`Γ(C, F) = Mor_{PSh(C)}(*, F)`, where `*` is the final object of the category of presheaves on
`C`, the presheaf sending every object to a singleton.

## Main definitions

* `CategoryTheory.Presheaf.isTerminalConstPUnit`: the presheaf constant at a singleton is final.
* `CategoryTheory.Presheaf.globalSections`: the hom-set `Γ(C, F)` out of the final presheaf.
* `CategoryTheory.Presheaf.globalSectionsEquivSections`: `Γ(C, F)` is equivalent to `F.sections`.

## Main results

* `CategoryTheory.Sheaf.Γ_hom_ext`: a natural transformation out of the global-sections functor
  of sheaves of sets is determined by its value at the terminal sheaf.
-/

@[expose] public section

namespace CategoryTheory.Presheaf

open Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C]

/-- The presheaf constant at a singleton is the final object of the category of presheaves
on `C`. -/
@[stacks 06UN]
def isTerminalConstPUnit :
    IsTerminal ((Functor.const Cᵒᵖ).obj (PUnit.{w + 1})) :=
  Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit

/-- The *global sections* of a presheaf of sets `F` on `C`: the set
`Γ(C, F) = Mor_{PSh(C)}(*, F)` of morphisms of presheaves from the final presheaf `*` to `F`. -/
@[stacks 06UN]
abbrev globalSections (F : Cᵒᵖ ⥤ Type w) : Type _ := (⊤_ (Cᵒᵖ ⥤ Type w)) ⟶ F

/-- The global sections of `F` are the compatible families of sections of `F`, i.e.
Mathlib's `Functor.sections`. -/
@[sga "3 I 2.3.3.1" "partial"]
noncomputable def globalSectionsEquivSections (F : Cᵒᵖ ⥤ Type w) :
    globalSections F ≃ F.sections := by
  refine Equiv.trans ?_ (F.sectionsEquivHom PUnit.{w + 1}).symm
  exact Iso.homCongr (terminalIsoIsTerminal isTerminalConstPUnit) (Iso.refl F)

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf
open Limits Opposite
universe w v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasTerminal C]
  [HasWeakSheafify J (Type w)]

/-- The global sections of the terminal sheaf of sets form a subsingleton. -/
lemma subsingleton_Γ_obj_terminal {T : C} (hT : IsTerminal T) :
    Subsingleton ((Γ J (Type w)).obj (Sheaf.terminal J Types.isTerminalPUnit.{w})) := by
  refine ⟨fun a b => ?_⟩
  have e := (ΓNatIsoSheafSections J (Type w) hT).app (Sheaf.terminal J Types.isTerminalPUnit.{w})
  exact ((isIso_iff_bijective e.hom).mp inferInstance).1
    (Subsingleton.elim (α := PUnit.{w + 1}) _ _)

/-- On a site with a terminal object, two natural transformations `Γ ⟶ K` out of the
global-sections functor of sheaves of sets agree as soon as `K` takes the terminal sheaf to a
subsingleton. -/
lemma Γ_hom_ext {T : C} (hT : IsTerminal T) {K : Sheaf J (Type w) ⥤ Type w}
    (α β : Γ J (Type w) ⟶ K)
    (h : Subsingleton (K.obj (Sheaf.terminal J Types.isTerminalPUnit.{w}))) : α = β := by
  let e := ΓNatIsoSheafSections J (Type w) hT
  ext F σ
  let τ : F.obj.obj (op T) := e.hom.app F σ
  let φ₀ : (Sheaf.terminal J Types.isTerminalPUnit.{w}).obj ⟶ F.obj :=
    NatTrans.mk (fun V => TypeCat.ofHom (fun _ => F.obj.map (hT.from V.unop).op τ))
      (fun V V' g => by
        ext x
        change F.obj.map (hT.from V'.unop).op τ = F.obj.map g (F.obj.map (hT.from V.unop).op τ)
        rw [show (hT.from V'.unop).op = (hT.from V.unop).op ≫ g from
          Quiver.Hom.unop_inj (hT.hom_ext _ _)]
        exact Functor.map_comp_apply F.obj _ _ τ)
  let φ : Sheaf.terminal J Types.isTerminalPUnit.{w} ⟶ F := ObjectProperty.homMk φ₀
  let pt : (Γ J (Type w)).obj (Sheaf.terminal J Types.isTerminalPUnit.{w}) :=
    e.inv.app _ PUnit.unit
  have hσ : (Γ J (Type w)).map φ pt = σ := by
    apply ((isIso_iff_bijective (e.hom.app F)).mp inferInstance).1
    have hn := ConcreteCategory.congr_hom (e.hom.naturality φ) pt
    have hpt : e.hom.app _ pt = PUnit.unit := Subsingleton.elim (α := PUnit.{w + 1}) _ _
    simp only [CategoryTheory.comp_apply, hpt] at hn
    refine hn.trans ?_
    change F.obj.map (hT.from T).op τ = τ
    rw [hT.hom_ext (hT.from T) (𝟙 T), op_id, Functor.map_id, CategoryTheory.id_apply]
  have hα := ConcreteCategory.congr_hom (α.naturality φ) pt
  have hβ := ConcreteCategory.congr_hom (β.naturality φ) pt
  simp only [CategoryTheory.comp_apply, hσ] at hα hβ
  exact hα.trans ((congrArg _ (Subsingleton.elim _ _)).trans hβ.symm)

end CategoryTheory.Sheaf

