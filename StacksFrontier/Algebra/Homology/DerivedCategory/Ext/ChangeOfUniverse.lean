module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The change of universe of `Ext` respects composition

Mathlib's `CategoryTheory.Abelian.Ext.chgUniv` identifies `Ext.{w} X Y n` with `Ext.{w'} X Y n`.
This identification commutes with composition and sends `Ext.mk₀ f` to `Ext.mk₀ f`.

## Main results

* `CategoryTheory.Abelian.Ext.chgUniv_comp`: the identification commutes with composition.
* `CategoryTheory.Abelian.Ext.chgUniv_mk₀`: it sends `Ext.mk₀ f` to `Ext.mk₀ f`.
* `CategoryTheory.Abelian.Ext.chgUniv_add` and `CategoryTheory.Abelian.Ext.chgUnivAddEquiv`: the
  identification is additive.
* `CategoryTheory.Abelian.Ext.chgUniv_mapExactFunctor`: it commutes with the action of an exact
  functor.
-/

@[expose] public section

universe w w' w₁ w₂ v u v₂ u₂

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasExt.{w'} C] {X Y Z : C}

/-- **The change of universe of `Ext` commutes with composition.** -/
lemma chgUniv_comp {a b c : ℕ} (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b) (h : a + b = c) :
    chgUniv.{w'} (α.comp β h) = (chgUniv.{w'} α).comp (chgUniv.{w'} β) h := by
  let := HasDerivedCategory.standard C
  ext
  rw [comp_hom]
  change homEquiv (chgUniv.{w'} (α.comp β h)) =
    (homEquiv (chgUniv.{w'} α)).comp (homEquiv (chgUniv.{w'} β)) _
  rw [homEquiv_chgUniv, homEquiv_chgUniv, homEquiv_chgUniv]
  exact comp_hom α β h

/-- **The change of universe of `Ext` sends `Ext.mk₀ f` to `Ext.mk₀ f`.** -/
lemma chgUniv_mk₀ (f : X ⟶ Y) : chgUniv.{w'} (mk₀.{w} f) = mk₀.{w'} f := by
  let := HasDerivedCategory.standard C
  ext
  change homEquiv (chgUniv.{w'} (mk₀.{w} f)) = homEquiv (mk₀.{w'} f)
  rw [homEquiv_chgUniv]
  change (mk₀.{w} f).hom = (mk₀.{w'} f).hom
  rw [mk₀_hom, mk₀_hom]

/-- **The change of universe of `Ext` is additive.** -/
lemma chgUniv_add {n : ℕ} (α β : Ext.{w} X Y n) :
    chgUniv.{w'} (α + β) = chgUniv.{w'} α + chgUniv.{w'} β := by
  let := HasDerivedCategory.standard C
  ext
  rw [add_hom]
  change homEquiv (chgUniv.{w'} (α + β)) =
    homEquiv (chgUniv.{w'} α) + homEquiv (chgUniv.{w'} β)
  rw [homEquiv_chgUniv, homEquiv_chgUniv, homEquiv_chgUniv]
  exact add_hom α β

/-- The change of universe of `Ext`, as an additive equivalence. -/
noncomputable def chgUnivAddEquiv {n : ℕ} : Ext.{w} X Y n ≃+ Ext.{w'} X Y n :=
  { chgUniv.{w'} with map_add' := chgUniv_add }

/-- **The change of universe of `Ext` commutes with the action of an exact functor.** -/
lemma chgUniv_mapExactFunctor {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [HasExt.{w₁} D] [HasExt.{w₂} D] {n : ℕ} (e : Ext.{w} X Y n) :
    chgUniv.{w₂} (Ext.mapExactFunctor.{w, w₁} F e) =
      (Ext.mapExactFunctor.{w', w₂} F (chgUniv.{w'} e)) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  ext
  change homEquiv (chgUniv.{w₂} (Ext.mapExactFunctor.{w, w₁} F e)) =
    homEquiv (Ext.mapExactFunctor.{w', w₂} F (chgUniv.{w'} e))
  rw [homEquiv_chgUniv]
  change (Ext.mapExactFunctor.{w, w₁} F e).hom =
    (Ext.mapExactFunctor.{w', w₂} F (chgUniv.{w'} e)).hom
  rw [mapExactFunctor_hom, mapExactFunctor_hom]
  congr 3
  change homEquiv e = homEquiv (chgUniv.{w'} e)
  rw [homEquiv_chgUniv]

end CategoryTheory.Abelian.Ext

end
