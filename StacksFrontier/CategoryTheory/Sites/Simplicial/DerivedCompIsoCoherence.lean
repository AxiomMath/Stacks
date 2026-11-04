module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.DerivedCocycleSystem

/-!
# The cocycle law for the compositor of derived functors of four exact functors

`CategoryTheory.derivedCompIso` identifies the derived functor of a composite of exact functors
with the composite of their derived functors. For four exact functors `F₁`, `F₂`, `F₃`, `F₄`
there are two ways of splitting the derived functor of `F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄` into the four derived
functors by compositors, and this file proves that they agree. The proof combines three instances
of the threefold cocycle law `CategoryTheory.derivedCompIso_pentagon` with the naturality of one
compositor.

## Main results

* `CategoryTheory.derivedCompIso_four`: the two splittings of the derived functor of
  `F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄` into the four derived functors, through `(F₁ ⋙ F₂ ⋙ F₃) ⋙ F₄` and through
  `(F₁ ⋙ F₂) ⋙ F₃ ⋙ F₄`, agree.

## References

* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

section Pentagon

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (G : B ⥤ C) (K : C ⥤ D) (FG : A ⥤ C) (GK : B ⥤ D) (H : A ⥤ D)
  [F.Additive] [G.Additive] [K.Additive] [FG.Additive] [GK.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [PreservesFiniteLimits GK] [PreservesFiniteColimits GK]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end Pentagon

section Fourfold

/-- Given the equalities `b ≫ a = r ≫ s`, `s ≫ x = t ≫ d'`, `c ≫ y = r ≫ t`, `y ≫ d' = d ≫ z`
and `z ≫ z' = 𝟙`, the composite `b ≫ a ≫ x ≫ z'` equals `c ≫ d`. -/
private theorem pentagon_chain {Z : Type*} [Category Z] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : Z}
    (a : o₁ ⟶ o₀) (b : o₂ ⟶ o₁) (c : o₂ ⟶ o₃) (d : o₃ ⟶ o₄) (d' : o₇ ⟶ o₆)
    (x : o₀ ⟶ o₆) (y : o₃ ⟶ o₇) (z : o₄ ⟶ o₆) (z' : o₆ ⟶ o₄)
    (r : o₂ ⟶ o₅) (s : o₅ ⟶ o₀) (t : o₅ ⟶ o₇)
    (hba : b ≫ a = r ≫ s) (hsx : s ≫ x = t ≫ d') (hcy : c ≫ y = r ≫ t)
    (hyd : y ≫ d' = d ≫ z) (hz : z ≫ z' = 𝟙 o₄) :
    b ≫ a ≫ x ≫ z' = c ≫ d := by
  rw [reassoc_of% hba, reassoc_of% hsx, ← reassoc_of% hcy, reassoc_of% hyd, hz,
    Category.comp_id]

/-- If `p ≫ p' = 𝟙`, `q ≫ q' = 𝟙` and `q' ≫ p' ≫ r = c ≫ d`, then `p ≫ q ≫ c ≫ d = r`. -/
private theorem comp_cancel_prefix {Z : Type*} [Category Z] {o₀ o₁ o₂ o₃ o₄ : Z}
    (p : o₀ ⟶ o₁) (p' : o₁ ⟶ o₀) (q : o₁ ⟶ o₂) (q' : o₂ ⟶ o₁) (c : o₂ ⟶ o₃) (d : o₃ ⟶ o₄)
    (r : o₀ ⟶ o₄) (hp : p ≫ p' = 𝟙 o₀) (hq : q ≫ q' = 𝟙 o₁)
    (key : q' ≫ p' ≫ r = c ≫ d) :
    p ≫ q ≫ c ≫ d = r := by
  rw [← key, ← Category.assoc q, hq, Category.id_comp, ← Category.assoc, hp, Category.id_comp]

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ w₁ w₂ w₃ w₄ w₅

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  {E : Type u₅} [Category.{v₅} E] [Abelian E] [HasDerivedCategory.{w₅} E]
  (F₁ : A ⥤ B) (F₂ : B ⥤ C) (F₃ : C ⥤ D) (F₄ : D ⥤ E)
  [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]

/-- **The coherence of the derived compositor for four exact functors.** The derived functor of
`F₁ ⋙ F₂ ⋙ F₃ ⋙ F₄` is split into the four derived functors in two ways by the compositors —
through `(F₁ ⋙ F₂ ⋙ F₃) ⋙ F₄`, first separating the outer factor and then the inner two, and
through `(F₁ ⋙ F₂) ⋙ F₃ ⋙ F₄`, separating the two halves and then each half — and the two
agree at every object `X` of the derived category of `A`. -/
theorem derivedCompIso_four (X : DerivedCategory A) :
    F₄.mapDerivedCategory.map
          ((derivedCompIso F₁ (F₂ ⋙ F₃) (F₁ ⋙ F₂ ⋙ F₃) (Iso.refl _)).inv.app X) ≫
        (derivedCompIso (F₁ ⋙ F₂ ⋙ F₃) F₄ ((F₁ ⋙ F₂ ⋙ F₃) ⋙ F₄) (Iso.refl _)).inv.app X ≫
          (derivedCompIso (F₁ ⋙ F₂) (F₃ ⋙ F₄) ((F₁ ⋙ F₂) ⋙ F₃ ⋙ F₄) (Iso.refl _)).hom.app X ≫
            (derivedCompIso F₃ F₄ (F₃ ⋙ F₄) (Iso.refl _)).hom.app
              ((F₁ ⋙ F₂).mapDerivedCategory.obj X) =
      F₄.mapDerivedCategory.map
          ((derivedCompIso F₂ F₃ (F₂ ⋙ F₃) (Iso.refl _)).hom.app
            (F₁.mapDerivedCategory.obj X)) ≫
        F₄.mapDerivedCategory.map (F₃.mapDerivedCategory.map
          ((derivedCompIso F₁ F₂ (F₁ ⋙ F₂) (Iso.refl _)).inv.app X)) := by
  have hba := congr_app (derivedCompIso_pentagon F₁ (F₂ ⋙ F₃) F₄ (F₁ ⋙ F₂ ⋙ F₃)
    ((F₂ ⋙ F₃) ⋙ F₄) ((F₁ ⋙ F₂ ⋙ F₃) ⋙ F₄) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (fun Y => by simp)) X
  have hsx := congr_app (derivedCompIso_pentagon F₂ F₃ F₄ (F₂ ⋙ F₃) (F₃ ⋙ F₄)
    ((F₂ ⋙ F₃) ⋙ F₄) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fun Y => by simp)) (F₁.mapDerivedCategory.obj X)
  have hcy := congr_app (derivedCompIso_pentagon F₁ F₂ (F₃ ⋙ F₄) (F₁ ⋙ F₂) (F₂ ⋙ F₃ ⋙ F₄)
    ((F₁ ⋙ F₂) ⋙ F₃ ⋙ F₄) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fun Y => by simp)) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hba hsx hcy
  have hyd := (derivedCompIso F₃ F₄ (F₃ ⋙ F₄) (Iso.refl _)).hom.naturality
    ((derivedCompIso F₁ F₂ (F₁ ⋙ F₂) (Iso.refl _)).hom.app X)
  have hz : (F₃.mapDerivedCategory ⋙ F₄.mapDerivedCategory).map
        ((derivedCompIso F₁ F₂ (F₁ ⋙ F₂) (Iso.refl _)).hom.app X) ≫
      F₄.mapDerivedCategory.map (F₃.mapDerivedCategory.map
        ((derivedCompIso F₁ F₂ (F₁ ⋙ F₂) (Iso.refl _)).inv.app X)) = 𝟙 _ := by
    simp only [Functor.comp_map, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Functor.comp_obj]
  refine comp_cancel_prefix _ (F₄.mapDerivedCategory.map
      ((derivedCompIso F₁ (F₂ ⋙ F₃) (F₁ ⋙ F₂ ⋙ F₃) (Iso.refl _)).hom.app X)) _
    ((derivedCompIso (F₁ ⋙ F₂ ⋙ F₃) F₄ ((F₁ ⋙ F₂ ⋙ F₃) ⋙ F₄) (Iso.refl _)).hom.app X)
    _ _ _ ?_ (Iso.inv_hom_id_app _ _) ?_
  · rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  · exact pentagon_chain _ _ _ _ _ _ _ _ _ _ _ _ hba hsx hcy hyd hz

end Fourfold

section Unit

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B]
  (F : A ⥤ B) (U : B ⥤ B) (H : A ⥤ B) [F.Additive] [U.Additive] [H.Additive]

end Unit

section DerivedUnit

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) (U : B ⥤ B) (H : A ⥤ B) [F.Additive] [U.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end DerivedUnit

end CategoryTheory

end
