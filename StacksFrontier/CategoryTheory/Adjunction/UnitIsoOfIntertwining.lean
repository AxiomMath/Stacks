module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Yoneda

/-!
# Transferring invertibility of the unit of an adjunction along intertwined functors

Let `F ⊣ G` be an adjunction between categories `C` and `D`, with unit `η : 𝟭 ⟶ F ⋙ G`.
The component `η_X` is an isomorphism exactly when `F` is bijective on morphisms into `X`:
`F : (P ⟶ X) → (F P ⟶ F X)` for every `P`, because composing with `η_X` is that map followed by
the hom-set bijection of the adjunction.

That criterion lets invertibility of the unit travel.  Suppose `K : C ⥤ C` is fully faithful,
`K' : D ⥤ D` is faithful, and `F` intertwines them: `F ∘ K ≅ K' ∘ F` naturally.  Then
`F : (P ⟶ X) → (F P ⟶ F X)` followed by `K'` is, up to the intertwining isomorphisms, `K`
followed by `F : (K P ⟶ K X) → (F K P ⟶ F K X)`.  So if `η_{K X}` is an isomorphism then so is
`η_X`.

The case in view is tensoring by an invertible module: for a morphism of ringed topoi the inverse
image commutes with tensor products, so `K = N' ⊗ -` and `K' = f^*N' ⊗ -` are intertwined, both
are equivalences when `N'` is invertible, and `K N ≅ 𝒪` when `N'` is a tensor inverse of `N`.
The unit at `N` is then an isomorphism as soon as the unit at `𝒪` is.

## Main results

* `CategoryTheory.Functor.bijective_map_of_intertwining`: `F` is bijective on `P ⟶ X` when it
  is bijective on `K P ⟶ K X`, for `K` fully faithful intertwined by `F` with a faithful `K'`.
* `CategoryTheory.Functor.bijective_map_iff_of_iso`: bijectivity of `F` on a hom set only
  depends on the endpoints up to isomorphism.
* `CategoryTheory.Adjunction.isIso_unit_app_iff_bijective_map`: `η_X` is an isomorphism exactly
  when `F` is bijective on morphisms into `X`.
* `CategoryTheory.Adjunction.isIso_unit_app_of_intertwining`: `η_X` is an isomorphism when
  `η_{K X}` is, for `K` fully faithful intertwined by `F` with a faithful `K'`.
* `CategoryTheory.Adjunction.isIso_unit_app_of_intertwining_of_iso`: the same with `K X`
  isomorphic to an object at which the unit is known to be an isomorphism.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D]

/-- **Bijectivity of a functor on a hom set is invariant under isomorphisms of the endpoints.** -/
theorem bijective_map_iff_of_iso (F : C ⥤ D) {P P' X X' : C} (e₁ : P ≅ P') (e₂ : X ≅ X') :
    Function.Bijective (fun f : P ⟶ X => F.map f) ↔
      Function.Bijective (fun f : P' ⟶ X' => F.map f) := by
  have h : (fun f : P' ⟶ X' => F.map f) ∘ e₁.homCongr e₂ =
      (F.mapIso e₁).homCongr (F.mapIso e₂) ∘ (fun f : P ⟶ X => F.map f) := by
    funext f
    simp [Iso.homCongr_apply]
  rw [← Function.Bijective.of_comp_iff _ (e₁.homCongr e₂).bijective, h,
    Function.Bijective.of_comp_iff' ((F.mapIso e₁).homCongr (F.mapIso e₂)).bijective]

/-- **Bijectivity of `F` on morphisms transfers along intertwined endofunctors.**  Let `K` be a
fully faithful endofunctor of `C` and `K'` a faithful endofunctor of `D`, intertwined by `F`
through isomorphisms `F (K Y) ≅ K' (F Y)` natural in `Y`.  If `F` is bijective on morphisms
`K P ⟶ K X` then it is bijective on morphisms `P ⟶ X`. -/
theorem bijective_map_of_intertwining (F : C ⥤ D) (K : C ⥤ C) (K' : D ⥤ D)
    [K.Full] [K.Faithful] [K'.Faithful]
    (α : ∀ Y : C, F.obj (K.obj Y) ≅ K'.obj (F.obj Y))
    (hα : ∀ {Y Y' : C} (f : Y ⟶ Y'),
      F.map (K.map f) ≫ (α Y').hom = (α Y).hom ≫ K'.map (F.map f))
    (P X : C) (h : Function.Bijective (fun g : K.obj P ⟶ K.obj X => F.map g)) :
    Function.Bijective (fun f : P ⟶ X => F.map f) := by
  have hcomp : (fun f : P ⟶ X => K'.map (F.map f)) =
      (α P).homCongr (α X) ∘ (fun g : K.obj P ⟶ K.obj X => F.map g) ∘
        (fun f : P ⟶ X => K.map f) := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, hα f, Iso.inv_hom_id_assoc]
  have hb : Function.Bijective (fun f : P ⟶ X => K'.map (F.map f)) := by
    rw [hcomp]
    exact ((α P).homCongr (α X)).bijective.comp
      (h.comp ((Functor.FullyFaithful.ofFullyFaithful K).map_bijective P X))
  refine ⟨fun f₁ f₂ h => hb.1 (by simp only [h]), fun ψ => ?_⟩
  obtain ⟨f, hf⟩ := hb.2 (K'.map ψ)
  exact ⟨f, K'.map_injective hf⟩

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}

/-- **The unit at `X` is an isomorphism exactly when `F` is bijective on morphisms into `X`.**
Composing with the unit at `X` is `F` followed by the hom-set bijection of the adjunction, and
an arrow is an isomorphism exactly when composing with it is bijective on every hom set. -/
theorem isIso_unit_app_iff_bijective_map (adj : F ⊣ G) (X : C) :
    IsIso (adj.unit.app X) ↔ ∀ P : C, Function.Bijective (fun f : P ⟶ X => F.map f) := by
  rw [isIso_iff_yoneda_map_bijective]
  refine forall_congr' fun P => ?_
  have h : (fun f : P ⟶ X => f ≫ adj.unit.app X) =
      adj.homEquiv P (F.obj X) ∘ (fun f : P ⟶ X => F.map f) := by
    funext f
    simp [Adjunction.homEquiv_unit]
  change Function.Bijective (fun f : P ⟶ X => f ≫ adj.unit.app X) ↔ _
  rw [h, Function.Bijective.of_comp_iff' (adj.homEquiv P (F.obj X)).bijective]

/-- **The unit is an isomorphism at `X` when it is one at `K X`**, for an endofunctor `K` of `C`
that is fully faithful and that `F` intertwines, through isomorphisms `F (K Y) ≅ K' (F Y)`
natural in `Y`, with a faithful endofunctor `K'` of `D`. -/
theorem isIso_unit_app_of_intertwining (adj : F ⊣ G) (K : C ⥤ C) (K' : D ⥤ D)
    [K.Full] [K.Faithful] [K'.Faithful]
    (α : ∀ Y : C, F.obj (K.obj Y) ≅ K'.obj (F.obj Y))
    (hα : ∀ {Y Y' : C} (f : Y ⟶ Y'),
      F.map (K.map f) ≫ (α Y').hom = (α Y).hom ≫ K'.map (F.map f))
    (X : C) (hX : IsIso (adj.unit.app (K.obj X))) : IsIso (adj.unit.app X) := by
  rw [isIso_unit_app_iff_bijective_map] at hX ⊢
  exact fun P => F.bijective_map_of_intertwining K K' α hα P X (hX (K.obj P))

/-- **The unit is an isomorphism at `X` when `K X` is isomorphic to an object at which it is
one**, for `K` fully faithful and intertwined by `F` with a faithful `K'`. -/
theorem isIso_unit_app_of_intertwining_of_iso (adj : F ⊣ G) (K : C ⥤ C) (K' : D ⥤ D)
    [K.Full] [K.Faithful] [K'.Faithful]
    (α : ∀ Y : C, F.obj (K.obj Y) ≅ K'.obj (F.obj Y))
    (hα : ∀ {Y Y' : C} (f : Y ⟶ Y'),
      F.map (K.map f) ≫ (α Y').hom = (α Y).hom ≫ K'.map (F.map f))
    {X U : C} (e : K.obj X ≅ U) (hU : IsIso (adj.unit.app U)) : IsIso (adj.unit.app X) := by
  refine isIso_unit_app_of_intertwining adj K K' α hα X ?_
  have h : adj.unit.app (K.obj X) =
      e.hom ≫ adj.unit.app U ≫ G.map (F.map e.inv) := by
    rw [← adj.unit_naturality_assoc, ← G.map_comp, ← F.map_comp, e.hom_inv_id, F.map_id,
      G.map_id, Category.comp_id]
  rw [h]
  infer_instance

end CategoryTheory.Adjunction
