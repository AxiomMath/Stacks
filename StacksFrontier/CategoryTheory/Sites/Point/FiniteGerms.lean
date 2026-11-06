module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# Finitely many germs at a point of a site

Let `Φ` be a point of a site.  Its neighbourhoods `(X, x)`, with `x ∈ Φ(X)`, form a cofiltered
category, and the fibre of a presheaf at `Φ` is the filtered colimit of its sections over them.
This file records the two finiteness statements that every elementwise argument with stalks at a
point uses: finitely many elements of a fibre are germs of sections over one common
neighbourhood below any given one, and finitely many sections with vanishing germs all vanish on
one common smaller neighbourhood.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.exists_le_le`: two neighbourhoods have a common
  refinement.
* `CategoryTheory.GrothendieckTopology.Point.exists_toPresheafFiber_eq_fin`: finitely many germs
  are represented over one neighbourhood, refining a given one.
* `CategoryTheory.GrothendieckTopology.Point.exists_map_eq_zero_fin`: finitely many sections with
  vanishing germs vanish on one smaller neighbourhood.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)

/-- Two neighbourhoods of a point have a common refinement. -/
theorem exists_le_le {X₁ X₂ : C} (x₁ : Φ.fiber.obj X₁) (x₂ : Φ.fiber.obj X₂) :
    ∃ (Y : C) (y : Φ.fiber.obj Y) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂),
      Φ.fiber.map f₁ y = x₁ ∧ Φ.fiber.map f₂ y = x₂ := by
  let e₁ : Φ.fiber.Elements := Φ.fiber.elementsMk X₁ x₁
  let e₂ : Φ.fiber.Elements := Φ.fiber.elementsMk X₂ x₂
  exact ⟨(IsCofiltered.min e₁ e₂).obj, (IsCofiltered.min e₁ e₂).val,
    (IsCofiltered.minToLeft e₁ e₂).hom, (IsCofiltered.minToRight e₁ e₂).hom,
    (IsCofiltered.minToLeft e₁ e₂).map_val, (IsCofiltered.minToRight e₁ e₂).map_val⟩

variable [LocallySmall.{w} C] {P : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **Finitely many germs over one neighbourhood.**  Finitely many elements of the fibre of a
presheaf of commutative rings at a point are germs of sections over a single neighbourhood,
which may be chosen below any given neighbourhood. -/
theorem exists_toPresheafFiber_eq_fin {X : C} (x : Φ.fiber.obj X) :
    ∀ (n : ℕ) (t : Fin n → ToType (Φ.presheafFiber.obj P)),
      ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        ∃ s : Fin n → ToType (P.obj (op Y)), ∀ k, Φ.toPresheafFiber Y y P (s k) = t k
  | 0, _ => ⟨X, 𝟙 X, x, by simp, Fin.elim0, fun k => k.elim0⟩
  | n + 1, t => by
    obtain ⟨Y, f, y, hy, s, hs⟩ := exists_toPresheafFiber_eq_fin x n (fun k => t k.castSucc)
    obtain ⟨Z, z, r, hr⟩ := Φ.toPresheafFiber_jointly_surjective (t (Fin.last n))
    obtain ⟨W, w, g₁, g₂, hg₁, hg₂⟩ := Φ.exists_le_le y z
    refine ⟨W, g₁ ≫ f, w, ?_, Fin.lastCases (P.map g₂.op r)
      (fun k => P.map g₁.op (s k)), fun k => ?_⟩
    · rw [Functor.map_comp_apply, hg₁, hy]
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · simp only [Fin.lastCases_last]
        rw [Point.toPresheafFiber_w_apply, hg₂, hr]
      · simp only [Fin.lastCases_castSucc]
        rw [Point.toPresheafFiber_w_apply, hg₁, hs k]

/-- **Finitely many vanishings on one neighbourhood.**  Finitely many sections of a presheaf of
commutative rings over a neighbourhood of a point whose germs vanish all vanish after
restriction to one smaller neighbourhood. -/
theorem exists_map_eq_zero_fin {X : C} (x : Φ.fiber.obj X) :
    ∀ (n : ℕ) (s : Fin n → ToType (P.obj (op X))), (∀ k, Φ.toPresheafFiber X x P (s k) = 0) →
      ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        ∀ k, P.map f.op (s k) = 0
  | 0, _, _ => ⟨X, 𝟙 X, x, by simp, fun k => k.elim0⟩
  | n + 1, s, hs => by
    obtain ⟨Y, f, y, hy, h⟩ := exists_map_eq_zero_fin x n (fun k => s k.castSucc)
      (fun k => hs k.castSucc)
    have h0 : Φ.toPresheafFiber Y y P (P.map f.op (s (Fin.last n))) =
        Φ.toPresheafFiber Y y P 0 := by
      rw [Point.toPresheafFiber_w_apply, hy, hs, map_zero]
    obtain ⟨Z, g, z, hz, hzero⟩ := (Φ.toPresheafFiber_eq_iff' Y y _ _).mp h0
    refine ⟨Z, g ≫ f, z, ?_, fun k => ?_⟩
    · rw [Functor.map_comp_apply, hz, hy]
    · rw [op_comp, P.map_comp_apply]
      refine Fin.lastCases ?_ (fun k => ?_) k
      · rw [hzero, map_zero]
      · rw [h k, map_zero]

end CategoryTheory.GrothendieckTopology.Point

end
