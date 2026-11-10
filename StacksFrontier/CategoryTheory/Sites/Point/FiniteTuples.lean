module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Finite tuples of germs at a point of a site

Let `Φ` be a point of a site `(C, J)` and let `P` be a presheaf on `C` with values in a concrete
category whose forgetful functor preserves filtered colimits.  The fibre `P_Φ` is the colimit of
the values of `P` over the cofiltered category of neighbourhoods of `Φ`, so each of its elements
is a germ and two germs at the same neighbourhood agree exactly when they agree on a smaller one;
that is `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjective` and
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_eq_iff'`.

This file upgrades both statements from one element to a **finite tuple** of elements, at a single
common neighbourhood.  That is exactly the content of filtered colimits commuting with finite
limits, in the form a hand computation needs it: a finite system of elements of the fibre comes
from one neighbourhood, and a finite system of equalities between germs already holds after one
single restriction.  Both are proved by induction on the length of the tuple, the inductive step
using only the binary cofiltered operations
`CategoryTheory.IsCofiltered.min` and the one-element statements above.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.exists_toPresheafFiber_tuple` — a finite tuple of
  elements of the fibre is a tuple of germs at a single neighbourhood.
* `CategoryTheory.GrothendieckTopology.Point.exists_map_eq_of_toPresheafFiber_eq` — a finite tuple
  of equalities of germs at one neighbourhood holds after a single restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v' u' v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w'} A FC]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]
  (P : Cᵒᵖ ⥤ A)

/-- **A finite tuple of elements of the fibre of a presheaf comes from a single
neighbourhood.**  Each element separately is a germ, by
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjective`; the neighbourhoods
are then brought together one at a time, which is possible because the category of neighbourhoods
of a point of a site is cofiltered. -/
theorem exists_toPresheafFiber_tuple (n : ℕ) :
    ∀ a : Fin n → ToType (Φ.presheafFiber.obj P),
      ∃ (Z : C) (z : Φ.fiber.obj Z) (b : Fin n → ToType (P.obj (op Z))),
        ∀ i, Φ.toPresheafFiber Z z P (b i) = a i := by
  induction n with
  | zero =>
      intro _
      obtain ⟨e⟩ := IsCofiltered.nonempty (C := Φ.fiber.Elements)
      exact ⟨e.obj, e.val, Fin.elim0, fun i => i.elim0⟩
  | succ n ih =>
      intro a
      obtain ⟨Z₀, z₀, u, hu⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) (a 0)
      obtain ⟨Z₁, z₁, b, hb⟩ := ih (fun i : Fin n => a i.succ)
      let E₀ : Φ.fiber.Elements := Φ.fiber.elementsMk Z₀ z₀
      let E₁ : Φ.fiber.Elements := Φ.fiber.elementsMk Z₁ z₁
      let Z : Φ.fiber.Elements := IsCofiltered.min E₀ E₁
      let l : Z ⟶ E₀ := IsCofiltered.minToLeft E₀ E₁
      let r : Z ⟶ E₁ := IsCofiltered.minToRight E₀ E₁
      refine ⟨Z.obj, Z.val, Fin.cons (P.map l.hom.op u) (fun i => P.map r.hom.op (b i)),
        fun i => ?_⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [l.map_val] using hu
      · simpa [r.map_val] using hb i

/-- **A finite tuple of equalities of germs at one neighbourhood holds after a single
restriction.**  Each equality separately holds after some restriction, by
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_eq_iff'`; the restrictions are then
composed one at a time, so that a single morphism of neighbourhoods serves for all of them. -/
theorem exists_map_eq_of_toPresheafFiber_eq (n : ℕ) :
    ∀ (Z : C) (z : Φ.fiber.obj Z) (b₁ b₂ : Fin n → ToType (P.obj (op Z))),
      (∀ i, Φ.toPresheafFiber Z z P (b₁ i) = Φ.toPresheafFiber Z z P (b₂ i)) →
      ∃ (Z' : C) (k : Z' ⟶ Z) (z' : Φ.fiber.obj Z'), Φ.fiber.map k z' = z ∧
        ∀ i, P.map k.op (b₁ i) = P.map k.op (b₂ i) := by
  induction n with
  | zero =>
      intro Z z _ _ _
      exact ⟨Z, CategoryStruct.id Z, z, by simp, fun i => i.elim0⟩
  | succ n ih =>
      intro Z z b₁ b₂ h
      obtain ⟨Y, f, y, hy, hf⟩ := (Φ.toPresheafFiber_eq_iff' Z z (b₁ 0) (b₂ 0)).1 (h 0)
      obtain ⟨Y', k', y', hy', h'⟩ := ih Y y
        (fun i : Fin n => P.map f.op (b₁ i.succ)) (fun i : Fin n => P.map f.op (b₂ i.succ))
        fun i => by simpa [hy] using h i.succ
      refine ⟨Y', k' ≫ f, y', ?_, fun i => ?_⟩
      · rw [Φ.fiber.map_comp, ConcreteCategory.comp_apply, hy', hy]
      · simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [congrArg (P.map k'.op) hf]
        · exact h' i

end CategoryTheory.GrothendieckTopology.Point

end
