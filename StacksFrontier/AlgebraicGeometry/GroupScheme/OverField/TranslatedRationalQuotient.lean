/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiCompact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Translating a quotient map defined on an open of a group

Let `Γ` be a group object over a scheme `S`, `V` an open of `Γ` and `π : V ⟶ X` a morphism over `S`
such that `x⁻¹ y` satisfies a property `P` whenever `x, y` are points of `Γ` through `V` with
`π x = π y`. For a global point `g` of `Γ`, put `W := λ_g⁻¹ V` and `π_W := π ∘ λ_g`. Then `π_W` has
the same fibre property, since `(g x)⁻¹ (g y) = x⁻¹ y`, it is flat when `π` is, and the unit lies
in `W` when `g` lies in `V`. Restricting to a smaller open keeps the fibre property.

## Main results

* `AlgebraicGeometry.translatedQuotient`: the translated map `π_W`.
* `AlgebraicGeometry.translatedQuotient_fibre`: it has the same fibre property.
* `AlgebraicGeometry.unit_mem_translatedOpen`: the unit lies in `W` when `g` lies in `V`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (Γ : Over S) [GrpObj Γ] (g : 𝟙_ (Over S) ⟶ Γ)

/-- Composing a point with the left translation by `g` multiplies it by `g` on the left. -/
lemma comp_leftTranslation {T : Over S} (x : T ⟶ Γ) :
    letI := Hom.group (X := T) (G := Γ)
    x ≫ leftTranslation Γ g = (toUnit T ≫ g) * x := by
  let := Hom.group (X := T) (G := Γ)
  rw [leftTranslation, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit Γ) (toUnit T),
    Category.comp_id]

/-- The unit is sent to `g` by the left translation by `g`. -/
lemma unit_leftTranslation : η[Γ] ≫ leftTranslation Γ g = g := by
  rw [comp_leftTranslation, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  exact mul_one (M := 𝟙_ (Over S) ⟶ Γ) g

/-- The left translation by `g` is an isomorphism. -/
@[ega "IV 17.12.7" "partial"]
instance isIso_leftTranslation_left : IsIso (leftTranslation Γ g).left := by
  have : IsIso (leftTranslation Γ g) :=
    ⟨leftTranslation Γ g⁻¹, by rw [leftTranslation_comp, inv_mul_cancel]; simp [leftTranslation],
      by rw [leftTranslation_comp, mul_inv_cancel]; simp [leftTranslation]⟩
  change IsIso ((Over.forget S).map (leftTranslation Γ g))
  infer_instance

/-- The open `λ_g⁻¹ V`. -/
noncomputable abbrev translatedOpen (V : Γ.left.Opens) : Γ.left.Opens :=
  (leftTranslation Γ g).left ⁻¹ᵁ V

/-- The translated map `π ∘ λ_g : λ_g⁻¹ V ⟶ X`. -/
noncomputable def translatedQuotient (V : Γ.left.Opens) {X : Scheme.{u}} (π : V.toScheme ⟶ X) :
    (translatedOpen Γ g V).toScheme ⟶ X :=
  (leftTranslation Γ g).left ∣_ V ≫ π

/-- If `π` commutes with the structure morphisms to `S`, so does `translatedQuotient Γ g V π`. -/
lemma translatedQuotient_over (V : Γ.left.Opens) (X : Over S) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ Γ.hom) :
    translatedQuotient Γ g V π ≫ X.hom = (translatedOpen Γ g V).ι ≫ Γ.hom := by
  rw [translatedQuotient, Category.assoc, hπ, morphismRestrict_ι_assoc, Over.w]

/-- The translated map `translatedQuotient Γ g V π` is flat when `π` is flat. -/
instance translatedQuotient_flat (V : Γ.left.Opens) {X : Scheme.{u}} (π : V.toScheme ⟶ X)
    [Flat π] : Flat (translatedQuotient Γ g V π) := by
  rw [translatedQuotient]
  infer_instance

/-- The unit lies in `λ_g⁻¹ V` when `g` lies in `V`. -/
lemma unit_mem_translatedOpen (V : Γ.left.Opens) (p : (𝟙_ (Over S)).left)
    (hg : g.left p ∈ V) : (η[Γ]).left p ∈ translatedOpen Γ g V := by
  show ((η[Γ]).left ≫ (leftTranslation Γ g).left) p ∈ V
  rw [← Over.comp_left, unit_leftTranslation]
  exact hg

/-- **The fibre property survives translation.**  If any two points `x, y` of `Γ` through `V`
with `π x = π y` have `x⁻¹ y` satisfying `P`, then the same holds for `λ_g⁻¹ V` and the translated
map. -/
lemma translatedQuotient_fibre (V : Γ.left.Opens) (X : Scheme.{u}) (π : V.toScheme ⟶ X)
    (P : ∀ T : Over S, (T ⟶ Γ) → Prop)
    (hP : ∀ (T : Over S) (x y : T ⟶ Γ) (x' y' : T.left ⟶ V.toScheme),
      x' ≫ V.ι = x.left → y' ≫ V.ι = y.left → x' ≫ π = y' ≫ π →
      letI := Hom.group (X := T) (G := Γ)
      P T (x⁻¹ * y))
    (T : Over S) (x y : T ⟶ Γ) (x' y' : T.left ⟶ (translatedOpen Γ g V).toScheme)
    (hx : x' ≫ (translatedOpen Γ g V).ι = x.left) (hy : y' ≫ (translatedOpen Γ g V).ι = y.left)
    (hxy : x' ≫ translatedQuotient Γ g V π = y' ≫ translatedQuotient Γ g V π) :
    letI := Hom.group (X := T) (G := Γ)
    P T (x⁻¹ * y) := by
  let := Hom.group (X := T) (G := Γ)
  have key := hP T (x ≫ leftTranslation Γ g) (y ≫ leftTranslation Γ g)
    (x' ≫ (leftTranslation Γ g).left ∣_ V) (y' ≫ (leftTranslation Γ g).left ∣_ V)
    (by rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hx, Over.comp_left])
    (by rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hy, Over.comp_left])
    (by simpa only [translatedQuotient, Category.assoc] using hxy)
  rw [comp_leftTranslation, comp_leftTranslation, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left] at key
  exact key

/-- The fibre property passes to a smaller open. -/
lemma fibre_of_le {V V' : Γ.left.Opens} (hV : V' ≤ V) (X : Scheme.{u}) (π : V.toScheme ⟶ X)
    (P : ∀ T : Over S, (T ⟶ Γ) → Prop)
    (hP : ∀ (T : Over S) (x y : T ⟶ Γ) (x' y' : T.left ⟶ V.toScheme),
      x' ≫ V.ι = x.left → y' ≫ V.ι = y.left → x' ≫ π = y' ≫ π →
      letI := Hom.group (X := T) (G := Γ)
      P T (x⁻¹ * y))
    (T : Over S) (x y : T ⟶ Γ) (x' y' : T.left ⟶ V'.toScheme)
    (hx : x' ≫ V'.ι = x.left) (hy : y' ≫ V'.ι = y.left)
    (hxy : x' ≫ Γ.left.homOfLE hV ≫ π = y' ≫ Γ.left.homOfLE hV ≫ π) :
    letI := Hom.group (X := T) (G := Γ)
    P T (x⁻¹ * y) :=
  hP T x y (x' ≫ Γ.left.homOfLE hV) (y' ≫ Γ.left.homOfLE hV)
    (by rw [Category.assoc, Scheme.homOfLE_ι, hx]) (by rw [Category.assoc, Scheme.homOfLE_ι, hy])
    (by simpa only [Category.assoc] using hxy)

end AlgebraicGeometry

end
