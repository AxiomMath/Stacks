module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTruncation
import all StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTruncation
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit

/-!
# Dévissage of an inverse system along its one-degree truncations

Let `t` be a `t`-structure on a triangulated category `𝒟` and let `P` be a property of inverse
sequences of `𝒟` that is invariant under isomorphism and satisfies two out of three on inverse
systems of distinguished triangles. An inverse system `(K_n)` whose terms live in the degree range
`[a, b]` has `P` as soon as each of its one-degree truncations `τ^{≥p}τ^{≤p}K_n`, `a ≤ p ≤ b`,
has `P`.

## Main results

* `CategoryTheory.Triangulated.TStructure.prop_of_truncGELE`: the dévissage.

## References

* [Stacks Project, Tag 0G4S](https://stacks.math.columbia.edu/tag/0G4S)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated Opposite

universe v u u'

namespace CategoryTheory

section Transport

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

end Transport

section Truncation

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] [IsTriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

namespace Triangulated.TStructure

/-- Let `P` be a property of inverse sequences that is invariant under isomorphism and satisfies
two out of three on inverse systems of distinguished triangles. If the terms of `(K_n)` lie in
`[a, a + k]` and every one-degree truncation in that range has `P`, then `(K_n)` has `P`. -/
public lemma prop_of_truncGELE_aux (t : TStructure 𝒟) (P : (ℕᵒᵖ ⥤ 𝒟) → Prop)
    (hiso : ∀ {F G : ℕᵒᵖ ⥤ 𝒟}, (F ≅ G) → P G → P F)
    (htri : ∀ T : ℕᵒᵖ ⥤ Triangle 𝒟, (∀ n, T.obj n ∈ distTriang 𝒟) →
      P (T ⋙ Triangle.π₁) → P (T ⋙ Triangle.π₃) → P (T ⋙ Triangle.π₂)) :
    ∀ (k : ℕ) (a b : ℤ), b = a + k → ∀ K : ℕᵒᵖ ⥤ 𝒟, (∀ n, t.IsGE (K.obj n) a) →
      (∀ n, t.IsLE (K.obj n) b) → (∀ p : ℤ, a ≤ p → p ≤ b → P (K ⋙ t.truncGELE p p)) → P K := by
  intro k
  induction k with
  | zero =>
    intro a b hb K hGE hLE H
    obtain rfl : b = a := by simpa using hb
    exact hiso (t.truncGELESelfIso K b hGE hLE) (H b le_rfl le_rfl)
  | succ k ih =>
    intro a b hb K hGE hLE H
    have hab : a + 1 ≤ b := by omega
    have h₁ : P (K ⋙ t.truncLE a) := by
      refine hiso (t.truncGELESelfIso (K ⋙ t.truncLE a) a (fun n => ?_) (fun n => ?_)) ?_
      · have := hGE n
        exact inferInstanceAs (t.IsGE ((t.truncLE a).obj (K.obj n)) a)
      · exact inferInstanceAs (t.IsLE ((t.truncLE a).obj (K.obj n)) a)
      · exact hiso (Functor.isoWhiskerLeft K (t.truncLECompTruncGELEIso a))
          (H a le_rfl (by omega))
    have h₃ : P (K ⋙ t.truncGE (a + 1)) := by
      refine ih (a + 1) b (by omega) (K ⋙ t.truncGE (a + 1))
        (fun n => ?_) (fun n => ?_) (fun p hp hp' => ?_)
      · exact inferInstanceAs (t.IsGE ((t.truncGE (a + 1)).obj (K.obj n)) (a + 1))
      · have := hLE n
        exact inferInstanceAs (t.IsLE ((t.truncGE (a + 1)).obj (K.obj n)) b)
      · exact hiso (Functor.isoWhiskerLeft K (t.truncGECompTruncGELEIso hp))
          (H p (by omega) hp')
    exact htri (K ⋙ t.triangleLEGE a (a + 1) rfl)
      (fun n => t.triangleLEGE_distinguished a (a + 1) rfl (K.obj n)) h₁ h₃

/-- **Dévissage of an inverse system along its one-degree truncations.** Let `P` be a property of
inverse sequences of `𝒟` that is invariant under isomorphism and satisfies two out of three on
inverse systems of distinguished triangles (the outer two having `P` forces the middle one to).
If the terms of `(K_n)` lie in the degree range `[a, b]` and each one-degree truncation system
`(τ^{≥p}τ^{≤p}K_n)`, `a ≤ p ≤ b`, has `P`, then `(K_n)` has `P`. -/
public lemma prop_of_truncGELE (t : TStructure 𝒟) (P : (ℕᵒᵖ ⥤ 𝒟) → Prop)
    (hiso : ∀ {F G : ℕᵒᵖ ⥤ 𝒟}, (F ≅ G) → P G → P F)
    (htri : ∀ T : ℕᵒᵖ ⥤ Triangle 𝒟, (∀ n, T.obj n ∈ distTriang 𝒟) →
      P (T ⋙ Triangle.π₁) → P (T ⋙ Triangle.π₃) → P (T ⋙ Triangle.π₂))
    {a b : ℤ} (hab : a ≤ b) (K : ℕᵒᵖ ⥤ 𝒟)
    (hGE : ∀ n, t.IsGE (K.obj n) a) (hLE : ∀ n, t.IsLE (K.obj n) b)
    (H : ∀ p : ℤ, a ≤ p → p ≤ b → P (K ⋙ t.truncGELE p p)) : P K :=
  t.prop_of_truncGELE_aux P hiso htri (b - a).toNat a b (by omega) K hGE hLE H

end Triangulated.TStructure

end Truncation

end CategoryTheory

end
