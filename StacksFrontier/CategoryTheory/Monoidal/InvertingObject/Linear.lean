module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Existence

/-!
# The additive, `ℚ`-linear extension

We prove (L) of `StacksFrontier.CategoryTheory.Monoidal.InvertingObject`. When `𝒜`, `ℳ`, `𝒞` are
preadditive, the tensor products of `ℳ` and `𝒞` are additive and `K`, `F` are additive, pairs
presented together are closed under sums, negatives and zero, so the category `Pairs` is
preadditive with additive projections; the extension `Pairs.ext`, the inverse of the first
projection followed by the second, is then additive, and `ℚ`-linear when `ℳ` and `𝒞` are.

## Main results

* `CategoryTheory.InvertingObject.linearExistence`: (L).
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.InvertingObject

open MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open Expr

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [SymmetricCategory 𝒜]
  {ℳ : Type u₂} [Category.{v₂} ℳ] [MonoidalCategory ℳ] [SymmetricCategory ℳ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  {K : 𝒜 ⥤ ℳ} [K.Braided] {F : 𝒜 ⥤ 𝒞} [F.Braided] {L : 𝒜} {T : ℳ}
  {ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ} {hL : HasInverse (F.obj L)}
  [Preadditive 𝒜] [Preadditive ℳ] [MonoidalPreadditive ℳ] [Preadditive 𝒞]
  [MonoidalPreadditive 𝒞] [K.Additive] [F.Additive]

namespace Pairs

/-- Sums of morphisms whiskered on the right satisfy the sum of the relations. -/
private theorem add_whiskerRight_comp_eq {D : Type*} [Category D] [MonoidalCategory D]
    [Preadditive D] [MonoidalPreadditive D] {A B P Z W : D} {u v : A ⟶ B} {m : B ⊗ P ⟶ Z}
    {n : A ⊗ P ⟶ W} {p q r : W ⟶ Z} (hr : r = p + q) (a : u ▷ P ≫ m = n ≫ p)
    (b : v ▷ P ≫ m = n ≫ q) :
    (u + v) ▷ P ≫ m = n ≫ r := by
  rw [hr, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, a, b, Preadditive.comp_add]

/-- Negatives of morphisms whiskered on the right satisfy the negative of the relation. -/
private theorem neg_whiskerRight_comp_eq {D : Type*} [Category D] [MonoidalCategory D]
    [Preadditive D] [MonoidalPreadditive D] {A B P Z W : D} {u : A ⟶ B} {m : B ⊗ P ⟶ Z}
    {n : A ⊗ P ⟶ W} {p r : W ⟶ Z} (hr : r = -p) (a : u ▷ P ≫ m = n ≫ p) :
    (-u) ▷ P ≫ m = n ≫ r := by
  rw [hr, show (-u) ▷ P = -(u ▷ P) from (tensorRight P).map_neg, Preadditive.neg_comp, a,
    Preadditive.comp_neg]

/-- Presentations by the same data add up. -/
theorem relX_add {e e' : Expr 𝒜}
    {u v : (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e ⟶
      (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e'}
    {X Y : 𝒜} {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y}
    {c c' : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y}
    (h : RelX L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) u X Y φ c)
    (h' : RelX L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) v X Y φ c') :
    RelX L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) ((u.1 + v.1, u.2 + v.2) : _)
      X Y φ (c + c') := by
  refine Prod.hom_ext ?_ ?_
  · exact add_whiskerRight_comp_eq (K.map_add ..) (relX_fst h) (relX_fst h')
  · exact add_whiskerRight_comp_eq (F.map_add ..) (relX_snd h) (relX_snd h')

variable [K.Full] [K.Faithful]

/-- The componentwise sum of two morphisms of `Pairs K F ℓ hL` satisfies `Good`. -/
theorem good_add {X Y : Pairs K F ℓ hL} (f g : X ⟶ Y) :
    Good (L := L) (ω := pairing K F ℓ hL) ((f.1.1 + g.1.1, f.1.2 + g.1.2) : _) := by
  obtain ⟨X₁, Y₁, φ₁, c₁, hX₁, hY₁, h₁⟩ := f.2
  obtain ⟨X₂, Y₂, φ₂, c₂, hX₂, hY₂, h₂⟩ := g.2
  have k₁ := h₁.padRight X₂
  have k₂ := (h₂.padRight X₁).changeLeft (β_ X₁ X₂)
  obtain ⟨χ, hχ⟩ := ((leftCancel_pad Y) (A := Y₂ ⊗ X₁) (B := Y₁ ⊗ X₂)).2
    ((whiskerLeftIso _ (β_ X₁ X₂) ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso φ₂ X₁ ≪≫ α_ _ _ _).inv ≫
      ((α_ _ _ _).symm ≪≫ whiskerRightIso φ₁ X₂ ≪≫ α_ _ _ _).hom)
  have k₂' := k₂.changeRightHom χ _ (by
    change (pad L).obj Y.expr ◁ χ = _ at hχ
    rw [hχ, Iso.hom_inv_id_assoc])
  exact ⟨_, _, _, _, IsInvertible.map_tensor _ hX₁ hX₂, IsInvertible.map_tensor _ hY₁ hX₂,
    relX_add k₁ k₂'⟩

omit [K.Full] [K.Faithful] in
/-- The zero pair of morphisms between two objects of `Pairs K F ℓ hL` satisfies `Good`. -/
theorem good_zero (X Y : Pairs K F ℓ hL) :
    Good (L := L) (ω := pairing K F ℓ hL) (((0 : ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj
      X.expr).1 ⟶ ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj Y.expr).1), (0 : _ ⟶ _)) : _) := by
  refine ⟨(pad L).obj Y.expr, (pad L).obj X.expr, β_ _ _, 0, Y.isInvertible, X.isInvertible,
    Prod.hom_ext ?_ ?_⟩
  · show (0 : ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj X.expr).1 ⟶ _) ▷ _ ≫ _ ≫ _ =
      _ ≫ K.map 0
    rw [MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, K.map_zero, Limits.comp_zero]
  · show (0 : ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj X.expr).2 ⟶ _) ▷ _ ≫ _ ≫ _ =
      _ ≫ F.map 0
    rw [MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, F.map_zero, Limits.comp_zero]

omit [K.Full] [K.Faithful] in
/-- The componentwise negative of a morphism of `Pairs K F ℓ hL` satisfies `Good`. -/
theorem good_neg {X Y : Pairs K F ℓ hL} (f : X ⟶ Y) :
    Good (L := L) (ω := pairing K F ℓ hL) ((-f.1.1, -f.1.2) : _) := by
  obtain ⟨X₁, Y₁, φ₁, c₁, hX₁, hY₁, h₁⟩ := f.2
  refine ⟨X₁, Y₁, φ₁, -c₁, hX₁, hY₁, Prod.hom_ext ?_ ?_⟩
  · exact neg_whiskerRight_comp_eq (K.map_neg ..) (relX_fst h₁)
  · exact neg_whiskerRight_comp_eq (F.map_neg ..) (relX_snd h₁)

/-- The pairs presented together form a subgroup of the pairs of morphisms. -/
def goodSubgroup (X Y : Pairs K F ℓ hL) :
    AddSubgroup ((((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj X.expr).1 ⟶
      ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj Y.expr).1) ×
      (((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj X.expr).2 ⟶
        ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj Y.expr).2)) where
  carrier := {u | Good (L := L) (ω := pairing K F ℓ hL) (e := X.expr) (e' := Y.expr) u}
  add_mem' {a b} ha hb := good_add (X := X) (Y := Y) ⟨a, ha⟩ ⟨b, hb⟩
  zero_mem' := good_zero X Y
  neg_mem' {a} ha := good_neg (X := X) (Y := Y) ⟨a, ha⟩

/-- `Pairs K F ℓ hL` is preadditive, with hom groups `goodSubgroup`. -/
instance : Preadditive (Pairs K F ℓ hL) where
  homGroup X Y := inferInstanceAs (AddCommGroup (goodSubgroup X Y))
  add_comp _ _ _ f f' g :=
    Graph.hom_ext (Prod.hom_ext (Preadditive.add_comp _ _ _ f.1.1 f'.1.1 g.1.1)
      (Preadditive.add_comp _ _ _ f.1.2 f'.1.2 g.1.2))
  comp_add _ _ _ f g g' :=
    Graph.hom_ext (Prod.hom_ext (Preadditive.comp_add _ _ _ f.1.1 g.1.1 g'.1.1)
      (Preadditive.comp_add _ _ _ f.1.2 g.1.2 g'.1.2))

/-- The first projection `pr₁ K F ℓ hL` is additive. -/
instance : (pr₁ K F ℓ hL).Additive where
  map_add := rfl

/-- The second projection `pr₂ K F ℓ hL` is additive. -/
instance : (pr₂ K F ℓ hL).Additive where
  map_add := rfl

variable (hess : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n))

/-- The functor of the equivalence `pr₁Equiv K F ℓ hL hess` is additive. -/
instance : (pr₁Equiv K F ℓ hL hess).functor.Additive := inferInstanceAs (pr₁ K F ℓ hL).Additive

attribute [local instance] Equivalence.inverseMonoidal Equivalence.inverseBraided

/-- The extension `ext K F ℓ hL hess` is additive. -/
instance : (ext K F ℓ hL hess).Additive := inferInstanceAs
  ((pr₁Equiv K F ℓ hL hess).inverse ⋙ pr₂ K F ℓ hL).Additive

end Pairs

section

attribute [local instance] Equivalence.inverseMonoidal Equivalence.inverseBraided

variable (𝒞 : Type u₃) [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  (K : 𝒜 ⥤ ℳ) [K.Braided] [K.Full] [K.Faithful] (L : 𝒜) (T : ℳ)
  [Preadditive 𝒜] [Preadditive ℳ] [Linear ℚ ℳ] [MonoidalPreadditive ℳ]
  [Preadditive 𝒞] [Linear ℚ 𝒞] [MonoidalPreadditive 𝒞] [K.Additive]

/-- **(L)**, see `CategoryTheory.InvertingObject.LinearExistence`. -/
theorem linearExistence : LinearExistence 𝒞 K L T := by
  intro ℓ _ hess F _ _ hF
  obtain ⟨hL⟩ := hF
  exact ⟨Pairs.ext K F ℓ hL hess, inferInstance, inferInstance, inferInstance,
    Pairs.extIso K F ℓ hL hess, inferInstance⟩

end

end CategoryTheory.InvertingObject
