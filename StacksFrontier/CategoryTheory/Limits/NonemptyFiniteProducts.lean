module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductBinaryProducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Products indexed by a nonempty finite type from binary products

A category with binary products has products indexed by any nonempty finite type: the induction
building a product of `n + 1` objects out of binary ones never reaches the empty product, so no
terminal object is needed. In particular the category `SR(C)` of semi-representable objects of a
category `C` with binary products has such products.

## Main results

* `CategoryTheory.Limits.hasProductsOfShape_of_finite_of_elem`: a category with binary products
  has products of every nonempty finite shape.
* `CategoryTheory.Limits.FormalCoproduct.instHasProductsOfShape`: the instance for formal
  coproducts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [HasBinaryProducts C]

/-- With binary products available, a family of `n + 1` objects has a product: the product of the
last `n` of them times the first. -/
private theorem hasProduct_fin_succ : ∀ (n : ℕ) (f : Fin (n + 1) → C), HasProduct f
  | 0 => fun f ↦
    have : Unique (Fin (0 + 1)) := Fin.instUnique
    hasProduct_unique f
  | n + 1 => fun f ↦
    have := hasProduct_fin_succ n fun i : Fin (n + 1) ↦ f i.succ
    HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

/-- **A category with binary products has products indexed by any finite type with an
element.** -/
theorem hasProductsOfShape_of_finite_of_elem (ι : Type w) [Finite ι] (i₀ : ι) :
    HasProductsOfShape ι C := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun hn ↦ (hn ▸ e i₀).elim0
  have : HasLimitsOfShape (Discrete (Fin (m + 1))) C := ⟨fun K ↦ by
    have h : (Discrete.functor fun i ↦ K.obj ⟨i⟩) ≅ K := Discrete.natIso fun ⟨_⟩ ↦ Iso.refl _
    rw [← hasLimit_iff_of_iso h]
    exact hasProduct_fin_succ C m _⟩
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

/-- The category `SR(C)` of semi-representable objects of a category with binary products has
products indexed by any inhabited finite type. -/
@[sga "4 V 7.3.0" "partial"]
instance FormalCoproduct.instHasProductsOfShape (ι : Type w') [Finite ι] [Inhabited ι] :
    HasProductsOfShape ι (FormalCoproduct.{w} C) :=
  hasProductsOfShape_of_finite_of_elem _ ι default

end CategoryTheory.Limits
