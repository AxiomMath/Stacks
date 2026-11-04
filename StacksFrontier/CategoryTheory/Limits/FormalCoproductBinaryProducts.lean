module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Binary products of formal coproducts

Let `C` be a category. The Stacks Project's category `SR(C)` of *semi-representable objects* of
`C` is Mathlib's `CategoryTheory.Limits.FormalCoproduct C`, whose objects are indexed families of
objects of `C`. Mathlib already constructs its terminal object, its arbitrary coproducts and its
pullbacks; this file constructs its binary products.

A morphism of formal coproducts is a map of index types together with a component morphism over
every index, so a morphism to a pair `X`, `Y` picks out, for each of its own indices, one index of
`X` and one of `Y`. The product is therefore indexed by `X.I × Y.I`, with component over `(i, j)`
the product `X.obj i ⨯ Y.obj j` in `C`.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.instHasBinaryProducts`: **Stacks Project, Tag 01G2**,
  products of pairs clause — if `C` has binary products then so does `FormalCoproduct.{w} C`,
  that is, the category `SR(C)` of semi-representable objects of `C` has binary products.

## Implementation notes

The product fan is built inside the proof rather than exposed as a separate definition. Exposing
it is of no use to a client here: `FormalCoproduct.hom_ext`, which is how one proves two morphisms
of formal coproducts equal, produces goals mentioning the index type of the fan's point, and these
are type-correct only once the semireducible definition naming it has been unfolded, so tactics
working at `implicit` transparency reject them.

The index universe `w` of the formal coproducts stays independent of the universes `u`, `v` of
`C`: the index type of the product is `X.I × Y.I : Type w`, so nothing here relates them.

## References

* [Stacks Project, Tag 01G2](https://stacks.math.columbia.edu/tag/01G2)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.FormalCoproduct

variable (C : Type u) [Category.{v} C] [HasBinaryProducts C]

/-- **Stacks Project, Tag 01G2**, products of pairs clause. If `C` has binary products, then so
does its category of formal coproducts — equivalently, the category `SR(C)` of semi-representable
objects of `C` has binary products. -/
@[stacks 01G2 "products of pairs in SR(C)"]
instance instHasBinaryProducts : HasBinaryProducts (FormalCoproduct.{w} C) := by
  let : ∀ {X Y : FormalCoproduct.{w} C}, HasLimit (pair X Y) := fun {X Y} ↦ by
    let P : FormalCoproduct.{w} C := ⟨X.I × Y.I, fun p ↦ X.obj p.1 ⨯ Y.obj p.2⟩
    let p₁ : P ⟶ X := ⟨fun p ↦ p.1, fun _ ↦ prod.fst⟩
    let p₂ : P ⟶ Y := ⟨fun p ↦ p.2, fun _ ↦ prod.snd⟩
    let s : BinaryFan X Y := BinaryFan.mk p₁ p₂
    exact HasLimit.mk ⟨s, BinaryFan.IsLimit.mk s
      (fun {_} f g ↦ ⟨fun i ↦ (f.f i, g.f i), fun i ↦ prod.lift (f.φ i) (g.φ i)⟩)
      (fun {_} _ _ ↦ hom_ext rfl fun i ↦ by simp [s, p₁])
      (fun {_} _ _ ↦ hom_ext rfl fun i ↦ by simp [s, p₂])
      (fun {_} f g m h₁ h₂ ↦ by
        subst h₁
        subst h₂
        refine hom_ext (funext fun _ ↦ rfl) fun i ↦ ?_
        simp only [s, p₁, p₂, BinaryFan.mk_fst, BinaryFan.mk_snd, category_comp_φ, eqToHom_refl,
          Category.comp_id]
        exact (prod.hom_ext (by simp) (by simp)).symm)⟩
  exact hasBinaryProducts_of_hasLimit_pair (FormalCoproduct.{w} C)

end CategoryTheory.Limits.FormalCoproduct

end
