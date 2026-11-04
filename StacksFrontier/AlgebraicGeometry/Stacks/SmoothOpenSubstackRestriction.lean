module

public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# Smoothness restricts to smaller open substacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `V ⊆ W` be open substacks
of `𝒳`. If the restriction of `f` to `W` is smooth, so is its restriction to `V`. This is how
smoothness over the base passes from an open substack of the stack of curves to the smaller
open substacks inside it, as in the proofs of Tags 0E00, 0E1N, 0E84 and 0E79.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.isSmooth_inclusion_comp_of_le`: the statement above.

## Implementation notes

The smooth locus `𝒰` of `f` (Tag 0DZR) contains `W`, hence `V`. By clause (1) of Tag 0DZR the
smooth locus of `V ⟶ 𝒳 ⟶ 𝒴` is the inverse image of `𝒰`, which is all of `V`, so the
restriction of `V ⟶ 𝒴` to its smooth locus is `V ⟶ 𝒴` itself up to the factorization of the
identity of `V` through that open substack, an equivalence.

## References

* [Stacks Project, Tag 0DZR](https://stacks.math.columbia.edu/tag/0DZR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The factorization of the identity of an algebraic stack through an open substack containing
every object is an equivalence of the underlying categories. -/
theorem OpenSubstack.isEquivalence_factor_id {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (hW : ∀ x, W.property x) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (W.factor B S hS (𝟙 𝒳) hW).hom) :=
  { faithful := ⟨fun {_ _} _ _ h => congrArg (fun k => k.hom) h⟩
    full := ⟨fun g => ⟨g.hom, rfl⟩⟩
    essSurj := ⟨fun y => ⟨y.obj, ⟨Iso.refl _⟩⟩⟩ }

/-- **Smoothness restricts to smaller open substacks.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` and `V ⊆ W` open substacks of `𝒳`. If `f` is smooth on `W`, it is smooth
on `V`. -/
theorem OpenSubstack.isSmooth_inclusion_comp_of_le {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) {V W : OpenSubstack 𝒳} (hle : V.property ≤ W.property)
    (hW : AlgebraicStacks.IsSmooth B S hS (W.inclusion ≫ f)) :
    AlgebraicStacks.IsSmooth B S hS (V.inclusion ≫ f) := by
  obtain ⟨U, hU⟩ := exists_isSmoothLocus B S hS f
  obtain ⟨U', hU'⟩ := exists_isSmoothLocus B S hS (V.inclusion ≫ f)
  have hall : ∀ x, U'.property x := fun x => by
    rw [isSmoothLocus_comp_of_isSmooth B S hS
      (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS V.inclusion V.isOpenImmersion) hU hU']
    exact hU.2 W hW _ (hle _ x.property)
  exact AlgebraicStacks.isSmooth_of_twoIso B S hS
    ((Bicategory.associator _ _ _).symm ≪≫ Bicategory.leftUnitor _)
    (AlgebraicStacks.isSmooth_comp B S hS _ _
      (AlgebraicStacks.isSmooth_of_isEquivalence B S hS (U'.factor B S hS (𝟙 _) hall)
        (U'.isEquivalence_factor_id B S hS hall)) hU'.1)

end AlgebraicGeometry.Stack

end
