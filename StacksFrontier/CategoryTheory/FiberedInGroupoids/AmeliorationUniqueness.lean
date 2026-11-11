module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.CategoryTheory.FiberedInGroupoids

/-!
# Uniqueness of a factorization through equivalences, for bare categories

`amelioration_unique`: if `F : 𝒳 ⥤ 𝒴` factors up to isomorphism as `a ⋙ f` and as `b ⋙ g`
with `a`, `b` equivalences, then `h = b⁻¹ ⋙ a` is an equivalence with `h ⋙ f ≅ g` and
`b ⋙ h ≅ a`. This ignores every base category and every strictness requirement. Stacks 06N8
itself, for categories fibred in groupoids over a base with 1-morphisms strictly over the base
and 2-isomorphisms over identities, is in
`StacksFrontier.CategoryTheory.FiberedInGroupoids.AmeliorationUniquenessOver`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-- Uniqueness of a factorization through equivalences, for bare categories.

Let `F : 𝒳 ⥤ 𝒴` be factored up to isomorphism in two ways, `a ⋙ f ≅ F` and `b ⋙ g ≅ F`, with
`a` and `b` equivalences. Then there is an equivalence `h : 𝒳'' ⥤ 𝒳'` with `h ⋙ f ≅ g` and
`b ⋙ h ≅ a`, namely `h = b⁻¹ ⋙ a`.

This ignores all base categories: `h ⋙ f ≅ g` is only an isomorphism and nothing lies over
identities, so it is much weaker than Stacks 06N8, which is
`CategoryTheory.Functor.IsFiberedInGroupoids.amelioration_unique_isEquivalenceOver` and
`CategoryTheory.Functor.IsFiberedInGroupoids.amelioration_unique_isEquivalenceOver_of_comp_eq`. -/
theorem amelioration_unique
    {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    {𝒳' : Type u₄} [Category.{v₄} 𝒳']
    {𝒳'' : Type u₅} [Category.{v₅} 𝒳'']
    (F : 𝒳 ⥤ 𝒴) (a : 𝒳 ⥤ 𝒳') (b : 𝒳 ⥤ 𝒳'')
    (f : 𝒳' ⥤ 𝒴) (g : 𝒳'' ⥤ 𝒴)
    (ha_equiv : a.IsEquivalence) (hb_equiv : b.IsEquivalence)
    (hleft : a ⋙ f ≅ F) (hright : b ⋙ g ≅ F) :
    ∃ (h : 𝒳'' ⥤ 𝒳') (_ : h.IsEquivalence) (_ : h ⋙ f ≅ g),
      Nonempty (b ⋙ h ≅ a) := by
  have := ha_equiv
  have := hb_equiv
  exact
    ⟨Functor.inv b ⋙ a, inferInstance,
      Functor.associator (Functor.inv b) a f ≪≫
        Functor.isoWhiskerLeft _ hleft ≪≫
        Functor.isoWhiskerLeft _ hright.symm ≪≫
        (Functor.associator (Functor.inv b) b g).symm ≪≫
        Functor.isoWhiskerRight b.asEquivalence.counitIso g ≪≫
        Functor.leftUnitor g,
      ⟨Functor.associator b (Functor.inv b) a ≪≫
        Functor.isoWhiskerRight b.asEquivalence.unitIso.symm a ≪≫
        Functor.leftUnitor a⟩⟩
