module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.CategoryTheory.FiberedInGroupoids

/-!
# Uniqueness of the amelioration of a 1-morphism of fibred categories

Stacks 06N8: let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over `𝒞`, and
suppose `F` factors in two ways, as `𝒳 ⟶[a] 𝒳' ⟶[f] 𝒴` and as `𝒳 ⟶[b] 𝒳'' ⟶[g] 𝒴`, with
`a`, `b` equivalences over `𝒞` and `f`, `g` themselves fibred in groupoids. Then `𝒳'` and
`𝒳''` are equivalent over `𝒴` compatibly with the first legs: there is an equivalence
`h : 𝒳'' ⥤ 𝒳'` with `h ⋙ f ≅ g` and `b ⋙ h ≅ a`. So the factorization produced by Stacks
06N7 is unique up to equivalence over `𝒴`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-- **Stacks 06N8** (uniqueness of the factorization of 4.35.16 / 06N7).

Let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over `𝒞`. Suppose `F`
is factored in two ways through categories fibred in groupoids over `𝒞`:
`𝒳 ⟶[a] 𝒳' ⟶[f] 𝒴` and `𝒳 ⟶[b] 𝒳'' ⟶[g] 𝒴`, where

* `a`, `b` are equivalences (over `𝒞`);
* the two factorizations agree with `F`: `a ⋙ f ≅ F` and `b ⋙ g ≅ F`.

Then there is an equivalence `h : 𝒳'' ⥤ 𝒳'` **over `𝒴`** (i.e. `h.IsEquivalence` together
with `h ⋙ f ≅ g`) such that `b ⋙ h ≅ a`. In particular the intermediate category is unique
up to equivalence over `𝒴`, compatibly with the first legs.

The conclusion uses none of the remaining data of 06N8 — the structure functors
`p : 𝒳 ⥤ 𝒞`, `q : 𝒴 ⥤ 𝒞`, `p' : 𝒳' ⥤ 𝒞`, `p'' : 𝒳'' ⥤ 𝒞`, their fiberedness in
groupoids, that of `f` and `g`, and the compatibilities `a ⋙ p' = p`, `b ⋙ p'' = p`,
`f ⋙ q = p'`, `g ⋙ q = p''` — so it is stated in the general form below, which
specializes to 06N8 in the fibred setting. -/
@[stacks 06N8]
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
