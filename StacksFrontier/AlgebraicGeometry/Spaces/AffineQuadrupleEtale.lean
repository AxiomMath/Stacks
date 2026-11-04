module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# The induced chart of a fibre product of étale charts is étale

Let `g' ≫ f = f' ≫ g` be a cartesian square of algebraic spaces, and let `a : U ⟶ X`,
`b : V ⟶ Y`, `c : V' ⟶ Y'` be étale with `U ⟶ V ⟵ V'` over `X ⟶ Y ⟵ Y'`. For
`U' = V' ×_V U`, the induced morphism `a' : U' ⟶ X' = Y' ×_Y X` is étale: it factors as the base
change along `V' ⟶ V` of the morphism `U ⟶ V ×_Y X`, étale by Stacks 03FV, followed by the base
change along `f'` of `c`. This is the étale morphism along which condition (2) of Stacks 0DKG
restricts `K'`.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_isPullback_of_etaleQuadruple`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The induced chart of a fibre product of étale charts is étale.** In a cartesian square
`g' ≫ f = f' ≫ g` of algebraic spaces, for étale `a : U ⟶ X`, `b : V ⟶ Y`, `c : V' ⟶ Y'` and a
cartesian square `U' = V' ×_V U` over `U ⟶ V ⟵ V'` compatible with them, every
`a' : U' ⟶ X'` compatible with `a` and `c` is étale. -/
theorem isEtale_of_isPullback_of_etaleQuadruple {X Y X' Y' U V V' U' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    {a : U ⟶ X} {b : V ⟶ Y} {c : V' ⟶ Y'} {a' : U' ⟶ X'} {f₀ : U ⟶ V} {g₀ : V' ⟶ V}
    {f₀' : U' ⟶ V'} {g₀' : U' ⟶ U} (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hc : IsEtale B S hS c.hom) (hpb : IsPullback g₀' f₀' f₀ g₀) (hfa : f₀ ≫ b = a ≫ f)
    (hgc : g₀ ≫ b = c ≫ g) (hfc : f₀' ≫ c = a' ≫ f') (hga : g₀' ≫ a = a' ≫ g') :
    IsEtale B S hS a'.hom := by
  -- `Q = V ×_Y X`, with its étale projection to `X`
  have hQ := IsPullback.of_hasPullback b f
  -- `m : U ⟶ Q` is étale, a morphism over `X` between spaces étale over `X`
  let m : U ⟶ pullback b f := pullback.lift f₀ a hfa
  have hm : IsEtale B S hS m.hom :=
    isEtale_of_isEtale_over B S hS U.2 (pullback b f).2 X.2 m.hom a.hom (pullback.snd b f).hom ha
      (isEtale_of_isPullback B S hS (pullback.fst b f) (pullback.snd b f) b f hQ hb)
      (congrArg (fun k => k.hom) (pullback.lift_snd f₀ a hfa))
  -- `P = Q ×_V V'`
  have hP := IsPullback.of_hasPullback (pullback.fst b f) g₀
  let ℓ : U' ⟶ pullback (pullback.fst b f) g₀ :=
    pullback.lift (g₀' ≫ m) f₀' (by rw [Category.assoc, pullback.lift_fst, hpb.w])
  have hℓsq : IsPullback g₀' ℓ m (pullback.fst (pullback.fst b f) g₀) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hP
    rwa [pullback.lift_snd, pullback.lift_fst]
  -- `s : P ⟶ X'`, the base change of `c` along `f'`
  have hs_w : (pullback.fst (pullback.fst b f) g₀ ≫ pullback.snd b f) ≫ f =
      (pullback.snd (pullback.fst b f) g₀ ≫ c) ≫ g := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, hgc, Category.assoc]
  let s : pullback (pullback.fst b f) g₀ ⟶ X' := sq.lift _ _ hs_w
  have hssq : IsPullback s (pullback.snd (pullback.fst b f) g₀) f' c := by
    refine IsPullback.of_right ?_ (sq.lift_snd _ _ _) sq
    rw [sq.lift_fst, ← hgc]
    exact hP.paste_horiz hQ.flip
  have ha' : a' = ℓ ≫ s := by
    refine sq.hom_ext ?_ ?_
    · rw [← hga, Category.assoc, sq.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, pullback.lift_snd]
    · rw [← hfc, Category.assoc, sq.lift_snd, ← Category.assoc, pullback.lift_snd]
  rw [ha']
  exact isEtale_comp B S hS (isEtale_of_isPullback B S hS g₀' ℓ m _ hℓsq hm)
    (isEtale_of_isPullback B S hS _ s c f' hssq.flip hc)

end AlgebraicGeometry.Space
