module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity

/-!
# The localization step for a single Chow class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` which is flat of relative dimension `r`, let
`V ⊆ Y` be an open subscheme and let `Z ⊆ Y` be a closed subscheme whose support is the
complement of `V`.

`Stacks.Chow.flatPullbackChow_surjective_of_opens_of_comap` deduces surjectivity of flat pullback
along `f` in degree `k` from surjectivity along both base changes of `f`. Its proof treats one
class `α` at a time and uses the hypothesis over `V` only on the restriction of `α` to
`f^{-1}(V)`. This file records that per-class form: the hypothesis over `V` is weakened to the
statement that the restriction of the *given* class `α` lies in the range of flat pullback along
`f ∣_ V`, and the conclusion is weakened to membership of `α` in the range of flat pullback along
`f`. The hypothesis over `Z` stays a surjectivity statement, since the class on `f^{-1}(Z)` that
the proof must pull back is only produced inside the argument.

This is what a devissage of the source needs when the open subscheme `V` is chosen in terms of
the class being lifted rather than once and for all.

## Main results

* `Stacks.Chow.mem_range_flatPullbackChow_of_opens_of_comap` — the per-class localization step:
  a class whose restriction to the inverse image of `V` is a flat pullback from `V` is a flat
  pullback from `Y`, provided flat pullback along the base change to `Z` is surjective.
* `Stacks.Chow.flatPullbackChow_surjective_of_opens_of_comap'` — the surjectivity statement of
  `Stacks.Chow.flatPullbackChow_surjective_of_opens_of_comap`, recovered from the per-class form.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **The localization step in the proof of Stacks 02TT, for a single class.** Let `f : X ⟶ Y` be
flat of relative dimension `r` between schemes locally of finite type over the base of chapter
42, let `V ⊆ Y` be an open subscheme and let `Z ⊆ Y` be a closed subscheme whose support is the
complement of `V`. Let `α` be a class on `X` in degree `k + r` whose restriction to `f^{-1}(V)`
is a flat pullback along `f ∣_ V : f^{-1}(V) ⟶ V` of a class on `V` in degree `k`. If flat
pullback in degree `k` is surjective along the base change `f^{-1}(Z) ⟶ Z`, then `α` is a flat
pullback along `f` of a class on `Y` in degree `k`.

The class on `V` is the restriction of a class `β` on `Y` by the surjectivity half of Stacks
02RX. Flat pullback commutes with the two restrictions by Stacks 02RD, so `α - f^* β` restricts
to zero on `f^{-1}(V)`; by the exactness half of Stacks 02RX it is the pushforward of a class on
`f^{-1}(Z)`, which by the hypothesis over `Z` is a pullback of a class `γ` on `Z`. Base change
for a closed immersion, Stacks 02RG, turns the pushforward of the pullback of `γ` into the
pullback of the pushforward of `γ`, so `α = f^*(β + i_* γ)`. -/
theorem mem_range_flatPullbackChow_of_opens_of_comap (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (V : Y.Opens) (Z : Y.IdealSheafData)
    (hcomplement : Set.range Z.subschemeι.base = (Set.range V.ι.base)ᶜ)
    (α : chowGroup C (f ≫ sY) (k + (r : ℤ)))
    (hV : chowGroupOpensRestrictOfIsOpenImmersion C (f ≫ sY) (f ⁻¹ᵁ V) (k + (r : ℤ)) α ∈
      (flatPullbackChowOfRelativeDimension C ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (V.ι ≫ sY) (f ∣_ V)
        (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) r
        (relativeDimension_morphismRestrict' f V r hf) k).range)
    (hZ : Function.Surjective
      (letI := locallyOfFiniteType_comapRestrict Z f
       letI := flat_comapRestrict Z f
       flatPullbackChowOfRelativeDimension C ((Z.comap f).subschemeι ≫ f ≫ sY)
        (Z.subschemeι ≫ sY) (comapRestrict Z f)
        (comapRestrict_comp_base C (f ≫ sY) sY f rfl Z) r
        (relativeDimension_comapRestrict Z f hf) k)) :
    α ∈ (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k).range := by
  let _ := locallyOfFiniteType_comapRestrict Z f
  let _ := flat_comapRestrict Z f
  -- the inverse image of `Z` is the closed complement of the inverse image of `V`
  have hcompl : Set.range (Z.comap f).subschemeι.base =
      (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Scheme.Opens.range_ι, TopologicalSpace.Closeds.coe_preimage]
    have hZV : (Z.support : Set Y) = ((V : Set Y))ᶜ := by
      rw [← Scheme.IdealSheafData.range_subschemeι, hcomplement, Scheme.Opens.range_ι]
    rw [hZV]
    rfl
  -- the class on `V` pulling back to the restriction of `α` comes from `Y`
  obtain ⟨β₀, hβ₀⟩ := AddMonoidHom.mem_range.mp hV
  obtain ⟨β, hβ⟩ := surjective_chowGroupOpensRestrictOfIsOpenImmersion C sY V k β₀
  have hzero : chowGroupOpensRestrictOfIsOpenImmersion C (f ≫ sY) (f ⁻¹ᵁ V) (k + (r : ℤ))
      (α - flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k β) = 0 := by
    rw [map_sub, chowGroupOpensRestrict_flatPullbackChow C sY f r hf k V β, hβ, hβ₀, sub_self]
  -- Stacks 02RX: the difference is a pushforward from the inverse image of `Z`
  obtain ⟨a, ha⟩ := (exact_chowPushforward_chowGroupOpensRestrict C (f ≫ sY)
    ((Z.comap f).subschemeι ≫ f ≫ sY) (Z.comap f).subschemeι rfl (f ⁻¹ᵁ V) hcompl
    (k + (r : ℤ)) _).mp hzero
  obtain ⟨γ, hγ⟩ := hZ a
  refine AddMonoidHom.mem_range.mpr
    ⟨β + chowPushforwardOfIsClosedImmersion C (Z.subschemeι ≫ sY) sY Z.subschemeι rfl k γ, ?_⟩
  rw [map_add, flatPullbackChow_chowPushforward_comap C (f ≫ sY) sY f rfl r hf k Z γ, hγ, ha]
  abel

/-- **The localization step in the proof of Stacks 02TT.** Surjectivity of flat pullback in
degree `k` along the restriction `f ∣_ V` and along the base change `f^{-1}(Z) ⟶ Z` implies
surjectivity along `f`.

This is `Stacks.Chow.mem_range_flatPullbackChow_of_opens_of_comap` applied to each class in
turn, the hypothesis over `V` supplying the required range membership. -/
theorem flatPullbackChow_surjective_of_opens_of_comap' (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (V : Y.Opens) (Z : Y.IdealSheafData)
    (hcomplement : Set.range Z.subschemeι.base = (Set.range V.ι.base)ᶜ)
    (hV : Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (V.ι ≫ sY) (f ∣_ V)
      (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) r
      (relativeDimension_morphismRestrict' f V r hf) k))
    (hZ : Function.Surjective
      (letI := locallyOfFiniteType_comapRestrict Z f
       letI := flat_comapRestrict Z f
       flatPullbackChowOfRelativeDimension C ((Z.comap f).subschemeι ≫ f ≫ sY)
        (Z.subschemeι ≫ sY) (comapRestrict Z f)
        (comapRestrict_comp_base C (f ≫ sY) sY f rfl Z) r
        (relativeDimension_comapRestrict Z f hf) k)) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) :=
  fun α ↦ AddMonoidHom.mem_range.mp (mem_range_flatPullbackChow_of_opens_of_comap C sY f r hf k
    V Z hcomplement α (AddMonoidHom.mem_range.mpr (hV _)) hZ)

end Stacks.Chow

end
