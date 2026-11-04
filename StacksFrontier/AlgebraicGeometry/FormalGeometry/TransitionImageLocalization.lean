module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import StacksFrontier.RingTheory.Localization.CoatomAtMaximal

/-!
# The transition image of a direct system dies over a localization

Let `G` be a direct system of modules over a commutative ring `A`, indexed by `ℕ`, let `g : A`,
and let `a ≤ n` and `m ≤ n`. If the images of `G a → G n` and of `G m → G n` have the same
localization away from `g`, then the image of `G m` in `G n ⧸ im(G a → G n)` vanishes after
localizing away from `g`.

This is the bridge between the two shapes the route of [Stacks, Tag 0EHK] passes through at the
step over one chart `D(g)` of the punctured spectrum. What the localized `Ext` systems of that
route produce is an *equality of images* after localization; what
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_localizedAway` consumes is the
*vanishing of a localized quotient*, one statement per chart. The two are the same statement,
and the only content of the translation is that an element of the localized image is already in
the image after multiplication by a power of `g`.

## Main results

* `Stacks.Algebraization.subsingleton_localizedAway_transitionImage` — the translation, in the
  shape of the `hloc` hypothesis of
  `Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_localizedAway`.

## Implementation notes

Neither Noetherianness of `A` nor finiteness of the terms of `G` is used: the statement is about
one element at a time, and `Submodule.exists_smul_mem_of_mem_localized₀` produces the power of
`g` that kills it with no finiteness anywhere. The hypothesis is stated with
`Submodule.localized₀` at `LocalizedModule.mkLinearMap`, the same localization of `G n` whose
quotient `LocalizedModule.Away` the conclusion speaks of.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- **The image of a later term in the quotient by an earlier one dies over `A_g`, as soon as
the two images agree over `A_g`.** For a direct system `G` of `A`-modules and indices `a ≤ n`,
`m ≤ n`, suppose the images of `G m → G n` and `G a → G n` have the same localization away from
`g : A`. Then the image of `G m` in `G n ⧸ im(G a → G n)` is killed by localizing away from `g`.

This is the hypothesis `hloc` of
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_localizedAway`, which checks the
transition-image condition of [Stacks, Tag 0EHK] one chart of the punctured spectrum at a
time. -/
theorem subsingleton_localizedAway_transitionImage (G : ℕ ⥤ ModuleCat.{u} A) (g : A)
    {a m n : ℕ} (han : a ≤ n) (hmn : m ≤ n)
    (h : Submodule.localized₀ (Submonoid.powers g)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) (G.obj n))
          (LinearMap.range (G.map (homOfLE hmn)).hom) =
        Submodule.localized₀ (Submonoid.powers g)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) (G.obj n))
          (LinearMap.range (G.map (homOfLE han)).hom)) :
    Subsingleton (LocalizedModule.Away g
      (LinearMap.range ((LinearMap.range (G.map (homOfLE han)).hom).mkQ ∘ₗ
        (G.map (homOfLE hmn)).hom) : Type u)) := by
  rw [LocalizedModule.subsingleton_iff]
  intro y
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp y.2
  -- the image of `w` in `G n` lies in the localization of `im(G a → G n)`, by the hypothesis
  have hmem : LocalizedModule.mkLinearMap (Submonoid.powers g) (G.obj n)
        ((G.map (homOfLE hmn)).hom w) ∈
      Submodule.localized₀ (Submonoid.powers g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) (G.obj n))
        (LinearMap.range (G.map (homOfLE hmn)).hom) :=
    ⟨(G.map (homOfLE hmn)).hom w, ⟨w, rfl⟩, 1, by simp⟩
  rw [h] at hmem
  obtain ⟨t, ht⟩ := Submodule.exists_smul_mem_of_mem_localized₀ (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) (G.obj n)) hmem
  refine ⟨(t : A), t.2, Subtype.ext ?_⟩
  rw [SetLike.val_smul, ZeroMemClass.coe_zero, ← hw, LinearMap.comp_apply, ← map_smul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ht

end Stacks.Algebraization

end
