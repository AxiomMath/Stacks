module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import StacksFrontier.RingTheory.Noetherian.DirectSystemTransitionImageSupport

/-!
# One stabilisation index for every chart at once

The hypothesis `himg` of
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_localizedAway`
asks for an index `a` chosen **before** the chart `D(f j)`: past it, and for `n ≫ m ≫ a`, the
images of `G m → G n` and `G a → G n` have the same localization away from `f j`, for every `j`
at once.

What the route of [Stacks, Tag 0EHK] produces over a chart is an index for *that* chart: the
stabilisation index of the images of a cocone on the localized system, which comes from
Noetherianness of a module over the chart's own ring and so depends on `j`. This file exchanges
the two quantifiers. The exchange is free, and for the reason the finiteness of the family is
there at all: with `a` the supremum of the per-chart indices, the chart's own conclusion at
`a j ≤ a ≤ m` *sandwiches* the image of `G a → G n` between two images that the chart says are
equal, since the transition images shrink as the index grows.

So no object over the base ring is needed to compare the charts, and the per-chart index is as
good as a uniform one.

## Main results

* `Stacks.Algebraization.exists_localized₀_range_transitionMap_eq_of_chart` — the quantifier
  exchange, landing exactly on the hypothesis `himg` of
  `Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_localizedAway`.

## Implementation notes

The index `k` is left inside the chart, where `himg` also has it: only `a` is pulled out. That
is possible because `a` is compared across charts by the sandwich, while `k` never has to be —
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_localizedAway` takes the
supremum of the `k` itself.

Nothing about the ring is assumed: not local, not Noetherian, and the family `f` is not required
to generate anything. The statement is about a direct system of modules and a finite family of
elements, and the only input is that the family is finite, through `Finset.univ.sup`.

Monotonicity of `Submodule.localized₀` in its submodule argument is immediate from
`Submodule.mem_localized₀` and is taken as a private lemma here: Mathlib's
`Submodule.localized₀_le_localized₀_of_smul_le` is the statement with a factor from the
submonoid in front, and specialising it to the unit costs more than the two lines of the
direct proof.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- Localizing a submodule is monotone in the submodule: a representative of an element of the
localization of the smaller one represents it in the localization of the larger. -/
private theorem localized₀_mono {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (p : Submonoid A) (l : X →ₗ[A] Y) [IsLocalizedModule p l]
    {N P : Submodule A X} (hNP : N ≤ P) : N.localized₀ p l ≤ P.localized₀ p l := by
  rintro - ⟨x, hx, s, rfl⟩
  exact ⟨x, hNP hx, s, rfl⟩

/-- The transition images of a direct system shrink as the source index grows: for `a ≤ m ≤ n`
the image of `G a → G n` is contained in that of `G m → G n`, because the first map factors
through the second. -/
private theorem range_map_le_range_map (G : ℕ ⥤ ModuleCat.{u} A) {a m n : ℕ} (ham : a ≤ m)
    (hmn : m ≤ n) (han : a ≤ n) :
    LinearMap.range (G.map (homOfLE han)).hom ≤ LinearMap.range (G.map (homOfLE hmn)).hom := by
  rintro - ⟨x, rfl⟩
  exact ⟨(G.map (homOfLE ham)).hom x, Stacks.directSystem_map_comp_apply G ham hmn han x⟩

/-- **One stabilisation index serves every chart.** Let `G` be a direct system of `A`-modules and
`f : Fin r → A` a finite family. Suppose that over each chart `D(f j)` there is an index `a j`
past which, for `n ≫ m ≫ a j`, the images of `G m → G n` and `G (a j) → G n` have the same
localization away from `f j`. Then there is a *single* index `a`, independent of the chart, with
the same property — which is the hypothesis `himg` of
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_localizedAway`.

*Argument.* Take `a` to be the supremum of the `a j`, which exists because the family is finite.
Fix `m ≥ a` and a chart `j`. Then `a j ≤ a ≤ m ≤ n`, so the transition images satisfy
`im(G (a j) → G n) ≤ im(G a → G n) ≤ im(G m → G n)`, and the chart's conclusion at the index
`a j` says that the outer two of the three localize to the same submodule. The middle one is
therefore squeezed onto them, which is the conclusion at `a`. -/
theorem exists_localized₀_range_transitionMap_eq_of_chart (G : ℕ ⥤ ModuleCat.{u} A) {r : ℕ}
    (f : Fin r → A)
    (h : ∀ j : Fin r, ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      Submodule.localized₀ (Submonoid.powers (f j))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (G.obj n))
          (LinearMap.range (G.map (homOfLE hmn)).hom) =
        Submodule.localized₀ (Submonoid.powers (f j))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (G.obj n))
          (LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom)) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m) (j : Fin r), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      Submodule.localized₀ (Submonoid.powers (f j))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (G.obj n))
          (LinearMap.range (G.map (homOfLE hmn)).hom) =
        Submodule.localized₀ (Submonoid.powers (f j))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (G.obj n))
          (LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom) := by
  choose a ha using h
  refine ⟨Finset.univ.sup a, fun m hm j => ?_⟩
  have hsup : a j ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ j)
  have haj : a j ≤ m := hsup.trans hm
  obtain ⟨k, hk⟩ := ha j m haj
  refine ⟨k, fun n hmn hkn => le_antisymm ?_ ?_⟩
  · -- `im(G m → G n)` localizes onto `im(G (a j) → G n)`, which sits inside `im(G a → G n)`
    rw [hk n hmn hkn]
    exact localized₀_mono _ _
      (range_map_le_range_map G hsup (hm.trans hmn) (haj.trans hmn))
  · -- and `im(G a → G n)` sits inside `im(G m → G n)`
    exact localized₀_mono _ _ (range_map_le_range_map G hm hmn (hm.trans hmn))

end Stacks.Algebraization

end
