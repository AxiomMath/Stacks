module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Over
import StacksCore.Tactic.StacksAttribute

/-!
# The objects of a covering sieve are cover-dense in the slice site

Let `(𝒞, J)` be a site, let `U` be an object and let `S` be a covering sieve of `U`. The objects
of the slice category `𝒞/U` which belong to `S` — that is, the objects `(W, p : W ⟶ U)` with
`S.arrows p` — form a full subcategory of `𝒞/U`, and this file proves that its inclusion is
**cover-dense** for the slice topology `J.over U`.

This is the site-theoretic content of the step of [Stacks, Tag 099E] which says that two
presheaves on `𝒞/U` agreeing above a covering `{U_j → U}` have the same sheafification: a
presheaf on `𝒞/U` is determined, after sheafification, by its restriction to the objects lying
over one of the `U_j`, because those objects cover every object of `𝒞/U`.

An arrow `(W', p') ⟶ (W, p)` of `𝒞/U` factors through an object of `S` exactly when
`S.arrows p'`, because `S` is downward closed; so the sieve `Sieve.coverByImage` of the inclusion
at `(W, p)` is the sieve of arrows whose composite to `U` lies in `S`, whose image in `Sieve W`
under `Sieve.overEquiv` is the pullback `S.pullback p`. That pullback is covering because `S` is.

## Main definitions

* `CategoryTheory.Sieve.overObjects`: the property of an object of `𝒞/U` of belonging to a
  sieve `S` on `U`.

## Main results

* `CategoryTheory.Sieve.overEquiv_coverByImage_ι_overObjects`: the `coverByImage` sieve of the
  inclusion is, under `Sieve.overEquiv`, the pullback of `S`.
* `CategoryTheory.Sieve.isCoverDense_ι_overObjects`: **the inclusion of the objects of a
  covering sieve into the slice site is cover-dense.**

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Sieve

variable {C : Type u} [Category.{v} C] {U : C}

/-- **The objects of the slice category `𝒞/U` which belong to a sieve `S` on `U`.** Since `S` is
a sieve, this full subcategory is closed under precomposition: every arrow of `𝒞/U` with target
in it has its source in it as well. -/
@[sga "3 IV 4.1.7", sga "3 IV 4.3.17" "object set E(R) of R̄"]
def overObjects (S : Sieve U) : ObjectProperty (Over U) := fun W ↦ S.arrows W.hom

/-- An object `(W, p)` of `𝒞/U` lies in `S.overObjects` if and only if `S.arrows p`. -/
theorem overObjects_iff (S : Sieve U) (W : Over U) : S.overObjects W ↔ S.arrows W.hom := Iff.rfl

/-- The source of any arrow of `𝒞/U` whose target lies in `S` lies in `S`. -/
theorem overObjects_of_hom (S : Sieve U) {W W' : Over U} (h : W' ⟶ W) (hW : S.overObjects W) :
    S.overObjects W' := by
  have := S.downward_closed hW h.left
  simpa only [overObjects, Over.w h] using this

/-- **The `coverByImage` sieve of the inclusion of the objects of `S`, read as a sieve on the
base.** Its arrows into `(W, p)` are exactly those whose composite to `U` lies in `S`, so the
corresponding sieve on `W` is the pullback of `S` along `p`. -/
theorem overEquiv_coverByImage_ι_overObjects (S : Sieve U) (W : Over U) :
    Sieve.overEquiv W (Sieve.coverByImage (S.overObjects).ι W) = S.pullback W.hom := by
  refine le_antisymm ?_ ?_
  · intro W' p hp
    rw [Sieve.overEquiv_iff] at hp
    obtain ⟨Z, l, -⟩ := hp.some
    exact overObjects_of_hom S l Z.property
  · intro W' p hp
    rw [Sieve.overEquiv_iff]
    refine ⟨⟨⟨Over.mk (p ≫ W.hom), hp⟩, 𝟙 _, Over.homMk p, by simp⟩⟩

/-- **The inclusion of the objects of a covering sieve into the slice site is cover-dense.**
Every object of `𝒞/U` is covered by objects lying in `S`, because the pullback of the covering
sieve `S` along the structure map is covering. -/
theorem isCoverDense_ι_overObjects {J : GrothendieckTopology C} (S : Sieve U) (hS : S ∈ J U) :
    (S.overObjects).ι.IsCoverDense (J.over U) where
  is_cover W := by
    rw [GrothendieckTopology.mem_over_iff, overEquiv_coverByImage_ι_overObjects]
    exact J.pullback_stable W.hom hS

end CategoryTheory.Sieve

end
