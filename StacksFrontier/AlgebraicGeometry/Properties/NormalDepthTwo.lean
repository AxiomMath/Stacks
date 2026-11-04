module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Depth two at a point of codimension at least two of a normal scheme

A Noetherian normal local domain of Krull dimension at least two has depth at least two: this is
the case `k = 2` of Serre's condition `(S₂)`, which [Stacks, Tag 031S] establishes for every
normal Noetherian ring, read at the maximal ideal. On a locally Noetherian normal scheme the
local ring at a point is such a ring, so the same bound holds for the stalk at every point whose
codimension is at least two.

## Main results

* `Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed`: the ring form. A Noetherian normal
  local domain of dimension at least two has depth at least two.
* `AlgebraicGeometry.two_le_depth_stalk_of_two_le_ringKrullDim` and
  `AlgebraicGeometry.two_le_depth_stalk_of_two_le_coheight`: the scheme forms, with the
  dimension hypothesis read on the stalk and on the space respectively.

## Implementation notes

The depth is Mathlib's `Module.depth` along the maximal ideal, which is the notion
[Stacks, Tag 00LI] defines and the one the coherence criteria of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthTwoRestriction`
consume. The `(S₂)` inequality of `min_two_le_moduleDepth_of_isIntegrallyClosed` is stated with
the unqualified `moduleDepth`, which agrees with it on a nonzero finite module over a Noetherian
local ring (`moduleDepth_eq_depth`); a normal local domain is such a module over itself.

The dimension hypothesis is phrased in `WithBot ℕ∞`, the target of `ringKrullDim`, whose `⊥`
records the dimension of the empty spectrum. A ring of dimension at least two is in particular
nonzero, so the hypothesis already rules `⊥` out and no nontriviality assumption is needed
beyond the domain structure.

## References

* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public section

open AlgebraicGeometry Order

universe u

namespace Stacks.NormalDepth

/-- **A Noetherian normal local domain of dimension at least two has depth at least two.**

This is Serre's condition `(S₂)` at the maximal ideal: the normal ring `A` satisfies
`min(2, dim A) ≤ depth A` by `min_two_le_moduleDepth_of_isIntegrallyClosed`, and the dimension
hypothesis turns the minimum into `2`. -/
theorem two_le_depth_of_isIntegrallyClosed (A : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] [IsIntegrallyClosed A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    (2 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A := by
  have hS2 := min_two_le_moduleDepth_of_isIntegrallyClosed A
  rw [moduleDepth_eq_depth] at hS2
  refine le_trans (le_of_eq ?_) hS2
  refine (min_eq_left ?_).symm
  rcases eq_or_ne (ringKrullDim A) ⊥ with hbot | hbot
  · rw [hbot] at hdim
    simp at hdim
  · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
    rw [← hd] at hdim ⊢
    rw [WithBot.unbotD_coe]
    exact WithBot.coe_le_coe.mp (show ((2 : ℕ∞) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) from hdim)

end Stacks.NormalDepth

namespace AlgebraicGeometry

/-- **The stalk of a normal scheme at a point of codimension at least two has depth at least
two.** On a locally Noetherian normal scheme the local ring at a point is a Noetherian normal
local domain, so `Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed` applies to it.

This is the depth hypothesis of the direct-image coherence step
`Stacks.LocalCohomology.isCoherent_pushforward_restrict_of_two_le_depth_of_notMem`. -/
theorem two_le_depth_stalk_of_two_le_ringKrullDim {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (x : X)
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed _ hdim

/-- The same bound with the dimension hypothesis read on the space: the codimension of a point,
`Order.coheight`, is the Krull dimension of its local ring by [Stacks, Tag 02IZ]. -/
theorem two_le_depth_stalk_of_two_le_coheight {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (x : X) (hx : (2 : ℕ∞) ≤ coheight x) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  two_le_depth_stalk_of_two_le_ringKrullDim x
    (by
      rw [ringKrullDim_stalk_eq_coheight]
      exact (WithBot.coe_le_coe.mpr hx : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (coheight x : WithBot ℕ∞)))

end AlgebraicGeometry

end
