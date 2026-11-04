module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem

/-!
# Disjoint unions of the finite levels of a family of completed thickenings

A morphism of `CRIS(C/A)` is a map of the underlying divided power rings, so the categorical
*product* of a family of objects of `CRIS(C/A)` is the product of their rings, the *disjoint union*
`⊔_i Spec(B_i)` of the corresponding affine schemes. By
`Crystalline.DividedPowerThickening.hasProduct_iff_exists_pow_natCast_eq_zero` the product of a
family exists exactly when a single power of `p` kills every member of the family, whatever the
index type.

The `p`-adically completed divided power envelopes `D` of [Stacks, Tag 07KD] are objects of
`Cris^∧(C/A)`, where `p` is not nilpotent; the objects of `CRIS(C/A)` attached to them are the
finite levels `D/(p)^k`, and `p ^ k` kills `D/(p)^k` with the exponent `k` depending on the level
alone (`Crystalline.pow_natCast_eq_zero_levelRing`). So at a fixed level the disjoint union of an
arbitrary family exists.

## Main results

* `Crystalline.hasProduct_levelThickeningObj`: the disjoint union `⊔_i Spec(D_i/(p)^k)` of the
  level-`k` thickenings of an arbitrary family of completed crystalline thickenings exists in
  `CRIS(C/A)`, for an arbitrary index type, as soon as `k` is a `p`-adic level of each member.
* `Crystalline.hasProduct_levelFunctor_obj`: the same at the uniform cutoff
  `Crystalline.uniformLevel`, which is a `p`-adic level of every object of `Cris^∧(C/A)`, with no
  hypothesis on the family.

## References

* [Stacks Project, Tag 07MM](https://stacks.math.columbia.edu/tag/07MM)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Crystalline

variable {s : AffineCrystallineSituation.{u, v}}

/-- **The disjoint union of the level-`k` thickenings of an arbitrary family of completed
crystalline thickenings exists in `CRIS(C/A)`**, for an arbitrary index type, when `k` is a
`p`-adic level of each member of the family. -/
theorem hasProduct_levelThickeningObj {ι : Type w}
    (Y : ι → CompletedCrystallineThickening.{u, v, w} s) (k : ℕ)
    (h : ∀ i, IsPAdicLevel (Y i).ring.ideal (Y i).ring.dividedPowers s.p k) :
    HasProduct (fun i => levelThickeningObj (Y i) k (h i)) :=
  DividedPowerThickening.hasProduct_of_pow_eq_zero _ k
    fun i ↦ pow_natCast_eq_zero_levelRing s.p (Y i).ring k (h i)

/-- **The disjoint union of the levels of an arbitrary family of completed crystalline
thickenings, at the uniform cutoff, exists in `CRIS(C/A)`**: the product of the underlying objects
of the values of `Crystalline.levelFunctor` at level `e`, for an arbitrary family over an arbitrary
index type. -/
theorem hasProduct_levelFunctor_obj {ι : Type w}
    (Y : ι → CompletedCrystallineThickening.{u, v, w} s) (e : ℕ) :
    HasProduct fun i =>
      ((levelFunctor s).obj (Y i, Opposite.op e)).obj :=
  hasProduct_levelThickeningObj Y (uniformLevel s + e)
    fun i ↦ isPAdicLevel_uniformLevel_add (Y i) e

end Crystalline

end
