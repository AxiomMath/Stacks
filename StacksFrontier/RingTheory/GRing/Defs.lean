module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.Regular.RegularRingHom

@[expose] public section

/-!
# G-rings

A commutative ring is a G-ring if it is Noetherian and the canonical map from each of its
local rings at a prime ideal to that local ring's completion is regular. An ideal-adic completion
of a G-ring need not be a G-ring; see [Nishimura] for an example and [Dumitrescu] for a
generalization.

## Main definitions

* `IsGRing`: the predicate that a commutative ring is a G-ring.

## References

* [Nishimura]
* [Dumitrescu]
* [Stacks Project, Tag 07GH](https://stacks.math.columbia.edu/tag/07GH)
* [Stacks Project, Tag 07PW](https://stacks.math.columbia.edu/tag/07PW)
-/

section

@[expose] public section

universe u

/-- A commutative ring is a G-ring if it is Noetherian and, for every prime ideal `p`, the
canonical map from its local ring at `p` to the completion of that local ring is regular. -/
@[stacks 07GH]
public def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (p : Ideal R) [p.IsPrime],
      IsRegularRingHom
        (algebraMap (Localization.AtPrime p)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p)))

end

end
