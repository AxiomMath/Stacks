module

public import Mathlib.Algebra.AlgebraicCard
public import StacksFrontier.AlgebraicGeometry.Size.SiteAlgebraClosure
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Algebraic extensions stay below the cutoff of a big site

An algebraic extension `A ⊆ A'` of domains has `#A' ≤ max #A ℵ₀` (Stacks 09GK), so at an
uncountable cutoff `κ` the spectrum of `A'` is below `κ` as soon as that of `A` is. In
particular a big fppf site containing the spectrum of a domain `A` contains the spectrum of
every `A`-subalgebra of a finite extension of the fraction field of `A`. This is how the finite
extensions of discrete valuation rings produced by stable reduction (Stacks 0E98) remain in the
site: no hypothesis on the site is needed.

## Main results

* `Cardinal.mk_le_max_of_isAlgebraic`: `#A' ≤ max #A ℵ₀` for an algebraic extension of domains.
* `AlgebraicGeometry.schemeSizeBelow_spec_of_isAlgebraic`: the spectrum of an algebraic
  extension of a domain of the site is in the site.
* `AlgebraicGeometry.schemeSizeBelow_spec_subalgebra_of_isAlgebraic`: the same for every
  subalgebra of an algebraic extension.
* `AlgebraicGeometry.schemeSizeBelow_spec_subalgebra_of_fractionRing`: the spectrum of every
  `A`-subalgebra of an algebraic (for instance finite) extension of the fraction field of a
  domain `A` of the site is in the site.

## References

* [Stacks Project, Tag 09GK](https://stacks.math.columbia.edu/tag/09GK)
* [Stacks Project, Tag 0E98](https://stacks.math.columbia.edu/tag/0E98)
-/

@[expose] public section

open Cardinal

universe u

namespace Cardinal

/-- An algebraic extension of domains is no larger than the base and `ℵ₀`. -/
theorem mk_le_max_of_isAlgebraic (A A' : Type u) [CommRing A] [IsDomain A] [CommRing A']
    [IsDomain A'] [Algebra A A'] [Module.IsTorsionFree A A'] [Algebra.IsAlgebraic A A'] :
    #A' ≤ max #A ℵ₀ :=
  calc #A' = #{ x : A' // IsAlgebraic A x } :=
        (mk_congr (Equiv.subtypeUnivEquiv fun x => Algebra.IsAlgebraic.isAlgebraic x)).symm
    _ ≤ max #A ℵ₀ := Algebraic.cardinalMk_le_max A A'

end Cardinal

namespace AlgebraicGeometry

/-- The spectrum of an algebraic extension of a domain whose spectrum is below an uncountable
cutoff is below that cutoff. -/
theorem schemeSizeBelow_spec_of_isAlgebraic {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (A A' : Type u)
    [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] [Algebra A A']
    [Module.IsTorsionFree A A'] [Algebra.IsAlgebraic A A']
    (hA : schemeSizeBelow κ (Spec (CommRingCat.of A))) :
    schemeSizeBelow κ (Spec (CommRingCat.of A')) :=
  (schemeSizeBelow_spec_iff hκ A').2 ((Cardinal.mk_le_max_of_isAlgebraic A A').trans_lt
    (max_lt ((schemeSizeBelow_spec_iff hκ A).1 hA) hκ))

/-- The spectrum of a subalgebra of an algebraic extension of a domain whose spectrum is below
an uncountable cutoff is below that cutoff. -/
theorem schemeSizeBelow_spec_subalgebra_of_isAlgebraic {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (A L : Type u) [CommRing A] [IsDomain A] [CommRing L] [IsDomain L] [Algebra A L]
    [Module.IsTorsionFree A L] [Algebra.IsAlgebraic A L] (A' : Subalgebra A L)
    (hA : schemeSizeBelow κ (Spec (CommRingCat.of A))) :
    schemeSizeBelow κ (Spec (CommRingCat.of A')) :=
  (schemeSizeBelow_spec_iff hκ A').2 ((mk_subtype_le _).trans_lt
    ((schemeSizeBelow_spec_iff hκ L).1 (schemeSizeBelow_spec_of_isAlgebraic hκ A L hA)))

/-- **Finite extensions of a domain of the site stay in the site.** Let `A` be a domain whose
spectrum is below an uncountable cutoff, `K` its fraction field and `L` an algebraic (for
instance finite) field extension of `K`. Then the spectrum of every `A`-subalgebra of `L` is
below the cutoff; e.g. a discrete valuation ring of `L` dominating a discrete valuation ring
`A`. -/
theorem schemeSizeBelow_spec_subalgebra_of_fractionRing {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (A K L : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    (A' : Subalgebra A L) (hA : schemeSizeBelow κ (Spec (CommRingCat.of A))) :
    schemeSizeBelow κ (Spec (CommRingCat.of A')) :=
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have : Algebra.IsAlgebraic A L := .trans A K L
  schemeSizeBelow_spec_subalgebra_of_isAlgebraic hκ A L A' hA

/-- A big fppf site containing the spectrum of a domain `A` contains the spectrum of every
`A`-subalgebra of an algebraic extension of the fraction field of `A`. -/
theorem BigFppfSite.contains_spec_subalgebra_of_fractionRing (B : BigFppfSite.{u})
    (A K L : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    (A' : Subalgebra A L) (hA : B.Contains (Spec (CommRingCat.of A))) :
    B.Contains (Spec (CommRingCat.of A')) :=
  schemeSizeBelow_spec_subalgebra_of_fractionRing B.aleph0_lt_cutoff A K L A' hA

end AlgebraicGeometry

end
