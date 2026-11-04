module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk

/-!
# An integral effective Cartier divisor is a prime divisor

On a locally Noetherian scheme an effective Cartier divisor whose subscheme is integral is a
prime divisor: Tag 0BCN gives its generic point a local ring of dimension one, which by Tag
02IZ is codimension one, the defining condition of `AlgebraicGeometry.PrimeDivisor`.

## Main results

* `AlgebraicGeometry.PrimeDivisor.ofEffectiveCartier`: the prime divisor carried by an integral
  effective Cartier divisor.
* `AlgebraicGeometry.isDiscreteValuationRing_ringStalk_genericPoint`: Tag 0AG9 in the
  `Stacks.SheafOfModules.SheafHomStalk.ringStalk` spelling of the stalk.

## Implementation notes

**No `@[stacks]` attribute.** Neither statement is an assertion of a tag: the first repackages
Tag 0BCN (2) and Tag 02IZ as a term of `AlgebraicGeometry.PrimeDivisor`, the second restates
`AlgebraicGeometry.isDiscreteValuationRing_stalk_genericPoint`, which carries Tag 0AG9, at a
reducible abbreviation of the same stalk.

The two stalk spellings `Stacks.SheafOfModules.SheafHomStalk.ringStalk X.sheaf x` and
`X.presheaf.stalk x` are definitionally equal, but a hypothesis stated in one is not found by
instance search for a goal stated in the other, so a file works in one spelling and bridges
once.

## References

* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0AG9](https://stacks.math.columbia.edu/tag/0AG9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData) [IsIntegral D.subscheme]

/-- **An integral effective Cartier divisor is a prime divisor.** Its subscheme is integral by
assumption, and the local ring at its generic point has dimension one by Tag 0BCN (2), which by
Tag 02IZ is codimension one. -/
def PrimeDivisor.ofEffectiveCartier (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    PrimeDivisor X where
  idealSheaf := D
  integral := inferInstance
  codimension_one :=
    (ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one _).mp
      (ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD _
        ⟨⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩,
          by simpa using genericPoint_spec (D.subscheme : Type u)⟩)

/-- The generic point of the prime divisor of an integral effective Cartier divisor is the
image in the ambient scheme of the generic point of its subscheme. -/
@[simp] theorem PrimeDivisor.genericPoint_ofEffectiveCartier
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    (PrimeDivisor.ofEffectiveCartier D hD).genericPoint =
      D.subschemeι (_root_.genericPoint (D.subscheme : Type u)) := rfl

/-- The generic point of the prime divisor of an integral effective Cartier divisor lies in the
support of that divisor. -/
theorem PrimeDivisor.genericPoint_ofEffectiveCartier_mem_support
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    (PrimeDivisor.ofEffectiveCartier D hD).genericPoint ∈ ((D.support : Closeds X) : Set X) := by
  rw [show ((D.support : Closeds X) : Set X) = Set.range D.subschemeι from
    (Scheme.IdealSheafData.range_subschemeι D).symm]
  exact Set.mem_range_self _

/-- **Tag 0AG9 in the `ringStalk` spelling.** The local ring of `X` at the generic point of an
integral effective Cartier divisor is a discrete valuation ring; in particular a domain. -/
theorem isDiscreteValuationRing_ringStalk_genericPoint
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    ∃ _ : IsDomain (ringStalk X.sheaf (D.subschemeι (_root_.genericPoint
        (D.subscheme : Type u)))),
      IsDiscreteValuationRing
        (ringStalk X.sheaf (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))) :=
  isDiscreteValuationRing_stalk_genericPoint D hD

end AlgebraicGeometry

end
