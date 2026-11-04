module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionRatio
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.ClassGroup

/-!
# The Weil divisor class of an invertible sheaf

Let `X` be a locally Noetherian integral scheme and `L` an invertible sheaf of `𝒪_X`-modules.
Every regular meromorphic section `s` of `L` has a Weil divisor `div_L(s)`, and two such
sections differ by a principal divisor, so the class of `div_L(s)` in the Weil divisor class
group `Cl(X)` depends only on `L`. Such a section exists, so the class is defined for every
invertible sheaf.

## Main definitions

* `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf`: the class of `div_L(s)` in `Cl(X)`,
  for a choice of regular meromorphic section `s` of `L`.

## Main results

* `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_eq`: every regular meromorphic section of
  `L` has the same divisor class, namely that one.

## References

* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 0BE4](https://stacks.math.columbia.edu/tag/0BE4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The Weil divisor class of an invertible sheaf on a locally Noetherian integral scheme: the
class in `Cl(X)` of the Weil divisor of a chosen regular meromorphic section of `L`. -/
@[stacks 0BE6 "part (2): divisor class of an invertible sheaf"]
def weilDivisorClassOfInvertibleSheaf : weilDivisorClassGroup X :=
  ((weilDivisorOfMeromorphicSection X L
      (exists_isRegularMeromorphicSection_of_isIntegral X L).choose
      (exists_isRegularMeromorphicSection_of_isIntegral X L).choose_spec :
    WeilDivisor X) : weilDivisorClassGroup X)

/-- The Weil divisor of any regular meromorphic section of an invertible sheaf `L` has class
`AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf X L` in `Cl(X)`. -/
@[stacks 0BE6 "part (2): independence of the meromorphic section"]
theorem weilDivisorClassOfInvertibleSheaf_eq (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    weilDivisorClassOfInvertibleSheaf X L =
      ((weilDivisorOfMeromorphicSection X L s hs : WeilDivisor X) :
        weilDivisorClassGroup X) := by
  set s' := (exists_isRegularMeromorphicSection_of_isIntegral X L).choose
  set hs' := (exists_isRegularMeromorphicSection_of_isIntegral X L).choose_spec
  show ((weilDivisorOfMeromorphicSection X L s' hs' : WeilDivisor X) :
    weilDivisorClassGroup X) = _
  refine QuotientAddGroup.eq.mpr ((mem_principalWeilDivisors_iff X _).2
    ⟨meromorphicSectionRatio X L s s' hs hs', ?_⟩)
  rw [meromorphicWeilDivisor_eq_add_principalDivisor X L s s' hs hs', neg_add_cancel_left]

end AlgebraicGeometry

end
