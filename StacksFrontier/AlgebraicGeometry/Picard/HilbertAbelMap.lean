module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClassPullback
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorDegreeSum
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyDivisor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Abel map on the values of the Hilbert functor of a smooth relative curve

Let `X ⟶ S` be smooth of relative dimension one and let `T` be a scheme over `S`. A degree-`d`
Hilbert family `Z` in `X` over `T` is a relative effective Cartier divisor on `X_T = X ×_S T`
(Tag 0B9C), so it has an invertible sheaf `𝒪_{X_T}(Z)` and hence a class in the Picard group of
`X_T`: this is the *Abel map* `γ_d` of a degree-`d` family. It is compatible with base change: for
`g : T' ⟶ T` the class of the base-changed family `Z_{T'}` is the pullback along `X_{T'} ⟶ X_T`
of the class of `Z`.

## Main definitions

* `Stacks.Hilbert.abelClass` — the class in `Pic(X_T)` of the invertible sheaf of a degree-`d`
  Hilbert family.
* `Stacks.Hilbert.HilbertFamily.add` — the sum of a degree-`d` and a degree-`e` family, a
  degree-`(d + e)` family.

## Main results

* `Stacks.Hilbert.abelClass_baseChange` — the Abel map commutes with base change.
* `Stacks.Hilbert.abelClass_add` — the Abel map is additive, carrying the sum of a degree-`d`
  and a degree-`e` family to the sum of their classes.

## References

* [Stacks Project, Tag 0B94](https://stacks.math.columbia.edu/tag/0B94)
* [Stacks Project, Tag 0B9C](https://stacks.math.columbia.edu/tag/0B9C)
* [Stacks Project, Tag 0B9E](https://stacks.math.columbia.edu/tag/0B9E)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}} {X : Over S} [SmoothOfRelativeDimension 1 X.hom] {d e : ℕ}

/-- The base change `X_T ⟶ T` of a scheme smooth of relative dimension one over `S` is again
smooth of relative dimension one. -/
@[sga "6 X 7.13.3" "special case"]
theorem smoothOfRelativeDimension_pullback_hom (X T : Over S)
    [SmoothOfRelativeDimension 1 X.hom] :
    SmoothOfRelativeDimension 1 ((Over.pullback T.hom).obj X).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback X.hom T.hom) inferInstance

/-- The ideal sheaf of a degree-`d` Hilbert family on a smooth relative curve is an effective
Cartier divisor on `X_T`. -/
instance HilbertFamily.isEffectiveCartierDivisor {T : Over S} (Z : HilbertFamily X T d) :
    Stacks.Divisors.IsEffectiveCartierDivisor Z.ideal :=
  Z.isRelativeEffectiveCartierDivisor.1

/-- The Abel map `γ_d` on the values of the Hilbert functor: the class in `Pic(X_T)` of the
invertible sheaf `𝒪_{X_T}(Z)` of a degree-`d` Hilbert family `Z`, a relative effective Cartier
divisor on `X_T`. -/
def abelClass {T : Over S} (Z : HilbertFamily X T d) :
    Stacks.Picard.ofScheme ((Over.pullback T.hom).obj X).left :=
  Stacks.Divisors.picardClass Z.ideal

/-- For `g : T' ⟶ T` over `S`, the class of the base-changed family `Z_{T'}` is the pullback of
the class of `Z` along the comparison map `X_{T'} ⟶ X_T`. -/
theorem abelClass_baseChange {T' T : Over S} (g : T' ⟶ T) (Z : HilbertFamily X T d) :
    Stacks.Picard.schemePullbackClass (familyBaseChangeMap X g) (abelClass Z) =
      abelClass (baseChange X g Z) :=
  have : Stacks.Divisors.IsPullbackDefined (familyBaseChangeMap X g) Z.ideal :=
    (baseChange X g Z).isRelativeEffectiveCartierDivisor.1
  Stacks.Divisors.schemePullbackClass_picardClass (familyBaseChangeMap X g) Z.ideal

/-- The sum of a degree-`d` and a degree-`e` Hilbert family, a degree-`(d + e)` family: the
closed subscheme cut out by the product of their ideal sheaves. -/
def HilbertFamily.add {T : Over S} (Z : HilbertFamily X T d) (W : HilbertFamily X T e) :
    HilbertFamily X T (d + e) where
  ideal := Z.ideal * W.ideal
  isFiniteLocallyFreeOfRank :=
    haveI := smoothOfRelativeDimension_pullback_hom X T
    haveI := Z.isFiniteLocallyFreeOfRank
    haveI := W.isFiniteLocallyFreeOfRank
    isFiniteLocallyFreeOfRank_mul ((Over.pullback T.hom).obj X).hom Z.ideal W.ideal d e

/-- The ideal sheaf of a sum of Hilbert families is the product of their ideal sheaves. -/
theorem HilbertFamily.add_ideal {T : Over S} (Z : HilbertFamily X T d) (W : HilbertFamily X T e) :
    (Z.add W).ideal = Z.ideal * W.ideal :=
  rfl

/-- The class of the sum of a degree-`d` and a degree-`e` family is the sum of their classes. -/
theorem abelClass_add {T : Over S} (Z : HilbertFamily X T d) (W : HilbertFamily X T e) :
    abelClass (Z.add W) = abelClass Z + abelClass W :=
  Stacks.Divisors.picardClass_mul Z.ideal W.ideal

end Stacks.Hilbert

end
