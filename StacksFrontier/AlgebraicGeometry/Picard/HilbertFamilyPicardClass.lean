module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClassPullback
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints

/-!
# The Picard class of a Hilbert family on a smooth relative curve

Let `X` be smooth of relative dimension one over `S`. A degree-`d` Hilbert family `D` of `X` over
`T` is a relative effective Cartier divisor on `X ×_S T` ([Stacks, Tag 0B9D]), hence an effective
Cartier divisor, so its invertible sheaf `𝒪(D)` has a class in `Pic(X ×_S T)`; this class is
compatible with base change ([Stacks, Tag 0C4U]).

## Main definitions

* `Stacks.Hilbert.HilbertFamily.picardClass`: the class of `𝒪(D)` in `Pic(X_T)`.

## Main results

* `Stacks.Hilbert.HilbertFamily.isEffectiveCartierDivisor_ideal`: a degree-`d` Hilbert family on
  a smooth relative curve is an effective Cartier divisor.
* `Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass`: the Picard class of a Hilbert
  family is compatible with base change.

## References

* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Smoothness of relative dimension `n` of a morphism of schemes is smoothness of relative
dimension `n` of the structure morphism of the object of the slice category it presents. -/
instance smoothOfRelativeDimension_overMk_hom {S Y : Scheme.{u}} {g : Y ⟶ S} {n : ℕ}
    [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n (Over.mk g).hom :=
  inferInstanceAs (SmoothOfRelativeDimension n g)

end AlgebraicGeometry

namespace Stacks.Hilbert

/-- **A degree-`d` Hilbert family on a smooth relative curve is an effective Cartier
divisor.** -/
theorem HilbertFamily.isEffectiveCartierDivisor_ideal {S : Scheme.{u}} {X T : Over S}
    [SmoothOfRelativeDimension 1 X.hom] {d : ℕ} (D : HilbertFamily X T d) :
    Stacks.Divisors.IsEffectiveCartierDivisor D.ideal :=
  have : SmoothOfRelativeDimension 1 ((Over.pullback T.hom).obj X).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback X.hom T.hom) inferInstance
  have := D.isFiniteLocallyFreeOfRank
  have : Stacks.Morphisms.IsFiniteLocallyFree
      (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree
    ((Over.pullback T.hom).obj X).hom D.ideal).1

/-- **The Picard class of a degree-`d` Hilbert family**: the class of the invertible sheaf
`𝒪(D)` of the effective Cartier divisor `D` cuts out on `X ×_S T`. -/
def HilbertFamily.picardClass {S : Scheme.{u}} {X T : Over S}
    [SmoothOfRelativeDimension 1 X.hom] {d : ℕ} (D : HilbertFamily X T d) :
    Stacks.Picard.ofScheme ((Over.pullback T.hom).obj X).left :=
  have := D.isEffectiveCartierDivisor_ideal
  Stacks.Divisors.picardClass D.ideal

/-- The Picard class of a Hilbert family is the Picard class of its ideal sheaf, for any proof
that the latter is an effective Cartier divisor. -/
theorem HilbertFamily.picardClass_eq {S : Scheme.{u}} {X T : Over S}
    [SmoothOfRelativeDimension 1 X.hom] {d : ℕ} (D : HilbertFamily X T d)
    (h : Stacks.Divisors.IsEffectiveCartierDivisor D.ideal) :
    D.picardClass = @Stacks.Divisors.picardClass _ D.ideal h :=
  rfl

/-- **Restricting the Picard class of a Hilbert family along a base change gives the Picard class
of the restricted family.** -/
theorem HilbertFamily.schemePullbackClass_picardClass {S : Scheme.{u}} {X T T' : Over S}
    [SmoothOfRelativeDimension 1 X.hom] {d : ℕ} (D : HilbertFamily X T d)
    (D' : HilbertFamily X T' d)
    (g : ((Over.pullback T'.hom).obj X).left ⟶ ((Over.pullback T.hom).obj X).left)
    (h : D'.ideal = D.ideal.comap g) :
    Stacks.Picard.schemePullbackClass g D.picardClass = D'.picardClass := by
  have hD := D.isEffectiveCartierDivisor_ideal
  have hD' := D'.isEffectiveCartierDivisor_ideal
  have hpd : Stacks.Divisors.IsEffectiveCartierDivisor (D.ideal.comap g) := h ▸ hD'
  rw [D.picardClass_eq hD, D'.picardClass_eq hD']
  exact (@Stacks.Divisors.schemePullbackClass_picardClass _ _ g D.ideal hD hpd).trans
    (@Stacks.Divisors.picardClass_congr _ _ _ h.symm hpd hD')

end Stacks.Hilbert

end
