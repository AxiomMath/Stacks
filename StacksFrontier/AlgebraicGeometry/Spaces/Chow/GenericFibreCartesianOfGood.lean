module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreResidueFieldCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisorFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteriaRepresentable03ZQ

/-!
# The generic fibre of a finite dominant morphism of integral good algebraic spaces

In Situation 0EDT let `X/B` and `Y/B` be good and integral, and let `p : X ⟶ Y` be a finite
morphism over `B` carrying the generic point of `X` to the generic point of `Y`. This file
proves that the square

```
Spec R(X) ⟶ X
    ↓         ↓ p
Spec R(Y) ⟶ Y
```

is cartesian: **the generic fibre of `p` is `Spec R(X)`**.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism_genericPoint`: the displayed
  square is a fibre product square, with the horizontal morphism of the site produced rather
  than assumed.

## Implementation notes

Nothing new is proved here; the content is that every hypothesis of
`AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreResidueFieldCartesian` is *discharged*
from the hypotheses of Stacks 0EQ4, so that the square is available with no side condition on
the fibre or on the local ring of the target:

* relative representability of `p` is `AlgebraicGeometry.Space.relativelyRepresentable_of_isFinite`
  (Stacks 03ZQ) applied to the two sheaf conditions of `IsAlgebraicSpace`;
* reducedness of `X` and of `Y` is the first conjunct of `IsIntegralSpace` (Stacks 0AD4), and
  decency its second;
* the local ring at the image point has dimension zero by
  `AlgebraicGeometry.Space.localRingDimension_genericPoint_eq_zero`, the image point being the
  generic point of the integral `Y`;
* the generic point of `X` is the *only* preimage of the generic point of `Y`, by
  `AlgebraicGeometry.Space.eq_genericPoint_of_pointsMap_eq_genericPoint`: a finite morphism is
  locally quasi-finite (`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isFinite`), so the
  δ-invariant of a point of `X` is that of its image, and a dimension function is strictly
  decreasing along a nontrivial specialization.

The finiteness of `p` is a hypothesis, not a consequence: this repository has no
"proper and locally quasi-finite implies finite" for algebraic spaces. In the source's proof of
Stacks 0EQ4 finiteness of `p` is arranged by Stacks 0AD2, which is also how a consumer should
supply it.

### Corrections to notes elsewhere in the tree

Three implementation notes in the tree describe as missing something that is now proved. They
are left in place — the files holding them carry other material — and the corrections are
recorded here.

1. `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor` says of the
   ring `D` of the generic fibre that "**what is missing is that `D` is a field** ... That is
   the statement anyone continuing this tag should build first". It is proved, as
   `AlgebraicGeometry.Space.isField_appTop_pullback_residueFieldMorphism` of
   `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreIsField`.
2. The implementation notes of
   `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreIsField` say that the transport of
   the Stacks 0EMW uniqueness clause across `AlgebraicGeometry.Scheme.isoSpec` of the fibre "is
   the one thing still owed". It is proved, as
   `AlgebraicGeometry.Space.isIso_residueFibreComparison` of
   `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreResidueFieldCartesian`, which obtains
   the transport from `AlgebraicGeometry.Space.exists_fieldValuedPoint_comp_eq` of
   `StacksFrontier.AlgebraicGeometry.Spaces.StratumSiteDatum`.
3. `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreChartReduced` says that "what is
   still owed before `AlgebraicGeometry.Space.isPullback_residueFieldMorphism_iff_isIso` gives
   the cartesian square ... is that the comparison morphism is an isomorphism". Same correction
   as 2.

### What Stacks 0EQ4 still needs after this

The cartesian square is the geometric input of the pushout chain of
`StacksFrontier.AlgebraicGeometry.Morphisms.Affine.PullbackGenericFibrePushout`, whose conclusion
`Algebra.IsPushout R(Y) R(V) R(X) T` is the hypothesis of
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_localization`. Deriving that hypothesis
from this square — pasting the square with an affine étale chart `V ⟶ Y` through the generic
point of a prime divisor, so that the generic fibre of `X ×_Y V ⟶ V` becomes
`Spec (R(V) ⊗_{R(Y)} R(X))` — is not done here and is the next step of the tag.

## References

* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The generic fibre of a finite dominant morphism of integral good algebraic spaces is
`Spec R(X)`.** In Situation 0EDT let `X/B` and `Y/B` be good and integral, let
`p : X ⟶ Y` be a morphism over `B` which is finite and carries the generic point of `X` to the
generic point of `Y`, and let `dX` be a dimension function on `|X|` inducing the δ-invariant.
Then

```
Spec R(X) ⟶ X
    ↓         ↓ p
Spec R(Y) ⟶ Y
```

is a fibre product square, the vertical morphisms being the canonical field-valued points of
Stacks 0EMW at the two generic points — where the residue field is the function field, by
Stacks 0END and `AlgebraicGeometry.Space.rationalFunctionsRingEquiv`. The morphism
`Spec R(X) ⟶ Spec R(Y)` of the site is produced, not assumed.

This is `AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism` with all of its
hypotheses discharged; see the implementation notes of this module for each of them. -/
theorem exists_isPullback_residueFieldMorphism_genericPoint
    (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (dX : TopologicalSpace.DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsFinite D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY) :
    ∃ g : (residueFieldRepresentative D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX)).1.siteObject
          D.site D.base D.base_mem X ⟶
        (residueFieldRepresentative D.site D.base D.base_mem Y hintY.2.1
          (genericPoint D.site D.base D.base_mem hY.1 hintY)).1.siteObject
          D.site D.base D.base_mem Y,
      IsPullback
        (residueFieldMorphism D.site D.base D.base_mem X hintX.2.1
          (genericPoint D.site D.base D.base_mem hX.1 hintX))
        (yoneda.map g) p
        (residueFieldMorphism D.site D.base D.base_mem Y hintY.2.1
          (genericPoint D.site D.base D.base_mem hY.1 hintY)) := by
  have hqf : IsLocallyQuasiFinite D.site D.base D.base_mem p :=
    isLocallyQuasiFinite_of_isFinite D.site D.base D.base_mem hX.1 hY.1 hp
  rw [← hgen]
  refine exists_isPullback_residueFieldMorphism D.site D.base D.base_mem
    (relativelyRepresentable_of_isFinite D.site D.base D.base_mem hX.1.isSheaf hY.1.isSheaf hp)
    hp hX.1 hY.1 hintX.2.1 hintY.2.1 hintX.1 hintY.1 _ ?_ ?_
  · rw [hgen]
    exact localRingDimension_genericPoint_eq_zero D.site D.base D.base_mem hY.1 hintY
  · intro y y' hy hy'
    rw [hgen] at hy hy'
    rw [eq_genericPoint_of_pointsMap_eq_genericPoint D sX hX sY hY hintX hintY dX hdX hpB hqf
        hgen hy,
      eq_genericPoint_of_pointsMap_eq_genericPoint D sX hX sY hY hintX hintY dX hdX hpB hqf
        hgen hy']

end AlgebraicGeometry.Space

end
