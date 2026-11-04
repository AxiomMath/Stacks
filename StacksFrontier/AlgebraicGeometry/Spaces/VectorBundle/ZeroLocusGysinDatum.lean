module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.Projection
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.ZeroLocusCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeOfCanonicalSection

/-!
# The zero section of a line bundle as the vanishing locus of a section

Let `W` be an algebraic space and `ℒ` an invertible `𝒪_W`-module, with line bundle
`p : L = \underline{Spec}_W(Sym(ℒ)) ⟶ W` and zero section `o : W ⟶ L`. The image `o(W) ⊆ L` is an
effective Cartier divisor, so it carries its invertible sheaf `𝒪_L(o(W))` and canonical section
`1_{o(W)}` (Stacks 0841), and the zero scheme of that section is `o(W)` again (Stacks 0847).
So `o(W)` is the vanishing locus `Z(s)` of a global section of an invertible module on `L`, which
is the shape of the datum `(ℒ, s, i : D ⟶ X)` of Stacks 0ER1: the refined Gysin map
`o^* : Z_{k+1}(L) ⟶ CH_k(o(W))` of the proof of Stacks 0ERH is the one of that triple.

## Main results

* `AlgebraicGeometry.Space.zeroScheme_canonicalSection_vectorBundleZeroLocus`: the zero scheme of
  the canonical section of `𝒪_L(o(W))` is `o(W)`.
* `AlgebraicGeometry.Space.vanishingLocus_canonicalSection_vectorBundleZeroLocus`: in the
  situation of Stacks 0EDT, with `W/B` good, `o(W)` is the vanishing locus of Stacks 0ER1 of the
  pair `(𝒪_L(o(W)), 1_{o(W)})` on the good space `L/B`.
* `AlgebraicGeometry.Space.isInvertibleSheaf_associatedInvertibleSheaf_vectorBundleZeroLocus`:
  the module of that pair is invertible, as Stacks 0ER1 requires.
* `AlgebraicGeometry.Space.isGood_vectorBundleZeroLocus`: the vanishing locus `o(W)` is good over
  the base.

## Main definitions

* `AlgebraicGeometry.Space.vectorBundleZeroLocusGysinDatum`: the closed immersion `o(W) ⟶ L` as a
  vanishing locus of a good algebraic space over the base.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ERH](https://stacks.math.columbia.edu/tag/0ERH)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 1]

/-- **The zero section of a line bundle is the zero scheme of the canonical section of its
invertible sheaf**: `Z(1_{o(W)}) = o(W)` in the line bundle `L`, by Stacks 0847 (2) for the
effective Cartier divisor `o(W) ⊆ L`. -/
theorem zeroScheme_canonicalSection_vectorBundleZeroLocus :
    zeroScheme B S hS (vectorBundle B S hS W F).obj.left
        (associatedInvertibleSheaf B S hS _ (vectorBundleZeroLocus B S hS W F)
          (isEffectiveCartierDivisor_vectorBundleZeroLocus B S hS W F))
        (canonicalSection B S hS _ (vectorBundleZeroLocus B S hS W F)
          (isEffectiveCartierDivisor_vectorBundleZeroLocus B S hS W F)) =
      vectorBundleZeroLocus B S hS W F :=
  zeroScheme_canonicalSection_eq B S hS _ _ _

end General

section Situation

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
  (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 1]
  (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- **The zero section of a line bundle is a vanishing locus in the sense of Stacks 0ER1.** In
the situation of Stacks 0EDT, with `W/B` good, the vanishing locus of the canonical section of
`𝒪_L(o(W))` on the good space `L/B` is `o(W)`. -/
theorem vanishingLocus_canonicalSection_vectorBundleZeroLocus :
    vanishingLocus D _ (isGood_vectorBundle D W F sW hW)
        (associatedInvertibleSheaf D.site D.base D.base_mem _
          (vectorBundleZeroLocus D.site D.base D.base_mem W F)
          (isEffectiveCartierDivisor_vectorBundleZeroLocus D.site D.base D.base_mem W F))
        (canonicalSection D.site D.base D.base_mem _
          (vectorBundleZeroLocus D.site D.base D.base_mem W F)
          (isEffectiveCartierDivisor_vectorBundleZeroLocus D.site D.base D.base_mem W F)) =
      vectorBundleZeroLocus D.site D.base D.base_mem W F :=
  zeroScheme_canonicalSection_vectorBundleZeroLocus D.site D.base D.base_mem W F

/-- **The module of the pair is invertible**, as Stacks 0ER1 requires of `ℒ`: it is the
invertible sheaf `𝒪_L(o(W))` of the effective Cartier divisor `o(W)` (Stacks 0841). -/
theorem isInvertibleSheaf_associatedInvertibleSheaf_vectorBundleZeroLocus :
    IsInvertibleSheaf D _ (isGood_vectorBundle D W F sW hW)
      (associatedInvertibleSheaf D.site D.base D.base_mem _
        (vectorBundleZeroLocus D.site D.base D.base_mem W F)
        (isEffectiveCartierDivisor_vectorBundleZeroLocus D.site D.base D.base_mem W F)) :=
  associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem _ _ _

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 1] in
include hW in
/-- **The zero locus of a vector bundle on a good space is good over the base**: it is a closed
subspace of the good space `E/B`. -/
theorem isGood_vectorBundleZeroLocus :
    D.IsGood ((vectorBundleZeroLocus D.site D.base D.base_mem W F).1.ι ≫
      (vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW) :=
  isGood_closedSubspace D _ (isGood_vectorBundle D W F sW hW) _

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 1] in
include hW in
/-- **The zero locus `o(W) ⊆ E` as a vanishing locus of the good space `E/B`**: the closed
immersion `o(W) ⟶ E`, its source being good over the base. In rank one it is the vanishing locus
of the canonical section of `𝒪_E(o(W))`, by
`AlgebraicGeometry.Space.vanishingLocus_canonicalSection_vectorBundleZeroLocus`. -/
def vectorBundleZeroLocusGysinDatum :
    GysinDatum D ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW) where
  locus := (vectorBundleZeroLocus D.site D.base D.base_mem W F).1.toFunctor
  ι := (vectorBundleZeroLocus D.site D.base D.base_mem W F).1.ι
  isClosedImmersion := (vectorBundleZeroLocus D.site D.base D.base_mem W F).2.2
  isGood := isGood_vectorBundleZeroLocus D W F sW hW

end Situation

end AlgebraicGeometry.Space

end
