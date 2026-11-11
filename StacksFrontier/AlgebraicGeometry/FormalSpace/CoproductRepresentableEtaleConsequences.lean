module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductRepresentableEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypesChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaReduction

/-!
# Consequences of the coproduct criterion for representable étale morphisms

Let `S` be a scheme contained in a big fppf site `B`.
`AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale` proves the assertion
`AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`: a morphism out of a finite
coproduct of fppf sheaves is representable by algebraic spaces and étale as soon as its
restriction to every summand is. The declarations below are the forms of the quasi-compactness
criterion of Stacks 0AJ9, of the implication (2) ⟹ (1) of Stacks 0AKX for countable indexing and
of clause (1) of Stacks 0GBB in which this assertion is supplied rather than assumed.

## Main results

* `tfae_isQuasiCompactSpace_unconditional`: for a formal algebraic space `X` with a reduction
  `Xred`, quasi-compactness of `Xred`, a finite atlas of `X` and a representable étale surjection
  onto `X` from an affine formal algebraic space are equivalent (Stacks 0AJ9).
* `isCountablyIndexed_of_isRepresentableEtale_unconditional` and
  `isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas_unconditional`: an affine
  formal algebraic space representable étale over a locally countably indexed one is countably
  indexed (Stacks 0AKX, (2) ⟹ (1)).
* `isLocallyCountablyIndexed_pullback_of_atlasChartLocality_unconditional`: a fibre product of
  locally countably indexed formal algebraic spaces is locally countably indexed (Stacks 0GBB,
  clause (1)).

## Hypotheses

Among their hypotheses, the declarations on countable indexing take `h0AJ2`, **Stacks 0AJ2** —
`AlgebraicGeometry.FormalSpace.HasFormalAffineChartPullbacks`.

`AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace_unconditional` takes none beyond the
reduction.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Consequences of the coproduct criterion -/

/-- A sheaf with a finite formal atlas is a quasi-compact formal algebraic space over `S`: the
implication (2) ⇒ (3) of Stacks 0AJ9. -/
theorem isQuasiCompactSpace_of_hasFiniteFormalAtlas {X : FppfSheaf B S hS}
    (h : HasFiniteFormalAtlas B S hS X) : IsQuasiCompactSpace B S hS X :=
  HasFiniteFormalAtlas.isQuasiCompactSpace B S hS (coproductsRepresentableEtale B S hS) h

/-- Let `X` be a formal algebraic space over `S` and let `i : Xred ⟶ X` be a reduction of `X`.
Then quasi-compactness of `Xred`, the existence of an atlas as in Definition 0AIM indexed by a
finite type, and the existence of a morphism from an affine formal algebraic space which is
representable by algebraic spaces, étale and a surjection of sheaves are equivalent.

A reduction of `X` exists by
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`. -/
@[stacks 0AJ9 "the equivalence of the three conditions, for every reduction i : Xred ⟶ X of X; \
a reduction exists by Stacks 0AIN (exists_isReduction_of_isFormalAlgebraicSpace)"]
theorem tfae_isQuasiCompactSpace_unconditional
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hX : IsFormalAlgebraicSpace B S hS X) (hi : IsReduction B S hS X Xred i) :
    [Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj,
      HasFiniteFormalAtlas B S hS X,
      IsQuasiCompactSpace B S hS X].TFAE :=
  tfae_isQuasiCompactSpace_of_isReduction B S hS (coproductsRepresentableEtale B S hS) hX hi

/-- **The refinement step in the proof of Stacks 0AKX.** Given Stacks 0AJ2 (`h0AJ2`), the
descent of `P` along representable étale morphisms of affine formal algebraic spaces (`h0AKQ`)
and the stability of `P` under finite disjoint unions (`hPsigma`), the property `P` satisfies
`AlgebraicGeometry.FormalSpace.HasAffineEtaleRefinementWithProperty`. -/
theorem hasAffineEtaleRefinementWithProperty_of_descends_unconditional
    (P : FppfSheaf B S hS → Prop)
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    (h0AKQ : ∀ {U V : FppfSheaf B S hS} (f : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS f → P V → P U)
    (hPsigma : PropertyOfFiniteDisjointUnions B S hS P) :
    HasAffineEtaleRefinementWithProperty B S hS P :=
  hasAffineEtaleRefinementWithProperty_of_descends B S hS P h0AJ2
    (coproductsRepresentableEtale B S hS) h0AKQ hPsigma

/-- **The refinement step in the proof of Stacks 0AKX for the countably indexed property.**
Given Stacks 0AJ2 (`h0AJ2`), being countably indexed satisfies
`AlgebraicGeometry.FormalSpace.HasAffineEtaleRefinementWithProperty`. -/
theorem hasAffineEtaleRefinementWithProperty_isCountablyIndexed_unconditional
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS) :
    HasAffineEtaleRefinementWithProperty B S hS (IsCountablyIndexed B S hS) :=
  hasAffineEtaleRefinementWithProperty_isCountablyIndexed B S hS h0AJ2
    (coproductsRepresentableEtale B S hS)

/-- **The implication (2) ⟹ (1) of Stacks 0AKX for countable indexing.** Let `Z` be a locally
countably indexed formal algebraic space over `S`. Then every affine formal algebraic space
representable étale over `Z` is countably indexed, given Stacks 0AJ2 as `h0AJ2`. -/
theorem isCountablyIndexed_of_isRepresentableEtale_unconditional
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    {Z U : FppfSheaf B S hS} (a : U ⟶ Z)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (ha : IsRepresentableEtale B S hS a) :
    IsCountablyIndexed B S hS U :=
  isCountablyIndexed_of_isRepresentableEtale B S hS h0AJ2
    (coproductsRepresentableEtale B S hS) a hZ hU ha

/-- **The implication (2) ⟹ (1) of Stacks 0AKX for countable indexing, from the atlas alone.**
If an fppf sheaf `T` on the big fppf site of `S` admits an atlas as in Definition 0AIM by
countably indexed affine formal algebraic spaces, then every affine formal algebraic space
representable étale over `T` is countably indexed. -/
theorem isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas_unconditional
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS) :
    ∀ T : FppfSheaf B S hS,
      HasAffineEtaleAtlasWithProperty B S hS T (IsCountablyIndexed B S hS) →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ T), IsAffineFormalAlgebraicSpace B S hS U →
        IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U :=
  isCountablyIndexed_of_isRepresentableEtale_of_hasAffineEtaleAtlas B S hS h0AJ2
    (coproductsRepresentableEtale B S hS)

/-- **Clause (1) of Stacks 0GBB.** A fibre product of locally countably indexed formal
algebraic spaces over `S` is locally countably indexed. -/
theorem isLocallyCountablyIndexed_pullback_of_atlasChartLocality_unconditional
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (h0AJ2 : HasFormalAffineChartPullbacks B S hS)
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS (IsCountablyIndexed B S hS))
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback f g)) :
    IsLocallyCountablyIndexed B S hS (pullback f g) :=
  isLocallyCountablyIndexed_pullback_of_atlasChartLocality B S hS f g hX hY hZ
    h0AJ2 (coproductsRepresentableEtale B S hS) h0AJ3f h0AJ3g hPaff hset

end AlgebraicGeometry.FormalSpace

end
