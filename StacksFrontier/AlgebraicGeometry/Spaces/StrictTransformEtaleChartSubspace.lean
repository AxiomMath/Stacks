module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupStrictTransformSpaceEtale

/-!
# The strict transform of an étale chart

Let `S` be a scheme, let `𝔅` be an algebraic space over `S`, let `Z ⊆ 𝔅` be a closed subspace
and let `b : 𝔅' ⟶ 𝔅` be the blowup of `𝔅` in `Z`.  Let `f : X ⟶ 𝔅` be an algebraic space over
`𝔅` and consider a commutative square

```
U ⟶ X
↓     ↓
𝒱 ⟶ 𝔅
```

with étale horizontal arrows, and let `v' : 𝒱' ⟶ 𝒱` be the blowup of `𝒱` in `Z ×_𝔅 𝒱`.
Part (2) of Stacks 0863 says that the strict transform `U'` of `U` relative to `v'` is
`X' ×_X U`, where `X'` is the strict transform of `X` relative to `b`, for blowups characterised
by the universal property of Stacks 085U.

## Main results

* `AlgebraicGeometry.Space.exists_strictTransformSubfunctor_eq_preimage`: **Stacks 0863,
  part (2)**.

## Implementation notes

The source takes `U` and `𝒱` to be schemes; here they are arbitrary algebraic spaces, which
contains the source's case.

The proof is the source's, through the ideal of sections supported on the exceptional
preimage.  The étale comparison of those ideals gives `U' = can⁻¹(X')` once `X'` is cut out by
its ideal, and that holds because the exceptional divisor `b⁻¹(Z)` is an effective Cartier
divisor (one half of the universal property of Stacks 085U): its inverse image in `X ×_𝔅 𝔅'` is
then locally principal, its complement has affine inclusion, and the ideal of supported sections
is quasi-coherent by Stacks 0859.  The two steps are
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isEtale` and
`AlgebraicGeometry.Space.strictTransform_exists_of_isEffectiveCartierDivisor`.

The equality `U' = X' ×_X U` is stated as an equality of subfunctors of `U ×_𝒱 𝒱'`, the inverse
image of `X'` along the canonical étale morphism `can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` of part (1),
together with the cartesian square over `u : U ⟶ X` exhibiting `U ×_𝒱 𝒱'` as
`(X ×_𝔅 𝔅') ×_X U`; in that square the inverse image along `can` is the base change along `u`.

## References

* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0863, part (2).**  Let `b : 𝔅' ⟶ 𝔅` be the blowup of an algebraic space `𝔅` in a
closed subspace `Z`, let `f : X ⟶ 𝔅` be an algebraic space over `𝔅`, let `u : U ⟶ X` and
`v : 𝒱 ⟶ 𝔅` be étale with `u ≫ f = w ≫ v`, and let `v' : 𝒱' ⟶ 𝒱` be the blowup of `𝒱` in
`Z ×_𝔅 𝒱`.  Then the strict transform `U'` of `U` relative to `v'` equals `X' ×_X U`, where
`X'` is the strict transform of `X` relative to `b`.

Precisely: there are `m : 𝒱' ⟶ 𝔅'` exhibiting `𝒱' = 𝒱 ×_𝔅 𝔅'` and an étale
`can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` over `u` and over `m`, sitting in a cartesian square over `u` that
exhibits `U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`, and `U'` is the inverse image of `X'` along `can`. -/
theorem exists_strictTransformSubfunctor_eq_preimage
    {Bl X Vv U B' V' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS Bl.1} {b : B' ⟶ Bl} (hb : IsBlowupAlong B S hS Z b)
    {f : X ⟶ Bl} {v : Vv ⟶ Bl} (hv : IsEtale B S hS v.hom)
    {u : U ⟶ X} (hu : IsEtale B S hS u.hom) {w : U ⟶ Vv} (hcomm : u ≫ f = w ≫ v)
    {v' : V' ⟶ Vv} (hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z) v') :
    ∃ (m : V' ⟶ B') (can : strictTransformPullback B S hS w v' ⟶
        strictTransformPullback B S hS f b),
      IsPullback v' m v b ∧ IsEtale B S hS can.hom ∧
        can ≫ strictTransformPullbackToSource B S hS f b =
          strictTransformPullbackToSource B S hS w v' ≫ u ∧
        can ≫ strictTransformPullbackToBlowUp B S hS f b =
          strictTransformPullbackToBlowUp B S hS w v' ≫ m ∧
        IsPullback can (strictTransformPullbackToSource B S hS w v')
          (strictTransformPullbackToSource B S hS f b) u ∧
        strictTransformSubfunctor B S hS w v'
            (preimageClosedSubspace v' (preimageClosedSubspace v Z)).1 =
          (strictTransformSubfunctor B S hS f b
            (preimageClosedSubspace b Z).1).preimage can.hom :=
  exists_strictTransform_eq_preimage_of_isEtale B S hS hb hv hu hcomm hv'
    (strictTransform_exists_of_isEffectiveCartierDivisor B S hS f b
      (preimageClosedSubspace b Z) hb.isPullbackDefined)

end AlgebraicGeometry.Space

end
