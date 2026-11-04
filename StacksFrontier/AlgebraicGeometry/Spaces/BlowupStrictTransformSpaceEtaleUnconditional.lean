module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupStrictTransformSpaceEtale

/-!
# Stacks 0863, parts (2) and (3), with no hypothesis beyond the source's

Let `S` be a scheme, let `𝔅` be an algebraic space over `S`, let `Z ⊆ 𝔅` be a closed subspace
and let `b : 𝔅' ⟶ 𝔅` be the blowup of `𝔅` in `Z`.  Let `f : X ⟶ 𝔅` be an algebraic space over
`𝔅` and consider a commutative square

```
U ⟶ X
↓     ↓
𝒱 ⟶ 𝔅
```

with étale horizontal arrows, and let `v' : 𝒱' ⟶ 𝒱` be the blowup of `𝒱` in the inverse image
`Z ×_𝔅 𝒱`.  Part (2) of Stacks 0863 says that the strict transform `U'` of `U` with respect to
`v'` is `X' ×_X U`, where `X'` is the strict transform of `X` with respect to `b`; part (3) says
that for an `𝒪_X`-module `F` the restriction of the strict transform `F'` to `U ×_𝒱 𝒱'` is the
strict transform of `F|_U` relative to `v'`.

Both are proved here for an arbitrary blowup, with no hypothesis beyond the source's, and
together in one statement so that a consumer of the tag gets the comparison morphism `can` and
both of its properties at once.

## Main results

* `AlgebraicGeometry.Space.exists_strictTransform_eq_preimage` is **Stacks 0863, part (2)**:
  being the blowup is the hypothesis `hb` in the sense of the universal property of Stacks 085U,
  and nothing further is assumed.
* `AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_strictTransformSheaf_iso` is
  **Stacks 0863, parts (2) and (3) together**, for the same `m` and the same `can`.

## Implementation notes

What the two statements of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupStrictTransformSpaceEtale.lean` leave over is the
existence of a closed subspace of `X ×_𝔅 𝔅'` cut out by the ideal of sections supported on the
exceptional preimage; `AlgebraicGeometry.Space.strictTransform` is the infimum of the closed
subspaces whose defining ideal is dominated by that ideal, and an infimum of a family is not
characterised by an ideal, so that existence is what makes the reading-off of part (2)
legitimate.  It is supplied here by
`AlgebraicGeometry.Space.strictTransform_exists_of_isEffectiveCartierDivisor` from the
exceptional divisor `b^{-1}Z` being an effective Cartier divisor on `𝔅'`, and *that* is one half
of the universal property of Stacks 085U — `AlgebraicGeometry.Space.IsBlowupAlong` is membership
in the category `𝒞` of that tag together with finality there, and membership is exactly
`AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined`.  So the blowup supplies its own
input and nothing is left over.

Accordingly the affineness hypothesis `haff` of
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isAffineHom` — the affineness
half of Stacks 07ZU — is not needed: it is an input *sufficient* for the existence, but the
exceptional divisor of a blowup already provides a different one.  The statement here is
therefore that one with `haff` removed, and also a generalization of
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isBlowupAlong`, which proves the
same conclusion for the two blowups that the construction of Stacks 085Q builds and so carries
that construction's data — two étale presentations, six `B.Contains` side conditions and a
`HasSheafify` instance.  None of that is needed for an arbitrary blowup.

Part (3) is `AlgebraicGeometry.Space.exists_isEtale_strictTransformSheaf_restriction` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEtaleLocalization.lean`, already unconditional; it
is restated here jointly with part (2) because the two existential statements would otherwise
produce the comparison morphism twice, with nothing identifying the two copies.  Both come from
part (1), `AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale`, applied to the two
canonical cartesian squares, so the joint statement is proved by invoking part (1) once and
reading both conclusions off the single `can` it returns.

No quasi-coherence hypothesis is carried on `F` in part (3): the source assumes it because that
is the case the tag is applied in, and neither the construction of the strict transform nor the
comparison uses it.

## References

* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Bl X Vv U B' V' : AlgebraicSpaces B S hS}

/-- **Stacks 0863, part (2).** Let `Z ⊆ 𝔅` be a closed subspace of an algebraic space over `S`,
let `b : 𝔅' ⟶ 𝔅` be the blowup of `𝔅` in `Z`, let `f : X ⟶ 𝔅` be an algebraic space over `𝔅`,
let

```
U ⟶ X
↓     ↓
𝒱 ⟶ 𝔅
```

be a commutative square with étale horizontal arrows and let `v' : 𝒱' ⟶ 𝒱` be the blowup of
`𝒱` in the inverse image `Z ×_𝔅 𝒱`.  Then the strict transform `U'` of `U` with respect to `v'`
is `X' ×_X U`, where `X'` is the strict transform of `X` with respect to `b`.

Precisely: there are `m : 𝒱' ⟶ 𝔅'` presenting `𝒱' = 𝒱 ×_𝔅 𝔅'` and an étale
`can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` over `u` and over `m`, sitting in a cartesian square that presents
`U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`, and `U'` is the inverse image of `X'` along `can` — which under
that presentation is the base change of `X'` along `u`.

**No hypothesis beyond the source's is carried.**  The existence of a closed subspace cut out by
the ideal of sections supported on the exceptional preimage, which is all that
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isEtale` asks for beyond the
étale comparison of those ideals, comes from the exceptional divisor `b^{-1}Z` being an
effective Cartier divisor on `𝔅'`; and that is one half of the universal property of Stacks
085U, so `hb` supplies it. -/
@[stacks 0863 "part (2): the strict transform of an étale chart U is the base change along u of \
the strict transform of X, for an arbitrary blowup and with no assumed inputs"]
theorem exists_strictTransform_eq_preimage
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

/-- **Stacks 0863, parts (2) and (3).** In the situation of part (1) there are `m : 𝒱' ⟶ 𝔅'`
presenting `𝒱' = 𝒱 ×_𝔅 𝔅'` and an étale `can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` over `u` and over `m`,
sitting in a cartesian square that presents `U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`, such that

* the strict transform `U'` of `U` with respect to `v'` is the inverse image of the strict
  transform `X'` of `X` with respect to `b` along `can`, which is part (2); and
* for every `𝒪_X`-module `F` the pullback along `can` of the strict transform of `F` with
  respect to `b` is the strict transform of `F|_U` with respect to `v'`, which is part (3).

Both for the *same* `m` and the same `can`: the two parts are read off the single comparison
morphism that part (1), `AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale`,
returns for the two canonical cartesian squares.  This is what a consumer of the tag needs, the
two parts separately leaving the two copies of `can` unidentified.

No hypothesis beyond the source's is carried, and no quasi-coherence of `F`; see
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage` and
`AlgebraicGeometry.Space.exists_isEtale_strictTransformSheaf_restriction`. -/
@[stacks 0863 "parts (2) and (3) for one and the same comparison morphism, for an arbitrary \
blowup and with no assumed inputs"]
theorem exists_strictTransform_eq_preimage_strictTransformSheaf_iso
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
            (preimageClosedSubspace b Z).1).preimage can.hom ∧
        ∀ F : Modules.{u, u} B S hS X.1 X.2,
          Nonempty ((modulePullback B S hS can).obj
              (strictTransformSheaf B S hS f b (preimageClosedSubspace b Z).1 F) ≅
            strictTransformSheaf B S hS w v'
              (preimageClosedSubspace v' (preimageClosedSubspace v Z)).1
              ((modulePullback B S hS u).obj F)) := by
  obtain ⟨m, sqm, -, can, hcanS, hcanB, hcan⟩ :=
    isEtale_baseChange_blowup_of_isEtale hb hv hu hcomm hv'
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w v')
  have hT := exceptionalPreimageSet_eq_preimage_of_comp_eq B S hS f b
    (preimageClosedSubspace b Z).1 w v'
    (preimageClosedSubspace v' (preimageClosedSubspace v Z)).1 m can hcanB
    (range_pointsMap_preimage_exceptional sqm)
  refine ⟨m, can, sqm, hcan, hcanS, hcanB,
    isPullback_canonical_of_comp_eq B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w v') sqm hcomm can hcanS hcanB,
    strictTransformSubfunctor_eq_preimage_of_isEffectiveCartierDivisor B S hS f b
      (preimageClosedSubspace b Z) hb.isPullbackDefined w v' _ can hcan hT,
    fun F => ⟨?_⟩⟩
  exact strictTransformSheafEtaleRestrictionIso B S hS f b _ u w v' _ m can hcan hcanS hcanB
    (range_pointsMap_preimage_exceptional sqm) F

end AlgebraicGeometry.Space

end
