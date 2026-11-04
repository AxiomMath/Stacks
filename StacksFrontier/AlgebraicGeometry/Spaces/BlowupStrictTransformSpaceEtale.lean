module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction

/-!
# Étale localization of the strict transform of an algebraic space

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
`v'` is `X' ×_X U`, where `X'` is the strict transform of `X` with respect to `b`.  That is
what this file proves, with no hypothesis beyond the source's.

The canonical morphism `can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` of part (1) sits in a cartesian square over
`u : U ⟶ X`, so `U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U` and the inverse image along `can` of a subspace
of `X ×_𝔅 𝔅'` *is* its base change along `u`.  The conclusions below are therefore the tag's
`U' = X' ×_X U`, stated as an assertion about `CategoryTheory.Subfunctor.preimage` along `can`
together with the cartesian square that makes that inverse image a base change.

## Main results

* `AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isBlowupAlong` is **Stacks
  0863, part (2)**, with no hypothesis beyond the source's: the two blowups are the ones Tag
  085Q constructs, `AlgebraicGeometry.Space.blowUpAlongHom'`, so that being a blowup is proved
  here (`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`) and not assumed.  What the
  statement takes besides the étale square is the construction data of Tag 085Q itself: an
  étale presentation of each of `𝔅` and `𝒱`, and the `B.Contains` side conditions on the
  relative `Proj`s.

The same identification from weaker inputs, for consumers that have one of them to hand rather
than a blowup — these are the general forms, and they do take being a blowup as a hypothesis:

* `AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isAffineHom`, from affineness
  of the inclusion of the complement of the exceptional preimage.
* `AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isEtale`, from the abstract
  hypothesis that the strict transform of `X` is cut out by the ideal of sections supported on
  the exceptional preimage.
* `AlgebraicGeometry.Space.exists_strictTransform_le_preimage_of_isEtale`: the inclusion
  `U' ⊆ X' ×_X U` alone, which needs none of those — it follows from the étale comparison of the
  ideals of supported sections by itself.

Auxiliary, and proved here:

* `AlgebraicGeometry.Space.isPullback_canonical_of_comp_eq`: the canonical morphism of part (1)
  sits in a cartesian square over `u`, which is the identification
  `U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`.

## How the two halves of the source's argument are supplied

The source derives part (2) from part (3) applied to `F = 𝒪_X`, which identifies the two
*quotients* of the structure sheaves, and then reads the closed subspaces off the ideals.

The étale compatibility that the first half needs is
`AlgebraicGeometry.Space.supportedSectionsUnit_obj_postcomp`, and it holds with no hypothesis:
a chart of `U ×_𝒱 𝒱'` is a chart of `X ×_𝔅 𝔅'` with the same underlying scheme, and the ideal
of supported sections is literally the same ideal there.

The reading-off is the half that needs an input, because
`AlgebraicGeometry.Space.strictTransform` is the infimum of the closed subspaces whose defining
ideal is dominated by the ideal of supported sections, and an infimum of a family is not
characterised by an ideal.  What repairs it is knowing that *some* closed subspace of
`X ×_𝔅 𝔅'` has that ideal as its defining ideal sheaf, i.e. quasi-coherence of the ideal, which
is part (3) of Stacks 0859,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_supportedSectionsSubmodule`, once the complement
of the exceptional preimage has quasi-compact inclusion.  For a blowup that is supplied by the
blowup itself, in three steps carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformSpaceEtaleRestriction.lean`:  the
exceptional divisor `b^{-1}Z` is an effective Cartier divisor on `𝔅'`, which is one half of the
universal property of Stacks 085U
(`AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined`); an effective Cartier divisor is
locally principal, Stacks 083B(1), and so is its inverse image `pr_{𝔅'}^{-1}(b^{-1}Z)` by
Stacks 083X; and the complement of a locally principal closed subspace has affine, hence
quasi-compact, inclusion by Stacks 083D.  So nothing is left over.

## Implementation notes

`m`, `can` and the two commutations come from part (1),
`AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale`, applied to the two canonical
cartesian squares of `AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`.  The
hypothesis on the exceptional divisors that the general statements of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformSpaceEtaleRestriction.lean` need is
`AlgebraicGeometry.Space.range_pointsMap_preimage_exceptional`, read off the cartesian square
`𝒱' = 𝒱 ×_𝔅 𝔅'`:  both exceptional divisors are inverse images of `Z`, and on points the
inverse image of a subspace is the inverse image of its points, Stacks 03H4.

The cartesian square for `can` is the one part (1)'s proof constructs internally but does not
return:  pasting `U ×_𝒱 𝒱' = U ×_𝒱 𝒱'` with `𝒱' = 𝒱 ×_𝔅 𝔅'` gives `U ×_𝒱 𝒱' = U ×_𝔅 𝔅'`, and
cancelling `X ×_𝔅 𝔅'` on the right gives `U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`.  That the lift so
obtained *is* `can` is uniqueness in the cartesian square `X ×_𝔅 𝔅'`, the two commutations
being exactly the two components.

No quasi-coherence of a module and no module at all enters:  part (2) is a statement about
closed subspaces, and it is proved here from the ideal of supported sections of the structure
sheaf directly, not by specializing a statement about modules.

`AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage_of_comp_eq` restates, under a
different name, a point-set computation that also occurs in the development of part (3) of this
tag; it is kept separate here, and a dedup pass should merge the two.

## References

* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083D](https://stacks.math.columbia.edu/tag/083D)
* [Stacks Project, Tag 083X](https://stacks.math.columbia.edu/tag/083X)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### An input read off the cartesian square of part (1) -/

section Inputs

variable {Bl X Vv U B' V' W W' : AlgebraicSpaces B S hS}

/-- **The canonical morphism `U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` sits in a cartesian square over `u`**, that
is, `U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`.

Pasting `U ×_𝒱 𝒱' = U ×_𝒱 𝒱'` with `𝒱' = 𝒱 ×_𝔅 𝔅'` gives `U ×_𝒱 𝒱' = U ×_𝔅 𝔅'`, and
cancelling `X ×_𝔅 𝔅'` on the right gives the square.  The morphism so obtained is `can` itself
because a morphism into `X ×_𝔅 𝔅'` is determined by its two components, which is what the two
commutations say. -/
theorem isPullback_canonical_of_comp_eq
    {f : X ⟶ Bl} {b : B' ⟶ Bl} {v : Vv ⟶ Bl} {u : U ⟶ X} {w : U ⟶ Vv} {v' : V' ⟶ Vv}
    {m : V' ⟶ B'} {pX : W ⟶ X} {pB' : W ⟶ B'} {qU : W' ⟶ U} {qV' : W' ⟶ V'}
    (sq : IsPullback pX pB' f b) (sq' : IsPullback qU qV' w v') (sqm : IsPullback v' m v b)
    (hcomm : u ≫ f = w ≫ v) (can : W' ⟶ W)
    (hcanS : can ≫ pX = qU ≫ u) (hcanB : can ≫ pB' = qV' ≫ m) :
    IsPullback can qU pX u := by
  have sbig : IsPullback (qV' ≫ m) qU b (u ≫ f) := by
    rw [hcomm]
    exact sq'.flip.paste_horiz sqm.flip
  have hlift : (qV' ≫ m) ≫ b = (qU ≫ u) ≫ f := by rw [sbig.w, Category.assoc]
  have hcart : IsPullback (sq.flip.lift (qV' ≫ m) (qU ≫ u) hlift) qU pX u :=
    IsPullback.of_right' sbig sq.flip
  have heq : can = sq.flip.lift (qV' ≫ m) (qU ≫ u) hlift :=
    sq.flip.hom_ext (by rw [sq.flip.lift_fst]; exact hcanB)
      (by rw [sq.flip.lift_snd]; exact hcanS)
  rwa [heq]

end Inputs

/-! ### Stacks 0863, part (2) -/

section Part2

variable {Bl X Vv U B' V' : AlgebraicSpaces B S hS}

/-- **Stacks 0863, part (2), one inclusion.** Let `Z ⊆ 𝔅` be a closed subspace of an algebraic
space over `S`, let `b : 𝔅' ⟶ 𝔅` be the blowup of `𝔅` in `Z`, let `f : X ⟶ 𝔅` be an algebraic
space over `𝔅`, let

```
U ⟶ X
↓     ↓
𝒱 ⟶ 𝔅
```

be a commutative square with étale horizontal arrows and let `v' : 𝒱' ⟶ 𝒱` be the blowup of
`𝒱` in `Z ×_𝔅 𝒱`.  Then there are `m : 𝒱' ⟶ 𝔅'` presenting `𝒱' = 𝒱 ×_𝔅 𝔅'` and an étale
`can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` over `u` and over `m`, presenting
`U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`, and the strict transform `U'` of `U` with respect to `v'` is
*contained in* `X' ×_X U`, the base change of the strict transform `X'` of `X` with respect
to `b`.

This inclusion carries no hypothesis beyond the source's.  It is proved from
`AlgebraicGeometry.Space.strictTransformSubfunctor_le_preimage_of_isEtale`:  the inverse image
along `can` of a closed subspace whose defining ideal is dominated by the ideal of supported
sections has the same property, so the infimum defining `U'` is at most the inverse image of the
infimum defining `X'`.  The reverse inclusion needs the strict transform of `X` to be honestly
cut out by that ideal; see
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isAffineHom`. -/
theorem exists_strictTransform_le_preimage_of_isEtale
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
            (preimageClosedSubspace v' (preimageClosedSubspace v Z)).1 ≤
          (strictTransformSubfunctor B S hS f b
            (preimageClosedSubspace b Z).1).preimage can.hom := by
  obtain ⟨m, sqm, -, can, hcanS, hcanB, hcan⟩ :=
    isEtale_baseChange_blowup_of_isEtale hb hv hu hcomm hv'
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w v')
  refine ⟨m, can, sqm, hcan, hcanS, hcanB,
    isPullback_canonical_of_comp_eq B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w v') sqm hcomm can hcanS hcanB, ?_⟩
  exact strictTransformSubfunctor_le_preimage_of_isEtale B S hS f b _ w v' _ can hcan
    (exceptionalPreimageSet_eq_preimage_of_comp_eq B S hS f b _ w v' _ m can hcanB
      (range_pointsMap_preimage_exceptional sqm))

/-- **Stacks 0863, part (2), from the strict transform of `X` being cut out by its ideal.** In
the situation of part (1), if some closed subspace of `X ×_𝔅 𝔅'` has the ideal of sections of
`𝒪_{X ×_𝔅 𝔅'}` supported on the exceptional preimage as its defining ideal sheaf, then the
strict transform `U'` of `U` with respect to `v'` *is* `X' ×_X U`.

The hypothesis is about the first situation alone.  See
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isAffineHom` for the version
whose hypothesis is geometric. -/
theorem exists_strictTransform_eq_preimage_of_isEtale
    {Z : ClosedSubspaces B S hS Bl.1} {b : B' ⟶ Bl} (hb : IsBlowupAlong B S hS Z b)
    {f : X ⟶ Bl} {v : Vv ⟶ Bl} (hv : IsEtale B S hS v.hom)
    {u : U ⟶ X} (hu : IsEtale B S hS u.hom) {w : U ⟶ Vv} (hcomm : u ≫ f = w ≫ v)
    {v' : V' ⟶ Vv} (hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z) v')
    (hex : ∃ Z₀ : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1,
      definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z₀ =
        strictTransformIdealSubmodule B S hS f b (preimageClosedSubspace b Z).1) :
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
            (preimageClosedSubspace b Z).1).preimage can.hom := by
  obtain ⟨m, sqm, -, can, hcanS, hcanB, hcan⟩ :=
    isEtale_baseChange_blowup_of_isEtale hb hv hu hcomm hv'
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w v')
  refine ⟨m, can, sqm, hcan, hcanS, hcanB,
    isPullback_canonical_of_comp_eq B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w v') sqm hcomm can hcanS hcanB, ?_⟩
  exact strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq B S hS f b _
    w v' _ can hcan
    (exceptionalPreimageSet_eq_preimage_of_comp_eq B S hS f b _ w v' _ m can hcanB
      (range_pointsMap_preimage_exceptional sqm)) hex

/-- **Stacks 0863, part (2).** In the situation of part (1) — `b : 𝔅' ⟶ 𝔅` the blowup of `𝔅` in
a closed subspace `Z`, `f : X ⟶ 𝔅` an algebraic space over `𝔅`, a commutative square from
`u : U ⟶ X` and `v : 𝒱 ⟶ 𝔅` with étale horizontal arrows, and `v' : 𝒱' ⟶ 𝒱` the blowup of `𝒱`
in `Z ×_𝔅 𝒱` — the strict transform `U'` of `U` with respect to `v'` is `X' ×_X U`, where `X'`
is the strict transform of `X` with respect to `b`.

Precisely: there are `m : 𝒱' ⟶ 𝔅'` presenting `𝒱' = 𝒱 ×_𝔅 𝔅'` and an étale
`can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` over `u` and over `m`, sitting in a cartesian square that presents
`U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`, and `U'` is the inverse image of `X'` along `can` — which under
that presentation is the base change of `X'` along `u`.

**This statement carries the extra hypothesis `haff`, which the source derives and this library
cannot.**  `haff` says that the inclusion of the complement of the exceptional preimage
`pr_{𝔅'}^{-1}(b^{-1}Z) ⊆ X ×_𝔅 𝔅'` is an affine morphism: the affineness half of Stacks 07ZU,
which feeds quasi-coherence of the ideal of supported sections through part (3) of Stacks 0859
and hence the passage from that ideal to the closed subspace it cuts out.  It is a hypothesis on
the first situation alone — it names neither `𝒱`, `U`, `𝒱'` nor `can` — and so is independent of
the conclusion.  See the module documentation for what would discharge it.

Without `haff` one inclusion still holds, with no hypothesis beyond the source's:
`AlgebraicGeometry.Space.exists_strictTransform_le_preimage_of_isEtale`. -/
theorem exists_strictTransform_eq_preimage_of_isAffineHom
    {Z : ClosedSubspaces B S hS Bl.1} {b : B' ⟶ Bl} (hb : IsBlowupAlong B S hS Z b)
    {f : X ⟶ Bl} {v : Vv ⟶ Bl} (hv : IsEtale B S hS v.hom)
    {u : U ⟶ X} (hu : IsEtale B S hS u.hom) {w : U ⟶ Vv} (hcomm : u ≫ f = w ≫ v)
    {v' : V' ⟶ Vv} (hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z) v')
    (haff : IsAffineHom B S hS (openComplement B S hS
      (exceptionalPreimage B S hS f b (preimageClosedSubspace b Z).1)).ι) :
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
    (strictTransform_exists_of_isAffineHom_openComplement B S hS f b
      (preimageClosedSubspace b Z).1 (preimageClosedSubspace b Z).2 haff)

end Part2

/-! ### Stacks 0863, part (2), for the blowups themselves -/

section Part2Blowup

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {Bl X Vv U : AlgebraicSpaces B S hS}

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

**No hypothesis beyond the source's is carried, and in particular being a blowup is not
assumed.**  The two blowups are the ones Tag 085Q constructs,
`AlgebraicGeometry.Space.blowUpAlongHom'` for `𝔅` in `Z` and for `𝒱` in `Z ×_𝔅 𝒱`; that each
of them *is* the blowup, in the sense of the universal property of Stacks 085U, is
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`.  The arguments `P`, `P'` and the six
`B.Contains` side conditions are the construction data Tag 085Q itself takes — an étale
presentation of the space being blown up and the set-theoretic conditions on the three relative
`Proj`s that `AlgebraicGeometry.Space.relativeProjChartOfSituation` asks for — and nothing is
assumed about `Z` beyond being a closed subspace.

The two halves of the argument are as in
`AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isEtale`: the étale comparison
of the ideals of supported sections, and that the strict transform of `X` is honestly cut out
by that ideal, which comes from the exceptional divisor `b^{-1}Z` being an effective Cartier
divisor — one half of the universal property of Stacks 085U. -/
@[stacks 0863 "part (2), for the blowups of 085Q themselves: the strict transform of an étale \
chart U is the base change along u of the strict transform of X"]
theorem exists_strictTransform_eq_preimage_of_isBlowupAlong
    {Z : ClosedSubspaces B S hS Bl.obj} (P : Presentation B S hS Bl.obj Bl.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    {f : X ⟶ Bl} {v : Vv ⟶ Bl} (hv : IsEtale B S hS v.hom)
    {u : U ⟶ X} (hu : IsEtale B S hS u.hom) {w : U ⟶ Vv} (hcomm : u ≫ f = w ≫ v)
    (P' : Presentation B S hS Vv.obj Vv.property)
    (hcU' : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace v Z))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace v Z)) P').relativeProj)
    (hcR' : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace v Z))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace v Z)) P').relativeProj)
    (hcRR' : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace v Z))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace v Z)) P').relativeProj) :
    ∃ (m : blowUpAlong' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR' ⟶
        blowUpAlong' Z P hcU hcR hcRR)
      (can : strictTransformPullback B S hS w
          (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR') ⟶
        strictTransformPullback B S hS f (blowUpAlongHom' Z P hcU hcR hcRR)),
      IsPullback (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR') m v
          (blowUpAlongHom' Z P hcU hcR hcRR) ∧
        IsEtale B S hS can.hom ∧
        can ≫ strictTransformPullbackToSource B S hS f (blowUpAlongHom' Z P hcU hcR hcRR) =
          strictTransformPullbackToSource B S hS w
            (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR') ≫ u ∧
        can ≫ strictTransformPullbackToBlowUp B S hS f (blowUpAlongHom' Z P hcU hcR hcRR) =
          strictTransformPullbackToBlowUp B S hS w
            (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR') ≫ m ∧
        IsPullback can
          (strictTransformPullbackToSource B S hS w
            (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR'))
          (strictTransformPullbackToSource B S hS f (blowUpAlongHom' Z P hcU hcR hcRR)) u ∧
        strictTransformSubfunctor B S hS w
            (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR')
            (preimageClosedSubspace
              (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR')
              (preimageClosedSubspace v Z)).1 =
          (strictTransformSubfunctor B S hS f (blowUpAlongHom' Z P hcU hcR hcRR)
            (preimageClosedSubspace (blowUpAlongHom' Z P hcU hcR hcRR) Z).1).preimage
            can.hom := by
  have hb : IsBlowupAlong B S hS Z (blowUpAlongHom' Z P hcU hcR hcRR) :=
    isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR
  have hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z)
      (blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR') :=
    isBlowupAlong_blowUpAlongHom' (preimageClosedSubspace v Z) P' hcU' hcR' hcRR'
  exact exists_strictTransform_eq_preimage_of_isEtale B S hS hb hv hu hcomm hv'
    (strictTransform_exists_of_isEffectiveCartierDivisor B S hS f
      (blowUpAlongHom' Z P hcU hcR hcRR)
      (preimageClosedSubspace (blowUpAlongHom' Z P hcU hcR hcRR) Z) hb.isPullbackDefined)

end Part2Blowup

end AlgebraicGeometry.Space

end
