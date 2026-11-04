module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformEtaleRestriction

/-!
# Étale localization of a blowup

Let `S` be a scheme, let `𝔅` be an algebraic space over `S`, let `Z ⊆ 𝔅` be a closed subspace
and let `b : 𝔅' ⟶ 𝔅` be the blowup of `𝔅` in `Z`.  Let `f : X ⟶ 𝔅` be an algebraic space over
`𝔅` and consider a commutative square

```
U ⟶ X
↓     ↓
𝒱 ⟶ 𝔅
```

with étale horizontal arrows, and let `v' : 𝒱' ⟶ 𝒱` be the blowup of `𝒱` in the inverse image
`Z ×_𝔅 𝒱`.  Part (1) of Stacks 0863 says that `𝒱' = 𝒱 ×_𝔅 𝔅'` and that the two morphisms
`𝒱' ⟶ 𝔅'` and `U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` are étale.  Part (3) says that for an `𝒪_X`-module `F`
the restriction of the strict transform `F'` to `U ×_𝒱 𝒱'` is the strict transform of `F|_U`
relative to `v'`.  Both are proved here.

## Main results

* `AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale` is **Stacks 0863, part (1)**:
  the blowup of `𝒱` in `Z ×_𝔅 𝒱` is the base change of the blowup of `𝔅` in `Z`, the induced
  morphism `𝒱' ⟶ 𝔅'` is étale, and so is the induced morphism `U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'`.
* `AlgebraicGeometry.Space.exists_isEtale_strictTransformSheaf_restriction` is **Stacks 0863,
  part (3)**: the induced morphism `can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` is étale, lies over `u`, and
  pulls the strict transform of `F` back to the strict transform of `F|_U`.

## Implementation notes

The source's argument is used verbatim: blowing up commutes with flat base change, étale
morphisms are flat, and the base change of an étale morphism is étale.  The first input is
`AlgebraicGeometry.Space.isBlowupAlong_preimage_of_isPullback_of_isFlat` (Stacks 085S), the
second `AlgebraicGeometry.Space.isFlat_of_isEtale` (Stacks 03ML) and the third
`AlgebraicGeometry.Space.isEtale_of_isPullback` (Stacks 03FV).

The source takes `U` and `𝒱` to be *schemes* étale over `X` and over `𝔅`.  Nothing in the
argument uses that, so the statement here is for an arbitrary commutative square of algebraic
spaces with étale horizontal arrows; a scheme of the ambient big fppf site represents such an
algebraic space, so the source's situation is the special case of this one.

The fibre products are taken as hypotheses in the form of cartesian squares rather than built,
as elsewhere in this development; the category of algebraic spaces over `S` does have fibre
products, `AlgebraicGeometry.AlgebraicSpaces.hasPullbacks`, so the hypotheses are satisfiable
for every input.  The blowup itself is named by the universal property of Stacks 085U,
`AlgebraicGeometry.Space.IsBlowupAlong`, rather than by the explicit construction of Stacks
085Q, `AlgebraicGeometry.Space.blowUpAlong'` — the latter is available, but only once a
presentation of the ambient algebraic space and the three containment side-conditions on its
charts have been fixed, which this lemma's hypotheses (an arbitrary commutative square of
algebraic spaces) do not supply.  The universal property needs no such choice, and any two
blowups of the same closed subspace are canonically isomorphic over it,
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`, so nothing is lost by stating the result
this way.

That `U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` is étale is read off the identification
`U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`, which makes it a base change of `U ⟶ X`.  The identification is
the cancellation of a cartesian square in a composite of two: pasting `U ×_𝒱 𝒱' = U ×_𝒱 𝒱'` with
`𝒱' = 𝒱 ×_𝔅 𝔅'` gives `U ×_𝒱 𝒱' = U ×_𝔅 𝔅'`, and `X ×_𝔅 𝔅' = X ×_𝔅 𝔅'` then cancels on the
right.

Part (3) is the source's argument too: taking the sheaf of sections supported on a closed subset
commutes with pullback by an étale morphism, so the quotient defining the strict transform does.
That compatibility is `AlgebraicGeometry.Space.modulePullbackSupportedSectionsQuotientIso`, and
the passage from it to the strict transforms is
`AlgebraicGeometry.Space.strictTransformSheafEtaleRestrictionIso`; see
`StacksFrontier/AlgebraicGeometry/Spaces/SupportedSectionsEtaleRestriction.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformEtaleRestriction.lean`.  The source cites
Stacks 0859 for the compatibility, which is an abuse: that tag has no base-change clause.  What
is used is the *defining* chartwise description of the supported-section subsheaf — an étale
chart of `U ×_𝒱 𝒱'` is an étale chart of `X ×_𝔅 𝔅'` with the same underlying scheme, and the
support of a section is unchanged — and not parts (2) or (3) of 0859; no quasi-coherence, no
finite type ideal and no ideal-power torsion enters.  The two hypotheses that the general
statement needs about the ambient geometry are exactly what part (1) supplies: that
`can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` is étale, and that the exceptional divisor of `v'` has as its
points the inverse image of the points of the exceptional divisor of `b`, which is
`AlgebraicGeometry.Space.range_pointsMap_preimage_exceptional` below, read off the cartesian
square `𝒱' = 𝒱 ×_𝔅 𝔅'`.

No quasi-coherence hypothesis is carried on `F` in part (3).  The source states it for a
quasi-coherent module because that is what it is applied to, but the strict transform of
Stacks 0862 is constructed for an arbitrary module and so is its étale restriction.

## What is not proved

Part (2) of Stacks 0863 — that the strict transform `U'` of `U` relative to `𝒱' ⟶ 𝒱` is
`X' ×_X U` — is not proved.  The source derives it from (3) applied to `F = 𝒪_X`, which
identifies the two *quotients* of the structure sheaves, and reads the closed subspaces off the
ideals.  The last step is what is missing: this library has no unconditional passage from a
prescribed quasi-coherent ideal to the closed subspace it cuts out, so
`AlgebraicGeometry.Space.strictTransform` is the infimum of the closed subspaces whose defining
ideal is dominated by the ideal of supported sections, and the infimum of a family is not
characterised by an ideal.  See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransform.lean`, and
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq`, which is the
statement that would make the reading-off legitimate as soon as one such closed subspace is
known to exist.  Existence rests on quasi-coherence of the ideal of supported sections, and
hence on the preamble of the section containing Stacks 0862: that the exceptional divisor is an
effective Cartier divisor, that its preimage is locally principal, and that the complement of a
locally principal closed subspace has an affine inclusion.  None of the three is available for
algebraic spaces.  Quasi-coherence of a cokernel on the small étale site, which that preamble
also feeds, *is* now available with no hypothesis —
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional` in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentCokernelsUnconditional.lean` — so it is no
longer part of the obstruction; on this point it supersedes the implementation notes of
`StrictTransform.lean`.

## References

* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0863, part (1).** Let `Z ⊆ 𝔅` be a closed subspace of an algebraic space over `S`,
let `b : 𝔅' ⟶ 𝔅` be the blowup of `𝔅` in `Z` and let `f : X ⟶ 𝔅` be an algebraic space over
`𝔅`.  Let

```
U ⟶ X
↓     ↓
𝒱 ⟶ 𝔅
```

be a commutative square with étale horizontal arrows, and let `v' : 𝒱' ⟶ 𝒱` be the blowup of
`𝒱` in the inverse image `Z ×_𝔅 𝒱` of `Z`.  Then:

* `𝒱' = 𝒱 ×_𝔅 𝔅'`, by a cartesian square over `v` and `b`;
* the resulting morphism `m : 𝒱' ⟶ 𝔅'` is étale;
* the induced morphism `U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` is étale.

The first assertion is Stacks 085S applied to `v`, which is flat because it is étale.  The
second is the base change of an étale morphism along `b`.  For the third,
`U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`, so the morphism is a base change of the étale morphism
`u : U ⟶ X`. -/
@[stacks 0863 "part (1): the blowup localizes étale-locally, and the induced morphisms are \
étale"]
theorem isEtale_baseChange_blowup_of_isEtale
    {𝔅 X 𝒱 U B' V' W W' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS 𝔅.1} {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b)
    {f : X ⟶ 𝔅} {v : 𝒱 ⟶ 𝔅} (hv : IsEtale B S hS v.hom)
    {u : U ⟶ X} (hu : IsEtale B S hS u.hom) {w : U ⟶ 𝒱} (hcomm : u ≫ f = w ≫ v)
    {v' : V' ⟶ 𝒱} (hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z) v')
    {pX : W ⟶ X} {pB' : W ⟶ B'} (sq : IsPullback pX pB' f b)
    {qU : W' ⟶ U} {qV' : W' ⟶ V'} (sq' : IsPullback qU qV' w v') :
    ∃ m : V' ⟶ B', IsPullback v' m v b ∧ IsEtale B S hS m.hom ∧
      ∃ can : W' ⟶ W, can ≫ pX = qU ≫ u ∧ can ≫ pB' = qV' ≫ m ∧
        IsEtale B S hS can.hom := by
  -- `𝒱' = 𝒱 ×_𝔅 𝔅'`: blowing up commutes with flat base change, and `v` is flat.
  obtain ⟨m, sqm⟩ := exists_isPullback_blowup_of_isFlat (isFlat_of_isEtale B S hS hv) hb hv'
  refine ⟨m, sqm, isEtale_of_isPullback B S hS v' m v b sqm hv, ?_⟩
  -- `U ×_𝒱 𝒱' = U ×_𝔅 𝔅'`, by pasting the two cartesian squares.
  have sbig : IsPullback (qV' ≫ m) qU b (u ≫ f) := by
    rw [hcomm]
    exact sq'.flip.paste_horiz sqm.flip
  -- Cancelling `X ×_𝔅 𝔅'` on the right makes `U ×_𝒱 𝒱' = (X ×_𝔅 𝔅') ×_X U`.
  have hlift : (qV' ≫ m) ≫ b = (qU ≫ u) ≫ f := by rw [sbig.w, Category.assoc]
  have hcart : IsPullback (sq.flip.lift (qV' ≫ m) (qU ≫ u) hlift) qU pX u :=
    IsPullback.of_right' sbig sq.flip
  refine ⟨sq.flip.lift (qV' ≫ m) (qU ≫ u) hlift, sq.flip.lift_snd _ _ _,
    sq.flip.lift_fst _ _ _, ?_⟩
  exact isEtale_of_isPullback B S hS qU _ u pX hcart.flip hu

/-- **The exceptional divisor of the blowup of `𝒱` has as its points the inverse image under
`|m|` of the points of the exceptional divisor of the blowup of `𝔅`.**

Both exceptional divisors are inverse images of `Z`: that of `b` is `b^{-1}Z` and that of `v'`
is `v'^{-1}(v^{-1}Z)`, since `v'` is the blowup of `𝒱` in `Z ×_𝔅 𝒱 = v^{-1}Z`.  On points the
inverse image of a subspace is the inverse image of its points, Stacks 03H4 in the form
`AlgebraicGeometry.Space.range_pointsMap_preimage_ι`, so both sides are the inverse image of
`|Z|` along the two sides of `v' ≫ v = m ≫ b`.

The two exceptional divisors are spelled by `CategoryTheory.Subfunctor.preimage`, which is what
`AlgebraicGeometry.Space.preimageClosedSubspace` is on underlying subfunctors. -/
theorem range_pointsMap_preimage_exceptional {𝔅 𝒱 B' V' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS 𝔅.1} {b : B' ⟶ 𝔅} {v : 𝒱 ⟶ 𝔅} {v' : V' ⟶ 𝒱} {m : V' ⟶ B'}
    (sqm : IsPullback v' m v b) :
    Set.range (pointsMap B S hS ((Z.1.preimage v.hom).preimage v'.hom).toFunctor
        ((Z.1.preimage v.hom).preimage v'.hom).ι) =
      pointsMap B S hS V'.1 m.hom ⁻¹'
        Set.range (pointsMap B S hS (Z.1.preimage b.hom).toFunctor
          (Z.1.preimage b.hom).ι) := by
  rw [range_pointsMap_preimage_ι B S hS v'.hom (Z.1.preimage v.hom),
    range_pointsMap_preimage_ι B S hS v.hom Z.1,
    range_pointsMap_preimage_ι B S hS b.hom Z.1,
    ← Set.preimage_comp, ← Set.preimage_comp,
    ← pointsMap_comp B S hS V'.1 v'.hom v.hom,
    ← pointsMap_comp B S hS V'.1 m.hom b.hom]
  exact congrArg (fun g => pointsMap B S hS V'.1 g ⁻¹'
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))
    (congrArg (fun g : V' ⟶ 𝔅 => g.hom) sqm.w)

/-- **Stacks 0863, part (3).** In the situation of part (1), let `F` be an `𝒪_X`-module.  Then
there are `m : 𝒱' ⟶ 𝔅'` presenting `𝒱' = 𝒱 ×_𝔅 𝔅'` and a morphism
`can : U ×_𝒱 𝒱' ⟶ X ×_𝔅 𝔅'` over `u : U ⟶ X` and over `m`, and `can` is étale and pulls the
strict transform of `F` relative to the blowup `b : 𝔅' ⟶ 𝔅` of `𝔅` in `Z` back to the strict
transform of `F|_U` relative to the blowup `v' : 𝒱' ⟶ 𝒱` of `𝒱` in `Z ×_𝔅 𝒱`.

The two commutations `can ≫ pr_X = pr_U ≫ u` and `can ≫ pr_{𝔅'} = pr_{𝒱'} ≫ m` say that `can`
is *the* canonical morphism of the tag, the universal property of `X ×_𝔅 𝔅'` determining it
from them; so pulling back along it is the restriction to `U ×_𝒱 𝒱'` that the tag speaks of.

Here the strict transform is the one of Stacks 0862,
`AlgebraicGeometry.Space.strictTransformSheaf`, taken with respect to the blowup together with
its exceptional divisor `b^{-1}Z`, respectively `v'^{-1}(v^{-1}Z)`; the fibre products are the
ones of `AlgebraicGeometry.AlgebraicSpaces.fiberProduct`, and `F|_U` is the pullback `u^*F` of
Stacks 03LU, which for the étale `u` is restriction of sections by Stacks 03LW.

`m`, `can` and their properties come from part (1),
`AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale`, applied to the two canonical
cartesian squares; the identification of the strict transforms is
`AlgebraicGeometry.Space.strictTransformSheafEtaleRestrictionIso`, whose hypothesis on the
exceptional divisors is `AlgebraicGeometry.Space.range_pointsMap_preimage_exceptional`.

No quasi-coherence of `F` is assumed: the source assumes it because that is the case the tag is
applied in, and neither the construction of the strict transform nor this comparison uses it. -/
@[stacks 0863 "part (3): the strict transform of a module restricts to the strict transform of \
its restriction; stated for an arbitrary module, the source's quasi-coherence being unused"]
theorem exists_isEtale_strictTransformSheaf_restriction
    {𝔅 X 𝒱 U B' V' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS 𝔅.1} {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b)
    {f : X ⟶ 𝔅} {v : 𝒱 ⟶ 𝔅} (hv : IsEtale B S hS v.hom)
    {u : U ⟶ X} (hu : IsEtale B S hS u.hom) {w : U ⟶ 𝒱} (hcomm : u ≫ f = w ≫ v)
    {v' : V' ⟶ 𝒱} (hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z) v')
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ∃ (m : V' ⟶ B') (can : strictTransformPullback B S hS w v' ⟶
        strictTransformPullback B S hS f b),
      IsPullback v' m v b ∧ IsEtale B S hS can.hom ∧
        can ≫ strictTransformPullbackToSource B S hS f b =
          strictTransformPullbackToSource B S hS w v' ≫ u ∧
        can ≫ strictTransformPullbackToBlowUp B S hS f b =
          strictTransformPullbackToBlowUp B S hS w v' ≫ m ∧
        Nonempty ((modulePullback B S hS can).obj
            (strictTransformSheaf B S hS f b (preimageClosedSubspace b Z).1 F) ≅
          strictTransformSheaf B S hS w v'
            (preimageClosedSubspace v' (preimageClosedSubspace v Z)).1
            ((modulePullback B S hS u).obj F)) := by
  obtain ⟨m, sqm, -, can, hcanS, hcanB, hcan⟩ :=
    isEtale_baseChange_blowup_of_isEtale hb hv hu hcomm hv'
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w v')
  exact ⟨m, can, sqm, hcan, hcanS, hcanB,
    ⟨strictTransformSheafEtaleRestrictionIso B S hS f b _ u w v' _ m can
      hcan hcanS hcanB (range_pointsMap_preimage_exceptional sqm) F⟩⟩

end AlgebraicGeometry.Space

end
