module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafSiteTopos
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposComp
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposId
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposTwoIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardTopoi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RingedToposEquivalenceTwoIso

/-!
# `f^{-1}ℐ · 𝒪_X` across the square of [Stacks, Tag 03CR]

The reduction of [Stacks, Tag 0A0G] from a morphism of ringed topoi to a morphism of ringed
*sites* goes through the square of [Stacks, Tag 03CR], exactly as `PushforwardTopoi.lean`'s proof
of [Stacks, Tag 099J] does:

* the dense-subsite replacements `g : X ⟶ X'` and `e : Y ⟶ Y'`, which are equivalences, and
  whose inverses are presented by morphisms of ringed *sites* — the restrictions
  `r_X = AlgebraicGeometry.RingedToposHom.denseRestrictSite X J' v` and `r_Y` — by
  `AlgebraicGeometry.RingedToposHom.inverseTwoIsoDenseRestrict`;
* the middle arrow `hs : X' ⟶ Y'`, a genuine morphism of ringed sites;
* a 2-isomorphism `τ` between `hs ∘ g` and `e ∘ f`, which is all the square asserts.

Each of the three arrows of the square that the ringed-sites case of the tag is applied to
constructs its own `ℐ' = f^{-1}ℐ · 𝒪` out of the ideal it is handed, and for the three
applications to compose, the ideal that `hs` produces out of `r_Y^{-1}ℐ · 𝒪_{Y'}` must be the
ideal that `r_X` produces out of `f^{-1}ℐ · 𝒪_X`. That is what this file proves.

## The proof is ideal-level algebra, with no 2-cell gymnastics

One might expect to build a 2-isomorphism between the two morphisms `X' ⟶ Y` obtained by going
round the square the two ways — `r_Y ∘ hs` and `f ∘ r_X` — by whiskering `τ` and cancelling the
round trips. That is not necessary. The construction `ℐ ↦ f^{-1}ℐ · 𝒪` is *functorial*
(`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp`), *2-isomorphism invariant*
(`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIdealSheaf_eq`) and *unital*
(`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_id`), so the whole computation can be
done on sheaves of ideals:

* apply the invariance to `τ` itself, at the ideal `g^{-1}`-transported from `ℐ`, and break both
  composites with the functoriality: `g^{-1}(hs^{-1}J) = f^{-1}(e^{-1}J)`;
* the right-hand side collapses because `e^{-1} ∘ e^{-1}`'s round trip is the identity, by
  `AlgebraicGeometry.RingedToposHom.inverseCompTwoIsoId`;
* apply `g^{-1}`'s inverse to both sides; the left-hand side collapses by
  `AlgebraicGeometry.RingedToposHom.compInverseTwoIsoId`.

The passage between the site-level and topos-level constructions, needed because the three
site-presented arrows state their ideals site-level, is
`AlgebraicGeometry.RingedSite.inverseImageIdealSheaf_ringedToposHom`.

## Main results

* `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_denseSquare`: **the sheaves of ideals
  match along the 03CR square**, with no hypothesis on `ℐ` and none on `f`.

## Deliberately untagged

Section 52.7 introduces `f^{-1}ℐ · 𝒪_X` in passing rather than as a numbered statement, and
nothing in this development of it carries an attribute. In particular this is *not* a statement
of [Stacks, Tag 0A0G]: it is the bookkeeping that makes the reduction to the ringed-sites case of
that tag type-check.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom.{u, u, u, u, u, u} X Y)
  {C' : Type u} [SmallCategory C'] (J' : GrothendieckTopology C') (v : X.C ⥤ C')
  [v.IsDenseSubsite X.J J']
  {D' : Type u} [SmallCategory D'] (K' : GrothendieckTopology D') (w : Y.C ⥤ D')
  [w.IsDenseSubsite Y.J K']
  (hs : RingedSite.Hom (denseReplacement X J' v).toRingedSite
    (denseReplacement Y K' w).toRingedSite)
  (τ : TwoIso.{u, u, u, u, u, u} (A := X) (B := denseReplacement Y K' w)
    (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := denseReplacement X J' v)
      hs.ringedToposHom (denseReplacementHom X J' v))
    (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (denseReplacementHom Y K' w) f))
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))

include τ in
/-- **The sheaves of ideals match along the square of [Stacks, Tag 03CR].** The ideal
`ℐ' = f^{-1}ℐ · 𝒪_X` that the middle arrow of the square builds out of the ideal the
`Y`-replacement hands it is the ideal that the `X`-replacement builds out of the ideal `f` builds
out of `ℐ`. No hypothesis on `ℐ`, and none on `f` beyond its being a morphism of ringed topoi.

This is the bookkeeping identity that makes the reduction of [Stacks, Tag 0A0G] to the
ringed-sites case type-check: all three of the square's non-equivalence arrows apply the
ringed-sites case of the tag to *their own* `f^{-1}ℐ · 𝒪`, and those three applications only
compose because of this. See the module documentation for the proof, which is algebra on sheaves
of ideals and constructs no 2-cell. -/
theorem inverseImageIdealSheaf_denseSquare :
    RingedSite.inverseImageIdealSheaf.{u} hs
        (RingedSite.inverseImageIdealSheaf.{u} (denseRestrictSite Y K' w) I) =
      RingedSite.inverseImageIdealSheaf.{u} (denseRestrictSite X J' v)
        (inverseImageIdealSheaf.{u} f I) := by
  -- The ideal on `Y'` that the replacement equivalence's inverse builds out of `ℐ`.
  have hY : RingedSite.inverseImageIdealSheaf.{u} (denseRestrictSite Y K' w) I =
      inverseImageIdealSheaf.{u} (denseReplacementInv Y K' w) I :=
    (RingedSite.inverseImageIdealSheaf_ringedToposHom.{u} (denseRestrictSite Y K' w) I).symm.trans
      (TwoIso.inverseImageIdealSheaf_eq (inverseTwoIsoDenseRestrict Y K' w) I).symm
  -- and the same on `X`, for the ideal `f` builds out of `ℐ`.
  have hX : RingedSite.inverseImageIdealSheaf.{u} (denseRestrictSite X J' v)
        (inverseImageIdealSheaf.{u} f I) =
      inverseImageIdealSheaf.{u} (denseReplacementInv X J' v)
        (inverseImageIdealSheaf.{u} f I) :=
    (RingedSite.inverseImageIdealSheaf_ringedToposHom.{u} (denseRestrictSite X J' v) _).symm.trans
      (TwoIso.inverseImageIdealSheaf_eq (inverseTwoIsoDenseRestrict X J' v) _).symm
  rw [hY, hX, ← RingedSite.inverseImageIdealSheaf_ringedToposHom.{u} hs]
  -- `e^{-1}` followed by `e` returns `ℐ`.
  have hround : inverseImageIdealSheaf.{u} (denseReplacementHom Y K' w)
      (inverseImageIdealSheaf.{u} (denseReplacementInv Y K' w) I) = I :=
    (inverseImageIdealSheaf_comp (denseReplacementInv Y K' w)
        (denseReplacementHom Y K' w) I).trans
      ((TwoIso.inverseImageIdealSheaf_eq (inverseCompTwoIsoId (denseReplacementHom Y K' w)) I).trans
        (inverseImageIdealSheaf_id Y I))
  -- the square, read on sheaves of ideals
  have hsq := TwoIso.inverseImageIdealSheaf_eq τ
    (inverseImageIdealSheaf.{u} (denseReplacementInv Y K' w) I)
  rw [← inverseImageIdealSheaf_comp hs.ringedToposHom (denseReplacementHom X J' v),
    ← inverseImageIdealSheaf_comp (denseReplacementHom Y K' w) f, hround] at hsq
  -- apply `g^{-1}` to both sides and collapse the other round trip
  have hgoal := congrArg
    (fun Q ↦ inverseImageIdealSheaf.{u} (denseReplacementInv X J' v) Q) hsq
  rw [inverseImageIdealSheaf_comp (denseReplacementHom X J' v) (denseReplacementInv X J' v),
    TwoIso.inverseImageIdealSheaf_eq (compInverseTwoIsoId (denseReplacementHom X J' v)),
    inverseImageIdealSheaf_id] at hgoal
  exact hgoal

end AlgebraicGeometry.RingedToposHom

end
