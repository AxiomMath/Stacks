module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartReesUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupComposite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence

/-!
# Blowups of an algebraic space in an arbitrary closed subspace

Let `S` be a scheme and let `X` be an algebraic space over `S`.  For every closed subspace
`Z ⊆ X` the blowup `b : X' ⟶ X` of `X` along `Z` exists, as the relative `Proj` of the Rees
algebra `⨁_{n ≥ 0} 𝓘_Zⁿ`, and it is final among the algebraic spaces over `X` on which the
inverse image of `Z` is an effective Cartier divisor.  This file records the consequences of
that for the blowups of Stacks 085X and 085Y:

* for every effective Cartier divisor `D` on `X` the pullback `b⁻¹(D)` is defined, that is,
  `b⁻¹(D)` is an effective Cartier divisor on `X'` (Stacks 085X);
* if `b : X' ⟶ X` is the blowup of `X` in `Z` and `b' : X'' ⟶ X'` the blowup of `X'` in
  `b⁻¹(Y)`, then `b' ≫ b` is the blowup of `X` in `Z + Y`, the closed subspace cut out by the
  product of the two ideal sheaves (Stacks 085Y).

Each is stated for blowups named by the universal property of Stacks 085U alone,
`AlgebraicGeometry.Space.IsBlowupAlong`, with no hypothesis on `X`, on `Z` or on the site.

## Main results

* `AlgebraicGeometry.Space.exists_isBlowupAlong`: the blowup of an algebraic space in an
  arbitrary closed subspace exists.
* `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined_of_isEffectiveCartierDivisor`:
  **Stacks 085X**.
* `AlgebraicGeometry.Space.IsBlowupAlong.comp_sumClosedSubspaces`: **Stacks 085Y**.
* `AlgebraicGeometry.Space.IsBlowupAlong.exists_iso_comp_sumClosedSubspaces`: Stacks 085Y in
  the source's phrasing, as an isomorphism over `X` with any blowup of `X` in `Z + Y`.

## Implementation notes

The construction of Stacks 085Q, `AlgebraicGeometry.Space.blowUpAlongHom'`, takes an étale
presentation of `X`, sheafification of presheaves of sets on the big fppf site, and three size
conditions saying that the relative `Proj`s of the Rees algebras on the presenting scheme, on
the relation scheme and on the scheme of composable pairs are objects of the site.  None of
these is a restriction: every algebraic space has an étale presentation
(`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace`, Stacks 0263), the big fppf site is
essentially small so sheafification exists (`AlgebraicGeometry.hasSheafify_bigFppfOver`), and
the relative `Proj` of the Rees algebra of a quasi-coherent sheaf of ideals is no larger than
its base, so each size condition holds for an arbitrary centre
(`AlgebraicGeometry.Space.contains_relativeProj_reesChartSituation` and its two companions).
So the construction applies to every closed subspace, and with it the comparison arguments of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupDivisorPullback.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupComposite.lean` reach every blowup.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 085Y](https://stacks.math.columbia.edu/tag/085Y)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X X' X'' : AlgebraicSpaces B S hS}

/-- **The blowup of an algebraic space in an arbitrary closed subspace exists.**  For every
closed subspace `Z ⊆ X` there are an algebraic space `X'` and a morphism `b : X' ⟶ X` which is
the blowup of `X` in `Z`, in the sense of the universal property of Stacks 085U.

The blowup is the one Stacks 085Q constructs, `AlgebraicGeometry.Space.blowUpAlongHom'`, on the
chosen presentation of `X`; the three size conditions of that construction hold for every
centre by `AlgebraicGeometry.Space.contains_relativeProj_reesChartSituation` and its two
companions, and being the blowup is Stacks 085U,
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`. -/
theorem exists_isBlowupAlong (Z : ClosedSubspaces B S hS X.1) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsBlowupAlong B S hS Z b := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  let P : Presentation B S hS X.obj X.property :=
    presentationOfIsAlgebraicSpace B S hS X.obj X.property
  exact ⟨_, _, isBlowupAlong_blowUpAlongHom' Z P
    (contains_relativeProj_reesChartSituation _ _ P)
    (contains_relativeProj_reesRelationSituation _ _ P)
    (contains_relativeProj_reesDoubleSituation _ _ P)⟩

namespace IsBlowupAlong

/-- **Stacks 085X.**  Let `X` be an algebraic space over a scheme `S` and let `b : X' ⟶ X` be a
blowup of `X` in a closed subspace `Z`.  For every effective Cartier divisor `D` on `X` the
pullback `b⁻¹(D)` is defined in the sense of Stacks 083Y: the inverse image of `D` along `b` is
an effective Cartier divisor on `X'`.

Nothing is assumed of `b` beyond being a blowup of `X` in `Z`, and nothing of `D` beyond being
an effective Cartier divisor.  The proof is
`AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong`, which compares `b` with the
blowup constructed in Stacks 085Q; the construction data it asks for is supplied for every
centre as in `AlgebraicGeometry.Space.exists_isBlowupAlong`. -/
theorem isPullbackDefined_of_isEffectiveCartierDivisor {Z : ClosedSubspaces B S hS X.1}
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    IsPullbackDefined B S hS b D := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  let P : Presentation B S hS X.obj X.property :=
    presentationOfIsAlgebraicSpace B S hS X.obj X.property
  exact isPullbackDefined_of_isBlowupAlong Z P
    (contains_relativeProj_reesChartSituation _ _ P)
    (contains_relativeProj_reesRelationSituation _ _ P)
    (contains_relativeProj_reesDoubleSituation _ _ P) hb D hD

/-- **Stacks 085Y.**  Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`Z, Y ⊆ X` be closed subspaces, with quasi-coherent ideal sheaves `𝓘` and `𝓙`.  Let
`b : X' ⟶ X` be the blowup of `X` in `Z` and let `b' : X'' ⟶ X'` be the blowup of `X'` in the
inverse image `b⁻¹(Y)`, the closed subspace cut out by `b⁻¹𝓙 𝒪_{X'}`.  Then the composite
`b' ≫ b` is the blowup of `X` in `Z + Y`, the closed subspace cut out by `𝓘𝓙` (Stacks 083U).

Both blowups are named only by the universal property of Stacks 085U, and so is the
conclusion; "canonically isomorphic to the blowing up of `X` in `𝓘𝓙`" is
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso_comp_sumClosedSubspaces`.  The proof is the
source's: finality of `b' ≫ b` comes from finality of `b` and of `b'`
(`AlgebraicGeometry.Space.existsUnique_lift_comp_of_isBlowupAlong`), and the inverse image of
`Z + Y` along `b' ≫ b` is the sum of the effective Cartier divisor `b'⁻¹(b⁻¹Y)` and of the
pullback along `b'` of the effective Cartier divisor `b⁻¹Z`, which is defined by Stacks 085X,
`AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined_of_isEffectiveCartierDivisor`. -/
theorem comp_sumClosedSubspaces {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b) {b' : X'' ⟶ X'}
    (hb' : IsBlowupAlong B S hS (preimageClosedSubspace b Y) b') :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS X Z Y) (b' ≫ b) :=
  isBlowupAlong_comp_of_isBlowupAlong hb hb'
    (hb'.isPullbackDefined_of_isEffectiveCartierDivisor (preimageClosedSubspace b Z)
      hb.isPullbackDefined)

/-- **Stacks 085Y in the source's phrasing.**  With `b` and `b'` as in
`AlgebraicGeometry.Space.IsBlowupAlong.comp_sumClosedSubspaces`, every blowup `c : W ⟶ X` of `X`
in `Z + Y` is isomorphic to `X''` over `X`, compatibly with `c` and with `b' ≫ b`.  The
isomorphism is unique, both being final objects of the category of Stacks 085U. -/
theorem exists_iso_comp_sumClosedSubspaces {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b) {b' : X'' ⟶ X'}
    (hb' : IsBlowupAlong B S hS (preimageClosedSubspace b Y) b')
    {W : AlgebraicSpaces B S hS} {c : W ⟶ X}
    (hc : IsBlowupAlong B S hS (sumClosedSubspaces B S hS X Z Y) c) :
    ∃ e : X'' ≅ W, e.hom ≫ c = b' ≫ b :=
  (hb.comp_sumClosedSubspaces hb').exists_iso hc

end IsBlowupAlong

end AlgebraicGeometry.Space

end
