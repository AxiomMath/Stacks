module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupDivisorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupUniversalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback

/-!
# Composing two blowups of an algebraic space

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `Z, Y ⊆ X` be closed
subspaces.  Let `b : X' ⟶ X` be the blowup of `X` in `Z` and let `b' : X'' ⟶ X'` be the blowup
of `X'` in the inverse image of `Y`.  Stacks Tag 085Y asserts that the composite `b' ≫ b` is the
blowup of `X` in the sum `Z + Y` (the closed subspace cut out by the product of the defining
ideals, `AlgebraicGeometry.Space.sumClosedSubspaces`, Stacks Tag 083U).

## What is proved here

The finality half of this statement — that every morphism to `X` along which `Z + Y` pulls back
to an effective Cartier divisor factors uniquely through `b' ≫ b` — is
`AlgebraicGeometry.Space.existsUnique_lift_comp_of_isBlowupAlong`, proved from the universal
property of each factor (Stacks Tag 085U) together with the split and recombination of
pullback-definedness along a sum (Stacks Tags 083W and 0840).  It assumes of the two blowups
only that they are blowups, in the sense of that universal property.

The membership half — that `Z + Y` itself pulls back to an effective Cartier divisor along
`b' ≫ b` — splits into two pieces after the same splitting of the sum: that the inverse image of
`Y` pulls back along `b'` (this is the membership half of `b'` itself) and that the inverse image
of `Z` pulls back along `b'` (Stacks Tag 085X: a blowup pulls back *any* effective Cartier
divisor, not only the one it is the blowup of).  Tag 085X is available in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupDivisorPullback.lean` for a blowup named by the
universal property, as `AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong`; it carries
the construction data of Stacks 085Q for the centre, because what it compares the blowup against
is the blowup that construction builds.  Supplying it closes Stacks 085Y, which is therefore
proved here for two blowups both named only by the universal property, with that construction
data for the second centre carried along and occurring nowhere in the conclusion.

The two halves stated separately,
`AlgebraicGeometry.Space.isPullbackDefined_comp_of_isBlowupAlong` and
`AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong`, keep the Tag 085X fact as an
explicit hypothesis `h085X`, in exactly the generic form in which it is consumed.  They are not
restated in terms of the construction data, because that trade is not a strengthening: a caller
holding `h085X` and no étale presentation of `X'` can use them and could not use the
construction-data form.

## Main results

* `AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong'`: **Stacks 085Y.**  For `b` a
  blowup of `X` in `Z` and `b'` a blowup of `X'` in `b⁻¹(Y)`, the composite `b' ≫ b` is the
  blowup of `X` in `Z + Y`.
* `AlgebraicGeometry.Space.exists_iso_blowup_comp_of_isBlowupAlong'`: the same statement in the
  source's phrasing, as an isomorphism over `X` with any blowup of `X` in `Z + Y`.
* `AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'_comp_of_isBlowupAlong`: the instance in
  which `b'` is the blowup *constructed* in Stacks 085Q — the source's own naming of the second
  blowup — where nothing at all is assumed of `b'`.
* `AlgebraicGeometry.Space.existsUnique_lift_comp_of_isBlowupAlong`: the finality half of
  Stacks 085Y, for two arbitrary blowups.
* `AlgebraicGeometry.Space.isPullbackDefined_comp_of_isBlowupAlong`: the membership half of
  Stacks 085Y, for two arbitrary blowups, given the Tag 085X fact for the first exceptional
  divisor and the second blowup.
* `AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong`: the two assembled, for two
  arbitrary blowups, still given that same Tag 085X fact.

## References

* [Stacks Project, Tag 085Y](https://stacks.math.columbia.edu/tag/085Y)
* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 083W](https://stacks.math.columbia.edu/tag/083W)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X X' X'' : AlgebraicSpaces B S hS}

/-- The inverse image of a sum of closed subspaces along `f` is an effective Cartier divisor
iff the sum of the inverse images is. -/
private theorem isPullbackDefined_sum_iff {V : AlgebraicSpaces B S hS} (f : V ⟶ X)
    (Z Y : ClosedSubspaces B S hS X.1) :
    IsPullbackDefined B S hS f (sumClosedSubspaces B S hS X Z Y) ↔
      IsEffectiveCartierDivisor B S hS V (sumClosedSubspaces B S hS V
        (preimageClosedSubspace f Z) (preimageClosedSubspace f Y)) := by
  exact Eq.to_iff (congrArg (IsEffectiveCartierDivisor B S hS V)
    (preimage_sumClosedSubspaces B S hS f Z Y))

/-- **The finality half of Stacks 085Y, unconditionally.**  Let `b : X' ⟶ X` be the blowup of
`X` in the closed subspace `Z` and let `b' : X'' ⟶ X'` be the blowup of `X'` in the inverse
image of the closed subspace `Y ⊆ X`.  Then every morphism `w : W ⟶ X` along which `Z + Y`
pulls back to an effective Cartier divisor on `W` admits exactly one lift to `X''` commuting
with the composite `b' ≫ b`.

The sum splits by Tag 083W into pullback-definedness of `Z` and of `Y` along `w`; the first
lifts through `b` by Tag 085U to `f₁ : W ⟶ X'`, and the inverse image of `Y` along `w` agrees
with the inverse image of `Y`'s pullback to `X'` along `f₁` because `f₁ ≫ b = w`, so the second
lifts through `b'` by Tag 085U again. -/
theorem existsUnique_lift_comp_of_isBlowupAlong
    {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    {b' : X'' ⟶ X'}
    (hb' : IsBlowupAlong B S hS
      ⟨Y.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Y.1 X.2 X'.2 Y.2⟩ b')
    {W : AlgebraicSpaces B S hS} (w : W ⟶ X)
    (hw : IsPullbackDefined B S hS w (sumClosedSubspaces B S hS X Z Y)) :
    ∃! l : W ⟶ X'', l ≫ (b' ≫ b) = w := by
  have hwsplit := (isPullbackDefined_sum_iff w Z Y).1 hw
  have hwZ : IsPullbackDefined B S hS w Z :=
    isEffectiveCartierDivisor_left_of_sumClosedSubspaces B S hS W _ _ hwsplit
  have hwY : IsPullbackDefined B S hS w Y :=
    isEffectiveCartierDivisor_right_of_sumClosedSubspaces B S hS W _ _ hwsplit
  obtain ⟨f₁, hf₁, hf₁u⟩ := hb.existsUnique_lift w hwZ
  have heq : (Y.1.preimage b.hom).preimage f₁.hom = Y.1.preimage w.hom := by
    rw [← Subfunctor.preimage_comp Y.1 f₁.hom b.hom,
      ← ObjectProperty.FullSubcategory.comp_hom, hf₁]
  have hf₁Y' : IsPullbackDefined B S hS f₁
      ⟨Y.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Y.1 X.2 X'.2 Y.2⟩ :=
    isEffectiveCartierDivisor_of_subfunctor_eq heq hwY
  obtain ⟨f₂, hf₂, hf₂u⟩ := hb'.existsUnique_lift f₁ hf₁Y'
  refine ⟨f₂, show f₂ ≫ b' ≫ b = w by rw [← Category.assoc, hf₂, hf₁], ?_⟩
  intro l hl
  have hl' : l ≫ b' ≫ b = w := hl
  have hlb : l ≫ b' = f₁ :=
    hf₁u (l ≫ b') (show (l ≫ b') ≫ b = w by rw [Category.assoc]; exact hl')
  exact hf₂u l hlb

/-- **The membership half of Stacks 085Y, given Tag 085X.**  With `b`, `b'` as above, if the
inverse image of `Z` along `b`, pulled further back along `b'`, is again an effective Cartier
divisor — the fact supplied by Tag 085X applied to the blowup `b'` and the effective Cartier
divisor `Z.preimage b` — then the inverse image of `Z + Y` along the composite `b' ≫ b` is an
effective Cartier divisor on `X''`.

The pullback of `Z + Y` along `b' ≫ b` is, by Tag 083U/0840 applied twice, the sum of the
pullback of `Z.preimage b` along `b'` (the hypothesis) and the pullback of `Y.preimage b` along
`b'` (unconditional, it is the membership half of `hb'` itself); the two recombine by Tag 083V. -/
theorem isPullbackDefined_comp_of_isBlowupAlong
    {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (_hb : IsBlowupAlong B S hS Z b)
    {b' : X'' ⟶ X'}
    (hb' : IsBlowupAlong B S hS
      ⟨Y.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Y.1 X.2 X'.2 Y.2⟩ b')
    (h085X : IsPullbackDefined B S hS b'
      ⟨Z.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Z.1 X.2 X'.2 Z.2⟩) :
    IsPullbackDefined B S hS (b' ≫ b) (sumClosedSubspaces B S hS X Z Y) := by
  have h := (isPullbackDefined_sum_iff b' (preimageClosedSubspace b Z)
    (preimageClosedSubspace b Y)).2
    (isEffectiveCartierDivisor_sumClosedSubspaces B S hS X'' _ _ h085X hb'.isPullbackDefined)
  replace h := (congrArg (IsPullbackDefined B S hS b')
    (preimage_sumClosedSubspaces B S hS b Z Y).symm).mp h
  refine isEffectiveCartierDivisor_of_subfunctor_eq (D' :=
    ⟨((sumClosedSubspaces B S hS X Z Y).1.preimage b.hom).preimage b'.hom, _⟩) ?_ h
  exact Subfunctor.preimage_comp (sumClosedSubspaces B S hS X Z Y).1 b'.hom b.hom

/-- **Stacks 085Y, given Tag 085X.**  Let `b : X' ⟶ X` be the blowup of `X` in the closed
subspace `Z` and let `b' : X'' ⟶ X'` be the blowup of `X'` in the inverse image of the closed
subspace `Y ⊆ X`.  If the inverse image of `Z` along `b`, pulled further back along `b'`, is
again an effective Cartier divisor — the fact supplied by Tag 085X — then the composite
`b' ≫ b` is the blowup of `X` in the sum `Z + Y`.

This is Stacks Tag 085Y, assembled from its finality half
(`AlgebraicGeometry.Space.existsUnique_lift_comp_of_isBlowupAlong`, unconditional) and its
membership half (`AlgebraicGeometry.Space.isPullbackDefined_comp_of_isBlowupAlong`, which is
where Tag 085X enters) through the lifting-property characterization of Tag 085U. -/
theorem isBlowupAlong_comp_of_isBlowupAlong
    {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    {b' : X'' ⟶ X'}
    (hb' : IsBlowupAlong B S hS
      ⟨Y.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Y.1 X.2 X'.2 Y.2⟩ b')
    (h085X : IsPullbackDefined B S hS b'
      ⟨Z.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Z.1 X.2 X'.2 Z.2⟩) :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS X Z Y) (b' ≫ b) :=
  isBlowupAlong_of_existsUnique_lift
    (isPullbackDefined_comp_of_isBlowupAlong hb hb' h085X)
    (fun _ w hw => existsUnique_lift_comp_of_isBlowupAlong hb hb' w hw)

section Constructed

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Stacks 085Y.**  Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`Z, Y ⊆ X` be closed subspaces.  Let `b : X' ⟶ X` be a blowup of `X` in `Z` and let
`b' : X'' ⟶ X'` be a blowup of `X'` in the inverse image `b⁻¹(Y)`, both in the sense of the
universal property of Stacks 085U.  Then the composite `b' ≫ b` is the blowup of `X` in the sum
`Z + Y`, the closed subspace cut out by the product of the two defining ideals (Stacks 083U).

Read through that universal property, which is how `AlgebraicGeometry.Space.IsBlowupAlong` says
"is the blowup", the conclusion asserts both that the blowup of `X` in `Z + Y` exists and that
it is `b' ≫ b`; that is the source's "`X'' ⟶ X` is canonically isomorphic to the blowing up of
`X` in `𝓘𝓙`", and the isomorphism itself is
`AlgebraicGeometry.Space.exists_iso_blowup_comp_of_isBlowupAlong'`.

The hypotheses on the two blowups are the source's own: each is named only by being a blowup of
its centre.  What is carried beyond them is the construction data of Stacks 085Q for the second
centre `b⁻¹(Y)` — an étale presentation `P` of `X'`, the `HasSheafify` universe choice, and the
three `B.Contains` side conditions on the relative `Proj`s which
`AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks for.  That data produces the
*constructed* blowup of `X'` in `b⁻¹(Y)`, which is what Stacks 085X is proved for; none of it
occurs in the conclusion, and no input of Stacks 085Y is assumed.

The proof is `AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong` with its Tag 085X
hypothesis discharged by `AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong`, applied
to the effective Cartier divisor `b⁻¹(Z)` on `X'` — effective Cartier because `b` is the blowup
of `Z`, so this is `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined` of `hb`. -/
@[stacks 085Y "with no assumed inputs beyond the Stacks 085Q construction data P, hcU, hcR and \
hcRR for the second centre, which does not occur in the conclusion: for b a blowup of X in Z \
and b' a blowup of X' in the inverse image of Y, both in the sense of the Stacks 085U universal \
property, the composite b' followed by b is the blowup of X in the sum Z + Y"]
theorem isBlowupAlong_comp_of_isBlowupAlong'
    {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    {b' : X'' ⟶ X'} (hb' : IsBlowupAlong B S hS (preimageClosedSubspace b Y) b')
    (P : Presentation B S hS X'.obj X'.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj) :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS X Z Y) (b' ≫ b) :=
  isBlowupAlong_comp_of_isBlowupAlong hb hb'
    (isPullbackDefined_of_isBlowupAlong (preimageClosedSubspace b Y) P hcU hcR hcRR hb'
      (preimageClosedSubspace b Z) hb.isPullbackDefined)

/-- **Stacks 085Y in the source's phrasing: the canonical isomorphism.**  With `b` and `b'` as
in `AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong'`, every blowup `c : W ⟶ X` of
`X` in the sum `Z + Y` is isomorphic to `X''` over `X`, compatibly with `c` and with the
composite `b' ≫ b`.

Blowups in a fixed centre are isomorphic over the base
(`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`), so this is a reading of
`AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong'`, which is where Tag 085Y is
registered; it carries no tag of its own. -/
theorem exists_iso_blowup_comp_of_isBlowupAlong'
    {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    {b' : X'' ⟶ X'} (hb' : IsBlowupAlong B S hS (preimageClosedSubspace b Y) b')
    (P : Presentation B S hS X'.obj X'.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj)
    (W : AlgebraicSpaces B S hS) (c : W ⟶ X)
    (hc : IsBlowupAlong B S hS (sumClosedSubspaces B S hS X Z Y) c) :
    ∃ e : X'' ≅ W, e.hom ≫ c = b' ≫ b :=
  (isBlowupAlong_comp_of_isBlowupAlong' hb hb' P hcU hcR hcRR).exists_iso hc

/-- **Stacks 085Y with the second blowup the one constructed in Stacks 085Q.**  The special case
of `AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong'` in which `b'` is
`AlgebraicGeometry.Space.blowUpAlongHom'`, whose being a blowup of `b⁻¹(Y)` is Stacks 085U
(`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`) rather than a hypothesis.  This is the
source's own naming of the second blowup — "let `b' : X'' → X'` be the blowing up of `X'` in
`b⁻¹𝓙 𝒪_{X'}`" — and it needs no hypothesis at all beyond the construction data that names it.

Tag 085Y is registered on `AlgebraicGeometry.Space.isBlowupAlong_comp_of_isBlowupAlong'`, of
which this is an instance, so this carries no tag of its own. -/
theorem isBlowupAlong_blowUpAlongHom'_comp_of_isBlowupAlong
    {Z Y : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (P : Presentation B S hS X'.obj X'.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace b Y))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace b Y)) P).relativeProj) :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS X Z Y)
      (blowUpAlongHom' (preimageClosedSubspace b Y) P hcU hcR hcRR ≫ b) :=
  isBlowupAlong_comp_of_isBlowupAlong' hb
    (isBlowupAlong_blowUpAlongHom' (preimageClosedSubspace b Y) P hcU hcR hcRR) P hcU hcR hcRR


end Constructed

end AlgebraicGeometry.Space

end
