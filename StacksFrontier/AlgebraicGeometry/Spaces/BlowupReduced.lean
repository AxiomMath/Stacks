module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Reducedness of a blowup of an algebraic space

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `Z ⊆ X` be the closed
subspace cut out by a quasi-coherent sheaf of ideals.  Stacks 085W says that if `X` is reduced
then so is the blowup `X'` of `X` in `Z`.

Reducedness of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of Stacks 03E6 applied to
`AlgebraicGeometry.IsReduced`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/Properties/Reduced.lean`.  The blowup is named by
its universal property, `AlgebraicGeometry.Space.IsBlowupAlong` of Stacks 085U, with the centre
a closed subspace; that is the library's convention for blowups of algebraic spaces, and the
module documentation of `StacksFrontier/AlgebraicGeometry/Spaces/AdmissibleBlowup.lean` explains
why a closed subspace and a universal property stand in for the ideal sheaf and the
construction of Stacks 085Q.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_isPullback_of_isEtale_of_isSurjective`: reducedness of
  an algebraic space passes from a surjective étale base change to the target.
* `AlgebraicGeometry.Space.isReduced_of_isBlowupAlong` is **Stacks 085W**, carrying the one
  input the library lacks as an explicit hypothesis; see "What is assumed".

## Implementation notes

The proof is the source's.  A surjective étale chart `a : U ⟶ X` by a scheme `U` of the site is
part of the datum; blowing up commutes with flat base change, so the projection `W ⟶ U` out of
`W = U ×_X X'` is the blowup of `U` in the inverse image of `Z`, which is
`AlgebraicGeometry.Space.isBlowupAlong_preimage_of_isPullback_of_isFlat` (Stacks 085S) applied
to `a`, flat because étale.  The scheme case is `AlgebraicGeometry.isReduced_blowUp`
(Stacks 0808).  Reducedness then returns to `X'` along `W ⟶ X'`, which is a base change of `a`
and so surjective and étale, by `AlgebraicGeometry.Space.isReduced_of_flat_of_surjective`
(Stacks 06MI).

## What is assumed

The source reads the scheme case off the construction of Stacks 085Q, which builds the blowup
as the relative `Proj` of the Rees algebra and in particular shows that the blowup of a scheme
is a scheme.  For algebraic spaces this library has neither Stacks 085Q nor the relative `Proj`
of Stacks 084A and 084B that it rests on, so nothing here identifies the blowup of a *scheme*
chart, taken in the category of algebraic spaces, with the scheme `AlgebraicGeometry.blowUp` of
Stacks 01OG.  That identification is the hypothesis `hrep` of
`AlgebraicGeometry.Space.isReduced_of_isBlowupAlong`: some blowup of the chart `U` in the
inverse image of `Z` is representable by a scheme isomorphic to a scheme blowup of `U`.

The hypothesis is upstream of the conclusion and strictly weaker than it: it is a
representability statement, it says nothing about reducedness, and it is the content of
Stacks 085Q, which is logically prior to Stacks 085W.  Once Stacks 085Q is available it is
discharged by exhibiting that construction.  The attribute's clause records the restriction.

`hrep` asks only for *some* blowup of the chart with that property, not for the particular
fibre product `W`: any two blowups of `U` in the same centre are isomorphic over `U` by
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`, and the proof passes along that
isomorphism.  It also does not ask that the scheme ideal cut out the inverse image of `Z`,
because Stacks 0808 reduces *every* blowup of a reduced scheme, whatever its centre.

## References

* [Stacks Project, Tag 085W](https://stacks.math.columbia.edu/tag/085W)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 0808](https://stacks.math.columbia.edu/tag/0808)
* [Stacks Project, Tag 06MI](https://stacks.math.columbia.edu/tag/06MI)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Reducedness of an algebraic space over `S` passes from a surjective étale base change to
the target: for a cartesian square with legs `q : W ⟶ U` and `r : W ⟶ X'` over a surjective
étale `a : U ⟶ X` and an arbitrary `b : X' ⟶ X`, the space `X'` is reduced as soon as `W` is.

The morphism `r` is a base change of `a`, hence surjective and étale, hence surjective and
flat, so this is Stacks 06MI. -/
theorem isReduced_of_isPullback_of_isEtale_of_isSurjective
    {X X' U W : AlgebraicSpaces B S hS} {a : U ⟶ X} {b : X' ⟶ X}
    {q : W ⟶ U} {r : W ⟶ X'} (sq : IsPullback q r a b)
    (haE : IsEtale B S hS a.hom) (haS : IsSurjective B S hS a.hom)
    (hW : HasEtaleLocalProperty B S hS W.1 (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS X'.1 (fun T : Scheme.{u} => IsReduced T) :=
  isReduced_of_flat_of_surjective B S hS W.2 X'.2 r.hom
    (isFlat_of_isEtale B S hS (isEtale_of_isPullback B S hS q r a b sq haE))
    (isSurjective_of_isPullback B S hS sq haS) hW

/-- **Stacks 085W**, with the étale-chart representability of Stacks 085Q carried as a
hypothesis.

Let `X` be a reduced algebraic space over `S`, let `Z ⊆ X` be the closed subspace cut out by a
quasi-coherent sheaf of ideals and let `b : X' ⟶ X` be the blowup of `X` in `Z`.  Then `X'` is
reduced.

The chart datum is the source's: a surjective étale morphism `a : U ⟶ X` from a scheme `U` of
the site, and the fibre product `W = U ×_X X'` as a cartesian square.  The hypothesis `hrep`
supplies what Stacks 085Q would: some blowup of `U` in the inverse image of `Z` is
representable by a scheme isomorphic to a scheme blowup of `U`.  See the module documentation
for why that hypothesis is upstream of this conclusion. -/
@[stacks 085W "given the étale-chart representability of the blowup supplied by Stacks 085Q"]
theorem isReduced_of_isBlowupAlong
    {X X' W : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T))
    (V : BigFppfOver B S hS) (a : schemeSpace V ⟶ X)
    (haE : IsEtale B S hS a.hom) (haS : IsSurjective B S hS a.hom)
    {q : W ⟶ schemeSpace V} {r : W ⟶ X'} (sq : IsPullback q r a b)
    (hrep : ∃ (Y : AlgebraicSpaces B S hS) (p : Y ⟶ schemeSpace V),
      IsBlowupAlong B S hS (preimageClosedSubspace a Z) p ∧
      ∃ (V' : BigFppfOver B S hS) (_ : Y.1 ≅ yoneda.obj V')
        (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData),
        Nonempty ((BigFppfOver.toScheme B S hS).obj V' ≅ blowUp I)) :
    HasEtaleLocalProperty B S hS X'.1 (fun T : Scheme.{u} => IsReduced T) := by
  obtain ⟨Y, p, hp, V', eY, I, ⟨ei⟩⟩ := hrep
  have hVred : IsReduced ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun T : Scheme.{u} => IsReduced T) X.2).mp hX
      V a.hom (presheaf_etale_of_isEtale B S hS (U := V) haE)
  have hblow : IsReduced (blowUp I) := isReduced_blowUp I
  have hV'red : IsReduced ((BigFppfOver.toScheme B S hS).obj V') :=
    isReduced_of_isOpenImmersion ei.hom
  have hq : IsBlowupAlong B S hS (preimageClosedSubspace a Z) q :=
    isBlowupAlong_preimage_of_isPullback_of_isFlat (isFlat_of_isEtale B S hS haE) hb sq
  obtain ⟨e, -⟩ := hq.exists_iso hp
  have eW : W.1 ≅ yoneda.obj V' := (ObjectProperty.ι _).mapIso e ≪≫ eY
  exact isReduced_of_isPullback_of_isEtale_of_isSurjective B S hS sq haE haS
    (hasEtaleLocalProperty_of_representable B S hS W.1
      (fun T : Scheme.{u} => IsReduced T) V' eW hV'red)

end AlgebraicGeometry.Space

end
