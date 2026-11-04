module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.OneGeneratorSquareShape

/-!
# An almost blowup square with a closed-immersion modification is locally of the one-generator
shape

The second step of the proof of Stacks 0EVI treats an almost blowup square whose modification
`b : X' ⟶ X` is a closed immersion and whose centre is a locally principal closed subscheme, and
says that affine locally on the base such a square is one of the squares of Example 0EVG.  This
file proves exactly that: every point of the base has an affine open neighbourhood over which
the restricted square — the base change of the square along the inclusion of that open, which is
again an almost blowup square by Stacks 0EV7 — has the shape
`AlgebraicGeometry.IsOneGeneratorAlmostBlowUpModel`.

## Main results

* `AlgebraicGeometry.isPrincipal_comap_ideal_top_of_isPrincipal`: the centre of the restriction
  of an ideal sheaf to an affine open on which it is principal is principal.
* `AlgebraicGeometry.exists_affineOpen_isOneGeneratorAlmostBlowUpModel`: every point of the base
  has an affine open neighbourhood over which the restricted square has the one-generator shape.

## Implementation notes

Restricting to an open subscheme is base change along its inclusion, so the restricted square is
an almost blowup square by Stacks 0EV7,
`AlgebraicGeometry.isAlmostBlowUpSquare_baseChange`, with centre the inverse image ideal sheaf
and modification the first projection of the fibre product; the modification stays a closed
immersion because closed immersions are stable under base change.

Local principality of the centre, `Stacks.Divisors.IsLocallyPrincipal`, produces for each point
an affine open on which the ideal of the centre is principal, and
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion` identifies the ideal of
the inverse image ideal sheaf over the whole of that open with the ideal of the centre there, up
to the isomorphism of global sections of an open immersion.  Principality transports along that
isomorphism.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The inverse image of a principal ideal along an isomorphism of rings is principal. -/
public theorem Ideal.isPrincipal_comap_of_commRingCatIso {R S : CommRingCat.{u}} (e : R ≅ S)
    {K : Ideal S} (h : K.IsPrincipal) : (K.comap e.hom.hom).IsPrincipal := by
  obtain ⟨a, ha⟩ := h
  exact ⟨e.inv.hom a, by
    rw [ha, ideal_comap_isoHom_eq_map_isoInv, Ideal.map_span, Set.image_singleton]⟩

/-- **The restriction of an ideal sheaf to an affine open on which it is principal is principal.**
The ideal of global sections of the inverse image ideal sheaf on the open subscheme is the ideal
of the given ideal sheaf there, read through the isomorphism of global sections of the open
immersion. -/
public theorem isPrincipal_comap_ideal_top_of_isPrincipal {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (hprin : (I.ideal U).IsPrincipal) :
    letI : IsAffine (U.1 : Scheme.{u}) := U.2
    ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩).IsPrincipal := by
  let : IsAffine (U.1 : Scheme.{u}) := U.2
  have himg : (U.1.ι ''ᵁ (⊤ : (U.1 : Scheme.{u}).Opens)) = U.1 := U.1.ι_image_top
  have hU : (⟨U.1.ι ''ᵁ (⊤ : (U.1 : Scheme.{u}).Opens),
      (isAffineOpen_top _).image_of_isOpenImmersion U.1.ι⟩ : X.affineOpens) = U :=
    Subtype.ext himg
  have hprin' : (I.ideal ⟨U.1.ι ''ᵁ (⊤ : (U.1 : Scheme.{u}).Opens),
      (isAffineOpen_top _).image_of_isOpenImmersion U.1.ι⟩).IsPrincipal :=
    Eq.mpr (congrArg (fun V : X.affineOpens => (I.ideal V).IsPrincipal) hU) hprin
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I U.1.ι ⟨⊤, isAffineOpen_top _⟩]
  exact Ideal.isPrincipal_comap_of_commRingCatIso (U.1.ι.appIso _).symm hprin'

/-- **An almost blowup square with a closed-immersion modification and a locally principal centre
is affine locally a square of Example 0EVG.** Every point of the base has an affine open
neighbourhood over which the restriction of the square — its base change along the inclusion of
that open — has the shape of Example 0EVG.

This is the affine-local reduction the second step of the proof of Stacks 0EVI performs before
appealing to condition (3). -/
public theorem exists_affineOpen_isOneGeneratorAlmostBlowUpModel {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsClosedImmersion b]
    (h : IsAlmostBlowUpSquare I b) (hI : Stacks.Divisors.IsLocallyPrincipal I) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U.1 : Set X) ∧
      IsOneGeneratorAlmostBlowUpModel (pullback.fst U.1.ι b) (I.comap U.1.ι).subschemeι := by
  obtain ⟨U, hxU, hprin⟩ := hI x
  let : IsAffine (U.1 : Scheme.{u}) := U.2
  let : IsClosedImmersion (pullback.fst U.1.ι b) := inferInstance
  obtain ⟨t, ht⟩ := isPrincipal_comap_ideal_top_of_isPrincipal I U hprin
  exact ⟨U, hxU, isOneGeneratorAlmostBlowUpModel_of_isAlmostBlowUpSquare (I.comap U.1.ι)
    (pullback.fst U.1.ι b) (isAlmostBlowUpSquare_baseChange I b U.1.ι h) t ht⟩

end AlgebraicGeometry

end
