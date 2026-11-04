module

public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.StalkBaseChange
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# The affine dictionary for quasi-coherent ideal sheaves

A quasi-coherent sheaf of ideals `K` on an affine scheme `Spec R` is determined by the single
ideal `K.ideal ⟨⊤, _⟩` of `Γ(Spec R, ⊤)`, hence — transporting along `Scheme.ΓSpecIso R` — by an
ideal `I` of `R`. This file writes the two invariants of `K` that the colength bookkeeping on a
blowup actually consumes in terms of `I`: the support of `K` is the zero locus of `I`, and the
colength of the stalk of `K` at a point `p` is the colength of the localisation of `I` at `p`.

Both are needed to turn computations inside an affine blowup algebra `A[𝔪/x]` — which take place
in a ring, with ordinary ideals — into statements about an ideal sheaf on the blowup of a
two-dimensional regular local ring, which is where the induction of Stacks tag 0AGT runs. The
third result transports a stalk colength along an open immersion, which is what lets a chart
computation be read off at a point of the whole blowup.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_support_iff_le`: a point `p` of `Spec R` lies
  in the support of `K` exactly when the ideal of `R` corresponding to `K` is contained in `p`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.support_eq_zeroLocus`: the support of `K` is the
  `PrimeSpectrum.zeroLocus` of that ideal.
* `Stacks.ResolutionOfSurfaces.CartierDescent.map_stalkIso_stalk`: the stalk of `K` at `p`,
  carried into `Localization.AtPrime p.asIdeal`, is the extension of that ideal.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_eq`: the colength of the
  stalk of `K` at `p` equals the colength, over `Localization.AtPrime p.asIdeal`, of the
  extension of that ideal to the localisation.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_comap_eq_of_isOpenImmersion`:
  for an open immersion `j : Y ⟶ X` the colength of the stalk of `K.comap j` at `z` equals the
  colength of the stalk of `K` at `j z`.

## Implementation notes

Points of `Spec R` are spelled as elements of `PrimeSpectrum R`, as Mathlib does for
`AlgebraicGeometry.Spec.stalkIso`; the two types are definitionally equal, so no coercion
appears in the statements. The ideal of `R` attached to `K` is the image of
`K.ideal ⟨⊤, isAffineOpen_top _⟩` under `(Scheme.ΓSpecIso R).hom`; by
`Ideal.map_comap_of_equiv` that image is also the preimage along `(Scheme.ΓSpecIso R).inv`,
which is the form in which `AlgebraicGeometry.Spec_zeroLocus` states the comparison of
`Scheme.zeroLocus` with `PrimeSpectrum.zeroLocus`.

The support statements rest on `Scheme.IdealSheafData.mem_support_iff_of_mem` at the affine open
`⊤`, so no quasi-coherence bookkeeping is needed. The colength statements transport
`Module.length` along a ring isomorphism with `Module.quotient_length_eq_of_ringEquiv`: for the
affine statement the isomorphism is `AlgebraicGeometry.Spec.stalkIso`, whose compatibility with
the germ at `⊤` is `AlgebraicGeometry.Spec.germ_stalkMapIso_hom`. The open-immersion statement is
the special case of
`Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_comap_of_isIso_stalkMap`, which
asks only that the stalk map be an isomorphism; an open immersion supplies that instance.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {R : CommRingCat.{u}}

/-- The ideal of `R` attached to a quasi-coherent ideal sheaf on `Spec R` is the preimage, along
`(Scheme.ΓSpecIso R).inv`, of its ideal of global sections. -/
public theorem coe_map_ΓSpecIso_hom_ideal_top (K : (Spec R).IdealSheafData) :
    ((Ideal.map (Scheme.ΓSpecIso R).hom.hom (K.ideal ⟨⊤, isAffineOpen_top _⟩) : Ideal R) :
        Set R) =
      (Scheme.ΓSpecIso R).inv ⁻¹' ((K.ideal ⟨⊤, isAffineOpen_top _⟩ : Ideal _) : Set _) := by
  have h : Ideal.map (Scheme.ΓSpecIso R).hom.hom (K.ideal ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.comap (Scheme.ΓSpecIso R).inv.hom (K.ideal ⟨⊤, isAffineOpen_top _⟩) :=
    Ideal.map_comap_of_equiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  rw [h, Ideal.coe_comap]

/-- An ideal sheaf on an affine scheme is the one induced by its ideal of global sections. -/
public theorem ofIdealTop_ideal_top (K : (Spec R).IdealSheafData) :
    Scheme.IdealSheafData.ofIdealTop (K.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩) = K :=
  Scheme.IdealSheafData.ext_of_isAffine (by simp)

/-- **The support of an ideal sheaf on `Spec R` is the zero locus of the corresponding ideal of
`R`.** -/
public theorem support_eq_zeroLocus (K : (Spec R).IdealSheafData) :
    (K.support : Set (Spec R)) =
      PrimeSpectrum.zeroLocus
        ((Ideal.map (Scheme.ΓSpecIso R).hom.hom (K.ideal ⟨⊤, isAffineOpen_top _⟩) : Ideal R) :
          Set R) := by
  rw [show (K.support : Set (Spec R)) = ((Scheme.IdealSheafData.ofIdealTop
        (K.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩)).support : Set (Spec R)) from by
      rw [ofIdealTop_ideal_top],
    Scheme.IdealSheafData.coe_support_ofIdealTop, AlgebraicGeometry.Spec_zeroLocus,
    coe_map_ΓSpecIso_hom_ideal_top]

/-- **A point of `Spec R` lies in the support of an ideal sheaf exactly when the corresponding
ideal of `R` is contained in it.** -/
public theorem mem_support_iff_le (K : (Spec R).IdealSheafData) (p : PrimeSpectrum R) :
    p ∈ (K.support : Set (Spec R)) ↔
      Ideal.map (Scheme.ΓSpecIso R).hom.hom (K.ideal ⟨⊤, isAffineOpen_top _⟩) ≤ p.asIdeal := by
  rw [support_eq_zeroLocus]
  exact (PrimeSpectrum.mem_zeroLocus p _).trans SetLike.coe_subset_coe

/-- The stalk of an ideal sheaf on `Spec R` at `p`, carried along `Spec.stalkIso` into the
localisation of `R` at `p`, is the extension to that localisation of the corresponding ideal
of `R`. -/
public theorem map_stalkIso_stalk (K : (Spec R).IdealSheafData) (p : PrimeSpectrum R) :
    Ideal.map (Spec.stalkIso R p).commRingCatIsoToRingEquiv.toRingHom
        (AlgebraicGeometry.IdealSheafData.stalk K p) =
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal))
        (Ideal.map (Scheme.ΓSpecIso R).hom.hom (K.ideal ⟨⊤, isAffineOpen_top _⟩)) := by
  have h : ((Spec.stalkIso R p).commRingCatIsoToRingEquiv.toRingHom).comp
        ((Spec R).presheaf.germ ⊤ p trivial).hom =
      (algebraMap R (Localization.AtPrime p.asIdeal)).comp (Scheme.ΓSpecIso R).hom.hom := by
    have h2 := congrArg CommRingCat.Hom.hom (Spec.germ_stalkMapIso_hom (R := R) (x := p))
    rwa [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ K p ⟨⊤, isAffineOpen_top _⟩ trivial,
    Ideal.map_map, Ideal.map_map, h]

/-- **The colength of the stalk of an ideal sheaf on `Spec R` is the colength of the localised
ideal.** The stalk of `Spec R` at `p` is the localisation of `R` at `p`, and under that
identification the stalk of the ideal sheaf becomes the extension of the corresponding ideal of
`R`. -/
public theorem length_stalk_quotient_eq (K : (Spec R).IdealSheafData) (p : PrimeSpectrum R) :
    Module.length ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p ⧸ AlgebraicGeometry.IdealSheafData.stalk K p) =
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸
          Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal))
            (Ideal.map (Scheme.ΓSpecIso R).hom.hom (K.ideal ⟨⊤, isAffineOpen_top _⟩))) := by
  rw [← map_stalkIso_stalk K p]
  exact Module.quotient_length_eq_of_ringEquiv _ _

/-- **A stalk colength is unchanged by an open immersion.** For an open immersion `j : Y ⟶ X`
the colength at `z` of the inverse image of an ideal sheaf `K` on `X` equals the colength of `K`
at `j z`, because an open immersion is an isomorphism on every local ring. -/
public theorem length_stalk_quotient_comap_eq_of_isOpenImmersion {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (K : X.IdealSheafData) (z : Y) :
    Module.length (Y.presheaf.stalk z)
        (Y.presheaf.stalk z ⧸ AlgebraicGeometry.IdealSheafData.stalk (K.comap j) z) =
      Module.length (X.presheaf.stalk (j.base z))
        (X.presheaf.stalk (j.base z) ⧸
          AlgebraicGeometry.IdealSheafData.stalk K (j.base z)) :=
  length_stalk_quotient_comap_of_isIso_stalkMap j K z inferInstance

end Stacks.ResolutionOfSurfaces.CartierDescent

end
