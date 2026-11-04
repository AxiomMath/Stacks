module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.PurelyTranscendental

/-!
# The residue extension of a morphism of spectra, read off the primes

A point of `Spec R` is a prime of `R`, and the morphism of spectra induced by an algebra map
`R → B` sends a prime `lp` of `B` to the prime of `R` below it. Over such a pair of points there
are two extensions of residue fields: the scheme-theoretic one, which `Scheme.residueFieldMap`
gives and which `AlgebraicGeometry.OneStepDevissageAt` records, and the ideal-theoretic one
`Ideal.ResidueField.map`, which is the shape in which the algebraic dévissage data of
Stacks 05HZ carries it. This file transports pure transcendence from the second to the first.

This is the pointed half of the dictionary of Stacks 05I0 (2) in the direction algebra ⇒
geometry, the direction in which an algebraic complete dévissage of `N/S/R` at a prime produces
the scheme-theoretic one-step dévissage of Stacks 05H5 on spectra; the opposite direction is
`AlgebraicGeometry.purelyTranscendental_residueField_appTop`.

## Main results

* `AlgebraicGeometry.specMap_algebraMap_apply`: **the morphism of spectra induced by an algebra
  map sends a prime to the prime it lies over.** This produces the equality of points that the
  residue field comparison needs.
* `AlgebraicGeometry.purelyTranscendental_residueField_specMap`: **if the extension of the
  residue fields of two primes, one lying over the other, is purely transcendental, then so is
  the scheme-theoretic residue extension of the induced morphism of spectra at the upper
  prime.** This is Stacks 05HZ (1) read on spectra.

## Implementation notes

The comparison of the two residue fields at a point of `Spec R` is Mathlib's
`AlgebraicGeometry.Scheme.Spec.residueFieldIso`, and the compatibility of the two residue field
maps with it is `AlgebraicGeometry.specResidueFieldMap_bridge`. Rather than invoking that bridge,
the proof below assembles the commutative square of which it is an avatar directly from the
structure maps of the two residue fields: the two composites `R → κ(lp)` agree because
`AlgebraicGeometry.Scheme.Spec.algebraMap_residueFieldIso_inv` identifies the comparison
isomorphism with evaluation at the point, and evaluation is natural. Assembled this way the
square starts at the given prime `r` rather than at `lp ∩ R`, so the residue field of the second
prime is never written down and no cast between the two is needed. Pure transcendence then moves
across the two comparison isomorphisms by `PurelyTranscendental.of_ringEquiv_square`, whose
square of ring maps is checked on the image of `R`, which suffices by
`Ideal.ResidueField.ringHom_ext`. The two isomorphisms enter that square as ring equivalences,
so the last step unfolds `CategoryTheory.Iso.commRingCatIsoToRingEquiv` to recover the underlying
ring maps of the square: the two residue fields carry both the field structure that
`PurelyTranscendental` uses and the ring structure of the category, and the lemma comparing the
equivalence with its ring map is stated for the second.

The isomorphism of residue fields at the two equal points `Spec.map φ lp` and `r`, which is the
factor `AlgebraicGeometry.Scheme.residueFieldCongr` of the geometric algebra structure, is a
transport along an equality of points; it is absorbed into evaluation by an auxiliary step whose
only content is `subst`.

Both points are written `show Spec _ from ⟨_, _⟩` rather than `(⟨_, _⟩ : Spec _)`: the latter
elaborates to a term of type `PrimeSpectrum _` rather than of the carrier of the scheme `Spec _`,
and instance synthesis, which does not unfold `Spec`, then fails to find the field structure on
the residue field at that point.

## References

* [Stacks Project, Tag 05H5](https://stacks.math.columbia.edu/tag/05H5)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- The morphism of spectra induced by the structure map of an algebra sends a prime of the
algebra to the prime of the base it lies over. -/
public theorem AlgebraicGeometry.specMap_algebraMap_apply {R B : Type u} [CommRing R]
    [CommRing B] [Algebra R B] (lp : Ideal B) [lp.IsPrime] (r : Ideal R) [r.IsPrime]
    (hover : lp.LiesOver r) :
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (show Spec (CommRingCat.of B) from ⟨lp, ‹_›⟩) =
      show Spec (CommRingCat.of R) from ⟨r, ‹_›⟩ :=
  PrimeSpectrum.ext hover.over.symm

/-- **Stacks 05HZ (1), read on spectra.** Let `B` be an `R`-algebra, `lp` a prime of `B` and `r`
the prime of `R` it lies over. If the extension `κ(r) ⊆ κ(lp)` of the residue fields of the two
primes is purely transcendental, then so is the scheme-theoretic residue extension of
`Spec B ⟶ Spec R` at the point `lp`.

The algebra structure on the left is the ideal-theoretic one, induced by `Algebra.ofId R B`; on
the right it is the one `AlgebraicGeometry.OneStepDevissageAt` records, induced by the morphism
of spectra after transport along the equality of its value at `lp` with `r`. -/
public theorem AlgebraicGeometry.purelyTranscendental_residueField_specMap {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] (r : Ideal R) [hr : r.IsPrime] (lp : Ideal B)
    [hlp : lp.IsPrime] (hover : lp.LiesOver r)
    (hg : (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩) =
      show Spec (CommRingCat.of R) from ⟨r, hr⟩)
    (h : letI : Algebra r.ResidueField lp.ResidueField :=
        (Ideal.ResidueField.mapₐ r lp (Algebra.ofId R B) hover.over).toRingHom.toAlgebra
      PurelyTranscendental r.ResidueField lp.ResidueField) :
    letI : Algebra
        ((Spec (CommRingCat.of R)).residueField (show Spec (CommRingCat.of R) from ⟨r, hr⟩))
        ((Spec (CommRingCat.of B)).residueField (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)) :=
      (((Spec (CommRingCat.of R)).residueFieldCongr hg).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R B))).residueFieldMap
          (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)).hom.toAlgebra
    PurelyTranscendental
      ((Spec (CommRingCat.of R)).residueField (show Spec (CommRingCat.of R) from ⟨r, hr⟩))
      ((Spec (CommRingCat.of B)).residueField
        (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)) := by
  let : Algebra r.ResidueField lp.ResidueField :=
    (Ideal.ResidueField.mapₐ r lp (Algebra.ofId R B) hover.over).toRingHom.toAlgebra
  let : Algebra
      ((Spec (CommRingCat.of R)).residueField (show Spec (CommRingCat.of R) from ⟨r, hr⟩))
      ((Spec (CommRingCat.of B)).residueField (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)) :=
    (((Spec (CommRingCat.of R)).residueFieldCongr hg).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).residueFieldMap
        (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)).hom.toAlgebra
  have := h
  -- The transport of evaluation along an equality of points, which is all that the factor
  -- `Scheme.residueFieldCongr` of the geometric algebra structure contributes.
  have haux : ∀ {X : Scheme.{u}} {a b : X} (hab : a = b) {W : CommRingCat.{u}}
      (k : X.residueField a ⟶ W),
      X.evaluation ⊤ b trivial ≫ (X.residueFieldCongr hab).inv ≫ k =
        X.evaluation ⊤ a trivial ≫ k := by
    intro X a b hab W k
    subst hab
    simp
  have hiso : ∀ {W : CommRingCat.{u}}
      (k : (Spec (CommRingCat.of R)).residueField
        (show Spec (CommRingCat.of R) from ⟨r, hr⟩) ⟶ W),
      CommRingCat.ofHom (algebraMap R r.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (CommRingCat.of R)
            (show Spec (CommRingCat.of R) from ⟨r, hr⟩)).inv ≫ k =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (Spec (CommRingCat.of R)).evaluation ⊤
            (show Spec (CommRingCat.of R) from ⟨r, hr⟩) trivial ≫ k :=
    fun k ↦ Scheme.Spec.algebraMap_residueFieldIso_inv_assoc (CommRingCat.of R) _ k
  have hisoB : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (Spec (CommRingCat.of B)).evaluation ⊤
          (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩) trivial =
      CommRingCat.ofHom (algebraMap B lp.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of B)
          (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)).inv :=
    (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of B) _).symm
  have hnat : (Spec (CommRingCat.of R)).evaluation ⊤
          ((Spec.map (CommRingCat.ofHom (algebraMap R B)))
            (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)) trivial ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R B))).residueFieldMap
          (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩) =
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop ≫
        (Spec (CommRingCat.of B)).evaluation ⊤
          (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩) trivial :=
    Scheme.Γevaluation_naturality (Spec.map (CommRingCat.ofHom (algebraMap R B))) _
  -- The square of structure maps: both composites `R → κ(lp)` are evaluation at `lp` of the
  -- image of a function on `Spec R`.
  have key : CommRingCat.ofHom (algebraMap R r.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of R)
          (show Spec (CommRingCat.of R) from ⟨r, hr⟩)).inv ≫
        ((Spec (CommRingCat.of R)).residueFieldCongr hg).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R B))).residueFieldMap
            (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩) =
      CommRingCat.ofHom (algebraMap R B) ≫
        CommRingCat.ofHom (algebraMap B lp.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (CommRingCat.of B)
            (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)).inv := by
    rw [hiso, haux hg, hnat, ← Scheme.ΓSpecIso_inv_naturality_assoc, hisoB]
  refine PurelyTranscendental.of_ringEquiv_square (k := r.ResidueField)
    (K := lp.ResidueField)
    (Scheme.Spec.residueFieldIso (CommRingCat.of R)
      (show Spec (CommRingCat.of R) from ⟨r, hr⟩)).symm.commRingCatIsoToRingEquiv
    (Scheme.Spec.residueFieldIso (CommRingCat.of B)
      (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩)).symm.commRingCatIsoToRingEquiv ?_
  apply Ideal.ResidueField.ringHom_ext
  ext a
  have h2 := congrArg (fun m : CommRingCat.of R ⟶ (Spec (CommRingCat.of B)).residueField
    (show Spec (CommRingCat.of B) from ⟨lp, hlp⟩) ↦ m.hom a) key
  simpa [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
    IsScalarTower.algebraMap_apply R B lp.ResidueField, Iso.commRingCatIsoToRingEquiv,
    RingEquiv.ofRingHom] using h2

end
