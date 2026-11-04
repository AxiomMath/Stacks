module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# Residue fields at closed points of locally Noetherian schemes

A locally Noetherian scheme with a point admits a morphism from the spectrum of a field which is
a monomorphism and locally of finite presentation. Such a morphism is produced by the residue
field at a closed point of an affine open: the spectrum of that residue field is a closed
immersion into the affine open, hence locally of finite type, and over a locally Noetherian
target local finite type upgrades to local finite presentation by **Stacks 01TX**.

The point of the statement is that the field-valued point can be taken locally of finite
presentation, which the generic points used for flatness cannot be: a localization at a minimal
prime is not a finitely presented algebra in general.

## Main results

* `AlgebraicGeometry.exists_isClosed_singleton_of_nonempty_spec`: the spectrum of a ring with a
  point has a closed point, namely a maximal ideal.
* `AlgebraicGeometry.exists_mono_locallyOfFinitePresentation_from_spec_isField`: a locally
  Noetherian scheme with a point receives a monomorphism which is locally of finite presentation
  from the spectrum of a field.

## Implementation notes

The affine open is taken from `AlgebraicGeometry.Scheme.affineOpenCover`, whose components are
spectra of rings on the nose, so that the maximal ideal of such a ring is literally a point of
the component and `PrimeSpectrum.isClosed_singleton_iff_isMaximal` applies without transporting
along an isomorphism onto a spectrum.

The closed point is closed in the affine open, not in the whole scheme, so the morphism out of
the spectrum of the residue field is a closed immersion only into that open. This is enough:
local finite presentation and being a monomorphism both compose, and the open immersion of the
affine open has both properties.

The field is delivered as a ring object of `CommRingCat` together with `IsField`, rather than as
a type carrying a `Field` instance, so that the source of the morphism is `Spec R` on the nose
and no commutative ring instance has to be reconstructed from the field structure. A consumer
wanting a `Field` instance obtains one from `IsField.toField`, whose underlying commutative ring
is the given one.

## References

* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- **The spectrum of a ring with a point has a closed point.** A point of the spectrum makes the
ring nontrivial, a nontrivial ring has a maximal ideal, and the maximal ideals are exactly the
closed points of the spectrum. -/
theorem exists_isClosed_singleton_of_nonempty_spec (R : CommRingCat.{u}) (x : Spec R) :
    ∃ y : Spec R, IsClosed ({y} : Set (Spec R)) := by
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨x⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := R)
  exact ⟨⟨m, hm.isPrime⟩, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm⟩

/-- **A locally Noetherian scheme with a point receives a monomorphism locally of finite
presentation from the spectrum of a field.** Take an affine open of the chosen affine open cover
containing the point; it is the spectrum of a ring and is locally Noetherian, being open in a
locally Noetherian scheme. A maximal ideal of that ring is a closed point of the affine open, so
the spectrum of the residue field there is a closed immersion into it and in particular locally
of finite type; over a locally Noetherian target this is local finite presentation by
**Stacks 01TX**. Composing with the open immersion of the affine open preserves both being a
monomorphism and being locally of finite presentation. -/
theorem exists_mono_locallyOfFinitePresentation_from_spec_isField
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    ∃ (R : CommRingCat.{u}) (g : Spec R ⟶ X),
      IsField R ∧ Mono g ∧ LocallyOfFinitePresentation g := by
  obtain ⟨y, -⟩ := X.affineOpenCover.covers x
  have hnoeth : IsLocallyNoetherian
      (Spec (X.affineOpenCover.X (X.affineOpenCover.idx x))) :=
    isLocallyNoetherian_of_isOpenImmersion (X.affineOpenCover.f (X.affineOpenCover.idx x))
  obtain ⟨p, hp⟩ := exists_isClosed_singleton_of_nonempty_spec
    (X.affineOpenCover.X (X.affineOpenCover.idx x)) y
  have hci : IsClosedImmersion
      ((Spec (X.affineOpenCover.X (X.affineOpenCover.idx x))).fromSpecResidueField p) :=
    isClosed_singleton_iff_isClosedImmersion.mp hp
  exact ⟨(Spec (X.affineOpenCover.X (X.affineOpenCover.idx x))).residueField p,
    (Spec (X.affineOpenCover.X (X.affineOpenCover.idx x))).fromSpecResidueField p ≫
      X.affineOpenCover.f (X.affineOpenCover.idx x),
    Field.toIsField _, inferInstance, inferInstance⟩

end AlgebraicGeometry

end
