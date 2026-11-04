module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlaneNotAffine

/-!
# The punctured plane over an arbitrary base ring

Over a field, the complement of the origin in the affine plane is the standard example of a
non-affine scheme, and that is already available here as
`AlgebraicGeometry.not_isAffine_puncturedScheme`.  This file carries the same example over an
arbitrary nonzero commutative ring `A`, in the one presentation that makes it behave well under
change of base ring: the open `puncturedOpen A` of `Spec A[x, y]` is *defined* as the union of
the two coordinate standard opens, so that it is literally the inverse image of `puncturedOpen B`
along the map induced by any ring homomorphism `B →+* A`.

## Main definitions

* `Stacks.Refute09ZM.puncturedOpen`: the open `D(x) ∪ D(y)` of `Spec A[x, y]`.
* `Stacks.Refute09ZM.specPlaneMap`: the morphism `Spec A[x, y] ⟶ Spec B[x, y]` induced by a ring
  homomorphism `B →+* A`.

## Main results

* `Stacks.Refute09ZM.preimage_puncturedOpen`: the punctured open is stable under inverse image
  along `specPlaneMap`, as an equality of opens and not merely an isomorphism.
* `Stacks.Refute09ZM.compactSpace_punctured`,
  `Stacks.Refute09ZM.quasiSeparatedSpace_punctured`: it is quasi-compact and quasi-separated.
* `Stacks.Refute09ZM.not_isAffineOpen_puncturedOpen`: **it is not affine, over any nonzero ring.**

## Implementation notes

Writing the punctured open as `D(x) ⊔ D(y)` rather than as the complement of the origin is what
makes `preimage_puncturedOpen` hold on the nose: inverse images of standard opens along `Spec` of
a ring homomorphism are standard opens by `PrimeSpectrum.comap_basicOpen`, which is a `rfl`, and
`MvPolynomial.map` fixes the two coordinates.  The repository's `PuncturedAffinePlane` records the
complement of the origin, and `AlgebraicGeometry.coe_basicOpen_X_sup` is exactly the comparison of
the two descriptions over a field, which is where it is needed.

## References

* [The Stacks Project, Tag 01IL](https://stacks.math.columbia.edu/tag/01IL)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Refute09ZM

variable (A : Type u) [CommRing A]

/-- The `i`-th coordinate standard open `D(X i)` of the affine plane over `A`. -/
def coordOpen (i : Fin 2) : (affinePlane A).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X i : affinePlaneRing A)

/-- The punctured plane over `A`, as an open subscheme of the affine plane: the union of the two
coordinate standard opens of `Spec A[x, y]`.  Over a field this is the complement of the origin,
by `AlgebraicGeometry.coe_basicOpen_X_sup`. -/
def puncturedOpen : (affinePlane A).Opens := coordOpen A 0 ⊔ coordOpen A 1

/-- The punctured plane over `A` as a scheme in its own right. -/
abbrev punctured : Scheme.{u} := (puncturedOpen A).toScheme

/-- Each coordinate standard open of the affine plane is quasi-compact. -/
theorem isCompact_coordOpen (i : Fin 2) : IsCompact (coordOpen A i : Set (affinePlane A)) :=
  PrimeSpectrum.isCompact_basicOpen _

/-- The punctured open of the affine plane is quasi-compact. -/
theorem isCompact_puncturedOpen : IsCompact (puncturedOpen A : Set (affinePlane A)) := by
  rw [puncturedOpen, Opens.coe_sup]
  exact (isCompact_coordOpen A 0).union (isCompact_coordOpen A 1)

/-- The punctured plane is a quasi-compact scheme. -/
instance compactSpace_punctured : CompactSpace (punctured A) :=
  isCompact_iff_compactSpace.mp (isCompact_puncturedOpen A)

/-- The punctured plane is a quasi-separated scheme. -/
instance quasiSeparatedSpace_punctured : QuasiSeparatedSpace (punctured A) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _ (puncturedOpen A).2).mp
    (isQuasiSeparated_univ.of_subset (Set.subset_univ _))

section Map

variable {A} {B : Type u} [CommRing B]

/-- The morphism of affine planes induced by a ring homomorphism of the base rings. -/
def specPlaneMap (phi : B →+* A) : affinePlane A ⟶ affinePlane B :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin 2) phi))

/-- The morphism of affine planes induced by a ring homomorphism is affine. -/
instance isAffineHom_specPlaneMap (phi : B →+* A) : IsAffineHom (specPlaneMap phi) :=
  inferInstanceAs (IsAffineHom (Spec.map _))

/-- The inverse image of a union of two opens along a morphism of schemes is the union of their
inverse images. -/
theorem preimage_sup {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) :
    f ⁻¹ᵁ (U ⊔ V) = (f ⁻¹ᵁ U) ⊔ (f ⁻¹ᵁ V) :=
  Opens.ext (by simp)

/-- The inverse image of the `i`-th coordinate standard open along `specPlaneMap phi` is the
`i`-th coordinate standard open. -/
theorem preimage_coordOpen (phi : B →+* A) (i : Fin 2) :
    (specPlaneMap phi) ⁻¹ᵁ (coordOpen B i) = coordOpen A i := by
  refine (PrimeSpectrum.comap_basicOpen
    (MvPolynomial.map (σ := Fin 2) phi) (MvPolynomial.X i)).trans ?_
  rw [MvPolynomial.map_X, coordOpen]

/-- **The punctured open is stable under change of base ring**: its inverse image along
`specPlaneMap phi` is the punctured open, as an equality of opens. -/
theorem preimage_puncturedOpen (phi : B →+* A) :
    (specPlaneMap phi) ⁻¹ᵁ (puncturedOpen B) = puncturedOpen A := by
  rw [puncturedOpen, preimage_sup, preimage_coordOpen, preimage_coordOpen, puncturedOpen]

end Map

/-- Over a field, the punctured open of the affine plane is not affine. -/
theorem not_isAffineOpen_puncturedOpen_field (k : Type u) [Field k] :
    ¬ IsAffineOpen (puncturedOpen k) :=
  not_isAffine_puncturedScheme (puncturedAffinePlaneOf k)

/-- **The punctured plane over any nonzero commutative ring is not affine.** -/
theorem not_isAffineOpen_puncturedOpen [Nontrivial A] : ¬ IsAffineOpen (puncturedOpen A) := by
  intro hA
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  refine not_isAffineOpen_puncturedOpen_field (A ⧸ m) ?_
  have h := hA.preimage (specPlaneMap (Ideal.Quotient.mk m))
  rwa [preimage_puncturedOpen] at h

/-- The punctured plane over a nonzero ring is not an affine scheme. -/
theorem not_isAffine_punctured [Nontrivial A] : ¬ IsAffine (punctured A) :=
  not_isAffineOpen_puncturedOpen A

end Stacks.Refute09ZM

end

end
