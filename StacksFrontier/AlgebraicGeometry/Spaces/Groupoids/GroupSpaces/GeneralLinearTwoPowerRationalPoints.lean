module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction

/-!
# Every `k`-point of `(GL₂)^m` is a tuple of invertible matrices

The coordinate ring of `(GL₂)^m` over a commutative ring `k` is the polynomial ring on the `4m`
entries of `m` generic two-by-two matrices with the product of their determinants inverted, so a
`k`-point of `(GL₂)^m` — a retraction of the structure map of that ring, that is a homomorphism
of `k`-algebras to `k` — is determined by the images of the `4m` indeterminates, and those
images are the entries of `m` matrices which the retraction makes invertible.  Conversely every
such tuple arises: `AlgebraicGeometry.generalLinearTwoPowerPoint` turns a tuple into a point.
So the `k`-points of `(GL₂)^m` *are* the `m`-tuples of invertible two-by-two matrices over `k`.

## Main definitions

* `AlgebraicGeometry.generalLinearTwoPowerPointMatrix`: the `m`-tuple of two-by-two matrices read
  off a retraction of the structure map of the coordinate ring of `(GL₂)^m`, namely the images of
  the generic matrices.
* `AlgebraicGeometry.generalLinearTwoPowerPointGL`: the same tuple with its invertibility, as an
  `m`-tuple of elements of the general linear group.

## Main results

* `AlgebraicGeometry.generalLinearTwoPowerPoint_generalLinearTwoPowerPointGL` and
  `AlgebraicGeometry.exists_eq_generalLinearTwoPowerPoint`: **every `k`-algebra retraction of the
  coordinate ring of `(GL₂)^m` is the point named by an `m`-tuple of invertible matrices.**
* `AlgebraicGeometry.Space.exists_eq_generalLinearTwoPowerSitePoint`: **every section of the
  structure morphism of the site object `(GL₂)^m` is the `k`-point named by an `m`-tuple of
  invertible matrices.**
* `AlgebraicGeometry.Space.exists_eq_yoneda_map_generalLinearTwoPowerSitePoint`: **every rational
  point of the functor of points of `(GL₂)^m` is the `k`-point named by an `m`-tuple of invertible
  matrices.**

## Implementation notes

The ring-level statement is `CategoryTheory.IsLocalization.ringHom_ext` for the submonoid of
powers of the product of the generic determinants together with `MvPolynomial.ringHom_ext`: two
ring maps out of the localization agree as soon as they agree on the polynomial ring, and there
as soon as they agree on the coefficients and on the indeterminates.  Agreement on the
coefficients is exactly the hypothesis that the retraction is a `k`-algebra map, and agreement on
the indeterminates holds by construction of the tuple.  That the hypothesis is needed, and not a
consequence of being a ring map, is visible already for `m = 0`: a ring endomorphism of a field
need not be the identity.

The passage to the site is `AlgebraicGeometry.Spec.map_surjective` — the spectrum of a ring map
is every morphism between affine spectra — followed by `AlgebraicGeometry.Spec.map_injective` to
read the triangle over the base as the retraction identity.  The passage to the functor of points
is fullness of the Yoneda embedding.

## References

* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-! ### The tuple of matrices named by a retraction -/

section Ring

variable (k : Type u) [CommRing k] (m : ℕ)
  (φ : generalLinearTwoPowerCoordinateRing k m →+* k)

/-- **The `m`-tuple of two-by-two matrices named by a retraction of the structure map of the
coordinate ring of `(GL₂)^m`**: the images under the retraction of the `m` generic matrices, that
is the matrices whose entries are the images of the `4m` indeterminates. -/
def generalLinearTwoPowerPointMatrix (i : Fin m) : Matrix (Fin 2) (Fin 2) k :=
  φ.mapMatrix (genericMatrixTwoPower k m i)

/-- The `(a, b)` entry of the `i`-th matrix named by a retraction `φ` is the image under `φ` of
the indeterminate indexed by `(i, a, b)`. -/
theorem generalLinearTwoPowerPointMatrix_apply (i : Fin m) (a b : Fin 2) :
    generalLinearTwoPowerPointMatrix k m φ i a b =
      φ (algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
        (generalLinearTwoPowerCoordinateRing k m) (MvPolynomial.X (i, a, b))) :=
  rfl

/-- **The matrices named by a retraction are invertible.**  The product of the generic
determinants is already a unit in the coordinate ring, so each generic determinant is, and a ring
map carries units to units. -/
theorem isUnit_det_generalLinearTwoPowerPointMatrix (i : Fin m) :
    IsUnit (generalLinearTwoPowerPointMatrix k m φ i).det := by
  rw [generalLinearTwoPowerPointMatrix, ← RingHom.map_det]
  exact (isUnit_det_genericMatrixTwoPower k m i).map φ

/-- **The `m`-tuple of invertible two-by-two matrices named by a retraction of the structure map
of the coordinate ring of `(GL₂)^m`.** -/
def generalLinearTwoPowerPointGL (i : Fin m) : Matrix.GeneralLinearGroup (Fin 2) k :=
  ((Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_det_generalLinearTwoPowerPointMatrix k m φ i)).unit

/-- The underlying matrix of the invertible matrix `generalLinearTwoPowerPointGL k m φ i` is
`generalLinearTwoPowerPointMatrix k m φ i`. -/
theorem generalLinearTwoPowerPointGL_coe (i : Fin m) :
    (generalLinearTwoPowerPointGL k m φ i : Matrix (Fin 2) (Fin 2) k) =
      generalLinearTwoPowerPointMatrix k m φ i :=
  IsUnit.unit_spec _

/-- **Every `k`-algebra retraction of the structure map of the coordinate ring of `(GL₂)^m` is the
`k`-point named by the `m`-tuple of invertible matrices it sends the generic matrices to.**

Two ring maps out of the coordinate ring agree as soon as they agree on the polynomial ring on
the `4m` indeterminates, since the coordinate ring is a localization of it, and there as soon as
they agree on the coefficients and on the indeterminates.  On the coefficients both are the
identity — for the retraction this is the hypothesis, for the point it is
`AlgebraicGeometry.generalLinearTwoPowerPoint_comp_algebraMap` — and on the indeterminates both
give the corresponding matrix entry. -/
theorem generalLinearTwoPowerPoint_generalLinearTwoPowerPointGL
    (hφ : φ.comp (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) = RingHom.id k) :
    generalLinearTwoPowerPoint k m (generalLinearTwoPowerPointGL k m φ) = φ := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (∏ i : Fin m, genericTwoPowerDeterminant k m i)) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · have hC : algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
        (generalLinearTwoPowerCoordinateRing k m) (MvPolynomial.C r) =
        algebraMap k (generalLinearTwoPowerCoordinateRing k m) r := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    change generalLinearTwoPowerPoint k m (generalLinearTwoPowerPointGL k m φ)
        (algebraMap _ _ (MvPolynomial.C r)) = φ (algebraMap _ _ (MvPolynomial.C r))
    rw [hC]
    exact (RingHom.congr_fun (generalLinearTwoPowerPoint_comp_algebraMap k m
      (generalLinearTwoPowerPointGL k m φ)) r).trans (RingHom.congr_fun hφ r).symm
  · change generalLinearTwoPowerPoint k m (generalLinearTwoPowerPointGL k m φ)
        (algebraMap _ _ (MvPolynomial.X p)) = φ (algebraMap _ _ (MvPolynomial.X p))
    rw [generalLinearTwoPowerPoint_algebraMap, genericTwoPowerEval_X,
      generalLinearTwoPowerPointGL_coe]
    exact generalLinearTwoPowerPointMatrix_apply k m φ p.1 p.2.1 p.2.2

/-- **The `k`-points of `(GL₂)^m` are the `m`-tuples of invertible two-by-two matrices over
`k`**: a `k`-algebra retraction of the structure map of the coordinate ring is
`AlgebraicGeometry.generalLinearTwoPowerPoint` at some tuple. -/
theorem exists_eq_generalLinearTwoPowerPoint
    (hφ : φ.comp (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) = RingHom.id k) :
    ∃ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k,
      generalLinearTwoPowerPoint k m M = φ :=
  ⟨generalLinearTwoPowerPointGL k m φ,
    generalLinearTwoPowerPoint_generalLinearTwoPowerPointGL k m φ hφ⟩

end Ring

/-! ### A retraction read off a section of the morphism of spectra -/

/-- **A section of the morphism of spectra of a ring map is the spectrum of a retraction.**  The
converse of `AlgebraicGeometry.specMap_comp_specMap_eq_id`: `Spec` is fully faithful on affine
spectra, so the triangle of schemes is the triangle of rings. -/
theorem comp_eq_id_of_specMap_comp_specMap_eq_id {R A : CommRingCat.{u}} (α : R ⟶ A) (γ : A ⟶ R)
    (h : Spec.map γ ≫ Spec.map α = 𝟙 (Spec R)) : α ≫ γ = 𝟙 R :=
  Spec.map_injective (by rwa [Spec.map_comp, Spec.map_id])

/-! ### The `k`-points of the site object and of the functor of points -/

namespace Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)

/-- **Every section of the structure morphism of the site object `(GL₂)^m` is the `k`-point named
by an `m`-tuple of invertible two-by-two matrices.**

The underlying morphism of schemes is a morphism between affine spectra, hence the spectrum of a
ring map, and the triangle over `Spec k` says that this ring map is a retraction of the structure
map of the coordinate ring; so
`AlgebraicGeometry.exists_eq_generalLinearTwoPowerPoint` applies. -/
theorem exists_eq_generalLinearTwoPowerSitePoint
    (ξ : (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (CommRingCat.of k)) hk) ⟶
      generalLinearTwoPowerSiteObject k B hk m) :
    ∃ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k,
      generalLinearTwoPowerSitePoint k B hk m M = ξ := by
  have hw : ξ.left.hom ≫ Spec.map (generalLinearTwoPowerStructureMap k m) =
      𝟙 (Spec (CommRingCat.of k)) :=
    congrArg (fun t : B.obj hk ⟶ B.obj hk => t.hom) (Over.w ξ)
  obtain ⟨γ, hγ⟩ := Spec.map_surjective ξ.left.hom
  rw [← hγ] at hw
  have hret : γ.hom.comp (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) =
      RingHom.id k := by
    have h := congrArg CommRingCat.Hom.hom (comp_eq_id_of_specMap_comp_specMap_eq_id _ _ hw)
    rwa [CommRingCat.hom_comp, CommRingCat.hom_id] at h
  obtain ⟨M, hM⟩ := exists_eq_generalLinearTwoPowerPoint k m γ.hom hret
  refine ⟨M, Over.OverMorphism.ext ?_⟩
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (generalLinearTwoPowerPoint k m M)) = ξ.left.hom
  rwa [hM, CommRingCat.ofHom_hom]

/-- **Every rational point of the functor of points of `(GL₂)^m` is the `k`-point named by an
`m`-tuple of invertible two-by-two matrices.**  The Yoneda embedding is full, so the rational
point is the Yoneda image of a section of the structure morphism of the site object. -/
theorem exists_eq_yoneda_map_generalLinearTwoPowerSitePoint
    (ξ : baseFunctor k B hk ⟶ generalLinearTwoPowerFunctor k B hk m) :
    ∃ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k,
      yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) = ξ := by
  obtain ⟨g, hg⟩ := yoneda.map_surjective ξ
  obtain ⟨M, hM⟩ := exists_eq_generalLinearTwoPowerSitePoint k B hk m g
  exact ⟨M, by rwa [hM]⟩

end Space

end AlgebraicGeometry

end
