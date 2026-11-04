module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlaneNotAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.GeneralLinearGroup

/-!
# The general linear scheme surjects onto the punctured plane

The first row `(a, b)` of the generic invertible two-by-two matrix defines a morphism from
`GL₂ = Spec k[a, b, c, d, 1/(ad - bc)]` to the affine plane `Spec k[x, y]`, by `x ↦ a`, `y ↦ b`.
Its image misses the origin, so it lifts along the open immersion of the punctured plane `U`, and
the lift is a surjection onto `U`. Since `U` is not affine, the image of this morphism is
therefore contained in no affine open of `U` at all.

## Main definitions

* `AlgebraicGeometry.generalLinearTwoFirstRowHom`: the ring map `x ↦ a`, `y ↦ b`.
* `AlgebraicGeometry.generalLinearTwoToAffinePlane`: the induced morphism to the affine plane.
* `AlgebraicGeometry.generalLinearTwoToPuncturedPlane`: its lift to the punctured plane.

## Main results

* `AlgebraicGeometry.range_generalLinearTwoToAffinePlane_subset`: the image misses the origin.
* `AlgebraicGeometry.surjective_generalLinearTwoToPuncturedPlane`: the lift is surjective.
* `AlgebraicGeometry.not_range_subset_of_isAffineOpen`: the image of that morphism is contained
  in no affine open of the punctured plane.

## Implementation notes

The first row of the generic matrix consists of the coordinates `(0, 0)` and `(0, 1)`, which are
`a` and `b`, so that the map `x ↦ a`, `y ↦ b` is `MvPolynomial.X j ↦ X (0, j)`. The index sets of
the two polynomial rings differ — `Fin 2 × Fin 2` for `GL₂` against `Fin 2` for the plane — so
the map is built by evaluation rather than by reindexing.

Surjectivity is proved by exhibiting a section over each of the two standard opens of the plane
that cover the complement of the origin. A section over `D(f)` is a two-by-two matrix over
`k[x, y][1/f]` with unit determinant whose first row is `(x, y)`; over `D(x)` take
`!![x, y; 0, 1/x]` and over `D(y)` take `!![x, y; -1/y, 0]`, both of determinant one. This is
packaged as `AlgebraicGeometry.generalLinearTwoSection`, which inverts the determinant using the
universal property of the localization away from it.

The final statement is about the image of this specific morphism, and quantifies over all affine
opens of the punctured plane; it is deduced from surjectivity, which forces such an affine open
to be everything, and from the punctured plane not being affine.

## References

* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section CommRingBase

variable (k : Type u) [CommRing k]

/-- The ring map `k[x, y] → k[a, b, c, d, 1/(ad - bc)]` sending `x` to `a` and `y` to `b`, that
is, sending the two variables to the two entries of the first row of the generic matrix. -/
noncomputable def generalLinearTwoFirstRowHom :
    affinePlaneRing k →+* generalLinearTwoCoordinateRing k :=
  MvPolynomial.eval₂Hom (algebraMap k (generalLinearTwoCoordinateRing k))
    (fun j : Fin 2 => generalLinearTwoCoordinate k 0 j)

/-- The first-row map sends the variable `X j` to the entry `(0, j)` of the generic matrix. -/
@[simp]
lemma generalLinearTwoFirstRowHom_X (j : Fin 2) :
    generalLinearTwoFirstRowHom k (MvPolynomial.X j) = generalLinearTwoCoordinate k 0 j := by
  simp [generalLinearTwoFirstRowHom]

/-- The morphism `GL₂ → 𝔸²` given by `x ↦ a`, `y ↦ b`. -/
noncomputable def generalLinearTwoToAffinePlane :
    generalLinearTwoScheme k ⟶ affinePlane k :=
  Spec.map (CommRingCat.ofHom (generalLinearTwoFirstRowHom k))

section Sections

variable {A : Type u} [CommRing A] [Algebra (affinePlaneRing k) A]

/-- A two-by-two matrix over a `k[x, y]`-algebra `A` whose determinant is a unit induces a ring
map out of the coordinate ring of `GL₂`, by the universal property of inverting the determinant.
-/
noncomputable def generalLinearTwoSection (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    generalLinearTwoCoordinateRing k →+* A :=
  IsLocalization.Away.lift
    (g := MvPolynomial.eval₂Hom ((algebraMap (affinePlaneRing k) A).comp MvPolynomial.C)
      (fun p : Fin 2 × Fin 2 => M p.1 p.2))
    (generalLinearTwoDeterminant k) (by
      have hdet : MvPolynomial.eval₂Hom
          ((algebraMap (affinePlaneRing k) A).comp MvPolynomial.C)
          (fun p : Fin 2 × Fin 2 => M p.1 p.2) (generalLinearTwoDeterminant k) = M.det := by
        change MvPolynomial.eval₂Hom _ _ ((Matrix.mvPolynomialX (Fin 2) (Fin 2) k).det) = _
        rw [Matrix.det_fin_two, Matrix.det_fin_two]
        simp
      rwa [hdet])

/-- Such a matrix is a section of the first-row map precisely when its first row is `(x, y)`. -/
lemma generalLinearTwoSection_comp_firstRowHom (M : Matrix (Fin 2) (Fin 2) A)
    (hM : IsUnit M.det) (h0 : M 0 0 = algebraMap (affinePlaneRing k) A (MvPolynomial.X 0))
    (h1 : M 0 1 = algebraMap (affinePlaneRing k) A (MvPolynomial.X 1)) :
    (generalLinearTwoSection k M hM).comp (generalLinearTwoFirstRowHom k) =
      algebraMap (affinePlaneRing k) A := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · change generalLinearTwoSection k M hM (generalLinearTwoFirstRowHom k (MvPolynomial.C r)) = _
    rw [generalLinearTwoFirstRowHom, MvPolynomial.eval₂Hom_C,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2 × Fin 2) k)]
    simp [generalLinearTwoSection]
  · change generalLinearTwoSection k M hM (generalLinearTwoFirstRowHom k (MvPolynomial.X j)) = _
    rw [generalLinearTwoFirstRowHom_X, generalLinearTwoCoordinate, generalLinearTwoSection,
      IsLocalization.Away.lift_eq]
    fin_cases j
    · simpa using h0
    · simpa using h1

/-- If `A` is the localization of `k[x, y]` away from `f` and `c, d ∈ A` satisfy `x d - y c = 1`,
then the standard open `D(f)` lies in the image of the first-row map on prime spectra. -/
lemma coe_basicOpen_subset_range_comap (f : affinePlaneRing k) [IsLocalization.Away f A]
    (c d : A) (hdet : algebraMap (affinePlaneRing k) A (MvPolynomial.X 0) * d -
      algebraMap (affinePlaneRing k) A (MvPolynomial.X 1) * c = 1) :
    (PrimeSpectrum.basicOpen f : Set _) ⊆
      Set.range (PrimeSpectrum.comap (generalLinearTwoFirstRowHom k)) := by
  let M : Matrix (Fin 2) (Fin 2) A := !![algebraMap (affinePlaneRing k) A (MvPolynomial.X 0),
    algebraMap (affinePlaneRing k) A (MvPolynomial.X 1); c, d]
  have hM : IsUnit M.det := by simp [M, Matrix.det_fin_two, hdet]
  have hcomp := generalLinearTwoSection_comp_firstRowHom k M hM (by simp [M]) (by simp [M])
  intro p hp
  rw [← PrimeSpectrum.localization_away_comap_range A f] at hp
  obtain ⟨q, rfl⟩ := hp
  exact ⟨PrimeSpectrum.comap (generalLinearTwoSection k M hM) q,
    by rw [← PrimeSpectrum.comap_comp_apply, hcomp]⟩

end Sections

/-- The standard open `D(x)` lies in the image of the first-row map on prime spectra: over `D(x)`
the matrix `!![x, y; 0, 1/x]` has determinant `1`. -/
lemma coe_basicOpen_X_zero_subset_range :
    (PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 2) : affinePlaneRing k) : Set _) ⊆
      Set.range (PrimeSpectrum.comap (generalLinearTwoFirstRowHom k)) :=
  coe_basicOpen_subset_range_comap k
    (A := Localization.Away (MvPolynomial.X (0 : Fin 2) : affinePlaneRing k)) _ 0
    (IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin 2) : affinePlaneRing k))
    (by simp [IsLocalization.Away.mul_invSelf])

/-- The standard open `D(y)` lies in the image of the first-row map on prime spectra: over `D(y)`
the matrix `!![x, y; -1/y, 0]` has determinant `1`. -/
lemma coe_basicOpen_X_one_subset_range :
    (PrimeSpectrum.basicOpen (MvPolynomial.X (1 : Fin 2) : affinePlaneRing k) : Set _) ⊆
      Set.range (PrimeSpectrum.comap (generalLinearTwoFirstRowHom k)) :=
  coe_basicOpen_subset_range_comap k
    (A := Localization.Away (MvPolynomial.X (1 : Fin 2) : affinePlaneRing k)) _
    (-IsLocalization.Away.invSelf (MvPolynomial.X (1 : Fin 2) : affinePlaneRing k)) 0
    (by simp [IsLocalization.Away.mul_invSelf])

end CommRingBase

section Punctured

variable (k : Type u) [Field k]

/-- The open immersion of the punctured plane has as image the complement of the origin. -/
lemma range_puncturedAffinePlane_openImmersion (S : PuncturedAffinePlane.{u}) :
    Set.range S.openImmersion.base = {affinePlaneOrigin S.k}ᶜ :=
  (Scheme.Opens.range_ι S.U).trans S.carrier_U

/-- The image of the first-row map on prime spectra is exactly the complement of the origin: a
prime containing both `a` and `b` would contain the unit `ad - bc`, and conversely the two
standard opens `D(x)` and `D(y)` covering the complement of the origin each carry a section. -/
lemma range_comap_generalLinearTwoFirstRowHom :
    Set.range (PrimeSpectrum.comap (generalLinearTwoFirstRowHom k)) =
      {affinePlaneOrigin k}ᶜ := by
  apply subset_antisymm
  · rintro _ ⟨p, rfl⟩ hp
    have hmem (j : Fin 2) : generalLinearTwoCoordinate k 0 j ∈ p.asIdeal := by
      have := X_mem_affinePlaneOrigin k j
      rw [← hp] at this
      simpa using this
    have htop : p.asIdeal = ⊤ := by
      rw [← top_le_iff, ← span_firstRow_eq_top k, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hmem j
    exact p.2.ne_top htop
  · rw [← coe_basicOpen_X_sup k]
    simpa using Set.union_subset (coe_basicOpen_X_zero_subset_range k)
      (coe_basicOpen_X_one_subset_range k)

/-- The image of `GL₂ → 𝔸²` lies in the punctured plane: a prime of the coordinate ring of `GL₂`
containing both `a` and `b` would contain the unit `ad - bc`. -/
theorem range_generalLinearTwoToAffinePlane_subset :
    Set.range (generalLinearTwoToAffinePlane k).base ⊆
      Set.range (puncturedAffinePlaneOf k).openImmersion.base :=
  Set.Subset.trans (range_comap_generalLinearTwoFirstRowHom k).le
    (range_puncturedAffinePlane_openImmersion (puncturedAffinePlaneOf k)).ge

/-- **Stacks Project, Tag 01KX (gl2_to_punctured_plane).** The morphism from `GL₂` to the
punctured affine plane `U = Spec k[x, y] ∖ {(x, y)}` determined by `x ↦ a`, `y ↦ b`. -/
@[stacks 01KX "gl2_to_punctured_plane"]
noncomputable def generalLinearTwoToPuncturedPlane :
    generalLinearTwoScheme k ⟶ (puncturedAffinePlaneOf k).puncturedScheme :=
  IsOpenImmersion.lift (puncturedAffinePlaneOf k).U.ι (generalLinearTwoToAffinePlane k)
    (range_generalLinearTwoToAffinePlane_subset k)

/-- The morphism `GL₂ → U` followed by the open immersion `U → 𝔸²` is the morphism `GL₂ → 𝔸²`. -/
@[simp]
lemma generalLinearTwoToPuncturedPlane_comp_openImmersion :
    generalLinearTwoToPuncturedPlane k ≫ (puncturedAffinePlaneOf k).openImmersion =
      generalLinearTwoToAffinePlane k :=
  IsOpenImmersion.lift_fac (puncturedAffinePlaneOf k).U.ι (generalLinearTwoToAffinePlane k)
    (range_generalLinearTwoToAffinePlane_subset k)

/-- **Stacks Project, Tag 01KX (gl2_to_punctured_plane_surjective).** The morphism from `GL₂` to
the punctured affine plane is surjective. -/
@[stacks 01KX "gl2_to_punctured_plane_surjective"]
instance surjective_generalLinearTwoToPuncturedPlane :
    Surjective (generalLinearTwoToPuncturedPlane k) := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ : (puncturedAffinePlaneOf k).openImmersion.base y ∈
      Set.range (generalLinearTwoToAffinePlane k).base :=
    (range_comap_generalLinearTwoFirstRowHom k).ge
      ((range_puncturedAffinePlane_openImmersion (puncturedAffinePlaneOf k)).le ⟨y, rfl⟩)
  refine ⟨z, (puncturedAffinePlaneOf k).U.ι.isOpenEmbedding.injective ?_⟩
  change (generalLinearTwoToPuncturedPlane k ≫
    (puncturedAffinePlaneOf k).openImmersion).base z = _
  rwa [generalLinearTwoToPuncturedPlane_comp_openImmersion]

/-- **Stacks Project, Tag 01KX (image_in_no_affine_open).** The image of the morphism from `GL₂`
to the punctured affine plane is contained in no affine open of the punctured plane: it is
everything, and the punctured plane is not affine. -/
@[stacks 01KX "image_in_no_affine_open"]
theorem not_range_subset_of_isAffineOpen
    (V : ((puncturedAffinePlaneOf k).puncturedScheme).Opens) (hV : IsAffineOpen V) :
    ¬ Set.range (generalLinearTwoToPuncturedPlane k).base ⊆ (V : Set _) := by
  intro hsub
  obtain rfl : V = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_univ_subset ?_)
    rwa [← Set.range_eq_univ.mpr (generalLinearTwoToPuncturedPlane k).surjective]
  have htop : IsAffine
      (⊤ : ((puncturedAffinePlaneOf k).puncturedScheme).Opens).toScheme := hV
  exact not_isAffine_puncturedScheme (puncturedAffinePlaneOf k)
    (IsAffine.of_isIso ((puncturedAffinePlaneOf k).puncturedScheme).topIso.inv)

end Punctured

end AlgebraicGeometry

end
