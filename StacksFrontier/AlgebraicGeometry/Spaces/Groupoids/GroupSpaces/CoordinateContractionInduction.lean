module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.NoRationalCurves

/-!
# Iterating a one-step contraction of a power of the projective line

Let `k` be a field and `B` a big fppf site containing `Spec k`.  The proof of
[Stacks, Tag 0AEM] reaches its factorization by *repeating a process*: as long as the morphism
under consideration has an infinite fibre over some point of the target, it is contracted —
it factors through the projection onto a strictly smaller set of coordinates — and the process
restarts with the second factor.  Since the number of coordinates drops at every step the
process stops, and it stops exactly when all the fibres on points are finite.

This file is that iteration, and nothing else: the one-step contraction is an explicit
hypothesis `step` and the geometry is elsewhere.  What is proved here is that `step` is enough,
that the recursion terminates, and that the composite of the projections met along the way is
again a coordinate projection.

## Main definitions

* `AlgebraicGeometry.Space.subsetProjection`: the projection of the power of the projective
  line indexed by a finite subset `I` of `Fin n` onto the power indexed by a subset `J ⊆ I`.

## Main results

* `AlgebraicGeometry.Space.coordinateProjection_comp_subsetProjection` and
  `AlgebraicGeometry.Space.subsetProjection_comp_subsetProjection`: the projections compose
  as the inclusions do, so a chain of contractions is a single coordinate projection.
* `AlgebraicGeometry.Space.exists_subsetProjection_finite_fibres_of_contraction_step`: the
  iteration itself, run on the power indexed by a subset of the coordinates.
* `AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_contraction_step`: the
  iteration started at the full set of coordinates.  Given the one-step contraction for every
  subset of the coordinates, every morphism from `(ℙ¹_k)^n` factors through the projection
  onto some subset of the coordinates by a morphism all of whose fibres on points are finite.

## Implementation notes

The recursion is a strong induction on the finite subset of the coordinates that survives,
ordered by strict inclusion (`Finset.strongInduction`), so no cardinality bookkeeping is
needed: the one-step contraction is asked to return a subset which is contained in the current
one and distinct from it, which is exactly the relation the induction is on.

The induction runs over the powers indexed by subsets `I ⊆ Fin n` rather than over `Fin m` for
varying `m`, so that the projections compose on the nose and the subset produced at the end is
literally a subset of `Fin n`; the statement of 0AEM is reached from the case `I = Finset.univ`
through `AlgebraicGeometry.Space.coordinateProjectionUnivIso`.

## References

* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-! ### Projections between the powers indexed by nested subsets of the coordinates -/

/-- The projection of the power of the projective line indexed by a finite subset `I` of
`Fin n` onto the power indexed by a subset `J ⊆ I`. -/
noncomputable abbrev subsetProjection {n : ℕ} {I J : Finset (Fin n)} (h : J ⊆ I) :
    projectiveLinePower k B hk I ⟶ projectiveLinePower k B hk J :=
  Pi.map' (fun j : J => (⟨(j : Fin n), h j.2⟩ : I)) fun _ => 𝟙 _

/-- Projecting a finite power of the projective line onto the coordinates in `I` and then onto
the coordinates in a subset `J ⊆ I` is the projection onto the coordinates in `J`. -/
theorem coordinateProjection_comp_subsetProjection {n : ℕ} {I J : Finset (Fin n)} (h : J ⊆ I) :
    coordinateProjection k B hk n I ≫ subsetProjection k B hk h =
      coordinateProjection k B hk n J := by
  apply Pi.hom_ext
  intro j
  simp

/-- The projection of a power of the projective line onto all of its own coordinates is the
identity. -/
@[simp]
theorem subsetProjection_rfl {n : ℕ} (I : Finset (Fin n)) :
    subsetProjection k B hk (subset_rfl : I ⊆ I) = 𝟙 (projectiveLinePower k B hk I) := by
  apply Pi.hom_ext
  intro j
  simp

/-- Projecting onto the coordinates in `J ⊆ I` and then onto those in `L ⊆ J` is the projection
onto the coordinates in `L`. -/
theorem subsetProjection_comp_subsetProjection {n : ℕ} {I J L : Finset (Fin n)} (hJ : J ⊆ I)
    (hL : L ⊆ J) :
    subsetProjection k B hk hJ ≫ subsetProjection k B hk hL =
      subsetProjection k B hk (hL.trans hJ) := by
  apply Pi.hom_ext
  intro j
  simp

/-! ### The iteration -/

variable {k B hk}

/-- **The one-step contraction of [Stacks, Tag 0AEM], iterated.**  Let `Z` be a presheaf on the
big fppf site over `Spec k` and suppose that every morphism to `Z` from the power of the
projective line indexed by a finite subset `I` of `Fin n` which has an infinite fibre over some
point of `Z` factors through the projection onto a strictly smaller subset of `I`.  Then every
such morphism factors through the projection onto some subset of `I` by a morphism all of whose
fibres on points are finite.

The recursion is on `I` ordered by strict inclusion, and the projections met along the way
compose to a single one by
`AlgebraicGeometry.Space.subsetProjection_comp_subsetProjection`. -/
theorem exists_subsetProjection_finite_fibres_of_contraction_step {n : ℕ}
    {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (step : ∀ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      (¬ ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
        {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) |
          pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) g x =
            y}.Finite) →
      ∃ (J : Finset (Fin n)) (hJI : J ⊆ I), J ≠ I ∧
        ∃ g' : projectiveLinePower k B hk J ⟶ Z, g = subsetProjection k B hk hJI ≫ g')
    (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z) :
    ∃ (J : Finset (Fin n)) (hJI : J ⊆ I) (g' : projectiveLinePower k B hk J ⟶ Z),
      g = subsetProjection k B hk hJI ≫ g' ∧
        ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
          {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk J) |
            pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk J) g' x =
              y}.Finite := by
  induction I using Finset.strongInduction with
  | _ I ih =>
    by_cases hfin : ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
        {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) |
          pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) g x =
            y}.Finite
    · exact ⟨I, subset_rfl, g, by rw [subsetProjection_rfl, Category.id_comp], hfin⟩
    · obtain ⟨J, hJI, hJne, g', hg'⟩ := step I g hfin
      obtain ⟨L, hLJ, g'', hg'', hfib⟩ := ih J (lt_of_le_of_ne hJI hJne) g'
      refine ⟨L, hLJ.trans hJI, g'', ?_, hfib⟩
      rw [hg', hg'', ← Category.assoc, subsetProjection_comp_subsetProjection]

/-- **The one-step contraction of [Stacks, Tag 0AEM] gives the factorization of 0AEM, with the
finiteness of the fibres on points in place of the finiteness of the second morphism.**  Let
`Z` be a presheaf on the big fppf site over `Spec k` and suppose that every morphism to `Z`
from the power of the projective line indexed by a finite subset of `Fin n` which has an
infinite fibre over some point of `Z` factors through the projection onto a strictly smaller
subset.  Then every morphism `(ℙ¹_k)^n ⟶ Z` factors through the projection onto some subset of
the coordinates by a morphism all of whose fibres on points are finite.

This is the iteration started at the full set of coordinates: the projection onto all of them
is an isomorphism (`AlgebraicGeometry.Space.coordinateProjectionUnivIso`), so the morphism to
start from is the given one composed with its inverse. -/
theorem exists_coordinateProjection_finite_fibres_of_contraction_step {n : ℕ}
    {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (step : ∀ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      (¬ ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
        {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) |
          pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) g x =
            y}.Finite) →
      ∃ (J : Finset (Fin n)) (hJI : J ⊆ I), J ≠ I ∧
        ∃ g' : projectiveLinePower k B hk J ⟶ Z, g = subsetProjection k B hk hJI ≫ g')
    (w : projectiveLinePower k B hk (Fin n) ⟶ Z) :
    ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      w = coordinateProjection k B hk n I ≫ g ∧
        ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
          {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) |
            pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) g x =
              y}.Finite := by
  obtain ⟨J, hJ, g, hg, hfib⟩ :=
    exists_subsetProjection_finite_fibres_of_contraction_step step Finset.univ
      ((coordinateProjectionUnivIso k B hk n).inv ≫ w)
  refine ⟨J, g, ?_, hfib⟩
  calc w = (coordinateProjectionUnivIso k B hk n).hom ≫
        (coordinateProjectionUnivIso k B hk n).inv ≫ w :=
      (Iso.hom_inv_id_assoc _ _).symm
    _ = coordinateProjection k B hk n Finset.univ ≫ subsetProjection k B hk hJ ≫ g := by
      rw [hg]; rfl
    _ = coordinateProjection k B hk n J ≫ g := by
      rw [← Category.assoc, coordinateProjection_comp_subsetProjection]

end AlgebraicGeometry.Space

end
