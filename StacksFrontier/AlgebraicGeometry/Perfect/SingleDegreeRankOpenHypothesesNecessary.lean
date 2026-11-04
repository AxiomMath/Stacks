module

public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankBettiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenInt
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenAffine
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CanonicalTruncation

/-!
# Which hypotheses of the single-degree rank locus are load-bearing

The pointwise description of the open subscheme of [stacks 0BDK] through the derived-fibre Betti
numbers,
`AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_of_derivedFiberBetti`, has two
conditions on the point: the Betti numbers vanish off degree `i`, and the one in degree `i` equals
`r`. This file proves that **neither may be dropped**, and exhibits the whole situation at a
non-degenerate value.

Everything is tested on one object: the structure sheaf placed in degree zero. It is perfect, so
it satisfies the source's hypothesis; its Betti numbers are `β_0 = 1` and `β_j = 0` for `j ≠ 0`
at every point; and its single-degree rank locus is the whole scheme at `(i, r) = (0, 1)` and has
no points at any other `(i, r)`.

## Main results

All names below are in the namespace `AlgebraicGeometry.Scheme.Modules`.

* `isPerfect_singleFunctor_unit`: the structure sheaf placed in degree zero is a **perfect** object
  of `D(𝒪_X)`. This is an inhabitant of the perfectness hypothesis of the statement of
  [stacks 0BDK], and it is not the zero object — its degree-zero Betti number is `1`.
* `singleDegreeRankOpen_singleFunctor_unit_eq_top`: at `(i, r) = (0, 1)` the open subscheme is the
  **whole** scheme, so the universal property of [stacks 0BDK] is asserted at a nonempty open
  subscheme and is not vacuous.
* `eq_of_mem_singleDegreeRankOpen_singleFunctor_unit`: and at every other `(i, r)` it has no
  points.
* `not_forall_mem_singleDegreeRankOpen_of_derivedFiberBetti_eq_rank` and
  `not_forall_mem_singleDegreeRankOpen_of_derivedFiberBetti_eq_zero`: the two negative controls,
  as proved negations.

## Implementation notes

*The two controls.* Dropping the vanishing condition and keeping the rank one leaves the claim
"`β_i(x) = r` puts `x` in the locus", which fails at `i = 1`, `r = 0` on the structure sheaf:
`β_1 = 0 = r`, yet the locus at `(1, 0)` has no points because `β_0 = 1 ≠ 0`. Dropping the rank
condition and keeping the vanishing one leaves "`β_j(x) = 0` for `j ≠ i` puts `x` in the locus",
which fails at `i = 0`, `r = 5`: the vanishing holds, yet the locus at `(0, 5)` has no points
because `β_0 = 1 ≠ 5`. Both refutations use only the *forward* half of the pointwise description,
so they are independent of its converse.

*The scheme used.* The two controls are stated at an arbitrary scheme **with a point**, so each is
a refutation on every nonempty scheme rather than on one example. A point is what the refutations
need: on an empty scheme every locus statement is vacuously true, which is exactly the degenerate
reading they rule out. That hypothesis is inhabited: `Spec (ULift ℤ)` is nonempty by instance
search, its points being the primes of `ℤ`.

*Perfectness of the structure sheaf in degree zero.* The complex concentrated in degree zero on
`𝒪_X` is strictly perfect and vanishes below degree zero, so
`Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_isStrictlyPerfect_of_isZero_X` applies.

*No Stacks attribute.* These are statements about particular schemes and particular objects, and
refutations of statements the tag does not make; they are not clauses of [stacks 0BDK].

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
* [The Stacks Project, Lemma 36.31.1 (0BDI)](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The structure sheaf in degree zero is perfect -/

/-- **The structure sheaf placed in degree zero is a perfect object of `D(𝒪_X)`.** The complex
concentrated in degree zero on `𝒪_X` is strictly perfect and vanishes in every negative degree. -/
theorem isPerfect_singleFunctor_unit (X : Scheme.{u}) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    (((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
      (SheafOfModules.unit X.ringCatSheaf)).symm)
    (Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_isStrictlyPerfect_of_isZero_X
      ((CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
      (StrictlyPerfect.isStrictlyPerfect_single
        (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule X.toRingedSpace) 0)
      0 fun _ hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))

/-- **The structure sheaf is flat.** It is finite locally free of rank one. -/
theorem isFlat_unit (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (SheafOfModules.unit X.ringCatSheaf) :=
  AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFreeOfRank _ 1
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X)

/-- **The derived-fibre Betti numbers of the structure sheaf vanish off degree zero.** -/
theorem derivedFiberBetti_singleFunctor_unit_eq_zero (X : Scheme.{u}) (j : ℤ) (hj : j ≠ 0)
    (x : X) :
    DerivedFibreBetti.derivedFiberBetti X
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
        (BottomRankStratum.isPseudoCoherent_singleFunctor_unit X) j x = 0 :=
  BottomRankStratum.derivedFiberBetti_single_eq_zero _ 0 (isFlat_unit X)
    (BottomRankStratum.isPseudoCoherent_singleFunctor_unit X) j hj x

/-! ### The single-degree rank locus of the structure sheaf -/

/-- **The single-degree rank locus of the structure sheaf has points only at `(0, 1)`.** If a
point of `X` lies in the locus of `𝒪_X[0]` in degree `i` with rank `r`, then `i = 0` and `r = 1`.

The forward half of the pointwise description says that at such a point `β_j = 0` for `j ≠ i` and
`β_i = r`; the structure sheaf has `β_0 = 1`, which forces `i = 0` and then `r = 1`. -/
theorem eq_of_mem_singleDegreeRankOpen_singleFunctor_unit (X : Scheme.{u}) (i : ℤ) (r : ℕ)
    {x : X}
    (hx : x ∈ singleDegreeRankOpen ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) i r) :
    i = 0 ∧ r = 1 := by
  have h0 := BottomRankStratum.derivedFiberBetti_singleFunctor_unit X x
  by_cases hi : i = 0
  · subst hi
    refine ⟨rfl, ?_⟩
    have hr := derivedFiberBetti_eq_rank_of_mem_singleDegreeRankOpen _
      (BottomRankStratum.isPseudoCoherent_singleFunctor_unit X) 0 r hx
    omega
  · exact absurd (derivedFiberBetti_eq_zero_of_mem_singleDegreeRankOpen _
      (BottomRankStratum.isPseudoCoherent_singleFunctor_unit X) i r 0 (Ne.symm hi) hx)
      (by omega)

/-- **At `(i, r) = (0, 1)` the single-degree rank locus of the structure sheaf is the whole
scheme.** So the universal property of [stacks 0BDK] is asserted at a nonempty open subscheme
whenever `X` is nonempty, and the data binders of its conclusion are inhabited by the restriction
of the structure sheaf. -/
theorem singleDegreeRankOpen_singleFunctor_unit_eq_top (X : Scheme.{u}) :
    singleDegreeRankOpen ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) 0 1 = ⊤ := by
  refine top_le_iff.1 (le_singleDegreeRankOpen _ 0 1 ((isSingleDegreeRank_iff _ 0 1 ⊤).2
    ⟨(restrictFunctor (⊤ : X.Opens).ι).obj (SheafOfModules.unit X.ringCatSheaf), ?_, ?_⟩))
  · exact (isFiniteLocallyFreeOfRank_iff _ 1).1
      (((isFiniteLocallyFreeOfRank_iff _ 1).2
        (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X)).restrict
          (⊤ : X.Opens).ι)
  · exact ⟨((restrictFunctor (⊤ : X.Opens).ι).mapDerivedCategorySingleFunctor 0).app _⟩

/-! ### The two negative controls -/

/-- **A point of `X` lies in no single-degree rank locus of the structure sheaf other than the one
in degree zero with rank one.** -/
theorem not_mem_singleDegreeRankOpen_singleFunctor_unit (X : Scheme.{u}) (i : ℤ) (r : ℕ)
    (h : ¬(i = 0 ∧ r = 1)) (x : X) :
    x ∉ singleDegreeRankOpen ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) i r :=
  fun hx => h (eq_of_mem_singleDegreeRankOpen_singleFunctor_unit X i r hx)

/-- **The vanishing condition of the pointwise description may not be dropped.** On any scheme
with a point it is *false* that a point at which the derived-fibre Betti number in degree `i`
equals `r` lies in the single-degree rank locus in degree `i` with rank `r`, even for a perfect
object.

The witness is the structure sheaf in degree zero at `i = 1`, `r = 0`: its Betti number in degree
`1` is `0 = r`, so the retained hypothesis holds, yet the locus at `(1, 0)` has no points because
the Betti number in degree `0` is `1`, not `0`. -/
theorem not_forall_mem_singleDegreeRankOpen_of_derivedFiberBetti_eq_rank
    (X : Scheme.{u}) (x : X) :
    ¬ ∀ (E : DerivedCategory X.Modules)
        (_hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
        (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
        (i : ℤ) (r : ℕ) (y : X),
        DerivedFibreBetti.derivedFiberBetti X E hPC i y = r →
          y ∈ singleDegreeRankOpen E i r := by
  intro h
  refine not_mem_singleDegreeRankOpen_singleFunctor_unit X 1 0 (by omega) x ?_
  exact h _ (isPerfect_singleFunctor_unit X)
    (BottomRankStratum.isPseudoCoherent_singleFunctor_unit X) 1 0 x
    (derivedFiberBetti_singleFunctor_unit_eq_zero X 1 (by omega) x)

/-- **The rank condition of the pointwise description may not be dropped.** On any scheme with a
point it is *false* that a point at which the derived-fibre Betti numbers vanish off degree `i`
lies in the single-degree rank locus in degree `i` with rank `r`, even for a perfect object.

The witness is the structure sheaf in degree zero at `i = 0`, `r = 5`: its Betti numbers do vanish
off degree `0`, so the retained hypothesis holds, yet the locus at `(0, 5)` has no points, its
degree-zero Betti number being `1`. -/
theorem not_forall_mem_singleDegreeRankOpen_of_derivedFiberBetti_eq_zero
    (X : Scheme.{u}) (x : X) :
    ¬ ∀ (E : DerivedCategory X.Modules)
        (_hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
        (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
        (i : ℤ) (r : ℕ) (y : X),
        (∀ j : ℤ, j ≠ i → DerivedFibreBetti.derivedFiberBetti X E hPC j y = 0) →
          y ∈ singleDegreeRankOpen E i r := by
  intro h
  refine not_mem_singleDegreeRankOpen_singleFunctor_unit X 0 5 (by omega) x ?_
  exact h _ (isPerfect_singleFunctor_unit X)
    (BottomRankStratum.isPseudoCoherent_singleFunctor_unit X) 0 5 x
    fun j hj => derivedFiberBetti_singleFunctor_unit_eq_zero X j hj x

end AlgebraicGeometry.Scheme.Modules

end
