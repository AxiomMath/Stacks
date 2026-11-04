module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TruncatingApproximations

/-!
# Truncating a strictly perfect approximation at an arbitrary ring universe

This file is the universe-general form of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/TruncatingApproximations.lean`.
That file states its results for a sheaf of rings `R : Sheaf J RingCat.{0}` and modules in
`SheafOfModules.{0} R`; everything it uses is available at an arbitrary ring universe `w`,
because `IsDirectSummandOfFiniteFree` and `IsStrictlyPerfect` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/ConeOfAMorphism.lean` are stated
at four independent universes and, at module universe equal to ring universe, reduce to the
plain retract condition by `isDirectSummandOfFiniteFree_iff_free`.

The statements and proofs below are the ones of that file with `0` replaced by `w`
throughout. They are restated rather than generalized in place because the file they come from
is owned elsewhere; see the implementation notes.

## Main results

* `IsDirectSummandOfFiniteFree.of_isZero_general`: a zero `O`-module is a direct summand of a
  finite free `O`-module.
* `IsDirectSummandOfFiniteFree.of_retract_general`: being a direct summand of a finite free
  `O`-module passes to retracts.
* `SheafOfModules.isZero_truncLE_X_general`: the canonical truncation in degrees `≤ r` has no
  terms above degree `r`.
* `SheafOfModules.isStrictlyPerfect_truncLE_general`: the canonical truncation `τ^{≤r} P` of a
  strictly perfect complex is strictly perfect provided its degree-`r` cycles are a direct
  summand of a finite free `O`-module.
* `SheafOfModules.isLE_of_isIso_homologyMap_general`: an approximation in degrees `≥ m` of a
  complex with no cohomology above `r ≥ m` has itself no cohomology above `r`.
* `SheafOfModules.exists_isStrictlyPerfect_boundedAbove_of_approximation_general`: the
  truncated approximation, packaged as the existence statement that a local approximation
  argument consumes.

## Implementation notes

The `0` in the source file is not forced by anything: the predicate carrying Stacks 08FL keeps
the ring universe and the module universe independent, and the only other inputs are Mathlib's
canonical truncation and `CochainComplex.quasiIso_ιTruncLE_iff`, both universe-polymorphic. The
generalization is therefore a literal replacement of `0` by `w`, with no change to any proof.

Only the `truncLE` half is restated: the `truncGE` half
(`SheafOfModules.isStrictlyPerfect_truncGE`) is used by the perfectness criterion of Stacks
08G7, not by the bounded-above local approximation, and nothing here needs it.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A zero `O`-module is a direct summand of a finite free `O`-module, namely of `O^{⊕0}`:
both composites out of a zero object agree with the identity.

The universe-general form of `IsDirectSummandOfFiniteFree.of_isZero`. -/
lemma IsDirectSummandOfFiniteFree.of_isZero_general {F : SheafOfModules.{w} R} (hF : IsZero F) :
    IsDirectSummandOfFiniteFree R F :=
  (isDirectSummandOfFiniteFree_iff_free R F).mpr ⟨0, 0, 0, hF.eq_of_src _ _⟩

/-- A retract of a direct summand of a finite free `O`-module is again a direct summand of a
finite free `O`-module: compose the two retractions.

The universe-general form of `IsDirectSummandOfFiniteFree.of_retract`. -/
lemma IsDirectSummandOfFiniteFree.of_retract_general {F G : SheafOfModules.{w} R}
    (ρ : Retract F G) (hG : IsDirectSummandOfFiniteFree R G) :
    IsDirectSummandOfFiniteFree R F := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R G).mp hG
  refine (isDirectSummandOfFiniteFree_iff_free R F).mpr ⟨n, ρ.i ≫ i, r ≫ ρ.r, ?_⟩
  rw [Category.assoc, ← Category.assoc i, hir, Category.id_comp, ρ.retract]

namespace SheafOfModules

variable {R}

/-- The canonical truncation in degrees `≤ r` has no terms above degree `r`.

The universe-general form of `SheafOfModules.isZero_truncLE_X`. -/
theorem isZero_truncLE_X_general (P : CochainComplex (SheafOfModules.{w} R) ℤ) (r : ℤ) {i : ℤ}
    (hi : r < i) : IsZero ((P.truncLE r).X i) :=
  (P.truncLE r).isZero_of_isStrictlyLE r i hi

/-- The canonical truncation in degrees `≤ r` of a strictly perfect complex of `O`-modules is
strictly perfect, provided its degree-`r` cycles are a direct summand of a finite free
`O`-module.

Below degree `r` the truncation agrees with `P`, in degree `r` it is the cycles object, and
above `r` it vanishes; only the middle case needs the extra hypothesis.

The universe-general form of `SheafOfModules.isStrictlyPerfect_truncLE`. -/
theorem isStrictlyPerfect_truncLE_general {P : CochainComplex (SheafOfModules.{w} R) ℤ}
    (hP : IsStrictlyPerfect R P) (r : ℤ)
    (hcyc : IsDirectSummandOfFiniteFree R (P.cycles r)) :
    IsStrictlyPerfect R (P.truncLE r) where
  bounded := by
    refine Set.Finite.subset (hP.bounded.union (Set.finite_singleton r)) ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    rcases lt_trichotomy i r with h | h | h
    · exact Or.inl fun hz => hi (hz.of_iso (P.truncLEXIso r i h))
    · exact Or.inr (by simp [h])
    · exact absurd (isZero_truncLE_X_general P r h) hi
  termDirectSummand i := by
    rcases lt_trichotomy i r with h | h | h
    · exact IsDirectSummandOfFiniteFree.of_iso R (P.truncLEXIso r i h)
        (hP.termDirectSummand i)
    · subst h
      exact IsDirectSummandOfFiniteFree.of_iso R (P.truncLEXIsoCycles i) hcyc
    · exact IsDirectSummandOfFiniteFree.of_isZero_general R (isZero_truncLE_X_general P r h)

/-- An approximation in degrees `≥ m` of a complex of `O`-modules without cohomology above
`r ≥ m` has itself no cohomology above `r`: in that range the approximation is an isomorphism
on cohomology.

The universe-general form of `SheafOfModules.isLE_of_isIso_homologyMap`. -/
theorem isLE_of_isIso_homologyMap_general {P G : CochainComplex (SheafOfModules.{w} R) ℤ}
    (m r : ℤ) (hmr : m ≤ r) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) : P.IsLE r := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : IsIso (HomologicalComplex.homologyMap α i) := hiso i (lt_of_le_of_lt hmr hi)
  exact (hG i hi).of_iso (asIso (HomologicalComplex.homologyMap α i))

/-- **Truncating an approximation on a ringed site, at an arbitrary ring universe.** If
`α : P ⟶ G` is an approximation in degrees `≥ m` of a complex `G` of `O`-modules with no
cohomology above `r`, if `m ≤ r`, if `P` is strictly perfect and if the degree-`r` cycles of `P`
are a direct summand of a finite free `O`-module, then `G` admits an approximation in degrees
`≥ m` by a strictly perfect complex with no terms above degree `r`.

The universe-general form of
`SheafOfModules.exists_isStrictlyPerfect_boundedAbove_of_approximation`. -/
theorem exists_isStrictlyPerfect_boundedAbove_of_approximation_general
    {P G : CochainComplex (SheafOfModules.{w} R) ℤ} (hP : IsStrictlyPerfect R P) (m r : ℤ)
    (hmr : m ≤ r) (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (hcyc : IsDirectSummandOfFiniteFree R (P.cycles r)) :
    ∃ Q : CochainComplex (SheafOfModules.{w} R) ℤ, IsStrictlyPerfect R Q ∧
      (∀ i : ℤ, r < i → IsZero (Q.X i)) ∧
      ∃ β : Q ⟶ G, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) := by
  have : P.IsLE r := isLE_of_isIso_homologyMap_general m r hmr α hiso hG
  have hι : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap (P.ιTruncLE r) j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap _ j).1 (QuasiIso.quasiIsoAt (f := P.ιTruncLE r) j)
  refine ⟨P.truncLE r, isStrictlyPerfect_truncLE_general hP r hcyc,
    fun i hi => isZero_truncLE_X_general P r hi, P.ιTruncLE r ≫ α, fun j hj => ?_, ?_⟩
  · rw [HomologicalComplex.homologyMap_comp]
    exact IsIso.comp_isIso' (hι j) (hiso j hj)
  · rw [HomologicalComplex.homologyMap_comp]
    have := hι m
    exact epi_comp _ _

end SheafOfModules

end
