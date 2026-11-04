module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Defs
public import StacksFrontier.RingTheory.Branches.Henselization

/-!
# Maximal ideals of the normalization of a local ring with two geometric branches

Let `A` be a reduced Noetherian local ring and let `A' = integralClosure A (FractionRing A)` be
its normalization in its total ring of fractions.  Counting each maximal ideal of `A'` with
multiplicity the separable degree of the corresponding residue-field extension gives the number
of geometric branches of `A` (Stacks 0C37).  Since every such multiplicity is at least one, a
ring with exactly two geometric branches has one or two maximal ideals in its normalization.

This is the quantitative half of the final assertion of Stacks 0C4A, isolated from the nodality
hypothesis: 0C4A derives "two geometric branches" from nodality, and that implication is not
available yet, but the step from the branch count to the count of maximal ideals is independent
of it and is proved here.

Because Stacks 0C37 is stated for the integral closure of `A` in the total ring of fractions of
`A ⧸ nilradical A`, the file also provides the transport of that normalization, and of its
maximal spectrum, across the identification `A ⧸ nilradical A ≃+* A` available for a reduced
ring.

## Main definitions

* `Stacks.Curves.maximalSpectrumCongr` — the bijection on maximal spectra induced by a ring
  isomorphism.
* `Stacks.Curves.quotNilradicalRingEquiv` — the reduction of a reduced ring is the ring itself.
* `Stacks.Curves.fractionRingQuotNilradicalAlgEquiv` — the total ring of fractions of the
  reduction of a reduced ring, as an `A`-algebra, is its total ring of fractions.
* `Stacks.Curves.integralClosureQuotNilradicalAlgEquiv` — the induced identification of the two
  spellings of the normalization.

## Main results

* `Stacks.Curves.encard_maximalSpectrum_integralClosure_eq_one_or_two_of_two_geometricBranches`
  — a reduced Noetherian local ring with two geometric branches has one or two maximal ideals in
  its normalization.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C37](https://stacks.math.columbia.edu/tag/0C37)
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Stacks.Curves

/-! ### Transport along a ring isomorphism -/

/-- The maximal spectra of isomorphic commutative rings are in bijection, by contraction of
ideals along the isomorphism. -/
public def maximalSpectrumCongr {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : MaximalSpectrum R ≃ MaximalSpectrum S where
  toFun m :=
    ⟨m.asIdeal.comap e.symm.toRingHom,
      Ideal.comap_isMaximal_of_surjective _ e.symm.surjective⟩
  invFun m :=
    ⟨m.asIdeal.comap e.toRingHom, Ideal.comap_isMaximal_of_surjective _ e.surjective⟩
  left_inv m := by
    refine MaximalSpectrum.ext ?_
    change (m.asIdeal.comap e.symm.toRingHom).comap e.toRingHom = m.asIdeal
    rw [Ideal.comap_comap]
    ext x
    simp
  right_inv m := by
    refine MaximalSpectrum.ext ?_
    change (m.asIdeal.comap e.toRingHom).comap e.symm.toRingHom = m.asIdeal
    rw [Ideal.comap_comap]
    ext x
    simp

/-- For a reduced ring the quotient by the nilradical is the ring itself. -/
public def quotNilradicalRingEquiv (A : Type u) [CommRing A] [IsReduced A] :
    A ⧸ nilradical A ≃+* A :=
  (Ideal.quotEquivOfEq (by simp [nilradical_eq_zero])).trans (RingEquiv.quotientBot A)

/-- The isomorphism `quotNilradicalRingEquiv A` sends the class of `x` to `x`. -/
@[simp]
public theorem quotNilradicalRingEquiv_mk (A : Type u) [CommRing A] [IsReduced A] (x : A) :
    quotNilradicalRingEquiv A (Ideal.Quotient.mk _ x) = x := rfl

/-- The total ring of fractions of the reduction of a reduced ring is a total ring of fractions
of the ring itself. -/
public theorem isFractionRing_fractionRing_quotNilradical (A : Type u) [CommRing A]
    [IsReduced A] : IsFractionRing A (FractionRing (A ⧸ nilradical A)) :=
  IsFractionRing.of_ringEquiv_left (quotNilradicalRingEquiv A).symm fun _ => rfl

/-- The total ring of fractions of the reduction of a reduced ring is, as an `A`-algebra, the
total ring of fractions of the ring itself. -/
public noncomputable def fractionRingQuotNilradicalAlgEquiv (A : Type u) [CommRing A]
    [IsReduced A] : FractionRing (A ⧸ nilradical A) ≃ₐ[A] FractionRing A :=
  let := isFractionRing_fractionRing_quotNilradical A
  IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing (A ⧸ nilradical A)) (FractionRing A)

/-- The two spellings of the normalization of a reduced ring — the integral closure in the total
ring of fractions of its reduction and the integral closure in its own total ring of fractions —
agree as `A`-algebras. -/
public noncomputable def integralClosureQuotNilradicalAlgEquiv (A : Type u) [CommRing A]
    [IsReduced A] :
    ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ≃ₐ[A]
      ↥(integralClosure A (FractionRing A)) :=
  (fractionRingQuotNilradicalAlgEquiv A).mapIntegralClosure

/-! ### Counting maximal ideals -/

/-- An extended natural number which is nonzero and at most two is one or two. -/
private theorem eq_one_or_two_of_ne_zero_of_le_two {n : ℕ∞} (h0 : n ≠ 0) (h2 : n ≤ 2) :
    n = 1 ∨ n = 2 := by
  have hne : n ≠ ⊤ := by intro h; rw [h] at h2; simp at h2
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hne
  have h2' : m ≤ 2 := by exact_mod_cast h2
  have h0' : m ≠ 0 := by simpa using h0
  interval_cases m
  · simp at h0'
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A sigma type over a family of nonempty types is at least as large as its index type. -/
private theorem enatCard_le_enatCard_sigma {ι : Type*} {T : ι → Type*}
    (h : ∀ i, Nonempty (T i)) : ENat.card ι ≤ ENat.card (Σ i, T i) := by
  classical
  exact ENat.card_le_card_of_injective (f := fun i => (⟨i, (h i).some⟩ : Σ i, T i))
    fun _ _ hab => by simpa using congrArg Sigma.fst hab

/-- The type of ordinals below the initial ordinal of a nonzero cardinal is nonempty. -/
private theorem nonempty_ord_toType {c : Cardinal} (h : c ≠ 0) : Nonempty c.ord.ToType := by
  rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
  exact h

/-- The type indexing a separable degree is nonempty, since a separable degree is never zero. -/
private theorem nonempty_ord_toType_sepDegree (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Nonempty (Field.sepDegree F E).ord.ToType :=
  nonempty_ord_toType (NeZero.ne _)

/-- **Stacks 0C4A** (the counting step of the final assertion). Let `A` be a reduced Noetherian
local ring with exactly two geometric branches. Then the integral closure of `A` in its total
ring of fractions has one or two maximal ideals.

This is the branch-count half of the final assertion of Stacks 0C4A; the derivation of the
branch count from nodality is a separate step. -/
public theorem
    encard_maximalSpectrum_integralClosure_eq_one_or_two_of_two_geometricBranches
    (A : Type u) (Ah : Type u) (Ash : Type u) (ksep : Type v)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah]
    [Field ksep] [Algebra (ResidueField A) ksep] [IsSepClosure (ResidueField A) ksep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsLocalRing.IsHenselization A ksep Ash]
    (hbranches : numberOfGeometricBranches A ksep Ash = 2) :
    Set.encard (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) = 1 ∨
      Set.encard
        (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) = 2 := by
  classical
  obtain ⟨-, -, -, hfin⟩ := numberOfBranches_characterizations A Ah Ash ksep
  obtain ⟨-, hcontract, hgeo⟩ := hfin (minimalPrimes.finite_of_isNoetherianRing A)
  have hcard :
      ENat.card (MaximalSpectrum ↥(integralClosure A (FractionRing (A ⧸ nilradical A)))) ≤ 2 := by
    rw [← hbranches, hgeo]
    refine enatCard_le_enatCard_sigma ?_
    intro m'
    let fieldQuot : Field (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m'.asIdeal) :=
      Ideal.Quotient.field m'.asIdeal
    let algQuot : Algebra (ResidueField A)
        (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m'.asIdeal) :=
      (Ideal.quotientMap m'.asIdeal
        (algebraMap A ↥(integralClosure A (FractionRing (A ⧸ nilradical A))))
        (le_of_eq (hcontract m'))).toAlgebra
    exact nonempty_ord_toType_sepDegree (ResidueField A)
      (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m'.asIdeal)
  have : Nontrivial (A ⧸ nilradical A) :=
    Submodule.Quotient.nontrivial_iff.mpr (by simp [nilradical_eq_zero])
  have : Nontrivial (FractionRing (A ⧸ nilradical A)) := OreLocalization.nontrivial
  have : Nontrivial ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) :=
    SubsemiringClass.nontrivial _
  have hnz :
      ENat.card (MaximalSpectrum ↥(integralClosure A (FractionRing (A ⧸ nilradical A)))) ≠ 0 :=
    (ENat.card_ne_zero_iff_nonempty _).mpr inferInstance
  have htransport :
      ENat.card (MaximalSpectrum ↥(integralClosure A (FractionRing A))) =
        ENat.card (MaximalSpectrum ↥(integralClosure A (FractionRing (A ⧸ nilradical A)))) :=
    (ENat.card_congr
      (maximalSpectrumCongr (integralClosureQuotNilradicalAlgEquiv A).toRingEquiv)).symm
  rw [Set.encard_univ, htransport]
  exact eq_one_or_two_of_ne_zero_of_le_two hnz hcard

end Stacks.Curves

end
