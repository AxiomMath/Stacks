module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.DimensionBound
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.Comparison
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ZeroLocusGeometry

/-!
# The local case of the cohomological dimension bound, in dimension zero

`StacksFrontier/RingTheory/LocalCohomology/VanishingTFAE/DimensionBound.lean` reduces both
assertions of Stacks 0DXC to the single statement

`B local, J finitely generated, dim B ≤ e ⟹ cd(B, J) ≤ e`,

and takes that statement as a hypothesis in two shapes: directly, and through the local form of
Kronecker's bound on the arithmetic rank of an ideal. This file does three things to that
hypothesis.

First it **proves the case `e = 0`** outright, for every ring, with no hypothesis beyond those of
the statement. In a local ring of Krull dimension at most zero the maximal ideal is the only
prime, so a finitely generated ideal `J` whose zero locus is nonempty is contained in every prime,
hence nilpotent; local cohomology is then the identity functor and vanishes in every nonzero
degree. The remaining case, `V(J) = ∅`, is
`Stacks.LocalCohomology.isZero_localCohomologyModule_of_zeroLocus_empty`.

Second it **refutes the arithmetic-rank hypothesis as stated**. The hypothesis of
`Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators`
quantifies over *every* finitely generated ideal of a local ring of dimension at most `e`,
including the unit ideal, whose zero locus is empty and which no family of at most `e = 0`
elements can cut out: the empty family spans `⊥`, whose zero locus is all of `Spec B`. So that
hypothesis holds for no `B` at all and the theorem is vacuous. A field witnesses this.

Third it **weakens both hypotheses** to their satisfiable form — a nonempty zero locus and a
positive bound — using the two cases proved here to discharge the difference. The resulting
theorems are strictly stronger than the ones they are derived from, and the obligation that
remains for Stacks 0DXC is correspondingly smaller.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_isIPowerTorsion` — local cohomology of
  an `I`-power-torsion module vanishes in every nonzero degree.
* `Stacks.LocalCohomology.cohomologicalDimension_le_zero_of_zeroLocus_eq_univ` — a finitely
  generated ideal contained in the nilradical has cohomological dimension at most zero.
* `Stacks.LocalCohomology.cohomologicalDimension_le_zero_of_isLocalRing` — **the case `e = 0` of
  the remaining statement of Stacks 0DXC**: a finitely generated ideal of a local ring of Krull
  dimension at most zero has cohomological dimension at most zero.
* `Stacks.LocalCohomology.not_forall_isLocalRing_exists_zeroLocus_generators_card_le` — the
  arithmetic-rank hypothesis of
  `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators`
  is false, so that theorem is vacuous as stated.
* `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_isLocalRing_of_one_le` and
  `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators'`
  — the two reductions of Stacks 0DXC with their hypotheses weakened to the cases this file does
  not settle.

## Implementation notes

`Stacks.LocalCohomology.cohomologicalDimension` is defined at module universe equal to the ring
universe, so the two results about it are stated there; the torsion vanishing lemma is stated at
an independent module universe, as the rest of the development does.

No Stacks tag attribute is placed here. What is proved is the case `e = 0` of the local
statement to which Stacks 0DXC reduces, not that tag; the tag is in
`StacksFrontier/RingTheory/LocalCohomology/CohomologicalDimension/KrullDimension.lean`.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
-/

@[expose] public noncomputable section

universe v u

namespace Stacks.LocalCohomology

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

/-- **Local cohomology is the identity functor on torsion modules.** For an `I`-power-torsion
module `M` the local cohomology `H^i_{V(I)}(M)` vanishes in every nonzero degree `i`.

The module placed in degree zero already lies in the full subcategory of `D(A)` on the objects
with `I`-power-torsion cohomology, so the unit of the adjunction of Stacks 0A6Q is an isomorphism
there and `RΓ_{V(I)}(M[0]) ≅ M[0]`; a module placed in degree zero has no cohomology in any other
degree. This is the companion in nonzero degrees of
`Stacks.LocalCohomology.localCohomologyZeroIsoOfTorsion`. -/
theorem isZero_localCohomologyModule_of_isIPowerTorsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (hM : IsIPowerTorsion A M I) (i : ℤ) (hi : i ≠ 0) :
    IsZero (localCohomologyModule A I hI M i) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  have hsingle : ∀ j : ℤ, j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj K) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · exact DerivedCategory.isZero_of_isGE K 0 j hj
    · exact DerivedCategory.isZero_of_isLE K 0 j hj
  have hK : Dualizing.derivedPowerTorsionProperty A I hI K := by
    intro j
    obtain rfl | hj := eq_or_ne j 0
    · exact isIPowerTorsion_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app M).symm hM
    · exact isIPowerTorsion_of_isZero (hsingle j hj)
  exact (hsingle i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso
      ((Dualizing.derivedPowerTorsionProperty A I hI).ι.mapIso
        (asIso ((Dualizing.localCohomologyAdjunction A I hI).unit.app ⟨K, hK⟩))).symm)

/-- Every module is `I`-power torsion for a nilpotent ideal `I`. -/
theorem isIPowerTorsion_of_isNilpotent {A : Type u} [CommRing A] {I : Ideal A}
    (hI : IsNilpotent I) (M : Type*) [AddCommGroup M] [Module A M] :
    IsIPowerTorsion A M I := by
  obtain ⟨n, hn⟩ := hI
  refine fun m => ⟨n + 1, by omega, fun a ha => ?_⟩
  have hmem : a ∈ I ^ n := (Ideal.pow_le_pow_right (by omega) : I ^ (n + 1) ≤ I ^ n) ha
  rw [hn] at hmem
  simp [show a = 0 by simpa using hmem]

/-- A finitely generated ideal whose zero locus is all of `Spec A` makes every module torsion. -/
private theorem isIPowerTorsion_of_zeroLocus_eq_univ {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I.FG) (h : PrimeSpectrum.zeroLocus (I : Set A) = Set.univ)
    (M : Type*) [AddCommGroup M] [Module A M] : IsIPowerTorsion A M I :=
  isIPowerTorsion_of_isNilpotent (hI.isNilpotent_iff_le_nilradical.mpr
    (PrimeSpectrum.zeroLocus_eq_univ_iff _ |>.mp h)) _

/-- An ideal with empty zero locus has cohomological dimension at most any `e ≥ 0`. -/
private theorem cohomologicalDimension_le_of_zeroLocus_empty
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (h : PrimeSpectrum.zeroLocus (I : Set A) = ∅) (e : ℤ) (he : 0 ≤ e) :
    cohomologicalDimension A I hI ≤ e :=
  cohomologicalDimension_le A I hI e ⟨by omega, fun i _ =>
    isZero_localCohomologyModule_of_zeroLocus_empty A I hI h _ i⟩

/-- **An ideal inside the nilradical has cohomological dimension at most zero.** A finitely
generated ideal whose zero locus is all of `Spec A` is nilpotent, so every `A`-module is
`I`-power torsion and local cohomology vanishes above degree zero. -/
theorem cohomologicalDimension_le_zero_of_zeroLocus_eq_univ
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (h : PrimeSpectrum.zeroLocus (I : Set A) = Set.univ) :
    cohomologicalDimension A I hI ≤ 0 := by
  refine cohomologicalDimension_le A I hI 0 ⟨by omega, fun i hi => ?_⟩
  exact isZero_localCohomologyModule_of_isIPowerTorsion A I hI _
    (isIPowerTorsion_of_zeroLocus_eq_univ hI h _) i (by omega)

/-- In a local ring of Krull dimension at most zero the maximal ideal is the only prime, so an
ideal with a nonempty zero locus is contained in every prime. -/
theorem zeroLocus_eq_univ_of_isLocalRing_of_ringKrullDim_nonpos
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hd : ringKrullDim A ≤ (0 : WithBot ℕ∞))
    (hne : (PrimeSpectrum.zeroLocus (I : Set A)).Nonempty) :
    PrimeSpectrum.zeroLocus (I : Set A) = Set.univ := by
  obtain ⟨p₀, hp₀⟩ := hne
  have hclosed : ∀ q : PrimeSpectrum A, q = IsLocalRing.closedPoint A := fun q =>
    le_antisymm
      (show q ≤ IsLocalRing.closedPoint A from IsLocalRing.le_maximalIdeal q.2.1)
      (Order.krullDim_nonpos_iff_forall_isMin.mp hd (IsLocalRing.closedPoint A)
        (IsLocalRing.le_maximalIdeal q.2.1))
  have hIm : (I : Set A) ⊆ (IsLocalRing.closedPoint A).asIdeal := by
    rw [← hclosed p₀]
    exact hp₀
  refine Set.eq_univ_of_forall fun q => ?_
  rw [PrimeSpectrum.mem_zeroLocus, hclosed q]
  exact hIm

/-- **The case `e = 0` of the statement to which Stacks 0DXC is reduced.** A finitely generated
ideal of a local ring of Krull dimension at most zero has cohomological dimension at most zero.

Either the zero locus is empty, and all local cohomology vanishes, or it is nonempty, and then it
is all of `Spec A` because the maximal ideal is the only prime; in that case the ideal is
nilpotent and local cohomology is the identity. No sheaf cohomology and no spectral space enter
either case. -/
theorem cohomologicalDimension_le_zero_of_isLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I.FG)
    (hd : ringKrullDim A ≤ (0 : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ 0 := by
  rcases Set.eq_empty_or_nonempty (PrimeSpectrum.zeroLocus (I : Set A)) with hempty | hne
  · exact cohomologicalDimension_le_of_zeroLocus_empty A I hI hempty 0 le_rfl
  · exact cohomologicalDimension_le_zero_of_zeroLocus_eq_univ A I hI
      (zeroLocus_eq_univ_of_isLocalRing_of_ringKrullDim_nonpos A I hd hne)

/-- **The arithmetic-rank hypothesis of
`Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators`
is false.** It asserts that in a local ring of Krull dimension at most `e` the zero locus of every
finitely generated ideal is cut out by at most `e` elements. Taking for `B` a field, for `e` the
value `0` and for the ideal the unit ideal refutes it: the only family of at most `0` elements is
the empty one, which spans `⊥` and cuts out all of `Spec B`, while `V(⊤) = ∅`.

The hypothesis therefore holds for no ring, and the theorem quantifying over it is vacuous. Its
satisfiable form restricts the ideal to one with a nonempty zero locus; that is the hypothesis of
`Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators'`
below, which is the source's own case distinction. -/
theorem not_forall_isLocalRing_exists_zeroLocus_generators_card_le :
    ¬ ∀ (B : Type u) [CommRing B] [IsLocalRing B] (J : Ideal B), J.FG → ∀ e : ℕ,
        ringKrullDim B ≤ (e : WithBot ℕ∞) → ∃ (n : ℕ) (g : Fin n → B), n ≤ e ∧
          PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal B) : Set B) =
            PrimeSpectrum.zeroLocus (J : Set B) := by
  intro h
  obtain ⟨n, g, hn, hg⟩ := h (ULift.{u} ℚ) ⊤ ⟨{1}, by simp⟩ 0
    (by simp [ringKrullDim_eq_zero_of_field])
  obtain rfl : n = 0 := Nat.le_zero.mp hn
  have hspan : (Ideal.span (Set.range g) : Ideal (ULift.{u} ℚ)) = ⊥ := by
    simp [Set.range_eq_empty (f := g)]
  rw [hspan] at hg
  have hbot : PrimeSpectrum.zeroLocus ((⊥ : Ideal (ULift.{u} ℚ)) : Set (ULift.{u} ℚ))
      = Set.univ := by
    simp
  have htop : PrimeSpectrum.zeroLocus ((⊤ : Ideal (ULift.{u} ℚ)) : Set (ULift.{u} ℚ)) = ∅ :=
    PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl
  rw [hbot, htop] at hg
  exact Set.not_nonempty_empty (hg ▸ Set.univ_nonempty (α := PrimeSpectrum (ULift.{u} ℚ)))

/-- **The second assertion of Stacks 0DXC, reduced to the local case in dimension at least one.**
A strengthening of
`Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_isLocalRing`: the hypothesis is
only needed for a bound `e ≥ 1` and for an ideal with a nonempty zero locus, the remaining cases
being `Stacks.LocalCohomology.cohomologicalDimension_le_zero_of_isLocalRing` and
`Stacks.LocalCohomology.isZero_localCohomologyModule_of_zeroLocus_empty`. -/
theorem cohomologicalDimension_le_ringKrullDim_of_isLocalRing_of_one_le
    (hlocal : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (J : Ideal B) (hJ : J.FG),
      (PrimeSpectrum.zeroLocus (J : Set B)).Nonempty → ∀ e : ℕ, 1 ≤ e →
        ringKrullDim B ≤ (e : WithBot ℕ∞) → cohomologicalDimension B J hJ ≤ (e : ℤ))
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (d : ℤ) := by
  refine cohomologicalDimension_le_ringKrullDim_of_isLocalRing
    (fun B _ _ J hJ e he => ?_) A I hI d hd
  rcases Set.eq_empty_or_nonempty (PrimeSpectrum.zeroLocus (J : Set B)) with hempty | hne
  · exact cohomologicalDimension_le_of_zeroLocus_empty B J hJ hempty e (by omega)
  · rcases Nat.eq_zero_or_pos e with rfl | he1
    · exact (cohomologicalDimension_le_zero_of_isLocalRing B J hJ
        (he.trans_eq (by simp))).trans_eq (by simp)
    · exact hlocal B J hJ hne e he1 he

/-- **The second assertion of Stacks 0DXC, reduced to a satisfiable arithmetic-rank bound.** The
hypothesis of
`Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators` is
false (`Stacks.LocalCohomology.not_forall_isLocalRing_exists_zeroLocus_generators_card_le`); this
is the same reduction with that hypothesis restricted to ideals with a nonempty zero locus and to
bounds `e ≥ 1`, which is the local form of Kronecker's bound on the arithmetic rank as it is
actually stated. -/
theorem cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators'
    (hara : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (J : Ideal B), J.FG →
      (PrimeSpectrum.zeroLocus (J : Set B)).Nonempty → ∀ e : ℕ, 1 ≤ e →
        ringKrullDim B ≤ (e : WithBot ℕ∞) → ∃ (n : ℕ) (g : Fin n → B), n ≤ e ∧
          PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal B) : Set B) =
            PrimeSpectrum.zeroLocus (J : Set B))
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (d : ℤ) :=
  cohomologicalDimension_le_ringKrullDim_of_isLocalRing_of_one_le
    (fun B _ _ J hJ hne e he1 he =>
      cohomologicalDimension_le_of_exists_zeroLocus_generators_card_le B J hJ e
        (hara B J hJ hne e he1 he))
    A I hI d hd

/-! ### Removing Stacks 0DX7 from the chain

The reductions above, like the ones of `DimensionBound.lean`, take their missing input in the
shape in which the source supplies it: vanishing of the *sheaf* cohomology of `U = Spec B ∖ V(J)`,
which the implication (3) ⇒ (1) of Stacks 0DX7 converts into vanishing of local cohomology. That
implication is not available in this library. It is also not needed: the comparison of Stacks
0DWR in degrees above one, `Stacks.LocalCohomology.homologyComplementIsoLocalCohomologyModule`,
is proved and unconditional, and it performs the same conversion directly.

What follows is therefore the same reduction with the missing input stated on the third term of
the affine localization triangle — the cone of the Čech augmentation — instead of on sheaf
cohomology. -/

/-- **The bound `cd(B, J) ≤ e` from vanishing of the cohomology of the localization triangle's
third term.** For `e ≥ 1`, if the degree-`p` cohomology of derived sections on
`U = Spec B ∖ V(J)` vanishes for every `p ≥ e`, then the cohomological dimension of `J` is at
most `e`.

This is the implication (3) ⇒ (1) of Stacks 0DX7 in the only form the bound needs, and unlike
that implication it is unconditional: the comparison
`Stacks.LocalCohomology.homologyComplementIsoLocalCohomologyModule` identifies the degree-`p`
cohomology of the third term with `H^{p+1}_{V(J)}(B)` for every `p ≥ 1`, and `e ≥ 1` puts every
degree `i > e` in that range. -/
theorem cohomologicalDimension_le_of_isZero_homology_complement
    (B : Type u) [CommRing B] (J : Ideal B) (hJ : J.FG) (e : ℕ) (he : 1 ≤ e)
    (h : ∀ (D : LocalizationTriangleData.{u, u} B J hJ) (p : ℕ), e ≤ p →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (p : ℤ)).obj
        (D.complement.obj (ModuleCat.of B B)))) :
    cohomologicalDimension B J hJ ≤ (e : ℤ) := by
  obtain ⟨D, hD⟩ := nonempty_localizationTriangleData_higherComparison.{u, u} B J hJ
  refine cohomologicalDimension_le B J hJ (e : ℤ) ⟨by omega, fun i hi => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  obtain ⟨c⟩ := hD (ModuleCat.of B B) p (by omega)
  exact (h D p (by omega)).of_iso c.symm

/-- **The hypothesis of
`Stacks.LocalCohomology.cohomologicalDimension_le_of_isZero_homology_complement` is attainable.**
When the zero locus is all of `Spec B` the third term of the localization triangle has no
cohomology in any positive degree, because local cohomology is then the identity functor; so the
hypothesis holds for `J = ⊥`, and more generally for any finitely generated ideal inside the
nilradical, at every `e ≥ 1`. -/
theorem isZero_homology_complement_of_zeroLocus_eq_univ
    (B : Type u) [CommRing B] (J : Ideal B) (hJ : J.FG)
    (hJuniv : PrimeSpectrum.zeroLocus (J : Set B) = Set.univ)
    (D : LocalizationTriangleData.{u, u} B J hJ) (M : ModuleCat.{u} B) (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (p : ℤ)).obj
      (D.complement.obj M)) := by
  refine IsZero.of_iso ?_ (homologyComplementIsoLocalCohomologyModule.{u, u} D M p hp)
  exact isZero_localCohomologyModule_of_isIPowerTorsion B J hJ M
    (isIPowerTorsion_of_zeroLocus_eq_univ hJ hJuniv M) ((p : ℤ) + 1) (by omega)

end Stacks.LocalCohomology

end
