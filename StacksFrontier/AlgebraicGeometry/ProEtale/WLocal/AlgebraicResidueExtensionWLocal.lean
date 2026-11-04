module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Spectral.Hom
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.AlgebraicResidueExtension
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteClosedSubset
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Profinite.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# A w-local extension after an algebraic residue-field extension

Let `A` be a ring whose closed points in `Spec A` are cut out by an ideal `I`, and let
`f : A →+* B` induce algebraic extensions of residue fields. The closed subset `V(I·B)` is then
a profinite space, so `B` carries the w-local ind-Zariski extension of Stacks 0979 along
`V(I·B)`. That extension `B → C` does not change the quotient by `I·B`, has w-local spectrum,
and the structure map `Spec C → Spec A` is a w-local map whose fibre over the closed points of
`Spec A` is exactly the set of closed points of `Spec C`.

## Main results

* `AlgebraicGeometry.ProEtale.isProfiniteStacks_zeroLocus_of_subset_closedPoints`: a closed
  subset `V(I) ⊆ Spec R` all of whose points are closed is a profinite space.
* `AlgebraicGeometry.ProEtale.isProfiniteStacks_zeroLocus_map_of_isAlgebraic_residueField`:
  `V(I·B)` is profinite under the hypotheses above.
* `AlgebraicGeometry.ProEtale.closedPoints_wLocalExtension_map_eq_preimage` and
  `AlgebraicGeometry.ProEtale.isWLocalMap_comap_wLocalExtension_map`: the closed points of
  `Spec C` are the inverse image of the closed points of `Spec A`, and `Spec C → Spec A` is a
  w-local map.
* `AlgebraicGeometry.ProEtale.exists_isIndZariski_wLocal_of_isAlgebraic_residueField`:
  **Stacks 097A, part (2)**, the existence statement of the source.

## Implementation notes

The hypothesis on `I` is an equality of the zero locus of `I` with the set of closed points of
`Spec A`; radicality of `I` is not needed, since only its zero locus enters, and w-locality of
`Spec A` is not needed either — the proof uses only that the closed points of `Spec A` are cut
out by `I`, which is how part (1) of the tag is already stated.

Profiniteness of `V(I·B)` is read off from the equivalence
`isProfiniteStacks_primeSpectrum_quotient_iff`: a prime of `B ⧸ I·B` contracts to a prime of
`B` containing `I·B`, which part (1) of the tag shows to be closed, hence maximal, so every
prime of `B ⧸ I·B` is maximal and `spec_profinite_tfae` applies.

The extension is the explicit `wLocalExtension (I·B)` of Stacks 0979 rather than an unnamed
ring, so each clause of part (2) is available for that one ring; the existential of the source
is then assembled from those named statements. The quotient clause is recorded as bijectivity of
the canonical map `B ⧸ I·B → C ⧸ I·C`, which identifies the isomorphism of the source.

`IsSpectralMap (PrimeSpectrum.comap f)` is not in Mathlib, which has it only for morphisms of
schemes (`AlgebraicGeometry.Scheme.Hom.isSpectralMap`), and the proof available in this library
is private to another file, so it is repeated here as a private lemma.

## References

* [Stacks Project, Tag 097A](https://stacks.math.columbia.edu/tag/097A)
* [Stacks Project, Tag 0978](https://stacks.math.columbia.edu/tag/0978)
* [Stacks Project, Tag 0979](https://stacks.math.columbia.edu/tag/0979)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open TopologicalSpace

universe u v

/-- If every prime of `R` containing `I` is a closed point of `Spec R`, then every prime of
`R ⧸ I` is maximal. -/
private theorem isMaximal_of_zeroLocus_subset_closedPoints {R : Type*} [CommRing R]
    (I : Ideal R)
    (hclosed : PrimeSpectrum.zeroLocus (I : Set R) ⊆ closedPoints (PrimeSpectrum R))
    (q : Ideal (R ⧸ I)) (hq : q.IsPrime) : q.IsMaximal := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨q, hq⟩
  have hpI : I ≤ p.asIdeal := I.mk_ker.symm.trans_le (Ideal.ker_le_comap _)
  have hpmax : p.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp (mem_closedPoints_iff.mp (hclosed hpI))
  have hqeq : q = p.asIdeal.map (Ideal.Quotient.mk I) :=
    (Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective q).symm
  rw [hqeq]
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (by simpa [Ideal.mk_ker] using hpI)

/-- A closed subset `V(I) ⊆ Spec R` all of whose points are closed in `Spec R` is a profinite
space: it is homeomorphic to `Spec (R ⧸ I)`, every prime of `R ⧸ I` is then maximal, and a
spectrum with no nontrivial inclusions of primes is profinite. -/
theorem isProfiniteStacks_zeroLocus_of_subset_closedPoints {R : Type u} [CommRing R]
    (I : Ideal R)
    (hclosed : PrimeSpectrum.zeroLocus (I : Set R) ⊆ closedPoints (PrimeSpectrum R)) :
    IsProfiniteStacks (PrimeSpectrum.zeroLocus (I : Set R)) :=
  (isProfiniteStacks_primeSpectrum_quotient_iff I).mp
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mpr
      (((spec_profinite_tfae (R ⧸ I)).out 6 1).mp
        (isMaximal_of_zeroLocus_subset_closedPoints I hclosed)))

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Let `I` be an ideal of `A` whose zero locus is the set of closed points of `Spec A`, and let
`f : A →+* B` induce algebraic extensions of residue fields. Then the closed subset `V(I·B)` of
`Spec B` is a profinite space. -/
theorem isProfiniteStacks_zeroLocus_map_of_isAlgebraic_residueField (f : A →+* B) (I : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (halg : ∀ q : Ideal B, ∀ [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap f).ResidueField q.ResidueField) :
    IsProfiniteStacks (PrimeSpectrum.zeroLocus (Ideal.map f I : Set B)) :=
  isProfiniteStacks_zeroLocus_of_subset_closedPoints _
    (closedPoints_of_mem_zeroLocus_map f I hzero halg)

/-- **Stacks 097A, part (2)(d).** The closed points of the w-local extension `C` of `B` along
`V(I·B)` are exactly the points lying over the closed points of `Spec A`. -/
theorem closedPoints_wLocalExtension_map_eq_preimage (f : A →+* B) (I : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (halg : ∀ q : Ideal B, ∀ [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap f).ResidueField q.ResidueField) :
    closedPoints (PrimeSpectrum (wLocalExtension (Ideal.map f I))) =
      PrimeSpectrum.comap
          ((algebraMap B (wLocalExtension (Ideal.map f I))).comp f) ⁻¹'
        closedPoints (PrimeSpectrum A) := by
  ext x
  rw [closedPoints_wLocalExtension B (Ideal.map f I)
    (isProfiniteStacks_zeroLocus_map_of_isAlgebraic_residueField f I hzero halg), ← hzero]
  show (Ideal.map f I).map (algebraMap B (wLocalExtension (Ideal.map f I))) ≤ x.asIdeal ↔
    I ≤ Ideal.comap f
      (Ideal.comap (algebraMap B (wLocalExtension (Ideal.map f I))) x.asIdeal)
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]

/-- **Stacks 097A, part (2)(c).** The map `Spec C → Spec A` from the w-local extension `C` of `B`
along `V(I·B)` is a w-local map. -/
theorem isWLocalMap_comap_wLocalExtension_map (f : A →+* B) (I : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (halg : ∀ q : Ideal B, ∀ [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap f).ResidueField q.ResidueField) :
    IsWLocalMap (PrimeSpectrum.comap
      ((algebraMap B (wLocalExtension (Ideal.map f I))).comp f)) :=
  ⟨PrimeSpectrum.isSpectralMap_comap _,
    (closedPoints_wLocalExtension_map_eq_preimage f I hzero halg).subset⟩

/-- **Stacks 097A, part (2).** Let `I` be an ideal of `A` whose zero locus is the set `X₀` of
closed points of `X = Spec A`, and let `f : A →+* B` induce algebraic extensions of residue
fields. Then there is an ind-Zariski ring map `B → C` such that `B ⧸ I·B → C ⧸ I·C` is an
isomorphism, the space `Y = Spec C` is w-local, the induced map `p : Y → X` is w-local, and
`p⁻¹(X₀)` is the set of closed points of `Y`. -/
@[stacks 097A "part (2)"]
theorem exists_isIndZariski_wLocal_of_isAlgebraic_residueField (f : A →+* B) (I : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (halg : ∀ q : Ideal B, ∀ [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap f).ResidueField q.ResidueField) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra B C),
      Algebra.IsIndZariski B C ∧
        Function.Bijective (algebraMap (B ⧸ Ideal.map f I)
          (C ⧸ (Ideal.map f I).map (algebraMap B C))) ∧
        WLocalSpace (PrimeSpectrum C) ∧
        IsWLocalMap (PrimeSpectrum.comap ((algebraMap B C).comp f)) ∧
        closedPoints (PrimeSpectrum C) =
          PrimeSpectrum.comap ((algebraMap B C).comp f) ⁻¹' closedPoints (PrimeSpectrum A) :=
  have hprof := isProfiniteStacks_zeroLocus_map_of_isAlgebraic_residueField f I hzero halg
  ⟨wLocalExtension (Ideal.map f I), inferInstance, inferInstance,
    isIndZariski_wLocalExtension B (Ideal.map f I),
    bijective_algebraMap_quotient_wLocalExtension B (Ideal.map f I) hprof,
    wLocalSpace_wLocalExtension B (Ideal.map f I) hprof,
    isWLocalMap_comap_wLocalExtension_map f I hzero halg,
    closedPoints_wLocalExtension_map_eq_preimage f I hzero halg⟩

end AlgebraicGeometry.ProEtale

end
