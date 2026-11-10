module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.GroupSchemes.DoubleGlue

/-!
# A non-separated flat group scheme

Over the affine line over any field, there is a group scheme that is flat and of finite type but
not separated: take the affine line with its origin doubled, which is two copies of the affine
line glued along the complement of the origin, and let the group law multiply the labels of the
two copies modulo two.

The structure morphism restricts to the identity on each copy, so it is flat and of finite type,
and the total space is covered by two spectra, so it is quasi-compact. It is not separated
because the complement of the origin is not closed in the affine line: the generic point lies in
it and specialises to the origin.

## Main results

* `Stacks.Examples.exists_flat_finiteType_groupScheme_not_isSeparated`: such a group scheme over
  the affine line.

## Implementation notes

A group scheme over the affine line is a group object in the category of schemes over
`Spec k[X]`. Finite type is expressed by local finite type together with quasi-compactness of the
structure morphism.

## References

* [Stacks Project, Tag 06E8](https://stacks.math.columbia.edu/tag/06E8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Examples

/-- The complement of the origin in the affine line over `k`. -/
public noncomputable def puncturedAffineLine (k : Type u) [Field k] :
    (Spec (.of (Polynomial k))).Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)

/-- The complement of the origin in the affine line is not closed: it contains the generic point,
which specialises to the origin. -/
public theorem not_isClosed_puncturedAffineLine (k : Type u) [Field k] :
    ¬ IsClosed (puncturedAffineLine k : Set (Spec (.of (Polynomial k)))) := by
  let R := Polynomial k
  let ev : R →+* k := Polynomial.evalRingHom 0
  let origin : PrimeSpectrum (↑(CommRingCat.of R)) :=
    ⟨RingHom.ker ev, RingHom.ker_isPrime ev⟩
  let generic : PrimeSpectrum (↑(CommRingCat.of R)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hbot : generic ∈ puncturedAffineLine k := by
    change generic ∈ PrimeSpectrum.basicOpen (Polynomial.X : R)
    rw [PrimeSpectrum.mem_basicOpen]
    change Polynomial.X ∉ (⊥ : Ideal (↑(CommRingCat.of R)))
    exact Polynomial.X_ne_zero
  have horigin : origin ∉ puncturedAffineLine k := by
    change origin ∉ PrimeSpectrum.basicOpen (Polynomial.X : R)
    rw [PrimeSpectrum.mem_basicOpen]
    refine not_not_intro (show (Polynomial.X : R) ∈ RingHom.ker ev from ?_)
    change Polynomial.eval 0 (Polynomial.X : R) = 0
    rw [Polynomial.eval_X]
  exact fun hclosed => horigin (hclosed.stableUnderSpecialization
    ((PrimeSpectrum.le_iff_specializes generic origin).mp bot_le) hbot)

/-- The affine line over `k` with its origin doubled, as a scheme over the affine line with its
two copies as the two sections of its structure morphism. -/
@[ega "I 5.5.11"]
public noncomputable abbrev doubledAffineLine (k : Type u) [Field k] :
    SectionCoverData (Spec (.of (Polynomial k))) :=
  doubleSectionCover _ (puncturedAffineLine k)

/-- **Stacks Project, Tag 06E8.** There is a flat group scheme of finite type over the affine
line that is not separated. -/
@[stacks 06E8, sga "3 VIB 5.6.4" "base = affine line"]
public theorem exists_flat_finiteType_groupScheme_not_isSeparated (k : Type u) [Field k] :
    ∃ G : CategoryTheory.Over (Spec (.of (Polynomial k))),
      Nonempty (GrpObj G) ∧ Flat G.hom ∧ LocallyOfFiniteType G.hom ∧
        QuasiCompact G.hom ∧ ¬ IsSeparated G.hom := by
  have : CompactSpace (Spec (.of (Polynomial k))) := PrimeSpectrum.compactSpace
  refine ⟨(doubledAffineLine k).over, ⟨(doubledAffineLine k).grpObj⟩, ?_, ?_, ?_, ?_⟩
  · exact (doubledAffineLine k).proj_prop _
      (HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)) inferInstance
  · exact (doubledAffineLine k).proj_prop _
      (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)) inferInstance
  · exact (doubledAffineLine k).quasiCompact_proj
  · exact doubleSectionCover_not_isSeparated _ _ (not_isClosed_puncturedAffineLine k)

end Stacks.Examples

end
