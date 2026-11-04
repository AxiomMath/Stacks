module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness need only be checked at the closed points

The last paragraph of the proof of [Stacks, Tag 0B5P] is a purely topological reduction, and it
is the step that distinguishes that tag from [Stacks, Tag 01PS]: the cohomological hypothesis
produces an affine nonvanishing locus around every *closed* point, and one then has to upgrade
that to every point.

The upgrade is the observation that the set of points covered by *some* affine nonvanishing
locus is open, so its complement is closed, hence quasi-compact in a quasi-compact space
([Stacks, Tag 005C], Mathlib's `IsClosed.isCompact`); a nonempty closed subset of a quasi-compact
Kolmogorov space contains a point closed in the ambient space ([Stacks, Tag 005E], Mathlib's
`IsClosed.exists_closed_singleton`), and the underlying space of a scheme is `T₀`. So a nonempty
complement would contain a closed point of `X`, which the hypothesis already covers.

Nothing here is specific to tensor powers of an invertible module: the statement is about an
arbitrary family `pow : ℤ → X.Modules`, exactly as `Stacks.Ample.IsAmpleForPowers` is.

## Main definitions

* `Stacks.AmpleCohomologicalCriterion.ampleLocus`: the set of points lying in an affine
  nonvanishing locus of a global section of `pow n` for some `n ≥ 1`. Ampleness of `pow` is
  quasi-compactness together with `ampleLocus = Set.univ`.

## Main results

* `Stacks.AmpleCohomologicalCriterion.isOpen_ampleLocus`: the ample locus is open.
* `Stacks.AmpleCohomologicalCriterion.ampleLocus_eq_univ_of_closed_points`: if every closed
  point of a quasi-compact scheme lies in the ample locus, the ample locus is everything.
* `Stacks.AmpleCohomologicalCriterion.isAmpleForPowers_of_closed_points`: ampleness of a family,
  checked only at the closed points.
* `Stacks.AmpleCohomologicalCriterion.isAmple_of_closed_points`: the same for
  `Stacks.Ample.IsAmple`, i.e. for the actual tensor powers of an invertible module.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 005C](https://stacks.math.columbia.edu/tag/005C)
* [Stacks Project, Tag 005E](https://stacks.math.columbia.edu/tag/005E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AmpleCohomologicalCriterion

variable {X : Scheme.{u}}

/-- The *ample locus* of a family `pow : ℤ → X.Modules`: the points of `X` which lie in an
affine nonvanishing locus of a global section of `pow n` for some `n ≥ 1`. By definition
`Stacks.Ample.IsAmpleForPowers X pow` is quasi-compactness of `X` together with the assertion
that this set is all of `X`. -/
def ampleLocus (pow : ℤ → X.Modules) : Set X :=
  {y | ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(pow (n : ℤ), ⊤), ∃ U : X.Opens,
    (U : Set X) = Stacks.Ample.nonvanishingLocus (pow (n : ℤ)) s ∧ y ∈ U ∧ IsAffineOpen U}

/-- A point `y` lies in `ampleLocus pow` if and only if there are `n ≥ 1`, a global section `s`
of `pow n` and an affine open `U` equal to the nonvanishing locus of `s` with `y ∈ U`. -/
theorem mem_ampleLocus_iff (pow : ℤ → X.Modules) (y : X) :
    y ∈ ampleLocus pow ↔ ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(pow (n : ℤ), ⊤), ∃ U : X.Opens,
      (U : Set X) = Stacks.Ample.nonvanishingLocus (pow (n : ℤ)) s ∧ y ∈ U ∧ IsAffineOpen U :=
  Iff.rfl

/-- **Ampleness is the ample locus being everything.** This is `Stacks.Ample.IsAmpleForPowers`
rewritten, with no hypothesis. -/
theorem isAmpleForPowers_iff_ampleLocus_eq_univ (X : Scheme.{u}) (pow : ℤ → X.Modules) :
    Stacks.Ample.IsAmpleForPowers X pow ↔ CompactSpace X ∧ ampleLocus pow = Set.univ := by
  rw [Stacks.Ample.isAmpleForPowers_iff]
  exact and_congr_right fun _ =>
    ⟨fun h => Set.eq_univ_of_forall fun y => h y,
      fun h y => (mem_ampleLocus_iff pow y).mp (h.ge (Set.mem_univ y))⟩

/-- **The ample locus is open.** A witness `U` for a point of the locus is an open neighbourhood
of that point contained in the locus, since every point of `U` is witnessed by the same data. -/
theorem isOpen_ampleLocus (pow : ℤ → X.Modules) : IsOpen (ampleLocus pow) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨n, hn, s, U, hU, hyU, haff⟩
  exact ⟨(U : Set X), fun z hz => ⟨n, hn, s, U, hU, hz, haff⟩, U.2, hyU⟩

/-- **The reduction to closed points.** On a quasi-compact scheme, a set which is open and
contains every closed point is the whole space: its complement is closed, so a nonempty
complement would contain a point closed in `X` by [Stacks, Tag 005E], and that point is in the
set. -/
@[ega "0 2.1.3" "special case"]
theorem eq_univ_of_isOpen_of_closed_points [CompactSpace X] {W : Set X} (hW : IsOpen W)
    (h : ∀ x : X, IsClosed ({x} : Set X) → x ∈ W) : W = Set.univ := by
  rw [← Set.compl_empty_iff, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  obtain ⟨x, hxW, hx⟩ := hW.isClosed_compl.exists_closed_singleton hne
  exact hxW (h x hx)

/-- **The ample locus of a quasi-compact scheme is everything as soon as it contains every closed
point.** -/
theorem ampleLocus_eq_univ_of_closed_points [CompactSpace X] (pow : ℤ → X.Modules)
    (h : ∀ x : X, IsClosed ({x} : Set X) → x ∈ ampleLocus pow) : ampleLocus pow = Set.univ :=
  eq_univ_of_isOpen_of_closed_points (isOpen_ampleLocus pow) h

/-- **Ampleness of a family of modules, checked only at the closed points.** This is the final
paragraph of the proof of [Stacks, Tag 0B5P], separated from the cohomological construction that
supplies the hypothesis. -/
theorem isAmpleForPowers_of_closed_points (X : Scheme.{u}) [CompactSpace X]
    (pow : ℤ → X.Modules)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(pow (n : ℤ), ⊤),
      ∃ U : X.Opens, (U : Set X) = Stacks.Ample.nonvanishingLocus (pow (n : ℤ)) s ∧ x ∈ U ∧
        IsAffineOpen U) :
    Stacks.Ample.IsAmpleForPowers X pow :=
  (isAmpleForPowers_iff_ampleLocus_eq_univ X pow).mpr
    ⟨‹_›, ampleLocus_eq_univ_of_closed_points pow h⟩

/-- **Ampleness of an invertible module, checked only at the closed points.** The tensor powers
are those of [Stacks, Tag 01CU], through `Stacks.Ample.tensorPowModule`. -/
theorem isAmple_of_closed_points (X : Scheme.{u}) [CompactSpace X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : Γ(Stacks.Ample.tensorPowModule X L (n : ℤ), ⊤), ∃ U : X.Opens,
        (U : Set X) = Stacks.Ample.nonvanishingLocus
          (Stacks.Ample.tensorPowModule X L (n : ℤ)) s ∧ x ∈ U ∧ IsAffineOpen U) :
    Stacks.Ample.IsAmple X L :=
  isAmpleForPowers_of_closed_points X _ h

end Stacks.AmpleCohomologicalCriterion

end
