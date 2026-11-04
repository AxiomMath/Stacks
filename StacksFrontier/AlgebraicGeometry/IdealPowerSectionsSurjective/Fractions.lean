module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSectionsComparison.Separated

/-!
# A section of `M̃` on a basic open is a single fraction

Let `R` be a commutative ring, `N` an `R`-module and `f : R`. The sections of `Ñ` on the basic
open `D(f)` are the localization `N_f`, so every such section is a *single* fraction `m / f ^ k`
rather than merely a locally constant choice of fractions. This file records that, in the
pointwise form in which the surjectivity half of [Stacks, Tag 01PM] uses it: a dependent
function on an open `W` which is locally a fraction has, on each basic open `D(f) ≤ W`, one
global numerator and one exponent that compute its value at *every* point of `D(f)`.

## Main results

* `mk'_toOpenₗ_eq_const`: the localization-map description `IsLocalizedModule.mk'` of a fraction
  on `D(f)` is the explicit section `StructureSheaf.const`.
* `exists_const_eq_of_basicOpen`: every section on `D(f)` is `const m (f ^ k) _`.
* `exists_mk_eq_of_mem_sectionsSubmodule`: the pointwise form, for a locally fractional function
  on an open containing `D(f)`.

## Implementation notes

The input is given as a bare dependent function together with its membership of
`AlgebraicGeometry.StructureSheaf.sectionsSubmodule`, not as an element of a presheaf of modules:
the sections of the tilde sheaf are *definitionally* that subtype (Mathlib's
`AlgebraicGeometry.tilde.modulesSpecToSheafIso` is the identity on carriers), and taking the data
and the predicate separately avoids having to transport anything across the
`modulesSpecToSheaf`/`restrictScalars` spellings. Restricting the predicate to the basic open is
`LocalPredicate.res` of `AlgebraicGeometry.StructureSheaf.isLocallyFraction`.

`IsLocalizedModule.mk'` is used rather than `StructureSheaf.toBasicOpenₗ` because the surjectivity
it supplies, `IsLocalizedModule.mk'_surjective`, is available for the instance
`IsLocalizedModule.Away f (StructureSheaf.toOpenₗ R N (basicOpen f))` directly.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.StructureSheaf
open PrimeSpectrum (basicOpen)

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerSections

variable {R : Type u} [CommRing R] {N : Type u} [AddCommGroup N] [Module R N]

/-- The fraction `m / f ^ k` of the localization map `toOpenₗ` on `D(f)` is the explicit
section `const m (f ^ k)`. -/
public lemma mk'_toOpenₗ_eq_const (f : R) (m : N) (k : ℕ) :
    IsLocalizedModule.mk' (toOpenₗ R N (basicOpen f)) m
        (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) =
      const m (f ^ k) (basicOpen f) (PrimeSpectrum.le_basicOpen_pow f k) := by
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def]
  change toOpenₗ R N (basicOpen f) m = (f ^ k) • const m (f ^ k) (basicOpen f) _
  rw [smul_const, toOpenₗ_eq_const]
  exact const_ext (one_smul R ((f ^ k) • m)).symm

/-- Every section of `Ñ` on a basic open `D(f)` is a single fraction `m / f ^ k`: the sections
there are the localization `N_f`. -/
public lemma exists_const_eq_of_basicOpen (f : R)
    (s : (structureSheafInType R N).1.obj (op (basicOpen f))) :
    ∃ (k : ℕ) (m : N),
      s = const m (f ^ k) (basicOpen f) (PrimeSpectrum.le_basicOpen_pow f k) := by
  obtain ⟨⟨m, _, k, rfl⟩, rfl⟩ :=
    IsLocalizedModule.mk'_surjective (Submonoid.powers f) (toOpenₗ R N (basicOpen f)) s
  exact ⟨k, m, mk'_toOpenₗ_eq_const f m k⟩

/-- A dependent function on `W` which is locally a fraction has, on each basic open `D(f) ≤ W`,
a single numerator and exponent computing its value at every point of `D(f)`. -/
public lemma exists_mk_eq_of_mem_sectionsSubmodule {W : Opens (PrimeSpectrum.Top R)}
    (g : ∀ x : ↥W, Localizations N x.1) (hg : g ∈ sectionsSubmodule N W)
    (f : R) (hf : basicOpen f ≤ W) :
    ∃ (k : ℕ) (m : N), ∀ (p : PrimeSpectrum R) (hp : f ∉ p.asIdeal) (hpW : p ∈ W),
      g ⟨p, hpW⟩ = LocalizedModule.mk m ⟨f ^ k, Submonoid.pow_mem _ hp k⟩ := by
  obtain ⟨k, m, hkm⟩ := exists_const_eq_of_basicOpen f
    (⟨_, (isLocallyFraction R N).res (homOfLE hf) g hg⟩ :
      (structureSheafInType R N).1.obj (op (basicOpen f)))
  exact ⟨k, m, fun p hp _ => congrFun (congrArg Subtype.val hkm) ⟨p, hp⟩⟩

end Stacks.AlgebraicGeometry.IdealPowerSections

end
