module

public import StacksFrontier.RingTheory.LocalCohomology.LowDegree

/-!
# Constant fractions as locally fractional sections

This file sets up the elementary operations on the locally fractional sections
`Stacks.LocalCohomology.moduleSections` of `LowDegree.lean`, which are Mathlib's
`AlgebraicGeometry.StructureSheaf.sectionsSubmodule` with the ring and the module universes
separated.

Two things are proved. The first is a purely algebraic localization principle: if an element `z`
of an `A`-module is annihilated, at every prime of the standard open `D(g)`, by some element
outside that prime, then `gⁿ • z = 0` for some `n`. Geometrically this says that the vanishing
locus of the annihilator of `z` is disjoint from `D(g)`, so `g` lies in the radical of the
annihilator. It is the engine behind both the injectivity and the normalization steps of the
identification of `Γ(D(f), M̃)` with `M_f`.

The second is the local description of a section: a locally fractional section on an open `U` is,
on a basic open neighbourhood of each point of `U`, the constant fraction `m / g` for a single
numerator `m` and denominator `g`. This is Mathlib's
`AlgebraicGeometry.StructureSheaf.exists_const` with the universes separated, phrased pointwise
so that no restriction map has to be named.

## Main definitions

* `Stacks.LocalCohomology.moduleSectionsMk` — the map `m ↦ m / 1` from a module to its locally
  fractional sections on an open of `Spec A`.

## Main results

* `Stacks.LocalCohomology.exists_pow_smul_eq_zero_of_forall_mem_basicOpen` — an element killed
  locally on `D(g)` is killed by a power of `g`.
* `Stacks.LocalCohomology.exists_basicOpen_forall_eq_mk` — a section is a constant fraction on a
  basic open neighbourhood of each point.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open PrimeSpectrum (basicOpen)

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- **A local annihilation principle.** If an element `z` of an `A`-module is annihilated at every
prime of the standard open `D(g)` by some element outside that prime, then a power of `g`
annihilates `z` outright: the hypothesis says that the vanishing locus of the annihilator ideal of
`z` misses `D(g)`, so `g` belongs to the radical of that annihilator. -/
theorem exists_pow_smul_eq_zero_of_forall_mem_basicOpen {M : Type v} [AddCommGroup M] [Module A M]
    (g : A) (z : M)
    (h : ∀ p : PrimeSpectrum A, g ∉ p.asIdeal → ∃ u ∈ p.asIdeal.primeCompl, u • z = 0) :
    ∃ n : ℕ, g ^ n • z = 0 := by
  have hg : g ∈ ((⊥ : Submodule A M).colon {z}).radical := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hgp
    obtain ⟨u, hu, huz⟩ := h p hgp
    rw [PrimeSpectrum.mem_zeroLocus] at hp
    exact hu (hp (Submodule.mem_colon_singleton.mpr (by simpa using huz)))
  obtain ⟨n, hn⟩ := hg
  exact ⟨n, by simpa using Submodule.mem_colon_singleton.mp hn⟩

variable (M : ModuleCat.{v} A)

/-- The constant fraction `m / 1`, as a locally fractional section of `M` on an open of `Spec A`.
This is Mathlib's `AlgebraicGeometry.StructureSheaf.toOpenₗ` with the ring and the module
universes separated. -/
def moduleSectionsMk (U : Opens (PrimeSpectrum.Top A)) : M →ₗ[A] moduleSections M U where
  toFun m :=
    ⟨fun x ↦ LocalizedModule.mk m 1,
      fun x ↦ ⟨U, x.2, 𝟙 _, m, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩
  map_add' m₁ m₂ := Subtype.ext <| funext fun x ↦ by
    change LocalizedModule.mk (m₁ + m₂) (1 : x.1.asIdeal.primeCompl) =
      LocalizedModule.mk m₁ 1 + LocalizedModule.mk m₂ 1
    rw [LocalizedModule.mk_add_mk]
    exact LocalizedModule.mk_eq.mpr ⟨1, by simp⟩
  map_smul' r m := Subtype.ext <| funext fun x ↦ (LocalizedModule.smul'_mk ..).symm

/-- The value of the section `moduleSectionsMk M U m` at a point `x` of `U` is the fraction
`m / 1` in the localization of `M` at `x`. -/
@[simp]
theorem moduleSectionsMk_apply {U : Opens (PrimeSpectrum.Top A)} (m : M) (x : U) :
    (moduleSectionsMk M U m).1 x = LocalizedModule.mk m 1 :=
  rfl

/-- **The local form of a section.** A locally fractional section on `U` is the constant fraction
`m / g` on a basic open neighbourhood `D(g) ⊆ U` of any given point of `U`. This is Mathlib's
`AlgebraicGeometry.StructureSheaf.exists_const` with the ring and the module universes
separated. -/
theorem exists_basicOpen_forall_eq_mk (U : Opens (PrimeSpectrum.Top A))
    (s : moduleSections M U) (x : PrimeSpectrum A) (hx : x ∈ U) :
    ∃ (g : A) (_ : x ∈ basicOpen g) (hgU : basicOpen g ≤ U) (m : M),
      ∀ y : basicOpen g, s.1 ⟨y.1, hgU y.2⟩ = LocalizedModule.mk m ⟨g, y.2⟩ := by
  obtain ⟨V, hxV, iVU, m, a, hma⟩ := s.2 ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hxb, hbV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
  refine ⟨b * a, ?_, ?_, b • m, fun y ↦ ?_⟩
  · exact (PrimeSpectrum.basicOpen_mul b a).ge ⟨hxb, (hma ⟨x, hxV⟩).1⟩
  · exact ((PrimeSpectrum.basicOpen_mul b a).trans_le inf_le_left).trans
      (le_trans hbV iVU.le)
  · obtain ⟨hay, hy⟩ := hma ⟨y.1, hbV ((PrimeSpectrum.basicOpen_mul b a).le y.2).1⟩
    refine Eq.trans hy (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩)
    simp only [Submonoid.smul_def, one_smul, ← smul_assoc, smul_eq_mul]
    ring_nf

end Stacks.LocalCohomology

end
