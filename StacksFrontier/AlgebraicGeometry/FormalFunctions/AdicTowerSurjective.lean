module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
import StacksFrontier.AlgebraicGeometry.FormalFunctions.AmpleFibreTwistLocalBase
import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8

/-!
# The `𝓘`-adic inverse-limit induction: sections of `ℱ` surject onto sections of `ℱ / 𝓘 ℱ`

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` proper, `ℱ` a coherent `𝒪_X`-module, `I` an ideal
of `A` and `𝓘 = I · 𝒪_X`. This file proves

**`H⁰(X, ℱ) ⟶ H⁰(X, ℱ / 𝓘 ⁿ ℱ)` is surjective for every `n`, as soon as `H¹` vanishes on the
kernel of every exponent-drop map `ℱ / 𝓘 ⁿ ℱ ⟶ ℱ / 𝓘 ᵐ ℱ`.**

That implication is the inverse-limit induction in the essential-surjectivity half of
[Stacks, Tag 0EXD]. The source runs it as: the exact sequences
`0 → 𝓘 ⁿ 𝒢 / 𝓘 ⁿ⁺¹ 𝒢 → 𝒢 / 𝓘 ⁿ⁺¹ 𝒢 → 𝒢 / 𝓘 ⁿ 𝒢 → 0` have `H¹` of their left term zero, because
that term lives on the exceptional line `E = 𝐏¹_Z` and is globally generated there; so by
induction `lim H⁰(X', 𝒢 / 𝓘 ⁿ 𝒢) ⟶ H⁰(E, 𝒢|_E)` is surjective; and *"the theorem on formal
functions upgrades this to surjectivity of `H⁰(X', 𝒢) ⟶ H⁰(E, 𝒢|_E)`"*.

## The two steps

The first step is `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyTowerMap_of_isZero`:
the long exact sequence of `0 → ker φ → ℱ / 𝓘 ⁿ ℱ → ℱ / 𝓘 ᵐ ℱ → 0`, where `φ` is the exponent
drop, makes `H⁰(φ)` surjective once `H¹(X, ker φ)` vanishes.

The second step is
`Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_of_surjective_towerMap`, and it
does **not** go through the inverse limit. [Stacks, Tag 02OB] clause (3), which the theorem
on formal functions is assembled from in this development, already says that the image of a
tower map `H^p(X, ℱ / 𝓘 ᵏ ℱ) ⟶ H^p(X, ℱ / 𝓘 ⁿ ℱ)` equals the image of
`H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ⁿ ℱ)` as soon as `k ≥ n + c`, for one uniform `c`. So a tower of
surjections forces the projection out of `H^p(X, ℱ)` itself to be surjective, with no
Mittag-Leffler argument and no adic-completion bookkeeping: the eventual image *is* the image of
the global sections. That clause is available here unconditionally, because its hypothesis
[Stacks, Tag 02O8] is a theorem of this development
(`Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`), the same discharge that makes
`Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_unconditional` — [Stacks, Tag
02OC] — hold with no hypothesis beyond the source's.

## Main results

* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyTowerMap_of_isZero`: **`H⁰` of the
  exponent drop is surjective when `H¹` of its kernel vanishes.**
* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_of_surjective_towerMap`:
  **a tower of surjections makes `H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ⁿ ℱ)` surjective**, in every degree.
* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_of_isZero_kernel`:
  **the inverse-limit induction of [Stacks, Tag 0EXD]** — the two steps composed.

## What this does not do

**The vanishing hypothesis is stated at `kernel (idealPowerQuotientDrop …)`**, not at
`𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ`. Identifying the two is the remaining geometric input of the step, together with
the global generation of the graded pieces on the exceptional line which makes their `H¹` vanish
by `Stacks.AlmostBlowUp.isZero_cohomology_one_exceptional_of_generatingSections`; neither is
proved here. So no `@[stacks 0EXD]` attribute appears in this file: the tag asserts that
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` is an equivalence, and this is one
implication inside the essential-surjectivity half of its proof.

**The vanishing is in Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`**, which is what
`Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅` produces its long exact
sequence in, and which needs no `HasDerivedCategory` instance. The projective-line vanishing
results of this development are stated in the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus`; `Stacks.DerivedIndexing.rightDerivedIso` crosses
between the two indexings, and that crossing is where a consumer supplies them.

**No `@[stacks 02OB]` attribute either**, although the unconditional form of that tag is what the
second step uses: the tag is already registered, on
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`
with a note recording the hypothesis it carries, and discharging that hypothesis here is a
by-product rather than the subject of this file.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (F : X.Modules)

/-! ### The exponent drop and its kernel -/

/-- **`H⁰` of the exponent drop is surjective as soon as `H¹` of its kernel vanishes.** The
exponent drop is an epimorphism, so it sits in a short exact sequence with its kernel, and one
degree of right exactness of `H⁰` follows from one degree of vanishing on the kernel.

This is the induction step of the inverse-limit argument of [Stacks, Tag 0EXD]: there the kernel
is `𝓘 ⁿ 𝒢 / 𝓘 ⁿ⁺¹ 𝒢`, a globally generated module on the exceptional line, whose `H¹` vanishes
by [Stacks, Tag 0E7H] — here, on the projective line, by
`Stacks.AlmostBlowUp.isZero_cohomology_one_exceptional_of_generatingSections`, with no hypothesis
at all. -/
public theorem surjective_adicCohomologyTowerMap_of_isZero {m n : ℕ} (h : m ≤ n)
    (hz : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
      (kernel (idealPowerQuotientDrop (baseIdealSheaf A I f) h F)))) :
    Function.Surjective (adicCohomologyTowerMap A f I F 0 m n h) := by
  have := epi_idealPowerQuotientDrop (baseIdealSheaf A I f) h F
  set φ := idealPowerQuotientDrop (baseIdealSheaf A I f) h F with hφ
  have hS : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_kernel φ }
  obtain ⟨δ, -, hex⟩ := Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅
    hS (Stacks.Cohomology.AffineBase.moduleGlobalSections X)
  have he : Epi (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
      (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).g) :=
    ((hex 0).exact 1).epi_f (hz.eq_of_tgt _ _)
  have hsurj := (ModuleCat.epi_iff_surjective _).mp he
  exact hsurj

/-! ### The theorem on formal functions turns a tower of surjections into surjectivity -/

/-- **A tower of surjections makes `H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ⁿ ℱ)` surjective.**

The input is clause (3) of [Stacks, Tag 02OB]: there is one `c` such that for every `n` and every
`k ≥ n + c` the image of the tower map `H^p(X, ℱ / 𝓘 ᵏ ℱ) ⟶ H^p(X, ℱ / 𝓘 ⁿ ℱ)` is exactly the
image of `H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ⁿ ℱ)`. Taking `k = n + c` and using that the tower map is
surjective makes the latter image everything. Clause (3) is available with no hypothesis beyond
the source's, its [Stacks, Tag 02O8] input being
`Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`. -/
public theorem surjective_adicCohomologyProj_of_surjective_towerMap
    [IsNoetherianRing A] (hX : AlgebraicGeometry.IsProper f)
    (hF : Stacks.SheafOfModules.IsCoherent F) (p : ℕ)
    (hsurj : ∀ (m n : ℕ) (h : m ≤ n),
      Function.Surjective (adicCohomologyTowerMap A f I F p m n h))
    (n : ℕ) : Function.Surjective (adicCohomologyProj A f I F p n) := by
  obtain ⟨c, -, -, hrange⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f hX I F hF p
      Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem
  intro y
  have hr := hrange n (n + c) le_rfl
  have hy : y ∈ LinearMap.range
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
        (idealPowerQuotientDrop (baseIdealSheaf A I f)
          ((Nat.le_add_right n c).trans le_rfl) F)).hom :=
    hsurj n (n + c) (Nat.le_add_right n c) y
  rw [hr] at hy
  exact hy

/-- **The `𝓘`-adic inverse-limit induction of [Stacks, Tag 0EXD].** If `H¹` vanishes on the kernel
of every exponent-drop map, then `H⁰(X, ℱ) ⟶ H⁰(X, ℱ / 𝓘 ⁿ ℱ)` is surjective for every `n`. At
`n = 1` this is the surjectivity of `H⁰(X', 𝒢) ⟶ H⁰(E, 𝒢|_E)` the source produces, from which the
map `α : 𝒪_{X'}^{⊕ r} ⟶ 𝒢` is chosen. -/
public theorem surjective_adicCohomologyProj_of_isZero_kernel
    [IsNoetherianRing A] (hX : AlgebraicGeometry.IsProper f)
    (hF : Stacks.SheafOfModules.IsCoherent F)
    (hz : ∀ (m n : ℕ) (h : m ≤ n),
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
        (kernel (idealPowerQuotientDrop (baseIdealSheaf A I f) h F))))
    (n : ℕ) : Function.Surjective (adicCohomologyProj A f I F 0 n) :=
  surjective_adicCohomologyProj_of_surjective_towerMap A f I F hX hF 0
    (fun m n h => surjective_adicCohomologyTowerMap_of_isZero A f I F h (hz m n h)) n

end Stacks.Cohomology.FormalFunctions

end
