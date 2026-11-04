module

public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.GradedModule
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.AffineBaseCase
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of [Stacks, Tag 09MR] over an affine open

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s` a global section of `ℒ` and `ℱ` a
quasi-coherent `𝒪_X`-module. [Stacks, Tag 09MR] asserts that on a quasi-compact and
quasi-separated `X` the canonical map

`H^p_*(X, ℒ, ℱ)₍s₎ ⟶ H^p(X_s, ℱ)`,  `ξ / sⁿ ↦ s^{-n} ξ`

out of the degree-zero localization at `s` of the graded module
`H^p_*(X, ℒ, ℱ) = ⨁_{n ∈ ℤ} H^p(X, ℱ ⊗ ℒ^{⊗ n})` over `Γ_*(X, ℒ) = ⨁_{n ≥ 0} Γ(X, ℒ^{⊗ n})` is
an isomorphism. The source proves it by the induction principle of [Stacks, Tag 08DR] over the
quasi-compact opens of `X`, with an affine open as the base case.

This file proves the **base case for the localization itself**: over an affine open `U` and in
positive degree the degree-zero localization `H^p_*(U, ℒ, ℱ)₍s₎` is trivial and
`H^p(U ⊓ X_s, ℱ)` vanishes, so **every** additive map between them -- in particular any
comparison map the source may single out -- is bijective.

## What this adds

`StacksFrontier/AlgebraicGeometry/TwistedCohomologyLocalization/AffineBaseCase.lean` proves the
componentwise statement: each `H^p(U, ℱ ⊗ ℒ^{⊗ n})` and `H^p(U ⊓ X_s, ℱ)` vanishes over an
affine open. It could not say anything about `H^p_*(U, ℒ, ℱ)₍s₎` itself, because the graded
module structure on `⨁_n H^p(U, ℱ ⊗ ℒ^{⊗ n})` was not available in a positive degree and
`GradedModuleDegreeZeroLocalization` takes it as an instance argument -- so the *type* of the
source of the comparison map did not exist. That structure is now
`StacksFrontier/AlgebraicGeometry/TwistedCohomologyLocalization/GradedModule.lean`, and this file
draws the conclusion the earlier file had to defer.

## Main results

* `Stacks.Cohomology.TwistedGradedModule.forall_eq_zero_grading_of_isAffineOpen`: the
  non-negative homogeneous components of `H^p_*(U, ℒ, ℱ)` vanish over an affine open in positive
  degree.
* `Stacks.Cohomology.TwistedGradedModule.subsingleton_degreeZeroLocalization_of_isAffineOpen`:
  **the degree-zero localization `H^p_*(U, ℒ, ℱ)₍s₎` is trivial** over an affine open in
  positive degree.
* `Stacks.Cohomology.TwistedGradedModule.bijective_of_isAffineOpen`: **every additive map
  `H^p_*(U, ℒ, ℱ)₍s₎ ⟶ H^p(U ⊓ X_s, ℱ)` is bijective** over an affine open in positive degree.

## Implementation notes

The element of the graded section ring at which the localization is taken is
`Stacks.SheafOfModules.homogeneousSection X ℒ s`, the degree-one homogeneous element attached to
a global section `s` of `ℒ`; that it has degree one is
`Stacks.SheafOfModules.homogeneousSection_mem`, which is what the triviality criterion needs.

**This is a vanishing statement on both sides, and nothing more.** Over an affine open the source
is trivial because all its non-negative homogeneous components are, by [Stacks, Tag 01XB], and
the target is trivial because `U ⊓ X_s` is affine by [Stacks, Tag 01PV]. Bijectivity of an
arbitrary additive map therefore holds for the reason that both sides are singletons, and the
statement carries no information about a comparison map at a nonempty proper `X_s`. The general
quasi-compact quasi-separated isomorphism needs two further inputs which are not available: the
untwisting isomorphism `H^p(X_s, ℱ ⊗ ℒ^{⊗ n}) ≅ H^p(X_s, ℱ)`, without which the canonical map
has no definition, and exactness of the degree-zero localization, without which the
Mayer--Vietoris induction step cannot be run.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules

universe u

namespace Stacks.Cohomology.TwistedGradedModule

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **The non-negative homogeneous components of `H^p_*(U, ℒ, ℱ)` vanish over an affine open in
positive degree.** A homogeneous element of degree `n` is a single cohomology class of the twist
`ℱ ⊗ ℒ^{⊗ n}`, and those groups vanish over an affine open by [Stacks, Tag 01XB]. -/
theorem forall_eq_zero_grading_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    ∀ n : ℕ, ∀ x ∈ grading X L F p U (n : ℤ), x = (0 : twistedCohomologyModule X L F p U) := by
  intro n x hx
  obtain ⟨ξ, rfl⟩ := hx
  have hzero : IsZero (Hgroup X.ringCatSheaf U p (twist X L F (n : ℤ))) :=
    Stacks.Cohomology.TwistedLocalization.isZero_hgroup_twistedModule_of_isAffineOpen
      X L F U hU p hp (n : ℤ)
  have : Subsingleton (Hgroup X.ringCatSheaf U p (twist X L F (n : ℤ)) : Type u) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hzero
  have hξ : ξ = 0 := Subsingleton.elim _ _
  rw [hξ]
  exact map_zero _

/-- **The degree-zero localization `H^p_*(U, ℒ, ℱ)₍s₎` is trivial over an affine open in positive
degree.** Every element of it is a fraction with homogeneous numerator of non-negative degree,
and all those numerators vanish. -/
theorem subsingleton_degreeZeroLocalization_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (s : L.sections) (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    Subsingleton (degreeZeroLocalization X L F p U (homogeneousSection X L s)) :=
  Stacks.Cohomology.TwistedLocalization.subsingleton_degreeZeroLocalization_of_forall_eq_zero
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p U)
    (homogeneousSection_mem X L s)
    (forall_eq_zero_grading_of_isAffineOpen X L F U hU p hp)

/-- **[Stacks, Tag 09MR] over an affine open.** Let `X` be a scheme, `ℒ` an invertible
`𝒪_X`-module, `s` a global section of `ℒ`, `ℱ` a quasi-coherent `𝒪_X`-module, `U ⊆ X` an affine
open and `p > 0`. Then every additive map

`H^p_*(U, ℒ, ℱ)₍s₎ ⟶ H^p(U ⊓ X_s, ℱ)`

is bijective -- in particular the comparison map `ξ / sⁿ ↦ s^{-n} ξ` of the source would be,
were it available. Both sides are trivial: the source by
`subsingleton_degreeZeroLocalization_of_isAffineOpen`, the target because `U ⊓ X_s` is affine by
[Stacks, Tag 01PV] and the positive-degree cohomology of a quasi-coherent module on an affine
open vanishes by [Stacks, Tag 01XB].

This is the base case of the induction of [Stacks, Tag 08DR] by which the source proves the tag
on a quasi-compact quasi-separated scheme, which is
`Stacks.Cohomology.TwistedLocalizationMap.bijective_canonicalMap_top`; the tag is registered
there. What is new here relative to
`Stacks.Cohomology.TwistedLocalization.isZero_twistedModule_and_nonvanishingOpen_of_isAffineOpen`
is that the degree-zero localization itself -- the source of the comparison map, whose type
needs the graded module structure of
`StacksFrontier/AlgebraicGeometry/TwistedCohomologyLocalization/GradedModule.lean` -- is shown
trivial, and the conclusion is drawn for maps rather than for the homogeneous components. -/
theorem bijective_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (s : L.sections) (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p)
    (φ : degreeZeroLocalization X L F p U (homogeneousSection X L s) →+
      (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) p F : Type u)) :
    Function.Bijective φ := by
  have hsrc : Subsingleton (degreeZeroLocalization X L F p U (homogeneousSection X L s)) :=
    subsingleton_degreeZeroLocalization_of_isAffineOpen X L F s U hU p hp
  have htgt : Subsingleton
      (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) p F : Type u) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      (Stacks.Cohomology.TwistedLocalization.isZero_hgroup_nonvanishingOpen_of_isAffineOpen
        X L F s U hU p hp)
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end Stacks.Cohomology.TwistedGradedModule

end
