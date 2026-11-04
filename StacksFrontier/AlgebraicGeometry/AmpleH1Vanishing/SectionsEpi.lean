module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Surjectivity on sections from vanishing of the first cohomology

Let `F : 𝒜 ⥤ ℬ` be an additive, left exact functor between abelian categories, with `𝒜` having
enough injectives, and let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence of `𝒜`. The long exact
sequence of the right derived functors of `F` begins

`0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ R¹F(A) ⟶ ⋯`

so `F(B) ⟶ F(C)` is epi as soon as `R¹F(A) = 0`. This file records that consequence and its
specialisation to the global sections of sheaves of modules on a scheme, where it reads: a short
exact sequence of `𝒪_X`-modules whose first term has vanishing `H¹(X, −)` induces a surjection
on global sections.

This is the step that carries the cohomological criterion for ampleness of
[Stacks, Tag 0B5P] (Chapter 30, Cohomology of Schemes) — the criterion used by
[Stacks, Tag 0B5U] for the implication (3) `⇒` (1), and hence by [Stacks, Tag 0B5X] for the
converse direction on a proper curve. There the sequence is
`0 ⟶ ℐ' ⊗ 𝓛^{⊗n} ⟶ ℐ ⊗ 𝓛^{⊗n} ⟶ (ℐ/ℐ') ⊗ 𝓛^{⊗n} ⟶ 0` and the hypothesis is the chosen
vanishing of `H¹(X, ℐ' ⊗ 𝓛^{⊗n})`; what the step produces is the global section of
`ℐ ⊗ 𝓛^{⊗n}` cutting out an affine nonvanishing locus around a closed point.

## Main results

* `Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one`: the general statement,
  for an additive left exact functor between abelian categories.
* `Stacks.Cohomology.SectionsEpi.shortExact_map_of_isZero_rightDerived_one`: the image of the
  short exact sequence stays short exact.
* `Stacks.Cohomology.SectionsEpi.epi_moduleGlobalSections_map_of_isZero_rightDerived_one`: the
  same for global sections of sheaves of modules on a scheme.

## Implementation notes

No tag attribute is attached. The long exact sequence itself is [Stacks, Tag 010Q], already
carried by `CategoryTheory.DeltaFunctor`, and the identification of `R⁰F` with `F` for a left
exact `F` is `CategoryTheory.Functor.rightDerivedZeroIsoSelf`; what is below is a corollary of
the two and states no tag of its own.

The `ℕ`-indexed long exact sequence comes from
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, which already packages it
with no hypothesis beyond additivity of `F` and enough injectives in the source — in particular
the comparison between Mathlib's `ℕ`-indexed `Functor.rightDerived` and the `ℤ`-indexed
`Functor.rightDerivedPlus` on the bounded below derived category is spent inside it, and does
not have to be redone here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Cohomology.SectionsEpi

universe u

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **Vanishing of `R¹F` on the first term of a short exact sequence makes `F` surjective on the
other two.** For an additive, left exact `F : 𝒜 ⥤ ℬ` between abelian categories with enough
injectives in `𝒜`, and a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, the long exact sequence
`0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ R¹F(A) ⟶ ⋯` of [Stacks, Tag 010Q] is exact at `F(C)`, so a vanishing
`R¹F(A)` forces `F(B) ⟶ F(C)` to be epi. -/
public theorem epi_map_g_of_isZero_rightDerived_one (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : IsZero ((F.rightDerived 1).obj S.X₁)) : Epi (F.map S.g) := by
  set E := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F
  have hδ : E.δ hS 0 = 0 := (show IsZero ((E.functor 1).obj S.X₁) from h₁).eq_of_tgt _ _
  have hepi : Epi ((F.rightDerived 0).map S.g) :=
    (ShortComplex.exact_iff_epi _ hδ).1 (E.exact_δ₁ hS 0)
  rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf S.g]
  infer_instance

/-- **Vanishing of `R¹F` on the first term keeps a short exact sequence short exact under `F`**,
for an additive left exact `F`: `F` preserves the monomorphism and exactness in the middle, and
`F(B) ⟶ F(C)` is epi by `epi_map_g_of_isZero_rightDerived_one`. -/
public theorem shortExact_map_of_isZero_rightDerived_one (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : IsZero ((F.rightDerived 1).obj S.X₁)) : (S.map F).ShortExact := by
  have := hS.mono_f
  have : Epi (F.map S.g) := epi_map_g_of_isZero_rightDerived_one F hS h₁
  have : Mono (F.map S.f) := inferInstance
  have : Mono (S.map F).f := ‹Mono (F.map S.f)›
  have : Epi (S.map F).g := ‹Epi (F.map S.g)›
  exact ⟨hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance⟩

end General

section Scheme

open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **A short exact sequence of `𝒪_X`-modules whose first term has vanishing `H¹` induces a
surjection on global sections.** This is
`Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one` for the global sections
functor `Γ(X, −) : Mod(𝒪_X) ⥤ Mod(Γ(X, ⊤))`, which is additive and left exact. It is the step
by which the cohomological criterion for ampleness of [Stacks, Tag 0B5P] produces a global
section of an ideal sheaf twist from the vanishing it assumes. -/
@[sga "6 II 2.1.2" "b)"]
public theorem epi_moduleGlobalSections_map_of_isZero_rightDerived_one (X : Scheme.{u})
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : IsZero ((((SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).rightDerived 1)).obj S.X₁)) :
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map S.g) :=
  epi_map_g_of_isZero_rightDerived_one
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) hS h₁

end Scheme

end Stacks.Cohomology.SectionsEpi

end
