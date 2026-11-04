module

public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.LowDegree
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Reduction
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Restriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine localization triangle exists, and the low-degree exact sequence

Let `I` be a finitely generated ideal of a commutative ring `R` and let `U = Spec R \ V(I)`.
`StacksFrontier/RingTheory/LocalCohomology/LowDegree/ExactSequence.lean` derives the five-term exact
sequence
`0 ⟶ H⁰_I(M) ⟶ M ⟶ Γ(U, M̃|U) ⟶ H¹_I(M) ⟶ 0`
of Stacks 0DWR from a `Stacks.LocalCohomology.LocalizationTriangleData`, and
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/Reduction.lean` reduces that structure to two
statements about the degree-zero cohomology of the cone of the Čech augmentation. Those two
statements are proved in
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/CechHomology.lean` and
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/Restriction.lean`. This file puts them
together: the structure has a term, and the exact sequence holds unconditionally.

The module universe is independent of the ring universe. `Cech.cechComplex` itself is a complex
of `ModuleCat.{max u v} R` even for `M` in `Type v`, because its terms are the localizations
`M_{f_{i₀} ⋯ f_{i_p}}`, which are quotients of `M × S` for a submonoid `S` of `R`; the
construction below therefore uses the small model `Cech.cechComplexShrink` of
`StacksFrontier/RingTheory/Cech/Shrink.lean`, whose terms are the canonical `Type v` models of those
localizations, through
`Stacks.LocalCohomology.cechLocalizationTriangleDataFree` of
`StacksFrontier/RingTheory/LocalCohomology/FreeUniverse/LowDegree.lean`.

## Main definitions

* `Stacks.LocalCohomology.cechLocalizationTriangleData` — **the affine localization triangle data
  of Stacks 0DWR**, for an ideal presented by a finite family of generators, from
  `Cech.cechComplex` and so at a module universe above the ring universe.

## Main results

* `Stacks.LocalCohomology.nonempty_localizationTriangleData` — a finitely generated ideal has a
  localization triangle data.
* `Stacks.LocalCohomology.lowDegreeExactSequence` — **the five-term exact sequence of
  Stacks 0DWR** holds for a localization triangle data chosen functorially in the module, for every
  module and every identification of a sheaf on `U` with the restriction of the associated sheaf.

## Implementation notes

`Stacks.LocalCohomology.cechLocalizationTriangleData` is kept at the module universe `max u v`:
it is the triangle data built from `Cech.cechComplex` directly, and
`StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/CechConeExact.lean` consumes it in
that form. The two results below use the small model instead, so they hold with the two universes
independent, and the pinned data is the special case `v := max u v`.

No attribute for tag 0DWR is placed here.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (I : Ideal R) (hI : I.FG)

/-- **The affine localization triangle data of Stacks 0DWR.** For an ideal `I = (f₁, …, f_r)` of a
commutative ring `R`, the localization triangle
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`
over `U = Spec R \ V(I)` exists functorially in the module, with the counit of Stacks 0A6Q as its
first map, and with the degree-zero cohomology of its third term identified with the sections of
the associated sheaf on `U` so that the second map is
`m ↦ m / 1`. All seven pieces of data come from the Čech model of local cohomology. -/
def cechLocalizationTriangleData (hIf : Ideal.span (Set.range f) = I) :
    LocalizationTriangleData.{u, max u v} R I hI :=
  localizationTriangleDataOfCechHomologyComparison.{v} f I hI hIf
    (fun {_ _} g z => cechComplementHomologyZeroEquivKer_naturality.{v} f g z)
    (fun M m i => cechComplementHomologyZeroEquivKer_restriction.{v} f M m i)

variable {f I}

variable (R I) in
/-- **A finitely generated ideal has an affine localization triangle data.** Choose a finite
family of generators and take the Čech model, in the small model of
`StacksFrontier/RingTheory/Cech/Shrink.lean` so that the module universe stays independent of the
ring universe. -/
theorem nonempty_localizationTriangleData :
    Nonempty (LocalizationTriangleData.{u, v} R I hI) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  exact ⟨cechLocalizationTriangleDataFree.{v} f I hf hI⟩

variable (R I) in
/-- **Stacks 0DWR, the low-degree exact sequence.** The affine localization triangle of
`U = Spec R \ V(I)` can be chosen functorially in the module, and its canonical restriction and
connecting maps then give the exact sequence
`0 ⟶ H⁰_I(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_I(M) ⟶ 0`
for every module `M` and every identification of a sheaf `F` on `U` with the restriction of the
sheaf associated to `M`.

The module universe is independent of the ring universe. The sections of the associated sheaf
live in `Type (max u v)` in any case, which is why `F` has that section universe while `M` is an
arbitrary object of `ModuleCat.{v} R`. -/
@[ega "III 1.4.3" "(1.4.3.2), special case",
  sga "2 II Corollary4",
  sga "4 V 6.5" "(6.5.3), special case"]
theorem lowDegreeExactSequence :
    ∃ D : LocalizationTriangleData.{u, v} R I hI,
      ∀ (M : ModuleCat.{v} R)
        (F : SheafOfModules.{max u v} (complementZeroLocus R I : Scheme).ringCatSheaf)
        (e : F ≅ complementTilde R I M),
        Function.Injective (localCohomologyZeroToModule R I hI M) ∧
        Function.Exact (localCohomologyZeroToModule R I hI M)
          (restrictionToComplement D M F e) ∧
        Function.Exact (restrictionToComplement D M F e) (localizationBoundary D M F e) ∧
        Function.Surjective (localizationBoundary D M F e) := by
  obtain ⟨D⟩ := nonempty_localizationTriangleData.{v} R I hI
  exact ⟨D, fun M F e =>
    ⟨localCohomologyZeroToModule_injective R I hI M,
      exact_localCohomologyZeroToModule_restrictionToComplement D M F e,
      exact_restrictionToComplement_localizationBoundary D M F e,
      localizationBoundary_surjective D M F e⟩⟩

end Stacks.LocalCohomology

end
