module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine nonvanishing loci containing a finite set

Let `X` be a scheme and `L` an ample invertible `𝒪_X`-module. Let `E ⊆ X` be a finite set of
points contained in an open `W`. Then there are an `n ≥ 1` and a global section `s` of `L ^⊗ n`
such that the nonvanishing locus `X_s` is affine and `E ⊆ X_s ⊆ W`.

## Main results

* `Stacks.AmpleFiniteAffineNonvanishing.exists_tensorPow_powNonvanishingOpen_eq`: a homogeneous
  element of degree `d` of the section ring of `L` is a global section of the `d`-th integer tensor
  power of `L` with the same nonvanishing open.
* `Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite`: the
  statement above, over `Γ(L ^⊗ n, ⊤)` and the scheme-level nonvanishing open.
* `Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite_sections`:
  the statement above, over `sections` and the ringed-space nonvanishing open.

## Implementation notes

Ampleness is `Stacks.Ample.IsAmple`, stated over the integer tensor powers
`Stacks.Ample.tensorPowModule`. The graded section ring is stated over
`Stacks.TensorPowers.natTensorPow`; in nonnegative degree the two modules are equal by
`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow`, and a nonvanishing locus is unchanged by
transporting its section along an isomorphism of modules by `Stacks.Ample.nonvanishingLocus_congr`.

`Stacks.TensorPowers.natTensorPow` is stated for an abstract monoidal category and
`AlgebraicGeometry.Scheme.Modules` is a `def`, so the `eqToIso` transporting the equality of
modules has its category pinned as `eqToIso (C := X.Modules)` and is bound with `let`; otherwise it
lands in the `SheafOfModules` category, where the `app` field used by
`Stacks.Ample.nonvanishingLocus_congr` does not resolve.

The nonvanishing open appears in two forms: `Stacks.AmpleTheory.powNonvanishingOpen`, the
scheme-level open over `Γ(·, ⊤)`, and `Stacks.NonvanishingTrivialize.nonvanishingOpen`, the
ringed-space open over `sections`. They are identified by
`Stacks.NonvanishingSpelling.sectionsEquiv` and
`Stacks.NonvanishingSpelling.nonvanishingOpen_symm_eq`.

## References

* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 00JS](https://stacks.math.columbia.edu/tag/00JS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Ample Stacks.NonvanishingSpelling

universe u

namespace Stacks.AmpleFiniteAffineNonvanishing

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- A homogeneous element of degree `d` of the section ring of `L` is a global section of the
`d`-th integer tensor power of `L` with the same nonvanishing open. -/
theorem exists_tensorPow_powNonvanishingOpen_eq {d : ℕ}
    (a : Stacks.GradedSections.powSections L d) :
    ∃ s : Γ(tensorPowModule X L (d : ℤ), ⊤),
      Stacks.AmpleTheory.powNonvanishingOpen X L d s =
        Stacks.AmpleFiniteAvoidance.nvOpen L a := by
  have heq : (Stacks.TensorPowers.natTensorPow L d : X.Modules) = tensorPowModule X L (d : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L d
  let e : (Stacks.TensorPowers.natTensorPow L d : X.Modules) ≅ tensorPowModule X L (d : ℤ) :=
    eqToIso (C := X.Modules) heq
  refine ⟨e.hom.app ⊤ (Stacks.SectionProduct.globalSection X _ a), Opens.ext ?_⟩
  rw [Stacks.AmpleTheory.coe_powNonvanishingOpen, Stacks.AmpleFiniteAvoidance.coe_nvOpen,
    Stacks.AmpleFiniteAvoidance.nvLocus]
  exact nonvanishingLocus_congr e _

/-- Let `L` be an ample invertible `𝒪_X`-module on a scheme `X`. A finite subset `E` of an open
`W` of `X` lies in an affine nonvanishing locus of a global section of a positive tensor power of
`L`, with that locus contained in `W`. -/
theorem exists_affine_nonvanishingOpen_containing_finite (hL : IsAmple X L) {E : Set X}
    (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      IsAffineOpen (Stacks.AmpleTheory.powNonvanishingOpen X L n s) ∧
        E ⊆ (Stacks.AmpleTheory.powNonvanishingOpen X L n s : Set X) ∧
          (Stacks.AmpleTheory.powNonvanishingOpen X L n s : Set X) ⊆ (W : Set X) := by
  obtain ⟨d, a, hd, hEa, haW, haff⟩ :=
    Stacks.SectionExtension.exists_affine_nvOpen_containing_finite_le_of_isAmple L hL hE W hEW
  obtain ⟨s, hs⟩ := exists_tensorPow_powNonvanishingOpen_eq L a
  refine ⟨d, hd, s, ?_⟩
  rw [hs]
  exact ⟨haff, hEa, SetLike.coe_subset_coe.mpr haW⟩

/-- Let `L` be an ample invertible `𝒪_X`-module on a scheme `X`. A finite subset `E` of an open
`W` of `X` lies in an affine ringed-space nonvanishing locus of a section of a positive tensor
power of `L`, with that locus contained in `W`. -/
@[stacks 09NV, ega "II 4.5.4"]
theorem exists_affine_nonvanishingOpen_containing_finite_sections (hL : IsAmple X L) {E : Set X}
    (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (toSheafOfModules X (tensorPowModule X L (n : ℤ))).sections,
        IsAffineOpen (Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace
            (toSheafOfModules X (tensorPowModule X L (n : ℤ))) s) ∧
          E ⊆ (Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace
            (toSheafOfModules X (tensorPowModule X L (n : ℤ))) s : Set X) ∧
            (Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace
              (toSheafOfModules X (tensorPowModule X L (n : ℤ))) s : Set X) ⊆ (W : Set X) := by
  obtain ⟨n, hn, s, haff, hEs, hsW⟩ :=
    exists_affine_nonvanishingOpen_containing_finite L hL hE W hEW
  refine ⟨n, hn, (sectionsEquiv X (tensorPowModule X L (n : ℤ))).symm s, ?_⟩
  rw [nonvanishingOpen_symm_eq X (tensorPowModule X L (n : ℤ)) s]
  exact ⟨haff, hEs, hsW⟩

end Stacks.AmpleFiniteAffineNonvanishing

end
