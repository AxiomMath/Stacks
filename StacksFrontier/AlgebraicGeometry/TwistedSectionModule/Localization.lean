module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Grading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.Basic

/-!
# The degree-zero localization of the twisted sections at a global section

Stacks Tag 0B5L localizes the graded module `Γ_*(X, F, L) = ⨁_{m ≥ 0} Γ(X, F ⊗ L ^⊗ m)` at a
global section `s` of a tensor power `L ^⊗ d`, viewed as a homogeneous element of degree `d` of
the section ring `Γ_*(X, L)`, and takes the degree-zero part. This file names that object over
library vocabulary: the graded ring and graded module are the ones of the two sibling files, and
the degree-zero part is `GradedModuleDegreeZeroLocalization` of Stacks Tag 01M4.

**The degree is arbitrary.** Stacks Tag 0B5I glues the resulting maps over the standard opens
`D₊(p)` of every homogeneous `p` of positive degree, so nothing here is restricted to degree
one.

## Main definitions

* `Stacks.TwistedSections.homogeneousSectionOfDegree`: a global section of `L ^⊗ d`, as a
  homogeneous element of degree `d` of the section ring.
* `Stacks.TwistedSections.sectionAtNonvanishingOpen`: **the source of Tag 0B5L's map** — the
  degree-zero part `Γ_*(X, F, L)_{(s)}` of the localization of the twisted sections away from `s`.
* `Stacks.TwistedSections.ringAtNonvanishingOpen`: the degree-zero part `Γ_*(X, L)_{(s)}` of the
  localization of the section *ring*, which is `HomogeneousLocalization.Away` and the ring the
  previous module is a module over. This is the source of the ring map of Stacks Tag 01PW.

## Main results

* `Stacks.TwistedSections.homogeneousSection_mem`: the embedded section is homogeneous of
  degree `d`, which is what makes its powers usable as denominators.
* `Stacks.TwistedSections.mk_mem_sectionAtNonvanishingOpen`: `t / sⁿ` lies in the degree-zero
  part whenever the numerator is a twisted section of degree `d * n`. These are the generators,
  so this is the statement that the object is not vacuously small.
* `Stacks.TwistedSections.schemeSectionAtNonvanishingOpen`: the same object for an invertible
  module on a scheme, with every side condition discharged — the concrete instance Tag 0B5L
  needs.

## Implementation notes

**What this file settles and what it does not.** The three objects above are the *source* of Tag
0B5L's map; the map itself is built in the sibling `LocalizationComparison.lean` and produced,
with no hypothesis left over, in `InvertibleSection.lean` and `MonoidalFunctor.lean`. The record
that used to stand here — that the remaining input is the bijectivity of
`Γ(W, F) → Γ(W, F ⊗ L ^⊗ n)`, `t ↦ t ⊗ (sⁿ)|_W`, for an arbitrary module `F` — is **not** what
produces the map, and is corrected in `LocalizationComparison.lean`: the division is defined as
the inverse of multiplication by `sⁿ`, which is bijective for formal reasons once `s` is an
isomorphism, so no elementary tensor of sections ever appears.

**The grading of the section ring needs nothing new.** `Stacks.ExternalGrading.gradedRing` already
proves `GradedRing` for the summands of *any* `DirectSum.GRing`, hence for the section ring, so
`HomogeneousLocalization.Away` applies to it directly.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)
open scoped Stacks.GradedLocalization

universe v u

namespace Stacks.TwistedSections

section Abstract

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] {L : C}

/-- **A global section of `L`, as a homogeneous element of degree one of the section ring.** -/
def homogeneousSection (s : powSections L 1) : sectionRing L :=
  DirectSum.of (powSections L) 1 s

/-- **A global section of a tensor power of `L`, as a homogeneous element of the section ring.**
A section of `L ^⊗ d` is homogeneous of degree `d`; the case `d = 1` is a global section of `L`
itself. -/
def homogeneousSectionOfDegree {d : ℕ} (s : powSections L d) : sectionRing L :=
  DirectSum.of (powSections L) d s

/-- The embedded section is homogeneous of degree one. -/
theorem homogeneousSection_mem (s : powSections L 1) :
    homogeneousSection s ∈ sectionGrading L 1 := ⟨s, rfl⟩

/-- The embedded section is homogeneous of the degree of the tensor power it is a section of. -/
theorem homogeneousSectionOfDegree_mem {d : ℕ} (s : powSections L d) :
    homogeneousSectionOfDegree s ∈ sectionGrading L d := ⟨s, rfl⟩

variable {F : C} [(tensorRight L).Additive] [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **The degree-zero part of the localization of the section ring away from `s`**: the ring
`Γ_*(X, L)_{(s)}` that Stacks Tag 01PW's ring map comes out of. -/
abbrev ringAtNonvanishingOpen (s : powSections L 1) : Type v :=
  HomogeneousLocalization.Away (sectionGrading L) (homogeneousSection s)

/-- **The degree-zero part of the localization of the section ring away from `s`**: the ring
`Γ_*(X, L)_{(s)}` that Stacks Tag 01PW's ring map comes out of. -/
abbrev ringAtNonvanishingOpenOfDegree {d : ℕ} (s : powSections L d) : Type v :=
  HomogeneousLocalization.Away (sectionGrading L) (homogeneousSectionOfDegree s)

/-- **The source of Stacks Tag 0B5L's map**: the degree-zero part `Γ_*(X, F, L)_{(s)}` of the
localization of the graded module of twisted sections away from `s`. A submodule of
`LocalizedModule.Away (homogeneousSection s) (twistModule F L)` over
`Stacks.TwistedSections.ringAtNonvanishingOpen s`. -/
noncomputable abbrev sectionAtNonvanishingOpen (F L : C) [(tensorRight L).Additive]
    [HasTrivialSelfBraiding L] (s : powSections L 1) :=
  GradedModuleDegreeZeroLocalization (sectionGrading L) (moduleGrading F L) (homogeneousSection s)

/-- **The source of Stacks Tag 0B5L's map**: the degree-zero part `Γ_*(X, F, L)_{(s)}` of the
localization of the graded module of twisted sections away from `s`. A submodule of
`LocalizedModule.Away (homogeneousSectionOfDegree s) (twistModule F L)` over
`Stacks.TwistedSections.ringAtNonvanishingOpenOfDegree s`. -/
noncomputable abbrev sectionAtNonvanishingOpenOfDegree (F L : C) [(tensorRight L).Additive]
    [HasTrivialSelfBraiding L] {d : ℕ} (s : powSections L d) :=
  GradedModuleDegreeZeroLocalization (sectionGrading L) (moduleGrading F L)
    (homogeneousSectionOfDegree s)

/-- **The generators of the degree-zero part**: a twisted section of degree `n` divided by the
`n`-th power of `s`. These span, so this is the statement that the object is not vacuously
small. -/
theorem mk_mem_sectionAtNonvanishingOpen (s : powSections L 1) (n : ℕ)
    (t : twistSections F L n) :
    LocalizedModule.mk (DirectSum.of (twistSections F L) n t)
        (⟨homogeneousSection s ^ n, ⟨n, rfl⟩⟩ :
          Submonoid.powers (homogeneousSection s)) ∈ sectionAtNonvanishingOpen F L s := by
  let _ := Module.compHom (R := Localization.Away (homogeneousSection s))
    (LocalizedModule.Away (R := sectionRing L) (homogeneousSection s) (twistModule F L))
    (algebraMap (ringAtNonvanishingOpen s) (Localization.Away (homogeneousSection s)))
  refine Submodule.subset_span ⟨1, n, homogeneousSection_mem s,
    DirectSum.of (twistSections F L) n t, ?_, rfl⟩
  simp only [show n • ((1 : ℕ) : ℤ) = (n : ℤ) by simp]
  exact ⟨t, rfl⟩

/-- **The generators of the degree-zero part**: a twisted section of degree `d * n` divided by
the `n`-th power of a section `s` of `L ^⊗ d`. These span, so this is the statement that the
object is not vacuously small. -/
theorem mk_mem_sectionAtNonvanishingOpenOfDegree {d : ℕ} (s : powSections L d) (n : ℕ)
    (t : twistSections F L (d * n)) :
    LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
        (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
          Submonoid.powers (homogeneousSectionOfDegree s)) ∈
      sectionAtNonvanishingOpenOfDegree F L s := by
  let _ := Module.compHom (R := Localization.Away (homogeneousSectionOfDegree s))
    (LocalizedModule.Away (R := sectionRing L) (homogeneousSectionOfDegree s) (twistModule F L))
    (algebraMap (ringAtNonvanishingOpenOfDegree s)
      (Localization.Away (homogeneousSectionOfDegree s)))
  refine Submodule.subset_span ⟨d, n, homogeneousSectionOfDegree_mem s,
    DirectSum.of (twistSections F L) (d * n) t, ?_, rfl⟩
  simp only [show n • ((d : ℕ) : ℤ) = ((n * d : ℕ) : ℤ) by push_cast; ring]
  exact ⟨twistCongr (Nat.mul_comm d n) t, of_twistCongr (Nat.mul_comm d n) t⟩

end Abstract

/-! ### On a scheme -/

section Scheme

open AlgebraicGeometry Stacks.Ample

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (F L : X.Modules) [IsInvertibleModule X L]

/-- **The graded module of twisted sections of an invertible module on a scheme**,
`Γ_*(X, F, L) = ⨁_{m ≥ 0} Γ(X, F ⊗ L ^⊗ m)`, with its module structure over `Γ_*(X, L)`. Every
side condition of the abstract development is discharged here. -/
noncomputable abbrev schemeTwistModule : Type u := twistModule F L

/-- **The source of Stacks Tag 0B5L's map, for an invertible module on a scheme**: the
degree-zero part `Γ_*(X, F, L)_{(s)}` of the localization away from a global section `s` of `L`.
This is the domain of the map in the statement of Tag 0B5L, in library vocabulary. -/
noncomputable abbrev schemeSectionAtNonvanishingOpen (s : Stacks.GradedSections.powSections L 1) :=
  sectionAtNonvanishingOpen F L s

/-- **The source of Stacks Tag 0B5L's map, for an invertible module on a scheme**: the
degree-zero part `Γ_*(X, F, L)_{(s)}` of the localization away from a global section `s` of `L`.
This is the domain of the map in the statement of Tag 0B5L, in library vocabulary. -/
noncomputable abbrev schemeSectionAtNonvanishingOpenOfDegree {d : ℕ}
    (s : Stacks.GradedSections.powSections L d) :=
  sectionAtNonvanishingOpenOfDegree F L s

/-- **The degree-zero part of the localized section ring on a scheme**: the ring that Stacks
Tag 01PW's ring map comes out of. -/
noncomputable abbrev schemeRingAtNonvanishingOpen (s : Stacks.GradedSections.powSections L 1) :
    Type u :=
  ringAtNonvanishingOpen s

/-- **The degree-zero part of the localized section ring on a scheme**: the ring that Stacks
Tag 01PW's ring map comes out of. -/
noncomputable abbrev schemeRingAtNonvanishingOpenOfDegree {d : ℕ}
    (s : Stacks.GradedSections.powSections L d) : Type u :=
  ringAtNonvanishingOpenOfDegree s

end Scheme

end Stacks.TwistedSections

end
