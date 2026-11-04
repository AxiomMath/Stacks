module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# The canonical section of `𝒪(1)` attached to a degree-one element does not vanish on `D₊(f)`

Let `𝒮` be a nonnegatively graded ring and let `f ∈ 𝒮 d`. The element `f` determines a global
section of the twisting sheaf `𝒪_{Proj 𝒮}(d)`, the global homogeneous fraction `f / 1`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`). For `d = 1` its nonvanishing locus
contains the standard open `D₊(f)`: on any open contained in `D₊(f)` the restriction of `f / 1`
is the trivializing section of `𝒪(1)` of [Stacks, Tag 01MS].

## Main definitions

* `Stacks.ProjTwistSection.twistingModule`: the twisting sheaf `𝒪_{Proj 𝒮}(d)`, ascribed at
  `AlgebraicGeometry.Scheme.Modules` rather than at the sheaf of modules over
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf`.
* `Stacks.ProjTwistSection.homogeneousSection`: the global section `f / 1` of `𝒪(d)`.
* `Stacks.ProjTwistSection.degreeOneGenerator`: `f / 1` as a local frame of `𝒪(1)` on `D₊(f)`.

## Main results

* `Stacks.ProjTwistSection.homogeneousSection_eval_eq_trivializingSection`: on an open contained
  in `D₊(f)` the section `f / 1` of `𝒪(1)` is the Tag 01MS trivializing section.
* `Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection`: `D₊(f)` is
  contained in the nonvanishing locus of `f / 1`.

## Implementation notes

`twistingModule` is an `abbrev`, so that the two spellings of the structure sheaf of `Proj 𝒮`
can be interchanged without a bridge.

The identification of `f / 1` with the trivializing section at arbitrary degree `d` and index
`n : ℕ` is `Stacks.AlgebraicGeometry.ProjTrivialization.powSection_eq_trivializingSection`. The
statement here is at degree one because its left-hand side is read at
`(twistingModule 𝒮 (d : ℤ)).sections`, where the index is `d` and not `1 * d`.

`basicOpen_le_nonvanishingOpen_homogeneousSection` takes invertibility of `𝒪(1)` as an instance
hypothesis: `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf`
derives it only under a hypothesis on `𝒮` (a cover of `Proj 𝒮` by standard opens of degree-one
elements), not on `f`.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.ProjTwistSection

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
    (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The twisting sheaf `𝒪_{Proj 𝒮}(d)`, ascribed as a module on the scheme `Proj 𝒮`. -/
noncomputable abbrev twistingModule (d : ℤ) : (AlgebraicGeometry.Proj 𝒮).Modules :=
  twistingSheaf 𝒮 d

/-- The global section `f / 1` of `𝒪_{Proj 𝒮}(d)` determined by a homogeneous element `f` of
degree `d`. -/
noncomputable def homogeneousSection {d : ℕ} (f : S) (hf : f ∈ 𝒮 d) :
    (twistingModule 𝒮 (d : ℤ)).sections :=
  Stacks.SheafOfModules.sectionsOfTop (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
    (twistingModule 𝒮 (d : ℤ)) (degreeSection 𝒮 d ⟨f, hf⟩)

/-- **On an open contained in `D₊(f)` the section `f / 1` of `𝒪(1)` is the trivializing section
of [Stacks, Tag 01MS].** -/
theorem homogeneousSection_eval_eq_trivializingSection (f : S) (hf : f ∈ 𝒮 1)
    {V : Opens (ProjectiveSpectrum.top 𝒮)} (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (((homogeneousSection 𝒮 f hf).eval (op V) : _) :
        ↥(moduleSections 𝒮 (twistGrading 𝒮 (1 * ((1 : ℕ) : ℤ))) V))
      = Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection 𝒮 hf 1 hV := by
  apply Subtype.ext
  funext x
  have := x.1.isPrime
  rw [Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection]
  change LocalizedModule.mk f (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
      = Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun 𝒮 1 hV x
  rw [Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun]
  change Localization.mk f (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) = _
  simp
  rfl

/-- **The section `f / 1` is a local frame of `𝒪(1)` on `D₊(f)`**: multiplication by it is
bijective on every open contained in `D₊(f)`. -/
noncomputable def degreeOneGenerator (f : S) (hf : f ∈ 𝒮 1) :
    Stacks.SheafOfModules.GeneratorSections (AlgebraicGeometry.Proj 𝒮).toRingedSpace
      (twistingModule 𝒮 1) (ProjectiveSpectrum.basicOpen 𝒮 f) :=
  ⟨(homogeneousSection 𝒮 f hf).eval (op (ProjectiveSpectrum.basicOpen 𝒮 f)), by
    intro V hVle
    have hres : (homogeneousSection 𝒮 f hf).eval (op V) =
        (twistingModule 𝒮 1).val.restrictₛₗ (homOfLE hVle).op
          ((homogeneousSection 𝒮 f hf).eval (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :=
      (PresheafOfModules.sections_property (homogeneousSection 𝒮 f hf) (homOfLE hVle).op).symm
    rw [← hres, homogeneousSection_eval_eq_trivializingSection 𝒮 f hf hVle]
    exact Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom 𝒮 hf 1 hVle⟩

/-- **The canonical section of `𝒪(1)` attached to a degree-one element `f` does not vanish
anywhere on the standard open `D₊(f)`.** -/
theorem basicOpen_le_nonvanishingOpen_homogeneousSection (f : S) (hf : f ∈ 𝒮 1)
    [Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace).property (twistingModule 𝒮 1)] :
    ProjectiveSpectrum.basicOpen 𝒮 f ≤
      Stacks.SheafOfModules.nonvanishingOpen (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
        (twistingModule 𝒮 1) (homogeneousSection 𝒮 f hf) := by
  intro x hx
  exact (Stacks.SheafOfModules.mem_nonvanishingLocus_iff_isUnit_ringGerm (twistingModule 𝒮 1)
    (homogeneousSection 𝒮 f hf) (degreeOneGenerator 𝒮 f hf) 1 ((one_smul _ _).symm) x hx).mpr
    (by simp)

end Stacks.ProjTwistSection

end
