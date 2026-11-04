module

public import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The standard open of a homogeneous element, as the nonvanishing open of a global section

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring generated as an `𝒜 0`-algebra by its degree-one part,
let `X = Proj A` and let `f ∈ 𝒜 (n d)` be homogeneous with `0 < d`. Two opens of `X` are
attached to `f`:

* the standard open `D₊(f)`, over which the charts of `X` and the local comparison map of
  [Stacks, Tag 03GM] are built, and
* the nonvanishing open `X_s` of the global section `s` of the invertible module `𝒪_X(n d)` that
  `f` determines, which is the open that [Stacks, Tag 01PW] localizes the twisted global sections
  over.

They are the same open. For the underlying sets this is
`Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen`,
with the left-hand side spelled as `Stacks.Ample.nonvanishingLocus`; this file states it for the
bundled opens, with the left-hand side spelled as `Stacks.SheafOfModules.nonvanishingOpen`, which
is the spelling of the statement of Tag 01PW. The two spellings agree by
`Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop`.

## Main results

* `nonvanishingOpen_degreeSection_eq_basicOpen`: **`X_s = D₊(f)` as opens**, for `s` the global
  section of `𝒪(n d)` attached to a homogeneous `f` of degree `n d`, in the spelling of Tag 01PW.
* `nonvanishingOpen_degreeSection_eq_projectiveSpectrumBasicOpen`: the same with the right-hand
  side spelled `ProjectiveSpectrum.basicOpen`, which is how the chart comparison map of Tag 03GM
  names its chart.
* `bijective_sectionLocalizationMap_degreeSection`: the comparison map
  `(⨁_m Γ(X, ℱ ⊗ 𝒪(n d)^{⊗ m}))_{(s)} → Γ(D₊(f), ℱ)` is bijective for `ℱ` quasi-coherent and
  `Proj A` quasi-compact.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection twistGlobalSections)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartNonvanishingOpen

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **`X_s = D₊(f)` as opens of `Proj A`, in the spelling Tag 01PW is stated at.** For `A`
generated as an `𝒜 0`-algebra by its degree-one part, `0 < d` and `f` homogeneous of degree
`n d`, the open on which the global section of `𝒪(n d)` attached to `f` does not vanish is the
standard open of `f`.

`Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen`
is this equality of underlying sets with the left-hand side spelled
`Stacks.Ample.nonvanishingLocus`; the two spellings are reconciled by
`Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop`. -/
@[ega "II 3.3.3" "affine base Y = Spec A₀"]
theorem nonvanishingOpen_degreeSection_eq_basicOpen
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) {d : ℕ} (hd : 0 < d) (n : ℕ)
    (f : 𝒜 (n * d))
    [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ))] :
    Stacks.SheafOfModules.nonvanishingOpen
        (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace)
        (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ))
        (Stacks.SheafOfModules.sectionsOfTop
          (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace)
          (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ)) (degreeSection 𝒜 (n * d) f)) =
      AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) :=
  Opens.ext
    ((Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop (AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ)) (degreeSection 𝒜 (n * d) f)).trans
      (Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
        𝒜 hgen hd n f))

/-- `nonvanishingOpen_degreeSection_eq_basicOpen` with the standard open spelled as
`ProjectiveSpectrum.basicOpen`, which is how the local comparison map of Tag 03GM names it;
`AlgebraicGeometry.Proj.basicOpen 𝒜 f` is defined as `ProjectiveSpectrum.basicOpen 𝒜 f`. -/
theorem nonvanishingOpen_degreeSection_eq_projectiveSpectrumBasicOpen
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) {d : ℕ} (hd : 0 < d) (n : ℕ)
    (f : 𝒜 (n * d))
    [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ))] :
    Stacks.SheafOfModules.nonvanishingOpen
        (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace)
        (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ))
        (Stacks.SheafOfModules.sectionsOfTop
          (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace)
          (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ)) (degreeSection 𝒜 (n * d) f)) =
      ProjectiveSpectrum.basicOpen 𝒜 (f : A) :=
  nonvanishingOpen_degreeSection_eq_basicOpen 𝒜 hgen hd n f

/-- **[Stacks, Tag 01PW] part (2) read on a chart of `Proj A`.** For `A` generated in degree one,
`Proj A` quasi-compact and `ℱ` quasi-coherent, the comparison map of Tag 0B5L for the invertible
module `𝒪(n d)` and the global section attached to a homogeneous `f` of degree `n d` is
bijective: `(⨁_m Γ(X, ℱ ⊗ 𝒪(n d)^{⊗ m}))_{(s)} → Γ(D₊(f), ℱ)`.

This is `Stacks.SheafOfModules.sectionLocalizationMap_bijective` for `Proj A`. Quasi-separatedness
of `Proj A` is automatic (`Stacks.AlgebraicGeometry.ProjQuasiSeparated.quasiSeparatedSpace_proj`);
quasi-compactness is not, and is a hypothesis. -/
theorem bijective_sectionLocalizationMap_degreeSection
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)] {d : ℕ} (n : ℕ) (f : 𝒜 (n * d))
    [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ))]
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent] :
    Function.Bijective (Stacks.SheafOfModules.sectionLocalizationMap
      (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ)) F
      (Stacks.SheafOfModules.sectionsOfTop
        (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace)
        (twistingSheaf 𝒜 ((n * d : ℕ) : ℤ)) (degreeSection 𝒜 (n * d) f))) :=
  Stacks.SheafOfModules.sectionLocalizationMap_bijective _ _ _ _

end Stacks.AlgebraicGeometry.ProjChartNonvanishingOpen

end
