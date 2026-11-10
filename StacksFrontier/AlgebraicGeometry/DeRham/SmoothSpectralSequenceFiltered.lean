module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackKFlatMonoidal
import StacksCore.Tactic.StacksAttribute

/-!
# The spectral sequence of a smooth morphism, at the filtration of Section 50.12

`StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence` produces the bounded spectral
sequence of [Stacks, Tag 0FMM] from an arbitrary filtration of `Ω^•_{X/S}` supplied as a filtered
complex, and `StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltration` constructs the filtration
Section 50.12 actually uses — the one by the forms pulled back from `Y`. This file joins them: the
spectral sequence is stated at that filtration, so that nothing about the filtration is assumed.

Concretely, of the five hypotheses of
`Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence` three are discharged here: the
filtered complex `K` is `Stacks.DeRhamSmooth.deRhamSmoothFiltration`, the identification
`K.X = Ω^•_{X/S}` holds by `rfl`, and the exhaustion is the last clause of
`Stacks.DeRhamSmooth.deRhamSmoothFiltration_spec`. What remains assumed is the eventual vanishing
of `R^nf_*F^pΩ^•_{X/S}` for `p ≫ 0`, and the identification of `R^{p+q}f_*gr^pΩ^•_{X/S}` with the
first page.

## Main results

* `Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence_of_pullback`: **[Stacks, Tag 0FMM]**
  at the filtration of Section 50.12.

## Implementation notes

The filtered complex of `SmoothFiltration` is stated over
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf ((f ≫ g)^{-1}𝒪_S)`, the ring sheaf the
relative de Rham complex of `f ≫ g` is built over, while the spectral sequence is stated over
`structureSheafRing (Stacks.DeRhamDirectImage.inverseImageBase (f ≫ g))`,
the structure ring sheaf of the
inverse-image ringed space. The two have the same body, so the filtered complex is accepted
where the spectral sequence asks for one with no transport; this is the same identification that
lets `Stacks.DeRhamDirectImage.deRhamCochainComplex` be read in either spelling.

This is a separate module rather than an addition to `SmoothSpectralSequence` because
`StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex`, which constructs the pullback map the
filtration is built from, imports `SmoothSpectralSequence` for
`Stacks.DeRhamSmooth.relativeBase`.

## References

* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.FilteredComplex Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

/-- Sheaves of modules on a ringed space form an abelian category:
`Stacks.Cohomology.DerivedPullbackTensor.abelianStructureSheafRing` under its name in this
namespace. Supplied explicitly as a local instance: at this import surface the search for it
exceeds the default instance-synthesis budget. -/
@[instance_reducible]
alias abelianModulesRingSheaf := Stacks.Cohomology.DerivedPullbackTensor.abelianStructureSheafRing

attribute [local instance] abelianModulesRingSheaf

/-- The `p`-th graded piece of a filtered complex of sheaves of modules on a ringed space.
Stated over an abstract ringed space so that the zero-morphism and cokernel instances are
resolved once, at a small type: resolving them against the concrete inverse-image ringed space
exceeds the default instance-synthesis budget at this import surface. -/
def gradedPiece (Z : RingedSpace.{u, u}) (p : ℤ)
    (K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing Z))) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ :=
  (FilteredObject.gr p).obj K

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **Stacks Project, Tag 0FMM**, at the filtration of Section 50.12. Let `f : X ⟶ Y` be a
quasi-compact, quasi-separated and smooth morphism of schemes over a base `S`, with `g : Y ⟶ S`
the structure morphism of the target. There is a bounded cohomological spectral sequence of
sheaves of `g^{-1}𝒪_S`-modules on `Y`, starting at its first page, with

`E_1^{p, q} = H^q(Ω^p_{Y/S} ⊗^{\mathbf L}_{𝒪_Y} Rf_*Ω^•_{X/Y})`,

which abuts to `R^{p + q}f_*Ω^•_{X/S}`.

The filtration is not assumed: it is `Stacks.DeRhamSmooth.deRhamSmoothFiltration`, the filtration
of `Ω^•_{X/S}` by the forms pulled back from `Y`, and its identification with `Ω^•_{X/S}` and its
exhaustion come from `Stacks.DeRhamSmooth.deRhamSmoothFiltration_spec`. What is assumed is the
eventual vanishing `hvanish` of `R^nf_*` on the far steps of that filtration, and the
identification `hgr` of `R^{p+q}f_*gr^p` with the first page, which is the computation of the
graded pieces `gr^kΩ^•_{X/S} = f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` of Section 0FMK
followed by the projection formula of Tag 0FML. -/
@[stacks 0FMM "at the filtration of Section 0FMK, which is constructed rather than assumed; \
granted only hvanish, the eventual vanishing of R^nf_* on the far steps, and hgr, the graded \
pieces of Section 0FMK followed by the projection formula of Tag 0FML conclusions (4) and (5)"]
theorem exists_boundedDeRhamSpectralSequence_of_pullback
    [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (hvanish : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (higherDirectImage (derivedRelativePushforward f g)
        ((deRhamSmoothFiltration f g).filtration.obj (op p)) n))
    (hgr : ∀ p q : ℤ, Nonempty (higherDirectImage (derivedRelativePushforward f g)
      (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)) (p + q) ≅
        deRhamFirstPage f g p q)) :
    ∃ E : CohomologicalSpectralSequence
        (SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) 1,
      _root_.IsBounded E ∧
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ deRhamFirstPage f g p q)) ∧
      SpectralSequence.AbutsTo E (fun n => deRhamHigherDirectImage f g n) :=
  exists_boundedDeRhamSpectralSequence f g (deRhamSmoothFiltration f g) rfl
    (deRhamSmoothFiltration_spec f g).2.2.2 hvanish hgr

end Stacks.DeRhamSmooth

end
