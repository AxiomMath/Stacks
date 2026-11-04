module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.CechSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.CechRows
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.Abutment

/-!
# The relative Čech-to-cohomology spectral sequence for sheaves of modules

For a faithful 1-morphism `f : 𝒰 ⥤ 𝒳` of categories fibred in groupoids over the big fppf
category of a scheme `S`, with equalizers in `𝒰` and whose image covers `𝒳` locally in the
`τ`-topology, every sheaf of `𝒪_𝒳`-modules `𝓕` carries a first-quadrant spectral sequence of
`Γ(𝒪_𝒳)`-modules
`E₁^{i,j} = Hʲ((𝒰ᵢ)_τ, fᵢ^*𝓕) ⇒ Hⁱ⁺ʲ(𝒳_τ, 𝓕)`,
where `𝒰ᵢ` is the degree-`i` term of the relative Čech nerve of `f` and the scalars on the first
page are restricted along `Γ(𝒪_𝒳) → Γ(𝒪_{𝒰ᵢ})`.

The construction is the sections double complex of the relative Čech nerve applied to an
injective resolution of `𝓕`: its columns compute the cohomology of the inverse images on the
terms of the nerve, and its rows are acyclic because the relative Čech complex of an injective
sheaf of modules is an injective resolution.

## Main definitions

* `Stacks.RelativeCech.tupleModuleCohomology`: the first-page term `Hʲ((𝒰ᵢ)_τ, fᵢ^*𝓕)`, as a
  `Γ(𝒪_𝒳)`-module.
* `Stacks.RelativeCech.ModuleSpectralSequenceData`: the spectral sequence together with its first
  page, its first-quadrant vanishing and its abutment.

## Main results

* `Stacks.RelativeCech.exists_moduleSpectralSequenceData`: the spectral sequence exists.

## References

* [Stacks Project, Tag 06XG](https://stacks.math.columbia.edu/tag/06XG)
-/
