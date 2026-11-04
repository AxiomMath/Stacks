module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistClauseOne
public import StacksFrontier.AlgebraicGeometry.ProjTwistGradedAlgebra.Basic

/-!
# Clause (1) of Tag 02NC: the comparison maps fitting together

Let `R` be a commutative ring, `𝒜` a graded `R`-algebra, `𝓛` a family of tensor powers of an
invertible `R`-module `ℒ = 𝓛 1` inside a commutative ring `T`, and `ℬ` the twist of `𝒜` by `𝓛`,
so that `ℬ d` is `𝒜 d ⊗_R 𝓛 d`. Clause (1) of
[Stacks, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC) asks for two things: that the
comparison maps `θ_n` on the `n`-th twisting sheaves are isomorphisms, and that they *fit
together to give an isomorphism of `ℤ`-graded algebras*

`θ : g^*(⨁_{n ∈ ℤ} 𝒪_{P'}(n)) ⟶ ⨁_{n ∈ ℤ} 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`.

`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwist.lean` and
`ProjInvertibleTwistClauseOne.lean` prove the first half, as
`Stacks.GradedRing.InvertibleTwist.isIso_twistMap` and `isIso_twistMap_twistHomOf`: one
invertible morphism of sheaves of modules per integer `n`, and nothing tying the family
together. **This file proves the second half**: the family is one isomorphism in the category of
sheaves of `ℤ`-graded algebras of [Stacks, Tag 0FQW].

## Main definitions

* `Stacks.GradedRing.InvertibleTwist.thetaGradedIso`: **the graded assembly of clause (1), for a
  twisting module with a global generator.**
* `Stacks.GradedRing.InvertibleTwist.thetaGradedIsoOf`: **the graded assembly of clause (1) for
  an arbitrary degree-one element `ℓ`**, on the domain of definition `U(ψ_ℓ) ⊆ Proj ℬ` of the
  comparison attached to `ℓ`.

## How the tag's two sides are spelled here

The tag's `⨁_{n ∈ ℤ} 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` is read through the identification `ℬ_n = 𝒜_n ⊗ ℒ^n`
of the setting: the twisted graded ring `ℬ` is the one whose twisting sheaves *are* the tensor
products the tag writes out, so the tag's target is the algebra of integer twists of `Proj ℬ`,
pulled back to `U(ψ)`. The two spectra are identified by
`Stacks.GradedRing.InvertibleTwist.projTwistIso` (with a global generator) and
`projTwistIsoGeneral` (in general), and the comparison homomorphism `ψ_ℓ : 𝒜 →+*ᵍ ℬ` induces
`r_{ψ_ℓ} : U(ψ_ℓ) ⟶ Proj 𝒜`, which is the tag's `g` read in the direction this library's
comparison on twists runs: `θ` has source the pullback along `r_{ψ_ℓ}` of the twists of
`Proj 𝒜` and target the twists of `Proj ℬ`. Each `θ_n` being invertible, the two readings carry
the same data.

For a twisting module with a global generator `U(ψ)` is the whole of `Proj ℬ`
(`Stacks.GradedRing.InvertibleTwist.mapDomain_twistHom_eq_top`), so `thetaGradedIso` is a
statement about the two homogeneous spectra themselves; without one the opens `U(ψ_ℓ)` cover
`Proj ℬ` (`iSup_mapDomain_twistHomOf_eq_top`), so `thetaGradedIsoOf` is a statement about the
whole of `Proj ℬ` read on a cover.

## What is not proved here

The unit is not addressed. `SheafOfModules.GradedAlgebra.Hom` does not require preservation of
the distinguished degree-zero unit, and the category of sheaves of graded algebras is formed on
`Hom`, so an isomorphism in that category — which is what the tag's "isomorphism of `ℤ`-graded
algebras" is read as — does not carry it. The unit clause is available at the level of
morphisms, as `Stacks.AlgebraicGeometry.ProjMapCardUnit.projMapData_preserves_unit`, and is not
folded into a `SheafOfModules.GradedAlgebra.UnitalHom` here.

The relative case over a base scheme is not treated: everything here is over `Spec R`.

## References

* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry DirectSum Graded HomogeneousIdeal
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra (pullbackTwistAlgebra)
open scoped TensorProduct

namespace Stacks.GradedRing.InvertibleTwist

attribute [local instance] ProjectiveSpectrum.isPrime

variable {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T]
  {𝒜 : ℕ → Submodule R A} [_root_.GradedAlgebra 𝒜] {𝓛 : ℕ → Submodule R T}
  {ℬ : ℕ → Submodule R B} [_root_.GradedAlgebra ℬ] (tw : InvertibleTwist 𝒜 𝓛 ℬ)
  (h𝓛 : IsTensorPowerFamily 𝓛)

/-! ### The graded assembly, for a twisting module with a global generator -/

section Generator

variable {ℓ : T} {hℓ : ℓ ∈ 𝓛 1}
  (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩))

include tw h𝓛 hgen

/-- **Clause (1) of Stacks Tag 02NC, the graded assembly, for a twisting module with a global
generator.** The comparison maps `θ_n` on the individual twisting sheaves fit together into a
single isomorphism of sheaves of `ℤ`-graded algebras

`θ : r_ψ^*(⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n)) ≅ ⨁_{n ∈ ℤ} 𝒪_{Proj ℬ}(n)|_{U(ψ)}`,

whose degree-`n` component is the comparison map of
`Stacks.GradedRing.InvertibleTwist.isIso_twistMap`. The open `U(ψ)` is the whole of `Proj ℬ`, by
`Stacks.GradedRing.InvertibleTwist.mapDomain_twistHom_eq_top`.

Multiplicativity of the assembled map is the Tag 01MY clause
`Stacks.AlgebraicGeometry.ProjMapCard.twistMap_comp_pullbackTwistMultiplication`, read on a
local pure tensor; invertibility of the assembled map is invertibility of each component. -/
def thetaGradedIso :
    pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ (tw.twistHom h𝓛 hgen)) ≅
      pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ (tw.twistHom h𝓛 hgen)).ι :=
  Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.thetaGradedIso 𝒜 ℬ (tw.twistHom h𝓛 hgen)
    (tw.isIso_twistMap h𝓛 hgen)

/-- The degree-`n` component of the graded assembly is the comparison map on the `n`-th twist. -/
theorem thetaGradedIso_hom_app (n : ℤ) :
    (tw.thetaGradedIso h𝓛 hgen).hom.app n = twistMap 𝒜 ℬ (tw.twistHom h𝓛 hgen) n := rfl

end Generator

/-! ### The graded assembly without a global generator -/

section NoGenerator

variable [Module.Invertible R ↥(𝓛 1)] {ℓ : T}

include tw h𝓛

/-- **Clause (1) of Stacks Tag 02NC, the graded assembly, with no global generator of the
twisting module.** For *every* degree-one element `ℓ ∈ 𝓛 1` the comparison maps `θ_n` attached
to `ψ_ℓ` fit together into a single isomorphism of sheaves of `ℤ`-graded algebras

`θ : r_{ψ_ℓ}^*(⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n)) ≅ ⨁_{n ∈ ℤ} 𝒪_{Proj ℬ}(n)|_{U(ψ_ℓ)}`

over the domain of definition `U(ψ_ℓ) ⊆ Proj ℬ`, whose degree-`n` component is the comparison
map of `Stacks.GradedRing.InvertibleTwist.isIso_twistMap_twistHomOf`. The opens `U(ψ_ℓ)` cover
`Proj ℬ` as `ℓ` ranges over `𝓛 1`, by
`Stacks.GradedRing.InvertibleTwist.iSup_mapDomain_twistHomOf_eq_top`, so this is a statement
about the whole of `Proj ℬ` read on a cover. -/
def thetaGradedIsoOf (hℓ : ℓ ∈ 𝓛 1) :
    pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)) ≅
      pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι :=
  Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.thetaGradedIso 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)
    (tw.isIso_twistMap_twistHomOf h𝓛 hℓ)

/-- The degree-`n` component of the generator-free graded assembly is the comparison map on the
`n`-th twist attached to `ℓ`. -/
theorem thetaGradedIsoOf_hom_app (hℓ : ℓ ∈ 𝓛 1) (n : ℤ) :
    (tw.thetaGradedIsoOf h𝓛 hℓ).hom.app n = twistMap 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) n := rfl

end NoGenerator

end Stacks.GradedRing.InvertibleTwist

end
