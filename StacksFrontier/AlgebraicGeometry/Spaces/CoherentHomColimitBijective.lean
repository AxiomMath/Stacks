module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartDescent

/-!
# Stacks 07UM: the canonical maps are bijective

Let `X` be a Noetherian algebraic space over a scheme `S`, let `ℐ ⊆ 𝒪_X` be a quasi-coherent
sheaf of ideals, let `U = X ∖ V(ℐ)` be its open complement, let `𝒢` be a coherent `𝒪_X`-module and
let `ℱ` be a quasi-coherent `𝒪_X`-module.  This file assembles the two clauses of
[Stacks, Tag 07UM] for the first display: the canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)`

is **bijective**.

Injectivity is `AlgebraicGeometry.Space.canonicalMapToHomRestrict_injective` and surjectivity
is `AlgebraicGeometry.Space.canonicalMapToHomRestrict_surjective`.

It also proves the tag's "in particular" display, which is the first display at `𝒢 = 𝒪_X`: the
canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ, ℱ) ⟶ Γ(U, ℱ|_U)`

is **bijective**.  The structure sheaf of a Noetherian algebraic space is coherent by the
structure-sheaf clause of [Stacks, Tag 07UB], so the first display applies at `𝒢 = 𝒪_X`; and a
morphism out of the unit object is a section, by the bijection `SheafOfModules.unitHomEquiv`
through which `AlgebraicGeometry.Space.canonicalMapToSections` is defined.  No comparison between
`𝒪_X|_U` and `𝒪_U` is needed: they are equal, by
`AlgebraicGeometry.Space.restrictToIdealComplement_unit_eq`.

## Main results

* `AlgebraicGeometry.Space.canonicalMapToHomRestrict_bijective`: **[Stacks, Tag 07UM], first
  display.**
* `AlgebraicGeometry.Space.canonicalMapToSections_bijective`: **[Stacks, Tag 07UM], the "in
  particular" display.**

## Implementation notes

**The hypotheses are the tag's and no others.**  That `ℐ` is cartesian on affine charts, which
the surjectivity argument on charts uses, is Descent, Proposition 03DX (2) for quasi-coherent
`ℐ` — `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`; and
quasi-coherence of `ℐⁿ𝒢`, which the chart transport needs, is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowModule`, which derives it from coherence of
`𝒢` through `AlgebraicGeometry.Space.isCoherent_idealPowModule_of_isQuasicoherentOnSite`.  So
neither is a hypothesis of the statements below.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)

/-- **[Stacks, Tag 07UM], first display.**  For a Noetherian algebraic space `X` over `S`, a
quasi-coherent sheaf of ideals `ℐ` with open complement `U = X ∖ V(ℐ)`, a coherent `𝒪_X`-module
`𝒢` and a quasi-coherent `𝒪_X`-module `ℱ`, the canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)`

is bijective.

Injectivity is `AlgebraicGeometry.Space.canonicalMapToHomRestrict_injective`: a morphism
`φ : ℐⁿ𝒢 ⟶ ℱ` vanishing on `U` has coherent image supported in `V(ℐ)`, so some power of `ℐ`
annihilates that image and `φ` dies on a deeper step of the filtration.  Surjectivity is
`AlgebraicGeometry.Space.canonicalMapToHomRestrict_surjective`: a morphism `𝒢|_U ⟶ ℱ|_U` is
transported to a surjective Noetherian affine chart, extended there by the first display of
[Stacks, Tag 01YB] on the chart's scheme, made compatible on the kernel pair by raising the
exponent of the ideal, and glued. -/
@[stacks 07UM "first display"]
theorem canonicalMapToHomRestrict_bijective (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (G F : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G)
    [F.IsQuasicoherentOnSite] :
    Function.Bijective (canonicalMapToHomRestrict B S hS X I G F) :=
  ⟨canonicalMapToHomRestrict_injective B S hS X I hZ hN hI G F hG,
    canonicalMapToHomRestrict_surjective B S hS X I
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 I.toSheafOfModules hI)
      G F hZ hN hI ‹F.IsQuasicoherentOnSite› hG⟩

/-- **[Stacks, Tag 07UM], the "in particular" display.**  For a Noetherian algebraic space `X`
over `S`, a quasi-coherent sheaf of ideals `ℐ` with open complement `U = X ∖ V(ℐ)` and a
quasi-coherent `𝒪_X`-module `ℱ`, the canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ, ℱ) ⟶ Γ(U, ℱ|_U)`

is bijective.

This is `AlgebraicGeometry.Space.canonicalMapToHomRestrict_bijective` at `𝒢 = 𝒪_X`, which is
legitimate because the structure sheaf of a Noetherian algebraic space is coherent
(`AlgebraicGeometry.Space.isCoherent_structureSheaf`, the structure-sheaf clause of
[Stacks, Tag 07UB]), composed with the bijection `SheafOfModules.unitHomEquiv` identifying the
morphisms `𝒪_U ⟶ ℱ|_U` with the sections of `ℱ|_U`.  Noetherian implies the étale-local
Noetherian property that the coherence of the structure sheaf asks for, which is `hN.2.2`. -/
@[stacks 07UM "the in particular display"]
theorem canonicalMapToSections_bijective (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] :
    Function.Bijective (canonicalMapToSections B S hS X I F) := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  exact (SheafOfModules.unitHomEquiv _).bijective.comp
    (canonicalMapToHomRestrict_bijective B S hS X I hZ hN hI
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) F
      (isCoherent_structureSheaf B S hS X.1 X.2))

end AlgebraicGeometry.Space

end
