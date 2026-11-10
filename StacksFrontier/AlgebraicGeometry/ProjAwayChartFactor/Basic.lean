module

public import StacksFrontier.AlgebraicGeometry.ProjF1DegreeOneChart.Basic

/-!
# Factoring the chart bijection of `Proj` through `Spec` of the `Away` ring

`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv` is the bijection, for `r` a
homogeneous element of positive degree of a graded ring `𝒜`, between the morphisms
`Y ⟶ Proj 𝒜` landing in `D₊(r)` and the ring homomorphisms out of
`HomogeneousLocalization.Away 𝒜 r`. It is assembled from three equivalences, and nothing so far
says what its inverse *is*.

This file says it: the morphism attached to a ring homomorphism `ρ` is
`Y.toSpecΓ ≫ Spec.map ρ ≫ awayι 𝒜 r`, where `AlgebraicGeometry.Proj.awayι` is Mathlib's open
immersion `Spec (𝒜_r)₀ ⟶ Proj 𝒜`. Everything Mathlib knows about `awayι` — the preimages of the
basic opens of `Proj` (`AlgebraicGeometry.Proj.awayι_preimage_basicOpen`) and the compatibility
with the transition maps `(𝒜_r)₀ → (𝒜_{rs})₀` (`AlgebraicGeometry.Proj.SpecMap_awayMap_awayι`) —
becomes usable for a morphism produced by `chartHomEquiv` only through this identification.

## Main results

* `Stacks.AlgebraicGeometry.ProjAwayChartFactor.specHomEquiv_symm`: the `Γ`–`Spec` bijection of
  `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.specHomEquiv`, read backwards, is composition
  with the unit `Y ⟶ Spec Γ(Y, ⊤)`.
* `Stacks.AlgebraicGeometry.ProjAwayChartFactor.chartHomEquiv_symm_val`: **the inverse of the
  chart bijection, computed.** `(chartHomEquiv 𝒜 hr hd Y).symm ρ` is
  `Y.toSpecΓ ≫ Spec.map ρ ≫ awayι 𝒜 r`.
* `Stacks.AlgebraicGeometry.ProjAwayChartFactor.awayι_congr`: `awayι` does not depend on the
  degree in which the element is presented. The degree enters only through two propositions, and
  `AlgebraicGeometry.Proj.SpecMap_awayMap_awayι` returns the degree `d + e` on one side of a
  product and `e + d` on the other, so the two spellings have to be identified once.

## References

* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)

## What is not done

No `@[stacks]` attribute is attached: this is a computation of an existing bijection, not the
statement of a tag.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjAwayChartFactor

universe u w

variable {Y : Scheme.{u}} {σ : Type w} {R : Type u} [CommRing R] [SetLike σ R]
  [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {r : R} {d : ℕ}

/-- **`AlgebraicGeometry.Proj.awayι` does not depend on the degree.** The degree of `r` occurs in
`awayι 𝒜 r hr hd` only inside the two propositions `hr` and `hd`, so the two presentations are
the same morphism. -/
public theorem awayι_congr {d' : ℕ} (hr : r ∈ 𝒜 d) (hd : 0 < d) (hr' : r ∈ 𝒜 d')
    (hd' : 0 < d') :
    Proj.awayι 𝒜 r hr hd = Proj.awayι 𝒜 r hr' hd' := rfl

/-- **Morphisms to an affine scheme, read backwards.** The morphism attached to a ring
homomorphism out of `Γ(Spec R, ⊤)` is the composite of the unit of the `Γ`–`Spec` adjunction with
`Spec` of that homomorphism. -/
public theorem specHomEquiv_symm (R : CommRingCat.{u}) (Y : Scheme.{u}) (ρ : R ⟶ Γ(Y, ⊤)) :
    (ProjF1DegreeOneChart.specHomEquiv R Y).symm ρ = Y.toSpecΓ ≫ Spec.map ρ :=
  Scheme.Hom.ext' rfl

/-- **The inverse of the chart bijection of `Proj` at `r`, computed.** The morphism attached to a
ring homomorphism `ρ` out of `HomogeneousLocalization.Away 𝒜 r` is the composite of the unit
`Y ⟶ Spec Γ(Y, ⊤)`, of `Spec ρ`, and of Mathlib's open immersion
`AlgebraicGeometry.Proj.awayι`. -/
public theorem chartHomEquiv_symm_val (hr : r ∈ 𝒜 d) (hd : 0 < d)
    (ρ : CommRingCat.of (HomogeneousLocalization.Away 𝒜 r) ⟶ Γ(Y, ⊤)) :
    ((ProjF1DegreeOneChart.chartHomEquiv 𝒜 hr hd Y).symm ρ).1
      = Y.toSpecΓ ≫ Spec.map ρ ≫ Proj.awayι 𝒜 r hr hd := by
  change ((Iso.refl Y).hom ≫ (ProjF1DegreeOneChart.specHomEquiv _ Y).symm ρ ≫
    (Proj.basicOpenIsoSpec 𝒜 r hr hd).inv) ≫ (Proj.basicOpen 𝒜 r).ι = _
  rw [Iso.refl_hom, Category.id_comp, specHomEquiv_symm, Category.assoc, Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι]

end Stacks.AlgebraicGeometry.ProjAwayChartFactor

end
