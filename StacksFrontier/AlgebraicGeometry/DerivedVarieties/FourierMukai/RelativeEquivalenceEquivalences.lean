module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelIdentity
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.PerfectPreservationCriteria
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionFormulaDischarged
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceIsEquivalence

/-!
# The Fourier-Mukai functors of a relative equivalence are equivalences, with no inputs left open

Let `S` be a scheme, let `f : X ⟶ S` and `g : Y ⟶ S` be smooth and proper, and let `K` be the
Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over `S` in the sense of
[Stacks, Tag 0G0I] (`AlgebraicGeometry.IsRelativeEquivalenceKernel`). Then both Fourier-Mukai
functors attached to `K`,

`Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0FYR] and
`Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` of [Stacks, Tag 0FYT],

are equivalences. This is [Stacks, Tag 0G0J], under exactly the source's hypotheses.

## Main results

* `AlgebraicGeometry.isEquivalence_quasiCoherentFourierMukai_of_isRelativeEquivalenceKernel` —
  **[Stacks, Tag 0G0J]**, the clause for `D_QCoh`.
* `AlgebraicGeometry.fourierMukaiPreservesPerfect` — clause (3) of [Stacks, Tag 0FYT] in the
  shape of `AlgebraicGeometry.FourierMukaiPreservesPerfect`.
* `AlgebraicGeometry.isEquivalence_perfectFourierMukai_of_isRelativeEquivalenceKernel` —
  **[Stacks, Tag 0G0J]**, the clause for `D_perf`.

## Implementation notes

The argument is the source's ("immediate from [Stacks, Tag 0FYS] and [Stacks, Tag 0FYV]") and
is carried out in the module
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceIsEquivalence`
as `AlgebraicGeometry.isEquivalence_quasiCoherentFourierMukai` and
`AlgebraicGeometry.isEquivalence_perfectFourierMukai`. Those two theorems take exactly the
source's hypotheses and assume nothing further: the four auxiliary Stacks results their proof
needs — [Stacks, Tag 08IB], [Stacks, Tag 08EU], the closing assertion of [Stacks, Tag 0FYV] and
clause (3) of [Stacks, Tag 0FYT] — are theorems of this library
(`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`,
`AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`,
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso` and
`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`)
and are used there directly. Nothing is left for this module to supply, so the two results of
this module under the longer names are `alias`es of those two theorems.

What this module still adds is the two propositions of
`RelativeEquivalenceIsEquivalence.lean` in their variable-free shape:

* `AlgebraicGeometry.DiagonalFourierMukaiIsIdentity` is the closing assertion of
  [Stacks, Tag 0FYV], that `Φ_{𝒪_Δ} ≅ 𝟭` for a separated `f`; it is proved here, from
  `AlgebraicGeometry.fourierMukaiDiagonalKernelIso`, as
  `AlgebraicGeometry.diagonalFourierMukaiIsIdentity`;
* `AlgebraicGeometry.FourierMukaiPreservesPerfect` is clause (3) of [Stacks, Tag 0FYT]; it is
  proved here, from
  `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`,
  as `AlgebraicGeometry.fourierMukaiPreservesPerfect`.

## References

* [Stacks Project, Tag 0G0J](https://stacks.math.columbia.edu/tag/0G0J)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0FYR](https://stacks.math.columbia.edu/tag/0FYR)
* [Stacks Project, Tag 0FYT](https://stacks.math.columbia.edu/tag/0FYT)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, the one the Fourier-Mukai
-- functor and the diagonal kernel are read at, over the locally small model arriving with the
-- imports.
attribute [local instance 100000] HasDerivedCategory.standard

/-- **The closing assertion of [Stacks, Tag 0FYV], in the shape of
`AlgebraicGeometry.DiagonalFourierMukaiIsIdentity`**: for every separated morphism of schemes
`f : X ⟶ S`, the Fourier-Mukai functor of the diagonal kernel `𝒪_Δ` is isomorphic to the
identity functor of `D(𝒪_X)`. This is `AlgebraicGeometry.fourierMukaiDiagonalKernelIso`. -/
theorem diagonalFourierMukaiIsIdentity : DiagonalFourierMukaiIsIdentity.{u} := by
  intro S X f hf
  have := hf
  exact ⟨fourierMukaiDiagonalKernelIso f⟩

/-- **Clause (3) of [Stacks, Tag 0FYT], in the shape of
`AlgebraicGeometry.FourierMukaiPreservesPerfect`**: for `X ⟶ S` proper, flat and of finite
presentation and `K` perfect, `Φ_K` carries perfect objects to perfect objects. This is
`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`. -/
theorem fourierMukaiPreservesPerfect : FourierMukaiPreservesPerfect.{u} := by
  intro S X Y f g hp hf hl K hK M hM
  have := hp
  have := hf
  have := hl
  exact isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation f g K hK M hM

/-- **[Stacks, Tag 0G0J], the clause for `D_QCoh`.** Let `S` be a scheme, let `f : X ⟶ S` and
`g : Y ⟶ S` be smooth and proper, and let `K` be the Fourier-Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, [Stacks, Tag 0G0I]. Then the Fourier-Mukai functor
`Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0FYR] is an equivalence.

Its inverse is `Φ_{K'}` for the kernel `K'` that the definition of a relative equivalence
supplies: by [Stacks, Tag 0FYS] the two composites are the Fourier-Mukai functors of the two
convolutions, which the definition identifies with the diagonal kernels, whose Fourier-Mukai
functors are the identities by [Stacks, Tag 0FYV]. This is another name for
`AlgebraicGeometry.isEquivalence_quasiCoherentFourierMukai`. -/
@[stacks 0G0J "Phi_K : D_QCoh(O_X) -> D_QCoh(O_Y) is an equivalence"]
public alias isEquivalence_quasiCoherentFourierMukai_of_isRelativeEquivalenceKernel :=
  isEquivalence_quasiCoherentFourierMukai

/-- **[Stacks, Tag 0G0J], the clause for `D_perf`.** Let `S` be a scheme, let `f : X ⟶ S` and
`g : Y ⟶ S` be smooth and proper, and let `K` be the Fourier-Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, [Stacks, Tag 0G0I]. Then the Fourier-Mukai functor
`Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` of [Stacks, Tag 0FYT] is an equivalence.

The functor exists by clause (3) of [Stacks, Tag 0FYT], `f` being proper, flat and of finite
presentation and `K` perfect. Its inverse is `Φ_{K'}`, as in the `D_QCoh` clause
`AlgebraicGeometry.isEquivalence_quasiCoherentFourierMukai_of_isRelativeEquivalenceKernel`,
whose two composite isomorphisms restrict to `D_perf(𝒪_X) ⊆ D_QCoh(𝒪_X)`. This is another name
for `AlgebraicGeometry.isEquivalence_perfectFourierMukai`. -/
@[stacks 0G0J "Phi_K : D_perf(O_X) -> D_perf(O_Y) is an equivalence"]
public alias isEquivalence_perfectFourierMukai_of_isRelativeEquivalenceKernel :=
  isEquivalence_perfectFourierMukai

end AlgebraicGeometry

end
