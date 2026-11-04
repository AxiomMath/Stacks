module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.RelativeProj.LocalAtBase

/-!
# Relative dimension of a relative `Proj`

Relative dimension, in the sense of `AlgebraicGeometry.RelativeDimension`, is a condition on the
fibres of a morphism, and a fibre of the structure morphism of a relative `Proj` is a fibre of one
of its charts: a point `s` of the base lies in some affine open `U`, the chart over `U` is the
preimage of `U`, and the fibre over `s` is contained in that preimage. So the fibre of
`Stacks.RelativeProj.Data.toBase` over `s` is homeomorphic to the fibre of
`Stacks.RelativeProj.chartToOpen` over the corresponding point of `U`, and relative dimension
transfers from the charts to the structure morphism.

This is the third of the three geometric properties a projective bundle is asked to have — the
other two, being local at the target, are handled by
`Stacks.RelativeProj.Data.prop_toBase` — and it is the one that does not fit the
morphism-property machinery, because `AlgebraicGeometry.RelativeDimension` carries both a natural
number and a local-finite-type instance and so is not a `CategoryTheory.MorphismProperty`.

## Main results

* `Stacks.RelativeProj.Data.fiberHomeoChart`: the fibre of a chart over a point of its affine
  open is homeomorphic to the fibre of the structure morphism over the corresponding point of the
  base.
* `Stacks.RelativeProj.Data.relativeDimension_toBase`: the structure morphism of a relative `Proj`
  has relative dimension `e` as soon as every chart does.

## Implementation notes

The homeomorphism of fibres is built on the underlying topological spaces rather than as an
isomorphism of schemes, because that is all relative dimension sees and because it avoids the
pullback-of-residue-field manipulations an isomorphism of fibre schemes would need. Its two
inputs are `AlgebraicGeometry.Scheme.Hom.fiberHomeo`, which identifies the fibre with the
set-theoretic preimage of a point, and the two defining properties of the charts: the chart
morphism is a morphism over the base, so the preimage of a point of `U` in the chart is the
preimage of its image under the chart immersion; and the chart is the whole preimage of `U`, so
that preimage is reached.

The local-finite-type hypotheses are instance-implicit. They mention the `Data` and so cannot be
found by instance search, but `AlgebraicGeometry.RelativeDimension` takes one as an instance
argument, so a caller must supply them anyway; `Stacks.RelativeProj.Data.locallyOfFiniteType_toBase`
produces the one for `toBase`, and the chart ones follow from Mathlib's instance for
`AlgebraicGeometry.Proj.toSpecZero` through `Stacks.RelativeProj.prop_chartToOpen_iff`.

Homeomorphism invariance of equidimensionality is
`TopologicalSpace.Equidimensional.of_homeomorph`, taken from
`StacksFrontier/Topology/Dimension/Equidimensional.lean`, which is where equidimensionality is
defined.

No `@[stacks]` attribute is attached. Relative dimension of a projective bundle is one of the
assertions of tag 02TX, whose subject is the relative `Proj` of a symmetric algebra; this is the
reduction of that assertion to the charts, not the assertion.

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.RelativeProj.Data

variable {S : Scheme.{u}} {A σ : S.affineOpens → Type u} [∀ U, CommRing (A U)]
  [∀ U, SetLike (σ U) (A U)] [∀ U, AddSubgroupClass (σ U) (A U)]
  {𝒜 : ∀ U, ℕ → σ U} [∀ U, GradedRing (𝒜 U)] (d : Data 𝒜)

/-- The chart immersion is a morphism over the base, read on points. -/
theorem toBase_chartι_apply (U : S.affineOpens) (x : Proj (𝒜 U)) :
    d.toBase.base ((d.chartι U).base x) =
      (U : S.Opens).ι.base ((chartToOpen 𝒜 U (d.base U)).base x) :=
  congrArg (fun m : Proj (𝒜 U) ⟶ S ↦ m.base x) (d.chartι_toBase U)

/-- The charts cover the relative `Proj`, as an equality of sets: the image of the chart over `U`
is the preimage of `U`. -/
theorem range_chartι (U : S.affineOpens) :
    Set.range (d.chartι U).base = d.toBase.base ⁻¹' ((U : S.Opens) : Set S) := by
  rw [← Scheme.Hom.coe_opensRange, ← d.toBase_preimage_coe U]
  rfl

/-- The fibre of the chart over `U` at a point `s` of `U` is, through the chart immersion, the
fibre of the structure morphism at the image of `s` in the base. -/
theorem chartToOpen_preimage_singleton (U : S.affineOpens) (s : (U : S.Opens)) :
    (chartToOpen 𝒜 U (d.base U)).base ⁻¹' {s} =
      (d.chartι U).base ⁻¹' (d.toBase.base ⁻¹' {(U : S.Opens).ι.base s}) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, d.toBase_chartι_apply U x,
    Scheme.Opens.ι_apply]
  exact Subtype.ext_iff

/-- The image under the chart immersion of a fibre of the chart is the corresponding fibre of the
structure morphism: the fibre lies over a point of `U`, hence inside the chart. -/
theorem chartι_image_preimage_singleton (U : S.affineOpens) (s : (U : S.Opens)) :
    (d.chartι U).base '' ((chartToOpen 𝒜 U (d.base U)).base ⁻¹' {s}) =
      d.toBase.base ⁻¹' {(U : S.Opens).ι.base s} := by
  rw [d.chartToOpen_preimage_singleton U s, Set.image_preimage_eq_of_subset]
  rw [d.range_chartι U]
  intro z hz
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
  simp [hz]

/-- **The fibre of a chart is a fibre of the structure morphism.** The fibre of the chart over `U`
at `s : U` is homeomorphic to the fibre of the structure morphism of the relative `Proj` at the
image of `s` in the base. -/
def fiberHomeoChart (U : S.affineOpens) (s : (U : S.Opens)) :
    (chartToOpen 𝒜 U (d.base U)).fiber s ≃ₜ d.toBase.fiber ((U : S.Opens).ι.base s) :=
  let e₁ : (chartToOpen 𝒜 U (d.base U)).fiber s ≃ₜ
      ((chartToOpen 𝒜 U (d.base U)).base ⁻¹' {s} : Set (Proj (𝒜 U))) :=
    Scheme.Hom.fiberHomeo (chartToOpen 𝒜 U (d.base U)) s
  let e₂ : ((chartToOpen 𝒜 U (d.base U)).base ⁻¹' {s} : Set (Proj (𝒜 U))) ≃ₜ
      ((d.chartι U).base '' ((chartToOpen 𝒜 U (d.base U)).base ⁻¹' {s}) :
        Set d.relativeProj) :=
    (d.chartι U).isOpenEmbedding.isEmbedding.homeomorphImage _
  let e₃ : ((d.chartι U).base '' ((chartToOpen 𝒜 U (d.base U)).base ⁻¹' {s}) :
      Set d.relativeProj) ≃ₜ
      (d.toBase.base ⁻¹' {(U : S.Opens).ι.base s} : Set d.relativeProj) :=
    Homeomorph.setCongr (d.chartι_image_preimage_singleton U s)
  e₁.trans (e₂.trans (e₃.trans (Scheme.Hom.fiberHomeo d.toBase _).symm))

/-- **The structure morphism of a relative `Proj` has relative dimension `e` as soon as every
chart does.** Every point of the base lies in an affine open, and the fibre there is a fibre of
the corresponding chart. -/
theorem relativeDimension_toBase [LocallyOfFiniteType d.toBase]
    [∀ U : S.affineOpens, LocallyOfFiniteType (chartToOpen 𝒜 U (d.base U))] (e : ℕ)
    (h : ∀ U : S.affineOpens, RelativeDimension (chartToOpen 𝒜 U (d.base U)) e) :
    RelativeDimension d.toBase e := by
  intro y hy
  obtain ⟨U, hU⟩ : ∃ U : S.affineOpens, y ∈ (U : S.Opens) := by
    have : y ∈ (⊤ : S.Opens) := trivial
    rw [← iSup_affineOpens_eq_top S] at this
    exact Opens.mem_iSup.mp this
  set s : (U : S.Opens) := ⟨y, hU⟩ with hs
  have hiy : (U : S.Opens).ι.base s = y := rfl
  have E : (chartToOpen 𝒜 U (d.base U)).fiber s ≃ₜ d.toBase.fiber y :=
    hiy ▸ d.fiberHomeoChart U s
  obtain ⟨heq, hdim⟩ := h U s ⟨E.symm hy.some⟩
  refine ⟨heq.of_homeomorph E.symm, ?_⟩
  rw [← IsHomeomorph.topologicalKrullDim_eq _ E.isHomeomorph]
  exact hdim

end Stacks.RelativeProj.Data

end
