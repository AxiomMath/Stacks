module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Clause
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.SectionDictionary

/-!
# The charts of the degree-one coordinates of Stacks Tag 02NP

`StacksFrontier/AlgebraicGeometry/VeryAmpleAffineBase/SectionDictionary.lean` identifies the
coordinate ratio `s_k / s_i` of the family of sections attached to degree-one elements
`y_0, …, y_n` of a graded ring `A` with the inverse image along `α : X ⟶ Proj A` of the
degree-zero fraction `y_k / y_i`, over any open inside **both** `α⁻¹(D₊(y_i))` and the
nonvanishing open `X_{s_i}`. This file removes the second of those two hypotheses: for a graded
ring generated in degree one over its degree-zero part,

> `α⁻¹(D₊(y)) ≤ X_{α⁎y}`,

so an open inside the first is inside the second automatically. Consequently the charts of the
chosen coordinates *are* the opens `α⁻¹(D₊(y_i))` that
`Stacks.CoordinateChoice.exists_mem_preimage_basicOpen_of_mem_adjoin` proves cover `X`, and the
family of sections generates every stalk.

## Both inclusions

The opposite inclusion is needed as well: the coordinate cut also has to read an open of the chart
`X_{s_i}` as an open of `α⁻¹(D₊(y_i))`, because the inverse image along the pinned morphism
`p : X ⟶ ℙⁿ_S` of a standard open of `D₊(T_i)` is computed inside `X_{s_i}`
(`Stacks.AmpleImmersionReduction.preimage_standardChart`) while the fraction dictionary produces
its sections over `α⁻¹(D₊(y_i))`. So the equality is proved here, as
`Stacks.CoordinateDictionary.preimage_basicOpen_eq_nvCover`; the extra ingredient is
[Stacks, Tag 01MV] in its sharp form, an *iff* rather than an implication, which
`Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'` already
supplies.

## Main results

* `Stacks.CoordinateDictionary.mem_nonvanishingLocus_coordSection`: **the inclusion**, pointwise
  on `α⁎𝒪(1)`, and
  `Stacks.CoordinateDictionary.mem_nonvanishingLocus_coordSection_iff`: **the equality**, in the
  same pointwise form. That [Stacks, Tag 01MV] is available at every point is
  `Stacks.AlgebraicGeometry.ProjTwistPowers.whereInvertible_one_eq_top`, which is proved and is
  not restated here.
* `Stacks.CoordinateDictionary.preimage_basicOpen_le_nvCover`: the inclusion transported along an
  isomorphism `α⁎𝒪(1) ≅ L`, as an inequality of opens of `X`, and
  `Stacks.CoordinateDictionary.preimage_basicOpen_eq_nvCover`: **the chart of a degree-one
  coordinate is the inverse image of its standard open**, the same transported equality.
* `Stacks.CoordinateDictionary.generatesStalks_coordFamily`: **the family of sections attached to
  the coordinates generates `L`** as soon as the opens `α⁻¹(D₊(y_i))` cover `X` — which is the
  generation clause of `Stacks.VeryAmpleAffineBase.ProjCoordinateImmersion` at the source's
  coordinates.
* `Stacks.CoordinateDictionary.resO_ratio_eq_pullbackAwayCoord_of_le_preimage`: **the dictionary
  with one hypothesis**, the form the coordinate cut consumes.

## References

* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.ProjectiveFromSections
open Stacks.TwistPullbackRatio (O1)

universe u w

namespace Stacks.CoordinateDictionary

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (α : X ⟶ AlgebraicGeometry.Proj 𝒜)

/-! ### The preimage of a standard open lies in the chart -/

/-- **A point whose image lies in `D₊(y)` lies in the nonvanishing locus of `α⁎y`.** This is
[Stacks, Tag 01MV] — the degree-one section of `y` is nonvanishing on `D₊(y)`, available at every
point because the invertible locus of degree one is everything — followed by [Stacks, Tag 0H78]
for the pullback. -/
theorem mem_nonvanishingLocus_coordSection
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) (y : 𝒜 1) {x : X}
    (hx : α.base x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (y : A)) :
    x ∈ Stacks.Ample.nonvanishingLocus (pullbackTwistOne 𝒜 α) (coordSection 𝒜 α y) :=
  mem_nonvanishingLocus_pullbackSectionHom α (O1 𝒜) (by simp) (degreeSection 𝒜 1 y)
    (mem_nonvanishingLocus_degreeSection 𝒜 (one_mul 1).symm y
      ((Stacks.AlgebraicGeometry.ProjTwistPowers.whereInvertible_one_eq_top 𝒜 hgen).ge trivial)
      hx)

/-- **The nonvanishing locus of `α⁎y` is exactly the inverse image of `D₊(y)`**, for `y`
homogeneous of degree one in a graded ring generated in degree one over its degree-zero part.

This is [Stacks, Tag 0H78] — the nonvanishing locus of an inverse image is the inverse image of
the nonvanishing locus — composed with [Stacks, Tag 01MV] in the sharp form
`Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'`, whose
hypothesis is that the point lies in the invertible locus of degree one; that locus is everything
by `Stacks.AlgebraicGeometry.ProjTwistPowers.whereInvertible_one_eq_top`. -/
theorem mem_nonvanishingLocus_coordSection_iff
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) (y : 𝒜 1) {x : X} :
    x ∈ Stacks.Ample.nonvanishingLocus (pullbackTwistOne 𝒜 α) (coordSection 𝒜 α y) ↔
      α.base x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (y : A) := by
  have hsec : coordSection 𝒜 α y =
      Stacks.NonvanishingPullback.pullbackGlobalSection α (O1 𝒜) (degreeSection 𝒜 1 y) := by
    change ((Scheme.Modules.pullback α).obj (O1 𝒜)).presheaf.map
        (eqToHom (show α ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) = ⊤ from rfl)).op
        (Stacks.NonvanishingPullback.pullbackGlobalSection α (O1 𝒜)
          (degreeSection 𝒜 1 y)) = _
    exact Functor.map_id_apply _ _ _
  rw [hsec]
  refine (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff α (O1 𝒜)
    (degreeSection 𝒜 1 y) x).trans ?_
  exact Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒜 1 1 y ((Stacks.AlgebraicGeometry.ProjTwistPowers.whereInvertible_one_eq_top 𝒜 hgen).ge
      trivial)

section Family

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- A point lies in the chart `X_{s_i}` iff its image lies in `D₊(y_i)`. -/
private theorem mem_nvCover_iff_base_mem_basicOpen
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    (e : pullbackTwistOne 𝒜 α ≅ L) {ι : Type*} (y : ι → 𝒜 1) (s : ι → Γ(L, ⊤))
    (hs : ∀ i, s i = e.hom.app ⊤ (coordSection 𝒜 α (y i))) (i : ι) {x : X} :
    x ∈ nvCover s i ↔ α.base x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (y i : A) := by
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, hs i,
    Stacks.Ample.nonvanishingLocus_congr e (coordSection 𝒜 α (y i)),
    mem_nonvanishingLocus_coordSection_iff 𝒜 α hgen (y i)]

/-- **The preimage of the standard open of a coordinate lies in that coordinate's chart.** The
sections `s i` of `L` are the images under an isomorphism `α⁎𝒪(1) ≅ L` of the sections attached
to the degree-one elements `y i`, and transporting a section along an isomorphism of modules does
not change its nonvanishing locus. -/
theorem preimage_basicOpen_le_nvCover (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    (e : pullbackTwistOne 𝒜 α ≅ L) {ι : Type*} (y : ι → 𝒜 1) (s : ι → Γ(L, ⊤))
    (hs : ∀ i, s i = e.hom.app ⊤ (coordSection 𝒜 α (y i))) (i : ι) :
    α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 ((y i : A)) ≤ nvCover s i :=
  fun _ hx => (mem_nvCover_iff_base_mem_basicOpen 𝒜 α hgen e y s hs i).2 hx

/-- **The family of sections attached to the chosen coordinates generates `L`**, as soon as the
preimages `α⁻¹(D₊(y_i))` cover `X`. That covering statement is
`Stacks.CoordinateChoice.exists_mem_preimage_basicOpen_of_mem_adjoin` at the source's choice of
coordinates, so this is the generation clause of
`Stacks.VeryAmpleAffineBase.ProjCoordinateImmersion` there. -/
theorem generatesStalks_coordFamily (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    (e : pullbackTwistOne 𝒜 α ≅ L) {ι : Type*} (y : ι → 𝒜 1) (s : ι → Γ(L, ⊤))
    (hs : ∀ i, s i = e.hom.app ⊤ (coordSection 𝒜 α (y i)))
    (hcov : ∀ x : X, ∃ i, x ∈ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 ((y i : A))) :
    GeneratesStalks s :=
  Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem s fun x =>
    (hcov x).elim fun i hi =>
      ⟨i, preimage_basicOpen_le_nvCover 𝒜 α hgen e y s hs i hi⟩

/-- **The chart of a degree-one coordinate is the inverse image of its standard open.** The
inclusion `Stacks.CoordinateDictionary.preimage_basicOpen_le_nvCover` is an equality: the
nonvanishing locus of `α⁎y` is exactly `α⁻¹(D₊(y))`, by
`Stacks.CoordinateDictionary.mem_nonvanishingLocus_coordSection_iff`.

This is what lets the coordinate cut of [Stacks, Tag 02NP] read an open of the chart `X_{s_i}`
as an open of `α⁻¹(D₊(y_i))` and back: the inverse image along the pinned morphism of a standard
open of `D₊(T_i)` is computed inside `X_{s_i}`, while the fraction dictionary produces its
sections over `α⁻¹(D₊(y_i))`. -/
theorem preimage_basicOpen_eq_nvCover (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    (e : pullbackTwistOne 𝒜 α ≅ L) {ι : Type*} (y : ι → 𝒜 1) (s : ι → Γ(L, ⊤))
    (hs : ∀ i, s i = e.hom.app ⊤ (coordSection 𝒜 α (y i))) (i : ι) :
    α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 ((y i : A)) = nvCover s i :=
  SetLike.ext fun _ => (mem_nvCover_iff_base_mem_basicOpen 𝒜 α hgen e y s hs i).symm

/-- **The section-value dictionary with one hypothesis.** On any open inside `α⁻¹(D₊(y_i))` the
ratio `s_k / s_i` is the inverse image along `α` of the degree-zero fraction `y_k / y_i`; the
inclusion into the chart `X_{s_i}` that
`Stacks.CoordinateDictionary.resO_ratio_eq_pullbackAwayCoord` also asks for is
`Stacks.CoordinateDictionary.preimage_basicOpen_le_nvCover`. This is the form every step of the
coordinate cut of [Stacks, Tag 02NP] consumes. -/
theorem resO_ratio_eq_pullbackAwayCoord_of_le_preimage
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    (e : pullbackTwistOne 𝒜 α ≅ L) {ι : Type*} (y : ι → 𝒜 1) (s : ι → Γ(L, ⊤))
    (hs : ∀ i, s i = e.hom.app ⊤ (coordSection 𝒜 α (y i))) (i k : ι) {W : X.Opens}
    (hle : W ≤ α ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 ((y i : A))) :
    resO (hle.trans (preimage_basicOpen_le_nvCover 𝒜 α hgen e y s hs i)) (ratio s i k) =
      pullbackAwayCoord 𝒜 α (y i).2 hle (y k) :=
  resO_ratio_eq_pullbackAwayCoord 𝒜 α e y s hs i k
    (hle.trans (preimage_basicOpen_le_nvCover 𝒜 α hgen e y s hs i)) hle

end Family

end Stacks.CoordinateDictionary

end
