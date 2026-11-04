module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedRingFunctoriality
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY

/-!
# The morphism `r_{L, ψ}` of Stacks Tag 01NK against the morphism of Stacks Tag 01MY

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of graded rings and `ψ : B → Γ_*(T, L)` a graded map, the
datum of [Stacks, Tag 01NK]. `ProjChartGradedRingFunctoriality.lean` proves that
`r_{L, ψ ∘ φ} = r_{L, ψ} ≫ Proj(φ)` when `φ` induces an everywhere defined morphism
`Proj(φ) : Proj ℬ ⟶ Proj 𝒜` (Mathlib's `AlgebraicGeometry.Proj.map`, which asks
`ℬ₊ ≤ 𝒜₊.map φ`). This file proves the same compatibility for the morphism
`U(φ) ⟶ Proj 𝒜` of [Stacks, Tag 01MY], defined on the open `U(φ) ⊆ Proj ℬ` only
(`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`): `r_{L, ψ}` maps `U(ψ ∘ φ)` into `U(φ)`, and
there `r_{L, ψ} ≫ r_φ = r_{L, ψ ∘ φ}`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality`.

* `chartToProj_comap_eq`: the chart of a homogeneous `f` for `ψ ∘ φ` is the chart of `φ f` for
  `ψ` followed by the local morphism of [Stacks, Tag 01MY] at `f`.
* `glued_comp_mapHom`: **`r_{L, ψ}` followed by `r_φ` is `r_{L, ψ ∘ φ}`.**
* `coveringOpen_comap_eq_of_mapDomain_eq_top`: `U(ψ ∘ φ) = U(ψ)` when `U(φ)` is all of
  `Proj ℬ`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal Graded
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom mapAwayHom basicOpen_le_mapDomain
  homOfLE_mapHom)
open Stacks.MorphismToProj (HomogeneousRatios)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections ℬ L)

section Chart

variable {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
  (hV : V ≤ nonvanishingOpen T (natTensorPow L e) ((comap φ ψ).toFun e ⟨f, hf⟩))
  (hV' : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨φ f, map_mem φ hf⟩))

include hV hV'

/-- **The chart of a homogeneous `f` for `ψ ∘ φ` is the chart of `φ f` for `ψ` followed by the
local morphism of [Stacks, Tag 01MY] at `f`.** The two dehomogenisation ring maps differ by
`HomogeneousLocalization.Away.map φ f` (`lift_comp_awayMap`), which is the ring map the local
morphism of Tag 01MY is `Spec` of. -/
theorem chartToProj_comap_eq :
    (comap φ ψ).chartToProj hf hV he
      = ψ.chart (map_mem φ hf) hV' he ≫ mapAwayHom 𝒜 ℬ φ he hf := by
  unfold GradedSections.chartToProj GradedSections.chart HomogeneousRatios.chartToProj
    HomogeneousRatios.chart HomogeneousRatios.toSpecAway mapAwayHom
  rw [lift_comp_awayMap φ ψ hf he hV hV', CommRingCat.ofHom_comp, Spec.map_comp,
    ← Proj.basicOpenIsoSpec_hom ℬ (φ f) (map_mem φ hf) he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Chart

/-- **`r_{L, ψ}` followed by the morphism `r_φ : U(φ) ⟶ Proj 𝒜` of [Stacks, Tag 01MY] is
`r_{L, ψ ∘ φ}`.** The morphism `k : U(ψ ∘ φ) ⟶ U(φ)` is any lift of
`U(ψ ∘ φ) ⊆ U(ψ) ⟶ Proj ℬ` through `U(φ) ⊆ Proj ℬ`; it is unique, `U(φ) ⊆ Proj ℬ` being a
monomorphism.

Both sides are compared on each `T_{ψ(φ f)}`: there `r_{L, ψ}` is the chart of `φ f`, which lands
in `D₊(φ f)`, where `r_φ` is the local morphism of Tag 01MY at `f` (`homOfLE_mapHom`); the two
charts are then identified by `chartToProj_comap_eq`. -/
theorem glued_comp_mapHom (k : (comap φ ψ).coveringOpen.toScheme ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    (hk : k ≫ (mapDomain 𝒜 ℬ φ).ι = T.homOfLE (coveringOpen_le φ ψ) ≫ ψ.glued) :
    k ≫ mapHom 𝒜 ℬ φ = (comap φ ψ).glued := by
  refine (comap φ ψ).eq_glued_of_homOfLE_eq fun e f hf he => ?_
  have hVψ : nonvanishingOpen T (natTensorPow L e) ((comap φ ψ).toFun e ⟨f, hf⟩)
      ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨φ f, map_mem φ hf⟩) := le_rfl
  have key : T.homOfLE ((comap φ ψ).nonvanishingOpenAt_le_coveringOpen_of_pos hf he) ≫ k
      = ψ.chart (map_mem φ hf) hVψ he
          ≫ (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ φ he hf) := by
    rw [← cancel_mono (mapDomain 𝒜 ℬ φ).ι, Category.assoc, hk, Category.assoc,
      Scheme.homOfLE_ι, GradedSections.chart_ι, ← Category.assoc, T.homOfLE_homOfLE]
    exact ψ.homOfLE_glued_of_pos (map_mem φ hf) he
  rw [← Category.assoc, key, Category.assoc, homOfLE_mapHom]
  exact (chartToProj_comap_eq φ ψ hf he le_rfl hVψ).symm

/-- **When the morphism of [Stacks, Tag 01MY] is everywhere defined, restricting the datum along
`φ` loses no points**: `U(ψ ∘ φ) = U(ψ)`. A point `t` of `U(ψ)` is sent by `r_{L, ψ}` into some
`D₊(φ f)`, `f` homogeneous of positive degree, and the preimage of `D₊(φ f)` is `T_{ψ(φ f)}`
(`GradedSections.preimage_basicOpen_glued`), which is a member of the family `U(ψ ∘ φ)` is the
union of. -/
theorem coveringOpen_comap_eq_of_mapDomain_eq_top (h : mapDomain 𝒜 ℬ φ = ⊤) :
    (comap φ ψ).coveringOpen = ψ.coveringOpen := by
  refine le_antisymm (coveringOpen_le φ ψ) fun x hx => ?_
  have hy : ψ.glued.base ⟨x, hx⟩ ∈ mapDomain 𝒜 ℬ φ := h ▸ trivial
  obtain ⟨d, f, hd, hf, hfy⟩ :=
    (Stacks.AlgebraicGeometry.ProjShared.mem_mapDomain_iff 𝒜 ℬ φ _).mp hy
  have hmem : (⟨x, hx⟩ : ψ.coveringOpen.toScheme) ∈
      ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (φ f) := hfy
  rw [ψ.preimage_basicOpen_glued (map_mem φ hf) hd] at hmem
  exact (comap φ ψ).nonvanishingOpenAt_le_coveringOpen_of_pos hf hd hmem

end Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality

end
