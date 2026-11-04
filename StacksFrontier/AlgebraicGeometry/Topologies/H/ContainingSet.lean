module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ExtendingFunctors

/-!
# Every set-sized collection of schemes lies in a big h site

A big h site `AlgebraicGeometry.BigHSite` is built from a size cutoff `κ`, giving the full
subcategory `Sch_κ`, together with a set-sized system of chosen h covering families on it. For
any set of schemes that is small in the working universe there is a big h site containing all of
its members.

## Main results

* `AlgebraicGeometry.isSite_hCutoff`: the h covering families of `Sch_κ` satisfy the site axioms
  of Stacks 000X.
* `AlgebraicGeometry.BigHSite.ofCutoff`: a big h site with a prescribed cutoff.
* `AlgebraicGeometry.BigHSite.exists_containing`: a small set of schemes is contained in some
  big h site.

## Implementation notes

The cutoff comes from **Stacks 000J**, `AlgebraicGeometry.exists_size_cutoff`; the chosen covering
system comes from `exists_covBounded_isSite` (Stacks 000X) applied to the h covering families of
`Sch_κ`, whose site axioms are `AlgebraicGeometry.isSite_hCutoff`. Those axioms are Stacks 0ETY: an
isomorphism is an h covering (`AlgebraicGeometry.isHCovering_of_isIso`), and h coverings are stable
under composition of families (`AlgebraicGeometry.isHCovering_bind`) and under base change
(`AlgebraicGeometry.isHCovering_pullback`); fibre products exist in `Sch_κ` and are computed in all
schemes (Stacks 021U).

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 0ETY](https://stacks.math.columbia.edu/tag/0ETY)
* [Stacks Project, Tag 0ETZ](https://stacks.math.columbia.edu/tag/0ETZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- The image in all schemes of a covering of `Sch_κ`, pushed forward along an identification of
its target, is an h covering as soon as the covering is one. -/
private theorem isHCovering_map_pushforward_eqToHom {κ : Cardinal.{u}}
    (c : Covering.{u + 1, u, u + 1} (SchemeBelow κ)) (hc : IsHCoveringInCutoff c)
    {T : SchemeBelow κ} (e : c.1 = T) :
    IsHCovering ((c.2.pushforward (eqToHom e)).map (schemeBelowInclusion κ)).X
      ((c.2.pushforward (eqToHom e)).map (schemeBelowInclusion κ)).f := by
  obtain ⟨U, E⟩ := c
  obtain rfl : U = T := e
  change IsHCovering (E.map (schemeBelowInclusion κ)).X (E.map (schemeBelowInclusion κ)).f at hc
  exact hc.of_iso (fun _ ↦ Iso.refl _) (fun i ↦ by
    show 𝟙 _ ≫ (schemeBelowInclusion κ).map (E.f i) =
      (schemeBelowInclusion κ).map (E.f i ≫ 𝟙 U)
    simp)

/-- **The h covering families of `Sch_κ` satisfy the site axioms** (Stacks 0ETY and 021U). -/
theorem isSite_hCutoff (κ : Cardinal.{u}) : IsSite (IsHCoveringInCutoff (κ := κ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    exact isHCovering_of_isIso (I := PUnit) ((schemeBelowInclusion κ).map f)
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    exact isHCovering_bind (𝒰.2.map (schemeBelowInclusion κ)) h𝒰
      (fun i ↦ ((𝒱 i).2.pushforward (eqToHom (h i))).map (schemeBelowInclusion κ))
      (fun i ↦ isHCovering_map_pushforward_eqToHom (𝒱 i) (h𝒱 i) (h i))
  · intro 𝒰 h𝒰 V g
    refine ⟨fun i ↦ pullback (𝒰.2.f i) g, fun i ↦ pullback.fst _ _, fun i ↦ pullback.snd _ _,
      fun i ↦ IsPullback.of_hasPullback _ _, ?_⟩
    exact (isHCovering_pullback h𝒰 ((schemeBelowInclusion κ).map g)).of_iso
      (fun i ↦ PreservesPullback.iso (schemeBelowInclusion κ) (𝒰.2.f i) g)
      (fun i ↦ PreservesPullback.iso_hom_snd (schemeBelowInclusion κ) (𝒰.2.f i) g)

namespace BigHSite

/-- **A big h site with a prescribed cutoff and prescribed initial schemes.** The cutoff `κ`
must satisfy the three conditions of **Stacks 000J** and dominate the sizes of the initial
schemes; the chosen covering system is a bounded representative system for the h covering
families of `Sch_κ` (**Stacks 000X**), with no initially prescribed coverings. -/
public noncomputable abbrev ofCutoff (κ : Cardinal.{u}) (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof)
    (S₀ : Set Scheme.{u}) [Small.{u} S₀] (hS₀ : ∀ X ∈ S₀, X.size < κ) : BigHSite.{u} :=
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1} (SchemeBelow κ)) := ∅
  have : Small.{u + 1} Cov₀ := inferInstance
  have h := _root_.exists_covBounded_isSite (IsHCoveringInCutoff (κ := κ))
    (isSite_hCutoff κ) Cov₀ (by intro U hU; cases hU)
  { initialSchemes := S₀
    initialSchemes_small := inferInstance
    cutoff := κ
    aleph0_lt_cutoff := hκ
    cutoff_isStrongPrelimit := hsl
    aleph0_lt_cutoff_cof := hcof
    initialSchemes_mem := hS₀
    initialCoverings := Cov₀
    initialCoverings_small := inferInstance
    initialCoverings_supported := by simp [Cov₀]
    coveringBound := Classical.choose h
    coveringOrdinal := Classical.choose (Classical.choose_spec h)
    coveringOrdinal_isSuccLimit := (Classical.choose_spec (Classical.choose_spec h)).1
    initialCoverings_mem := by simp [Cov₀]
    coverings_isSite := (Classical.choose_spec (Classical.choose_spec h)).2.2.1
    covering_representative := (Classical.choose_spec (Classical.choose_spec h)).2.2.2 }

/-- **A set-sized collection of schemes is contained in some big h site.** -/
theorem exists_containing (S₀ : Set Scheme.{u}) [Small.{u} S₀] :
    ∃ B : BigHSite.{u}, ∀ X ∈ S₀, B.Contains X := by
  obtain ⟨κ, hκ₀, hκ₁, hκ₂, hκS₀⟩ := AlgebraicGeometry.exists_size_cutoff S₀
  exact ⟨ofCutoff κ hκ₀ hκ₁ hκ₂ S₀ hκS₀, hκS₀⟩

end BigHSite

end AlgebraicGeometry

end
