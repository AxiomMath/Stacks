module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CohomologyOfClosedMapUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FiberNeighborhoods
public import Mathlib.CategoryTheory.Sites.LocallyInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The higher cohomology presheaf of a proper map dies locally on the target

Let `π : X ⟶ W` be a closed continuous map whose fibres are quasi-compact and any two distinct
points of which have disjoint open neighbourhoods in `X`, and let `G` be an abelian sheaf on `X`
whose restriction to every fibre of `π` is soft. This file proves that for `p > 0` every class in
`H^p(π^{-1} V, G)`, for `V` an open subset of `W`, is killed by restriction along the members of
a covering sieve of `V`.

By [Stacks, Tag 072W] the presheaf `V ↦ H^p(π^{-1} V, G)` on `W` sheafifies to `R^p π_* G`, so
this is the vanishing `R^p π_* G = 0` in its pointwise form.

## Main results

All in the namespace `Stacks.Topology`.

* `isZero_colimit_openNeighborhoodCohomology_of_isZero_restriction`: the colimit of the
  cohomology of `G` over the open neighbourhoods of a quasi-compact subset with separated points
  vanishes as soon as the cohomology of the restriction of `G` to that subset does.
* `exists_openNhds_map_eq_zero_of_isZero_restriction`: the same conclusion read on one class — it
  restricts to zero on a smaller open neighbourhood of the subset.
* `isZero_restrictionCohomologyPresheaf_of_isSoft`: the higher cohomology of a soft restriction
  to a quasi-compact subset with separated points vanishes.
* `equalizerSieve_mem_of_isSoft_fiber`: the higher cohomology presheaf of a sheaf whose
  restrictions to the fibres of `π` are soft dies locally on `W`.
* `equalizerSieve_mem_of_isFlasque`: the same for a flasque `G`.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe t s

noncomputable section

-- The cheap instance for `HasPointwiseRightDerivedFunctor` on `K⁺` is given precedence: otherwise
-- synthesis tries to prove termwise injectivity of an unknown complex and times out.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X : TopCat.{s}}
  [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t}) (Z : Set X)
  [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [EnoughInjectives
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]

section Subset

variable (hZ : IsCompact Z)
  (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)

include hZ hSep in
/-- **The colimit of the cohomology of `G` over the open neighbourhoods of a quasi-compact subset
with separated points vanishes when the cohomology of the restriction does.** -/
theorem isZero_colimit_openNeighborhoodCohomology_of_isZero_restriction (p : ℕ)
    (hres : IsZero ((restrictionCohomologyPresheaf.{t} (TopCat.of Z)
      ((restrictionFunctorUnivLE.{max s t} X Z).obj G) p).obj (op ⊤)))
    (U : (OpenNhdsSet Z)ᵒᵖ)
    (ξ : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z G p).obj U)) :
    colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z G p) U ξ = 0 := by
  let _hdc := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})
  let _hdc' := HasDerivedCategory.standard AddCommGrpCat.{max s t}
  have _hiso := isIso_cohomologyOfClosedMapUnivLE.{_, _, t} Z hZ hSep G p
  refine (ConcreteCategory.bijective_of_isIso (cohomologyOfClosedMapUnivLE.{t} Z G p)).1 ?_
  rw [map_zero]
  exact @Subsingleton.elim _ (AddCommGrpCat.isZero_iff_subsingleton.mp hres) _ _

include hZ hSep in
/-- **A class on an open neighbourhood of a quasi-compact subset with separated points restricts
to zero on a smaller open neighbourhood**, as soon as the cohomology of the restriction of `G` to
the subset vanishes. -/
theorem exists_openNhds_map_eq_zero_of_isZero_restriction (p : ℕ)
    (hres : IsZero ((restrictionCohomologyPresheaf.{t} (TopCat.of Z)
      ((restrictionFunctorUnivLE.{max s t} X Z).obj G) p).obj (op ⊤)))
    (U₀ : Opens X) (hU₀ : Z ⊆ (U₀ : Set X))
    (ξ : ToType ((restrictionCohomologyPresheaf.{t} X G p).obj (op U₀))) :
    ∃ (U₁ : Opens X) (_ : Z ⊆ (U₁ : Set X)) (hle : U₁ ≤ U₀),
      (restrictionCohomologyPresheaf.{t} X G p).map (homOfLE hle).op ξ = 0 := by
  have hzero := isZero_colimit_openNeighborhoodCohomology_of_isZero_restriction.{t} G Z hZ hSep p
    hres (op ⟨U₀, hU₀⟩) ξ
  obtain ⟨U₁, a, b, ha⟩ := exists_map_eq_of_colimit_ι_eqUnivLE.{t} Z G p
    (U := op ⟨U₀, hU₀⟩) (V := op ⟨U₀, hU₀⟩) ξ
    (0 : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z G p).obj (op ⟨U₀, hU₀⟩)))
    (hzero.trans (map_zero (ConcreteCategory.hom
      (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z G p) (op ⟨U₀, hU₀⟩)))).symm)
  rw [map_zero] at ha
  refine ⟨U₁.unop.obj, U₁.unop.property,
    leOfHom ((openNhdsSetInclusion Z).map a.unop), Eq.trans ?_ ha⟩
  exact congrArg
    (fun m : U₁.unop.obj ⟶ U₀ ↦ (restrictionCohomologyPresheaf.{t} X G p).map m.op ξ)
    (Subsingleton.elim _ _)

omit [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})] in
include hZ hSep in
/-- **The higher cohomology of a soft restriction to a quasi-compact subset with separated points
vanishes.** -/
theorem isZero_restrictionCohomologyPresheaf_of_isSoft
    [HasInjectiveResolutions
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
    (hsoft : IsSoft ((restrictionFunctorUnivLE.{max s t} X Z).obj G)) (p : ℕ) (hp : 0 < p) :
    IsZero ((restrictionCohomologyPresheaf.{t} (TopCat.of Z)
      ((restrictionFunctorUnivLE.{max s t} X Z).obj G) p).obj (op ⊤)) := by
  have _hcs : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  have _ht2 : T2Space Z := t2Space_coe_of_pairwiseSeparated hSep
  let _hdc := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})
  let _hdc' := HasDerivedCategory.standard AddCommGrpCat.{max s t}
  exact isZero_cohomologyPresheaf_restriction_of_rightAcyclic.{_, _, t} G
    (rightAcyclic_sections_of_isSoft_univLE.{_, _, max s t} _ hsoft) p hp

end Subset

section Fibre

variable {W : TopCat.{s}} (π : X ⟶ W)

/-- Distinct points of one fibre of a separated map have disjoint open neighbourhoods. -/
private theorem exists_disjoint_open_of_isSeparatedMap_fibre {α β : Type*} [TopologicalSpace α]
    {f : α → β} (hsep : IsSeparatedMap f) (w : β) :
    ∀ x ∈ f ⁻¹' ({w} : Set β), ∀ y ∈ f ⁻¹' ({w} : Set β), x ≠ y →
      ∃ A B : Set α, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B :=
  fun x hx y hy hxy ↦ hsep x y (Eq.trans hx (Eq.symm hy)) hxy

/-- **The higher cohomology presheaf of a sheaf whose restrictions to the fibres of a closed map
are soft dies locally on the target.** For `p > 0` and `V` an open subset of `W`, every class in
`H^p(π^{-1} V, G)` is killed by restriction along the members of a covering sieve of `V`.

By [Stacks, Tag 072W] this is the vanishing `R^p π_* G = 0` in its pointwise form. -/
@[sga "4 V 4.13" "special case"]
theorem equalizerSieve_mem_of_isSoft_fiber
    (hcl : IsClosedMap (π.hom : X → W))
    (hcpt : ∀ w : W, IsCompact ((π.hom : X → W) ⁻¹' ({w} : Set W)))
    (hsep : IsSeparatedMap (π.hom : X → W))
    (hsoft : ∀ w : W, IsSoft ((restrictionFunctorUnivLE.{max s t} X
      ((π.hom : X → W) ⁻¹' ({w} : Set W))).obj G))
    (p : ℕ) (hp : 0 < p) (V : Opens W)
    (ξ : ToType (((Opens.map π).op ⋙ restrictionCohomologyPresheaf.{t} X G p).obj (op V))) :
    Presheaf.equalizerSieve
        (F := (Opens.map π).op ⋙ restrictionCohomologyPresheaf.{t} X G p) (X := op V) ξ 0 ∈
      Opens.grothendieckTopology W V := by
  intro w hwV
  let _hext : HasExt.{max s t} (Sheaf (Opens.grothendieckTopology
      (TopCat.of ((π.hom : X → W) ⁻¹' ({w} : Set W)))) AddCommGrpCat.{max s t}) :=
    hasExt_sheafOpens.{max s t} _
  let _hei : EnoughInjectives (Sheaf (Opens.grothendieckTopology
      (TopCat.of ((π.hom : X → W) ⁻¹' ({w} : Set W)))) AddCommGrpCat.{max s t}) :=
    enoughInjectives_sheafOpens.{max s t} _
  let _hir : HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology
      (TopCat.of ((π.hom : X → W) ⁻¹' ({w} : Set W)))) AddCommGrpCat.{max s t}) :=
    hasInjectiveResolutions_sheafOpens.{max s t} _
  have hSep := exists_disjoint_open_of_isSeparatedMap_fibre hsep w
  have hres := isZero_restrictionCohomologyPresheaf_of_isSoft.{t} G _ (hcpt w) hSep (hsoft w) p hp
  have hU₀ : ((π.hom : X → W) ⁻¹' ({w} : Set W)) ⊆ (((Opens.map π).obj V : Opens X) : Set X) := by
    intro x (hx : (π.hom : X → W) x = w)
    change (π.hom : X → W) x ∈ V
    rwa [hx]
  obtain ⟨U₁, hZU₁, hle, hmap⟩ := exists_openNhds_map_eq_zero_of_isZero_restriction.{t} G _
    (hcpt w) hSep p hres ((Opens.map π).obj V) hU₀ ξ
  obtain ⟨V₁, hwV₁, hV₁⟩ := preimageNeighborhoods_cofinal (π.hom : X → W) w hcl
    π.hom.continuous U₁ hZU₁
  have hle₂ : (Opens.map π).obj (V ⊓ V₁) ≤ U₁ := fun x hx => hV₁ hx.2
  refine ⟨V ⊓ V₁, homOfLE inf_le_left, ?_, hwV, hwV₁⟩
  change ((Opens.map π).op ⋙ restrictionCohomologyPresheaf.{t} X G p).map
    (homOfLE (inf_le_left : V ⊓ V₁ ≤ V)).op ξ = _
  rw [map_zero]
  refine Eq.trans (congrArg
    (fun m : (Opens.map π).obj (V ⊓ V₁) ⟶ (Opens.map π).obj V ↦
      (restrictionCohomologyPresheaf.{t} X G p).map m.op ξ)
    (Subsingleton.elim ((Opens.map π).map (homOfLE (inf_le_left : V ⊓ V₁ ≤ V)))
      (homOfLE hle₂ ≫ homOfLE hle))) ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    ((restrictionCohomologyPresheaf.{t} X G p).map_comp (homOfLE hle).op (homOfLE hle₂).op) ξ) ?_
  exact Eq.trans
    (congrArg (ConcreteCategory.hom
      ((restrictionCohomologyPresheaf.{t} X G p).map (homOfLE hle₂).op)) hmap)
    (map_zero (ConcreteCategory.hom
      ((restrictionCohomologyPresheaf.{t} X G p).map (homOfLE hle₂).op)))

/-- **The higher cohomology presheaf of a flasque sheaf dies locally on the target of a closed
map with quasi-compact fibres whose points are separated in the source.** -/
theorem equalizerSieve_mem_of_isFlasque [TopCat.Sheaf.IsFlasque G]
    (hcl : IsClosedMap (π.hom : X → W))
    (hcpt : ∀ w : W, IsCompact ((π.hom : X → W) ⁻¹' ({w} : Set W)))
    (hsep : IsSeparatedMap (π.hom : X → W))
    (p : ℕ) (hp : 0 < p) (V : Opens W)
    (ξ : ToType (((Opens.map π).op ⋙ restrictionCohomologyPresheaf.{t} X G p).obj (op V))) :
    Presheaf.equalizerSieve
        (F := (Opens.map π).op ⋙ restrictionCohomologyPresheaf.{t} X G p) (X := op V) ξ 0 ∈
      Opens.grothendieckTopology W V := by
  refine equalizerSieve_mem_of_isSoft_fiber.{t} G π hcl hcpt hsep (fun w => ?_) p hp V ξ
  exact isSoft_restrictionFunctorUnivLE_of_isFlasque.{max s t} G _ (hcpt w)
    (exists_disjoint_open_of_isSeparatedMap_fibre hsep w)

end Fibre

end

end Stacks.Topology

end
