module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Lifting an étale covering across a thickening, inside a big fppf site

Let `j : Y ⟶ Y'` be a morphism of the big fppf site of `S` whose underlying morphism of schemes is
a thickening. By the topological invariance of the étale site ([Stacks Project, Tag 039R]) every
étale morphism `W ⟶ Y` is the base change along `j` of an étale morphism `V ⟶ Y'`, which can be
taken inside the site. This file does this for a whole jointly surjective family with affine
sources at once: the lifted family is again étale with affine sources (a thickening of an affine
scheme is affine, [Stacks Project, Tag 06AD]), it covers `Y'` for the fppf topology because `Y` and
`Y'` have the same points, and the fibre products `Y ×_{Y'} V` of the site map back to the given
members over `Y`.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_etale_covering_lift_of_isThickening`: the lift of an étale
  family with affine sources across a thickening.

That the lifted family covers `Y'` is
`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_etale`: a jointly surjective family of
étale morphisms of the site is a covering family.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigFppfOver

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- **An étale family with affine sources lifts across a thickening.** Let `j : Y ⟶ Y'` be a
morphism of the big fppf site of `S` which is a thickening, and `e k : W k ⟶ Y` a jointly
surjective family of étale morphisms of the site with affine sources. Then there is a family
`τ k : V k ⟶ Y'` of étale morphisms of the site with affine sources, covering `Y'`, together with
morphisms `ι k : Y ×_{Y'} V k ⟶ W k` over `Y` from the fibre products of the site. -/
theorem exists_etale_covering_lift_of_isThickening {Y Y' : BigFppfOver B S hS} (j : Y ⟶ Y')
    (hj : Stacks.Thickenings.IsThickening ((toScheme B S hS).map j)) {I : Type (u + 1)}
    (W : I → BigFppfOver B S hS) (e : ∀ k, W k ⟶ Y)
    (he : ∀ k, Etale ((toScheme B S hS).map (e k)))
    (hW : ∀ k, IsAffine ((toScheme B S hS).obj (W k)))
    (hsurj : ∀ y : (toScheme B S hS).obj Y, ∃ k, y ∈ Set.range ((toScheme B S hS).map (e k))) :
    ∃ (V : I → BigFppfOver B S hS) (τ : ∀ k, V k ⟶ Y') (ι : ∀ k, pullback j (τ k) ⟶ W k),
      (∀ k, Etale ((toScheme B S hS).map (τ k))) ∧
      (∀ k, IsAffine ((toScheme B S hS).obj (V k))) ∧
      (∀ k, ι k ≫ e k = pullback.fst j (τ k)) ∧
      Sieve.ofArrows V τ ∈ topology B S hS Y' := by
  let T := toScheme B S hS
  have : IsClosedImmersion (T.map j) := hj.1
  have hjs : Function.Surjective (T.map j).base := hj.2
  have hlift (k : I) :=
    Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective
      B S hS j hjs (W k) (T.map (e k)) (he k)
  choose V τ hτ eS heS using hlift
  -- the comparison from the fibre product of the site to the given member
  let φ : ∀ k, T.obj (pullback j (τ k)) ⟶ T.obj (W k) := fun k =>
    (PreservesPullback.iso T j (τ k)).hom ≫ (pullbackSymmetry (T.map j) (T.map (τ k))).hom ≫
      (eS k).hom
  have hφ (k : I) : φ k ≫ T.map (e k) = T.map (pullback.fst j (τ k)) := by
    simp only [φ, Category.assoc]
    rw [heS, pullbackSymmetry_hom_comp_snd, PreservesPullback.iso_hom_fst]
  have hT {A A' : BigFppfOver B S hS} (f : A ⟶ A') :
      T.map f ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom := by
    change B.inclusion.map f.left ≫ B.inclusion.map A'.hom = _
    rw [← B.inclusion.map_comp, Over.w]
  have hφS (k : I) : φ k ≫ B.inclusion.map (W k).hom =
      B.inclusion.map (pullback j (τ k)).hom := by
    rw [← hT (e k), ← Category.assoc, hφ, hT]
  have hι (k : I) := exists_hom_of_comp_eq B S hS (φ k) (hφS k)
  choose ι hιφ using hι
  refine ⟨V, τ, ι, hτ, fun k => ?_, fun k => ?_, ?_⟩
  · -- `Y ×_{Y'} V k ⟶ V k` is a thickening with affine source
    have := hW k
    have : IsAffine (pullback (T.map (τ k)) (T.map j)) := IsAffine.of_isIso (eS k).hom
    exact Stacks.Thickenings.isAffine_of_isThickening
      (Stacks.Thickenings.isThickening_of_isPullback
        (IsPullback.of_hasPullback (T.map (τ k)) (T.map j)) hj)
  · apply T.map_injective
    rw [T.map_comp, hιφ, hφ]
  · refine ofArrows_mem_topology_of_etale B S hS V τ hτ fun y' => ?_
    obtain ⟨y, rfl⟩ := hjs y'
    obtain ⟨k, w, rfl⟩ := hsurj y
    refine ⟨k, (pullback.fst (T.map (τ k)) (T.map j)).base ((eS k).inv.base w), ?_⟩
    have h₁ : (eS k).inv ≫ pullback.snd (T.map (τ k)) (T.map j) = T.map (e k) := by
      rw [← heS, Iso.inv_hom_id_assoc]
    have h₂ := congrArg (fun t => t.base w)
      (((eS k).inv ≫= pullback.condition (f := T.map (τ k)) (g := T.map j)).trans
        (by rw [reassoc_of% h₁]))
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h₂
    exact h₂

end AlgebraicGeometry.BigFppfOver

end
