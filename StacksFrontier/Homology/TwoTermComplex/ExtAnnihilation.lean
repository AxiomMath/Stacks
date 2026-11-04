module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

/-!
# Transporting ideal annihilation of `Ext¹` along a two-term comparison

For objects of the derived category with cohomology concentrated in degrees `-1` and `0`, a
morphism that is an isomorphism in degree `0` and an epimorphism in degree `-1` transports the
property "an ideal annihilates every first Ext group against a module" from its source to its
target.

## Main results

* `TwoTermComplexExt.ext_one_annihilated_of_homology_iso_epi` (Stacks 0G9J).

## Implementation notes

The argument is the cone. Completing the comparison to a distinguished triangle, the
degree-`0` isomorphism and the degree-`-1` epimorphism force the cone to lie in degrees
`≤ -2`: at each degree the long exact sequence turns the epimorphism into vanishing of the
cone's map and the mono in the next degree into an epimorphism onto the cone's homology, so the
cone's homology vanishes there. A class on the target that is killed after pulling back to the
source factors through the cone by Yoneda exactness, and a map from an object in degrees
`≤ -2` to a shifted module, which lies in degrees `≥ -1`, is zero by the t-structure.

`DerivedCategory.Ext` and the t-structure come from
`StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic`, where the Ext groups are defined.

## References

* [The Stacks Project, Lemma 15.85.10 (0G9J)](https://stacks.math.columbia.edu/tag/0G9J)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TwoTermComplexExt

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0G9J.** Let `K ⟶ K'` be a morphism of derived objects whose cohomology is
concentrated in degrees `-1` and `0`. If it induces an isomorphism in degree `0` and an
epimorphism in degree `-1`, then ideal annihilation of every first Ext group for `K` implies
the same ideal annihilation for `K'`. -/
@[stacks 0G9J]
public theorem ext_one_annihilated_of_homology_iso_epi
    {R : Type u} [CommRing R] (I : Ideal R)
    {K K' : DerivedCategory (ModuleCat.{v} R)}
    (α : K ⟶ K')
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (hK' : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K'))
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map α)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).map α)]
    (h : ∀ (N : ModuleCat.{v} R) (a : R), a ∈ I →
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1,
        a • ξ = 0) :
    ∀ (N : ModuleCat.{v} R) (a : R), a ∈ I →
      ∀ ξ : DerivedCategory.Ext K'
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1,
        a • ξ = 0 := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle α
  have hC : C.IsLE (-2) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    have hαepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α) := by
      rcases eq_or_ne i (-1) with rfl | hi₁
      · infer_instance
      rcases eq_or_ne i 0 with rfl | hi₀
      · infer_instance
      exact (hK' i hi₁ hi₀).epi _
    have hαmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i + 1)).map α) := by
      rcases eq_or_ne (i + 1) 0 with hi0 | hi0
      · rw [hi0]
        infer_instance
      exact (hK (i + 1) (by omega) hi0).mono _
    have hg0 : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map g = 0 :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff
        (Triangle.mk α g δ) hT i).mp hαepi
    have hgEpi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map g) := by
      have he : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
          (Triangle.mk α g δ).mor₂) :=
        (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        (Triangle.mk α g δ) hT i (i + 1) rfl).mpr
        ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
          (Triangle.mk α g δ) hT i (i + 1) rfl).mp hαmono)
      change Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map g)
      exact he
    have := hgEpi
    exact IsZero.of_epi_eq_zero _ hg0
  intro N a ha ξ
  have hz : α ≫ (a • ξ) = 0 := by
    rw [CategoryTheory.Linear.comp_smul]
    exact h N a ha (α ≫ ξ)
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ (Triangle.mk α g δ) hT (a • ξ) hz
  rw [hq]
  have hq0 : q = 0 := by
    have : DerivedCategory.TStructure.t.IsLE C (-2) := hC
    have : DerivedCategory.TStructure.t.IsGE
        (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦(1 : ℤ)⟧) (-1) :=
      DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1) (by omega)
    change C ⟶ _ at q
    exact DerivedCategory.TStructure.t.zero q (-2) (-1) (by omega)
  rw [hq0, comp_zero]

end TwoTermComplexExt
