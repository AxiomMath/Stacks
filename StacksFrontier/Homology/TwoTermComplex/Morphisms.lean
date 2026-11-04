module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor

@[expose] public section

/-!
# Maps between two-term objects of the derived category

This file collects two facts about objects of `D(R)` whose cohomology is concentrated in degrees
`-1` and `0`, both of which say that such an object is rigid enough that a map out of it is
controlled by what it does on cohomology.

## Main results

* `TwoTermComplex.comp_eq_zero_of_two_term_homology` (Stacks 0AJT): for `φ : K₁ ⟶ K₂` and
  `ψ : K₂ ⟶ K₃` between two-term objects, if `H⁰(φ) = 0` and `H⁻¹(ψ) = 0` then `φ ≫ ψ = 0`.
* `TwoTermComplex.smul_id_eq_zero_of_two_term_homology_map` (Stacks 0G9I): if `α : K ⟶ K'` is an
  isomorphism on `H⁰` and surjective on `H⁻¹`, then a scalar `f : R` acting as zero on `K` acts
  as zero on `K'`.

## Implementation notes

Cohomology concentration is expressed by vanishing of `DerivedCategory.homologyFunctor` outside
`{-1, 0}`; surjectivity on `H⁻¹` is `Epi` on the corresponding homology map. Stacks 0AJT is
proved by factoring `φ` through the truncation triangle of `K₂` and applying the vanishing of
maps from a `t`-coconnective to a `t`-connective object.

## References

* [The Stacks Project, Lemma 15.86.10 (0AJT)](https://stacks.math.columbia.edu/tag/0AJT)
* [The Stacks Project, Lemma 15.86.8 (0G9I)](https://stacks.math.columbia.edu/tag/0G9I)
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace TwoTermComplex

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

/-- **Stacks 0AJT.** Let `K₁, K₂, K₃` be objects of `D(R)` with cohomology in degrees `-1` and
`0`, and let `φ : K₁ ⟶ K₂`, `ψ : K₂ ⟶ K₃`. If `H⁰(φ) = 0` and `H⁻¹(ψ) = 0`, then `φ ≫ ψ = 0`. -/
@[stacks 0AJT]
public theorem comp_eq_zero_of_two_term_homology
    {R : Type u} [Ring R]
    (K₁ K₂ K₃ : DerivedCategory (ModuleCat.{u} R))
    (hK₁ : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K₁))
    (_hK₂ : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K₂))
    (hK₃ : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K₃))
    (φ : K₁ ⟶ K₂) (ψ : K₂ ⟶ K₃)
    (hφ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map φ = 0)
    (hψ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-1)).map ψ = 0) :
    φ ≫ ψ = 0 := by
  have _ : K₁.IsLE 0 := (DerivedCategory.isLE_iff K₁ 0).2 fun i hi =>
    hK₁ i (by omega) (by omega)
  have _ : K₃.IsGE (-1) := (DerivedCategory.isGE_iff K₃ (-1)).2 fun i hi =>
    hK₃ i (by omega) (by omega)
  have hdeg : (-1 : ℤ) + 1 = 0 := by omega
  let T := (DerivedCategory.TStructure.t.triangleLEGE (-1) 0 hdeg).obj K₂
  have i3 : DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.triangleLEGE (-1) 0 hdeg).obj K₂).obj₃ 0 :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE 0).obj K₂) 0)
  have i1 : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.triangleLEGE (-1) 0 hdeg).obj K₂).obj₁ (-1) :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLE (-1)).obj K₂) (-1))
  have hzero : φ ≫ T.mor₂ = 0 := by
    change φ ≫ ((DerivedCategory.TStructure.t.triangleLEGE (-1) 0 hdeg).obj K₂).mor₂ = 0
    apply hom_eq_zero_of_isLE_isGE K₁
      ((DerivedCategory.TStructure.t.triangleLEGE (-1) 0 hdeg).obj K₂).obj₃ 0
    rw [Functor.map_comp, hφ]
    simp
  obtain ⟨φ', hφ'⟩ := Triangle.coyoneda_exact₂ T
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (-1) 0 hdeg K₂) φ hzero
  have htail : T.mor₁ ≫ ψ = 0 := by
    change ((DerivedCategory.TStructure.t.triangleLEGE (-1) 0 hdeg).obj K₂).mor₁ ≫ ψ = 0
    apply hom_eq_zero_of_isLE_isGE
      ((DerivedCategory.TStructure.t.triangleLEGE (-1) 0 hdeg).obj K₂).obj₁ K₃ (-1)
    rw [Functor.map_comp, hψ]
    simp
  rw [hφ', Category.assoc, htail]
  simp

/-- **Stacks 0G9I.** Let `α : K ⟶ K'` be a morphism of `D(R)` between objects with cohomology in
degrees `-1` and `0` such that `H⁰(α)` is an isomorphism and `H⁻¹(α)` is surjective. If
multiplication by `f : R` is zero on `K`, then it is zero on `K'`. -/
@[stacks 0G9I]
public theorem smul_id_eq_zero_of_two_term_homology_map
    {R : Type u} [CommRing R]
    {K K' : DerivedCategory (ModuleCat.{v} R)} (α : K ⟶ K')
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (hK' : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K'))
    (hα0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map α))
    (hαneg : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).map α))
    (f : R) (hf : f • 𝟙 K = 0) :
    f • 𝟙 K' = 0 := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α g δ
  have : DerivedCategory.TStructure.t.IsLE T.obj₃ (-2) :=
    (DerivedCategory.isLE_iff T.obj₃ (-2)).2 fun i hi => by
      by_cases hi0 : i = 0
      · subst i
        have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map T.mor₁) := hα0
        have hg : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map g = 0 :=
          (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT 0).1 inferInstance
        have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map g) :=
          (DerivedCategory.HomologySequence.exact₃ T hT 0 1 rfl).epi_f
            ((hK 1 (by omega) (by omega)).eq_zero_of_tgt _)
        exact Limits.IsZero.of_epi_eq_zero _ hg
      obtain rfl | hi_pos : i = -1 ∨ 0 < i := by omega
      · have : Mono (DerivedCategory.HomologySequence.δ T (-1) 0 rfl) :=
          (DerivedCategory.HomologySequence.exact₃ T hT (-1) 0 rfl).mono_g
            ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT (-1)).1 hαneg)
        have hδ : DerivedCategory.HomologySequence.δ T (-1) 0 rfl = 0 := by
          apply (cancel_mono
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map α)).1
          simpa [T] using DerivedCategory.HomologySequence.δ_comp T hT (-1) 0 rfl
        exact Limits.IsZero.of_mono_eq_zero _ hδ
      · have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map g) :=
          (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).epi_f
            ((hK (i + 1) (by omega) (by omega)).eq_zero_of_tgt _)
        exact Limits.IsZero.of_epi
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map g)
          (hK' i (by omega) (by omega))
  have hcomp : α ≫ (f • 𝟙 K') = 0 := by
    calc
      α ≫ (f • 𝟙 K') = f • α := by simp
      _ = (f • 𝟙 K) ≫ α := by simp
      _ = 0 := by rw [hf, Limits.zero_comp]
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ T hT (f • 𝟙 K') (by simpa [T] using hcomp)
  have : DerivedCategory.TStructure.t.IsGE K' (-1) :=
    (DerivedCategory.isGE_iff K' (-1)).2 fun i hi => hK' i (by omega) (by omega)
  rw [hq, DerivedCategory.TStructure.t.zero q (-2) (-1) (by omega)]
  simp

end TwoTermComplex
