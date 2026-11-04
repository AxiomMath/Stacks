module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProj.TwistIso
public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The domain of definition of Tag 07ZG, and its compatibility with the charts of the base

A homomorphism `ψ` of quasi-coherent graded `𝒪_S`-algebras does not induce a morphism on all of
the relative projective spectrum of the target: over an affine open `U` of the base it induces
one only on the open `U(ψ_U) ⊆ Proj Γ(U, B)` of
`Stacks.AlgebraicGeometry.ProjShared.mapDomain`. Tag 07ZG glues those opens, and the glueing
needs exactly one compatibility: for nested affine opens `U ⊆ V` of the base, the inverse image
of `U(ψ_V)` under the transition morphism of Tag 01NO is `U(ψ_U)`.

This file proves that compatibility, and that precomposition with a pointwise generating
homomorphism does not change the domain of definition.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.chartDomain`: the open
  `U(ψ_U)` of the chart over an affine open `U` of the base.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.mapDomain_comp_eq_of_generates`: **precomposition
  with a pointwise generating homomorphism does not change the domain of definition.** For
  `ρ : 𝒜₁ →+*ᵍ 𝒜₂` and `ψ : 𝒜₂ →+*ᵍ ℬ`, if `ρ` generates `𝒜₂` pointwise in the sense of
  `Stacks.AlgebraicGeometry.RelativeTwistRigidity.Generates`, then
  `U(ψ ∘ ρ) = U(ψ)` as opens of `Proj ℬ`. Only `≤` holds in general
  (`Stacks.AlgebraicGeometry.ProjShared.mapDomain_comp_le`).
* `RelativeProjMapDomain.SheafGradedAlgebraHom.projInclusionMap_preimage_chartDomain`:
  **the glueing datum of Tag 07ZG's open.** The inverse image of the chart domain over `V` under
  the transition morphism of a nested pair `U ⊆ V` of affine opens of the base is the chart
  domain over `U`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry HomogeneousIdeal
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeTwistRigidity

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain

attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w' w''

section Algebraic

variable {A₁ A₂ B : Type u} {σ₁ : Type w} {σ₂ : Type w'} {τ : Type w''}
  [CommRing A₁] [CommRing A₂] [CommRing B]
  [SetLike σ₁ A₁] [AddSubgroupClass σ₁ A₁]
  [SetLike σ₂ A₂] [AddSubgroupClass σ₂ A₂]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜₁ : ℕ → σ₁) (𝒜₂ : ℕ → σ₂) (ℬ : ℕ → τ)
  [GradedRing 𝒜₁] [GradedRing 𝒜₂] [GradedRing ℬ]

omit [AddSubgroupClass σ₁ A₁] [GradedRing 𝒜₁] in
/-- **Precomposition with a pointwise generating homomorphism does not change the domain of
definition.** If `ρ : 𝒜₁ →+*ᵍ 𝒜₂` generates `𝒜₂` pointwise, then for every `ψ : 𝒜₂ →+*ᵍ ℬ`
the domains of definition `U(ψ ∘ ρ)` and `U(ψ)` are equal as opens of `Proj ℬ`. -/
public theorem mapDomain_comp_eq_of_generates (ρ : 𝒜₁ →+*ᵍ 𝒜₂) (ψ : 𝒜₂ →+*ᵍ ℬ)
    (hgen : Generates ρ) :
    mapDomain 𝒜₁ ℬ (ψ.comp ρ) = mapDomain 𝒜₂ ℬ ψ := by
  refine le_antisymm (mapDomain_comp_le 𝒜₁ 𝒜₂ ℬ ρ ψ) fun z hz => ?_
  obtain ⟨k, a, hk, ha, haz⟩ := (mem_mapDomain_iff 𝒜₂ ℬ ψ z).mp hz
  obtain ⟨d, c, hd, hac⟩ :=
    hgen k ⟨a, ha⟩ ((mapHom 𝒜₂ ℬ ψ).base (⟨z, hz⟩ : (mapDomain 𝒜₂ ℬ ψ).toScheme))
  have hψd : ψ (ρ (d : A₁)) ∉ (z : ProjectiveSpectrum ℬ).asHomogeneousIdeal :=
    (notMem_mapHom_base_iff 𝒜₂ ℬ ψ (⟨z, hz⟩ : (mapDomain 𝒜₂ ℬ ψ).toScheme)
      (ρ.map_mem d.2)).mp hd
  refine (mem_mapDomain_iff 𝒜₁ ℬ (ψ.comp ρ) z).mpr ⟨k, (c : A₁), hk, c.2, ?_⟩
  have hprod : (ψ.comp ρ) (c : A₁) = ψ a * ψ (ρ (d : A₁)) := by
    change ψ (ρ (c : A₁)) = ψ a * ψ (ρ (d : A₁))
    rw [← map_mul, ← hac]
  rw [hprod]
  exact fun hmem => ((z : ProjectiveSpectrum ℬ).isPrime.mem_or_mem hmem).elim haz hψd

end Algebraic

section Relative

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S}

namespace SheafGradedAlgebraHom

variable (ψ : SheafGradedAlgebraHom A B)

/-- The open of the chart over an affine open `U` of the base on which `ψ` induces a morphism of
projective spectra: the domain of definition of the induced homomorphism of the graded rings of
sections over `U`. -/
@[ega "II 3.5.1" "partial"]
public def chartDomain (U : S.Opens) : (AlgebraicGeometry.Proj (B.grading U)).Opens :=
  mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U)

/-- **The glueing datum of Tag 07ZG's open subscheme.** For a nested pair `U ⊆ V` of affine
opens of the base, the inverse image of the chart domain over `V` under the transition morphism
of Tag 01NO is exactly the chart domain over `U`. -/
@[ega "II 3.5.1" "partial"]
public theorem projInclusionMap_preimage_chartDomain (U V : S.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    projInclusionMap B U V h hU hV ⁻¹ᵁ ψ.chartDomain V = ψ.chartDomain U := by
  have key : projInclusionMap B U V h hU hV ⁻¹ᵁ ψ.chartDomain V =
      mapDomain (A.grading V) (B.grading U) ((B.res h).comp (ψ.sectionHom V)) := by
    rw [← projInclusionMap_eq_comp B U V h hU hV, Scheme.Hom.comp_preimage,
      projMapData_hom, chartDomain,
      mapHom_preimage_mapDomain (A.grading V) (B.grading V) (B.grading U)
        (ψ.sectionHom V) (B.res h),
      ← Scheme.Hom.comp_preimage, projInclusionTopSection_ι B U V h hU hV]
    rfl
  rw [key, ψ.res_comp_sectionHom h,
    mapDomain_comp_eq_of_generates (A.grading V) (A.grading U) (B.grading U)
      (A.res h) (ψ.sectionHom U) (generates_res A U V h hU hV)]
  rfl

end SheafGradedAlgebraHom

end Relative

end Stacks.AlgebraicGeometry.RelativeProjMapDomain

end
