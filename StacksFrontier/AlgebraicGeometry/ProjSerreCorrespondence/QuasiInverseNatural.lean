module

public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.EssentiallySurjective

/-!
# `(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ≅ ℱ` is natural in `ℱ`

Let `A` be a graded ring and `X = Proj A`. The comparison

`ε_ℱ : (⨁_{n ≥ k} Γ(X, ℱ(n)))~ ⟶ ℱ`

of Tag 0B5I is the isomorphism `truncatedTwistedSectionsIso` once `X` is quasi-compact and `ℱ` is
quasi-coherent. This file proves that the comparison is natural in `ℱ`, and, over a Noetherian
graded ring, assembles it into the natural isomorphism

`ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))` composed with `M ↦ M̃`  `≅`  `𝟭 Coh(𝒪_X)`,

one of the two natural isomorphisms of the equivalence of Stacks 0BXF.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentQuasiInverseCounit`: the natural
  isomorphism `(ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))) ⋙ (M ↦ M̃) ≅ 𝟭 Coh(𝒪_X)`.

## Main results

* `ProjSheafFunctoriality.associatedModuleSheafTruncationAboveIso_naturality`: the isomorphism
  `(M_{≥ k})~ ≅ M̃` is natural in the graded module.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.truncatedTwistedSectionsComparison_naturality`:
  the comparison `(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ⟶ ℱ` is natural in `ℱ`, with no hypothesis on `X` or `ℱ`.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedGlobalSectionsGrading
  twistedGlobalSectionsModule twistedSectionsLinearMap
  isTwistedSectionsSMul_twistedGlobalSectionsModule)
open Stacks.AlgebraicGeometry.ProjTwistComparison (twistedSectionsMap_mem_grading
  twistedGlobalSectionsAssociatedSheafMap)
open Stacks.AlgebraicGeometry.ProjTwistIntegerComparison (integerComparison
  integerComparison_naturality)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule
open scoped Stacks.GradedLocalization

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

section TruncationNatural

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {M N : Type u} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  {τ υ : Type*} [SetLike τ M] [AddSubgroupClass τ M] [SetLike υ N] [AddSubgroupClass υ N]
  (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
  (𝒩 : ℤ → υ) [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩]

/-- The isomorphism `(M_{≥ k})~ ≅ M̃` is natural in the graded module: for a degree-preserving
linear map `φ : M ⟶ N`, it intertwines the map induced by `φ` on the sheaves associated with the
truncations `M_{≥ k} ⟶ N_{≥ k}` and the map `M̃ ⟶ Ñ` associated with `φ`. -/
public theorem associatedModuleSheafTruncationAboveIso_naturality
    (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (k : ℤ) :
    associatedModuleSheafMap 𝒮 (Stacks.GradedModule.truncationAboveGrading 𝒮 𝒨 k)
          (Stacks.GradedModule.truncationAboveGrading 𝒮 𝒩 k)
          (truncationAboveMap 𝒮 𝒨 𝒩 φ hφ k)
          (truncationAboveMap_mem_grading 𝒮 𝒨 𝒩 φ hφ k) ≫
        (associatedModuleSheafTruncationAboveIso 𝒮 𝒩 k).hom =
      (associatedModuleSheafTruncationAboveIso 𝒮 𝒨 k).hom ≫
        associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ := by
  have key : ∀ (L L' : ↥(Stacks.GradedModule.truncationAbove 𝒮 𝒨 k) →ₗ[S] N)
      (hL : ∀ i (m : ↥(Stacks.GradedModule.truncationAbove 𝒮 𝒨 k)),
        m ∈ Stacks.GradedModule.truncationAboveGrading 𝒮 𝒨 k i → L m ∈ 𝒩 i)
      (hL' : ∀ i (m : ↥(Stacks.GradedModule.truncationAbove 𝒮 𝒨 k)),
        m ∈ Stacks.GradedModule.truncationAboveGrading 𝒮 𝒨 k i → L' m ∈ 𝒩 i),
      L = L' →
        associatedModuleSheafMap 𝒮 (Stacks.GradedModule.truncationAboveGrading 𝒮 𝒨 k) 𝒩 L hL =
          associatedModuleSheafMap 𝒮 (Stacks.GradedModule.truncationAboveGrading 𝒮 𝒨 k) 𝒩
            L' hL' := by
    rintro L L' hL hL' rfl
    rfl
  rw [associatedModuleSheafTruncationAboveIso_hom, associatedModuleSheafTruncationAboveIso_hom,
    ← associatedModuleSheafMap_comp, ← associatedModuleSheafMap_comp]
  exact key _ _ _ _ (LinearMap.ext fun x => coe_truncationAboveMap 𝒮 𝒨 𝒩 φ hφ k x)

end TruncationNatural

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

section Comparison

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The comparison `(⨁_{n ≥ k} Γ(X, ℱ(n)))~ ⟶ ℱ`, written as the truncation isomorphism
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafTruncationAboveIso` followed
by the comparison `integerComparison` of Tag 0B5I, is natural in `ℱ`. No hypothesis on `X` or `ℱ`
is needed. -/
public theorem truncatedTwistedSectionsComparison_naturality
    {F G : SheafOfModules.{u} (projRingSheaf 𝒮)} (ψ : F ⟶ G) (k : ℤ) :
    letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
    letI := (twistedGlobalSectionsModule 𝒮 G).moduleInst
    letI := (twistedGlobalSectionsModule 𝒮 G).gradedSMul
    associatedModuleSheafMap 𝒮
          (truncationAboveGrading 𝒮 (twistedGlobalSectionsGrading 𝒮 F) k)
          (truncationAboveGrading 𝒮 (twistedGlobalSectionsGrading 𝒮 G) k)
          (truncationAboveMap 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
            (twistedGlobalSectionsGrading 𝒮 G)
            (twistedSectionsLinearMap 𝒮
              (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F
                (twistedGlobalSectionsModule 𝒮 F))
              (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 G
                (twistedGlobalSectionsModule 𝒮 G)) ψ)
            (twistedSectionsMap_mem_grading 𝒮 ψ) k)
          (truncationAboveMap_mem_grading 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
            (twistedGlobalSectionsGrading 𝒮 G) _ (twistedSectionsMap_mem_grading 𝒮 ψ) k) ≫
        ((associatedModuleSheafTruncationAboveIso 𝒮
              (twistedGlobalSectionsGrading 𝒮 G) k).hom ≫
          integerComparison 𝒮 G (twistedGlobalSectionsModule 𝒮 G)) =
      ((associatedModuleSheafTruncationAboveIso 𝒮
            (twistedGlobalSectionsGrading 𝒮 F) k).hom ≫
        integerComparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F)) ≫ ψ := by
  let := (twistedGlobalSectionsModule 𝒮 F).moduleInst
  let := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
  let := (twistedGlobalSectionsModule 𝒮 G).moduleInst
  let := (twistedGlobalSectionsModule 𝒮 G).gradedSMul
  have h1 := associatedModuleSheafTruncationAboveIso_naturality 𝒮
    (twistedGlobalSectionsGrading 𝒮 F) (twistedGlobalSectionsGrading 𝒮 G)
    (twistedSectionsLinearMap 𝒮
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F (twistedGlobalSectionsModule 𝒮 F))
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 G (twistedGlobalSectionsModule 𝒮 G))
      ψ) (twistedSectionsMap_mem_grading 𝒮 ψ) k
  have h2 : associatedModuleSheafMap 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
        (twistedGlobalSectionsGrading 𝒮 G)
        (twistedSectionsLinearMap 𝒮
          (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F
            (twistedGlobalSectionsModule 𝒮 F))
          (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 G
            (twistedGlobalSectionsModule 𝒮 G)) ψ)
        (twistedSectionsMap_mem_grading 𝒮 ψ) ≫
      integerComparison 𝒮 G (twistedGlobalSectionsModule 𝒮 G) =
    integerComparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F) ≫ ψ :=
    integerComparison_naturality 𝒮 (twistedGlobalSectionsModule 𝒮 F)
      (twistedGlobalSectionsModule 𝒮 G) ψ
  exact (Category.assoc _ _ _).symm.trans
    ((h1 =≫ integerComparison 𝒮 G (twistedGlobalSectionsModule 𝒮 G)).trans
      ((Category.assoc _ _ _).trans
        (((associatedModuleSheafTruncationAboveIso 𝒮
              (twistedGlobalSectionsGrading 𝒮 F) k).hom ≫= h2).trans
          (Category.assoc _ _ _).symm)))

end Comparison

/-! ### The natural isomorphism on `Coh(𝒪_X)` -/

section Counit

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] [IsNoetherianRing S]

/-- The natural isomorphism `(ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))) ⋙ (M ↦ M̃) ≅ 𝟭 Coh(𝒪_X)` on
`X = Proj A`, for a Noetherian graded ring `A`: the counit of the equivalence of Stacks 0BXF. -/
public def coherentQuasiInverseCounit (k : ℤ) :
    coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 k ⋙ coherentAssociatedSheafFunctor.{u, u} 𝒮 ≅
      𝟭 (_root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮)) :=
  NatIso.ofComponents (fun F => coherentTruncatedTwistedSectionsObj_iso 𝒮 k F) <| by
    intro F G ψ
    exact ObjectProperty.hom_ext _
      (truncatedTwistedSectionsComparison_naturality 𝒮 ψ.hom k)

end Counit

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
