module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonCanonical.ChainMap
import all StacksFrontier.Cotangent.StandardResolutionFrobeniusHomotopy

/-!
# The comparison map on `H^{-2}`

This file proves that the comparison map of complexes `Algebra.Presentation.lsChainMap`
`L_{B/A} → L` is an isomorphism on `H^{-2}` (Remarks 09D5 and 09D6 of the Stacks Project):
every `2`-cycle of `L_{B/A}` is cohomologous to `1 ⊗ dg` with `g ∈ J₂` and
`d₀ g - d₁ g + d₂ g ∈ J₁²`, and on such a `g` the comparison is `λ(d₀ g - d₁ g + d₂ g)`.

## Main results

* `Algebra.Presentation.isIso_homologyMap_lsChainMap_negTwo`: `lsChainMap` is an isomorphism on
  `H^{-2}`.

## References

* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TensorProduct KaehlerDifferential
open Stacks.Cotangent

universe u v w

namespace Algebra.Presentation

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
variable {X T : Type w} (P : Algebra.Presentation A B X T)

local notation "𝒫" => (CommAlgCat.standardResolution A (CommAlgCat.of A B))

/-! ### `I` acts trivially on relations -/

/-- Elements of `F/TrivRel` with the same image in `P` have the same product with any `a ∈ I`. -/
theorem ker_smul_eq_of_freeQuotientRelationMap_eq {a : P.Ring} (ha : a ∈ P.ker)
    {m m' : freeQuotient P} (h : freeQuotientRelationMap P m = freeQuotientRelationMap P m') :
    a • m = a • m' := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ m
  obtain ⟨u', rfl⟩ := Submodule.mkQ_surjective _ m'
  exact ker_smul_mk_eq P ha h

/-- Every element of `I` acts as zero on `Rel/TrivRel`. -/
theorem ker_smul_relationQuotient {a : P.Ring} (ha : a ∈ P.ker) (q : relationQuotient P) :
    a • q = 0 :=
  Module.mem_annihilator.1 (relationKer_le_annihilator P ha) q

/-- `λ(0) = 0`. -/
theorem lsBiderivation_zero : P.lsBiderivation 0 = 0 := by
  have := P.lsBiderivation_add 0 0
  rw [add_zero] at this
  exact add_eq_left.1 this.symm

/-- `λ(-x) = -λ(x)`. -/
theorem lsBiderivation_neg (x : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsBiderivation (-x) = -P.lsBiderivation x := by
  have := P.lsBiderivation_add (-x) x
  rw [neg_add_cancel, lsBiderivation_zero, eq_comm, add_eq_zero_iff_eq_neg] at this
  exact this

/-! ### The section `ψ` on augmentation ideals -/

/-- `ψ : P₀ → P` maps the augmentation ideal `J₀` into `I`. -/
theorem lsSection_mem_ker {p : (𝒫).left.obj (op ⦋0⦌)}
    (hp : p ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋0⦌)) :
    P.lsSection.toRingHom p ∈ P.ker := by
  show algebraMap P.Ring B (P.lsSection p) = 0
  rw [algebraMap_lsSection]
  exact hp

/-- `λ(([a] - [0])([b] - [0])) = ψ(a) λ([b] - [0])` for `a, b ∈ J₀`. -/
theorem lsBiderivation_contract_mul (a b : (𝒫).left.obj (op ⦋0⦌))
    (hb : b ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋0⦌)) :
    P.lsBiderivation (CommAlgCat.standardResolutionContract A _ 0 a *
        CommAlgCat.standardResolutionContract A _ 0 b) =
      P.lsSection a • P.lsBiderivation (CommAlgCat.standardResolutionContract A _ 0 b) := by
  rw [lsBiderivation_mul, CommAlgCat.δ_zero_standardResolutionContract,
    CommAlgCat.δ_one_standardResolutionContract_zero A _ b hb, map_zero, zero_smul, add_zero]

/-- For `b ∈ J₀`, the image of `λ([b] - [0])` in `P` is `ψ(b)`. -/
theorem freeQuotientRelationMap_lsBiderivation_contract (b : (𝒫).left.obj (op ⦋0⦌))
    (hb : b ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋0⦌)) :
    freeQuotientRelationMap P (P.lsBiderivation (CommAlgCat.standardResolutionContract A _ 0 b)) =
      P.lsSection b := by
  rw [freeQuotientRelationMap_lsBiderivation, CommAlgCat.δ_zero_standardResolutionContract,
    CommAlgCat.δ_one_standardResolutionContract_zero A _ b hb, map_zero, sub_zero]

/-- On a finite sum of products of contractions, `λ` is `μ ∘ ψ`. -/
theorem lsBiderivation_sum_contract
    (S : Finset (CommAlgCat.augmentationIdealZero A (CommAlgCat.of A B) ×
      CommAlgCat.augmentationIdealZero A (CommAlgCat.of A B))) :
    P.lsBiderivation (∑ p ∈ S, CommAlgCat.standardResolutionContract A _ 0 p.1 *
        CommAlgCat.standardResolutionContract A _ 0 p.2) =
      kerTensorRelation P (idealTensorMap _ (fun _ ha => P.lsSection_mem_ker ha)
        (∑ p ∈ S, p.1 ⊗ₜ p.2)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [lsBiderivation_zero]
  | insert p S hp ih =>
    rw [Finset.sum_insert hp, Finset.sum_insert hp, lsBiderivation_add, ih, map_add, map_add,
      lsBiderivation_contract_mul _ _ _ p.2.2, idealTensorMap_tmul, kerTensorRelation_comm]
    congr 1
    obtain ⟨u, hu⟩ := exists_relationMap_eq P _ (P.lsSection_mem_ker p.2.2)
    rw [kerTensorRelation_tmul P _ _ u hu]
    refine ker_smul_eq_of_freeQuotientRelationMap_eq P (P.lsSection_mem_ker p.1.2) ?_
    rw [freeQuotientRelationMap_lsBiderivation_contract _ _ p.2.2, freeQuotientRelationMap_mk, hu]
    rfl

/-! ### `λ ∘ (d₀ - d₁ + d₂)` kills `J₂²` -/

/-- `λ(d₀ - d₁ + d₂)` vanishes on a product of two elements of `J₂`. -/
theorem lsRelation_mul_eq_zero {g h : (𝒫).left.obj (op ⦋2⦌)}
    (hg : g ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌))
    (hh : h ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌)) :
    P.lsRelation (g * h) = 0 := by
  have m : ∀ (i : Fin 2) (j : Fin 3) (x : (𝒫).left.obj (op ⦋2⦌)),
      x ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌) →
      P.lsSection ((𝒫).left.δ i ((𝒫).left.δ j x)) ∈ P.ker := fun i j x hx =>
    P.lsSection_mem_ker (CommAlgCat.delta_mem_augmentationIdeal A _ 0 i _
      (CommAlgCat.delta_mem_augmentationIdeal A _ 1 j x hx))
  rw [lsRelation_mul, ker_smul_relationQuotient P (m 0 0 g hg),
    ker_smul_relationQuotient P (m 1 2 h hh), add_zero]

/-- `λ(d₀ - d₁ + d₂)` vanishes on `J₂²`. -/
theorem lsRelation_eq_zero_of_mem_sq {u : (𝒫).left.obj (op ⦋2⦌)}
    (hu : u ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌) ^ 2) :
    P.lsRelation u = 0 := by
  rw [pow_two] at hu
  refine Submodule.mul_induction_on hu (fun g hg h hh => P.lsRelation_mul_eq_zero hg hh) ?_
  intro x y hx hy
  rw [lsRelation_add, hx, hy, add_zero]

/-- `λ` vanishes on `(d₀ - d₁ + d₂)(J₂²)`. -/
theorem lsBiderivation_boundaryOfSquares {z : (𝒫).left.obj (op ⦋1⦌)}
    (hz : z ∈ CommAlgCat.boundaryOfSquares A (CommAlgCat.of A B)) :
    P.lsBiderivation z = 0 := by
  obtain ⟨u, hu, rfl⟩ := hz
  rw [← relationQuotientToFree_lsRelation, P.lsRelation_eq_zero_of_mem_sq hu, map_zero]

/-! ### The two homotopy invariances -/

/-- The `A`-algebra map `φ : P → P₀`, `x_i ↦ [x_i ↦ b]`, over `B`. -/
def lsRetraction : P.Ring →ₐ[A] (𝒫).left.obj (op ⦋0⦌) :=
  MvPolynomial.aeval fun i => CommAlgCat.standardResolutionVarZero A (CommAlgCat.of A B) (P.val i)

/-- `φ : P → P₀` is compatible with the maps to `B`. -/
theorem augmentation_lsRetraction (x : P.Ring) :
    (𝒫).hom.app (op ⦋0⦌) (P.lsRetraction x) = algebraMap P.Ring B x := by
  induction x using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    exact ((𝒫).hom.app (op ⦋0⦌)).hom.commutes a
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, lsRetraction, MvPolynomial.aeval_X,
      CommAlgCat.standardResolution_augmentation_varZero, P.algebraMap_apply (MvPolynomial.X i),
      MvPolynomial.aeval_X]

/-- `φ : P → P₀` maps `I` into the augmentation ideal `J₀`. -/
theorem lsRetraction_mem {x : P.Ring} (hx : x ∈ P.ker) :
    P.lsRetraction.toRingHom x ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋0⦌) := by
  show (𝒫).hom.app (op ⦋0⦌) (P.lsRetraction x) = 0
  rw [augmentation_lsRetraction]
  exact hx

/-- **`μ` is invariant under the endomorphism `ψ ∘ φ` of `P` over `B`.** -/
theorem kerTensorRelation_idealTensorMap_lsSection_comp (ξ : P.ker ⊗[P.Ring] P.ker)
    (hξ : idealTensorMul P.ker ξ = 0) :
    kerTensorRelation P (idealTensorMap (P.lsSection.comp P.lsRetraction).toRingHom
      (fun _ ha => P.lsSection_mem_ker (P.lsRetraction_mem ha)) ξ) = kerTensorRelation P ξ := by
  have h := idealTensorMap_sub_mem_antisymm (P.lsSection.comp P.lsRetraction) (AlgHom.id A P.Ring)
    (fun a ha => P.lsSection_mem_ker (P.lsRetraction_mem ha)) (fun a ha => ha)
    (fun i => by
      show algebraMap P.Ring B _ = 0
      rw [map_sub, AlgHom.comp_apply, algebraMap_lsSection, augmentation_lsRetraction,
        AlgHom.id_apply, sub_self]) ξ hξ
  have h' := kerTensorRelation_antisymm P h
  rw [map_sub, sub_eq_zero] at h'
  rw [h']
  exact congrArg _ (idealTensorMap_id _ ξ)

/-- **`H̄` is invariant under the endomorphism `φ ∘ ψ` of `P₀` over `B`.** -/
theorem squareClass_idealTensorMap_lsRetraction_comp
    (ξ : CommAlgCat.augmentationIdealZero A (CommAlgCat.of A B) ⊗[(𝒫).left.obj (op ⦋0⦌)]
      CommAlgCat.augmentationIdealZero A (CommAlgCat.of A B))
    (hξ : idealTensorMul _ ξ = 0) :
    CommAlgCat.squareClass A _ (idealTensorMap (P.lsRetraction.comp P.lsSection).toRingHom
        (fun _ ha => P.lsRetraction_mem (P.lsSection_mem_ker ha)) ξ) =
      CommAlgCat.squareClass A _ ξ := by
  let e := CommAlgCat.standardResolutionZeroAlgEquiv A (CommAlgCat.of A B)
  let φ₁ := P.lsRetraction.comp P.lsSection
  let V : CommAlgCat.of A B → (𝒫).left.obj (op ⦋0⦌) :=
    CommAlgCat.standardResolutionVarZero A (CommAlgCat.of A B)
  let E : (𝒫).left.obj (op ⦋0⦌) →ₐ[A] (𝒫).left.obj (op ⦋1⦌) :=
    (MvPolynomial.aeval fun b => CommAlgCat.standardResolutionX A _ 0 (φ₁ (V b)) -
      CommAlgCat.standardResolutionX A _ 0 (V b) + (𝒫).left.σ 0 (V b)).comp e.toAlgHom
  have hs0 : ∀ r, (𝒫).left.δ (0 : Fin 2) ((𝒫).left.σ 0 r) = r := fun r =>
    CommAlgCat.apply_of_comp_eq ((𝒫).left.δ_comp_σ_self (i := (0 : Fin 1))) r
  have hs1 : ∀ r, (𝒫).left.δ (1 : Fin 2) ((𝒫).left.σ 0 r) = r := fun r =>
    CommAlgCat.apply_of_comp_eq ((𝒫).left.δ_comp_σ_succ (i := (0 : Fin 1))) r
  have hext : ∀ f g : (𝒫).left.obj (op ⦋0⦌) →ₐ[A] (𝒫).left.obj (op ⦋0⦌),
      (∀ b, f (V b) = g (V b)) → ∀ a, f a = g a := fun f g h a => by
    have : f.comp e.symm.toAlgHom = g.comp e.symm.toAlgHom :=
      MvPolynomial.algHom_ext fun b => h b
    simpa using congrArg (fun k => k (e a)) this
  have hE₀ : ∀ a, (𝒫).left.δ 0 (E a) = φ₁ a := hext (((𝒫).left.δ 0).hom.comp E) φ₁ fun b => by
    show (𝒫).left.δ 0 (E (e.symm (MvPolynomial.X b))) = _
    simp only [E, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.apply_symm_apply, MvPolynomial.aeval_X, map_add, map_sub,
      CommAlgCat.standardResolution_δ_zero_X, hs0]
    abel
  have hE₁ : ∀ a, (𝒫).left.δ 1 (E a) = a := hext (((𝒫).left.δ 1).hom.comp E) (AlgHom.id A _)
    fun b => by
    show (𝒫).left.δ 1 (E (e.symm (MvPolynomial.X b))) = _
    simp only [E, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.apply_symm_apply, MvPolynomial.aeval_X, map_add, map_sub,
      CommAlgCat.standardResolution_δ_one_X, hs1, AlgHom.id_apply]
    have : CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) (φ₁ (V b)) =
        CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) (V b) := by
      show (𝒫).hom.app (op ⦋0⦌) (P.lsRetraction (P.lsSection (V b))) =
        (𝒫).hom.app (op ⦋0⦌) (V b)
      rw [augmentation_lsRetraction, algebraMap_lsSection]
    rw [this, sub_self, zero_add]
  have key := CommAlgCat.squareClass_idealTensorMap_eq_of_homotopy A (CommAlgCat.of A B)
    φ₁ (AlgHom.id A _) E hE₀ hE₁ (fun a ha => P.lsRetraction_mem (P.lsSection_mem_ker ha))
    (fun a ha => ha) ξ hξ
  rw [key]
  exact congrArg _ (idealTensorMap_id _ ξ)

/-! ### Cycles of `L_{B/A}` in degree `-2` -/

local notation "𝕂" => (CommAlgCat.cotangentComplex A (CommAlgCat.of A B))
local notation "𝓔" n => (CommAlgCat.standardResolutionExtension A (CommAlgCat.of A B) n)

/-- `d₀ g - d₁ g + d₂ g` has the same augmentation as `g`. -/
private theorem augmentation_faceSumTwo (g : (𝒫).left.obj (op ⦋2⦌)) :
    (𝒫).hom.app (op ⦋1⦌) (CommAlgCat.faceSumTwo A _ g) = (𝒫).hom.app (op ⦋2⦌) g := by
  rw [CommAlgCat.faceSumTwo_apply, map_add, map_sub,
    CommAlgCat.standardResolution_augmentation_δ, CommAlgCat.standardResolution_augmentation_δ,
    CommAlgCat.standardResolution_augmentation_δ, sub_self, zero_add]

omit P in
/-- **Remark 09D5 on elements**, on the Moore complex of `Ω_{P_•/A} ⊗ B`: every `2`-cycle is
cohomologous to `1 ⊗ dg` for some `g ∈ J₂` with `d₀ g - d₁ g + d₂ g ∈ J₁²`. -/
theorem exists_conormal_representative
    (m : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2)
    (hm : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 2 1 m = 0) :
    ∃ g : (𝒫).left.obj (op ⦋2⦌),
      g ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌) ∧
      CommAlgCat.faceSumTwo A _ g ∈
        CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋1⦌) ^ 2 ∧
      ∃ w : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 3,
        m = @HAdd.hAdd ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2)
          ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2) _ _
            (CommAlgCat.cotangentTermDifferential A _ (op ⦋2⦌) g)
          ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 w) := by
  have : IsIso (HomologicalComplex.homologyMap
      (conormalToCotangentMoore A (CommAlgCat.of A B)) 2) :=
    isIso_homologyMap_conormalToCotangentMoore A (CommAlgCat.of A B) 2 le_rfl
  obtain ⟨c, hc, w, hw⟩ := HomologicalComplex.exists_of_epi_homologyMap
    (conormalToCotangentMoore A (CommAlgCat.of A B)) 3 2 1 (by simp) (by simp) m hm
  obtain ⟨g, hg, rfl⟩ : ∃ (g : (𝒫).left.obj (op ⦋2⦌))
      (hg : g ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌)),
      Algebra.Extension.Cotangent.mk (P := conormalExtension A (CommAlgCat.of A B) (op ⦋2⦌))
        ⟨g, hg⟩ = c := by
    obtain ⟨⟨g, hg⟩, h⟩ := Algebra.Extension.Cotangent.mk_surjective c
    exact ⟨g, hg, h⟩
  refine ⟨g, hg, ?_, w, hw⟩
  rw [conormalMooreComplex_d_two_one] at hc
  have hz : CommAlgCat.faceSumTwo A _ g ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B)
      (op ⦋1⦌) := by
    show (𝒫).hom.app (op ⦋1⦌) _ = 0
    rw [augmentation_faceSumTwo]
    exact hg
  have e : ((conormalSimplicialModule A (CommAlgCat.of A B)).δ (0 : Fin 3) -
      (conormalSimplicialModule A (CommAlgCat.of A B)).δ (1 : Fin 3) +
      (conormalSimplicialModule A (CommAlgCat.of A B)).δ (2 : Fin 3))
        (Algebra.Extension.Cotangent.mk
          (P := conormalExtension A (CommAlgCat.of A B) (op ⦋1 + 1⦌)) ⟨g, hg⟩) =
      Algebra.Extension.Cotangent.mk
        (P := conormalExtension A (CommAlgCat.of A B) (op ⦋1⦌)) ⟨_, hz⟩ :=
    conormalDelta_alt_mk A (CommAlgCat.of A B) ⟨g, hg⟩
      ⟨_, CommAlgCat.delta_mem_augmentationIdeal A _ 1 0 g hg⟩
      ⟨_, CommAlgCat.delta_mem_augmentationIdeal A _ 1 1 g hg⟩
      ⟨_, CommAlgCat.delta_mem_augmentationIdeal A _ 1 2 g hg⟩ ⟨_, hz⟩ rfl rfl rfl rfl
  have e' := e.symm.trans hc
  have e'' := (Algebra.Extension.Cotangent.mk_eq_zero_iff _).1 e'
  show CommAlgCat.faceSumTwo A _ g ∈ (conormalExtension A (CommAlgCat.of A B) (op ⦋1⦌)).ker ^ 2
  exact e''

local notation "τ" n => CommAlgCat.cotangentTermDifferential A (CommAlgCat.of A B) (op ⦋n⦌)

omit P in
/-- The differential `p ↦ 1 ⊗ dp` into the terms of `L_{B/A}` is additive on differences. -/
theorem cotangentTermDifferential_sub (n : ℕ) (p q : (𝒫).left.obj (op ⦋n⦌)) :
    (τ n) (p - q) = (τ n) p - (τ n) q := by
  have := CommAlgCat.cotangentTermDifferential_add A (CommAlgCat.of A B) (op ⦋n⦌) (p - q) q
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

omit P in
/-- `1 ⊗ du = 0` for `u ∈ J_n²`. -/
theorem cotangentTermDifferential_eq_zero_of_mem_sq (n : ℕ) {u : (𝒫).left.obj (op ⦋n⦌)}
    (hu : u ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋n⦌) ^ 2) :
    (τ n) u = 0 := by
  rw [pow_two] at hu
  refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [CommAlgCat.cotangentTermDifferential_mul]
    show (𝒫).hom.app (op ⦋n⦌) a • _ + (𝒫).hom.app (op ⦋n⦌) b • _ = 0
    rw [show (𝒫).hom.app (op ⦋n⦌) a = 0 from ha, show (𝒫).hom.app (op ⦋n⦌) b = 0 from hb,
      zero_smul, zero_smul, add_zero]
  · rw [CommAlgCat.cotangentTermDifferential_add, hx, hy, add_zero]

omit P in
/-- The Moore differential sends `1 ⊗ dp` to `1 ⊗ d(d₀ p - d₁ p + d₂ p)` for `p ∈ P₂`. -/
theorem cotangentMooreComplex_d_two_one_differential (p : (𝒫).left.obj (op ⦋2⦌)) :
    (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 2 1 ((τ 2) p) =
      (τ 1) (CommAlgCat.faceSumTwo A _ p) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_smul, one_smul,
    even_two, Even.neg_pow, one_pow, ModuleCat.hom_add, ModuleCat.hom_neg]
  have hδ : ∀ i : Fin 3, ((CommAlgCat.cotangentSimplicialModule A (CommAlgCat.of A B)).object.δ i)
      ((τ 2) p) = (τ 1) ((𝒫).left.δ i p) := fun i =>
    CommAlgCat.cotangentSimplicialModule_map_differential A _ _ p
  show ((CommAlgCat.cotangentSimplicialModule A (CommAlgCat.of A B)).object.δ 0) ((τ 2) p) +
      -((CommAlgCat.cotangentSimplicialModule A (CommAlgCat.of A B)).object.δ 1) ((τ 2) p) +
      ((CommAlgCat.cotangentSimplicialModule A (CommAlgCat.of A B)).object.δ 2) ((τ 2) p) = _
  rw [hδ, hδ, hδ, CommAlgCat.faceSumTwo_apply, CommAlgCat.cotangentTermDifferential_add,
    cotangentTermDifferential_sub, sub_eq_add_neg]
  rfl

omit P in
/-- The Moore differential sends `1 ⊗ dp` to `1 ⊗ d(d₀ p - d₁ p + d₂ p - d₃ p)` for `p ∈ P₃`. -/
theorem cotangentMooreComplex_d_three_two_differential (p : (𝒫).left.obj (op ⦋3⦌)) :
    (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 ((τ 3) p) =
      (τ 2) ((𝒫).left.δ (0 : Fin 4) p - (𝒫).left.δ (1 : Fin 4) p +
        (𝒫).left.δ (2 : Fin 4) p - (𝒫).left.δ (3 : Fin 4) p) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_four]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul]
  have hδ : ∀ i : Fin 4, ((CommAlgCat.cotangentSimplicialModule A (CommAlgCat.of A B)).object.δ i)
      ((τ 3) p) = (τ 2) ((𝒫).left.δ i p) := fun i =>
    CommAlgCat.cotangentSimplicialModule_map_differential A _ _ p
  show (-1 : ℤ) ^ (0 : ℕ) • ((CommAlgCat.cotangentSimplicialModule A _).object.δ 0) ((τ 3) p) +
      (-1 : ℤ) ^ (1 : ℕ) • ((CommAlgCat.cotangentSimplicialModule A _).object.δ 1) ((τ 3) p) +
      (-1 : ℤ) ^ (2 : ℕ) • ((CommAlgCat.cotangentSimplicialModule A _).object.δ 2) ((τ 3) p) +
      (-1 : ℤ) ^ (3 : ℕ) • ((CommAlgCat.cotangentSimplicialModule A _).object.δ 3) ((τ 3) p) = _
  rw [hδ, hδ, hδ, hδ, cotangentTermDifferential_sub, CommAlgCat.cotangentTermDifferential_add,
    cotangentTermDifferential_sub]
  simp only [pow_zero, pow_one, Even.neg_pow, even_two, one_pow,
    Odd.neg_pow (by decide : Odd 3)]
  abel

omit P in
/-- On elements, the differential of `L_{B/A}` from degree `-2` to degree `-1` is the Moore
differential `d₂₁`. -/
theorem cotangentComplex_d_negTwo_negOne_apply (m : (𝕂).X (-2)) :
    (𝕂).d (-2) (-1) m = (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 1).inv
      ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 2 1
        ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).hom m)) :=
  ConcreteCategory.congr_hom (CommAlgCat.cotangentComplex_d A (CommAlgCat.of A B) 1) m

omit P in
/-- On elements, the differential of `L_{B/A}` from degree `-3` to degree `-2` is the Moore
differential `d₃₂`. -/
theorem cotangentComplex_d_negThree_negTwo_apply (m : (𝕂).X (-3)) :
    (𝕂).d (-3) (-2) m = (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).inv
      ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2
        ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 3).hom m)) :=
  ConcreteCategory.congr_hom (CommAlgCat.cotangentComplex_d A (CommAlgCat.of A B) 2) m

omit P in
/-- The differential of `L_{B/A}` from degree `-3` to degree `-2`, applied to the image of an
element of the Moore complex, is the image of its Moore differential. -/
theorem cotangentComplex_d_negThree_negTwo_inv
    (y : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 3) :
    (𝕂).d (-3) (-2) ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 3).inv y) =
      (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).inv
        ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 y) := by
  have h : (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 3).inv ≫ (𝕂).d (-3) (-2) =
      (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 ≫
        (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).inv :=
    (congrArg (fun f => (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 3).inv ≫
      f) (CommAlgCat.cotangentComplex_d A (CommAlgCat.of A B) 2)).trans
        (Iso.inv_hom_id_assoc _ _)
  exact ConcreteCategory.congr_hom h y

omit P in
/-- `d₀` and `d₁` agree on `d₀ g - d₁ g + d₂ g` for `g ∈ P₂`. -/
theorem δ_faceSumTwo (g : (𝒫).left.obj (op ⦋2⦌)) :
    (𝒫).left.δ (0 : Fin 2) (CommAlgCat.faceSumTwo A _ g) =
      (𝒫).left.δ (1 : Fin 2) (CommAlgCat.faceSumTwo A _ g) := by
  obtain ⟨h1, h2, h3⟩ := δ_δ_identities (A := A) (B := B) g
  rw [CommAlgCat.faceSumTwo_apply]
  simp only [map_add, map_sub, h1, h2, h3]
  abel

/-- For an extension `R → S` with kernel `I` and `u ∈ I²`, `1 ⊗ du = 0` in `S ⊗ Ω`. -/
theorem _root_.Algebra.Extension.tmul_D_eq_zero_of_mem_sq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (E : Algebra.Extension R S) {u : E.Ring} (hu : u ∈ E.ker ^ 2) :
    (1 : S) ⊗ₜ[E.Ring] D R E.Ring u = 0 := by
  have h := E.cotangentComplex_mk ⟨u, Ideal.pow_le_self two_ne_zero hu⟩
  rw [(Algebra.Extension.Cotangent.mk_eq_zero_iff _).2 hu, map_zero] at h
  exact h.symm

/-! ### Surjectivity on `H^{-2}` -/

/-- Every relation `r` with coefficients in `I` is `λ(d₀ g - d₁ g + d₂ g)` modulo `TrivRel` for
some `g ∈ J₂` with `d₀ g - d₁ g + d₂ g ∈ J₁²`. -/
theorem exists_cycle_of_relation (r : T →₀ P.Ring) (hr : relationMap P r = 0)
    (hrI : ∀ t, r t ∈ P.ker) :
    ∃ g : (𝒫).left.obj (op ⦋2⦌),
      g ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌) ∧
      CommAlgCat.faceSumTwo A _ g ∈
        CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋1⦌) ^ 2 ∧
      P.lsBiderivation (CommAlgCat.faceSumTwo A _ g) = Submodule.Quotient.mk r := by
  obtain ⟨ξ, hξm, hξμ⟩ := exists_kerTensorRelation_eq P r hr hrI
  set ξ' := idealTensorMap P.lsRetraction.toRingHom (fun a ha => P.lsRetraction_mem ha) ξ
  have hξ' : idealTensorMul _ ξ' = 0 := by
    rw [idealTensorMul_idealTensorMap, hξm, map_zero]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ξ'
  obtain ⟨z, hz⟩ : ∃ z, z = ∑ p ∈ S,
      CommAlgCat.standardResolutionContract A (CommAlgCat.of A B) 0 p.1 *
        CommAlgCat.standardResolutionContract A (CommAlgCat.of A B) 0 p.2 := ⟨_, rfl⟩
  have hzJ : z ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋1⦌) ^ 2 := by
    rw [hz]
    refine Ideal.sum_mem _ fun p _ => ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (CommAlgCat.standardResolutionContract_mem A _ 0 _ p.1.2)
      (CommAlgCat.standardResolutionContract_mem A _ 0 _ p.2.2)
  have hδ : (𝒫).left.δ (0 : Fin 2) z - (𝒫).left.δ (1 : Fin 2) z = 0 := by
    have h0 : (𝒫).left.δ (0 : Fin 2) z = idealTensorMul _ ξ' := by
      rw [hS, map_sum, hz, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, CommAlgCat.δ_zero_standardResolutionContract,
        CommAlgCat.δ_zero_standardResolutionContract, idealTensorMul_tmul]
    have h1 : (𝒫).left.δ (1 : Fin 2) z = 0 := by
      rw [hz, map_sum]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [map_mul, CommAlgCat.δ_one_standardResolutionContract_zero A _ _ p.2.2, mul_zero]
    rw [h0, h1, hξ', sub_zero]
  obtain ⟨g, hg⟩ := CommAlgCat.standardResolution_exists_of_delta_sub_delta_eq_zero A _ z hδ
  have hgz : CommAlgCat.faceSumTwo A _ g = z := hg
  refine ⟨g, ?_, hgz ▸ hzJ, ?_⟩
  · show (𝒫).hom.app (op ⦋2⦌) g = 0
    rw [← augmentation_faceSumTwo, hgz]
    exact Ideal.pow_le_self two_ne_zero hzJ
  · rw [hgz, hz, lsBiderivation_sum_contract, ← hS, ← hξμ,
      ← kerTensorRelation_idealTensorMap_lsSection_comp P ξ hξm]
    congr 1
    exact (idealTensorMap_comp _ _ _ _ ξ).trans (idealTensorMap_congr rfl _ _ ξ)

/-! ### The isomorphism on `H^{-2}` -/

/-- The component of the comparison in degree `-2` on an element of the cotangent space of
`P₂ → B` is `lsComponentTwo`. -/
theorem relationIso_hom_lsChainTwo_ulift (c : (𝓔 2).CotangentSpace) :
    (lichtenbaumSchlessingerComplex P).relationIso.hom
      (P.lsChainTwo (uliftUp.{u, v, w} (A := A) (B := B) (-2)
        ((cotangentDegreeIsoTwo (A := A) (B := B)).inv c))) =
      P.lsComponentTwo c := by
  rw [lsChainTwo_apply]
  exact congrArg _ (Iso.inv_hom_id_apply _ _)

omit P in
/-- On the cotangent space of `P₂ → B`, the differential of `L_{B/A}` from degree `-2` to
degree `-1` is `d₀ - d₁ + d₂`. -/
theorem cotangentComplex_d_negTwo_negOne_inv (c : (𝓔 2).CotangentSpace) :
    (𝕂).d (-2) (-1) ((cotangentDegreeIsoTwo (A := A) (B := B)).inv c) =
      (cotangentDegreeIsoOne (A := A) (B := B)).inv
        ((Algebra.Extension.CotangentSpace.map
        (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 0) -
        Algebra.Extension.CotangentSpace.map
        (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 1) +
        Algebra.Extension.CotangentSpace.map
        (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 2)) c) := by
  rw [cotangentComplex_d_negTwo_negOne', ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

omit P in
/-- The differential `g ↦ 1 ⊗ dg` into the terms of `L_{B/A}`, read in the cotangent space of
`P_n → B`, is `1 ⊗ dg`. -/
theorem eqToHom_cotangentTermDifferential (n : ℕ) (g : (𝒫).left.obj (op ⦋n⦌)) :
    eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) n) ((τ n) g) =
      (1 : B) ⊗ₜ[(𝓔 n).Ring] D A (𝓔 n).Ring g := rfl

omit P in
/-- `cotangentDegreeIsoTwo` is the identification with the Moore complex followed by the
identification of its term with the cotangent space of `P₂ → B`. -/
theorem cotangentDegreeIsoTwo_hom_apply (m : (𝕂).X (-2)) :
    (cotangentDegreeIsoTwo (A := A) (B := B)).hom m =
      eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 2)
        ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).hom m) := by
  rw [cotangentDegreeIsoTwo, Iso.trans_hom, ConcreteCategory.comp_apply, eqToIso.hom]

/-- Every `(-2)`-cycle of `L` is the image of a `(-2)`-cycle of `L_{B/A}` under the
comparison. -/
theorem lsSurj_negTwo (y : (lichtenbaumSchlessingerComplex P).complex.X (-2))
    (hy : (lichtenbaumSchlessingerComplex P).complex.d (-2) (-1) y = 0) :
    ∃ x : (cotangentComplexULift.{u, v, w} A B).X (-2),
      (cotangentComplexULift.{u, v, w} A B).d (-2) (-1) x = 0 ∧
        y = P.lsChainTwo x := by
  classical
  let _ := relationModule P
  set t := (lichtenbaumSchlessingerComplex P).relationIso.hom y with ht
  have hbd : relationBoundary P t = 0 := by
    rw [← lsComplex_d_negTwo_inv_apply, ht, Iso.hom_inv_id_apply, hy, map_zero]
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective (trivialRelations P) (relationBaseChangeEquiv P t)
  have hR : relationBoundaryR P (Submodule.mkQ (trivialRelations P) r) = 0 := by
    rw [hr]; exact hbd
  rw [relationBoundaryR_mk] at hR
  have hrI : ∀ t, (r : T →₀ P.Ring) t ∈ P.ker := fun i => by
    have := congrArg (fun z => TensorProduct.finsuppScalarRight P.Ring B B T z i) hR
    simp only [TensorProduct.finsuppScalarRight_apply_tmul_apply, Algebra.smul_def, mul_one,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this
  obtain ⟨g, hg, hgz, hgl⟩ := P.exists_cycle_of_relation r (LinearMap.mem_ker.1 r.2) hrI
  refine ⟨uliftUp.{u, v, w} (A := A) (B := B) (-2)
    ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).inv ((τ 2) g)), ?_, ?_⟩
  · apply ULift.ext
    rw [cotangentComplexULift_d_apply, uliftUp_down, cotangentComplex_d_negTwo_negOne_apply,
      Iso.inv_hom_id_apply, cotangentMooreComplex_d_two_one_differential,
      cotangentTermDifferential_eq_zero_of_mem_sq 1 hgz, map_zero]
    rfl
  · have hq : P.lsRelation g = Submodule.mkQ (trivialRelations P) r := by
      rw [lsRelation_eq_iff, Submodule.mkQ_apply, relationQuotientToFree_mk]
      exact hgl.symm
    have ht' : t = (1 : B) ⊗ₜ[P.Ring] Submodule.mkQ (trivialRelations P) r := by
      apply (relationBaseChangeEquiv P).injective
      rw [relationBaseChangeEquiv_tmul, hr]
    have e : (lichtenbaumSchlessingerComplex P).relationIso.hom
        (P.lsChainTwo (uliftUp.{u, v, w} (A := A) (B := B) (-2)
          ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).inv ((τ 2) g)))) =
        (lichtenbaumSchlessingerComplex P).relationIso.hom y := by
      rw [lsChainTwo_apply, uliftUp_down, cotangentDegreeIsoTwo_hom_apply, Iso.inv_hom_id_apply,
        eqToHom_cotangentTermDifferential, lsComponentTwo_tmul, lsDerivTwo, hq, ← ht, ht']
    have e' := congrArg (lichtenbaumSchlessingerComplex P).relationIso.inv e
    rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at e'
    exact e'.symm

omit P in
/-- Read in cotangent spaces, the Moore differential `d₃₂` of `L_{B/A}` is `d₀ - d₁ + d₂ - d₃`. -/
theorem eqToHom_cotangentMooreComplex_d_three_two
    (w : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 3) :
    eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 2)
        ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 w) =
      (Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 0) -
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 1) +
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 2) -
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 3))
        (eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 3) w) := by
  have h : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 ≫
      eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 2) =
      eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 3) ≫
        ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 0) -
          Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 1) +
          Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 2) -
          Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 3)) := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d, objD_two_eq, faceAsTermMap_eq_eqToHom,
      faceAsTermMap_eq_eqToHom, faceAsTermMap_eq_eqToHom, faceAsTermMap_eq_eqToHom,
      ← Preadditive.comp_sub, ← Preadditive.sub_comp, ← Preadditive.comp_add,
      ← Preadditive.add_comp, ← Preadditive.comp_sub, ← Preadditive.sub_comp]
    rfl
  exact ConcreteCategory.congr_hom h w

/-- A `(-2)`-cycle of `L_{B/A}` killed by the comparison is a boundary. -/
theorem lsInj_negTwo (x : (cotangentComplexULift.{u, v, w} A B).X (-2))
    (hx : (cotangentComplexULift.{u, v, w} A B).d (-2) (-1) x = 0) (hφ : P.lsChainTwo x = 0) :
    ∃ z : (cotangentComplexULift.{u, v, w} A B).X (-3),
      (cotangentComplexULift.{u, v, w} A B).d (-3) (-2) z = x := by
  let _ := relationModule P
  have hm : (𝕂).d (-2) (-1) x.down = 0 := by
    rw [← cotangentComplexULift_d_apply, hx]; rfl
  set m' := (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 2).hom x.down with hm'def
  have hm' : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 2 1 m' = 0 := by
    rw [cotangentComplex_d_negTwo_negOne_apply] at hm
    have hinj := (ModuleCat.mono_iff_injective
      (CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 1).inv).1 inferInstance
    exact hinj (hm.trans (map_zero _).symm)
  obtain ⟨g, hg, hz, w, hw⟩ := exists_conormal_representative m' hm'
  have h0 : P.lsComponentTwo ((1 : B) ⊗ₜ[(𝓔 2).Ring] D A (𝓔 2).Ring g) = 0 := by
    have e := congrArg (lichtenbaumSchlessingerComplex P).relationIso.hom hφ
    have hsplit : eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 2)
        (@HAdd.hAdd ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2)
          ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2) _ _
            ((τ 2) g) ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 w)) =
        eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 2) ((τ 2) g) +
        eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 2)
          ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 w) := map_add _ _ _
    have h2 := LinearMap.congr_fun P.lsComponent_square_two
      (eqToHom (CommAlgCat.cotangentTerm_eq_cotangentSpace A (CommAlgCat.of A B) 3) w)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h2
    rw [lsChainTwo_apply, cotangentDegreeIsoTwo_hom_apply, ← hm'def, hw, hsplit, map_add,
      eqToHom_cotangentMooreComplex_d_three_two, h2, add_zero, map_zero,
      eqToHom_cotangentTermDifferential] at e
    exact e
  rw [lsComponentTwo_tmul, lsDerivTwo] at h0
  have hrel : P.lsRelation g = 0 := by
    have := congrArg (relationBaseChangeEquiv P) h0
    rwa [relationBaseChangeEquiv_tmul, map_zero] at this
  have hlz : P.lsBiderivation (CommAlgCat.faceSumTwo A _ g) = 0 := by
    rw [← relationQuotientToFree_lsRelation, hrel, map_zero]
  obtain ⟨ξ, hξm, hξs⟩ := CommAlgCat.exists_squareClass_eq A (CommAlgCat.of A B)
    (CommAlgCat.faceSumTwo A _ g) hz
  rw [δ_faceSumTwo, sub_self] at hξm
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ξ
  have hcls : QuotientAddGroup.mk (s := CommAlgCat.boundaryOfSquares A (CommAlgCat.of A B))
      (∑ p ∈ S, CommAlgCat.standardResolutionContract A (CommAlgCat.of A B) 0 p.1 *
        CommAlgCat.standardResolutionContract A (CommAlgCat.of A B) 0 p.2) =
      QuotientAddGroup.mk (CommAlgCat.faceSumTwo A _ g) := by
    rw [← hξs, hS, map_sum]
    simp only [CommAlgCat.squareClass_tmul]
    exact map_sum (QuotientAddGroup.mk' (CommAlgCat.boundaryOfSquares A (CommAlgCat.of A B))) _ S
  have hmem := (QuotientAddGroup.eq).1 hcls
  have hμ : kerTensorRelation P (idealTensorMap _ (fun a ha => P.lsSection_mem_ker ha) ξ) = 0 := by
    rw [hS, ← lsBiderivation_sum_contract]
    have h1 := P.lsBiderivation_boundaryOfSquares hmem
    rw [lsBiderivation_add, lsBiderivation_neg, hlz, add_zero, neg_eq_zero] at h1
    exact h1
  have hanti := mem_antisymm_of_kerTensorRelation_eq_zero P hμ
  have hanti0 := idealTensorMap_mem_antisymm P.lsRetraction.toRingHom
    (fun a ha => P.lsRetraction_mem ha) hanti
  have hsq0 := CommAlgCat.squareClass_antisymm A (CommAlgCat.of A B) hanti0
  rw [idealTensorMap_comp, idealTensorMap_congr
    (f := P.lsRetraction.toRingHom.comp P.lsSection.toRingHom)
    (g := (P.lsRetraction.comp P.lsSection).toRingHom)
    rfl _ (fun a ha => P.lsRetraction_mem (P.lsSection_mem_ker ha)),
    P.squareClass_idealTensorMap_lsRetraction_comp ξ hξm, hξs] at hsq0
  obtain ⟨u, hu, hfu⟩ := (QuotientAddGroup.eq_zero_iff _).1 hsq0
  have hu' : u ∈ CommAlgCat.augmentationIdeal A (CommAlgCat.of A B) (op ⦋2⦌) ^ 2 := hu
  have hfu' : CommAlgCat.faceSumTwo A _ u = CommAlgCat.faceSumTwo A _ g := hfu
  obtain ⟨v, hv⟩ := CommAlgCat.standardResolution_exists_of_faceSumTwo_eq_zero A
    (CommAlgCat.of A B) (g - u) (by rw [map_sub, hfu', sub_self])
  obtain ⟨y, hy⟩ : ∃ y : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 3,
      y = @HAdd.hAdd ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 3)
        ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 3) _ _ ((τ 3) v) w :=
    ⟨_, rfl⟩
  have e1 : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 y =
      @HAdd.hAdd ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2)
        ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2) _ _
        ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 ((τ 3) v))
        ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 w) := by
    rw [hy]; exact map_add _ _ _
  have e2 : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 ((τ 3) v) = (τ 2) g :=
    (cotangentMooreComplex_d_three_two_differential v).trans (by
      rw [hv, cotangentTermDifferential_sub, cotangentTermDifferential_eq_zero_of_mem_sq 2 hu',
        sub_zero])
  have hdy : (CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 y = m' := by
    rw [hw]
    exact e1.trans (congrArg (fun a => @HAdd.hAdd
      ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2)
      ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).X 2) _ _ a
      ((CommAlgCat.cotangentMooreComplex A (CommAlgCat.of A B)).d 3 2 w)) e2)
  refine ⟨uliftUp.{u, v, w} (A := A) (B := B) (-3)
    ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) 3).inv y), ?_⟩
  apply ULift.ext
  rw [cotangentComplexULift_d_apply, uliftUp_down, cotangentComplex_d_negThree_negTwo_inv, hdy,
    hm'def, Iso.hom_inv_id_apply]

/-- **The comparison map is an isomorphism on `H^{-2}`.** -/
theorem isIso_homologyMap_lsChainMap_negTwo :
    IsIso (HomologicalComplex.homologyMap P.lsChainMap (-2)) := by
  refine HomologicalComplex.isIso_homologyMap_of_forall P.lsChainMap (-3) (-2) (-1)
    (by simp) (by simp) (fun y hy => ?_) (fun x hx y hy => ?_)
  · obtain ⟨x, hx, rfl⟩ := P.lsSurj_negTwo y hy
    refine ⟨x, hx, 0, ?_⟩
    rw [map_zero, add_zero, lsChainMap_f, lsChainComponent_negTwo]
  · have hz : y = 0 := ((ModuleCat.isZero_iff_subsingleton).1
      ((lichtenbaumSchlessingerComplex P).isZero_X (-3) (by decide) (by decide)
        (by decide))).elim y 0
    rw [lsChainMap_f, lsChainComponent_negTwo, hz, map_zero] at hy
    exact P.lsInj_negTwo x hx hy

end Algebra.Presentation

end
