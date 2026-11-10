module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonCanonical.HomologyNegTwo
import all StacksFrontier.Cotangent.StandardResolutionFrobeniusHomotopy

/-!
# The comparison map on `H⁰` and `H^{-1}`

This file proves that the comparison map of complexes `Algebra.Presentation.lsChainMap`
`L_{B/A} → L` is an isomorphism on `H⁰` and `H^{-1}` (Remark 08UP and Lemma 08RB of the
Stacks Project): the explicit map `L_{B/A} → NL(P₀ → B)` is an isomorphism there, and the
comparison followed by the surjection `F ⊗ B → I/I²` is the map induced by `ψ` on naive
cotangent complexes.

## Main results

* `Algebra.Presentation.isIso_homologyMap_lsChainMap_zero`,
  `Algebra.Presentation.isIso_homologyMap_lsChainMap_negOne`: `lsChainMap` is an isomorphism on
  `H⁰` and `H^{-1}`.

## References

* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TensorProduct KaehlerDifferential
open Stacks.Cotangent

universe u v w

namespace Algebra.Presentation

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
variable {X T : Type w} (P : Algebra.Presentation A B X T)

local notation "𝒫" => (CommAlgCat.standardResolution A (CommAlgCat.of A B))
local notation "𝓔" n => (CommAlgCat.standardResolutionExtension A (CommAlgCat.of A B) n)

/-! ### `ψ` and `φ` as morphisms of extensions -/

/-- `ψ : P₀ → P` as a morphism of extensions of `B`. -/
def lsSectionHom : (𝓔 0).Hom P.toExtension where
  toRingHom := P.lsSection.toRingHom
  toRingHom_algebraMap x := P.lsSection.commutes x
  algebraMap_toRingHom x := P.algebraMap_lsSection x

/-- `φ : P → P₀` as a morphism of extensions of `B`. -/
def lsRetractionHom : P.toExtension.Hom (𝓔 0) where
  toRingHom := P.lsRetraction.toRingHom
  toRingHom_algebraMap x := P.lsRetraction.commutes x
  algebraMap_toRingHom x := P.augmentation_lsRetraction x

/-- `H¹` of the naive cotangent complex does not depend on the presentation: `ψ` induces a
bijection `H¹(NL(P₀ → B)) → H¹(NL(P → B))`. -/
theorem bijective_h1Cotangent_map_lsSectionHom :
    Function.Bijective (Algebra.Extension.H1Cotangent.map P.lsSectionHom) :=
  (Algebra.Extension.H1Cotangent.equiv P.lsSectionHom P.lsRetractionHom).bijective

/-- `ψ` is injective on `H¹` of the naive cotangent complexes, on elements. -/
theorem eq_zero_of_cotangentMap_lsSectionHom (v : (𝓔 0).Cotangent)
    (hv : (𝓔 0).cotangentComplex v = 0)
    (h0 : Algebra.Extension.Cotangent.map P.lsSectionHom v = 0) : v = 0 := by
  have h := P.bijective_h1Cotangent_map_lsSectionHom.1
    (a₁ := (⟨v, hv⟩ : LinearMap.ker (𝓔 0).cotangentComplex)) (a₂ := 0) (by
      rw [map_zero]
      exact Subtype.ext h0)
  exact congrArg Subtype.val h

/-! ### `F ⊗ B → I/I²` -/

/-- The class of the generator `f_t` in `I/I²`. -/
def relationCotangent (t : T) : P.toExtension.Cotangent :=
  Algebra.Extension.Cotangent.mk ⟨P.relation t, P.relation_mem_ker t⟩

open scoped Classical in
/-- The surjection `F ⊗_P B → I/I²`, `e_t ↦ f_t`. -/
def freeTensorToCotangent : B ⊗[P.Ring] (T →₀ P.Ring) →ₗ[B] P.toExtension.Cotangent :=
  Finsupp.linearCombination B P.relationCotangent ∘ₗ
    (TensorProduct.finsuppScalarRight P.Ring B B T).toLinearMap

/-- The `B`-module structure of `I/I²` on the class of an element of `I`. -/
theorem algebraMap_smul_cotangent_mk (p x : P.Ring) (hx : x ∈ P.toExtension.ker) :
    algebraMap P.Ring B p • Algebra.Extension.Cotangent.mk (P := P.toExtension) ⟨x, hx⟩ =
      Algebra.Extension.Cotangent.mk ⟨p * x, Ideal.mul_mem_left _ p hx⟩ :=
  (algebraMap_smul B (show P.toExtension.Ring from p)
    (Algebra.Extension.Cotangent.mk (P := P.toExtension) ⟨x, hx⟩)).trans
      (Algebra.Extension.Cotangent.mk.map_smul _ _).symm

open scoped Classical in
/-- `F ⊗ B → I/I²` sends `1 ⊗ u` to the class of `ρ(u)`. -/
theorem freeTensorToCotangent_one_tmul (u : T →₀ P.Ring) :
    P.freeTensorToCotangent ((1 : B) ⊗ₜ u) =
      Algebra.Extension.Cotangent.mk ⟨relationMap P u, relationMap_mem_ker P u⟩ := by
  classical
  induction u using Finsupp.induction_linear with
  | zero =>
    rw [tmul_zero, map_zero, eq_comm, Algebra.Extension.Cotangent.mk_eq_zero_iff]
    exact Submodule.zero_mem _
  | add x y hx hy =>
    rw [tmul_add, map_add, hx, hy, ← map_add]
    congr 1
    exact Subtype.ext (map_add _ _ _).symm
  | single t c =>
    rw [freeTensorToCotangent, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.finsuppScalarRight_apply_tmul, Finsupp.sum_single_index (by simp),
      Finsupp.linearCombination_single, Algebra.smul_def, mul_one, relationCotangent]
    refine (P.algebraMap_smul_cotangent_mk c _ (P.relation_mem_ker t)).trans ?_
    congr 1
    apply Subtype.ext
    change c * P.relation t = relationMap P (Finsupp.single t c)
    rw [relationMap_single]

/-- Since `P → B` is surjective, every element of `B ⊗_P M` is of the form `1 ⊗ m`. -/
theorem tensor_eq_one_tmul {M : Type*} [AddCommGroup M] [Module P.Ring M]
    (c : B ⊗[P.Ring] M) : ∃ m : M, c = (1 : B) ⊗ₜ m := by
  induction c using TensorProduct.inductionOn with
  | tmul b m =>
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective b
    exact ⟨p • m, by rw [tmul_smul, smul_tmul', Algebra.smul_def, mul_one]⟩
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact ⟨m + m', by rw [tmul_add]⟩

/-- `ρ : F/TrivRel → P` lands in `I`. -/
theorem freeQuotientRelationMap_mem_ker (m : freeQuotient P) :
    freeQuotientRelationMap P m ∈ P.ker := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ m
  exact relationMap_mem_ker P u

/-- `F/TrivRel → F ⊗ B → I/I²` is `ρ` followed by the projection. -/
theorem freeTensorToCotangent_freeQuotientToTensor (m : freeQuotient P) :
    P.freeTensorToCotangent (freeQuotientToTensor P m) =
      Algebra.Extension.Cotangent.mk ⟨freeQuotientRelationMap P m,
        P.freeQuotientRelationMap_mem_ker m⟩ := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ m
  exact P.freeTensorToCotangent_one_tmul u

/-- The surjection `F ⊗ B → I/I²` followed by `I/I² → Ω_{P/A} ⊗ B` is the differential of `L`. -/
theorem cotangentComplex_freeTensorToCotangent (c : B ⊗[P.Ring] (T →₀ P.Ring)) :
    P.toExtension.cotangentComplex (P.freeTensorToCotangent c) = relationDifferentialB P c := by
  obtain ⟨u, rfl⟩ := P.tensor_eq_one_tmul c
  rw [P.freeTensorToCotangent_one_tmul, Algebra.Extension.cotangentComplex_mk]
  exact (relationDifferentialB_freeQuotientToTensor P (Submodule.Quotient.mk u)).symm

/-- `F ⊗ B → I/I²` is surjective. -/
theorem surjective_freeTensorToCotangent : Function.Surjective P.freeTensorToCotangent := by
  intro k
  obtain ⟨⟨a, ha⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective k
  obtain ⟨u, rfl⟩ := exists_relationMap_eq P a ha
  exact ⟨(1 : B) ⊗ₜ u, P.freeTensorToCotangent_one_tmul u⟩

/-- `1 ⊗ w = 0` in `B ⊗_P F` for `w ∈ I F`. -/
theorem one_tmul_eq_zero_of_mem_smul {w : T →₀ P.Ring} (hw : w ∈ P.ker • (⊤ : Submodule P.Ring
    (T →₀ P.Ring))) : (1 : B) ⊗ₜ[P.Ring] w = 0 := by
  refine Submodule.smul_induction_on hw (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [tmul_smul_eq_algebraMap_smul, show algebraMap P.Ring B a = 0 from ha, zero_smul]
  · rw [tmul_add, hx, hy, add_zero]

/-- **The kernel of `F ⊗ B → I/I²` is the image of `Rel/TrivRel ⊗ B`.** -/
theorem exists_relationBoundary_eq (c : B ⊗[P.Ring] (T →₀ P.Ring))
    (hc : P.freeTensorToCotangent c = 0) :
    letI := relationModule P
    ∃ s : B ⊗[P.Ring] relationQuotient P, relationBoundary P s = c := by
  let _ := relationModule P
  obtain ⟨u, rfl⟩ := P.tensor_eq_one_tmul c
  rw [P.freeTensorToCotangent_one_tmul, Algebra.Extension.Cotangent.mk_eq_zero_iff] at hc
  have hrange : Submodule.map (relationMap P) ⊤ = P.ker := by
    refine le_antisymm ?_ fun a ha => ?_
    · rintro _ ⟨u, -, rfl⟩
      exact relationMap_mem_ker P u
    · obtain ⟨u, rfl⟩ := exists_relationMap_eq P a ha
      exact ⟨u, trivial, rfl⟩
  have hsq : relationMap P u ∈ Submodule.map (relationMap P)
      (P.ker • (⊤ : Submodule P.Ring (T →₀ P.Ring))) := by
    rw [Submodule.map_smul'', hrange, smul_eq_mul, ← pow_two]
    exact hc
  obtain ⟨w, hw, hwu⟩ := hsq
  have hr : u - w ∈ relations P := by
    change relationMap P (u - w) = 0
    rw [map_sub, hwu, sub_self]
  refine ⟨(1 : B) ⊗ₜ Submodule.mkQ (trivialRelations P) ⟨u - w, hr⟩,
    (relationBoundary_tmul P ⟨u - w, hr⟩).trans ?_⟩
  change (1 : B) ⊗ₜ[P.Ring] (u - w) = _
  rw [tmul_sub, P.one_tmul_eq_zero_of_mem_smul hw, sub_zero]

/-- `F ⊗ B → I/I²` kills the image of `Rel/TrivRel ⊗ B`. -/
theorem freeTensorToCotangent_relationBoundary (s : B ⊗[P.Ring] relationQuotient P) :
    letI := relationModule P
    P.freeTensorToCotangent (relationBoundary P s) = 0 := by
  let _ := relationModule P
  induction s using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul b q =>
    rw [show b ⊗ₜ[P.Ring] q = b • ((1 : B) ⊗ₜ[P.Ring] q) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, map_smul, relationBoundary_tmul_one, freeTensorToCotangent_freeQuotientToTensor]
    rw [show (⟨_, _⟩ : P.toExtension.ker) = 0 from
      Subtype.ext (freeQuotientRelationMap_relationQuotientToFree P q), map_zero, smul_zero]

/-- **The degree `-1` component followed by `F ⊗ B → I/I²` is the arrow of Remark 08UP
followed by `ψ`.** -/
theorem freeTensorToCotangent_lsComponentOne (c : (𝓔 1).CotangentSpace) :
    P.freeTensorToCotangent (P.lsComponentOne c) =
      Algebra.Extension.Cotangent.map P.lsSectionHom
        (CommAlgCat.naiveCotangentComparison A (CommAlgCat.of A B) c) := by
  have h := Algebra.Extension.cotangentSpace_hom_ext (𝓔 1)
    (P.freeTensorToCotangent ∘ₗ P.lsComponentOne)
    (Algebra.Extension.Cotangent.map P.lsSectionHom ∘ₗ
      CommAlgCat.naiveCotangentComparison A (CommAlgCat.of A B))
    (fun (x : (𝒫).left.obj (op ⦋1⦌)) => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, lsComponentOne_tmul, lsDerivOne,
        freeTensorToCotangent_freeQuotientToTensor]
      refine Eq.trans ?_ (congrArg (Algebra.Extension.Cotangent.map P.lsSectionHom)
        (CommAlgCat.naiveCotangentComparison_tmul A (CommAlgCat.of A B) 1 x)).symm
      rw [one_smul, Algebra.Extension.Cotangent.map_mk]
      congr 1
      apply Subtype.ext
      refine (P.freeQuotientRelationMap_lsBiderivation x).trans ?_
      refine Eq.trans ?_ (congrArg P.lsSectionHom.toAlgHom
        (CommAlgCat.naiveCotangentComparison_subToKer_coe A (CommAlgCat.of A B) x)).symm
      exact (map_sub P.lsSection _ _).symm)
  exact LinearMap.congr_fun h c

/-- `Ω_{P₀/A} ⊗ B → Ω_{P/A} ⊗ B → Ω_{B/A}` is the canonical map. -/
theorem toKaehler_lsComponentZero (c : (𝓔 0).CotangentSpace) :
    P.toExtension.toKaehler (P.lsComponentZero c) = (𝓔 0).toKaehler c := by
  have h := Algebra.Extension.cotangentSpace_hom_ext (𝓔 0)
    (P.toExtension.toKaehler ∘ₗ P.lsComponentZero) (𝓔 0).toKaehler
    fun (x : (𝒫).left.obj (op ⦋0⦌)) => by
      refine (congrArg P.toExtension.toKaehler (P.lsComponentZero_tmul x)).trans ?_
      refine (toKaehler_one_tmul_D P.toExtension (P.lsSection x)).trans ?_
      refine Eq.trans ?_ (toKaehler_one_tmul_D (𝓔 0) x).symm
      exact congrArg (D A B) (P.algebraMap_lsSection x)
  exact LinearMap.congr_fun h c

/-! ### The explicit map of Remark 08UP on elements -/

local notation "𝕂" => (CommAlgCat.cotangentComplex A (CommAlgCat.of A B))
local notation "𝔼" => (CommAlgCat.explicitNaiveComparison A (CommAlgCat.of A B))
local notation "ℕ𝕃" => (Algebra.Extension.naiveComplex (𝓔 0))

omit P in
/-- In degree `-1`, the explicit map `L_{B/A} → NL(P₀ → B)` is `naiveCotangentComparison` on
the cotangent space of `P₁ → B`. -/
theorem explicitNaiveComparison_f_negOne_apply (m : (𝕂).X (-1)) :
    (Algebra.Extension.naiveComplexXNegOneIso (𝓔 0)).hom ((𝔼).f (-1) m) =
      CommAlgCat.naiveCotangentComparison A (CommAlgCat.of A B)
        ((cotangentDegreeIsoOne (A := A) (B := B)).hom m) := by
  rw [CommAlgCat.explicitNaiveComparison_f, CommAlgCat.comparisonComponent_negOne,
    CommAlgCat.comparisonDegreeNegOne]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

omit P in
/-- In degree `0`, the explicit map `L_{B/A} → NL(P₀ → B)` is `cotangentDegreeIsoZero`. -/
theorem explicitNaiveComparison_f_zero_apply (m : (𝕂).X 0) :
    (Algebra.Extension.naiveComplexXZeroIso (𝓔 0)).hom ((𝔼).f 0 m) =
      (cotangentDegreeIsoZero (A := A) (B := B)).hom m := by
  rw [CommAlgCat.explicitNaiveComparison_f, CommAlgCat.comparisonComponent_zero,
    CommAlgCat.comparisonDegreeZero]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

omit P in
/-- The differential of `NL(P₀ → B)` is `I/I² → Ω_{P₀/A} ⊗ B` on elements. -/
theorem naiveComplex_d_negOne_zero_apply (y : (ℕ𝕃).X (-1)) :
    (Algebra.Extension.naiveComplexXZeroIso (𝓔 0)).hom ((ℕ𝕃).d (-1) 0 y) =
      (𝓔 0).cotangentComplex ((Algebra.Extension.naiveComplexXNegOneIso (𝓔 0)).hom y) := by
  rw [Algebra.Extension.naiveComplex_d]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

omit P in
/-- On elements, the differential of `L_{B/A}` from degree `-1` to degree `0` is `d₀ - d₁` on
cotangent spaces. -/
theorem cotangentComplex_d_negOne_zero_apply (m : (𝕂).X (-1)) :
    (cotangentDegreeIsoZero (A := A) (B := B)).hom ((𝕂).d (-1) 0 m) =
      (Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 0 0) -
        Algebra.Extension.CotangentSpace.map
          (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 0 1))
        ((cotangentDegreeIsoOne (A := A) (B := B)).hom m) := by
  rw [cotangentComplex_d_negOne_zero']
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

omit P in
/-- The differential of the lifted cotangent complex out of degree `0` vanishes. -/
theorem cotangentComplexULift_d_zero_one (x : (cotangentComplexULift.{u, v, w} A B).X 0) :
    (cotangentComplexULift.{u, v, w} A B).d 0 1 x = 0 :=
  ULift.ext (((ModuleCat.isZero_iff_subsingleton).1
    (CommAlgCat.cotangentComplex_isZero_pos A (CommAlgCat.of A B) 1 (by decide))).elim _ _)

/-! ### The isomorphisms on `H^{-1}` and `H⁰` -/

/-- **The comparison map is an isomorphism on `H^{-1}`.** -/
theorem isIso_homologyMap_lsChainMap_negOne :
    IsIso (HomologicalComplex.homologyMap P.lsChainMap (-1)) := by
  have := Stacks.Cotangent.isIso_homologyMap_explicitNaiveComparison A (CommAlgCat.of A B) (-1)
    (Or.inl rfl)
  let _ := relationModule P
  refine HomologicalComplex.isIso_homologyMap_of_forall P.lsChainMap (-2) (-1) 0
    (by simp) (by simp) (fun y hy => ?_) (fun x hx y hy => ?_)
  · set t := (lichtenbaumSchlessingerComplex P).freeIso.hom y with ht
    have hdt : relationDifferentialB P t = 0 := by
      rw [← lsComplex_d_negOne_inv_apply, ht, Iso.hom_inv_id_apply, hy, map_zero]
    have hker : P.freeTensorToCotangent t ∈ LinearMap.ker P.toExtension.cotangentComplex := by
      rw [LinearMap.mem_ker, cotangentComplex_freeTensorToCotangent, hdt]
      rfl
    obtain ⟨h, hh⟩ := P.bijective_h1Cotangent_map_lsSectionHom.2 ⟨_, hker⟩
    have hy0 : (ℕ𝕃).d (-1) 0 ((Algebra.Extension.naiveComplexXNegOneIso (𝓔 0)).inv h.1) = 0 := by
      apply ConcreteCategory.injective_of_mono_of_preservesPullback
        (Algebra.Extension.naiveComplexXZeroIso (𝓔 0)).hom
      rw [naiveComplex_d_negOne_zero_apply, Iso.inv_hom_id_apply, map_zero]
      exact h.2
    obtain ⟨x, hx, y', hy'⟩ := HomologicalComplex.exists_of_epi_homologyMap (𝔼) (-2) (-1) 0
      (by simp) (by simp) _ hy0
    have hy'0 : y' = 0 := ((ModuleCat.isZero_iff_subsingleton).1
      (Algebra.Extension.isZero_naiveComplex_X (𝓔 0) (-2) (by decide) (by decide))).elim _ _
    have hcomp : CommAlgCat.naiveCotangentComparison A (CommAlgCat.of A B)
        ((cotangentDegreeIsoOne (A := A) (B := B)).hom x) = h.1 := by
      have e := congrArg (Algebra.Extension.naiveComplexXNegOneIso (𝓔 0)).hom hy'
      rw [hy'0, map_zero, add_zero, explicitNaiveComparison_f_negOne_apply,
        Iso.inv_hom_id_apply] at e
      exact e.symm
    have hν : P.freeTensorToCotangent
        (t - P.lsComponentOne ((cotangentDegreeIsoOne (A := A) (B := B)).hom x)) = 0 := by
      rw [map_sub, freeTensorToCotangent_lsComponentOne, hcomp, sub_eq_zero]
      exact (congrArg Subtype.val hh).symm
    obtain ⟨s, hs⟩ := P.exists_relationBoundary_eq _ hν
    refine ⟨uliftUp.{u, v, w} (A := A) (B := B) (-1) x, ULift.ext hx,
      (lichtenbaumSchlessingerComplex P).relationIso.inv s, ?_⟩
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (lichtenbaumSchlessingerComplex P).freeIso.hom
    rw [map_add, lsChainMap_f, lsChainComponent_negOne, lsChainOne_apply, uliftUp_down,
      lsComplex_d_negTwo_inv_apply, hs, ← ht, add_sub_cancel]
  · have hm : (𝕂).d (-1) 0 x.down = 0 := by
      rw [← cotangentComplexULift_d_apply, hx]
      rfl
    have hcyc : (𝓔 0).cotangentComplex (CommAlgCat.naiveCotangentComparison A (CommAlgCat.of A B)
        ((cotangentDegreeIsoOne (A := A) (B := B)).hom x.down)) = 0 := by
      rw [← LinearMap.comp_apply, CommAlgCat.naiveCotangentComparison_cotangentComplex,
        ← cotangentComplex_d_negOne_zero_apply, hm, map_zero]
    have hzero : Algebra.Extension.Cotangent.map P.lsSectionHom
        (CommAlgCat.naiveCotangentComparison A (CommAlgCat.of A B)
          ((cotangentDegreeIsoOne (A := A) (B := B)).hom x.down)) = 0 := by
      rw [← freeTensorToCotangent_lsComponentOne]
      have e := congrArg (lichtenbaumSchlessingerComplex P).freeIso.hom hy
      rw [lsChainMap_f, lsChainComponent_negOne, lsChainOne_apply,
        ← (lichtenbaumSchlessingerComplex P).relationIso.hom_inv_id_apply y,
        lsComplex_d_negTwo_inv_apply] at e
      rw [e, freeTensorToCotangent_relationBoundary]
    have hh := P.eq_zero_of_cotangentMap_lsSectionHom _ hcyc hzero
    have hE : (𝔼).f (-1) x.down = (ℕ𝕃).d (-2) (-1) 0 := by
      rw [map_zero]
      apply ConcreteCategory.injective_of_mono_of_preservesPullback
        (Algebra.Extension.naiveComplexXNegOneIso (𝓔 0)).hom
      rw [explicitNaiveComparison_f_negOne_apply, map_zero]
      exact hh
    obtain ⟨z, hz⟩ := HomologicalComplex.exists_of_mono_homologyMap (𝔼) (-2) (-1) 0
      (by simp) (by simp) x.down hm 0 hE
    exact ⟨uliftUp.{u, v, w} (A := A) (B := B) (-2) z, ULift.ext hz⟩

/-- **The comparison map is an isomorphism on `H⁰`.** -/
theorem isIso_homologyMap_lsChainMap_zero :
    IsIso (HomologicalComplex.homologyMap P.lsChainMap 0) := by
  have := Stacks.Cotangent.isIso_homologyMap_explicitNaiveComparison A (CommAlgCat.of A B) 0
    (Or.inr rfl)
  refine HomologicalComplex.isIso_homologyMap_of_forall P.lsChainMap (-1) 0 1
    (by simp) (by simp) (fun y _ => ?_) (fun x _ y hy => ?_)
  · set t := (lichtenbaumSchlessingerComplex P).differentialIso.hom y with ht
    obtain ⟨c, hc⟩ := (𝓔 0).toKaehler_surjective (P.toExtension.toKaehler t)
    have hk : P.toExtension.toKaehler (t - P.lsComponentZero c) = 0 :=
      (map_sub P.toExtension.toKaehler _ _).trans (by
        rw [toKaehler_lsComponentZero, hc, sub_self])
    obtain ⟨k, hk'⟩ := (P.toExtension.exact_cotangentComplex_toKaehler _).1 hk
    obtain ⟨s, rfl⟩ := P.surjective_freeTensorToCotangent k
    rw [cotangentComplex_freeTensorToCotangent] at hk'
    refine ⟨uliftUp.{u, v, w} (A := A) (B := B) 0
      ((cotangentDegreeIsoZero (A := A) (B := B)).inv c),
      cotangentComplexULift_d_zero_one _, (lichtenbaumSchlessingerComplex P).freeIso.inv s, ?_⟩
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (lichtenbaumSchlessingerComplex P).differentialIso.hom
    rw [map_add, lsChainMap_f, lsChainComponent_zero, lsChainZero_apply, uliftUp_down,
      Iso.inv_hom_id_apply, lsComplex_d_negOne_inv_apply, hk', ← ht, add_sub_cancel]
  · have h1 : P.lsComponentZero ((cotangentDegreeIsoZero (A := A) (B := B)).hom x.down) =
        relationDifferentialB P ((lichtenbaumSchlessingerComplex P).freeIso.hom y) := by
      have e := congrArg (lichtenbaumSchlessingerComplex P).differentialIso.hom hy
      rw [lsChainMap_f, lsChainComponent_zero, lsChainZero_apply,
        ← (lichtenbaumSchlessingerComplex P).freeIso.hom_inv_id_apply y,
        lsComplex_d_negOne_inv_apply] at e
      exact e
    have h2 : (𝓔 0).toKaehler ((cotangentDegreeIsoZero (A := A) (B := B)).hom x.down) = 0 := by
      rw [← toKaehler_lsComponentZero, h1, ← cotangentComplex_freeTensorToCotangent]
      exact P.toExtension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero _
    obtain ⟨k, hk⟩ := ((𝓔 0).exact_cotangentComplex_toKaehler _).1 h2
    have hm : (𝕂).d 0 1 x.down = 0 := congrArg ULift.down (cotangentComplexULift_d_zero_one x)
    have hE : (𝔼).f 0 x.down =
        (ℕ𝕃).d (-1) 0 ((Algebra.Extension.naiveComplexXNegOneIso (𝓔 0)).inv k) := by
      apply ConcreteCategory.injective_of_mono_of_preservesPullback
        (Algebra.Extension.naiveComplexXZeroIso (𝓔 0)).hom
      rw [explicitNaiveComparison_f_zero_apply, naiveComplex_d_negOne_zero_apply,
        Iso.inv_hom_id_apply, hk]
    obtain ⟨z, hz⟩ := HomologicalComplex.exists_of_mono_homologyMap (𝔼) (-1) 0 1
      (by simp) (by simp) x.down hm _ hE
    exact ⟨uliftUp.{u, v, w} (A := A) (B := B) (-1) z, ULift.ext hz⟩

end Algebra.Presentation

end
