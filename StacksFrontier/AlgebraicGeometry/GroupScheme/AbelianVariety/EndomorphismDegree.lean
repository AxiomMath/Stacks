module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.DegreePolynomial
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DominantPullback

/-!
# The degree of an endomorphism of an abelian variety is a polynomial function

Let `A` be an abelian variety of dimension `g` over a field `k`. For a morphism `f : A ⟶ A` over
`k` write `deg f` for its degree `[R(A) : f^* R(A)]` when `f` is dominant (an isogeny, when `f`
is a homomorphism) and `0` otherwise (`Stacks.Groupoids.endDegree`). This file proves that for
morphisms `a_1, …, a_r : A ⟶ A` the function `c ↦ deg (∑ c_j a_j)` on `ℤ^r` is given by a
polynomial of total degree at most `2 g` ([Mumford, Abelian varieties, §19, Theorem 2]).

## Main definitions

* `Stacks.Groupoids.endDegree` — the degree of a morphism `A ⟶ A`, `0` if it is not dominant.

## Main results

* `Stacks.Groupoids.endDegree_mul_selfIntersectionNumber` — `deg f · (N^g · A) = (f^*N^g · A)`.
* `Stacks.Groupoids.exists_mvPolynomial_endDegree_prod_zpow` — the polynomiality.
* `Stacks.Groupoids.endDegree_comp` — `deg (f ≫ g) = deg f · deg g`.
* `Stacks.Groupoids.endDegree_zpow` — `deg (n • f) = |n| ^ (2 g) · deg f` for `n ≠ 0`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- A morphism `A ⟶ A` over `k` is proper. -/
theorem isProper_left_of_isAbelianVariety (f : A ⟶ A) : IsProper f.left := by
  have : IsProper (f.left ≫ A.hom) := by rw [Over.w f]; infer_instance
  exact IsProper.of_comp _ A.hom

/-- **The degree of a morphism `A ⟶ A` over `k`**: the degree `[R(A) : f^* R(A)]` of the
extension of function fields if `f` is dominant, and `0` otherwise. -/
def endDegree (f : A ⟶ A) : ℕ := by
  classical
  exact if h : IsDominant f.left then
    haveI := h
    haveI := isProper_left_of_isAbelianVariety A f
    degreeOver f.left
  else 0

/-- **The degree of `f` against an invertible module.** For every invertible `𝒪_A`-module `N`,
`deg f · (N^g · A) = (f^*N^g · A)`, `g = dim A` ([Stacks, Tag 0BET]). -/
theorem endDegree_mul_selfIntersectionNumber (f : A ⟶ A) (N : A.left.Modules)
    [SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2 N] :
    (endDegree A f : ℤ) * selfIntersectionNumber k A.hom (𝟙 A.left) (abelianVarietyDimension A)
        (topologicalKrullDim_eq_abelianVarietyDimension A).le N =
      selfIntersectionNumber k A.hom (𝟙 A.left) (abelianVarietyDimension A)
        (topologicalKrullDim_eq_abelianVarietyDimension A).le
        ((Scheme.Modules.pullback f.left).obj N) := by
  classical
  have hdim := topologicalKrullDim_eq_abelianVarietyDimension A
  have := isProper_left_of_isAbelianVariety A f
  by_cases h : IsDominant f.left
  · rw [endDegree, dite_eq_left h]
    exact (selfIntersectionNumber_pullback_of_isDominant k A.hom A.hom f.left (Over.w f) _ hdim
      hdim N).symm
  · rw [endDegree, dite_eq_right h, Nat.cast_zero, zero_mul]
    refine (selfIntersectionNumber_pullback_eq_zero_of_not_isDominant k A.hom A.hom f.left
      (Over.w f) _ h (Nat.pos_of_ne_zero fun h0 => h ?_) hdim.le hdim N).symm
    -- in dimension zero `A` is the spectrum of `k`, so `f` is an isomorphism
    have hiso := isIso_hom_of_topologicalKrullDim_eq_zero A (by rw [hdim, h0]; rfl)
    have : IsIso f.left := by
      have : f.left = 𝟙 A.left := by rw [← cancel_mono A.hom, Over.w f, Category.id_comp]
      rw [this]; infer_instance
    exact (isDominant_iff _).mpr f.left.homeomorph.surjective.denseRange

/-- Some invertible module on `A` has positive self-intersection number `(N^g · A)`. -/
private theorem exists_invertible_selfIntersectionNumber_pos :
    ∃ (N : A.left.Modules) (_ : SheafOfModules.IsInvertible A.left.presheaf
        A.left.ringCatIsSheaf N),
      0 < selfIntersectionNumber k A.hom (𝟙 A.left) (abelianVarietyDimension A)
        (topologicalKrullDim_eq_abelianVarietyDimension A).le N := by
  obtain ⟨N, hN, hNa, -⟩ := exists_isAmple_symmetric A
  exact ⟨N, hN, selfIntersectionNumber_pos k A.hom (𝟙 A.left) _
    (topologicalKrullDim_eq_abelianVarietyDimension A) N
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple A.left N hNa)⟩

/-- **The degree of `∑ c_j a_j` is a polynomial of total degree at most `2 g` in `c`**
([Mumford, Abelian varieties, §19, Theorem 2]), for morphisms `a_j : A ⟶ A` over `k` and
`g = dim A`. -/
theorem exists_mvPolynomial_endDegree_prod_zpow {σ : Type*} [LinearOrder σ] [Fintype σ]
    (a : σ → (A ⟶ A)) :
    ∃ P : MvPolynomial σ ℚ, P.totalDegree ≤ 2 * abelianVarietyDimension A ∧ ∀ c : σ → ℤ,
      (endDegree A (∏ j, a j ^ c j) : ℚ) = MvPolynomial.eval (fun j => (c j : ℚ)) P := by
  have hdim := topologicalKrullDim_eq_abelianVarietyDimension A
  obtain ⟨N, hN, hpos⟩ := exists_invertible_selfIntersectionNumber_pos A
  have := hN
  obtain ⟨P, hP, hPc⟩ := exists_mvPolynomial_picardIntersection_pullbackPicardClass_prod_zpow A N
    hN (B := A) (𝟙 A.left) _ hdim.le a
  set I := selfIntersectionNumber k A.hom (𝟙 A.left) _ hdim.le N
  refine ⟨MvPolynomial.C ((I : ℚ)⁻¹) * P, ?_, fun c => ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hP
  · rw [map_mul, MvPolynomial.eval_C, ← hPc c]
    have key := endDegree_mul_selfIntersectionNumber A (∏ j, a j ^ c j) N
    have : SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2
        ((Scheme.Modules.pullback (∏ j, a j ^ c j).left).obj N) :=
      RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ N
    have hform := picardIntersection_picardClass k A.hom (𝟙 A.left) _ hdim.le
      (fun _ => (Scheme.Modules.pullback (∏ j, a j ^ c j).left).obj N)
    rw [← selfIntersectionNumber_eq_intersectionNumber] at hform
    have hI : (I : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [eq_inv_mul_iff_mul_eq₀ hI, mul_comm]
    have : ((picardIntersection k A.hom (𝟙 A.left) _ hdim.le fun _ =>
        Stacks.SheafOfModules.pullbackPicardClass (∏ j, a j ^ c j).left N hN : ℤ) : ℚ) =
        ((endDegree A (∏ j, a j ^ c j) : ℤ) * I : ℤ) := by
      rw [key, ← hform]
      rfl
    rw [this]
    push_cast
    ring

/-- **The degree is multiplicative**: `deg (f ≫ g) = deg f · deg g` for morphisms
`f g : A ⟶ A` over `k`. -/
theorem endDegree_comp (f g : A ⟶ A) : endDegree A (f ≫ g) = endDegree A f * endDegree A g := by
  have hdim := topologicalKrullDim_eq_abelianVarietyDimension A
  obtain ⟨N, hN, hpos⟩ := exists_invertible_selfIntersectionNumber_pos A
  have := hN
  have h1 := endDegree_mul_selfIntersectionNumber A (f ≫ g) N
  have h2 := endDegree_mul_selfIntersectionNumber A f ((Scheme.Modules.pullback g.left).obj N)
  have h3 := endDegree_mul_selfIntersectionNumber A g N
  have hiso : selfIntersectionNumber k A.hom (𝟙 A.left) (abelianVarietyDimension A) hdim.le
        ((Scheme.Modules.pullback (f ≫ g).left).obj N) =
      selfIntersectionNumber k A.hom (𝟙 A.left) (abelianVarietyDimension A) hdim.le
        ((Scheme.Modules.pullback f.left).obj ((Scheme.Modules.pullback g.left).obj N)) :=
    selfIntersectionNumber_eq_of_iso k A.hom (𝟙 A.left) _ hdim.le _ _
      (eqToIso (by rw [Over.comp_left]) ≪≫ ((Scheme.Modules.pullbackComp f.left g.left).app N).symm)
  have key : ((endDegree A (f ≫ g) : ℤ)) * selfIntersectionNumber k A.hom (𝟙 A.left)
      (abelianVarietyDimension A) hdim.le N =
      ((endDegree A f * endDegree A g : ℕ) : ℤ) * selfIntersectionNumber k A.hom (𝟙 A.left)
      (abelianVarietyDimension A) hdim.le N := by
    rw [h1, hiso, ← h2, ← h3, Nat.cast_mul, mul_assoc]
  exact_mod_cast mul_right_cancel₀ hpos.ne' key

/-- **The degree of multiplication by `n`** is `|n| ^ (2 g)`, `g = dim A`, for `n ≠ 0`
([Stacks, Tag 0BFG]). -/
theorem endDegree_zpow_id (n : ℤ) (hn : n ≠ 0) :
    endDegree A ((𝟙 A : A ⟶ A) ^ n) = n.natAbs ^ (2 * abelianVarietyDimension A) := by
  classical
  have hcube := hasTheoremOfTheCube k A
  have := isFinite_zpow_id_left A hcube n hn
  have : Surjective ((𝟙 A : A ⟶ A) ^ n).left :=
    have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
    have := isLocallyNoetherian_left A
    have : IsNoetherian A.left := {}
    surjective_of_isFinite_of_topologicalKrullDim_le _
      (topologicalKrullDim_ne_top_of_isProper k A.hom) le_rfl
  have hd : IsDominant ((𝟙 A : A ⟶ A) ^ n).left := inferInstance
  rw [endDegree, dite_eq_left hd]
  exact degreeOver_zpow_id_left A hcube n hn

/-- **Homogeneity of the degree**: `deg (f ^ n) = |n| ^ (2 g) · deg f` for `n ≠ 0`, where
`f ^ n = n • f` is the `n`-th power in the group `A ⟶ A`, which is `f` followed by
multiplication by `n`. -/
theorem endDegree_zpow (f : A ⟶ A) (n : ℤ) (hn : n ≠ 0) :
    endDegree A (f ^ n) = n.natAbs ^ (2 * abelianVarietyDimension A) * endDegree A f := by
  have h : f ^ n = f ≫ (𝟙 A : A ⟶ A) ^ n := by rw [GrpObj.comp_zpow, Category.comp_id]
  rw [h, endDegree_comp, endDegree_zpow_id A n hn, mul_comm]

end Stacks.Groupoids
