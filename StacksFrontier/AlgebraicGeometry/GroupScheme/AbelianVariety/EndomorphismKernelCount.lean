module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.IsogenyKernelCount
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.FieldTheory.Perfect
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionCharpoly
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kernels of polynomials in an endomorphism of an abelian variety

Let `A` be an abelian variety over an algebraically closed field `k` and `α` an endomorphism of
`A` (a homomorphism of group schemes `A ⟶ A`). For `R ∈ ℤ[X]` write `R(α)` for the corresponding
endomorphism (`Stacks.Groupoids.endPolyEval`). This file shows that the group of `k`-points of
the kernel of `R(α)` has exactly `deg R(α)` elements in the two cases needed for
[Mumford, *Abelian varieties*, §19, Theorem 4]:

* in characteristic `p > 0`, when `R` is congruent modulo `p` to a constant `c` with `p ∤ c`:
  then the derivative of `R(α)` at the identity is multiplication by `c`, because `p`-th powers
  of tangent vectors vanish, so `R(α)` is étale
  (`Stacks.Groupoids.natCard_comp_endPolyEval_eq_one_eq_endDegree_of_charP`);
* in characteristic `0`, whenever `deg R(α) ≠ 0`: a dominant homomorphism is étale at the generic
  point, because the extension of function fields is finite and separable, hence étale at a
  closed point, hence at the identity by translation, hence everywhere
  (`Stacks.Groupoids.natCard_comp_eq_one_eq_endDegree_of_charZero`).

In both cases the kernel is a finite étale group scheme of rank `deg R(α)` over `k`. The kernel
on `A(k)`, as the kernel of the polynomial `R` evaluated at postcomposition with `α` on the group
`A(k)`, is related to the kernel of `R(α)` by
`Stacks.Groupoids.aeval_postcompPoints_apply`.

## Main results

* `Stacks.Groupoids.homMk_tangent_zpow_char_eq_one`: `v ^ p = 1` for a tangent vector `v` at the
  identity in characteristic `p`.
* `Stacks.Groupoids.natCard_comp_eq_one_eq_endDegree_of_etaleAt_unit`: a homomorphism étale at
  the identity has `deg β` points in its kernel.
* `Stacks.Groupoids.etaleAt_genericPoint_of_charZero`: in characteristic zero a homomorphism of
  nonzero degree is étale at the generic point.
* `Stacks.Groupoids.endDegree_eq_of_isFiniteLocallyFreeOfRank`: the degree of an endomorphism
  which is finite locally free of rank `d` is `d`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

section Tangent

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **In characteristic `p` the `p`-th power of a tangent vector at the identity is trivial.**
Integer multiples of tangent vectors are integer powers of the corresponding dual-number points
(`Stacks.Groupoids.tangentArrow_zsmul_val`), and the tangent space is a vector space over a field
of characteristic `p`. -/
theorem homMk_tangent_zpow_char_eq_one (p : ℕ) [CharP k p] (s : Spec (.of k))
    (v : DottedTangentArrow A.hom ((η[A]).left s)) :
    (Over.homMk v.val v.property.2 :
      Over.mk (dualNumberBasePoint A.hom ((η[A]).left s)) ⟶ A) ^ (p : ℤ) = 1 := by
  have hp : ((p : ℤ) : A.left.residueField ((η[A]).left s)) = 0 := by
    have h : ¬ IsUnit ((p : ℤ) : k) := by
      rw [Int.cast_natCast, CharP.cast_eq_zero]
      exact not_isUnit_zero
    rwa [← isUnit_intCast_residueField_iff k A.left A.hom _ (p : ℤ), isUnit_iff_ne_zero,
      not_not] at h
  have hv : (p : ℤ) • v = (0 : ℤ) • v := by
    rw [zero_smul, ← Int.cast_smul_eq_zsmul (A.left.residueField ((η[A]).left s)), hp,
      zero_smul]
  have h1 := tangentArrow_zsmul_val A s v (p : ℤ)
  have h0 := tangentArrow_zsmul_val A s v 0
  rw [hv, h0, zpow_zero] at h1
  exact Over.OverMorphism.ext h1.symm

/-- A homomorphism carries a dual-number point at the identity to a dual-number point at the
identity: its derivative there, transported back along `β e = e`. -/
theorem exists_homMk_tangent_comp_eq (β : A ⟶ A) [IsMonHom β] (s : Spec (.of k))
    (v : DottedTangentArrow A.hom ((η[A]).left s)) :
    ∃ w : DottedTangentArrow A.hom ((η[A]).left s),
      (Over.homMk v.val v.property.2 :
        Over.mk (dualNumberBasePoint A.hom ((η[A]).left s)) ⟶ A) ≫ β =
        Over.homMk w.val w.property.2 := by
  have := isIso_residueFieldMap_unit_of_isMonHom A β s
  have := AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section A.hom (η[A]).left
    (η[A]).w s
  refine ⟨left_unit_apply_of_isMonHom A β s ▸
    tangentMap β.left A.hom A.hom β.w ((η[A]).left s) v, ?_⟩
  apply Over.OverMorphism.ext
  change v.val ≫ β.left = _
  exact (tangentMap_fixed_apply A.hom _ β.w ((η[A]).left s)
    (left_unit_apply_of_isMonHom A β s) v).symm

variable [IsCommMonObj A]

/-- **A polynomial congruent to a constant modulo `p` acts on tangent vectors at the identity
as that constant**, in characteristic `p`: if `p ∣ R_j` for `j ≠ 0`, then
`v ≫ R(α) = v ^ R(0)`. Write `R = R(0) + p S`; then `v ≫ R(α) = v ^ R(0) · (v ≫ S(α)) ^ p`, and
`v ≫ S(α)` is again a tangent vector. -/
theorem homMk_tangent_comp_endPolyEval_of_modEq (p : ℕ) [CharP k p] (α : A ⟶ A) [IsMonHom α]
    (R : ℤ[X]) (hR : ∀ j, j ≠ 0 → (p : ℤ) ∣ R.coeff j) (s : Spec (.of k))
    (v : DottedTangentArrow A.hom ((η[A]).left s)) :
    (Over.homMk v.val v.property.2 :
      Over.mk (dualNumberBasePoint A.hom ((η[A]).left s)) ⟶ A) ≫ endPolyEval α R =
      (Over.homMk v.val v.property.2) ^ R.coeff 0 := by
  obtain ⟨S, hS⟩ : C (p : ℤ) ∣ R - C (R.coeff 0) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · rw [coeff_sub, coeff_C, ite_eq_right hj, sub_zero]
      exact hR j hj
  have hRS : R = C (R.coeff 0) + C (p : ℤ) * S := by rw [← hS]; ring
  have := isMonHom_endPolyEval α S
  obtain ⟨w, hw⟩ := exists_homMk_tangent_comp_eq A (endPolyEval α S) s v
  conv_lhs => rw [hRS]
  rw [endPolyEval_add, endPolyEval_mul, endPolyEval_C, endPolyEval_C, MonObj.comp_mul,
    ← Category.assoc, hw, GrpObj.comp_zpow, GrpObj.comp_zpow, Category.comp_id, Category.comp_id,
    homMk_tangent_zpow_char_eq_one A p s w, mul_one]

end Tangent

section KernelPoints

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]

/-- Postcomposition with a homomorphism `α : A ⟶ A`, on the group `A(k)` of `k`-points written
additively. -/
abbrev postcompPoints (α : A ⟶ A) [IsMonHom α] :
    Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) →+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) :=
  (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).toAdditive

/-- **`R` evaluated at postcomposition with `α` is postcomposition with `R(α)`**, on `A(k)`. -/
theorem aeval_postcompPoints_apply (α : A ⟶ A) [IsMonHom α] (R : ℤ[X])
    (x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    (aeval (Stacks.Picard.asEnd (postcompPoints A α)) R) x =
      Additive.ofMul (x.toMul ≫ endPolyEval α R) := by
  induction R using Polynomial.induction_on generalizing x with
  | C c =>
    rw [aeval_C, endPolyEval_C, GrpObj.comp_zpow, Category.comp_id]
    change ((c : AddMonoid.End _) x) = _
    rw [AddMonoid.End.intCast_apply]
    rfl
  | add R S hR hS =>
    rw [map_add]
    change (aeval (Stacks.Picard.asEnd (postcompPoints A α)) R) x +
      (aeval (Stacks.Picard.asEnd (postcompPoints A α)) S) x = _
    rw [hR, hS, endPolyEval_add, MonObj.comp_mul]
    rfl
  | monomial n c ih =>
    have hpow : C c * Polynomial.X ^ (n + 1) = (C c * Polynomial.X ^ n) * Polynomial.X := by ring
    rw [hpow, map_mul]
    change (aeval (Stacks.Picard.asEnd (postcompPoints A α)) (C c * Polynomial.X ^ n))
      ((aeval (Stacks.Picard.asEnd (postcompPoints A α)) Polynomial.X) x) = _
    rw [aeval_X]
    change (aeval (Stacks.Picard.asEnd (postcompPoints A α)) (C c * Polynomial.X ^ n))
      (Additive.ofMul (x.toMul ≫ α)) = _
    rw [ih, endPolyEval_mul α (C c * Polynomial.X ^ n) Polynomial.X, endPolyEval_X]
    simp only [toMul_ofMul, Category.assoc]

/-- The kernel of `R` evaluated at postcomposition with `α`, on `A(k)`, is the set of points
killed by `R(α)`. -/
def kerAevalPostcompPointsEquiv (α : A ⟶ A) [IsMonHom α] (R : ℤ[X]) :
    (aeval (Stacks.Picard.asEnd (postcompPoints A α)) R).ker ≃
      {x : 𝟙_ (Over (Spec (.of k))) ⟶ A // x ≫ endPolyEval α R = 1} where
  toFun x := ⟨x.1.toMul, by
    have h : (aeval (Stacks.Picard.asEnd (postcompPoints A α)) R) x.1 = 0 := x.2
    rw [aeval_postcompPoints_apply] at h
    exact congrArg Additive.toMul h⟩
  invFun x := ⟨Additive.ofMul x.1, by
    change (aeval (Stacks.Picard.asEnd (postcompPoints A α)) R) (Additive.ofMul x.1) = 0
    rw [aeval_postcompPoints_apply]
    exact congrArg Additive.ofMul x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end KernelPoints

section EtaleAtUnit

variable (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A] (β : A ⟶ A) [IsMonHom β]

/-- A homomorphism is étale at a closed point iff it is étale at the identity: translation by the
corresponding point moves the identity to that point and preserves the étale locus. -/
private theorem etaleAt_iff_etaleAt_unit_of_mem_closedPoints [IsAlgClosed k] {y : A.left}
    (hyclosed : y ∈ closedPoints A.left) :
    AlgebraicGeometry.EtaleAt β.left y ↔
      AlgebraicGeometry.EtaleAt β.left ((η[A]).left (IsLocalRing.closedPoint k)) := by
  let point : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk
    ((pointEquivClosedPoint A.hom).symm ⟨y, hyclosed⟩).1
    ((pointEquivClosedPoint A.hom).symm ⟨y, hyclosed⟩).2
  have hpoint : point.left (IsLocalRing.closedPoint k) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint A.hom).apply_symm_apply ⟨y, hyclosed⟩)
  have htranslatePoint :=
    (mulRight_identity_point A point (IsLocalRing.closedPoint k)).trans hpoint
  rw [← htranslatePoint]
  exact etaleAt_translation_of_isMonHom A β point ((η[A]).left (IsLocalRing.closedPoint k))

/-- **A homomorphism of an abelian variety over an algebraically closed field which is étale at
the identity is étale**: its étale locus is open and translation-invariant, and every point
specializes to a closed point, which is a translate of the identity. -/
@[sga "3 XV 1.3" "translation reduction"]
theorem etale_left_of_etaleAt_unit [IsAlgClosed k]
    (he : AlgebraicGeometry.EtaleAt β.left ((η[A]).left (IsLocalRing.closedPoint k))) :
    Etale β.left := by
  have := LocallyOfFiniteType.jacobsonSpace A.hom
  rw [AlgebraicGeometry.etale_iff_forall_etaleAt]
  intro x
  by_contra hx
  have hopen : IsOpen {y : A.left | AlgebraicGeometry.EtaleAt β.left y} :=
    AlgebraicGeometry.isOpen_setOf_etaleAt _
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show {y : A.left | AlgebraicGeometry.EtaleAt β.left y}ᶜ.Nonempty from ⟨x, hx⟩)
    hopen.isClosed_compl.isLocallyClosed
  exact hy ((etaleAt_iff_etaleAt_unit_of_mem_closedPoints k A β hyclosed).mpr he)

omit [IsMonHom β] in
/-- A homomorphism étale at the identity fixes the generic point. -/
theorem left_genericPoint_of_etaleAt_unit
    (he : AlgebraicGeometry.EtaleAt β.left ((η[A]).left (IsLocalRing.closedPoint k))) :
    β.left (genericPoint A.left) = genericPoint A.left := by
  obtain ⟨U, -, heU, hEt⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt β.left _ he
  have hopen : IsOpen (Set.range (U.ι ≫ β.left)) := (U.ι ≫ β.left).isOpenMap.isOpen_range
  obtain ⟨w, hw⟩ : genericPoint A.left ∈ Set.range (U.ι ≫ β.left) :=
    ((genericPoint_spec A.left).mem_open_set_iff hopen).mpr
      ⟨_, Set.mem_univ _, Set.mem_range_self ⟨_, heU⟩⟩
  have hsp : β.left (genericPoint A.left) ⤳ genericPoint A.left := by
    have h := (genericPoint_specializes (U.ι w)).map β.left.continuous
    rwa [← Scheme.Hom.comp_apply, hw] at h
  have hgen : IsGenericPoint (β.left (genericPoint A.left)) (⊤ : Set A.left) := by
    have h := specializes_iff_closure_subset.mp hsp
    rw [(genericPoint_spec A.left).def] at h
    exact isGenericPoint_def.mpr (top_le_iff.mp h)
  exact hgen.eq (genericPoint_spec A.left)

/-- **A homomorphism étale at the identity is finite locally free of rank its degree**: it is
étale and proper, hence finite and flat. -/
theorem isFiniteLocallyFreeOfRank_endDegree_of_etaleAt_unit [IsAlgClosed k]
    (he : AlgebraicGeometry.EtaleAt β.left ((η[A]).left (IsLocalRing.closedPoint k))) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank β.left (endDegree A β) := by
  have := etale_left_of_etaleAt_unit k A β he
  have : IsProper β.left := isProper_left_of_isAbelianVariety A β
  have : IsFinite β.left := by
    rw [AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite]
    exact ⟨inferInstance, inferInstance⟩
  have := isFiniteLocallyFree_of_isFinite_of_flat A β.left
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hgen := left_genericPoint_of_etaleAt_unit k A β he
  have hdom : IsDominant β.left := by
    have hsub : ({genericPoint A.left} : Set A.left) ⊆ Set.range β.left.base := by
      rw [Set.singleton_subset_iff, ← hgen]
      exact Set.mem_range_self _
    exact ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_subset (closure_mono hsub)
      (genericPoint_closure (α := (A.left : Type u))))⟩
  have hrank := isFiniteLocallyFreeOfRank_degreeOver β.left hgen
    (preimage_genericPoint_of_locallyQuasiFinite β.left hgen)
  rwa [endDegree, dite_eq_left hdom]

/-- **The `k`-points of the kernel of a homomorphism étale at the identity number its degree**,
for `k` algebraically closed: the kernel is finite étale of rank `deg β` over `k`. -/
theorem natCard_comp_eq_one_eq_endDegree_of_etaleAt_unit [IsAlgClosed k]
    (he : AlgebraicGeometry.EtaleAt β.left ((η[A]).left (IsLocalRing.closedPoint k))) :
    Nat.card {x : 𝟙_ (Over (Spec (.of k))) ⟶ A // x ≫ β = 1} = endDegree A β := by
  have := etale_left_of_etaleAt_unit k A β he
  have hrank := isFiniteLocallyFreeOfRank_endDegree_of_etaleAt_unit k A β he
  have hpb := IsPullback.of_hasPullback β.left (η[A]).left
  have hrank' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd β.left (η[A]).left) (endDegree A β) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hpb
  have hetK : Etale (pullback.snd β.left (η[A]).left) := inferInstance
  have hone : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) = η[A] := by
    rw [CategoryTheory.Hom.one_def]
    change (𝟙 (Over.mk (𝟙 (Spec (.of k)))) ≫ η[A]) = η[A]
    exact Category.id_comp _
  rw [hone]
  exact (Nat.card_congr (pullbackKernelPointsEquiv β (η[A]))).trans
    (Stacks.Morphisms.card_sections_of_etale_of_isAlgClosed _ _ hrank' hetK)

/-- A homomorphism étale at some closed point is étale at the identity: translation by a point
moves the identity to that point and preserves the étale locus. -/
theorem etaleAt_unit_of_etaleAt_closedPoint [IsAlgClosed k] {y : A.left}
    (hyclosed : y ∈ closedPoints A.left) (hy : AlgebraicGeometry.EtaleAt β.left y) :
    AlgebraicGeometry.EtaleAt β.left ((η[A]).left (IsLocalRing.closedPoint k)) := by
  exact (etaleAt_iff_etaleAt_unit_of_mem_closedPoints k A β hyclosed).mp hy

end EtaleAtUnit

section CharZero

variable (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A] (β : A ⟶ A) [IsMonHom β]

/-- The stalk map at the generic point of a dominant endomorphism of an integral scheme is formally
unramified as soon as the induced map of function fields is. -/
theorem formallyUnramified_stalkMap_genericPoint_of_dominantFunctionFieldMap {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ X) [IsDominant f]
    (h : (dominantFunctionFieldMap f).FormallyUnramified) :
    (f.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  have key : ∀ (y : X) (hy : y = genericPoint X)
      (g : X.presheaf.stalk y ⟶ X.presheaf.stalk (genericPoint X)),
      (hy ▸ g).hom.FormallyUnramified → g.hom.FormallyUnramified := by
    rintro y rfl g hg
    exact hg
  exact key _ _ _ h

/-- A homomorphism of fields of characteristic zero which makes the target a nonzero finite
dimensional vector space is formally unramified: the extension is finite, hence separable. -/
theorem formallyUnramified_of_finrank_ne_zero {K L : Type*} [Field K] [Field L] [CharZero K]
    (f : K →+* L) (h : (letI := f.toAlgebra; Module.finrank K L) ≠ 0) : f.FormallyUnramified := by
  let := f.toAlgebra
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  exact Algebra.FormallyUnramified.of_isSeparable K L

omit [IsMonHom β] in
/-- **In characteristic zero a homomorphism of nonzero degree is étale at the generic point.** It
is dominant and fixes the generic point; the extension of function fields is finite, of degree
`deg β`, hence separable, hence formally unramified; the local rings at the generic point are
fields, so unramifiedness there is étaleness. -/
theorem etaleAt_genericPoint_of_charZero [CharZero k] (hβ : endDegree A β ≠ 0) :
    AlgebraicGeometry.EtaleAt β.left (genericPoint A.left) := by
  classical
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper β.left := isProper_left_of_isAbelianVariety A β
  have : LocallyOfFiniteType (β.left ≫ A.hom) := β.w.symm ▸ inferInstance
  have : LocallyOfFiniteType β.left := locallyOfFiniteType_of_comp β.left A.hom
  have := smooth_hom A
  have := isLocallyNoetherian_left A
  have hdom : IsDominant β.left := by
    by_contra h
    exact hβ (by rw [endDegree, dite_eq_right h])
  have hgen : β.left (genericPoint A.left) = genericPoint A.left :=
    ((tfae_isDominant_of_isIntegral β.left).out 1 2).mp hdom
  have hdeg : degreeOver β.left ≠ 0 := by rwa [endDegree, dite_eq_left hdom] at hβ
  have hunr : UnramifiedAt β.left (genericPoint A.left) := by
    rw [unramifiedAt_iff_formallyUnramified_stalkMap]
    refine formallyUnramified_stalkMap_genericPoint_of_dominantFunctionFieldMap β.left ?_
    unfold degreeOver at hdeg
    have : CharZero A.left.functionField :=
      charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.presheaf.germ ⊤ (genericPoint A.left) trivial).hom) (RingHom.injective _)
    exact formallyUnramified_of_finrank_ne_zero _ hdeg
  have : IsRegularLocalRing (A.left.presheaf.stalk (genericPoint A.left)) :=
    isRegularLocalRing_stalk_of_smooth_over_field A.hom _
  have : IsRegularLocalRing (A.left.presheaf.stalk (β.left.base (genericPoint A.left))) :=
    isRegularLocalRing_stalk_of_smooth_over_field A.hom _
  exact AlgebraicGeometry.etaleAt_of_unramifiedAt_of_ringKrullDim_eq β.left _ hunr
    (congrArg (fun y : A.left => ringKrullDim (A.left.presheaf.stalk y)) hgen.symm)

/-- **In characteristic zero a homomorphism of nonzero degree is étale at the identity**: it is
étale at the generic point, so on a nonempty open, which contains a closed point. -/
theorem etaleAt_unit_of_charZero [IsAlgClosed k] [CharZero k] (hβ : endDegree A β ≠ 0) :
    AlgebraicGeometry.EtaleAt β.left ((η[A]).left (IsLocalRing.closedPoint k)) := by
  have := LocallyOfFiniteType.jacobsonSpace A.hom
  have hopen : IsOpen {y : A.left | AlgebraicGeometry.EtaleAt β.left y} :=
    AlgebraicGeometry.isOpen_setOf_etaleAt _
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show {y : A.left | AlgebraicGeometry.EtaleAt β.left y}.Nonempty from
      ⟨_, etaleAt_genericPoint_of_charZero k A β hβ⟩) hopen.isLocallyClosed
  exact etaleAt_unit_of_etaleAt_closedPoint k A β hyclosed hy

/-- **In characteristic zero the kernel of a homomorphism of nonzero degree has `deg β`
`k`-points.** -/
theorem natCard_comp_eq_one_eq_endDegree_of_charZero [IsAlgClosed k] [CharZero k]
    (hβ : endDegree A β ≠ 0) :
    Nat.card {x : 𝟙_ (Over (Spec (.of k))) ⟶ A // x ≫ β = 1} = endDegree A β :=
  natCard_comp_eq_one_eq_endDegree_of_etaleAt_unit k A β (etaleAt_unit_of_charZero k A β hβ)

end CharZero

section CharP

variable (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- **In characteristic `p`, the kernel of `R(α)` has `deg R(α)` `k`-points when `R` is congruent
modulo `p` to a constant prime to `p`**: the derivative of `R(α)` at the identity is then
multiplication by that constant (`Stacks.Groupoids.homMk_tangent_comp_endPolyEval_of_modEq`), and
`Stacks.Groupoids.natCard_comp_eq_one_eq_endDegree` applies. -/
theorem natCard_comp_endPolyEval_eq_one_eq_endDegree_of_charP [IsAlgClosed k] (p : ℕ)
    [CharP k p] (α : A ⟶ A) [IsMonHom α] (R : ℤ[X]) (hR0 : ¬ (p : ℤ) ∣ R.coeff 0)
    (hR : ∀ j, j ≠ 0 → (p : ℤ) ∣ R.coeff j) :
    Nat.card {x : 𝟙_ (Over (Spec (.of k))) ⟶ A // x ≫ endPolyEval α R = 1} =
      endDegree A (endPolyEval α R) := by
  have := isMonHom_endPolyEval α R
  refine natCard_comp_eq_one_eq_endDegree k A (endPolyEval α R) (R.coeff 0) ?_
    (fun s v => homMk_tangent_comp_endPolyEval_of_modEq A p α R hR s v)
  rwa [isUnit_iff_ne_zero, Ne, CharP.intCast_eq_zero_iff k p]

end CharP

section Rank

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- **The degree of an endomorphism which is finite locally free of rank `d` is `d`.** A finite
locally free morphism is open and closed, so its image is all of the irreducible `A`; it is
dominant, fixes the generic point, and its rank is the degree of the extension of function
fields. -/
theorem endDegree_eq_of_isFiniteLocallyFreeOfRank (f : A ⟶ A) (d : ℕ)
    [hf : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f.left d] : endDegree A f = d := by
  classical
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper f.left := isProper_left_of_isAbelianVariety A f
  have : LocallyOfFiniteType (f.left ≫ A.hom) := f.w.symm ▸ inferInstance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left A.hom
  have hfl := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f.left d
  have := Stacks.Morphisms.IsFiniteLocallyFree.isFinite f.left
  have := Stacks.Morphisms.IsFiniteLocallyFree.flat f.left
  have := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation f.left
  have hclosed : IsClosed (Set.range f.left.base) := f.left.isClosedMap.isClosed_range
  have hopen : IsOpen (Set.range f.left.base) := f.left.isOpenMap.isOpen_range
  have hne : (Set.range f.left.base).Nonempty := ⟨_, Set.mem_range_self (genericPoint A.left)⟩
  have huniv : Set.range f.left.base = Set.univ :=
    (isClopen_iff.mp ⟨hclosed, hopen⟩).resolve_left hne.ne_empty
  have hdom : IsDominant f.left := ⟨by rw [DenseRange, huniv]; exact dense_univ⟩
  have hgen : f.left (genericPoint A.left) = genericPoint A.left :=
    ((tfae_isDominant_of_isIntegral f.left).out 1 2).mp hdom
  have hrank := isFiniteLocallyFreeOfRank_degreeOver f.left hgen
    (preimage_genericPoint_of_locallyQuasiFinite f.left hgen)
  rw [endDegree, dite_eq_left hdom]
  have h1 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f.left _).mp hrank
    (genericPoint A.left)
  have h2 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f.left d).mp hf
    (genericPoint A.left)
  exact h1.symm.trans h2

end Rank

end Stacks.Groupoids
