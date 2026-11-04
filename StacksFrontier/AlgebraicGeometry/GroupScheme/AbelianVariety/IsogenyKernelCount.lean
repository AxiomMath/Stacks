module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowEtaleOfIsUnit
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionScheme
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.EndomorphismNormForm
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.TangentIdentity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of an étale endomorphism of an abelian variety

Let `A` be an abelian variety over an algebraically closed field `k` and `β : A ⟶ A` a
homomorphism whose derivative at the identity is multiplication by an integer `d` invertible in
`k` (in the form: for every tangent vector `v` at the identity, read as a point of `A` with values
in the dual numbers, `v ≫ β = v ^ d`). Then `β` is étale, finite and finite locally free of rank
its degree, so the group of `k`-points of `Ker β` has exactly `deg β` elements.

This is the argument of [Stacks, Tag 0BFH] for `[d]` (unramified at the identity by Tag 0B2G,
étale there by miracle flatness, étale everywhere by translation) applied to `β`, followed by the
count of the points of a finite étale scheme over an algebraically closed field.

## Main results

* `Stacks.Groupoids.etale_left_of_comp_tangent_eq_zpow`: `β` is étale.
* `Stacks.Groupoids.natCard_comp_eq_one_eq_endDegree`: `#{x ∈ A(k) : β ∘ x = 0} = deg β`.
* `Stacks.Groupoids.comp_endPolyEval_of_comp_eq_one`: `x ≫ R(α) = x ^ R(0)` when `x ≫ α = 1`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

section Polynomial

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {G : C} [GrpObj G] [IsCommMonObj G]

/-- Peeling one factor of `X` off a monomial. -/
private theorem C_mul_X_pow_succ (c : ℤ) (n : ℕ) :
    Polynomial.C c * Polynomial.X ^ (n + 1) =
      (Polynomial.C c * Polynomial.X ^ n) * Polynomial.X := by ring

/-- **A polynomial in `α` on a point killed by `α`.** If `x ≫ α = 1` then
`x ≫ R(α) = x ^ R(0)`: the terms of positive degree vanish on `x`. -/
theorem comp_endPolyEval_of_comp_eq_one (α : G ⟶ G) [IsMonHom α] {Y : C} (x : Y ⟶ G)
    (hx : x ≫ α = 1) (R : Polynomial ℤ) :
    x ≫ endPolyEval α R = x ^ R.coeff 0 := by
  induction R using Polynomial.induction_on with
  | C c =>
    rw [endPolyEval_C, GrpObj.comp_zpow, Category.comp_id, Polynomial.coeff_C_zero]
  | add R S hR hS =>
    rw [endPolyEval_add, MonObj.comp_mul, hR, hS, Polynomial.coeff_add, zpow_add]
  | monomial n c _ =>
    rw [C_mul_X_pow_succ, endPolyEval_mul, endPolyEval_X, ← Category.assoc, hx,
      ← C_mul_X_pow_succ, Polynomial.coeff_C_mul_X_pow, if_neg (by lia), zpow_zero]
    have h1 : (1 : G ⟶ G) ≫ endPolyEval α (Polynomial.C c * Polynomial.X ^ n) = 1 := by
      rw [endPolyEval, ← postcompHom_apply]
      exact congrArg Additive.toMul (map_zero (Polynomial.aeval (postcompOf α)
        (Polynomial.C c * Polynomial.X ^ n)).1)
    rw [← MonObj.comp_one (1 : Y ⟶ G), Category.assoc, h1]

/-- The product of two homomorphisms into a commutative group object is a homomorphism. -/
theorem isMonHom_mul {H : C} [MonObj H] (f g : H ⟶ G) [IsMonHom f] [IsMonHom g] :
    IsMonHom (f * g) := by
  have : ∀ Y : C, IsMulCommutative (Y ⟶ G) := fun Y =>
    (isCommMonObj_iff_isMulCommutative G).mp inferInstance Y
  constructor
  · rw [MonObj.comp_mul, IsMonHom.one_hom f, IsMonHom.one_hom g]
    have h1 : (η[G] : 𝟙_ C ⟶ G) = 1 := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [h1, one_mul]
  · have hμH : (μ[H]) = fst H H * snd H H := by
      rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hμG : ∀ a b : H ⊗ H ⟶ G, lift a b ≫ μ[G] = a * b := fun a b => rfl
    have hten : ∀ a : H ⟶ G, (a ⊗ₘ a) = lift (fst H H ≫ a) (snd H H ≫ a) := by
      intro a
      ext <;> simp
    rw [MonObj.comp_mul, IsMonHom.mul_hom f, IsMonHom.mul_hom g, hten, hten, hten, hμG, hμG,
      hμG, MonObj.comp_mul, MonObj.comp_mul]
    exact mul_mul_mul_comm (fst H H ≫ f) (snd H H ≫ f) (fst H H ≫ g) (snd H H ≫ g)

/-- A polynomial in a homomorphism of a commutative group object is a homomorphism. -/
theorem isMonHom_endPolyEval (α : G ⟶ G) [IsMonHom α] (R : Polynomial ℤ) :
    IsMonHom (endPolyEval α R) := by
  induction R using Polynomial.induction_on with
  | C c => rw [endPolyEval_C]; infer_instance
  | add R S hR hS =>
    rw [endPolyEval_add]
    exact isMonHom_mul _ _
  | monomial n c ih =>
    rw [C_mul_X_pow_succ, endPolyEval_mul, endPolyEval_X]
    infer_instance

end Polynomial

/-- An endomorphism over `S` of a locally-finite-type `S`-scheme is locally of finite type. -/
private theorem locallyOfFiniteType_left_of_isMonHom {S : Scheme.{u}} (G : Over S) (β : G ⟶ G)
    [LocallyOfFiniteType G.hom] :
    LocallyOfFiniteType β.left := by
  have : LocallyOfFiniteType (β.left ≫ G.hom) := β.w.symm ▸ inferInstance
  exact locallyOfFiniteType_of_comp β.left G.hom

section Tangent

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (β : G ⟶ G) [IsMonHom β]

/-- A homomorphism fixes the identity point. -/
theorem left_unit_apply_of_isMonHom (s : S) : β.left ((η[G]).left s) = (η[G]).left s :=
  congrArg (fun f : S ⟶ G.left => f s) (congrArg Over.Hom.left (IsMonHom.one_hom β))

/-- A homomorphism does not change the residue field at the identity. -/
theorem isIso_residueFieldMap_unit_of_isMonHom (s : S) :
    IsIso (β.left.residueFieldMap ((η[G]).left s)) := by
  have : IsIso (G.hom.residueFieldMap ((η[G]).left s)) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left (η[G]).w s
  rw [residueFieldMap_eq_residueFieldCongr_of_fixed G.hom _ β.w
    ((η[G]).left s) (left_unit_apply_of_isMonHom G β s)]
  infer_instance

/-- **The derivative of a homomorphism at the identity**, when it acts on dual-number points at
the identity as the `d`-th power, is multiplication by `d`. -/
@[sga "3 II 4.1.1.2" "b), special case"]
theorem tangentMap_unit_eq_zsmul_of_comp (s : S) (d : ℤ)
    (hβ : ∀ v : DottedTangentArrow G.hom ((η[G]).left s),
      (Over.homMk v.val v.property.2 :
        Over.mk (dualNumberBasePoint G.hom ((η[G]).left s)) ⟶ G) ≫ β =
        (Over.homMk v.val v.property.2) ^ d)
    (v : DottedTangentArrow G.hom ((η[G]).left s)) :
    letI := isIso_residueFieldMap_unit_of_isMonHom G β s
    (left_unit_apply_of_isMonHom G β s ▸ tangentMap β.left G.hom G.hom β.w ((η[G]).left s) v :
        DottedTangentArrow G.hom ((η[G]).left s)) = d • v := by
  have := isIso_residueFieldMap_unit_of_isMonHom G β s
  have := AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left
    (η[G]).w s
  apply Subtype.ext
  rw [tangentMap_fixed_apply G.hom _ β.w ((η[G]).left s) (left_unit_apply_of_isMonHom G β s) v,
    tangentArrow_zsmul_val]
  exact congrArg Over.Hom.left (hβ v)

/-- Translation by a point intertwines a homomorphism `β` with translation by the image point. -/
theorem mulRight_comp_of_isMonHom (point : 𝟙_ (Over S) ⟶ G) :
    (GrpObj.mulRight point).hom ≫ β = β ≫ (GrpObj.mulRight (point ≫ β)).hom := by
  show ((𝟙 G : G ⟶ G) * (toUnit G ≫ point)) ≫ β =
    β ≫ ((𝟙 G : G ⟶ G) * (toUnit G ≫ point ≫ β))
  rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id,
    ← Category.assoc β, comp_toUnit, Category.assoc]

/-- **The étale locus of a homomorphism is translation-invariant.** -/
theorem etaleAt_translation_of_isMonHom (point : 𝟙_ (Over S) ⟶ G) (x : G.left) :
    AlgebraicGeometry.EtaleAt β.left ((GrpObj.mulRight point).hom.left x) ↔
      AlgebraicGeometry.EtaleAt β.left x := by
  have : IsIso (GrpObj.mulRight point).hom.left :=
    ((Over.forget S).mapIso (GrpObj.mulRight point)).isIso_hom
  have : IsIso (GrpObj.mulRight (point ≫ β)).hom.left :=
    ((Over.forget S).mapIso (GrpObj.mulRight (point ≫ β))).isIso_hom
  refine etaleAt_iff_of_isIso_square_self _ (GrpObj.mulRight point).hom.left
    (GrpObj.mulRight (point ≫ β)).hom.left ?_ x
  simpa only [Over.comp_left] using congrArg Over.Hom.left (mulRight_comp_of_isMonHom G β point)

end Tangent

section AbelianVariety

variable (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A] (β : A ⟶ A) [IsMonHom β] (d : ℤ)
  (hd : IsUnit ((d : ℤ) : k))
  (hβ : ∀ (s : Spec (.of k)) (v : DottedTangentArrow A.hom ((η[A]).left s)),
    (Over.homMk v.val v.property.2 :
      Over.mk (dualNumberBasePoint A.hom ((η[A]).left s)) ⟶ A) ≫ β =
      (Over.homMk v.val v.property.2) ^ d)

include hd hβ

/-- A homomorphism of an abelian variety whose derivative at the identity is multiplication by
an invertible integer is unramified at the identity (Tag 0B2G). -/
theorem unramifiedAt_unit_of_comp_tangent_eq_zpow (s : Spec (.of k)) :
    UnramifiedAt β.left ((η[A]).left s) := by
  let e : A.left := (η[A]).left s
  have := AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section A.hom (η[A]).left
    (η[A]).w s
  have := isIso_residueFieldMap_unit_of_isMonHom A β s
  have := locallyOfFiniteType_left_of_isMonHom A β
  have hfix : β.left e = e := left_unit_apply_of_isMonHom A β s
  refine (injective_tangentMap_iff_unramifiedAt β.left A.hom A.hom e β.w).mp
    fun first second hEq => ?_
  have htransport := congrArg
    (fun vector => (hfix ▸ vector : DottedTangentArrow A.hom e)) hEq
  have hsmul : d • first = d • second :=
    (tangentMap_unit_eq_zsmul_of_comp A β s d (hβ s) first).symm.trans
      (htransport.trans (tangentMap_unit_eq_zsmul_of_comp A β s d (hβ s) second))
  have hunit := (isUnit_intCast_residueField_iff k A.left A.hom e d).mpr hd
  have hEq' : (d : A.left.residueField e) • first = (d : A.left.residueField e) • second := by
    simpa only [Int.cast_smul_eq_zsmul] using hsmul
  have hcancel := congrArg (fun vector => (d : A.left.residueField e)⁻¹ • vector) hEq'
  simpa [smul_smul, hunit.ne_zero] using hcancel

/-- Such a homomorphism is étale at the identity: it fixes the identity, the local ring there is
regular, and miracle flatness upgrades unramifiedness to étaleness. -/
theorem etaleAt_unit_of_comp_tangent_eq_zpow (s : Spec (.of k)) :
    AlgebraicGeometry.EtaleAt β.left ((η[A]).left s) := by
  have := smooth_hom A
  have := isLocallyNoetherian_left A
  have := locallyOfFiniteType_left_of_isMonHom A β
  have hfix : β.left ((η[A]).left s) = (η[A]).left s := left_unit_apply_of_isMonHom A β s
  have : IsRegularLocalRing (A.left.presheaf.stalk ((η[A]).left s)) :=
    isRegularLocalRing_stalk_of_smooth_over_field A.hom ((η[A]).left s)
  have : IsRegularLocalRing (A.left.presheaf.stalk (β.left.base ((η[A]).left s))) :=
    isRegularLocalRing_stalk_of_smooth_over_field A.hom _
  exact AlgebraicGeometry.etaleAt_of_unramifiedAt_of_ringKrullDim_eq β.left ((η[A]).left s)
    (unramifiedAt_unit_of_comp_tangent_eq_zpow k A β d hd hβ s)
    (congrArg (fun y : A.left => ringKrullDim (A.left.presheaf.stalk y)) hfix.symm)

/-- **A homomorphism of an abelian variety over an algebraically closed field whose derivative at
the identity is multiplication by an invertible integer is étale.** -/
theorem etale_left_of_comp_tangent_eq_zpow [IsAlgClosed k] : Etale β.left := by
  have := LocallyOfFiniteType.jacobsonSpace A.hom
  rw [AlgebraicGeometry.etale_iff_forall_etaleAt]
  intro x
  by_contra hx
  have hopen : IsOpen {y : A.left | AlgebraicGeometry.EtaleAt β.left y} :=
    AlgebraicGeometry.isOpen_setOf_etaleAt _
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show {y : A.left | AlgebraicGeometry.EtaleAt β.left y}ᶜ.Nonempty from ⟨x, hx⟩)
    hopen.isClosed_compl.isLocallyClosed
  let point : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk
    ((pointEquivClosedPoint A.hom).symm ⟨y, hyclosed⟩).1
    ((pointEquivClosedPoint A.hom).symm ⟨y, hyclosed⟩).2
  have hpoint : point.left (IsLocalRing.closedPoint k) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint A.hom).apply_symm_apply ⟨y, hyclosed⟩)
  have hidentity := etaleAt_unit_of_comp_tangent_eq_zpow k A β d hd hβ
    (IsLocalRing.closedPoint k)
  have htranslation := (etaleAt_translation_of_isMonHom A β point
    ((η[A]).left (IsLocalRing.closedPoint k))).mpr hidentity
  have htranslatePoint :=
    (mulRight_identity_point A point (IsLocalRing.closedPoint k)).trans hpoint
  exact hy (htranslatePoint ▸ htranslation)

/-- Such a homomorphism fixes the generic point: it is étale, hence open, near the identity, so
its image contains the generic point, and a generization of the generic point is the generic
point. -/
theorem left_genericPoint_of_comp_tangent_eq_zpow :
    β.left (genericPoint A.left) = genericPoint A.left := by
  obtain ⟨U, -, heU, hEt⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt β.left _
    (etaleAt_unit_of_comp_tangent_eq_zpow k A β d hd hβ (IsLocalRing.closedPoint k))
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

/-- Such a homomorphism is dominant. -/
theorem isDominant_left_of_comp_tangent_eq_zpow : IsDominant β.left := by
  have hsub : ({genericPoint A.left} : Set A.left) ⊆ Set.range β.left.base := by
    rw [Set.singleton_subset_iff, ← left_genericPoint_of_comp_tangent_eq_zpow k A β d hd hβ]
    exact Set.mem_range_self _
  exact ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_subset (closure_mono hsub)
    (genericPoint_closure (α := (A.left : Type u))))⟩

/-- **Such a homomorphism is finite locally free of rank its degree** ([Stacks, Tag 02KB]): it is
étale and proper, hence finite and flat, and the rank of a finite locally free morphism of
integral schemes is the degree of the extension of function fields. -/
theorem isFiniteLocallyFreeOfRank_endDegree_of_comp_tangent_eq_zpow [IsAlgClosed k] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank β.left (endDegree A β) := by
  have := etale_left_of_comp_tangent_eq_zpow k A β d hd hβ
  have : IsProper β.left := isProper_left_of_isAbelianVariety A β
  have : IsFinite β.left := by
    rw [AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite]
    exact ⟨inferInstance, inferInstance⟩
  have := isFiniteLocallyFree_of_isFinite_of_flat A β.left
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hdom := isDominant_left_of_comp_tangent_eq_zpow k A β d hd hβ
  have hgen := left_genericPoint_of_comp_tangent_eq_zpow k A β d hd hβ
  have hrank := isFiniteLocallyFreeOfRank_degreeOver β.left hgen
    (preimage_genericPoint_of_locallyQuasiFinite β.left hgen)
  rwa [endDegree, dif_pos hdom]

/-- **The `k`-points of the kernel of a homomorphism whose derivative at the identity is
multiplication by an invertible integer number its degree**, for `k` algebraically closed: the
kernel is finite étale of rank `deg β` over `k`. -/
theorem natCard_comp_eq_one_eq_endDegree [IsAlgClosed k] :
    Nat.card {x : 𝟙_ (Over (Spec (.of k))) ⟶ A // x ≫ β = 1} = endDegree A β := by
  have := etale_left_of_comp_tangent_eq_zpow k A β d hd hβ
  have hrank := isFiniteLocallyFreeOfRank_endDegree_of_comp_tangent_eq_zpow k A β d hd hβ
  have hpb := IsPullback.of_hasPullback β.left (η[A]).left
  have hrank' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd β.left (η[A]).left) (endDegree A β) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hpb
  have hetK : Etale (pullback.snd β.left (η[A]).left) := inferInstance
  have hone : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) = η[A] := by
    rw [CategoryTheory.Hom.one_def]
    show (𝟙 (Over.mk (𝟙 (Spec (.of k)))) ≫ η[A]) = η[A]
    exact Category.id_comp _
  rw [hone]
  exact (Nat.card_congr (pullbackKernelPointsEquiv β (η[A]))).trans
    (Stacks.Morphisms.card_sections_of_etale_of_isAlgClosed _ _ hrank' hetK)

end AbelianVariety

end Stacks.Groupoids
