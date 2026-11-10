/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerSumMap
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TraceFromDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Pullback
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The trace of an endomorphism of an abelian variety from intersection numbers on `C^g`

Let `C` be a smooth proper curve over an algebraically closed field `k` with a rational point
`c₀`, let `J` be an abelian variety of dimension `g ≥ 1` over `k`, `aj : C ⟶ J` a morphism with
`aj(c₀) = 0`, and `L` an invertible module on `J` such that

* `B(aj ∘ p₀, aj ∘ p₁) = {c₀} × C + C × {c₀} - Δ` on `C × C`, where `B` is the biadditive form of
  `f ↦ [f^* L]`, and
* `deg aj^* L = g`.

Then for every homomorphism `α : J ⟶ J`, `Tr(α) = deg aj^* B(α, 1)`
(`Stacks.CurvePower.abelianVarietyTrace_eq_curveDeg`). The proof pulls the identity
`Tr(α) · (W^g · J) = 2 ∑ᵢ (W, …, B(α, 1), …, W · J)` of
`Stacks.Groupoids.abelianVarietyTrace_mul_eq_two_mul_sum`, `W = L + (-1)^* L`, back along
`σ = ∑ᵢ aj ∘ pᵢ : C^g ⟶ J` ([Stacks, Tag 0BET]) and evaluates both sides with the closed form
`Stacks.CurvePower.powerForm_sumMapTuple_eq`. That needs `deg (-aj)^* L = g` as well; this
comes from `P = L - (-1)^* L`: `f ↦ [f^* P]` is additive, so `σ^* P = ∑ᵢ pᵢ^* aj^* P` on
`C^(g+1)` has self-intersection `(g+1)! (deg aj^* P)^(g+1)`, which vanishes by Tag 0BET because
`J` has dimension `g < g + 1`.

## Main results

* `AlgebraicGeometry.exists_intersectionNumber_pullback_eq_mul`: the degree formula of Tag
  0BET for a morphism of integral proper varieties of the same dimension, in the form
  `(f^*𝓛_1 ⋯ f^*𝓛_d · Y) = δ (𝓛_1 ⋯ 𝓛_d · X)` for one integer `δ`.
* `Stacks.CurvePower.abelianVarietyTrace_eq_curveDeg`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open AlgebraicGeometry Finset
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- **[Stacks, Tag 0BET] for a morphism of integral proper schemes of the same dimension.**
There is an integer `δ` (the degree of `f` onto its image, or `0`) with
`(f^*𝓛_1 ⋯ f^*𝓛_d · Y) = δ (𝓛_1 ⋯ 𝓛_d · X)` for all invertible `𝓛_i` on `X`. -/
theorem exists_intersectionNumber_pullback_eq_mul {X Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k))
    (pX : X ⟶ Spec (.of k)) [IsProper pY] [IsProper pX] (f : Y ⟶ X) (hf : f ≫ pX = pY)
    [IsIntegral Y] [IsIntegral X] (d : ℕ) (hY : topologicalKrullDim Y = d)
    (hX : topologicalKrullDim X = d) :
    ∃ δ : ℤ, ∀ (L : Fin d → X.Modules)
      [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)],
      intersectionNumber k pY (𝟙 Y) d hY.le (fun j => (Scheme.Modules.pullback f).obj (L j)) =
        δ * intersectionNumber k pX (𝟙 X) d hX.le L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have hcomp : 𝟙 Y ≫ f = f := Category.id_comp f
  have hle : topologicalKrullDim (𝟙 Y ≫ f).image ≤ d := by
    rw [← hX]
    exact (𝟙 Y ≫ f).imageι.isClosedEmbedding.isInducing.topologicalKrullDim_le
  rcases hle.lt_or_eq with hlt | heq
  · exact ⟨0, fun L _ => by
      rw [zero_mul]
      exact intersectionNumber_pullback_eq_zero k pY pX f hf (𝟙 Y) d hY.le L hlt⟩
  · have : IsProper (𝟙 Y ≫ f) := isProper_comp_of_structureMap k pY pX f hf (𝟙 Y)
    have : IsIntegral (𝟙 Y ≫ f).image := Stacks.Chow.isIntegral_image (𝟙 Y ≫ f)
    have : IsProper (𝟙 Y ≫ f).toImage := Stacks.Chow.isProper_toImage (𝟙 Y ≫ f)
    refine ⟨degreeOver (𝟙 Y ≫ f).toImage, fun L _ => ?_⟩
    rw [intersectionNumber_pullback_eq_degreeOver_mul k pY pX f hf (𝟙 Y) d hY L heq]
    congr 1
    have : CompactSpace X :=
      ⟨QuasiCompact.isCompact_preimage (f := pX) _ isOpen_univ isCompact_univ⟩
    have : IsNoetherian X := {}
    have hsupp : (𝟙 Y ≫ f).ker.support = ⊤ := by
      by_contra hne
      have hclosed : IsClosed ((𝟙 Y ≫ f).ker.support : Set X) :=
        (𝟙 Y ≫ f).ker.support.isClosed
      obtain ⟨y, hy⟩ : (((𝟙 Y ≫ f).ker.support : Set X)ᶜ).Nonempty := by
        rw [Set.nonempty_compl]
        intro h
        exact hne (TopologicalSpace.Closeds.ext h)
      have hnd : IsNowhereDense ((𝟙 Y ≫ f).ker.support : Set X) := by
        rw [hclosed.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
        intro x hx
        obtain ⟨z, -, hz⟩ := (IrreducibleSpace.isIrreducible_univ X).2 _ _ isOpen_interior
          hclosed.isOpen_compl ⟨x, trivial, hx⟩ ⟨y, trivial, hy⟩
        exact hz.2 (interior_subset hz.1)
      have hlt := hnd.topologicalKrullDim_lt hclosed inferInstance
        (by rw [hX]; exact ne_of_beq_false rfl)
      have hrange := Scheme.IdealSheafData.range_subschemeι (𝟙 Y ≫ f).ker
      have hind : Topology.IsInducing (Set.codRestrict (𝟙 Y ≫ f).imageι.base
          ((𝟙 Y ≫ f).ker.support : Set X) (fun x => hrange ▸ Set.mem_range_self x)) :=
        (𝟙 Y ≫ f).imageι.isClosedEmbedding.isInducing.codRestrict _
      have h2 := hind.topologicalKrullDim_le
      rw [heq, hX] at *
      exact absurd (lt_of_le_of_lt h2 hlt) (lt_irrefl _)
    have : IsIso (𝟙 Y ≫ f).imageι :=
      (Scheme.isIso_subschemeι_iff_eq_bot _).2
        ((Scheme.IdealSheafData.support_eq_top_iff).1 hsupp)
    exact intersectionNumber_eq_intersectionNumber_id k pX _ d _ hX.le L

end AlgebraicGeometry

namespace Stacks.CurvePower

section Trace

variable {k : Type u} [Field k] [IsAlgClosed k] (C : Over (Spec (.of k))) [IsVariety k C.hom]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] (hC : topologicalKrullDim C.left = 1)
  (c₀ : power C 0 ⟶ C)

/-- The Picard group of `C^0 = Spec k` is trivial. -/
instance subsingleton_powerPic_zero : Subsingleton (PowerPic C 0) :=
  Stacks.SheafOfModules.subsingleton_picardGroup _ _ fun L hL => by
    have : Stacks.SheafOfModules.IsInvertible (Spec (CommRingCat.of k)).presheaf
        (structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace).property L := hL
    exact Stacks.PicardUFD.isTrivial_of_isInvertible_spec k L

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- A class pulled back along a morphism factoring through `C^0 = Spec k` vanishes. -/
theorem schemePullbackClass_eq_zero_of_factor {m n : ℕ} (h : power C n ⟶ power C m)
    (h₀ : power C 0 ⟶ power C m) (hh : h = toPowerZero C n ≫ h₀) (A : PowerPic C m) :
    Stacks.Picard.schemePullbackClass h.left A = 0 := by
  rw [hh, Over.comp_left, ← Stacks.Picard.schemePullbackClass_comp,
    Subsingleton.elim (Stacks.Picard.schemePullbackClass h₀.left A) 0]
  exact (Stacks.Picard.schemePullbackClassHom (toPowerZero C n).left).map_zero

/-- Pulling back classes along `h` commutes with finite sums. -/
theorem schemePullbackClass_sum {X Y : Scheme.{u}} (h : X ⟶ Y) {α : Type*} (s : Finset α)
    (f : α → Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass h (∑ i ∈ s, f i) =
      ∑ i ∈ s, Stacks.Picard.schemePullbackClass h (f i) :=
  map_sum (Stacks.Picard.schemePullbackClassHom h) f s

/-- The class `∑ᵢ wᵢ pᵢ^* A` on `C^m`. -/
abbrev linClass (A : PowerPic C 1) (m : ℕ) (w : Fin m → ℤ) : PowerPic C m :=
  ∑ i, w i • Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => i)).left A

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- Restricting `∑ᵢ wᵢ pᵢ^* A` along the insertion of `c₀` in slot `i` drops the weight `wᵢ`. -/
theorem schemePullbackClass_insertPoint_linClass (A : PowerPic C 1) (m : ℕ) (i : Fin (m + 1))
    (w : Fin (m + 1) → ℤ) :
    Stacks.Picard.schemePullbackClass (insertPoint C c₀ m i).left (linClass C A (m + 1) w) =
      linClass C A m (fun s => w (i.succAbove s)) := by
  rw [linClass, schemePullbackClass_sum, Fin.sum_univ_succAbove _ i]
  simp only [schemePullbackClass_zsmul, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left]
  rw [schemePullbackClass_eq_zero_of_factor C _ (lift 1 fun _ => c₀) (by
      refine hom_ext 1 fun t => ?_
      rw [Category.assoc, Category.assoc, reindex_coord, lift_coord, insertPoint_coord_self]
      ), smul_zero,
    zero_add]
  refine sum_congr rfl fun s _ => ?_
  congr 3
  refine hom_ext 1 fun t => ?_
  rw [Category.assoc, reindex_coord, reindex_coord, insertPoint_coord_succAbove]

include c₀ in
/-- **Self-intersection of a class pulled back from the coordinates**:
`((∑ᵢ wᵢ pᵢ^* A)^m · C^m) = m! (deg A)^m ∏ᵢ wᵢ`. -/
theorem powerForm_linClass (A : PowerPic C 1) :
    ∀ (m : ℕ) (w : Fin m → ℤ), powerForm C hC m (fun _ => linClass C A m w) =
      (m.factorial : ℤ) * curveDeg C hC A ^ m * ∏ i, w i
  | 0, w => by rw [powerForm_zero]; simp
  | m + 1, w => by
    have hcons : (fun _ : Fin (m + 1) => linClass C A (m + 1) w) =
        Fin.cons (linClass C A (m + 1) w) (fun _ : Fin m => linClass C A (m + 1) w) := by
      funext q
      refine Fin.cases rfl (fun _ => rfl) q
    rw [hcons, ← slotZero_apply, linClass, map_sum]
    simp_rw [map_zsmul, slotZero_apply, powerForm_cons_coordPullback C hC c₀ m,
      schemePullbackClass_insertPoint_linClass, powerForm_linClass A m, smul_eq_mul]
    rw [Fin.prod_univ_succ, Nat.factorial_succ]
    have : ∀ i : Fin (m + 1), w i * (curveDeg C hC A * ((m.factorial : ℤ) * curveDeg C hC A ^ m *
        ∏ s, w (i.succAbove s))) = (m.factorial : ℤ) * curveDeg C hC A ^ (m + 1) * ∏ t, w t := by
      intro i
      rw [Fin.prod_univ_succAbove w i]
      ring
    rw [sum_congr rfl fun i _ => this i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Fin.prod_univ_succ]
    push_cast
    ring

variable (J : Over (Spec (.of k))) [GrpObj J] [IsCommMonObj J]
  [AlgebraicGeometry.IsAbelianVariety k J]
  (aj : C ⟶ J) (L : SheafOfModules.{u} (structureSheafRing J.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible J.left.presheaf J.left.ringCatIsSheaf L)

/-- The antisymmetrization `P(f) = Q(f) - Q(-f)`, the class of `f^*(L - (-1)^* L)`. -/
abbrev classP {T : Over (Spec (.of k))} (x : Additive (T ⟶ J)) :
    Stacks.SheafOfModules.PicardGroup T.left.presheaf T.left.ringCatIsSheaf :=
  classQ J L hL x - classQ J L hL (-x)

omit [IsAlgClosed k] in
/-- **`P` is additive**: `P(x + y) = P(x) + P(y)`. -/
theorem classP_add {T : Over (Spec (.of k))} (x y : Additive (T ⟶ J)) :
    classP J L hL (x + y) = classP J L hL x + classP J L hL y := by
  have hQ := classQ_cube J L hL (T := T)
  have hB := Stacks.QuadraticMap.cubeBilin_zsmul hQ (-1) (-1) x y
  simp only [neg_smul, one_smul, neg_mul_neg, mul_one] at hB
  simp only [Stacks.QuadraticMap.cubeBilin] at hB
  simp only [classP, neg_add]
  rw [sub_eq_iff_eq_add.1 (sub_eq_iff_eq_add.1 hB.symm)]
  abel

/-- `P` as a homomorphism. -/
def classPHom (T : Over (Spec (.of k))) :
    Additive (T ⟶ J) →+ Stacks.SheafOfModules.PicardGroup T.left.presheaf T.left.ringCatIsSheaf :=
  AddMonoidHom.mk' (classP J L hL) (classP_add J L hL)

omit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k J] in
/-- Pulling back `P(x)` along `h` gives `P(x ∘ h)`. -/
theorem schemePullbackClass_classP {X Y : Over (Spec (.of k))} (h : X ⟶ Y) (x : Additive (Y ⟶ J)) :
    Stacks.Picard.schemePullbackClass h.left (classP J L hL x) =
      classP J L hL (precompHom J h x) := by
  rw [classP, schemePullbackClass_sub, schemePullbackClass_classQ, schemePullbackClass_classQ,
    map_neg]

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- `P(σ_w) = ∑ᵢ wᵢ pᵢ^* P(aj)` on `C^m`. -/
theorem classP_sumMap (m : ℕ) (w : Fin m → ℤ) :
    classP J L hL (Additive.ofMul (sumMap C J aj m w)) =
      linClass C (classP J L hL (Additive.ofMul (coord C 1 0 ≫ aj))) m w := by
  rw [ofMul_sumMap]
  change classPHom J L hL _ (∑ i, _) = _
  rw [map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  change classP J L hL _ = _
  rw [schemePullbackClass_classP, precompHom_apply, toMul_ofMul, reindex_coord_assoc]

include hC c₀ in
/-- **`deg aj^* L = deg (-aj)^* L`**: the class `P(aj)` has degree zero. -/
theorem curveDeg_classP_eq_zero :
    curveDeg C hC (classP J L hL (Additive.ofMul (coord C 1 0 ≫ aj))) = 0 := by
  set g := Stacks.Groupoids.abelianVarietyDimension J
  set σ := sumMap C J aj (g + 1) (fun _ => 1)
  set a := curveDeg C hC (classP J L hL (Additive.ofMul (coord C 1 0 ≫ aj)))
  have h1 := powerForm_linClass C hC c₀ (classP J L hL (Additive.ofMul (coord C 1 0 ≫ aj))) (g + 1)
    (fun _ => 1)
  rw [← classP_sumMap, prod_const_one, mul_one] at h1
  have h2 : classP J L hL (Additive.ofMul σ) =
      Stacks.Picard.schemePullbackClass σ.left (classP J L hL (Additive.ofMul (𝟙 J))) := by
    rw [schemePullbackClass_classP, precompHom_apply, toMul_ofMul, Category.comp_id]
  rw [h2, powerForm, picardIntersection_apply,
    ← intersectionNumber_eq_of_forall_iso k _ _ (g + 1) _
      (fun _ => (Scheme.Modules.pullback σ.left).obj
        (picardRep (classP J L hL (Additive.ofMul (𝟙 J))))) _
      (fun _ => nonempty_pullback_picardRep_iso σ.left _)] at h1
  have : IsIntegral (power C (g + 1)).left := (isVariety_power C (g + 1)).toIsIntegral
  have hlt : topologicalKrullDim (𝟙 (power C (g + 1)).left ≫ σ.left).image <
      ((g + 1 : ℕ) : WithBot ℕ∞) := by
    refine lt_of_le_of_lt (b := (g : WithBot ℕ∞)) ?_ (by exact_mod_cast Nat.lt_succ_self g)
    rw [← Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J]
    exact (𝟙 _ ≫ σ.left).imageι.isClosedEmbedding.isInducing.topologicalKrullDim_le
  rw [intersectionNumber_pullback_eq_zero k _ J.hom σ.left (Over.w σ) (𝟙 _) (g + 1) _ _ hlt] at h1
  have hfac : ((g + 1).factorial : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  exact pow_eq_zero_iff (Nat.succ_ne_zero g) |>.1 ((mul_eq_zero.1 h1.symm).resolve_left hfac)

/-- The class `Y(f) = B(α ∘ f, f)` of a morphism into `J`. -/
abbrev classYα (α : J ⟶ J) (T : Over (Spec (.of k))) (x : Additive (T ⟶ J)) :
    Stacks.SheafOfModules.PicardGroup T.left.presheaf T.left.ringCatIsSheaf :=
  Stacks.QuadraticMap.cubeBilin (classQ J L hL) (Additive.ofMul (Additive.toMul x ≫ α)) x

omit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k J] in
/-- Pulling back `Y(x)` along `h` gives `Y(x ∘ h)`. -/
theorem classYα_nat (α : J ⟶ J) (T T' : Over (Spec (.of k))) (h : T' ⟶ T) (x : Additive (T ⟶ J)) :
    Stacks.Picard.schemePullbackClass h.left (classYα J L hL α T x) =
      classYα J L hL α T' (precompHom J h x) := by
  rw [classYα, schemePullbackClass_cubeBilin_classQ]
  simp only [precompHom_apply, toMul_ofMul]
  rfl

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The degree on `C^1` is `ℤ`-linear. -/
theorem curveDeg_zsmul (v : ℤ) (A : PowerPic C 1) : curveDeg C hC (v • A) = v * curveDeg C hC A :=
  (curveDegHom C hC).map_zsmul v A

omit [IsAlgClosed k] in
/-- `Y(v x) = v² Y(x)` for a homomorphism `α`. -/
theorem classYα_zsmul (α : J ⟶ J) [IsMonHom α] {T : Over (Spec (.of k))} (v : ℤ)
    (x : Additive (T ⟶ J)) : classYα J L hL α T (v • x) = (v * v) • classYα J L hL α T x := by
  have hQ := classQ_cube J L hL (T := T)
  rw [classYα, classYα, ← Stacks.QuadraticMap.cubeBilin_zsmul hQ]
  congr 1
  change Additive.ofMul ((Additive.toMul x ^ v) ≫ α) = _
  rw [GrpObj.zpow_comp (Additive.toMul x) v α]
  rfl

omit [IsAlgClosed k] in
/-- `2 X(v x) = 2 v² X(x)`. -/
theorem classX_zsmul_two {T : Over (Spec (.of k))} (v : ℤ) (x : Additive (T ⟶ J)) :
    (2 : ℤ) • classX J L hL (v • x) = (2 * v ^ 2) • classX J L hL x := by
  have hQ := classQ_cube J L hL (T := T)
  have h1 := Stacks.QuadraticMap.two_smul_map_zsmul_of_cube hQ v x
  have h2 := Stacks.QuadraticMap.two_smul_map_zsmul_of_cube hQ (-v) x
  rw [neg_smul] at h2
  rw [classX, smul_add, h1, h2, classX, smul_add]
  module

omit [IsAlgClosed k] in
/-- The intersection form on classes is symmetric. -/
theorem picardIntersection_comp_perm {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (x : Fin d → Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf)
    (σ : Equiv.Perm (Fin d)) :
    picardIntersection k f i d hd (fun j => x (σ j)) = picardIntersection k f i d hd x := by
  rw [picardIntersection_apply, picardIntersection_apply]
  exact intersectionNumber_comp_perm k f i d hd (fun q => picardRep (x q)) σ

omit [IsAlgClosed k] in
/-- The intersection form is unchanged by transporting the number of slots along `d = d'`. -/
theorem picardIntersection_cast {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] {d d' : ℕ} (e : d = d') (hd : topologicalKrullDim Z ≤ d)
    (hd' : topologicalKrullDim Z ≤ d')
    (x : Fin d → Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) :
    picardIntersection k f i d hd x =
      picardIntersection k f i d' hd' (fun q => x (Fin.cast e.symm q)) := by
  subst e
  rfl

/-- Replacing the last entry of the constant tuple `(x, …, x)` by `y` gives `(x, …, x, y)`. -/
theorem update_const_eq_seqClass {G : Type*} (x y : G) :
    ∀ n : ℕ, Function.update (fun _ : Fin (n + 1) => x) (Fin.last n) y = seqClass x y n
  | 0 => by funext q; rw [Fin.fin_one_eq_zero q]; rfl
  | n + 1 => by
    funext q
    refine Fin.cases ?_ (fun t => ?_) q
    · rw [Function.update_of_ne (by simp [Fin.ext_iff])]
      rfl
    · change _ = seqClass x y n t
      rw [← update_const_eq_seqClass x y n, ← Fin.succ_last]
      by_cases h : t = Fin.last n
      · subst h; simp
      · rw [Function.update_of_ne (fun h' => h (Fin.succ_injective _ h')),
          Function.update_of_ne h]

section Closed

variable (Y : ∀ T : Over (Spec (.of k)), Additive (T ⟶ J) →
    Stacks.SheafOfModules.PicardGroup T.left.presheaf T.left.ringCatIsSheaf)
  (hYnat : ∀ (T T' : Over (Spec (.of k))) (h : T' ⟶ T) (x : Additive (T ⟶ J)),
    Stacks.Picard.schemePullbackClass h.left (Y T x) = Y T' (precompHom J h x))

include hYnat in
/-- **The closed form in any slot**, on `C^n`, `n ≥ 1`, with all weights one. -/
theorem powerForm_update_sumMap (haj : c₀ ≫ aj = 1) (c S b : ℤ)
    (hE : Stacks.QuadraticMap.cubeBilin (classQ J L hL) (Additive.ofMul (coord C 2 0 ≫ aj))
      (Additive.ofMul (coord C 2 1 ≫ aj)) = graphCorrespondence C c₀ c)
    (hS : ∀ v : ℤ, curveDeg C hC (classX J L hL (v • Additive.ofMul (coord C 1 0 ≫ aj))) =
      S * v ^ 2)
    (hb : ∀ v : ℤ, curveDeg C hC (Y (power C 1) (v • Additive.ofMul (coord C 1 0 ≫ aj))) =
      b * v ^ 2)
    (n : ℕ) (hn : 0 < n) (i : Fin n) :
    powerForm C hC n
        (Function.update (fun _ => classX J L hL (Additive.ofMul (sumMap C J aj n 1))) i
          (Y (power C n) (Additive.ofMul (sumMap C J aj n 1)))) =
      (n.factorial : ℤ) * b * ∏ j ∈ range (n - 1), (S - 2 * (j + 1) * c) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  rw [← picardIntersection_comp_perm _ _ (m + 1) _ _ (Equiv.swap i (Fin.last m))]
  have hfun : (fun j => Function.update (fun _ => classX J L hL (Additive.ofMul
      (sumMap C J aj (m + 1) 1))) i (Y (power C (m + 1)) (Additive.ofMul (sumMap C J aj (m + 1) 1)))
        (Equiv.swap i (Fin.last m) j)) = sumMapTuple C J aj L hL Y m 1 := by
    have := Function.update_comp_equiv (fun _ : Fin (m + 1) => classX J L hL (Additive.ofMul
      (sumMap C J aj (m + 1) 1))) (Equiv.swap i (Fin.last m)) i
      (Y (power C (m + 1)) (Additive.ofMul (sumMap C J aj (m + 1) 1)))
    rw [Equiv.symm_swap, Equiv.swap_apply_left] at this
    exact this.trans (update_const_eq_seqClass _ _ m)
  have h := powerForm_sumMapTuple_eq C hC c₀ J aj L hL Y hYnat haj c S b hE hS hb m 1
  have h1 : ∏ t : Fin (m + 1), (1 : Fin (m + 1) → ℤ) t ^ 2 = 1 := by simp
  rw [h1, mul_one] at h
  change powerForm C hC (m + 1) _ = _
  rw [hfun, h, Nat.add_sub_cancel]

end Closed

/-- **The trace of an endomorphism of `J` as a degree on the curve.** Let `aj : C ⟶ J` vanish at
`c₀`, and let `L` on `J` satisfy `B(aj ∘ p₀, aj ∘ p₁) = {c₀} × C + C × {c₀} - Δ` on `C × C` and
`deg aj^* L = dim J ≥ 1`. Then for every homomorphism `α : J ⟶ J`,
`Tr(α) = deg aj^* B(α, 1) = deg B(α ∘ aj, aj)`. -/
theorem abelianVarietyTrace_eq_curveDeg (haj : c₀ ≫ aj = 1)
    (hg : 0 < Stacks.Groupoids.abelianVarietyDimension J)
    (hE : Stacks.QuadraticMap.cubeBilin (classQ J L hL) (Additive.ofMul (coord C 2 0 ≫ aj))
      (Additive.ofMul (coord C 2 1 ≫ aj)) = graphCorrespondence C c₀ 1)
    (hq : curveDeg C hC (classQ J L hL (Additive.ofMul (coord C 1 0 ≫ aj))) =
      Stacks.Groupoids.abelianVarietyDimension J)
    (α : J ⟶ J) [IsMonHom α] :
    Stacks.Groupoids.abelianVarietyTrace J α =
      curveDeg C hC (classYα J L hL α (power C 1) (Additive.ofMul (coord C 1 0 ≫ aj))) := by
  set g := Stacks.Groupoids.abelianVarietyDimension J
  set x1 := Additive.ofMul (coord C 1 0 ≫ aj)
  set b := curveDeg C hC (classYα J L hL α (power C 1) x1)
  have hP := curveDeg_classP_eq_zero C hC c₀ J aj L hL
  have hS0 : curveDeg C hC (classX J L hL x1) = 2 * g := by
    have e1 := (curveDegHom C hC).map_add (classQ J L hL x1) (classQ J L hL (-x1))
    have e2 := (curveDegHom C hC).map_sub (classQ J L hL x1) (classQ J L hL (-x1))
    change curveDeg C hC (classX J L hL x1) =
      curveDeg C hC (classQ J L hL x1) + curveDeg C hC (classQ J L hL (-x1)) at e1
    change curveDeg C hC (classP J L hL x1) =
      curveDeg C hC (classQ J L hL x1) - curveDeg C hC (classQ J L hL (-x1)) at e2
    rw [e1]
    rw [e2] at hP
    linarith
  have hS : ∀ v : ℤ, curveDeg C hC (classX J L hL (v • x1)) = (2 * g) * v ^ 2 := by
    intro v
    have h := congrArg (curveDeg C hC) (classX_zsmul_two J L hL v x1)
    rw [curveDeg_zsmul, curveDeg_zsmul, hS0] at h
    linarith
  have hb : ∀ v : ℤ, curveDeg C hC (classYα J L hL α (power C 1) (v • x1)) = b * v ^ 2 := by
    intro v
    rw [classYα_zsmul, curveDeg_zsmul]
    ring
  have hXnat : ∀ (T T' : Over (Spec (.of k))) (h : T' ⟶ T) (x : Additive (T ⟶ J)),
      Stacks.Picard.schemePullbackClass h.left (classX J L hL x) =
        classX J L hL (precompHom J h x) := fun T T' h x => schemePullbackClass_classX J L hL h x
  set σ := sumMap C J aj g 1
  have : IsIntegral (power C g).left := (isVariety_power C g).toIsIntegral
  have : IsIntegral J.left := inferInstance
  obtain ⟨δ, hδ⟩ := exists_intersectionNumber_pullback_eq_mul k (power C g).hom J.hom σ.left
    (Over.w σ) g (topologicalKrullDim_power hC g)
    (Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J)
  have hδ' : ∀ x : Fin g → Stacks.SheafOfModules.PicardGroup J.left.presheaf J.left.ringCatIsSheaf,
      powerForm C hC g (fun q => Stacks.Picard.schemePullbackClass σ.left (x q)) =
        δ * picardIntersection k J.hom (𝟙 J.left) g
          (Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J).le x := by
    intro x
    rw [powerForm, picardIntersection_apply, picardIntersection_apply,
      ← intersectionNumber_eq_of_forall_iso k _ _ g _
        (fun q => (Scheme.Modules.pullback σ.left).obj (picardRep (x q))) _
        (fun q => nonempty_pullback_picardRep_iso σ.left (x q))]
    exact hδ _
  have hσW : Stacks.Picard.schemePullbackClass σ.left (classX J L hL (Additive.ofMul (𝟙 J))) =
      classX J L hL (Additive.ofMul σ) := by
    rw [schemePullbackClass_classX, precompHom_apply, toMul_ofMul, Category.comp_id]
  have hσB : Stacks.Picard.schemePullbackClass σ.left
      (Stacks.QuadraticMap.cubeBilin (classQ J L hL) (Additive.ofMul α) (Additive.ofMul (𝟙 J))) =
        classYα J L hL α (power C g) (Additive.ofMul σ) := by
    have := classYα_nat J L hL α J (power C g) σ (Additive.ofMul (𝟙 J))
    rw [precompHom_apply, toMul_ofMul, Category.comp_id] at this
    rw [← this, classYα, toMul_ofMul, Category.id_comp]
  have hX := powerForm_update_sumMap C hC c₀ J aj L hL (fun T x => classX J L hL x) hXnat haj 1
    (2 * g) (2 * g) hE hS hS g hg
  have hY := powerForm_update_sumMap C hC c₀ J aj L hL (classYα J L hL α) (classYα_nat J L hL α)
    haj 1 (2 * g) b hE hS hb g hg
  have hA := Stacks.Groupoids.abelianVarietyTrace_mul_eq_two_mul_sum J L hL α hg
  simp only at hA
  have hA' : (Stacks.Groupoids.abelianVarietyTrace J α : ℚ) *
      ((powerForm C hC g (fun _ => classX J L hL (Additive.ofMul σ)) : ℤ) : ℚ) =
      2 * ∑ i : Fin g, ((powerForm C hC g (Function.update
        (fun _ => classX J L hL (Additive.ofMul σ)) i
          (classYα J L hL α (power C g) (Additive.ofMul σ))) : ℤ) : ℚ) := by
    have e1 : powerForm C hC g (fun _ => classX J L hL (Additive.ofMul σ)) =
        δ * picardIntersection k J.hom (𝟙 J.left) g
          (Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J).le
          (fun _ => classX J L hL (Additive.ofMul (𝟙 J))) := by
      rw [← hδ']
      simp only [hσW]
    have e2 : ∀ i : Fin g, powerForm C hC g (Function.update
        (fun _ => classX J L hL (Additive.ofMul σ)) i
          (classYα J L hL α (power C g) (Additive.ofMul σ))) =
        δ * picardIntersection k J.hom (𝟙 J.left) g
          (Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J).le
          (Function.update (fun _ => classX J L hL (Additive.ofMul (𝟙 J))) i
            (Stacks.QuadraticMap.cubeBilin (classQ J L hL) (Additive.ofMul α)
              (Additive.ofMul (𝟙 J)))) := by
      intro i
      rw [← hδ']
      congr 1
      funext q
      rw [Function.apply_update (fun _ => Stacks.Picard.schemePullbackClass σ.left), hσW, hσB]
    rw [e1, sum_congr rfl fun i _ => congrArg (fun z : ℤ => (z : ℚ)) (e2 i)]
    push_cast
    rw [mul_left_comm, hA, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  have hX0 := hX ⟨0, hg⟩
  rw [Function.update_eq_self] at hX0
  rw [hX0, sum_congr rfl fun i _ => congrArg (fun z : ℤ => (z : ℚ)) (hY i), sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hA'
  have hpos : (0 : ℤ) < ∏ j ∈ range (g - 1), (2 * (g : ℤ) - 2 * (j + 1) * 1) := by
    refine prod_pos fun j hj => ?_
    rw [mem_range] at hj
    lia
  have hfac : (0 : ℚ) < (g.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos g
  have hgq : (0 : ℚ) < g := by exact_mod_cast hg
  have hposq : (0 : ℚ) < ∏ j ∈ range (g - 1), (2 * (g : ℚ) - 2 * (j + 1) * 1) := by
    exact_mod_cast hpos
  push_cast at hA'
  have hne :
      (g.factorial : ℚ) * (2 * g) * ∏ j ∈ range (g - 1), (2 * (g : ℚ) - 2 * (j + 1) * 1) ≠ 0 :=
    (mul_pos (mul_pos hfac (by linarith)) hposq).ne'
  apply mul_right_cancel₀ hne
  linear_combination hA'

end Trace

end Stacks.CurvePower

