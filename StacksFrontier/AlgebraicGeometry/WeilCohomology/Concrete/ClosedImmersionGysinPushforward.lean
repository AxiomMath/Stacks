module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalPushforwardRational

/-!
# Pushforward along a closed immersion of classes pulled back by the Gysin map

Let `j : Z ⟶ X` be a closed immersion of nonempty equidimensional smooth projective schemes over
`k`, of dimensions `e` and `d`, and `c = d - e`. For `b ∈ CH^p(X)` the projection formula
(Stacks 0FFA) gives `j_*(j^!b) = b · [Z]` in `CH^*(X) ⊗ 𝐐`. Hence, for data (D0)–(D3)
satisfying (A)(b), (C)(a) and (C)(c), if `j_*1 = γ([Z])` then

  `γ(j_*(j^!b)) = γ(b) ∪ γ([Z]) = γ(b) ∪ j_*1 = j_*(j^*γ(b)) = j_*γ(j^!b)`

by the projection formula of Stacks 0FHB. This is the step of the proof of Stacks 0FIP that
uses the hypothesis `i_*(1) = γ([Z])`.

## Main results

All names below are in the namespace `Stacks.WeilCohomology`.

* `codimensionToRationalChow_equidimensionalPushforward_codimensionGysin`: `j_*(j^!b) = b · j_*[Z]`
  in `CH_*(X) ⊗ 𝐐`, for any morphism `j`.
* `WeilData.cycleClass_pushforward_codimensionGysin_of_closedImmersion`:
  `γ(j_*(j^!b)) = j_*γ(j^!b)` granted `j_*1 = γ([Z])`.
* `WeilData.cycleClass_pushforward_of_closedImmersion_of_retraction`: the same for every class,
  when `j` has a retraction.
* `exists_zsmul_eq_codimensionGysin_of_lciGysinRational`: a class pulled back rationally by `j^!`
  has a nonzero multiple pulled back integrally.
* `WeilData.cycleClass_pushforward_of_closedImmersion_of_lciGysinRational`: `γ(j_*α) = j_*γ(α)` for
  every `α` rationally in the image of `j^!`.
* `WeilData.cycleClass_pushforward_comp`: commutation of `γ` with pushforward is stable under
  composition.
* `FirstChernClassData.IsCohomologicalChernCharacter.toWeilData_cycleClass_congr`: for the data of
  (A1)–(A6), `γ(a)` depends only on the class of `a` in `CH_*(X) ⊗ 𝐐`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- A smooth projective scheme over `k` has finite dimension. -/
theorem topologicalKrullDim_ne_top (X : (SmoothProjectiveScheme k).FullSubcategory) :
    topologicalKrullDim X.obj.left ≠ ⊤ := by
  have := isNoetherian_of_compactSpace (C := fieldChowSituation k) X.obj.hom
  obtain ⟨lo, hi, hb⟩ := exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom
  refine ne_top_of_le_ne_top ?_ (topologicalKrullDim_le_of_relativeDimension_bounds
    (C := fieldChowSituation k) (sX := X.obj.hom) lo hi hb)
  exact ne_of_lt (lt_of_lt_of_le (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)) le_top)

/-- **The projection formula for `j_*j^!`.** For a morphism `j : Z ⟶ X` of smooth projective
schemes over `k`, equidimensional of dimensions `e` and `d`, `c = d - e` and `b ∈ CH^p(X)`, the
classes of `j_*(j^!b) ∈ CH^{p+c}(X)` and of `b · j_*[Z] ∈ CH^{p+c}(X)` in `CH_*(X) ⊗ 𝐐` agree:
by Stacks 0FFA, `j_*([Z] · j^!b) = j_*[Z] · b`, and the product is commutative with unit `[Z]`. -/
theorem codimensionToRationalChow_equidimensionalPushforward_codimensionGysin
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (j : Z ⟶ X) {e d : ℕ}
    (hZ : RelativeDimension Z.obj.hom e)
    (hX : RelativeDimension X.obj.hom d) (p c : ℤ) (hc : c = 0 + d - e)
    (b : codimensionChowGroup k X.obj.hom p) :
    codimensionToRationalChow k X.obj.hom (p + c)
        (equidimensionalPushforward j e d p (p + c) (by omega)
          (codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p b)) =
      codimensionToRationalChow k X.obj.hom (p + c)
        (codimensionIntersectionProduct k X.obj.hom p c b
          (equidimensionalPushforward j e d 0 c hc (fundamentalClass Z))) := by
  have := isNoetherian_of_compactSpace (C := fieldChowSituation k) Z.obj.hom
  have := isNoetherian_of_compactSpace (C := fieldChowSituation k) X.obj.hom
  rw [codimensionToRationalChow_equidimensionalPushforward j hZ hX,
    codimensionToRationalChow_codimensionGysin,
    ← rationalIntersectionProduct_codimensionToRationalChow,
    codimensionToRationalChow_equidimensionalPushforward j hZ hX,
    rationalIntersectionProduct_comm]
  have h1 : codimensionToRationalChow k Z.obj.hom 0 (fundamentalClass Z) =
      rationalFundamentalClass (fieldChowSituation k) Z.obj.hom :=
    codimensionToRationalChow_fundamentalClass (k := k) Z.obj.hom
  rw [h1]
  conv_lhs => rw [← rationalFundamentalClass_rationalIntersectionProduct
    (isRegular_of_smooth_over_field Z.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k Z.obj.hom)
    (lciGysinRational _ _ _ _ _ _ _)]
  exact rationalProperChowPushforward_rationalIntersectionProduct_lciGysinRational (Over.w j.hom)
    _ _ (topologicalKrullDim_ne_top Z) (topologicalKrullDim_ne_top X) _ _ _

/-- **A class rationally pulled back by the Gysin map is integrally so, up to a multiple.** For a
morphism `j : Z ⟶ X` of smooth projective schemes over `k` and `α ∈ CH^p(Z)` whose class in
`CH_*(Z) ⊗ 𝐐` is the rational Gysin pullback `j^!w` of some `w ∈ CH_*(X) ⊗ 𝐐`, there are an
integer `N ≠ 0` and `b ∈ CH^p(X)` with `N α = j^!b` in `CH^p(Z)`. Indeed, through
`CH_*(-) ⊗ 𝐐 = (⨁_i CH^i(-)) ⊗ 𝐐`, `1 ⊗ α` is the image of the codimension-`p` component of `w`,
which is `(1/c) ⊗ b`; and an element `a` with `1 ⊗ a = 0` is torsion. -/
theorem exists_zsmul_eq_codimensionGysin_of_lciGysinRational
    {Z X : (SmoothProjectiveScheme k).FullSubcategory}
    (j : Z ⟶ X) (p : ℤ) (α : codimensionChowGroup k Z.obj.hom p)
    (w : DirectSum ℤ fun i : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) X.obj.hom i)
    (hw : codimensionToRationalChow k Z.obj.hom p α =
      lciGysinRational (fieldChowSituation k) Z.obj.hom X.obj.hom (Over.w j.hom)
        (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth j.hom.left X.obj.hom Z.obj.hom
          (Over.w j.hom))
        (GysinMapExists.of_smooth_source j.hom.left X.obj.hom Z.obj.hom (Over.w j.hom)) w) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ b : codimensionChowGroup k X.obj.hom p,
      N • α = codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p b := by
  set eX := codimensionRationalChowEquiv k X.obj.hom
  set eZ := codimensionRationalChowEquiv k Z.obj.hom
  set G : DirectSum ℤ (codimensionChowGroup k X.obj.hom) →+
      DirectSum ℤ (codimensionChowGroup k Z.obj.hom) :=
    DirectSum.map fun i => codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) i
  have key : ∀ t, lciGysinRational (fieldChowSituation k) Z.obj.hom X.obj.hom (Over.w j.hom)
        (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth j.hom.left X.obj.hom Z.obj.hom
          (Over.w j.hom))
        (GysinMapExists.of_smooth_source j.hom.left X.obj.hom Z.obj.hom (Over.w j.hom)) (eX t) =
      eZ (G.toIntLinearMap.baseChange ℚ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]
    | tmul q x =>
      induction x using DirectSum.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add x x' hx hx' => simp only [TensorProduct.tmul_add, map_add, hx, hx']
      | of i b =>
        rw [codimensionRationalChowEquiv_tmul_of, map_smul,
          ← codimensionToRationalChow_codimensionGysin, LinearMap.baseChange_tmul,
          AddMonoidHom.coe_toIntLinearMap, DirectSum.map_of, codimensionRationalChowEquiv_tmul_of]
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] DirectSum.of (codimensionChowGroup k Z.obj.hom) p α =
      G.toIntLinearMap.baseChange ℚ (eX.symm w) := by
    apply eZ.injective
    rw [← key, LinearEquiv.apply_symm_apply, codimensionRationalChowEquiv_tmul_of, one_smul, hw]
  set πX := (DirectSum.component ℤ ℤ (codimensionChowGroup k X.obj.hom) p).baseChange ℚ
  set πZ := (DirectSum.component ℤ ℤ (codimensionChowGroup k Z.obj.hom) p).baseChange ℚ
  have hcomm : ∀ t, πZ (G.toIntLinearMap.baseChange ℚ t) =
      (codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p).toIntLinearMap.baseChange ℚ
        (πX t) := by
    intro t
    simp only [πX, πZ, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    congr 2
  have h2 : (1 : ℚ) ⊗ₜ[ℤ] α =
      (codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p).toIntLinearMap.baseChange ℚ
        (πX (eX.symm w)) := by
    rw [← hcomm, ← h1]
    simp only [πZ, LinearMap.baseChange_tmul, ← DirectSum.apply_eq_component,
      DirectSum.of_eq_same]
  obtain ⟨⟨b, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (codimensionChowGroup k X.obj.hom p) 1) (πX (eX.symm w))
  have hc' : (c : ℤ) • πX (eX.symm w) = (1 : ℚ) ⊗ₜ[ℤ] b := hc
  have h3 : (1 : ℚ) ⊗ₜ[ℤ] ((c : ℤ) • α -
      codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p b) = 0 := by
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul, h2, ← map_zsmul, hc',
      LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap, sub_self]
  obtain ⟨m, hm, hm0⟩ := exists_zsmul_eq_zero_of_one_tmul_eq_zero h3
  refine ⟨m * c, mul_ne_zero hm (nonZeroDivisors.coe_ne_zero c), m • b, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul] at hm0
  rw [hm0, map_zsmul]

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- `x ∪ 1 = x`. -/
theorem cupTw_unitTw_zero_right (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (h : i + 0 = i) (s : ℤ)
    (h' : s + 0 = s) (x : W.Tw X i s) :
    W.cupTw X i 0 i h s 0 s h' x (W.unitTw X 0 0 rfl) = x := by
  apply (W.twCoord X _ _).injective
  rw [twCoord_cupTw]
  exact Subtype.ext (by rw [coe_cup, coe_twCoord_unitTw, mul_one])

/-- **Stacks 0FHB, the projection formula, at arbitrary spellings of the indices.** -/
theorem pushforward_cupTw_pullTw_of_eq (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (m s j t j' t' n u n' u' : ℤ)
    (hj : j' + 2 * d = j + 2 * e) (ht : t' + d = t + e) (hn : m + j = n) (hu : s + t = u)
    (hn' : m + j' = n') (hu' : s + t' = u') (b : W.Tw Y m s) (a : W.Tw X j t) :
    W.pushforward hA f hX hY n u n' u' (by omega) (by omega)
        (W.cupTw X m j n hn s t u hu (W.pullTw f m s b) a) =
      W.cupTw Y m j' n' hn' s t' u' hu' b (W.pushforward hA f hX hY j t j' t' hj ht a) := by
  subst hn hu hn' hu'
  exact W.pushforward_cupTw_pullTw hA f hX hY m s j t j' t' hj ht b a

/-- **`γ(j_*(j^!b)) = j_*γ(j^!b)` for a closed immersion `j` with `j_*1 = γ([Z])`.** Let the data
(D0)–(D3) satisfy (A)(b), (C)(a) and (C)(c), and let `j : Z ⟶ X` be a closed immersion of
nonempty equidimensional smooth projective schemes over `k`, of dimensions `e` and `d`, with
`j_*1 = γ([Z])` in `H^{2c}(X)(c)`, `c = d - e`. If the cycle class of a class of `CH^*(X)` depends
only on its image in `CH_*(X) ⊗ 𝐐` (`hrat`), then `γ(j_*(j^!b)) = j_*γ(j^!b)` for every
`b ∈ CH^p(X)`. -/
theorem cycleClass_pushforward_codimensionGysin_of_closedImmersion (hA : W.PerfectPairing)
    (hCa : W.CycleClassPullback) (hCc : W.CycleClassMul)
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hrat : ∀ (n : ℤ) (a a' : codimensionChowGroup k X.obj.hom n),
      codimensionToRationalChow k X.obj.hom n a = codimensionToRationalChow k X.obj.hom n a' →
        W.cycleClass X n a = W.cycleClass X n a')
    {Z : (SmoothProjectiveScheme k).FullSubcategory} (j : Z ⟶ X) [IsClosedImmersion j.hom.left]
    {e d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d) (c : ℤ)
    (hc : c = d - e)
    (hj : W.pushforward hA j hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
      W.cycleClass X c (closedSubschemeClass X.obj.hom j.hom.left c))
    (p : ℤ) (b : codimensionChowGroup k X.obj.hom p) :
    W.cycleClass X (p + c) (equidimensionalPushforward j e d p (p + c) (by omega)
        (codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p b)) =
      W.pushforward hA j hZ hX (2 * p) p (2 * (p + c)) (p + c) (by omega) (by omega)
        (W.cycleClass Z p (codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p b)) := by
  rw [hrat _ _ _ (codimensionToRationalChow_equidimensionalPushforward_codimensionGysin j
      hZ.relativeDimension hX.relativeDimension p c (by omega) b),
    equidimensionalPushforward_fundamentalClass j hZ hX c (by omega), hCc, ← hj, hCa,
    ← W.cupTw_unitTw_zero_right Z (2 * p) (by ring) p (by ring)
      (W.pullTw j (2 * p) p (W.cycleClass X p b))]
  exact (W.pushforward_cupTw_pullTw_of_eq hA j hZ hX (2 * p) p 0 0 (2 * c) c (2 * p) p
    (2 * (p + c)) (p + c) (by omega) (by omega) (by ring) (by ring) (by ring) rfl _ _).symm

/-- **`γ` commutes with pushforward along a closed immersion with a retraction.** Under the
hypotheses of `cycleClass_pushforward_codimensionGysin_of_closedImmersion`, if moreover `j` has a
retraction `r : X ⟶ Z`, `j ≫ r = 𝟙`, then `γ(j_*α) = j_*γ(α)` for every `α ∈ CH^p(Z)`: indeed
`α = j^!(r^!α)` (Stacks 0FF5). This applies to the graph `X ⟶ X × Y` of a morphism. -/
theorem cycleClass_pushforward_of_closedImmersion_of_retraction (hA : W.PerfectPairing)
    (hCa : W.CycleClassPullback) (hCc : W.CycleClassMul)
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hrat : ∀ (n : ℤ) (a a' : codimensionChowGroup k X.obj.hom n),
      codimensionToRationalChow k X.obj.hom n a = codimensionToRationalChow k X.obj.hom n a' →
        W.cycleClass X n a = W.cycleClass X n a')
    {Z : (SmoothProjectiveScheme k).FullSubcategory} (j : Z ⟶ X) [IsClosedImmersion j.hom.left]
    (r : X ⟶ Z)
    (hr : j ≫ r = 𝟙 Z) {e d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d) (c : ℤ)
    (hc : c = d - e)
    (hj : W.pushforward hA j hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
      W.cycleClass X c (closedSubschemeClass X.obj.hom j.hom.left c))
    (p : ℤ) (α : codimensionChowGroup k Z.obj.hom p) :
    W.cycleClass X (p + c) (equidimensionalPushforward j e d p (p + c) (by omega) α) =
      W.pushforward hA j hZ hX (2 * p) p (2 * (p + c)) (p + c) (by omega) (by omega)
        (W.cycleClass Z p α) := by
  have hid : ∀ (g : Z.obj.left ⟶ Z.obj.left) [LocallyOfFiniteType g]
      (hg : g ≫ Z.obj.hom = Z.obj.hom), g = 𝟙 _ →
      codimensionGysin Z.obj.hom Z.obj.hom (f := g) hg p α = α := by
    rintro g _ hg rfl
    exact codimensionGysin_id _ p α
  have h1 : j.hom.left ≫ r.hom.left = 𝟙 Z.obj.left :=
    congrArg (fun φ : Z ⟶ Z => φ.hom.left) hr
  have hα : α = codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p
      (codimensionGysin X.obj.hom Z.obj.hom (Over.w r.hom) p α) := by
    rw [← codimensionGysin_comp (sX := Z.obj.hom) (sY := X.obj.hom) (sZ := Z.obj.hom)
      (hf := Over.w j.hom) (hg := Over.w r.hom) p α]
    exact (hid _ _ h1).symm
  rw [hα]
  exact W.cycleClass_pushforward_codimensionGysin_of_closedImmersion hA hCa hCc hrat j hZ hX c hc
    hj p _

/-- **`γ(j_*α) = j_*γ(α)` for a class rationally pulled back by the Gysin map.** Under the
hypotheses of `cycleClass_pushforward_codimensionGysin_of_closedImmersion`, with `F` of
characteristic zero, the commutation holds for every `α ∈ CH^p(Z)` whose class in
`CH_*(Z) ⊗ 𝐐` is `j^!w` for some `w ∈ CH_*(X) ⊗ 𝐐`: then `Nα = j^!b` for some integer `N ≠ 0`
(`exists_zsmul_eq_codimensionGysin_of_lciGysinRational`), and one divides by `N` in `F`. -/
theorem cycleClass_pushforward_of_closedImmersion_of_lciGysinRational [CharZero F]
    (hA : W.PerfectPairing) (hCa : W.CycleClassPullback) (hCc : W.CycleClassMul)
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hrat : ∀ (n : ℤ) (a a' : codimensionChowGroup k X.obj.hom n),
      codimensionToRationalChow k X.obj.hom n a = codimensionToRationalChow k X.obj.hom n a' →
        W.cycleClass X n a = W.cycleClass X n a')
    {Z : (SmoothProjectiveScheme k).FullSubcategory} (j : Z ⟶ X) [IsClosedImmersion j.hom.left]
    {e d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d) (c : ℤ)
    (hc : c = d - e)
    (hj : W.pushforward hA j hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
      W.cycleClass X c (closedSubschemeClass X.obj.hom j.hom.left c))
    (p : ℤ) (α : codimensionChowGroup k Z.obj.hom p)
    (w : DirectSum ℤ fun i : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) X.obj.hom i)
    (hw : codimensionToRationalChow k Z.obj.hom p α =
      lciGysinRational (fieldChowSituation k) Z.obj.hom X.obj.hom (Over.w j.hom)
        (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth j.hom.left X.obj.hom Z.obj.hom
          (Over.w j.hom))
        (GysinMapExists.of_smooth_source j.hom.left X.obj.hom Z.obj.hom (Over.w j.hom)) w) :
    W.cycleClass X (p + c) (equidimensionalPushforward j e d p (p + c) (by omega) α) =
      W.pushforward hA j hZ hX (2 * p) p (2 * (p + c)) (p + c) (by omega) (by omega)
        (W.cycleClass Z p α) := by
  obtain ⟨N, hN, b, hb⟩ := exists_zsmul_eq_codimensionGysin_of_lciGysinRational j p α w hw
  have h := W.cycleClass_pushforward_codimensionGysin_of_closedImmersion hA hCa hCc hrat j hZ hX
    c hc hj p b
  rw [← hb, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul F,
    ← Int.cast_smul_eq_zsmul F] at h
  exact smul_right_injective _ (Int.cast_ne_zero.2 hN) h

/-- **Commutation of `γ` with pushforward is stable under composition.** For morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z` of nonempty equidimensional smooth projective schemes over `k`, if
`γ(f_*α) = f_*γ(α)` and `γ(g_*(f_*α)) = g_*γ(f_*α)`, then `γ((g ∘ f)_*α) = (g ∘ f)_*γ(α)`, by
Stacks 02R5 and Stacks 0FHB, provided the cycle class map on `Z` depends only on classes in
`CH_*(Z) ⊗ 𝐐` (`hrat`). -/
theorem cycleClass_pushforward_comp (hA : W.PerfectPairing)
    {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) {d e c : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (hZ : IsNonemptyEquidimensional Z c)
    (hrat : ∀ (n : ℤ) (a a' : codimensionChowGroup k Z.obj.hom n),
      codimensionToRationalChow k Z.obj.hom n a = codimensionToRationalChow k Z.obj.hom n a' →
        W.cycleClass Z n a = W.cycleClass Z n a')
    (p q r : ℤ) (hq : q = p + e - d) (hr : r = q + c - e) (α : codimensionChowGroup k X.obj.hom p)
    (hf : W.cycleClass Y q (equidimensionalPushforward f d e p q hq α) =
      W.pushforward hA f hX hY (2 * p) p (2 * q) q (by omega) (by omega) (W.cycleClass X p α))
    (hg : W.cycleClass Z r (equidimensionalPushforward g e c q r hr
        (equidimensionalPushforward f d e p q hq α)) =
      W.pushforward hA g hY hZ (2 * q) q (2 * r) r (by omega) (by omega)
        (W.cycleClass Y q (equidimensionalPushforward f d e p q hq α))) :
    W.cycleClass Z r (equidimensionalPushforward (f ≫ g) d c p r (by omega) α) =
      W.pushforward hA (f ≫ g) hX hZ (2 * p) p (2 * r) r (by omega) (by omega)
        (W.cycleClass X p α) := by
  rw [← hrat _ _ _ (codimensionToRationalChow_equidimensionalPushforward_comp f g
    hX.relativeDimension hY.relativeDimension hZ.relativeDimension p q r hq hr α), hg, hf,
    W.pushforward_comp hA f g hX hY hZ]

end WeilData

namespace FirstChernClassData.IsCohomologicalChernCharacter

variable {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom)
  (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass)

/-- **`γ` of `toWeilData` in coordinates**: the coordinate in `H^*(X)` of `γ(a) ∈ H^{2n}(X)(n)`
is the coordinate of the cycle class `γ(a) ∈ H^*(X)(n)` of Tag 0FIF. -/
theorem coe_twCoord_toWeilData_cycleClass (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
    (a : codimensionChowGroup k X.obj.hom n) :
    ((h.toWeilData hA1 hA3 hA5 hA6).twCoord X (2 * (n : ℤ)) n
        ((h.toWeilData hA1 hA3 hA5 hA6).cycleClass X n a) : (h.toWeilData hA1 hA3 hA5 hA6).H X) =
      𝔇.κ X n (h.codimensionCycleClass X n a) := by
  have h1 : (h.toWeilData hA1 hA3 hA5 hA6).cycleClass X n a = h.cycleClassGrade hA1 hA3 X n a :=
    rfl
  have h2 : h.cycleClassGrade hA1 hA3 X n a = (tateTwistCoordinates 𝔇.coord (n : ℤ)).symm
      ⟨𝔇.κ X n (h.codimensionCycleClass X n a), h.κ_codimensionCycleClass_mem hA1 hA3 X n a⟩ :=
    rfl
  rw [h1, h2]
  exact congrArg Subtype.val ((tateTwistCoordinates 𝔇.coord (n : ℤ)).apply_symm_apply _)

/-- **`γ` of `toWeilData` depends only on the rational class**: classes of `CH^n(X)` with the
same image in `CH_*(X) ⊗ 𝐐` have the same cycle class, `γ` being defined on `CH^*(X) ⊗ 𝐐`. -/
theorem toWeilData_cycleClass_congr (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a a' : codimensionChowGroup k X.obj.hom n)
    (haa' : codimensionToRationalChow k X.obj.hom n a =
      codimensionToRationalChow k X.obj.hom n a') :
    (h.toWeilData hA1 hA3 hA5 hA6).cycleClass X n a =
      (h.toWeilData hA1 hA3 hA5 hA6).cycleClass X n a' := by
  rcases lt_or_ge n 0 with hn | hn
  · have := subsingleton_codimensionChowGroup_of_neg k X.obj.hom hn
    rw [Subsingleton.elim a a']
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  apply ((h.toWeilData hA1 hA3 hA5 hA6).twCoord X _ _).injective
  apply Subtype.ext
  rw [h.coe_twCoord_toWeilData_cycleClass hA1 hA3 hA5 hA6,
    h.coe_twCoord_toWeilData_cycleClass hA1 hA3 hA5 hA6, codimensionCycleClass_apply,
    codimensionCycleClass_apply, haa']

end FirstChernClassData.IsCohomologicalChernCharacter

end Stacks.WeilCohomology

end
