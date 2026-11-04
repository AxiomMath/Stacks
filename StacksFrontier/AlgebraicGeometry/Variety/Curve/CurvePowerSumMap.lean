/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerRestriction
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullback
public import StacksFrontier.Algebra.QuadraticMap.CubeRelation

/-!
# Intersection numbers on `C^m` of classes pulled back from a group along sums of coordinates

Let `C` be a smooth proper curve over an algebraically closed field `k` with a rational point
`c₀`, let `J` be an abelian variety over `k` and `aj : C ⟶ J` a morphism with `aj(c₀) = 0`.
For integer weights `w : Fin m → 𝐙` let `σ_w = ∑ᵢ wᵢ · (aj ∘ pᵢ) : C^m ⟶ J`. For an invertible
module `N` on `J` write `Q(f) = [f^* N]`; by the theorem of the cube `Q` is quadratic, with
biadditive form `B`.

Suppose that on `C^2` the class `B(aj ∘ p₀, aj ∘ p₁)` is `c · ({c₀} × C + C × {c₀} - Δ)`, and that
`deg Q(w · aj) = s w²` on `C`. Then `X_w = Q(σ_w)` is, up to classes of degree zero on the
coordinate curves, `∑ᵢ (s wᵢ² + c wᵢ ∑_{l ≠ i} w_l) Fᵢ - c ∑_{j < l} w_j w_l Δ_{jl}`, and the fibre
and diagonal rules `Stacks.CurvePower.powerForm_cons_coordPullback` and
`Stacks.CurvePower.powerForm_cons_diagonal` compute, for every family of classes `Z(f)` natural in
`f` with `deg Z(w · aj) = b w²` on `C`,

`(X_w^m · Z(σ_w) · C^(m+1)) = (m+1)! · b · ∏_{i=1}^{m} (s - i c) · ∏ₜ wₜ²`

(`Stacks.CurvePower.powerForm_sumMapTuple_eq`): restricting `X_w` to a fibre `Fᵢ` drops the
weight `wᵢ`, restricting it to a diagonal `Δ_{jl}` merges `w_j` and `w_l`, and the closed form
satisfies the resulting recursion (`Stacks.CurvePower.powerForm_sumMapTuple_succ`) by the
polynomial identity `Stacks.CurvePower.sum_restriction_weights`.

## Main results

* `Stacks.CurvePower.classX_sumMap_eq`: the expansion of `X(σ_w)` on `C^m`.
* `Stacks.CurvePower.powerForm_sumMapTuple_eq`: the closed form of `(X(σ_w)^m · Y(σ_w))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open AlgebraicGeometry Finset
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.CurvePower

/-! ### The polynomial identity -/

section Algebra

/-- Exchanging the order of summation over ordered pairs `j ≠ l`. -/
theorem sum_erase_comm {N : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin N → Fin N → M) :
    ∑ j, ∑ l ∈ univ.erase j, f j l = ∑ l, ∑ j ∈ univ.erase l, f j l := by
  refine Finset.sum_comm' fun j l => ?_
  simp only [mem_univ, mem_erase, ne_eq, true_and, and_true]
  exact ⟨Ne.symm, Ne.symm⟩

/-- **The polynomial identity behind the closed form.** With `Π = ∏ₜ wₜ²`, `Πᵢ = ∏_{t ≠ i} wₜ²`
and `Π_{jl} = ∏_{t ≠ j, l} wₜ²`,
`∑ᵢ (s wᵢ² + 2 c wᵢ ∑_{l ≠ i} w_l) Πᵢ - c ∑_{j ≠ l} w_j w_l (w_j + w_l)² Π_{jl}
  = N (s - 2 (N - 1) c) Π`. -/
theorem sum_restriction_weights (N : ℕ) (w : Fin N → ℤ) (s c : ℤ) :
    (∑ i, (s * w i ^ 2 + 2 * c * w i * ∑ l ∈ univ.erase i, w l) *
        ∏ t ∈ univ.erase i, w t ^ 2) -
      c * ∑ j, ∑ l ∈ univ.erase j, w j * w l * (w j + w l) ^ 2 *
        ∏ t ∈ (univ.erase j).erase l, w t ^ 2 =
      N * (s - 2 * (N - 1) * c) * ∏ t, w t ^ 2 := by
  set P := ∏ t, w t ^ 2
  have h1 : ∀ i, w i ^ 2 * ∏ t ∈ univ.erase i, w t ^ 2 = P := fun i =>
    Finset.mul_prod_erase _ (fun t => w t ^ 2) (mem_univ i)
  have h2 : ∀ j, ∀ l ∈ univ.erase j,
      w l ^ 2 * ∏ t ∈ (univ.erase j).erase l, w t ^ 2 = ∏ t ∈ univ.erase j, w t ^ 2 :=
    fun j l hl => Finset.mul_prod_erase _ (fun t => w t ^ 2) hl
  have h3 : ∀ j l, ∏ t ∈ (univ.erase j).erase l, w t ^ 2 =
      ∏ t ∈ (univ.erase l).erase j, w t ^ 2 := fun j l => by
    rw [Finset.erase_right_comm]
  have hmerge : ∀ j, ∀ l ∈ univ.erase j,
      w j * w l * (w j + w l) ^ 2 * ∏ t ∈ (univ.erase j).erase l, w t ^ 2 =
        w j * w l * ∏ t ∈ univ.erase l, w t ^ 2 + w j * w l * ∏ t ∈ univ.erase j, w t ^ 2 +
          2 * P := by
    intro j l hl
    have hj : j ∈ univ.erase l := by
      rw [mem_erase] at hl ⊢
      exact ⟨Ne.symm hl.1, mem_univ _⟩
    have e1 := h2 j l hl
    have e2 := h2 l j hj
    rw [← h3 j l] at e2
    have e3 : w j ^ 2 * w l ^ 2 * ∏ t ∈ (univ.erase j).erase l, w t ^ 2 = P := by
      rw [mul_assoc, e1, h1]
    rw [← e1, ← e2, ← e3]
    ring
  have hcard : ∀ j : Fin N, ((univ.erase j).card : ℤ) = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
    have : 1 ≤ N := Fin.pos_iff_nonempty.2 ⟨j⟩
    push_cast [this]
    ring
  rw [show (∑ j, ∑ l ∈ univ.erase j, w j * w l * (w j + w l) ^ 2 *
      ∏ t ∈ (univ.erase j).erase l, w t ^ 2) =
      ∑ j, ∑ l ∈ univ.erase j, (w j * w l * ∏ t ∈ univ.erase l, w t ^ 2 +
        w j * w l * ∏ t ∈ univ.erase j, w t ^ 2 + 2 * P) from
    sum_congr rfl fun j _ => sum_congr rfl fun l hl => hmerge j l hl]
  simp only [sum_add_distrib]
  rw [sum_erase_comm (fun j l => w j * w l * ∏ t ∈ univ.erase l, w t ^ 2)]
  set T := ∑ i, ∑ l ∈ univ.erase i, w i * w l * ∏ t ∈ univ.erase i, w t ^ 2
  have hsingle : ∀ i, (s * w i ^ 2 + 2 * c * w i * ∑ l ∈ univ.erase i, w l) *
      ∏ t ∈ univ.erase i, w t ^ 2 =
        s * P + 2 * c * ∑ l ∈ univ.erase i, w i * w l * ∏ t ∈ univ.erase i, w t ^ 2 := by
    intro i
    rw [← h1 i, Finset.mul_sum, Finset.mul_sum, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact sum_congr rfl fun l _ => by ring
  rw [sum_congr rfl fun i _ => hsingle i, sum_add_distrib]
  have hA : ∑ i : Fin N, 2 * c * ∑ l ∈ univ.erase i, w i * w l * ∏ t ∈ univ.erase i, w t ^ 2 =
      2 * c * T := by rw [Finset.mul_sum]
  have hconst : ∑ j : Fin N, ∑ _l ∈ univ.erase j, 2 * P = (N : ℤ) * (N - 1) * 2 * P := by
    rw [sum_congr rfl fun j _ => by rw [sum_const, nsmul_eq_mul, hcard j]]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hswap : ∑ l, ∑ j ∈ univ.erase l, w j * w l * ∏ t ∈ univ.erase l, w t ^ 2 = T :=
    sum_congr rfl fun i _ => sum_congr rfl fun l _ => by ring
  rw [hA, hconst, hswap]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `∏ₛ f(i.succAbove s) = ∏_{t ≠ i} f t`. -/
theorem prod_succAbove_eq_prod_erase {N : ℕ} {M : Type*} [CommMonoid M] (i : Fin (N + 1))
    (f : Fin (N + 1) → M) : ∏ s, f (i.succAbove s) = ∏ t ∈ univ.erase i, f t := by
  classical
  have himg : univ.erase i = Finset.image i.succAbove univ := by
    ext t
    simp only [mem_erase, mem_univ, and_true, mem_image, true_and]
    constructor
    · intro ht
      exact Fin.exists_succAbove_eq ht
    · rintro ⟨s, rfl⟩
      exact Fin.succAbove_ne i s
  rw [himg, Finset.prod_image (fun a _ b _ hab => i.succAbove_right_injective hab)]

/-- `∏ₛ f(σ(s + 2)) = ∏_{t ≠ σ 0, σ 1} f t` for a permutation `σ`. -/
theorem prod_perm_succ_succ_eq_prod_erase {N : ℕ} {M : Type*} [CommMonoid M]
    (σ : Equiv.Perm (Fin (N + 2))) (f : Fin (N + 2) → M) :
    ∏ s : Fin N, f (σ s.succ.succ) = ∏ t ∈ (univ.erase (σ 0)).erase (σ 1), f t := by
  classical
  set g : Fin (N + 2) → M := fun t => if t = σ 0 ∨ t = σ 1 then 1 else f t
  have e0 : g (σ 0) = 1 := if_pos (Or.inl rfl)
  have e1 : g (σ 1) = 1 := if_pos (Or.inr rfl)
  have hg : ∀ s : Fin N, g (σ s.succ.succ) = f (σ s.succ.succ) := by
    intro s
    refine if_neg ?_
    rintro (h | h)
    · exact Fin.succ_ne_zero _ (σ.injective h)
    · have := σ.injective h
      rw [← Fin.succ_zero_eq_one, Fin.succ_inj] at this
      exact Fin.succ_ne_zero _ this
  have hall : ∏ t, g t = ∏ s : Fin N, f (σ s.succ.succ) := by
    rw [← Equiv.prod_comp σ g, Fin.prod_univ_succ, Fin.prod_univ_succ, e0, Fin.succ_zero_eq_one,
      e1, one_mul, one_mul]
    exact prod_congr rfl fun s _ => hg s
  have h01 : σ 1 ≠ σ 0 := fun h => absurd (σ.injective h) (by simp)
  rw [← hall, ← Finset.mul_prod_erase _ g (mem_univ (σ 0)), e0, one_mul,
    ← Finset.mul_prod_erase _ g (mem_erase.2 ⟨h01, mem_univ _⟩), e1, one_mul]
  refine prod_congr rfl fun t ht => ?_
  rw [mem_erase, mem_erase] at ht
  exact if_neg (by rintro (h | h) <;> [exact ht.2.1 h; exact ht.1 h])

end Algebra

/-! ### Pulling back classes from a group along sums of coordinates -/

section Group

/-- Pulling back the class of `ψ^* L` along `φ` gives the class of `(φ ≫ ψ)^* L`. -/
theorem schemePullbackClass_pullbackPicardClass {X Y Z : Scheme.{u}} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatIsSheaf L) :
    Stacks.Picard.schemePullbackClass φ (Stacks.SheafOfModules.pullbackPicardClass ψ L hL) =
      Stacks.SheafOfModules.pullbackPicardClass (φ ≫ ψ) L hL := by
  have := hL
  rw [Stacks.SheafOfModules.pullbackPicardClass_comp φ ψ L hL
    (Stacks.RingedSpace.modulePullback_isInvertible _ L)]
  exact Stacks.Picard.pullbackClass_classOf _ _ _

/-- Pulling back classes along `h` commutes with integer multiples. -/
theorem schemePullbackClass_zsmul {X Y : Scheme.{u}} (h : X ⟶ Y) (n : ℤ)
    (a : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass h (n • a) = n • Stacks.Picard.schemePullbackClass h a :=
  map_zsmul (Stacks.Picard.schemePullbackClassHom h) n a

/-- Pulling back classes along `h` commutes with subtraction. -/
theorem schemePullbackClass_sub {X Y : Scheme.{u}} (h : X ⟶ Y) (a b : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass h (a - b) =
      Stacks.Picard.schemePullbackClass h a - Stacks.Picard.schemePullbackClass h b :=
  map_sub (Stacks.Picard.schemePullbackClassHom h) a b

variable {k : Type u} [Field k] [IsAlgClosed k] (C : Over (Spec (.of k))) [IsVariety k C.hom]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] (hC : topologicalKrullDim C.left = 1)
  (c₀ : power C 0 ⟶ C) (J : Over (Spec (.of k))) [GrpObj J] [IsCommMonObj J] (aj : C ⟶ J)

/-- Precomposition with `h : X ⟶ Y`, as a homomorphism of the groups of morphisms into `J`. -/
def precompHom {X Y : Over (Spec (.of k))} (h : X ⟶ Y) : Additive (Y ⟶ J) →+ Additive (X ⟶ J) where
  toFun x := Additive.ofMul (h ≫ Additive.toMul x)
  map_zero' := by
    change Additive.ofMul (h ≫ (1 : Y ⟶ J)) = Additive.ofMul 1
    rw [MonObj.comp_one]
  map_add' x y := by
    change Additive.ofMul (h ≫ (Additive.toMul x * Additive.toMul y)) = _
    rw [MonObj.comp_mul]
    rfl

omit [IsAlgClosed k] in
/-- `precompHom J h x = h ≫ x`. -/
@[simp] theorem precompHom_apply {X Y : Over (Spec (.of k))} (h : X ⟶ Y) (x : Additive (Y ⟶ J)) :
    precompHom J h x = Additive.ofMul (h ≫ Additive.toMul x) := rfl

/-- **`σ_w = ∑ᵢ wᵢ (aj ∘ pᵢ) : C^m ⟶ J`**, in the group of morphisms into `J`. -/
def sumMap (m : ℕ) (w : Fin m → ℤ) : power C m ⟶ J :=
  Additive.toMul (∑ i, w i • Additive.ofMul (coord C m i ≫ aj))

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- `σ_w` as a sum in `Additive (C^m ⟶ J)`. -/
theorem ofMul_sumMap (m : ℕ) (w : Fin m → ℤ) :
    Additive.ofMul (sumMap C J aj m w) = ∑ i, w i • Additive.ofMul (coord C m i ≫ aj) := rfl

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- `h ≫ σ_w = ∑ᵢ wᵢ (h ≫ pᵢ ≫ aj)` in `Additive (C^n ⟶ J)`. -/
theorem ofMul_comp_sumMap {n m : ℕ} (h : power C n ⟶ power C m) (w : Fin m → ℤ) :
    Additive.ofMul (h ≫ sumMap C J aj m w) =
      ∑ i, w i • Additive.ofMul (h ≫ coord C m i ≫ aj) := by
  have := map_sum (precompHom J h) (fun i => w i • Additive.ofMul (coord C m i ≫ aj)) univ
  simp only [map_zsmul, precompHom_apply, toMul_ofMul] at this
  exact this

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
variable {C c₀ J aj} in
/-- **Inserting the base point drops a weight**: `σ_w ∘ ι_i = σ_{w ∘ succAbove i}` when
`aj(c₀) = 0`. -/
theorem insertPoint_comp_sumMap (haj : c₀ ≫ aj = 1) (m : ℕ) (i : Fin (m + 1))
    (w : Fin (m + 1) → ℤ) :
    insertPoint C c₀ m i ≫ sumMap C J aj (m + 1) w =
      sumMap C J aj m (fun s => w (i.succAbove s)) := by
  apply Additive.ofMul.injective
  rw [ofMul_comp_sumMap, ofMul_sumMap, Fin.sum_univ_succAbove _ i, insertPoint_coord_self_assoc,
    haj, MonObj.comp_one, ofMul_one, smul_zero, zero_add]
  refine sum_congr rfl fun s _ => ?_
  rw [insertPoint_coord_succAbove_assoc]

/-- The merged weights: `(w_{σ 0} + w_{σ 1}, w_{σ 2}, …)`. -/
def mergedWeights {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (w : Fin (n + 2) → ℤ) : Fin (n + 1) → ℤ :=
  Fin.cons (w (σ 0) + w (σ 1)) (fun s => w (σ s.succ.succ))

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- **Merging two coordinates adds their weights.** -/
theorem mergeMap_comp_sumMap (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) (w : Fin (n + 2) → ℤ) :
    mergeMap C n σ ≫ sumMap C J aj (n + 2) w = sumMap C J aj (n + 1) (mergedWeights σ w) := by
  apply Additive.ofMul.injective
  rw [ofMul_comp_sumMap, ofMul_sumMap]
  have hc : ∀ t, mergeMap C n σ ≫ coord C (n + 2) t =
      doubleFirst C n ≫ coord C (n + 2) (σ.symm t) :=
    fun t => by rw [mergeMap, Category.assoc, reindex_coord]
  simp_rw [← Category.assoc, hc, Category.assoc]
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ (f := fun s => mergedWeights σ w s • _)]
  simp only [doubleFirst, lift_coord_assoc, Fin.cons_zero, Fin.cons_succ, mergedWeights]
  rw [Fin.succ_zero_eq_one, add_smul]
  exact (add_assoc _ _ _).symm

/-- The class `Q(f) = [f^* N]` of a morphism into `J`, on the group of morphisms. -/
abbrev classQ (N : SheafOfModules.{u} (structureSheafRing J.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible J.left.presheaf J.left.ringCatIsSheaf N)
    {T : Over (Spec (.of k))} (x : Additive (T ⟶ J)) :
    Stacks.SheafOfModules.PicardGroup T.left.presheaf T.left.ringCatIsSheaf :=
  Stacks.SheafOfModules.pullbackPicardClass (Additive.toMul x).left N hN

variable (N : SheafOfModules.{u} (structureSheafRing J.left.toRingedSpace))
  (hN : Stacks.SheafOfModules.IsInvertible J.left.presheaf J.left.ringCatIsSheaf N)

omit [IsAlgClosed k] in
/-- Pulling back `Q(x)` along `h` gives `Q(h ≫ x)`. -/
theorem schemePullbackClass_classQ {X Y : Over (Spec (.of k))} (h : X ⟶ Y) (x : Additive (Y ⟶ J)) :
    Stacks.Picard.schemePullbackClass h.left (classQ J N hN x) =
      classQ J N hN (precompHom J h x) := by
  rw [classQ, schemePullbackClass_pullbackPicardClass]
  rfl

omit [IsAlgClosed k] in
/-- Pulling back `B(x, y)` along `h` gives `B(h ≫ x, h ≫ y)`. -/
theorem schemePullbackClass_cubeBilin_classQ {X Y : Over (Spec (.of k))} (h : X ⟶ Y)
    (x y : Additive (Y ⟶ J)) :
    Stacks.Picard.schemePullbackClass h.left
        (Stacks.QuadraticMap.cubeBilin (classQ J N hN) x y) =
      Stacks.QuadraticMap.cubeBilin (classQ J N hN) (precompHom J h x) (precompHom J h y) := by
  simp only [Stacks.QuadraticMap.cubeBilin]
  rw [schemePullbackClass_sub, schemePullbackClass_sub, schemePullbackClass_classQ,
    schemePullbackClass_classQ, schemePullbackClass_classQ, map_add]

variable [AlgebraicGeometry.IsAbelianVariety k J]

omit [IsAlgClosed k] [IsCommMonObj J] in
/-- **The theorem of the cube** for `Q`:
`Q(x + y + z) + Q(x) + Q(y) + Q(z) = Q(x + y) + Q(x + z) + Q(y + z)`. -/
theorem classQ_cube {T : Over (Spec (.of k))} (x y z : Additive (T ⟶ J)) :
    classQ J N hN (x + y + z) + classQ J N hN x + classQ J N hN y + classQ J N hN z =
      classQ J N hN (x + y) + classQ J N hN (x + z) + classQ J N hN (y + z) :=
  Stacks.Groupoids.pullbackPicardClass_cubeRelation J
    (Stacks.Groupoids.hasTheoremOfTheCube k J) N hN
    (Additive.toMul x) (Additive.toMul y) (Additive.toMul z)

/-- The symmetrization `X(f) = Q(f) + Q(-f)`. -/
abbrev classX {T : Over (Spec (.of k))} (x : Additive (T ⟶ J)) :
    Stacks.SheafOfModules.PicardGroup T.left.presheaf T.left.ringCatIsSheaf :=
  classQ J N hN x + classQ J N hN (-x)

omit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k J] in
/-- Pulling back `X(x)` along `h` gives `X(h ≫ x)`. -/
theorem schemePullbackClass_classX {X Y : Over (Spec (.of k))} (h : X ⟶ Y) (x : Additive (Y ⟶ J)) :
    Stacks.Picard.schemePullbackClass h.left (classX J N hN x) =
      classX J N hN (precompHom J h x) := by
  rw [classX, Stacks.Picard.schemePullbackClass_add, schemePullbackClass_classQ,
    schemePullbackClass_classQ, map_neg]

/-- For a symmetric function, the sum over ordered pairs `j ≠ l` is twice the sum over `j < l`. -/
theorem sum_erase_eq_two_mul_sum_lt {N : ℕ} {M : Type*} [AddCommGroup M] (f : Fin N → Fin N → M)
    (hf : ∀ j l, f j l = f l j) :
    ∑ j, ∑ l ∈ univ.erase j, f j l =
      (∑ j, ∑ l, if j < l then f j l else 0) + ∑ j, ∑ l, if j < l then f j l else 0 := by
  have h1 : ∀ j, ∑ l ∈ univ.erase j, f j l =
      (∑ l, if j < l then f j l else 0) + ∑ l, if l < j then f j l else 0 := by
    intro j
    rw [← sum_add_distrib, ← Finset.sum_erase_add _ _ (mem_univ j)]
    simp only [lt_self_iff_false, if_false, add_zero]
    refine sum_congr rfl fun l hl => ?_
    rcases lt_trichotomy j l with h | h | h
    · simp [h, not_lt.2 h.le]
    · exact absurd h.symm (mem_erase.1 hl).1
    · simp [h, not_lt.2 h.le]
  rw [sum_congr rfl fun j _ => h1 j, sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun l _ => by rw [hf]

variable {J N hN} in
/-- The class `c · (F₀ + F₁ - Δ)` on `C^2`, where `F₀` and `F₁` are the pullbacks of the point
`c₀` along the two coordinates and `Δ` is the diagonal. -/
abbrev graphCorrespondence (c : ℤ) : PowerPic C 2 :=
  c • (Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => (0 : Fin 2))).left
      (pointClass C c₀) +
    Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => (1 : Fin 2))).left
      (pointClass C c₀) - diagClass C)

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- **The expansion of `X(σ_w)`** on `C^m` into classes pulled back from `C^1` along the
coordinates and from `C^2` along pairs of coordinates. -/
theorem classX_sumMap_eq (m : ℕ) (w : Fin m → ℤ) :
    classX J N hN (Additive.ofMul (sumMap C J aj m w)) =
      (∑ i, Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => i)).left
          (classX J N hN (w i • Additive.ofMul (coord C 1 0 ≫ aj)))) +
        ∑ j, ∑ l ∈ univ.erase j, (w j * w l) • Stacks.Picard.schemePullbackClass
          (reindex C ![j, l]).left (Stacks.QuadraticMap.cubeBilin (classQ J N hN)
            (Additive.ofMul (coord C 2 0 ≫ aj)) (Additive.ofMul (coord C 2 1 ≫ aj))) := by
  have hQ := classQ_cube J N hN (T := power C m)
  set x : Fin m → Additive (power C m ⟶ J) := fun i => w i • Additive.ofMul (coord C m i ≫ aj)
  have hsum := Stacks.QuadraticMap.map_sum_of_cube hQ x univ
  have hsumn := Stacks.QuadraticMap.map_sum_of_cube hQ (fun i => -x i) univ
  rw [sum_neg_distrib] at hsumn
  have hB : ∀ j l, Stacks.QuadraticMap.cubeBilin (classQ J N hN) (-x j) (-x l) =
      Stacks.QuadraticMap.cubeBilin (classQ J N hN) (x j) (x l) := fun j l => by
    have := Stacks.QuadraticMap.cubeBilin_zsmul hQ (-1) (-1) (x j) (x l)
    simpa using this
  have hBpair : ∀ j l, Stacks.QuadraticMap.cubeBilin (classQ J N hN) (x j) (x l) =
      (w j * w l) • Stacks.Picard.schemePullbackClass (reindex C ![j, l]).left
        (Stacks.QuadraticMap.cubeBilin (classQ J N hN)
          (Additive.ofMul (coord C 2 0 ≫ aj)) (Additive.ofMul (coord C 2 1 ≫ aj))) := by
    intro j l
    rw [Stacks.QuadraticMap.cubeBilin_zsmul hQ, schemePullbackClass_cubeBilin_classQ]
    simp only [precompHom_apply, toMul_ofMul]
    rw [reindex_coord_assoc, reindex_coord_assoc]
    rfl
  have hsingle : ∀ i, classX J N hN (x i) =
      Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => i)).left
        (classX J N hN (w i • Additive.ofMul (coord C 1 0 ≫ aj))) := by
    intro i
    rw [schemePullbackClass_classX, map_zsmul, precompHom_apply, toMul_ofMul, reindex_coord_assoc]
  rw [classX, ofMul_sumMap, hsum, hsumn]
  simp only [hB]
  rw [show (∑ i, classQ J N hN (x i)) + (∑ j, ∑ l, if j < l then
      Stacks.QuadraticMap.cubeBilin (classQ J N hN) (x j) (x l) else 0) +
      ((∑ i, classQ J N hN (-x i)) + ∑ j, ∑ l, if j < l then
      Stacks.QuadraticMap.cubeBilin (classQ J N hN) (x j) (x l) else 0) =
      (∑ i, classX J N hN (x i)) + ((∑ j, ∑ l, if j < l then
      Stacks.QuadraticMap.cubeBilin (classQ J N hN) (x j) (x l) else 0) + ∑ j, ∑ l, if j < l then
      Stacks.QuadraticMap.cubeBilin (classQ J N hN) (x j) (x l) else 0) by
    simp only [classX, sum_add_distrib]; abel]
  rw [← sum_erase_eq_two_mul_sum_lt _ (fun j l => Stacks.QuadraticMap.cubeBilin_comm hQ _ _)]
  congr 1
  · exact sum_congr rfl fun i _ => hsingle i
  · exact sum_congr rfl fun j _ => sum_congr rfl fun l _ => hBpair j l

/-- The tuple `(x, …, x, y)` with `m` copies of `x`. -/
def seqClass {G : Type*} (x y : G) : (m : ℕ) → Fin (m + 1) → G
  | 0 => fun _ => y
  | m + 1 => Fin.cons x (seqClass x y m)

/-- Applying `φ` entrywise to `(x, …, x, y)` gives `(φ x, …, φ x, φ y)`. -/
theorem seqClass_map {G H : Type*} (φ : G → H) (x y : G) :
    (m : ℕ) → (q : Fin (m + 1)) → φ (seqClass x y m q) = seqClass (φ x) (φ y) m q
  | 0, _ => rfl
  | m + 1, q => by
    refine Fin.cases ?_ (fun t => ?_) q
    · rfl
    · exact seqClass_map φ x y m t

/-- A permutation sending `0 ↦ j` and `1 ↦ l`. -/
def pairPerm {n : ℕ} (j l : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (Equiv.swap 1 (Equiv.swap 0 j l)).trans (Equiv.swap 0 j)

/-- `pairPerm j l 0 = j` when `l ≠ j`. -/
theorem pairPerm_zero {n : ℕ} {j l : Fin (n + 2)} (h : l ≠ j) : pairPerm j l 0 = j := by
  have hl : Equiv.swap 0 j l ≠ 0 := by
    intro h0
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h0
    exact h h0
  simp only [pairPerm, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hl), Equiv.swap_apply_left]

/-- `pairPerm j l 1 = l`. -/
theorem pairPerm_one {n : ℕ} (j l : Fin (n + 2)) : pairPerm j l 1 = l := by
  simp only [pairPerm, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- Reindexing along `(pairPerm j l 0, pairPerm j l 1)` is reindexing along `(j, l)`. -/
theorem reindex_pair_pairPerm {n : ℕ} {j l : Fin (n + 2)} (h : l ≠ j) :
    reindex C ![pairPerm j l 0, pairPerm j l 1] = reindex C ![j, l] := by
  rw [pairPerm_zero h, pairPerm_one]

variable (Y : ∀ T : Over (Spec (.of k)), Additive (T ⟶ J) →
    Stacks.SheafOfModules.PicardGroup T.left.presheaf T.left.ringCatIsSheaf)
  (hYnat : ∀ (T T' : Over (Spec (.of k))) (h : T' ⟶ T) (x : Additive (T ⟶ J)),
    Stacks.Picard.schemePullbackClass h.left (Y T x) = Y T' (precompHom J h x))

/-- The tuple `(X(σ_w), …, X(σ_w), Y(σ_w))` on `C^(m+1)`. -/
abbrev sumMapTuple (m : ℕ) (w : Fin (m + 1) → ℤ) : Fin (m + 1) → PowerPic C (m + 1) :=
  seqClass (classX J N hN (Additive.ofMul (sumMap C J aj (m + 1) w)))
    (Y (power C (m + 1)) (Additive.ofMul (sumMap C J aj (m + 1) w))) m

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [AlgebraicGeometry.IsAbelianVariety k J] in
include hYnat in
/-- Pulling the tuple `(X(σ_w), …, X(σ_w), Y(σ_w))` back along `h` with `h ≫ σ_w = σ_{w'}` gives
the tuple `(X(σ_{w'}), …, X(σ_{w'}), Y(σ_{w'}))`. -/
theorem schemePullbackClass_sumMapTuple (m : ℕ) {n : ℕ} (h : power C n ⟶ power C (m + 1))
    (w : Fin (m + 1) → ℤ) (w' : Fin n → ℤ) (hw : h ≫ sumMap C J aj (m + 1) w = sumMap C J aj n w')
    (q : Fin (m + 1)) :
    Stacks.Picard.schemePullbackClass h.left (sumMapTuple C J aj N hN Y m w q) =
      seqClass (classX J N hN (Additive.ofMul (sumMap C J aj n w')))
        (Y (power C n) (Additive.ofMul (sumMap C J aj n w'))) m q := by
  rw [sumMapTuple, seqClass_map (Stacks.Picard.schemePullbackClass h.left),
    schemePullbackClass_classX, hYnat]
  simp only [precompHom_apply, toMul_ofMul, hw]

/-- Slot `0` of a multilinear form on `Fin (m + 1)` as a linear map. -/
abbrev slotZero {m : ℕ} {G : Type*} [AddCommGroup G]
    (F : MultilinearMap ℤ (fun _ : Fin (m + 1) => G) ℤ) (rest : Fin m → G) : G →ₗ[ℤ] ℤ :=
  F.toLinearMap (Fin.cons 0 rest) 0

/-- `slotZero F rest a = F (a, rest)`. -/
theorem slotZero_apply {m : ℕ} {G : Type*} [AddCommGroup G]
    (F : MultilinearMap ℤ (fun _ : Fin (m + 1) => G) ℤ) (rest : Fin m → G) (a : G) :
    slotZero F rest a = F (Fin.cons a rest) := by
  rw [slotZero, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]

include hYnat in
/-- **The recursion.** Expanding the first slot `X(σ_w)` of `(X(σ_w)^(m+1) · Y(σ_w) · C^(m+2))`
and restricting to fibres and diagonals. -/
theorem powerForm_sumMapTuple_succ (haj : c₀ ≫ aj = 1) (c S : ℤ)
    (hE : Stacks.QuadraticMap.cubeBilin (classQ J N hN) (Additive.ofMul (coord C 2 0 ≫ aj))
      (Additive.ofMul (coord C 2 1 ≫ aj)) = graphCorrespondence C c₀ c)
    (hS : ∀ v : ℤ, curveDeg C hC (classX J N hN (v • Additive.ofMul (coord C 1 0 ≫ aj))) =
      S * v ^ 2)
    (m : ℕ) (w : Fin (m + 2) → ℤ) :
    powerForm C hC (m + 2) (sumMapTuple C J aj N hN Y (m + 1) w) =
      (∑ i, (S * w i ^ 2 + 2 * c * w i * ∑ l ∈ univ.erase i, w l) *
          powerForm C hC (m + 1) (sumMapTuple C J aj N hN Y m (fun s => w (i.succAbove s)))) -
        c * ∑ j, ∑ l ∈ univ.erase j, w j * w l *
          powerForm C hC (m + 1)
            (sumMapTuple C J aj N hN Y m (mergedWeights (pairPerm j l) w)) := by
  set F := slotZero (powerForm C hC (m + 2)) (fun q => (sumMapTuple C J aj N hN Y (m + 1) w) q.succ)
  have hF : powerForm C hC (m + 2) (sumMapTuple C J aj N hN Y (m + 1) w) =
      F (classX J N hN (Additive.ofMul (sumMap C J aj (m + 2) w))) := by
    rw [slotZero_apply]
    congr 1
  have hrest : (fun q => (sumMapTuple C J aj N hN Y (m + 1) w) q.succ) =
      seqClass (classX J N hN (Additive.ofMul (sumMap C J aj (m + 2) w)))
        (Y (power C (m + 2)) (Additive.ofMul (sumMap C J aj (m + 2) w))) m := rfl
  have hfib : ∀ (i : Fin (m + 2)) (A : PowerPic C 1),
      F (Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => i)).left A) =
        curveDeg C hC A *
          powerForm C hC (m + 1) (sumMapTuple C J aj N hN Y m (fun s => w (i.succAbove s))) := by
    intro i A
    rw [slotZero_apply, powerForm_cons_coordPullback C hC c₀ (m + 1) i A]
    congr 2
    funext q
    rw [schemePullbackClass_sumMapTuple C J aj N hN Y hYnat (m + 1)
      (insertPoint C c₀ (m + 1) i) w _ (insertPoint_comp_sumMap haj (m + 1) i w) q.succ]
    rfl
  have hdiag : ∀ j, ∀ l ∈ univ.erase j,
      F (Stacks.Picard.schemePullbackClass (reindex C ![j, l]).left (diagClass C)) =
        powerForm C hC (m + 1) (sumMapTuple C J aj N hN Y m (mergedWeights (pairPerm j l) w)) := by
    intro j l hl
    have hlj : l ≠ j := (mem_erase.1 hl).1
    rw [slotZero_apply, ← reindex_pair_pairPerm C hlj,
      powerForm_cons_diagonal C hC m (pairPerm j l)]
    congr 1
    funext q
    rw [schemePullbackClass_sumMapTuple C J aj N hN Y hYnat (m + 1) (mergeMap C m (pairPerm j l))
      w _ (mergeMap_comp_sumMap C J aj m (pairPerm j l) w) q.succ]
    rfl
  have hpair : ∀ j l : Fin (m + 2), Stacks.Picard.schemePullbackClass (reindex C ![j, l]).left
      (graphCorrespondence C c₀ c) =
        c • (Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => j)).left
            (pointClass C c₀) +
          Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => l)).left
            (pointClass C c₀) -
          Stacks.Picard.schemePullbackClass (reindex C ![j, l]).left (diagClass C)) := by
    intro j l
    rw [graphCorrespondence, schemePullbackClass_zsmul, schemePullbackClass_sub,
      Stacks.Picard.schemePullbackClass_add, Stacks.Picard.schemePullbackClass_comp,
      Stacks.Picard.schemePullbackClass_comp,
      ← Over.comp_left, ← Over.comp_left, reindex_comp, reindex_comp]
    rfl
  rw [hF, classX_sumMap_eq, map_add, map_sum, map_sum]
  simp_rw [map_sum, map_zsmul, hE, hpair, map_zsmul, map_sub, map_add, hfib, curveDeg_pointClass,
    one_mul, smul_eq_mul, hS]
  rw [show (∑ j, ∑ l ∈ univ.erase j, w j * w l * (c * (powerForm C hC (m + 1)
      (sumMapTuple C J aj N hN Y m (fun s => w (j.succAbove s))) + powerForm C hC (m + 1)
      (sumMapTuple C J aj N hN Y m (fun s => w (l.succAbove s))) -
      F (Stacks.Picard.schemePullbackClass (reindex C ![j, l]).left (diagClass C))))) =
      (∑ j, ∑ l ∈ univ.erase j, w j * w l * c * powerForm C hC (m + 1)
        (sumMapTuple C J aj N hN Y m (fun s => w (j.succAbove s)))) +
      (∑ j, ∑ l ∈ univ.erase j, w j * w l * c * powerForm C hC (m + 1)
        (sumMapTuple C J aj N hN Y m (fun s => w (l.succAbove s)))) -
      c * ∑ j, ∑ l ∈ univ.erase j, w j * w l * powerForm C hC (m + 1)
        (sumMapTuple C J aj N hN Y m (mergedWeights (pairPerm j l) w)) by
    rw [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun l hl => ?_
    rw [hdiag j l hl]
    ring]
  rw [sum_erase_comm (fun j l => w j * w l * c * powerForm C hC (m + 1)
    (sumMapTuple C J aj N hN Y m (fun s => w (l.succAbove s))))]
  have key : ∀ P : Fin (m + 2) → ℤ, (∑ i, (S * w i ^ 2 + 2 * c * w i * ∑ l ∈ univ.erase i, w l) *
      P i) = (∑ i, S * w i ^ 2 * P i) + (∑ i, ∑ l ∈ univ.erase i, w i * w l * c * P i) +
        ∑ i, ∑ l ∈ univ.erase i, w l * w i * c * P i := by
    intro P
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [add_assoc, ← sum_add_distrib, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact sum_congr rfl fun l _ => by ring
  rw [key fun i =>
    powerForm C hC (m + 1) (sumMapTuple C J aj N hN Y m (fun s => w (i.succAbove s)))]
  ring

/-- `∏ₜ (merged weights)ₜ² = (w_j + w_l)² ∏_{t ≠ j, l} wₜ²`. -/
theorem prod_mergedWeights_sq {n : ℕ} {j l : Fin (n + 2)} (hlj : l ≠ j) (w : Fin (n + 2) → ℤ) :
    ∏ t, mergedWeights (pairPerm j l) w t ^ 2 =
      (w j + w l) ^ 2 * ∏ t ∈ (univ.erase j).erase l, w t ^ 2 := by
  rw [Fin.prod_univ_succ]
  simp only [mergedWeights, Fin.cons_zero, Fin.cons_succ]
  rw [prod_perm_succ_succ_eq_prod_erase (pairPerm j l) (fun t => w t ^ 2), pairPerm_zero hlj,
    pairPerm_one]

include hYnat in
/-- **The closed form.** If `B(aj ∘ p₀, aj ∘ p₁) = c (F₀ + F₁ - Δ)` on `C^2`,
`deg X(v · aj) = S v²` and `deg Y(v · aj) = b v²` on `C^1`, then on `C^(m+1)`
`(X(σ_w)^m · Y(σ_w)) = (m+1)! · b · ∏_{i < m} (S - 2(i+1) c) · ∏ₜ wₜ²`. -/
theorem powerForm_sumMapTuple_eq (haj : c₀ ≫ aj = 1) (c S b : ℤ)
    (hE : Stacks.QuadraticMap.cubeBilin (classQ J N hN) (Additive.ofMul (coord C 2 0 ≫ aj))
      (Additive.ofMul (coord C 2 1 ≫ aj)) = graphCorrespondence C c₀ c)
    (hS : ∀ v : ℤ, curveDeg C hC (classX J N hN (v • Additive.ofMul (coord C 1 0 ≫ aj))) =
      S * v ^ 2)
    (hb : ∀ v : ℤ, curveDeg C hC (Y (power C 1) (v • Additive.ofMul (coord C 1 0 ≫ aj))) =
      b * v ^ 2) :
    ∀ (m : ℕ) (w : Fin (m + 1) → ℤ),
      powerForm C hC (m + 1) (sumMapTuple C J aj N hN Y m w) =
        ((m + 1).factorial : ℤ) * b * (∏ i ∈ range m, (S - 2 * (i + 1) * c)) * ∏ t, w t ^ 2
  | 0, w => by
    have hw : Additive.ofMul (sumMap C J aj 1 w) = w 0 • Additive.ofMul (coord C 1 0 ≫ aj) := by
      rw [ofMul_sumMap, Fin.sum_univ_one]
    show curveDeg C hC (Y (power C 1) (Additive.ofMul (sumMap C J aj 1 w))) = _
    rw [hw, hb, Fin.prod_univ_one]
    simp
  | m + 1, w => by
    rw [powerForm_sumMapTuple_succ C hC c₀ J aj N hN Y hYnat haj c S hE hS m w]
    simp_rw [powerForm_sumMapTuple_eq haj c S b hE hS hb m,
      prod_succAbove_eq_prod_erase _ (fun t => w t ^ 2)]
    rw [show (∑ j, ∑ l ∈ univ.erase j, w j * w l * (((m + 1).factorial : ℤ) * b *
        (∏ i ∈ range m, (S - 2 * (i + 1) * c)) *
          ∏ t, mergedWeights (pairPerm j l) w t ^ 2)) =
        ((m + 1).factorial : ℤ) * b * (∏ i ∈ range m, (S - 2 * (i + 1) * c)) *
          ∑ j, ∑ l ∈ univ.erase j, w j * w l * (w j + w l) ^ 2 *
            ∏ t ∈ (univ.erase j).erase l, w t ^ 2 by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun l hl => ?_
      rw [prod_mergedWeights_sq (mem_erase.1 hl).1]
      ring]
    rw [show (∑ i, (S * w i ^ 2 + 2 * c * w i * ∑ l ∈ univ.erase i, w l) *
        (((m + 1).factorial : ℤ) * b * (∏ i ∈ range m, (S - 2 * (i + 1) * c)) *
          ∏ t ∈ univ.erase i, w t ^ 2)) =
        ((m + 1).factorial : ℤ) * b * (∏ i ∈ range m, (S - 2 * (i + 1) * c)) *
          ∑ i, (S * w i ^ 2 + 2 * c * w i * ∑ l ∈ univ.erase i, w l) *
            ∏ t ∈ univ.erase i, w t ^ 2 by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun i _ => by ring]
    rw [mul_left_comm c, ← mul_sub, sum_restriction_weights (m + 2) w S c,
      Finset.prod_range_succ, Nat.factorial_succ (m + 1)]
    push_cast
    ring

end Group

end Stacks.CurvePower
