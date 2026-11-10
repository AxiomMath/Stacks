module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalProductClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExteriorProductGysin
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Lemma 0FIL: axiom (B) for data satisfying (A1)–(A7)

Let (D0), (D1), (D2') satisfy axioms (A1)–(A7) of Section 45.14, with `γ` the cycle class map of
Tag 0FIF and `∫_X = λ_X` the trace map of axiom (A6) (`WeilChernData.toWeilData`). Lemma 0FIL
says that axiom (B) of Section 0FHA holds.

The proof is the source's. (B)(a) is (A5). For (B)(b), let `X` and `Y` be nonempty and
equidimensional of dimensions `d` and `e`. The diagonal of `X × Y` is the intersection product of
the pullbacks of `Δ_X` and `Δ_Y` by the projections `p : (X × Y)² ⟶ X × X` and
`q : (X × Y)² ⟶ Y × Y` (`SmoothProjectiveScheme.diagonalClass_prod`), so, `γ` being compatible
with pullbacks and intersection products, `γ([Δ_{X × Y}]) = p^*γ([Δ_X]) ∪ q^*γ([Δ_Y])`
(`untwistClass_diagonalClass_prod`). Writing `γ([Δ_X]) = ∑ e_t ⊗ f_t` and
`γ([Δ_Y]) = ∑ e'_s ⊗ f'_s` by (A5), this is `∑ ± (e_t ⊗ e'_s) ⊗ (f_t ⊗ f'_s)`, and the linear map
`μ = λ_X ⊗ λ_Y` on `H^{2d+2e}(X × Y)(d + e)` (`productTrace`) contracts it to
`(∑ λ_X(f_t) e_t) ⊗ (∑ λ_Y(f'_s) e'_s) = 1 ⊗ 1 = 1` (`traceContract_productTrace`): `μ`
satisfies the condition of (A6) for `X × Y`. By the uniqueness of the trace map (Remark 0FIK)
`λ_{X × Y} = μ`, which is (B)(b) (`kunnethTrace_toWeilData`).

In namespace `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`:

## Main definitions

* `productTrace`: `λ_X ⊗ λ_Y : H^{2(d+e)}(X × Y)(d + e) ⟶ F` through (A5).

## Main results

* `untwistClass_diagonalClass_prod`: `γ([Δ_{X × Y}]) = p^*γ([Δ_X]) ∪ q^*γ([Δ_Y])`.
* `traceContract_productTrace`: `λ_X ⊗ λ_Y` satisfies the condition of (A6) for `X × Y`.
* `kunneth_toWeilData`: Lemma 0FIL; `Stacks.WeilCohomology.WeilChernData.kunneth_toWeilData`, its
  form for the bundled data.

## References

* [Stacks Project, Tag 0FIL](https://stacks.math.columbia.edu/tag/0FIL)
* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct DirectSum Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-! ### The product of two trace maps -/

section ProductTrace

variable (hA5 : 𝔇.KunnethAxiom) (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d e : ℕ)
  (lamX : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
  (lamY : tateTwist F 𝔇.tate (𝔇.grade Y (2 * (e : ℤ))) e →ₗ[F] F)

/-- The linear form `λ_X ⊗ λ_Y` on `H^*(X × Y) = H^*(X) ⊗ H^*(Y)` (by (A5)), in the coordinates of
the twists: `pr₁^*a ∪ pr₂^*b ↦ λ_X(a) λ_Y(b)`. -/
def kunnethTraceForm : 𝔇.H (prod X Y) →ₗ[F] F :=
  TensorProduct.lift ((LinearMap.mul F F).compl₁₂ (𝔇.untwistTrace X d lamX)
    (𝔇.untwistTrace Y e lamY)) ∘ₗ (𝔇.kunnethEquiv hA5 X Y).symm.toLinearMap

/-- `kunnethTraceForm` takes `pr₁^*a ∪ pr₂^*b` to `λ_X(a) λ_Y(b)`. -/
theorem kunnethTraceForm_kunnethMap (a : 𝔇.H X) (b : 𝔇.H Y) :
    𝔇.kunnethTraceForm hA5 X Y d e lamX lamY (𝔇.kunnethMap X Y (a ⊗ₜ b)) =
      𝔇.untwistTrace X d lamX a * 𝔇.untwistTrace Y e lamY b := by
  have h : 𝔇.kunnethMap X Y (a ⊗ₜ b) = 𝔇.kunnethEquiv hA5 X Y (a ⊗ₜ b) := rfl
  rw [kunnethTraceForm, LinearMap.comp_apply, LinearEquiv.coe_coe, h,
    LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul]
  rfl

/-- **The trace map `λ_X ⊗ λ_Y : H^{2(d+e)}(X × Y)(d + e) ⟶ F`** of the product, through the
Künneth isomorphism of (A5): `pr₁^*a ∪ pr₂^*b ↦ λ_X(a) λ_Y(b)`, the trace maps vanishing outside
their degree. -/
def productTrace :
    tateTwist F 𝔇.tate (𝔇.grade (prod X Y) (2 * ((d + e : ℕ) : ℤ))) (d + e : ℕ) →ₗ[F] F :=
  𝔇.kunnethTraceForm hA5 X Y d e lamX lamY ∘ₗ (𝔇.grade (prod X Y) _).subtype ∘ₗ
    (tateTwistCoordinates 𝔇.coord ((d + e : ℕ) : ℤ)).toLinearMap

/-- `λ_X ⊗ λ_Y` on a twisted class is `kunnethTraceForm` applied to its coordinates. -/
theorem productTrace_apply (z : tateTwist F 𝔇.tate (𝔇.grade (prod X Y) (2 * ((d + e : ℕ) : ℤ)))
    (d + e : ℕ)) :
    𝔇.productTrace hA5 X Y d e lamX lamY z =
      𝔇.kunnethTraceForm hA5 X Y d e lamX lamY
        (tateTwistCoordinates (V := 𝔇.grade (prod X Y) (2 * ((d + e : ℕ) : ℤ))) 𝔇.coord
          ((d + e : ℕ) : ℤ) z : 𝔇.H (prod X Y)) :=
  rfl

/-- A trace map on a class `x` of degree `2d` is `λ` of its preimage under the coordinates. -/
private theorem untwistTrace_of_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) (x : 𝔇.H X)
    (hx : x ∈ 𝔇.grade X (2 * (d : ℤ))) :
    𝔇.untwistTrace X d lam x = lam ((tateTwistCoordinates 𝔇.coord (d : ℤ)).symm ⟨x, hx⟩) := by
  have hp : 𝔇.projGrade X (2 * (d : ℤ)) x = ⟨x, hx⟩ :=
    Subtype.ext (by rw [coe_projGrade, decompose_of_mem_same _ hx])
  rw [untwistTrace, LinearMap.comp_apply, LinearMap.comp_apply, hp, LinearEquiv.coe_coe]

/-- `λ_X ⊗ λ_Y` read on `H^*(X × Y)`: on `pr₁^*a ∪ pr₂^*b` for homogeneous `a` and `b` it is
`λ_X(a) λ_Y(b)`. -/
theorem untwistTrace_productTrace_kunnethMap {i j : ℤ} {a : 𝔇.H X} {b : 𝔇.H Y}
    (ha : a ∈ 𝔇.grade X i) (hb : b ∈ 𝔇.grade Y j) :
    𝔇.untwistTrace (prod X Y) (d + e) (𝔇.productTrace hA5 X Y d e lamX lamY)
        (𝔇.kunnethMap X Y (a ⊗ₜ b)) =
      𝔇.untwistTrace X d lamX a * 𝔇.untwistTrace Y e lamY b := by
  have hmem : 𝔇.kunnethMap X Y (a ⊗ₜ b) ∈ 𝔇.grade (prod X Y) (i + j) :=
    SetLike.GradedMul.mul_mem (𝔇.pull_grade _ _ _ ha) (𝔇.pull_grade _ _ _ hb)
  by_cases hij : i + j = 2 * ((d + e : ℕ) : ℤ)
  · rw [untwistTrace_of_mem _ _ _ _ _ (hij ▸ hmem), productTrace_apply,
      LinearEquiv.apply_symm_apply]
    exact 𝔇.kunnethTraceForm_kunnethMap hA5 X Y d e lamX lamY a b
  · rw [𝔇.untwistTrace_eq_zero _ _ _ _ hij _ hmem]
    by_cases hi : i = 2 * (d : ℤ)
    · rw [𝔇.untwistTrace_eq_zero Y e lamY j (by push_cast at hij; omega) b hb, mul_zero]
    · rw [𝔇.untwistTrace_eq_zero X d lamX i hi a ha, zero_mul]

/-- Pullback along `pr₁ × pr₁ : (X × Y)² ⟶ X × X` of `pr₁^*a` is `pr₁^*pr₁^*a`. -/
theorem pull_prodMap_fst_fst (a : 𝔇.H X) :
    𝔇.pull (prodMap (fst X Y) (fst X Y)) (𝔇.pull (fst X X) a) =
      𝔇.pull (fst (prod X Y) (prod X Y)) (𝔇.pull (fst X Y) a) := by
  rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, prodMap_fst, 𝔇.pull_comp, AlgHom.comp_apply]

/-- Pullback along `pr₁ × pr₁ : (X × Y)² ⟶ X × X` of `pr₂^*a` is `pr₂^*pr₁^*a`. -/
theorem pull_prodMap_fst_snd (a : 𝔇.H X) :
    𝔇.pull (prodMap (fst X Y) (fst X Y)) (𝔇.pull (snd X X) a) =
      𝔇.pull (snd (prod X Y) (prod X Y)) (𝔇.pull (fst X Y) a) := by
  rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, prodMap_snd, 𝔇.pull_comp, AlgHom.comp_apply]

/-- Pullback along `pr₂ × pr₂ : (X × Y)² ⟶ Y × Y` of `pr₁^*b` is `pr₁^*pr₂^*b`. -/
theorem pull_prodMap_snd_fst (b : 𝔇.H Y) :
    𝔇.pull (prodMap (snd X Y) (snd X Y)) (𝔇.pull (fst Y Y) b) =
      𝔇.pull (fst (prod X Y) (prod X Y)) (𝔇.pull (snd X Y) b) := by
  rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, prodMap_fst, 𝔇.pull_comp, AlgHom.comp_apply]

/-- Pullback along `pr₂ × pr₂ : (X × Y)² ⟶ Y × Y` of `pr₂^*b` is `pr₂^*pr₂^*b`. -/
theorem pull_prodMap_snd_snd (b : 𝔇.H Y) :
    𝔇.pull (prodMap (snd X Y) (snd X Y)) (𝔇.pull (snd Y Y) b) =
      𝔇.pull (snd (prod X Y) (prod X Y)) (𝔇.pull (snd X Y) b) := by
  rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, prodMap_snd, 𝔇.pull_comp, AlgHom.comp_apply]

/-- **The product of the pullbacks of two Künneth classes**: for homogeneous `a, b ∈ H^*(X)` and
`a', b' ∈ H^*(Y)`, with `b` of degree `j` and `a'` of degree `i'`,
`p^*(a ⊗ b) ∪ q^*(a' ⊗ b') = (-1)^{j i'} (a ⊗ a') ⊗ (b ⊗ b')` in
`H^*((X × Y)²) = H^*(X × Y) ⊗ H^*(X × Y)`. -/
theorem pull_kunnethMap_mul_pull_kunnethMap {j i' : ℤ} (a b : 𝔇.H X) (a' b' : 𝔇.H Y)
    (hb : b ∈ 𝔇.grade X j) (ha' : a' ∈ 𝔇.grade Y i') :
    𝔇.pull (prodMap (fst X Y) (fst X Y)) (𝔇.kunnethMap X X (a ⊗ₜ b)) *
        𝔇.pull (prodMap (snd X Y) (snd X Y)) (𝔇.kunnethMap Y Y (a' ⊗ₜ b')) =
      (Int.negOnePow (j * i') : ℤ) • 𝔇.kunnethMap (prod X Y) (prod X Y)
        (𝔇.kunnethMap X Y (a ⊗ₜ a') ⊗ₜ 𝔇.kunnethMap X Y (b ⊗ₜ b')) := by
  set P := prod (prod X Y) (prod X Y)
  have hcomm := 𝔇.graded_comm P j i' (𝔇.pull (snd (prod X Y) (prod X Y)) (𝔇.pull (fst X Y) b))
    (𝔇.pull (fst (prod X Y) (prod X Y)) (𝔇.pull (snd X Y) a'))
    (𝔇.pull_grade _ _ _ (𝔇.pull_grade _ _ _ hb)) (𝔇.pull_grade _ _ _ (𝔇.pull_grade _ _ _ ha'))
  simp only [kunnethMap_tmul, map_mul, pull_prodMap_fst_fst, pull_prodMap_fst_snd,
    pull_prodMap_snd_fst, pull_prodMap_snd_snd]
  rw [show ∀ x y z t : 𝔇.H P, x * y * (z * t) = x * (y * z) * t from
      fun x y z t ↦ by simp only [mul_assoc], hcomm, mul_smul_comm, smul_mul_assoc,
    show ∀ x y z t : 𝔇.H P, x * (y * z) * t = x * y * (z * t) from
      fun x y z t ↦ by simp only [mul_assoc]]

/-- The contraction of `p^*(a ⊗ b) ∪ q^*(a' ⊗ b')` against `λ_X ⊗ λ_Y`, for homogeneous classes. -/
theorem contractRight_productTrace_tmul {j i' j' : ℤ} {a b : 𝔇.H X} {a' b' : 𝔇.H Y}
    (hb : b ∈ 𝔇.grade X j) (ha' : a' ∈ 𝔇.grade Y i') (hb' : b' ∈ 𝔇.grade Y j') :
    DiagonalExpansion.contractRight
        (𝔇.untwistTrace (prod X Y) (d + e) (𝔇.productTrace hA5 X Y d e lamX lamY))
        ((𝔇.kunnethEquiv hA5 (prod X Y) (prod X Y)).symm
          (𝔇.pull (prodMap (fst X Y) (fst X Y)) (𝔇.kunnethMap X X (a ⊗ₜ b)) *
            𝔇.pull (prodMap (snd X Y) (snd X Y)) (𝔇.kunnethMap Y Y (a' ⊗ₜ b')))) =
      𝔇.kunnethMap X Y (DiagonalExpansion.contractRight (𝔇.untwistTrace X d lamX) (a ⊗ₜ b) ⊗ₜ
        DiagonalExpansion.contractRight (𝔇.untwistTrace Y e lamY) (a' ⊗ₜ b')) := by
  have hK : ∀ z, (𝔇.kunnethEquiv hA5 (prod X Y) (prod X Y)).symm
      (𝔇.kunnethMap (prod X Y) (prod X Y) z) = z := fun z ↦
    (𝔇.kunnethEquiv hA5 (prod X Y) (prod X Y)).symm_apply_apply z
  rw [𝔇.pull_kunnethMap_mul_pull_kunnethMap X Y a b a' b' hb ha', ← map_zsmul, hK, map_zsmul,
    DiagonalExpansion.contractRight_tmul, DiagonalExpansion.contractRight_tmul,
    DiagonalExpansion.contractRight_tmul,
    𝔇.untwistTrace_productTrace_kunnethMap hA5 X Y d e lamX lamY hb hb',
    TensorProduct.smul_tmul_smul, map_smul]
  by_cases hj : j = 2 * (d : ℤ)
  · have h1 : Int.negOnePow (j * i') = 1 := by
      rw [hj, Int.negOnePow_eq_one_iff]
      exact ⟨(d : ℤ) * i', by ring⟩
    rw [h1, Units.val_one, one_smul]
  · rw [𝔇.untwistTrace_eq_zero X d lamX j hj b hb, zero_mul, zero_smul, smul_zero]

/-- **The contraction of `p^*z ∪ q^*w` against `λ_X ⊗ λ_Y`** is the product of the contractions of
`z ∈ H^*(X) ⊗ H^*(X)` against `λ_X` and of `w ∈ H^*(Y) ⊗ H^*(Y)` against `λ_Y`. -/
theorem contractRight_productTrace_mul (z : 𝔇.H X ⊗[F] 𝔇.H X) (w : 𝔇.H Y ⊗[F] 𝔇.H Y) :
    DiagonalExpansion.contractRight
        (𝔇.untwistTrace (prod X Y) (d + e) (𝔇.productTrace hA5 X Y d e lamX lamY))
        ((𝔇.kunnethEquiv hA5 (prod X Y) (prod X Y)).symm
          (𝔇.pull (prodMap (fst X Y) (fst X Y)) (𝔇.kunnethMap X X z) *
            𝔇.pull (prodMap (snd X Y) (snd X Y)) (𝔇.kunnethMap Y Y w))) =
      𝔇.kunnethMap X Y (DiagonalExpansion.contractRight (𝔇.untwistTrace X d lamX) z ⊗ₜ
        DiagonalExpansion.contractRight (𝔇.untwistTrace Y e lamY) w) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, add_mul, TensorProduct.add_tmul, hz, hz']
  | tmul a b =>
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [map_add, mul_add, TensorProduct.tmul_add, hw, hw']
  | tmul a' b' =>
  induction b using DirectSum.Decomposition.inductionOn (𝔇.grade X) with
  | zero => simp
  | add b c hb hc => simp only [TensorProduct.tmul_add, map_add, add_mul, TensorProduct.add_tmul,
      hb, hc]
  | @homogeneous j b =>
  induction a' using DirectSum.Decomposition.inductionOn (𝔇.grade Y) with
  | zero => simp
  | add a' c' ha' hc' => simp only [TensorProduct.add_tmul, map_add, mul_add,
      TensorProduct.tmul_add, ha', hc']
  | @homogeneous i' a' =>
  induction b' using DirectSum.Decomposition.inductionOn (𝔇.grade Y) with
  | zero => simp
  | add b' c' hb' hc' => simp only [TensorProduct.tmul_add, map_add, mul_add,
      TensorProduct.tmul_add, hb', hc']
  | @homogeneous j' b' =>
  exact 𝔇.contractRight_productTrace_tmul hA5 X Y d e lamX lamY b.2 a'.2 b'.2

/-- A trace map read on the coordinates of a class of degree `2d` is the trace map. -/
theorem untwistTrace_coe_tateTwistCoordinates
    (a : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d) :
    𝔇.untwistTrace X d lamX
        (tateTwistCoordinates (V := 𝔇.grade X (2 * (d : ℤ))) 𝔇.coord (d : ℤ) a : 𝔇.H X) =
      lamX a := by
  rw [untwistTrace_of_mem _ _ _ _ _ (Submodule.coe_mem _)]
  exact congrArg lamX (LinearEquiv.symm_apply_apply _ a)

/-- `λ_X ⊗ λ_Y` on a class whose coordinates are `pr₁^*a ∪ pr₂^*b`. -/
theorem productTrace_of_coe_tateTwistCoordinates (a : 𝔇.H X) (b : 𝔇.H Y)
    (z : tateTwist F 𝔇.tate (𝔇.grade (prod X Y) (2 * ((d + e : ℕ) : ℤ))) (d + e : ℕ))
    (hz : (tateTwistCoordinates (V := 𝔇.grade (prod X Y) (2 * ((d + e : ℕ) : ℤ))) 𝔇.coord
      ((d + e : ℕ) : ℤ) z : 𝔇.H (prod X Y)) =
      𝔇.pull (fst X Y) a * 𝔇.pull (snd X Y) b) :
    𝔇.productTrace hA5 X Y d e lamX lamY z =
      𝔇.untwistTrace X d lamX a * 𝔇.untwistTrace Y e lamY b := by
  rw [productTrace_apply, hz, ← kunnethMap_tmul, kunnethTraceForm_kunnethMap]

end ProductTrace

/-! ### The trace map of a product -/

namespace IsCohomologicalChernCharacter

variable {𝔇} [CharZero F]
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom)

include hA1 hA3 in
/-- **`γ` is compatible with exterior products**: `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`, from its
compatibility with pullbacks and intersection products, `α × β` being `pr₁^!α · pr₂^!β`
(Remark 0FHD). -/
theorem codimensionCycleClass_codimensionExteriorProduct
    (V W : (SmoothProjectiveScheme k).FullSubcategory)
    (i j : ℕ) (α : codimensionChowGroup k V.obj.hom i) (β : codimensionChowGroup k W.obj.hom j) :
    h.codimensionCycleClass (prod V W) (i + j)
        (codimensionExteriorProduct k V.obj.hom W.obj.hom i j α β) =
      tateCup 𝔇.finrank_tate (𝔇.cup (prod V W)) i j (i + j) (by ring)
        (𝔇.pullTw (fst V W) i (h.codimensionCycleClass V i α))
        (𝔇.pullTw (snd V W) j (h.codimensionCycleClass W j β)) := by
  rw [codimensionExteriorProduct_eq_codimensionIntersectionProduct]
  refine (h.codimensionCycleClass_codimensionIntersectionProduct hA1 hA3 (prod V W) i j _ _).trans
    ?_
  rw [← h.codimensionCycleClass_codimensionGysin (fst V W) i α,
    ← h.codimensionCycleClass_codimensionGysin (snd V W) j β]
  rfl

include hA1 hA3 in
/-- **The class of the diagonal of a product**: `γ([Δ_{X × Y}]) = p^*γ([Δ_X]) ∪ q^*γ([Δ_Y])` in
`H^*((X × Y)²)`, for `p = pr₁ × pr₁ : (X × Y)² ⟶ X × X` and `q = pr₂ × pr₂ : (X × Y)² ⟶ Y × Y`
(read in the coordinates of the twists). -/
theorem untwistClass_diagonalClass_prod (X Y : (SmoothProjectiveScheme k).FullSubcategory) {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) :
    𝔇.untwistClass (prod X Y) (d + e)
        (h.codimensionCycleClass (prod (prod X Y) (prod X Y)) (d + e)
          (diagonalClass (prod X Y) (d + e))) =
      𝔇.pull (prodMap (fst X Y) (fst X Y))
          (𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d))) *
        𝔇.pull (prodMap (snd X Y) (snd X Y))
          (𝔇.untwistClass Y e (h.codimensionCycleClass (prod Y Y) e (diagonalClass Y e))) := by
  have h1 : h.codimensionCycleClass (prod (prod X Y) (prod X Y)) (d + e)
      (diagonalClass (prod X Y) (d + e)) =
        𝔇.pullTw (prodShuffle X Y) ((d + e : ℕ) : ℤ)
          (tateCup 𝔇.finrank_tate (𝔇.cup (prod (prod X X) (prod Y Y))) d e ((d + e : ℕ) : ℤ)
            (by push_cast; ring)
            (𝔇.pullTw (fst (prod X X) (prod Y Y)) d
              (h.codimensionCycleClass (prod X X) d (diagonalClass X d)))
            (𝔇.pullTw (snd (prod X X) (prod Y Y)) e
              (h.codimensionCycleClass (prod Y Y) e (diagonalClass Y e)))) :=
    (congrArg (h.codimensionCycleClass (prod (prod X Y) (prod X Y)) (d + e))
      (diagonalClass_prod X Y hX hY)).trans
      ((h.codimensionCycleClass_codimensionGysin (prodShuffle X Y) (d + e) _).trans
        (congrArg (𝔇.pullTw (prodShuffle X Y) ((d + e : ℕ) : ℤ))
          (h.codimensionCycleClass_codimensionExteriorProduct hA1 hA3 (prod X X) (prod Y Y) d e
            _ _)))
  rw [h1, untwistClass, κ_pullTw, κ_tateCup, κ_pullTw, κ_pullTw, map_mul, ← AlgHom.comp_apply,
    ← AlgHom.comp_apply, ← 𝔇.pull_comp, ← 𝔇.pull_comp, prodShuffle_fst, prodShuffle_snd]

include hA1 hA3 in
/-- **`λ_X ⊗ λ_Y` satisfies the condition of axiom (A6) for `X × Y`**: if
`(id ⊗ λ_X)γ([Δ_X]) = 1` and `(id ⊗ λ_Y)γ([Δ_Y]) = 1`, then
`(id ⊗ (λ_X ⊗ λ_Y))γ([Δ_{X × Y}]) = 1`. -/
theorem traceContract_productTrace
    (hA5 : 𝔇.KunnethAxiom) (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    {d e : ℕ} (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)
    (lamX : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (lamY : tateTwist F 𝔇.tate (𝔇.grade Y (2 * (e : ℤ))) e →ₗ[F] F)
    (hlamX : 𝔇.traceContract hA5 X d lamX
      (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) = 1)
    (hlamY : 𝔇.traceContract hA5 Y e lamY
      (h.codimensionCycleClass (prod Y Y) e (diagonalClass Y e)) = 1) :
    𝔇.traceContract hA5 (prod X Y) (d + e) (𝔇.productTrace hA5 X Y d e lamX lamY)
        (h.codimensionCycleClass (prod (prod X Y) (prod X Y)) (d + e)
          (diagonalClass (prod X Y) (d + e))) = 1 := by
  simp only [traceContract, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe] at hlamX hlamY ⊢
  have hK : ∀ (Z : (SmoothProjectiveScheme k).FullSubcategory) (x : 𝔇.H (prod Z Z)),
      x = 𝔇.kunnethMap Z Z ((𝔇.kunnethEquiv hA5 Z Z).symm x) := fun Z x ↦
    ((𝔇.kunnethEquiv hA5 Z Z).apply_symm_apply x).symm
  have hXY := h.untwistClass_diagonalClass_prod hA1 hA3 X Y hX hY
  simp only [untwistClass] at hXY
  rw [hXY, hK X (𝔇.κ (prod X X) d _), hK Y (𝔇.κ (prod Y Y) e _),
    𝔇.contractRight_productTrace_mul hA5 X Y d e lamX lamY, hlamX, hlamY, kunnethMap_tmul,
    map_one, map_one, one_mul]

/-! ### Lemma 0FIL -/

variable (hA5 : 𝔇.KunnethAxiom) (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass)

/-- **Axiom (B)(a)** for the data of (A1)–(A6): it is axiom (A5). -/
theorem kunnethIsomorphism_toWeilData : (h.toWeilData hA1 hA3 hA5 hA6).KunnethIsomorphism :=
  fun X Y ↦ hA5.2 X Y

variable (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom)

include hA4 hA7 in
/-- **The trace map of a product is the product of the trace maps**: for `X`, `Y` nonempty and
equidimensional of dimensions `d` and `e`, `λ_{X × Y} = λ_X ⊗ λ_Y`, since `λ_X ⊗ λ_Y` satisfies the
condition of (A6) for `X × Y` (`traceContract_productTrace`) and that condition determines the
trace map (Remark 0FIK). -/
theorem trace_prod_toWeilData (X Y : (SmoothProjectiveScheme k).FullSubcategory) {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hXY : IsNonemptyEquidimensional (prod X Y) (d + e)) :
    (h.toWeilData hA1 hA3 hA5 hA6).trace (prod X Y) (d + e) hXY =
      𝔇.productTrace hA5 X Y d e ((h.toWeilData hA1 hA3 hA5 hA6).trace X d hX)
        ((h.toWeilData hA1 hA3 hA5 hA6).trace Y e hY) :=
  h.trace_unique hA1 hA3 hA4 hA5 hA7 (prod X Y) (d + e) hXY _ _
    (h.traceContract_toWeilData_trace hA1 hA3 hA5 hA6 _ _ hXY)
    (h.traceContract_productTrace hA1 hA3 hA5 X Y hX.relativeDimension hY.relativeDimension _ _
      (h.traceContract_toWeilData_trace hA1 hA3 hA5 hA6 X d hX)
      (h.traceContract_toWeilData_trace hA1 hA3 hA5 hA6 Y e hY))

/-- The coordinates of `pr₁^*a ∪ pr₂^*b` are `pr₁^*` and `pr₂^*` of the coordinates. -/
theorem coe_tateTwistCoordinates_cupTw_toWeilData
    (X Y : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ)
    (hij : i + j = n) (s t m : ℤ) (hst : s + t = m)
    (a : (h.toWeilData hA1 hA3 hA5 hA6).Tw X i s) (b : (h.toWeilData hA1 hA3 hA5 hA6).Tw Y j t) :
    (tateTwistCoordinates (V := 𝔇.grade (prod X Y) n) 𝔇.coord m
        ((h.toWeilData hA1 hA3 hA5 hA6).cupTw (prod X Y) i j n hij s t m hst
          ((h.toWeilData hA1 hA3 hA5 hA6).pullTw (fst X Y) i s a)
          ((h.toWeilData hA1 hA3 hA5 hA6).pullTw (snd X Y) j t b)) : 𝔇.H (prod X Y)) =
      𝔇.pull (fst X Y) (tateTwistCoordinates (V := 𝔇.grade X i) 𝔇.coord s a : 𝔇.H X) *
        𝔇.pull (snd X Y) (tateTwistCoordinates (V := 𝔇.grade Y j) 𝔇.coord t b : 𝔇.H Y) :=
  (congrArg Subtype.val (tateTwistCoordinates_tateCup 𝔇.finrank_tate _ _ _ _ _ _ _)).trans
    (congrArg₂ (fun x y ↦ x * y) (congrArg Subtype.val (tateTwistCoordinates_map _ _ _ _))
      (congrArg Subtype.val (tateTwistCoordinates_map _ _ _ _)))

include hA4 hA7 in
/-- **Axiom (B)(b)** for the data of (A1)–(A7): `∫_{X × Y} = ∫_X ⊗ ∫_Y` via (B)(a). -/
theorem kunnethTrace_toWeilData : (h.toWeilData hA1 hA3 hA5 hA6).KunnethTrace := by
  intro X Y d e hX hY hXY
  have hμ := h.trace_prod_toWeilData hA1 hA3 hA5 hA6 hA4 hA7 X Y hX hY hXY
  refine ⟨fun a b ↦ ?_, fun i j hij hi a b ↦ ?_⟩ <;>
  refine (LinearMap.congr_fun hμ _).trans ((𝔇.productTrace_of_coe_tateTwistCoordinates hA5 X Y d e
    _ _ _ _ _
    (h.coe_tateTwistCoordinates_cupTw_toWeilData hA1 hA3 hA5 hA6 X Y _ _ _ _ _ _ _ _ a b)).trans ?_)
  · exact congrArg₂ (fun x y ↦ x * y) (𝔇.untwistTrace_coe_tateTwistCoordinates X d _ a)
      (𝔇.untwistTrace_coe_tateTwistCoordinates Y e _ b)
  · exact (congrArg (fun x ↦ x * _)
      (𝔇.untwistTrace_eq_zero X d _ i hi _ (Submodule.coe_mem _))).trans (zero_mul _)

include hA4 hA7 in
/-- **Lemma 0FIL**, for (D0), (D1), (D2') satisfying (A1)–(A7) given as separate hypotheses: the
data of Section 0FHA they define, with `∫_X = λ` as in (A6), satisfy axiom (B). -/
theorem kunneth_toWeilData : (h.toWeilData hA1 hA3 hA5 hA6).Kunneth :=
  ⟨h.kunnethIsomorphism_toWeilData hA1 hA3 hA5 hA6,
    h.kunnethTrace_toWeilData hA1 hA3 hA5 hA6 hA4 hA7⟩

end IsCohomologicalChernCharacter

end FirstChernClassData

namespace WeilChernData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F]

/-- **Stacks Project, Lemma 0FIL.** Let (D0), (D1), (D2') be data satisfying axioms (A1)–(A7) of
Section 45.14. Then axiom (B) of Section 0FHA holds for the data (D0)–(D3) they define
(`WeilChernData.toWeilData`: `γ` the cycle class map of Tag 0FIF, `∫_X = λ` the trace map of
(A6)): for smooth projective `X`, `Y` over `k`, (a) `H^*(X) ⊗_F H^*(Y) ⟶ H^*(X × Y)`,
`α ⊗ β ↦ pr₁^*α ∪ pr₂^*β`, is an isomorphism, and (b) if `X` and `Y` are nonempty and
equidimensional, `∫_{X × Y} = ∫_X ⊗ ∫_Y` via (a). -/
@[stacks 0FIL "axiom (B) of 0FHA for the data of (A1)-(A7): the Künneth map is an isomorphism and \
∫_{X×Y} = ∫_X ⊗ ∫_Y, with ∫ = λ of (A6) and γ the cycle class map of 0FIF"]
theorem kunneth_toWeilData (𝔚 : WeilChernData k F) : 𝔚.toWeilData.Kunneth :=
  𝔚.isCohomologicalChernCharacter.kunneth_toWeilData 𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth
    𝔚.trace 𝔚.divisor 𝔚.blowup

end WeilChernData

end Stacks.WeilCohomology

end
