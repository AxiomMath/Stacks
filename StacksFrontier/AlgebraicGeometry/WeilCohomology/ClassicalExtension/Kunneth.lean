module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.PoincareDuality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Product
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalKunnethTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalSecondProjection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The Künneth formula for the extension of a classical Weil cohomology theory

For the data (D0)–(D3) obtained from a classical Weil cohomology theory by taking products over
connected components (`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilData`), the
Künneth formula (B) holds: the components of `X × Y` are the products `X_c × Y_d` of the
components of `X` and `Y`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.bijective_compMap_fst_snd`), so that
`H^*(X) ⊗ H^*(Y) = ∏_{c, d} H^*(X_c) ⊗ H^*(Y_d)` maps factor by factor to
`H^*(X × Y) = ∏_{c, d} H^*(X_c × Y_d)` by the Künneth isomorphisms of the classical theory, and
the trace of `X × Y` is the sum of the traces of the `X_c × Y_d`, which are the products of the
traces of `X_c` and `Y_d` (Stacks 0FGX).

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.kunnethIsomorphism`: axiom (B)(a).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.kunnethTrace`: axiom (B)(b).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilData_kunneth`: axiom (B).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum TensorProduct

universe u v

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

/-! ### Components of a product, by index -/

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] [IsAlgClosed k] (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The components of `X × Y` are the pairs of components of `X` and `Y`**, by index. -/
theorem bijective_idxMap_fst_snd :
    Function.Bijective fun E : Idx (prod X Y) ↦ (idxMap (fst X Y) E, idxMap (snd X Y) E) := by
  have h : (fun E : Idx (prod X Y) ↦ (idxMap (fst X Y) E, idxMap (snd X Y) E)) =
      Prod.map (idxEquiv X).symm (idxEquiv Y).symm ∘
        (fun E ↦ (compMap (fst X Y) E, compMap (snd X Y) E)) ∘ idxEquiv (prod X Y) := rfl
  rw [h]
  exact ((Equiv.prodCongr (idxEquiv X).symm (idxEquiv Y).symm).bijective.comp
    (bijective_compMap_fst_snd X Y)).comp (idxEquiv _).bijective

/-- The identification of the indices of the components of `X × Y` with pairs of indices. -/
def idxProdEquiv : Idx (prod X Y) ≃ Idx X × Idx Y :=
  Equiv.ofBijective _ (bijective_idxMap_fst_snd X Y)

/-- `idxProdEquiv X Y` sends a component of `X × Y` to the components of `X` and `Y` it maps to
under the two projections. -/
@[simp]
theorem idxProdEquiv_apply (E : Idx (prod X Y)) :
    idxProdEquiv X Y E = (idxMap (fst X Y) E, idxMap (snd X Y) E) :=
  rfl

end SmoothProjectiveScheme

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-- The Künneth map of a classical theory on total cohomology: `x ⊗ y ↦ p^*x ∪ q^*y`. -/
theorem kunnethMap_tmul {V V' P : (SmoothProjective k).FullSubcategory} (p : P ⟶ V)
    (q : P ⟶ V') (x : T.totalH V) (y : T.totalH V') :
    kunnethMap (T.H V) (T.H V') (T.H P) (fun i ↦ T.pullback p i) (fun j ↦ T.pullback q j)
      (x ⊗ₜ y) = T.pullTotal p x * T.pullTotal q y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [TensorProduct.add_tmul, map_add, hx, hx', map_add, add_mul]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, hy, hy', map_add, mul_add]
    | of j b =>
      rw [← lof_eq_of F, ← lof_eq_of F, kunnethMap_lof_tmul_lof, pullTotal_lof, pullTotal_lof,
        ExternallyGradedAlgebra.lof_mul_lof]

/-- The classical Künneth map at the component `E` of `X × Y`. -/
abbrev kunnethAt (X Y : (SmoothProjectiveScheme k).FullSubcategory) (E : Idx (prod X Y)) :
    T.totalH (compAt X (idxMap (fst X Y) E)) ⊗[F] T.totalH (compAt Y (idxMap (snd X Y) E)) →ₗ[F]
      T.totalH (compAt (prod X Y) E) :=
  kunnethMap (T.H _) (T.H _) (T.H _) (fun i ↦ T.pullback (resIdx (fst X Y) E) i)
    (fun j ↦ T.pullback (resIdx (snd X Y) E) j)

/-- The classical Künneth map at each component of `X × Y` is bijective. -/
theorem bijective_kunnethAt (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (E : Idx (prod X Y)) :
    Function.Bijective (T.kunnethAt X Y E) :=
  T.kunneth _ _ _ _ _ (isPullback_resIdx_fst_snd X Y E)

/-! ### Axiom (B)(a) -/

/-- **Axiom (B)(a)** for the extension: the Künneth map `H^*(X) ⊗ H^*(Y) → H^*(X × Y)` is an
isomorphism. -/
theorem kunnethIsomorphism : T.toWeilData.KunnethIsomorphism := by
  intro X Y
  let φ : Idx X × Idx Y → Type v := fun p ↦
    T.totalH (compAt X p.1) ⊗[F] T.totalH (compAt Y p.2)
  let L₁ : T.extH X ⊗[F] T.extH Y ≃ₗ[F] ∀ c, ∀ d, φ (c, d) :=
    (TensorProduct.piLeft F (T.extH Y) fun c ↦ T.totalH (compAt X c)).trans
      (LinearEquiv.piCongrRight fun c ↦
        TensorProduct.piRight F F (T.totalH (compAt X c)) fun d ↦ T.totalH (compAt Y d))
  let L₂ : (∀ c, ∀ d, φ (c, d)) →ₗ[F] ∀ p, φ p :=
    LinearMap.pi fun p ↦ (LinearMap.proj (R := F) (φ := fun d ↦ φ (p.1, d)) p.2).comp
      (LinearMap.proj (R := F) (φ := fun c ↦ ∀ d, φ (c, d)) p.1)
  let L₃ : (∀ p, φ p) ≃ₗ[F] ∀ E, φ (idxProdEquiv X Y E) :=
    (LinearEquiv.piCongrLeft F φ (idxProdEquiv X Y)).symm
  let L₄ : (∀ E, φ (idxProdEquiv X Y E)) →ₗ[F] T.extH (prod X Y) :=
    LinearMap.pi fun E ↦ (T.kunnethAt X Y E).comp (LinearMap.proj E)
  have hL₂ : Function.Bijective L₂ := by
    refine ⟨fun u u' h ↦ funext fun c ↦ funext fun d ↦ congrFun h (c, d), fun v ↦
      ⟨fun c d ↦ v (c, d), funext fun ⟨c, d⟩ ↦ rfl⟩⟩
  have hL₄ : Function.Bijective L₄ := by
    refine ⟨fun u u' h ↦ funext fun E ↦ (T.bijective_kunnethAt X Y E).1 (congrFun h E),
      fun v ↦ ⟨fun E ↦ ((T.bijective_kunnethAt X Y E).2 (v E)).choose, funext fun E ↦
        ((T.bijective_kunnethAt X Y E).2 (v E)).choose_spec⟩⟩
  have h : T.toWeilData.kunnethMap X Y = L₄ ∘ₗ L₃.toLinearMap ∘ₗ L₂ ∘ₗ L₁.toLinearMap := by
    have hL : ∀ (x : T.extH X) (y : T.extH Y), L₁ (x ⊗ₜ y) = fun c d ↦ x c ⊗ₜ y d := by
      intro x y
      funext c d
      simp [L₁, TensorProduct.piRightHom_tmul]
    refine TensorProduct.ext' fun x y ↦ funext fun E ↦ ?_
    rw [WeilData.kunnethMap_tmul, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, hL]
    exact (T.kunnethMap_tmul _ _ _ _).symm
  rw [h]
  exact hL₄.comp (L₃.bijective.comp (hL₂.comp L₁.bijective))

/-! ### Axiom (B)(b) -/

/-- Casting the degree-`n` component of a total cohomology class along `n = n'` gives its
degree-`n'` component. -/
theorem degreeCast_component {V : (SmoothProjective k).FullSubcategory} {n n' : ℤ} (h : n = n')
    (z : T.totalH V) :
    ExternallyGraded.degreeCast (R := F) (X := (T.H V).piece) h (component F ℤ _ n z) =
      component F ℤ _ n' z := by
  subst h
  rfl

/-- The trace of a class supported on the components of `X × Y`, in terms of the classical
traces: `∫_{X_c} a_c` with the degree read off the dimension of the component. -/
theorem extTraceUntw_apply' (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (x : T.extH X) :
    T.extTraceUntw X hX x = ∑ i, T.integration (compAt X i)
      (component F ℤ _ (2 * (T.dimension (compAt X i) : ℤ)) (x i)) := by
  rw [extTraceUntw_apply]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg _ (T.degreeCast_component _ _)

/-- **The trace of `X × Y` is the product of the traces**:
`∫_{X × Y} pr₁^*x ∪ pr₂^*y = ∫_X x · ∫_Y y` on all of `H^*(X) × H^*(Y)`, the traces vanishing
outside the top degrees. -/
theorem extTraceUntw_prod {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hXY : IsNonemptyEquidimensional (prod X Y) (d + e)) (x : T.extH X) (y : T.extH Y) :
    T.extTraceUntw (prod X Y) hXY (T.extPull (fst X Y) x * T.extPull (snd X Y) y) =
      T.extTraceUntw X hX x * T.extTraceUntw Y hY y := by
  rw [extTraceUntw_apply', extTraceUntw_apply', extTraceUntw_apply', Finset.sum_mul_sum,
    ← Fintype.sum_prod_type', ← Equiv.sum_comp (idxProdEquiv X Y)]
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  have hk := LinearMap.congr_fun (T.integration_comp_kunnethMap (isPullback_resIdx_fst_snd X Y E))
    (x (idxMap (fst X Y) E) ⊗ₜ y (idxMap (snd X Y) E))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lift.tmul,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at hk
  rw [Pi.mul_apply, extPull_apply, extPull_apply, ← T.kunnethMap_tmul]
  exact hk

/-- A class of degree `i` has trace zero unless `i` is the top degree. -/
theorem extTraceUntw_eq_zero_of_ne {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) {i : ℤ} (hi : i ≠ 2 * d) {x : T.extH X}
    (hx : x ∈ T.extGrade X i) : T.extTraceUntw X hX x = 0 := by
  rw [extTraceUntw_apply]
  refine Finset.sum_eq_zero fun c _ ↦ ?_
  rw [← ExternallyGradedAlgebra.lof_component_of_mem _ (T.mem_extGrade.1 hx c),
    ExternallyGradedAlgebra.component_lof_of_ne _ hi, map_zero, map_zero]

/-- **Axiom (B)(b)** for the extension: `∫_{X × Y} = ∫_X ⊗ ∫_Y`. -/
theorem kunnethTrace : T.toWeilData.KunnethTrace := by
  intro X Y d e hX hY hXY
  refine ⟨fun a b ↦ ?_, fun i j h hi a b ↦ ?_⟩
  · rw [toWeilData_trace, toWeilData_trace, toWeilData_trace, twistCoord_cupTw,
      WeilData.coe_cup, twistCoord_pullTw, twistCoord_pullTw, coe_pullDeg, coe_pullDeg]
    exact T.extTraceUntw_prod hX hY hXY _ _
  · rw [toWeilData_trace, twistCoord_cupTw, WeilData.coe_cup, twistCoord_pullTw,
      twistCoord_pullTw, coe_pullDeg, coe_pullDeg, T.extTraceUntw_prod hX hY hXY,
      T.extTraceUntw_eq_zero_of_ne hX hi (T.twCoord X i d a).2, zero_mul]

/-- **Axiom (B), the Künneth formula**, for the extension. -/
theorem toWeilData_kunneth : T.toWeilData.Kunneth :=
  ⟨T.kunnethIsomorphism, T.kunnethTrace⟩

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
