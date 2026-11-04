module

public import StacksFrontier.Homology.Eta.Perfect.TotalDirectSumIdeal

/-!
# The obstruction ideals of the décalage do not see a unit multiple of the equation

Let `A` be a commutative ring, let `f ∈ A` be a nonzerodivisor, let `u ∈ A` be a unit and let
`M^•` be a bounded complex of finite free `A`-modules whose determinantal ideals `I_i(M^•, f)` are
principal.  The ideals `J_i(M^•, f) ⊆ A ⧸ fA` of More on Algebra, Tag 0GSW and
`J_i(M^•, u f) ⊆ A ⧸ (u f)A` correspond under the identification `A ⧸ fA = A ⧸ (u f)A`; hence so do
the total obstruction ideals `J(M^•, f)` and `J(M^•, u f)` of Tag 0F81.

This is the companion, for the obstruction ideals, of Tag 0GST (`idealI_unit_mul_eq`), which says
the same of the determinantal ideals.  It is what lets the obstruction ideals computed on two
affine charts of a triple as in Situation 0F8S be compared on an overlap, where the two
equations of the divisor differ by a unit (More on Flatness, Tag 0GTZ).

## Main results

* `Stacks.Decalage.DirectSumIdeal.identifiesDirectSum_reduction_congr`: the direct-sum property
  of Tag 0F80 for the reductions of two isomorphic maps `E → P × Q` over two `A`-algebras `R` and
  `R'` is the same condition on an algebra `D` over both.
* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_unit_mul`: `J_i(M^•, u f)` is the image of
  `J_i(M^•, f)` under `A ⧸ fA ≃ A ⧸ (u f)A`.
* `Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal_unit_mul`: the same for the total
  obstruction ideals.

## Implementation notes

Both obstruction ideals are characterised by the universal property of Tag 0F80 for the
reduction of the décalage inclusion `x ↦ (x, dⁱ x)` on the degree-`i` décalage term.  The
décalage term for `f` is identified with the graph kernel `{(x, y) : dⁱ x = f y}` by
`EtaPow.graphToEta`, and the graph kernel for `u f` is identified with the one for `f` by
`(x, y) ↦ (x, u y)`.  The two reductions are then compared after the single base change
`D ⊗_A -`, which both factor through.
-/

@[expose] public noncomputable section

open TensorProduct Stacks.SplitInjectionDirectSum

universe u

namespace Stacks.Decalage.DirectSumIdeal

section Transport

variable {A : Type*} [CommRing A]

/-- The base change of `(x, y) ↦ (x, 0)` on a product, read through
`D ⊗ (P × Q) ≅ (D ⊗ P) × (D ⊗ Q)`, is the projection onto the first factor. -/
private theorem prodRight_baseChange_q₁_eq {D P Q : Type*} [CommRing D] [Algebra A D]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (z : D ⊗[A] (P × Q)) :
    TensorProduct.prodRight A D D P Q ((q₁ (A := A) (N₁ := P) (N₂ := Q)).baseChange D z) =
      ((TensorProduct.prodRight A D D P Q z).1, 0) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add z w hz hw => simp only [map_add, hz, hw, Prod.fst_add, Prod.mk_add_mk, add_zero]
  | tmul d x => simp [q₁]

/-- The base change of `(x, y) ↦ (0, y)` on a product, read through
`D ⊗ (P × Q) ≅ (D ⊗ P) × (D ⊗ Q)`, is the projection onto the second factor. -/
private theorem prodRight_baseChange_q₂_eq {D P Q : Type*} [CommRing D] [Algebra A D]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (z : D ⊗[A] (P × Q)) :
    TensorProduct.prodRight A D D P Q ((q₂ (A := A) (N₁ := P) (N₂ := Q)).baseChange D z) =
      (0, (TensorProduct.prodRight A D D P Q z).2) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add z w hz hw => simp only [map_add, hz, hw, Prod.snd_add, Prod.mk_add_mk, add_zero]
  | tmul d x => simp [q₂]

/-- The condition of Tag 0F80 read in split form: the image of a map `σ : X → Y₁ × Y₂` is stable
under the two coordinate projections. -/
private def ProjStable {D X Y₁ Y₂ : Type*} [CommRing D] [AddCommGroup X] [Module D X]
    [AddCommGroup Y₁] [Module D Y₁] [AddCommGroup Y₂] [Module D Y₂] (σ : X →ₗ[D] Y₁ × Y₂) :
    Prop :=
  (∀ x, ∃ x', σ x' = ((σ x).1, 0)) ∧ ∀ x, ∃ x', σ x' = (0, (σ x).2)

/-- The direct-sum property of the reduction of `s : E → P × Q` over an `A`-algebra `R`, tested
on an `R`-algebra `D`, is the projection stability of the single base change `D ⊗_A s`. -/
private theorem identifiesDirectSum_reduction_iff {E P Q : Type*}
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (s : E →ₗ[A] P × Q) (R D : Type*) [CommRing R] [CommRing D] [Algebra A R] [Algebra A D]
    [Algebra R D] [IsScalarTower A R D] :
    IdentifiesDirectSum
        ((TensorProduct.prodRight A R R P Q).toLinearMap ∘ₗ s.baseChange R) D ↔
      ProjStable ((TensorProduct.prodRight A D D P Q).toLinearMap ∘ₗ s.baseChange D) := by
  set t := (TensorProduct.prodRight A R R P Q).toLinearMap ∘ₗ s.baseChange R
  set σ := (TensorProduct.prodRight A D D P Q).toLinearMap ∘ₗ s.baseChange D
  let eE := TensorProduct.AlgebraTensorModule.cancelBaseChange A R D D E
  let θ : D ⊗[R] ((R ⊗[A] P) × (R ⊗[A] Q)) ≃ₗ[D] (D ⊗[A] P) × (D ⊗[A] Q) :=
    (TensorProduct.prodRight R D D (R ⊗[A] P) (R ⊗[A] Q)).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R D D P).prodCongr
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A R D D Q))
  have hst : ∀ z, θ (t.baseChange D z) = σ (eE z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul d w =>
      induction w using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add w w' hw hw' => simp only [tmul_add, map_add, hw, hw']
      | tmul r x =>
        simp [t, σ, θ, eE]
  have hq₁ : ∀ z, θ ((q₁ (A := R) (N₁ := R ⊗[A] P) (N₂ := R ⊗[A] Q)).baseChange D z) =
      ((θ z).1, 0) := by
    intro z
    simp [θ, prodRight_baseChange_q₁_eq]
  have hq₂ : ∀ z, θ ((q₂ (A := R) (N₁ := R ⊗[A] P) (N₂ := R ⊗[A] Q)).baseChange D z) =
      (0, (θ z).2) := by
    intro z
    simp [θ, prodRight_baseChange_q₂_eq]
  rw [identifiesDirectSum_iff_stable]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · obtain ⟨w, hw⟩ := h₁ (LinearMap.mem_range_self _ (eE.symm x))
      refine ⟨eE w, ?_⟩
      rw [← hst, hw, LinearMap.comp_apply, hq₁, hst, LinearEquiv.apply_symm_apply]
    · obtain ⟨w, hw⟩ := h₂ (LinearMap.mem_range_self _ (eE.symm x))
      refine ⟨eE w, ?_⟩
      rw [← hst, hw, LinearMap.comp_apply, hq₂, hst, LinearEquiv.apply_symm_apply]
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := h₁ (eE x)
      refine ⟨eE.symm x', θ.injective ?_⟩
      rw [LinearMap.comp_apply, hq₁, hst, hst, LinearEquiv.apply_symm_apply, hx']
    · rintro _ ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := h₂ (eE x)
      refine ⟨eE.symm x', θ.injective ?_⟩
      rw [LinearMap.comp_apply, hq₂, hst, hst, LinearEquiv.apply_symm_apply, hx']

/-- Projection stability is invariant under isomorphisms of source and of the two factors of
the target which intertwine the two maps. -/
private theorem projStable_congr {D X Y₁ Y₂ X' Y₁' Y₂' : Type*} [CommRing D]
    [AddCommGroup X] [Module D X] [AddCommGroup Y₁] [Module D Y₁] [AddCommGroup Y₂] [Module D Y₂]
    [AddCommGroup X'] [Module D X'] [AddCommGroup Y₁'] [Module D Y₁']
    [AddCommGroup Y₂'] [Module D Y₂']
    (σ : X →ₗ[D] Y₁ × Y₂) (τ : X' →ₗ[D] Y₁' × Y₂')
    (e : X ≃ₗ[D] X') (p : Y₁ ≃ₗ[D] Y₁') (q : Y₂ ≃ₗ[D] Y₂')
    (h : ∀ x, τ (e x) = (p (σ x).1, q (σ x).2)) :
    ProjStable σ → ProjStable τ := by
  rintro ⟨h₁, h₂⟩
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨y', hy'⟩ := h₁ y
    refine ⟨e y', ?_⟩
    rw [h, h, hy', map_zero]
  · obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨y', hy'⟩ := h₂ y
    refine ⟨e y', ?_⟩
    rw [h, h, hy', map_zero]

/-- **The direct-sum property of Tag 0F80 for two isomorphic maps, reduced over two different
algebras.**  Let `s : E → P × Q` and `t : E' → P' × Q'` be `A`-linear maps identified by
isomorphisms `E ≅ E'`, `P ≅ P'` and `Q ≅ Q'`, and let `R`, `R'` be `A`-algebras.  For an algebra
`D` over both `R` and `R'`, compatibly with `A`, the reduction of `s` over `R` identifies a direct
sum over `D` exactly when the reduction of `t` over `R'` does: both conditions are conditions on
the single base change `D ⊗_A -`. -/
theorem identifiesDirectSum_reduction_congr {E P Q E' P' Q' : Type*}
    [AddCommGroup E] [Module A E] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [AddCommGroup E'] [Module A E'] [AddCommGroup P'] [Module A P'] [AddCommGroup Q']
    [Module A Q']
    (s : E →ₗ[A] P × Q) (t : E' →ₗ[A] P' × Q')
    (e : E ≃ₗ[A] E') (p : P ≃ₗ[A] P') (q : Q ≃ₗ[A] Q')
    (h : ∀ x, t (e x) = (p (s x).1, q (s x).2))
    (R R' D : Type*) [CommRing R] [CommRing R'] [CommRing D] [Algebra A R] [Algebra A R']
    [Algebra A D] [Algebra R D] [Algebra R' D] [IsScalarTower A R D] [IsScalarTower A R' D] :
    IdentifiesDirectSum ((TensorProduct.prodRight A R R P Q).toLinearMap ∘ₗ s.baseChange R) D ↔
      IdentifiesDirectSum
        ((TensorProduct.prodRight A R' R' P' Q').toLinearMap ∘ₗ t.baseChange R') D := by
  rw [identifiesDirectSum_reduction_iff, identifiesDirectSum_reduction_iff]
  have key : ∀ x, ((TensorProduct.prodRight A D D P' Q').toLinearMap ∘ₗ t.baseChange D)
      (LinearEquiv.baseChange A D E E' e x) =
      (LinearEquiv.baseChange A D P P' p
          (((TensorProduct.prodRight A D D P Q).toLinearMap ∘ₗ s.baseChange D) x).1,
        LinearEquiv.baseChange A D Q Q' q
          (((TensorProduct.prodRight A D D P Q).toLinearMap ∘ₗ s.baseChange D) x).2) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero]
    | add x y hx hy =>
      simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    | tmul d x => simp [h]
  refine ⟨projStable_congr _ _ (LinearEquiv.baseChange A D E E' e)
      (LinearEquiv.baseChange A D P P' p) (LinearEquiv.baseChange A D Q Q' q) key, ?_⟩
  refine projStable_congr _ _ (LinearEquiv.baseChange A D E E' e).symm
    (LinearEquiv.baseChange A D P P' p).symm (LinearEquiv.baseChange A D Q Q' q).symm
    fun x => ?_
  obtain ⟨y, rfl⟩ := (LinearEquiv.baseChange A D E E' e).surjective x
  rw [LinearEquiv.symm_apply_apply, key, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

end Transport

section UnitChange

open EtaPow

variable {A : Type u} [CommRing A]

/-- The décalage inclusion `x ↦ (x, dⁱ x)` of the degree-`i` décalage term of `M^•` with respect to
`f`, into `fⁱMⁱ × fⁱ⁺¹Mⁱ⁺¹`; its reduction modulo `f` is `ObstructionIdeal.etaReductionMap`. -/
private def etaIncl (C : BoundedComplex A) (f : A) (i : ℤ) :
    fetaTerm f (C.d i).mulVecLin i →ₗ[A]
      fpowSub f (Fin (C.rank i) → A) i × fpowSub f (Fin (C.rank (i + 1)) → A) (i + 1) :=
  LinearMap.prod
    (LinearMap.codRestrict _ (fetaTerm f (C.d i).mulVecLin i).subtype (fun x => x.2.1))
    (LinearMap.codRestrict _
      ((fLoc f (C.d i).mulVecLin).comp (fetaTerm f (C.d i).mulVecLin i).subtype)
      (fun x => x.2.2))

private theorem etaReductionMap_eq (C : BoundedComplex A) (f : A) (i : ℤ) :
    ObstructionIdeal.etaReductionMap C f i =
      (TensorProduct.prodRight A (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f}) _ _).toLinearMap ∘ₗ
        (etaIncl C f i).baseChange (A ⧸ Ideal.span {f}) :=
  rfl

/-- The décalage term of `dⁱ` with respect to `f` is the graph kernel `{(x, y) : dⁱ x = f y}`. -/
private def graphEtaEquiv (C : BoundedComplex A) {f : A} (hf : IsRegular f) (i : ℤ) :
    LinearMap.ker (graphMap f (C.d i).mulVecLin) ≃ₗ[A] fetaTerm f (C.d i).mulVecLin i :=
  LinearEquiv.ofBijective (graphToEta f (C.d i).mulVecLin i)
    ⟨graphToEta_injective f (Module.Flat.isSMulRegular_of_isRegular hf)
      (Module.Flat.isSMulRegular_of_isRegular hf) _ i,
      graphToEta_surjective f (Module.Flat.isSMulRegular_of_isRegular hf) _ i⟩

/-- The décalage inclusion on the image of a graph-kernel element `(x, y)` is
`(fⁱ x, fⁱ⁺¹ y)`. -/
private theorem etaIncl_graphToEta (C : BoundedComplex A) {f : A} (hf : IsRegular f) (i : ℤ)
    (g : LinearMap.ker (graphMap f (C.d i).mulVecLin)) :
    etaIncl C f i (graphToEta f (C.d i).mulVecLin i g) =
      (fpowEquiv f (Module.Flat.isSMulRegular_of_isRegular hf) i g.1.1,
        fpowEquiv f (Module.Flat.isSMulRegular_of_isRegular hf) (i + 1) g.1.2) := by
  refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
  show fLoc f (C.d i).mulVecLin (fpowMap f _ i g.1.1) = fpowMap f _ (i + 1) g.1.2
  have hx : (C.d i).mulVecLin g.1.1 = f • g.1.2 := sub_eq_zero.mp g.2
  rw [fpowMap_succ]
  simp only [fpowMap_apply, fLoc_zpow_smul, fLoc_toLoc, hx]

/-- Rescaling the second coordinate by a unit identifies the graph kernel for `f` with the graph
kernel for `u f`. -/
private def graphUnitEquiv (C : BoundedComplex A) (f : A) (u : Aˣ) (i : ℤ) :
    LinearMap.ker (graphMap f (C.d i).mulVecLin) ≃ₗ[A]
      LinearMap.ker (graphMap ((u : A) * f) (C.d i).mulVecLin) where
  toFun g := ⟨(g.1.1, (↑u⁻¹ : A) • g.1.2), by
    have hx : (C.d i).mulVecLin g.1.1 = f • g.1.2 := sub_eq_zero.mp g.2
    change (C.d i).mulVecLin g.1.1 - ((u : A) * f) • ((↑u⁻¹ : A) • g.1.2) = 0
    rw [hx, smul_smul, mul_assoc, mul_comm f, ← mul_assoc, Units.mul_inv, one_mul, sub_self]⟩
  invFun g := ⟨(g.1.1, (u : A) • g.1.2), by
    have hx : (C.d i).mulVecLin g.1.1 = ((u : A) * f) • g.1.2 := sub_eq_zero.mp g.2
    change (C.d i).mulVecLin g.1.1 - f • ((u : A) • g.1.2) = 0
    rw [hx, smul_smul, mul_comm f, sub_self]⟩
  left_inv g := Subtype.ext (Prod.ext rfl (by
    change (u : A) • ((↑u⁻¹ : A) • g.1.2) = g.1.2
    rw [smul_smul, Units.mul_inv, one_smul]))
  right_inv g := Subtype.ext (Prod.ext rfl (by
    change (↑u⁻¹ : A) • ((u : A) • g.1.2) = g.1.2
    rw [smul_smul, Units.inv_mul, one_smul]))
  map_add' _ _ := Subtype.ext (Prod.ext rfl (smul_add _ _ _))
  map_smul' _ _ := Subtype.ext (Prod.ext rfl (smul_comm _ _ _))

/-- Multiplication by a unit, as an automorphism of a module. -/
private def unitSMulEquiv (M : Type*) [AddCommGroup M] [Module A M] (u : Aˣ) : M ≃ₗ[A] M where
  toFun x := (u : A) • x
  invFun x := (↑u⁻¹ : A) • x
  left_inv x := by simp only [smul_smul, Units.inv_mul, one_smul]
  right_inv x := by simp only [smul_smul, Units.mul_inv, one_smul]
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

/-- The identification `A ⧸ fA ≃ A ⧸ (u f)A` for a unit `u`. -/
def quotSpanUnitMulEquiv (f : A) (u : Aˣ) :
    (A ⧸ Ideal.span {f}) ≃+* (A ⧸ Ideal.span {(u : A) * f}) :=
  Ideal.quotEquivOfEq (Ideal.span_singleton_mul_left_unit u.isUnit f).symm

/-- `quotSpanUnitMulEquiv f u` sends the class of `a` modulo `fA` to the class of `a` modulo
`(u f)A`. -/
@[simp]
theorem quotSpanUnitMulEquiv_mk (f : A) (u : Aˣ) (a : A) :
    quotSpanUnitMulEquiv f u (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
  rfl

/-- **The degreewise obstruction ideal under a unit change of the equation.**  For a unit `u`,
`J_i(M^•, u f) ⊆ A ⧸ (u f)A` is the image of `J_i(M^•, f) ⊆ A ⧸ fA` under the identification of the
two quotients.  Both ideals are pinned by the universal property of Tag 0F80, and the two
universal properties are the same condition by
`identifiesDirectSum_etaReductionMap_unit_mul_iff`. -/
theorem etaDirectSumIdeal_unit_mul (C : BoundedComplex A) {f : A} (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) (u : Aˣ) (i : ℤ) :
    etaDirectSumIdeal C ((u : A) * f) i =
      (etaDirectSumIdeal C f i).map (quotSpanUnitMulEquiv f u : _ →+* _) := by
  refine etaDirectSumIdeal_eq_of_le_ker_iff C ((u : A) * f) i fun D _ _ => ?_
  let σ : (A ⧸ Ideal.span {f}) →+* (A ⧸ Ideal.span {(u : A) * f}) := quotSpanUnitMulEquiv f u
  let : Algebra (A ⧸ Ideal.span {f}) D := ((algebraMap _ D).comp σ).toAlgebra
  let : Algebra A D :=
    ((algebraMap (A ⧸ Ideal.span {(u : A) * f}) D).comp (Ideal.Quotient.mk _)).toAlgebra
  have : IsScalarTower A (A ⧸ Ideal.span {(u : A) * f}) D :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A (A ⧸ Ideal.span {f}) D :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [Ideal.map_le_iff_le_comap, show Ideal.comap σ
      (RingHom.ker (algebraMap (A ⧸ Ideal.span {(u : A) * f}) D)) =
        RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) D) from rfl,
    etaDirectSumIdeal_le_ker_iff C f hf hI i D]
  exact (identifiesDirectSum_etaReductionMap_unit_mul_iff C f hf u i D).symm

/-- **The total obstruction ideal under a unit change of the equation.**  For a unit `u`,
`J(M^•, u f)` is the image of `J(M^•, f)` under `A ⧸ fA ≃ A ⧸ (u f)A`. -/
theorem etaTotalDirectSumIdeal_unit_mul (C : BoundedComplex A) {f : A} (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) (u : Aˣ) :
    etaTotalDirectSumIdeal C ((u : A) * f) =
      (etaTotalDirectSumIdeal C f).map (quotSpanUnitMulEquiv f u : _ →+* _) := by
  rw [etaTotalDirectSumIdeal, etaTotalDirectSumIdeal, Ideal.map_iSup]
  exact iSup_congr fun i => etaDirectSumIdeal_unit_mul C hf hI u i

end UnitChange

end Stacks.Decalage.DirectSumIdeal

end
