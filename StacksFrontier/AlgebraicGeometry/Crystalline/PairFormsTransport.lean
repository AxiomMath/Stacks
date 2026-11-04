module

public import StacksFrontier.AlgebraicGeometry.Crystalline.RetractPairEquivalence

/-!
# Transporting pairs along an isomorphism of the modules of one-forms

The category of pairs `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG] is built from a ring `D`, a
module of one-forms `Ω` with a differential `d : D → Ω`, and the coordinates `d x_i`.  The library
has two spellings of `Ω_D` for the `p`-adically completed divided power envelope of a polynomial
presentation ([Stacks, Tag 07J9]): the completion of the divided power differentials of the
envelope, and the completed one-forms of the completed ring.  A `D`-linear isomorphism
`e : Ω₁ ≃ Ω₂` carrying the differential to the differential, and a basis of `Ω₁` to a basis of
`Ω₂` up to a reindexing `σ` of the coordinates, identifies the two categories of pairs: a
connection `∇` with values in `M ⊗̂ Ω₁` becomes `(1 ⊗ e) ∘ ∇` with values in `M ⊗̂ Ω₂`, and the
coordinate operators are reindexed by `σ`, so integrability and topological quasi-nilpotence are
unchanged.  This is `Crystalline.Pair.formsTransportEquivalence`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

section Transport

variable (p : ℕ) {D : Type u} [CommRing D] {Ω₁ Ω₂ : Type u} [AddCommGroup Ω₁] [Module D Ω₁]
  [AddCommGroup Ω₂] [Module D Ω₂] (e : Ω₁ ≃ₗ[D] Ω₂) {d₁ : D → Ω₁} {d₂ : D → Ω₂}
  (hd : ∀ x, e (d₁ x) = d₂ x)

/-- **A completed connection transported along an isomorphism of the one-forms**:
`(1 ⊗ e) ∘ ∇`. -/
def CompletedConnection.transportForms {M : Type u} [AddCommGroup M] [Module D M]
    (nabla : CompletedConnection p D Ω₁ d₁ M) : CompletedConnection p D Ω₂ d₂ M where
  toFun m := ((AdicCompletion.map (pAdicIdeal (A := D) p)
    (LinearMap.lTensor M e.toLinearMap)).restrictScalars D) (nabla m)
  map_add' m n := by rw [nabla.map_add, _root_.map_add]
  leibniz' f m := by
    rw [nabla.leibniz, _root_.map_add, _root_.map_smul]
    congr 1
    rw [LinearMap.restrictScalars_apply, toCompletedTensor, AdicCompletion.map_of,
      LinearMap.lTensor_tmul, LinearEquiv.coe_coe, hd]

/-- The value of a transported connection. -/
theorem CompletedConnection.transportForms_apply {M : Type u} [AddCommGroup M] [Module D M]
    (nabla : CompletedConnection p D Ω₁ d₁ M) (m : M) :
    nabla.transportForms p e hd m = AdicCompletion.map (pAdicIdeal (A := D) p)
      (LinearMap.lTensor M e.toLinearMap) (nabla m) := rfl

variable {ι₁ ι₂ : Type u} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  (σ : ι₁ ≃ ι₂) (b₁ : Module.Basis ι₁ D Ω₁) (b₂ : Module.Basis ι₂ D Ω₂)
  (hb : ∀ i, e (b₁ i) = b₂ (σ i))

include hb in
/-- **The coordinate operators do not change under transport**, up to the reindexing `σ`. -/
theorem coordOp_transportForms {M : Type u} [AddCommGroup M] [Module D M]
    (hM : IsPAdicallyComplete p D M) (nabla : CompletedConnection p D Ω₁ d₁ M) :
    coordOp p b₂ hM (nabla.transportForms p e hd) =
      fun j ↦ coordOp p b₁ hM nabla (σ.symm j) := by
  refine (eq_coordOp_of_isCoordinateExpansion p b₂ hM _ (fun _ ↦ rfl) fun m ↦ ?_).symm
  let := completedTensorTopology p D Ω₂ M
  have h : ∑ j, toCompletedTensor p D Ω₂ M (coordOp p b₁ hM nabla (σ.symm j) m ⊗ₜ[D] b₂ j) =
      nabla.transportForms p e hd m := by
    rw [CompletedConnection.transportForms_apply, nabla_eq_sum_coordOp p b₁ hM nabla m,
      AdicCompletion.map_of, _root_.map_sum, ← _root_.map_sum]
    simp only [LinearMap.lTensor_tmul, LinearEquiv.coe_coe, hb]
    congr 1
    exact (Fintype.sum_equiv σ _ _ fun i ↦ by rw [Equiv.symm_apply_apply]).symm
  exact h ▸ hasSum_fintype _

/-- Transport back along `e⁻¹` recovers the connection. -/
theorem CompletedConnection.transportForms_symm {M : Type u} [AddCommGroup M] [Module D M]
    (nabla : CompletedConnection p D Ω₁ d₁ M)
    (hd' : ∀ x, e.symm (d₂ x) = d₁ x) :
    (nabla.transportForms p e hd).transportForms p e.symm hd' = nabla := by
  refine CompletedConnection.ext fun m ↦ ?_
  simp only [CompletedConnection.transportForms_apply]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.lTensor_comp]
  have : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by ext; simp
  rw [this, LinearMap.lTensor_id, AdicCompletion.map_id, LinearMap.id_apply]

/-- A linear map horizontal for two connections is horizontal for their transports. -/
theorem horizontal_transportForms {M N : Type u} [AddCommGroup M] [Module D M] [AddCommGroup N]
    [Module D N] {nablaM : CompletedConnection p D Ω₁ d₁ M}
    {nablaN : CompletedConnection p D Ω₁ d₁ N} (f : M →ₗ[D] N)
    (hf : ∀ m, nablaN (f m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map f (LinearMap.id (R := D) (M := Ω₁))) (nablaM m)) (m : M) :
    nablaN.transportForms p e hd (f m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map f (LinearMap.id (R := D) (M := Ω₂)))
        (nablaM.transportForms p e hd m) := by
  simp only [CompletedConnection.transportForms_apply]
  rw [hf, AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
  congr 2
  ext x ω
  simp

variable {dx₁ : ι₁ → Ω₁} {dx₂ : ι₂ → Ω₂} (hdx₁ : ∀ i, dx₁ i = b₁ i) (hdx₂ : ∀ i, dx₂ i = b₂ i)

include hb hdx₁ hdx₂ in
/-- **A pair transported along an isomorphism of the one-forms**, the coordinates being
reindexed along `σ`. -/
def Pair.transportForms (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    Pair.{u, u, u, u} p D Ω₂ dx₂ d₂ where
  carrier := P.carrier
  isPAdicallyComplete := P.isPAdicallyComplete
  nabla := P.nabla.transportForms p e hd
  hasCoordinateOperators :=
    ⟨_, isCoordinateExpansion_coordOp p b₂ P.isPAdicallyComplete _ hdx₂⟩
  isIntegrable := by
    intro theta hco i j
    rw [eq_coordOp_of_isCoordinateExpansion p b₂ P.isPAdicallyComplete _ hdx₂ hco,
      coordOp_transportForms p e hd σ b₁ b₂ hb]
    exact P.isIntegrable _ (isCoordinateExpansion_coordOp p b₁ P.isPAdicallyComplete _ hdx₁) _ _
  isTopologicallyQuasiNilpotent := by
    intro theta hco m
    rw [eq_coordOp_of_isCoordinateExpansion p b₂ P.isPAdicallyComplete _ hdx₂ hco,
      coordOp_transportForms p e hd σ b₁ b₂ hb]
    have h := P.isTopologicallyQuasiNilpotent _
      (isCoordinateExpansion_coordOp p b₁ P.isPAdicallyComplete _ hdx₁) m
    refine (h.preimage (f := fun q : ι₂ × ℕ ↦ (σ.symm q.1, q.2)) ?_).subset fun q hq ↦ hq
    intro q _ q' _ hqq'
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hqq'
    exact Prod.ext hqq'.1 hqq'.2

/-- The connection of a transported pair. -/
theorem Pair.transportForms_nabla (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    (P.transportForms p e hd σ b₁ b₂ hb hdx₁ hdx₂).nabla = P.nabla.transportForms p e hd := rfl

/-- **The functor transporting pairs along an isomorphism of the one-forms.** -/
def Pair.transportFormsFunctor :
    Pair.{u, u, u, u} p D Ω₁ dx₁ d₁ ⥤ Pair.{u, u, u, u} p D Ω₂ dx₂ d₂ where
  obj P := P.transportForms p e hd σ b₁ b₂ hb hdx₁ hdx₂
  map f := ⟨f.toLinearMap, horizontal_transportForms p e hd f.toLinearMap f.horizontal⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The identity is horizontal between two equal connections. -/
theorem horizontal_id_of_eq {Ω : Type u} [AddCommGroup Ω] [Module D Ω] {d : D → Ω}
    {M : Type u} [AddCommGroup M] [Module D M] {nabla nabla' : CompletedConnection p D Ω d M}
    (h : nabla' = nabla) (m : M) :
    nabla' (LinearMap.id (R := D) m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map LinearMap.id (LinearMap.id (R := D) (M := Ω))) (nabla m) := by
  subst h
  rw [TensorProduct.map_id, AdicCompletion.map_id]
  rfl

variable (hd' : ∀ x, e.symm (d₂ x) = d₁ x) (hb' : ∀ j, e.symm (b₂ j) = b₁ (σ.symm j))

/-- Transporting a pair along `e` and back along `e⁻¹` recovers its connection. -/
theorem Pair.transportForms_transportForms_nabla (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    ((P.transportForms p e hd σ b₁ b₂ hb hdx₁ hdx₂).transportForms p e.symm hd' σ.symm b₂ b₁
      hb' hdx₂ hdx₁).nabla = P.nabla :=
  CompletedConnection.transportForms_symm p e hd P.nabla hd'

/-- A pair is isomorphic to its transport along `e` and back along `e⁻¹`, by the identity. -/
def Pair.transportFormsUnitIso (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    P ≅ (P.transportForms p e hd σ b₁ b₂ hb hdx₁ hdx₂).transportForms p e.symm hd' σ.symm b₂ b₁
      hb' hdx₂ hdx₁ where
  hom := ⟨LinearMap.id, fun m ↦ by
    rw [Pair.transportForms_transportForms_nabla]
    exact horizontal_id_of_eq p rfl m⟩
  inv := ⟨LinearMap.id, fun m ↦ by
    rw [Pair.transportForms_transportForms_nabla]
    exact horizontal_id_of_eq p rfl m⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **Transport along an isomorphism of the one-forms is an equivalence of the categories of
pairs**, with inverse the transport along `e⁻¹`. -/
def Pair.formsTransportEquivalence :
    Pair.{u, u, u, u} p D Ω₁ dx₁ d₁ ≌ Pair.{u, u, u, u} p D Ω₂ dx₂ d₂ :=
  CategoryTheory.Equivalence.mk (Pair.transportFormsFunctor p e hd σ b₁ b₂ hb hdx₁ hdx₂)
    (Pair.transportFormsFunctor p e.symm hd' σ.symm b₂ b₁ hb' hdx₂ hdx₁)
    (NatIso.ofComponents
      (fun P ↦ Pair.transportFormsUnitIso p e hd σ b₁ b₂ hb hdx₁ hdx₂ hd' hb' P)
      fun _ ↦ rfl)
    (NatIso.ofComponents (fun P ↦ (Pair.transportFormsUnitIso p e.symm hd' σ.symm b₂ b₁ hb'
      hdx₂ hdx₁
      (fun x ↦ by rw [LinearEquiv.symm_symm]; exact hd x)
      (fun i ↦ by rw [LinearEquiv.symm_symm, Equiv.symm_symm]; exact hb i) P).symm)
      fun _ ↦ rfl)

/-- The functor of `Crystalline.Pair.formsTransportEquivalence` is the transport along `e`. -/
theorem Pair.formsTransportEquivalence_functor :
    (Pair.formsTransportEquivalence p e hd σ b₁ b₂ hb hdx₁ hdx₂ hd' hb').functor =
      Pair.transportFormsFunctor p e hd σ b₁ b₂ hb hdx₁ hdx₂ := rfl

end Transport

end Crystalline

end
