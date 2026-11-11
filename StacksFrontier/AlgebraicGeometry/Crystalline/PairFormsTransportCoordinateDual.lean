module

public import StacksFrontier.AlgebraicGeometry.Crystalline.PairFormsTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairEquivalence07JH

/-!
# Transporting pairs along an isomorphism of the one-forms, for any family of coordinates

`Crystalline.Pair.formsTransportEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairFormsTransport.lean` identifies the categories of
pairs `(M, ∇)` for two spellings `Ω₁ ≃ Ω₂` of the one-forms when both have a *finite basis* on the
coordinate differentials.  This module does the same when the coordinates form an arbitrary
family and the one-forms only carry coordinate functionals dual to the differentials
(`Crystalline.IsCoordinateDual`), the situation of the completed envelope of a polynomial
algebra in infinitely many variables: a connection `∇` with values in `M ⊗̂ Ω₁` becomes
`(1 ⊗ e) ∘ ∇`, its convergent coordinate expansion is carried by the continuous map `1 ⊗ e`, and
the coordinate operators are reindexed along `σ`, so integrability and topological
quasi-nilpotence are unchanged.

## Main definitions

* `Crystalline.Pair.transportFormsOfDual` — a pair transported along `e`.
* `Crystalline.Pair.formsTransportEquivalenceOfDual` — the equivalence of the two categories of
  pairs.

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
  (hd : ∀ x, e (d₁ x) = d₂ x) {ι₁ ι₂ : Type u} (σ : ι₁ ≃ ι₂) {dx₁ : ι₁ → Ω₁} {dx₂ : ι₂ → Ω₂}
  (hdx : ∀ i, e (dx₁ i) = dx₂ (σ i))

include hdx in
/-- **A coordinate expansion is carried along the transport of the one-forms**, reindexed
along `σ`. -/
theorem isCoordinateExpansion_transportForms {M : Type u} [AddCommGroup M] [Module D M]
    {nabla : CompletedConnection p D Ω₁ d₁ M} {theta : ι₁ → (M → M)}
    (hco : IsCoordinateExpansion p D Ω₁ dx₁ nabla theta) :
    IsCoordinateExpansion p D Ω₂ dx₂ (nabla.transportForms p e hd)
      (fun j ↦ theta (σ.symm j)) := by
  intro m
  let := completedTensorTopology p D Ω₁ M
  let := completedTensorTopology p D Ω₂ M
  have hmap := (hco m).map (AdicCompletion.map (pAdicIdeal (A := D) p)
      (LinearMap.lTensor M e.toLinearMap)).toAddMonoidHom
    (continuous_linearMap_adicModuleTopology (pAdicIdeal (A := D) p)
      ((AdicCompletion.map (pAdicIdeal (A := D) p)
        (LinearMap.lTensor M e.toLinearMap)).restrictScalars D))
  rw [CompletedConnection.transportForms_apply]
  refine (Equiv.hasSum_iff σ).mp ?_
  convert hmap using 1
  all_goals try rfl
  funext i
  simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe, toCompletedTensor,
    AdicCompletion.map_of, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, hdx,
    Equiv.symm_apply_apply]

variable {coord₂ : ι₂ → (Ω₂ →ₗ[D] D)} (hc₂ : IsCoordinateDual dx₂ coord₂)

include hdx hc₂ in
/-- **A pair transported along an isomorphism of the one-forms**, the coordinates being
reindexed along `σ`, for any family of coordinates with dual functionals on `Ω₂`. -/
def Pair.transportFormsOfDual (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    Pair.{u, u, u, u} p D Ω₂ dx₂ d₂ where
  carrier := P.carrier
  isPAdicallyComplete := P.isPAdicallyComplete
  nabla := P.nabla.transportForms p e hd
  hasCoordinateOperators := ⟨_, isCoordinateExpansion_transportForms p e hd σ hdx
    P.hasCoordinateOperators.choose_spec⟩
  isIntegrable := by
    intro theta hco i j
    rw [eq_of_isCoordinateExpansion_of_isCoordinateDual p D Ω₂ P.carrier hco
      (isCoordinateExpansion_transportForms p e hd σ hdx P.hasCoordinateOperators.choose_spec)
      hc₂ P.isPAdicallyComplete.toIsHausdorff]
    exact P.isIntegrable _ P.hasCoordinateOperators.choose_spec _ _
  isTopologicallyQuasiNilpotent := by
    intro theta hco m
    rw [eq_of_isCoordinateExpansion_of_isCoordinateDual p D Ω₂ P.carrier hco
      (isCoordinateExpansion_transportForms p e hd σ hdx P.hasCoordinateOperators.choose_spec)
      hc₂ P.isPAdicallyComplete.toIsHausdorff]
    have h := P.isTopologicallyQuasiNilpotent _ P.hasCoordinateOperators.choose_spec m
    refine (h.preimage (f := fun q : ι₂ × ℕ ↦ (σ.symm q.1, q.2)) ?_).subset fun q hq ↦ hq
    intro q _ q' _ hqq'
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hqq'
    exact Prod.ext hqq'.1 hqq'.2

/-- The connection of a transported pair. -/
theorem Pair.transportFormsOfDual_nabla (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    (P.transportFormsOfDual p e hd σ hdx hc₂).nabla = P.nabla.transportForms p e hd := rfl

/-- **The functor transporting pairs along an isomorphism of the one-forms.** -/
def Pair.transportFormsOfDualFunctor :
    Pair.{u, u, u, u} p D Ω₁ dx₁ d₁ ⥤ Pair.{u, u, u, u} p D Ω₂ dx₂ d₂ where
  obj P := P.transportFormsOfDual p e hd σ hdx hc₂
  map f := ⟨f.toLinearMap, horizontal_transportForms p e hd f.toLinearMap f.horizontal⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable (hd' : ∀ x, e.symm (d₂ x) = d₁ x) (hdx' : ∀ j, e.symm (dx₂ j) = dx₁ (σ.symm j))
  {coord₁ : ι₁ → (Ω₁ →ₗ[D] D)} (hc₁ : IsCoordinateDual dx₁ coord₁)

/-- Transporting a pair along `e` and back along `e⁻¹` recovers its connection. -/
theorem Pair.transportFormsOfDual_transportFormsOfDual_nabla (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    ((P.transportFormsOfDual p e hd σ hdx hc₂).transportFormsOfDual p e.symm hd' σ.symm hdx'
      hc₁).nabla = P.nabla :=
  CompletedConnection.transportForms_symm p e hd P.nabla hd'

/-- A pair is isomorphic to its transport along `e` and back along `e⁻¹`, by the identity. -/
def Pair.transportFormsOfDualUnitIso (P : Pair.{u, u, u, u} p D Ω₁ dx₁ d₁) :
    P ≅ (P.transportFormsOfDual p e hd σ hdx hc₂).transportFormsOfDual p e.symm hd' σ.symm hdx'
      hc₁ where
  hom := ⟨LinearMap.id, fun m ↦ by
    rw [Pair.transportFormsOfDual_transportFormsOfDual_nabla]
    exact horizontal_id_of_eq p rfl m⟩
  inv := ⟨LinearMap.id, fun m ↦ by
    rw [Pair.transportFormsOfDual_transportFormsOfDual_nabla]
    exact horizontal_id_of_eq p rfl m⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **Transport along an isomorphism of the one-forms is an equivalence of the categories of
pairs**, with inverse the transport along `e⁻¹`, for any family of coordinates with dual
functionals. -/
def Pair.formsTransportEquivalenceOfDual :
    Pair.{u, u, u, u} p D Ω₁ dx₁ d₁ ≌ Pair.{u, u, u, u} p D Ω₂ dx₂ d₂ :=
  CategoryTheory.Equivalence.mk (Pair.transportFormsOfDualFunctor p e hd σ hdx hc₂)
    (Pair.transportFormsOfDualFunctor p e.symm hd' σ.symm hdx' hc₁)
    (NatIso.ofComponents
      (fun P ↦ Pair.transportFormsOfDualUnitIso p e hd σ hdx hc₂ hd' hdx' hc₁ P)
      fun _ ↦ rfl)
    (NatIso.ofComponents (fun P ↦ (Pair.transportFormsOfDualUnitIso p e.symm hd' σ.symm hdx' hc₁
      (fun x ↦ by rw [LinearEquiv.symm_symm]; exact hd x)
      (fun i ↦ by rw [LinearEquiv.symm_symm, Equiv.symm_symm]; exact hdx i) hc₂ P).symm)
      fun _ ↦ rfl)

/-- The functor of `Crystalline.Pair.formsTransportEquivalenceOfDual` is the transport along
`e`. -/
theorem Pair.formsTransportEquivalenceOfDual_functor :
    (Pair.formsTransportEquivalenceOfDual p e hd σ hdx hc₂ hd' hdx' hc₁).functor =
      Pair.transportFormsOfDualFunctor p e hd σ hdx hc₂ := rfl

end Transport

end Crystalline

end
