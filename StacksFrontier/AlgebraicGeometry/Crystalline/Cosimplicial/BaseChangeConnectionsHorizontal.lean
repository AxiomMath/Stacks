module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnections

/-!
# Compatibility of the base-change connections with the cosimplicial direction

`Crystalline.CosimplicialCompletedModule.baseChangeConnection` puts on every `M(b)` the
connection obtained from a connection `∇` on `M(0)` by base change along the coprojection
`σ_b : ⦋0⦌ ⟶ ⦋b⦌` onto the vertex `0`.  For these to be the connections of a double complex
(the field `nabla_tensorMap` of `Crystalline.CosimplicialCompletedPair`) they must commute with
**every** transition map `M(m) ⟶ M(n)`, also those of maps `⦋m⦌ ⟶ ⦋n⦌` that move the vertex `0`.

They do so as soon as the transition `M(0) ⟶ M(1)` of the coface `δ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` is
horizontal, which is the horizontality of the stratification of the crystal
[Stacks, Lemma 60.17.3, Tag 07JG].

## Main results

* `Crystalline.eq_zero_of_baseChangeInclusion` — a semilinear additive map out of a completed
  base change into a `p`-adic completion which kills every `1 ⊗ m` is zero.
* `Crystalline.CosimplicialCompletedModule.horizontalDefect_smul` — the horizontality defect
  `y ↦ ∇_n (M(φ) y) - M(φ)_* (∇_m y)` of a transition map is semilinear.
* `Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_coprojection` — the
  coprojections are horizontal.
* `Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_of_horizontal` — **every
  transition is horizontal**, given that the coface `δ` is.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Simplicial
open scoped TensorProduct Pointwise

namespace Crystalline

open DividedPowers

/-- **A semilinear map out of a completed base change is determined by the image of the
module.**  Let `g` be an additive map from `(D' ⊗_D M)^∧` into a `p`-adic completion over `R`
which is semilinear over a ring map `f : D' → R` and kills every `1 ⊗ m`.  Then `g = 0`. -/
theorem eq_zero_of_baseChangeInclusion (p : ℕ) {D : Type*} [CommRing D] {D' : Type*}
    [CommRing D'] [Algebra D D'] {M : Type*} [AddCommGroup M] [Module D M] {R : Type*}
    [CommRing R] (f : D' →+* R) {N : Type*} [AddCommGroup N] [Module R N]
    (g : CompletedConnection.baseChangeCarrier p D D' M →+ AdicCompletion (pAdicIdeal (A := R) p) N)
    (hg : ∀ (c : D') (x : CompletedConnection.baseChangeCarrier p D D' M), g (c • x) = f c • g x)
    (h0 : ∀ m : M, g (CompletedConnection.baseChangeInclusion p D D' M m) = 0)
    (x : CompletedConnection.baseChangeCarrier p D D' M) : g x = 0 := by
  have hof : ∀ t : D' ⊗[D] M, g (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) t) = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c m => rw [CompletedConnection.of_tmul_eq_smul_inclusion, hg, h0, smul_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  refine AdicCompletion.ext fun k => ?_
  obtain ⟨t, ht⟩ := Submodule.mkQ_surjective
    ((pAdicIdeal (A := D') p) ^ k • (⊤ : Submodule D' (D' ⊗[D] M))) (x.val k)
  have hmem : x - AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) t ∈
      (pAdicIdeal (A := D') p) ^ k •
        (⊤ : Submodule D' (CompletedConnection.baseChangeCarrier p D D' M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (CompletedConnection.pAdicIdeal_fg p D'),
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact ht.symm
  have hmem' : x - AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) t ∈
      ((p : D') ^ k) • (⊤ : Submodule D' (CompletedConnection.baseChangeCarrier p D D' M)) := by
    rwa [← Submodule.ideal_span_singleton_smul, ← Ideal.span_singleton_pow]
  obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem'
  have hx : x = AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) t +
      ((p : D') ^ k) • z := by
    rw [hz]
    abel
  rw [hx, map_add, hof, zero_add, hg, map_pow, map_natCast, AdicCompletion.val_zero_apply,
    AdicCompletion.val_smul_apply]
  refine (Submodule.Quotient.mk_surjective _ ((g z).val k)).elim fun w hw => ?_
  rw [← hw, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k)
    Submodule.mem_top

/-- **The values of a base-changed connection, read through an identification of the base
change**, are the completion of `m ⊗ ω ↦ f m ⊗ ψ ω`, where `f m = β (1 ⊗ m)`. -/
theorem isoValuesFwd_baseChangeValues (p : ℕ) {D : Type u} [CommRing D] {D' : Type u}
    [CommRing D'] [Algebra D D'] {M : Type u} [AddCommGroup M] [Module D M] {M' : Type u}
    [AddCommGroup M'] [Module D' M']
    (β : CompletedConnection.baseChangeCarrier p D D' M ≃ₗ[D'] M')
    {Om : Type u} [AddCommGroup Om] [Module D Om] {Om' : Type u} [AddCommGroup Om']
    [Module D' Om'] (ψ : Om →ₛₗ[algebraMap D D'] Om') (f : M →ₛₗ[algebraMap D D'] M')
    (hf : ∀ m, f m = β (CompletedConnection.baseChangeInclusion p D D' M m))
    (z : CompletedTensor p D Om M) :
    CompletedDeRham.isoValuesFwd p (RingEquiv.refl D') β.toLinearMap
        (fun _ : ℕ => (LinearMap.id : Om' →ₗ[D'] Om')) 1
        (CompletedConnection.baseChangeValues p D D' M Om Om' ψ z) =
      adicCompletionMapₛₗ (TensorProduct.map f ψ) (map_pAdicIdeal_le p (algebraMap D D')) z := by
  symm
  refine adicCompletionMapₛₗ_comp_apply
    (CompletedConnection.baseChangeTensor p D D' M Om Om' ψ)
    (TensorProduct.map (β.toLinearMap : _ →ₛₗ[(RingEquiv.refl D' : D' →+* D')] M')
      (LinearMap.id : Om' →ₗ[D'] Om'))
    (TensorProduct.map f ψ) _ _ _ (fun y => ?_) z
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x ω =>
    show f x ⊗ₜ[D'] ψ ω = β (CompletedConnection.baseChangeInclusion p D D' M x) ⊗ₜ[D'] ψ ω
    rw [hf]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, v, v} E p)
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)

include hbeta in
/-- **The coprojections are horizontal for the base-change connections**: the transition
`M(0) ⟶ M(b)` of the coprojection `σ_b` carries `∇` to `∇_b`. -/
theorem baseChangeConnection_map_coprojection (b : ℕ) (m : V.carrier 0) :
    V.baseChangeConnection nabla beta b (V.map (CosimplicialDPAlgebra.coprojection b) m) =
      V.tensorMap (CosimplicialDPAlgebra.coprojection b) 1 (nabla m) := by
  let := E.coprojectionAlgebra p b
  have h1 : ∀ x : V.carrier 0, V.map (CosimplicialDPAlgebra.coprojection b) x =
      beta b (CompletedConnection.baseChangeInclusion p (E.completedRing p 0)
        (E.completedRing p b) (V.carrier 0) x) := fun x => by
    rw [CompletedConnection.baseChangeInclusion_apply, hbeta, one_smul]
  rw [h1 m, baseChangeConnection_apply, CosimplicialDPAlgebra.coprojectionConnection,
    CompletedConnection.baseChange_inclusion]
  exact isoValuesFwd_baseChangeValues p (beta b) (E.coprojectionFormsMap p b 1)
    (V.map (CosimplicialDPAlgebra.coprojection b))
    h1 (z := nabla m)

include hbeta in
/-- **In degree zero the base-change connection is the given connection.** -/
theorem baseChangeConnection_zero (y : V.carrier 0) :
    V.baseChangeConnection nabla beta 0 y = nabla y := by
  have h0 : CosimplicialDPAlgebra.coprojection 0 = 𝟙 (⦋0⦌ : SimplexCategory) :=
    SimplexCategory.Hom.ext_zero_left _ _
  have := V.baseChangeConnection_map_coprojection nabla beta hbeta 0 y
  rwa [h0, V.map_id_apply, V.tensorMap_id] at this

/-- **The horizontality defect of a transition map**:
`y ↦ ∇_n (M(φ) y) - M(φ)_* (∇_m y)`, for the base-change connections. -/
def horizontalDefect {m n : SimplexCategory} (φ : m ⟶ n) :
    V.carrier m.len →+ V.obj 1 n.len :=
  AddMonoidHom.mk' (fun y => V.baseChangeConnection nabla beta n.len (V.map φ y) -
      V.tensorMap φ 1 (V.baseChangeConnection nabla beta m.len y))
    (fun y z => by
      rw [map_add, CompletedConnection.map_add, CompletedConnection.map_add, map_add]
      abel)

/-- The horizontality defect of `φ` at `y` is `∇_n (M(φ) y) - M(φ)_* (∇_m y)`. -/
theorem horizontalDefect_apply {m n : SimplexCategory} (φ : m ⟶ n) (y : V.carrier m.len) :
    V.horizontalDefect nabla beta φ y = V.baseChangeConnection nabla beta n.len (V.map φ y) -
      V.tensorMap φ 1 (V.baseChangeConnection nabla beta m.len y) := rfl

/-- **The horizontality defect is semilinear** over the transition `D(m) ⟶ D(n)` of the completed
rings. -/
theorem horizontalDefect_smul {m n : SimplexCategory} (φ : m ⟶ n) (c : E.completedRing p m.len)
    (y : V.carrier m.len) :
    V.horizontalDefect nabla beta φ (c • y) =
      E.completedRingMap p φ c • V.horizontalDefect nabla beta φ y := by
  rw [horizontalDefect_apply, horizontalDefect_apply, (V.map φ).map_smulₛₗ,
    CompletedConnection.leibniz, CompletedConnection.leibniz, (V.tensorMap φ 1).map_add,
    (V.tensorMap φ 1).map_smulₛₗ, V.tensorMap_of_tmul, E.formsMap_differential,
    add_sub_add_right_eq_sub]
  exact (smul_sub _ _ _).symm

include hbeta in
/-- **A transition map is horizontal as soon as it is horizontal on the image of `M(0)`**: if
`M(σ_m ≫ φ)` carries `∇` to `∇_n`, then `M(φ)` carries `∇_m` to `∇_n`. -/
theorem baseChangeConnection_map_of_coprojection {m n : SimplexCategory} (φ : m ⟶ n)
    (h : ∀ x : V.carrier 0,
      V.baseChangeConnection nabla beta n.len
          (V.map (CosimplicialDPAlgebra.coprojection m.len ≫ φ) x) =
        V.tensorMap (CosimplicialDPAlgebra.coprojection m.len ≫ φ) 1 (nabla x))
    (y : V.carrier m.len) :
    V.baseChangeConnection nabla beta n.len (V.map φ y) =
      V.tensorMap φ 1 (V.baseChangeConnection nabla beta m.len y) := by
  let := E.coprojectionAlgebra p m.len
  rw [← sub_eq_zero, ← horizontalDefect_apply, ← (beta m.len).apply_symm_apply y]
  refine eq_zero_of_baseChangeInclusion p (E.completedRingMap p φ)
    ((V.horizontalDefect nabla beta φ).comp (beta m.len).toLinearMap.toAddMonoidHom)
    (fun c x => ?_) (fun x => ?_) ((beta m.len).symm y)
  · show V.horizontalDefect nabla beta φ (beta m.len (c • x)) = _
    rw [map_smul, horizontalDefect_smul]
    rfl
  · show V.horizontalDefect nabla beta φ (beta m.len
      (CompletedConnection.baseChangeInclusion p _ _ _ x)) = 0
    rw [CompletedConnection.baseChangeInclusion_apply, hbeta, one_smul, horizontalDefect_apply,
      ← V.map_comp_apply, h, baseChangeConnection_map_coprojection V nabla beta hbeta,
      V.tensorMap_comp, sub_self]

include hbeta in
/-- **Every transition map fixing the vertex `0` is horizontal.** -/
theorem baseChangeConnection_map_of_fix_zero {m n : SimplexCategory} (φ : m ⟶ n)
    (hφ : φ.toOrderHom 0 = 0) (y : V.carrier m.len) :
    V.baseChangeConnection nabla beta n.len (V.map φ y) =
      V.tensorMap φ 1 (V.baseChangeConnection nabla beta m.len y) := by
  have he : CosimplicialDPAlgebra.coprojection m.len ≫ φ =
      CosimplicialDPAlgebra.coprojection n.len := by
    rw [CosimplicialDPAlgebra.coprojection, SimplexCategory.const_comp]
    exact congrArg _ hφ
  refine V.baseChangeConnection_map_of_coprojection nabla beta hbeta φ (fun x => ?_) y
  rw [he]
  exact V.baseChangeConnection_map_coprojection nabla beta hbeta n.len x

include hbeta in
/-- **Every transition map is horizontal, given that the coface `δ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` is.** -/
theorem baseChangeConnection_map_of_horizontal
    (hδ : ∀ x : V.carrier 0,
      V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
        V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
    {m n : SimplexCategory} (φ : m ⟶ n) (y : V.carrier m.len) :
    V.baseChangeConnection nabla beta n.len (V.map φ y) =
      V.tensorMap φ 1 (V.baseChangeConnection nabla beta m.len y) := by
  refine V.baseChangeConnection_map_of_coprojection nabla beta hbeta φ (fun x => ?_) y
  set j : Fin (n.len + 1) := φ.toOrderHom 0
  have he : CosimplicialDPAlgebra.coprojection m.len ≫ φ =
      SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 ≫
        SimplexCategory.mkOfLe (n := n.len) 0 j (Fin.zero_le j) := by
    rw [CosimplicialDPAlgebra.coprojection, SimplexCategory.const_comp,
      SimplexCategory.const_comp]
    rfl
  rw [he, V.map_comp_apply, V.tensorMap_comp,
    V.baseChangeConnection_map_of_fix_zero nabla beta hbeta _ rfl, hδ]

end CosimplicialCompletedModule

end Crystalline

end
