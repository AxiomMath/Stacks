module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.Tactic.NoncommRing
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The exterior algebra of a direct sum

For `V = Fin r → R` and `W = Fin s → R`, this file constructs the canonical isomorphism of
graded algebras `⋀(V × W) ≅ ⋀V ⊗̂ ⋀W` onto the Koszul-signed graded tensor product, its
degreewise form `⋀ⁿ(Fin (r + s) → R) ≃ ⊕_{p+q=n} ⋀ᵖ V ⊗ ⋀^q W`, and the computation rules for
these isomorphisms on decomposable elements, together with the graded Leibniz rule and the
naturality of contraction on exterior powers.
-/

open scoped DirectSum

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The linear identification of `Fin (r + s) → R` with the product `(Fin r → R) × (Fin s → R)`,
`u ↦ (u ∘ Fin.castAdd s, u ∘ Fin.natAdd r)`, with inverse `(p, q) ↦ Fin.append p q`. -/
noncomputable def finAppendProdEquiv (r s : ℕ) :
    (Fin (r + s) → R) ≃ₗ[R] ((Fin r → R) × (Fin s → R)) :=
  (LinearEquiv.funCongrLeft R R (finSumFinEquiv (m := r) (n := s))) ≪≫ₗ
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) R R)

/-- The ℕ-graded Koszul-signed tensor product `Λ V ⊗̂ Λ W` of the two exterior
algebras (`V = Fin r → R`, `W = Fin s → R`).  Its degree-`n` part is
`⊕_{p+q=n} ⋀^p V ⊗ ⋀^q W`; multiplication carries the Koszul sign `(-1)^{|y||x'|}`. -/
abbrev gradedTensorAppend (R : Type*) [CommRing R] (r s : ℕ) : Type _ :=
  GradedTensorProduct R (fun p : ℕ => (⋀[R]^p (Fin r → R)))
    (fun q : ℕ => (⋀[R]^q (Fin s → R)))

/-- The universal `R`-linear map `η : V × W → Λ V ⊗̂ Λ W`,
`η(v,w) = ι_V v ⊗ 1 + 1 ⊗ ι_W w` (`includeLeft ∘ ι ∘ fst + includeRight ∘ ι ∘ snd`). -/
noncomputable def etaAppend (r s : ℕ) :
    ((Fin r → R) × (Fin s → R)) →ₗ[R] gradedTensorAppend R r s :=
  (GradedTensorProduct.includeLeft (R := R) _ _).toLinearMap.comp
      ((ExteriorAlgebra.ι R).comp (LinearMap.fst R _ _))
    + (GradedTensorProduct.includeRight (R := R) _ _).toLinearMap.comp
      ((ExteriorAlgebra.ι R).comp (LinearMap.snd R _ _))

/-- `ι v` lies in the degree-one exterior power. -/
private theorem ι_mem_extPow_one (v : M) :
    ExteriorAlgebra.ι R v ∈ (⋀[R]^1 M : Submodule R _) := by
  change ExteriorAlgebra.ι R v ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ 1
  rw [pow_one]; exact LinearMap.mem_range_self _ v

/-- The map `η` squares to zero: `η(a) * η(a) = 0` for every `a ∈ V × W`. -/
theorem etaAppend_sq_zero (r s : ℕ) (a : (Fin r → R) × (Fin s → R)) :
    etaAppend (R := R) r s a * etaAppend (R := R) r s a = 0 := by
  obtain ⟨v, w⟩ := a
  simp only [etaAppend, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  set L := (GradedTensorProduct.includeLeft (R := R)
    (fun p : ℕ => (⋀[R]^p (Fin r → R))) (fun q : ℕ => (⋀[R]^q (Fin s → R))))
      ((ExteriorAlgebra.ι R) v) with hL
  set Rr := (GradedTensorProduct.includeRight (R := R)
    (fun p : ℕ => (⋀[R]^p (Fin r → R))) (fun q : ℕ => (⋀[R]^q (Fin s → R))))
      ((ExteriorAlgebra.ι R) w) with hRr
  have hLL : L * L = 0 := by
    rw [hL, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  have hRR : Rr * Rr = 0 := by
    rw [hRr, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  have hcross : L * Rr + Rr * L = 0 := by
    rw [hL, hRr, GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
    have e1 : (ExteriorAlgebra.ι R v)
        = ((⟨ExteriorAlgebra.ι R v, ι_mem_extPow_one v⟩ : (⋀[R]^1 (Fin r → R)))
            : ExteriorAlgebra R (Fin r → R)) := rfl
    have e2 : (ExteriorAlgebra.ι R w)
        = ((⟨ExteriorAlgebra.ι R w, ι_mem_extPow_one w⟩ : (⋀[R]^1 (Fin s → R)))
            : ExteriorAlgebra R (Fin s → R)) := rfl
    rw [e1, e2, GradedTensorProduct.tmul_one_mul_one_tmul,
      GradedTensorProduct.tmul_coe_mul_coe_tmul]
    simp
  have expand : (L + Rr) * (L + Rr) = (L * L) + (L * Rr + Rr * L) + Rr * Rr := by
    noncomm_ring
  rw [expand, hLL, hRR, hcross]
  simp

/-- The forward `R`-algebra hom `F : Λ(V×W) → Λ V ⊗̂ Λ W`, `F(ι_M(v,w)) = ι_V v ⊗ 1 + 1 ⊗ ι_W w`,
induced by `η` via the universal property of the exterior algebra. -/
noncomputable def exteriorAppend_toTensor (r s : ℕ) :
    ExteriorAlgebra R ((Fin r → R) × (Fin s → R)) →ₐ[R] gradedTensorAppend R r s :=
  ExteriorAlgebra.lift R ⟨etaAppend r s, etaAppend_sq_zero r s⟩

/-- The unital inclusion `jV : V → V × W`, `v ↦ (v,0)`. -/
def jVAppend (r s : ℕ) : (Fin r → R) →ₗ[R] ((Fin r → R) × (Fin s → R)) := LinearMap.inl R _ _
/-- The unital inclusion `jW : W → V × W`, `w ↦ (0,w)`. -/
def jWAppend (r s : ℕ) : (Fin s → R) →ₗ[R] ((Fin r → R) × (Fin s → R)) := LinearMap.inr R _ _

/-- `ExteriorAlgebra.map f` sends `(range ι)^n`, that is `⋀^n`, into `(range ι)^n`. -/
theorem map_mem_extPow_aux {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂] (f : N₁ →ₗ[R] N₂) (n : ℕ) (x : ExteriorAlgebra R N₁)
    (hx : x ∈ (LinearMap.range (ExteriorAlgebra.ι R : N₁ →ₗ[R] _)) ^ n) :
    (ExteriorAlgebra.map f) x ∈ (LinearMap.range (ExteriorAlgebra.ι R : N₂ →ₗ[R] _)) ^ n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [AlgHom.commutes, pow_zero]; exact Submodule.algebraMap_mem r
  | add x y i hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
      rw [map_mul]
      obtain ⟨v, rfl⟩ := hm
      rw [ExteriorAlgebra.map_apply_ι, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

/-- Graded commutativity of the exterior algebra: for `α ∈ (range ι)^i` and `β ∈ (range ι)^j`,
`α * β = (-1)^(j*i) • (β * α)`. -/
theorem exteriorPower_mul_comm_aux {N₁ : Type*} [AddCommGroup N₁] [Module R N₁] :
    ∀ {i j : ℕ} (α : ExteriorAlgebra R N₁),
      α ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ i →
      ∀ (β : ExteriorAlgebra R N₁), β ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ j →
      α * β = ((-1 : ℤˣ) ^ (j * i)) • (β * α) := by
  have single_gen_comm : ∀ (g : ExteriorAlgebra R N₁),
      g ∈ LinearMap.range (ExteriorAlgebra.ι R) →
      ∀ {j : ℕ} (β : ExteriorAlgebra R N₁), β ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ j →
        g * β = ((-1 : ℤˣ) ^ j) • (β * g) := by
    intro g hg j β hβ
    induction hβ using Submodule.pow_induction_on_left' with
    | algebraMap r => rw [pow_zero, one_smul, Algebra.commutes]
    | add x y i hx hy ihx ihy => rw [mul_add, add_mul, smul_add, ihx, ihy]
    | mem_mul m hm i x hx ih =>
        obtain ⟨v, rfl⟩ := hm
        obtain ⟨u, rfl⟩ := hg
        have anti : (ExteriorAlgebra.ι R) u * (ExteriorAlgebra.ι R) v
            = - ((ExteriorAlgebra.ι R) v * (ExteriorAlgebra.ι R) u) := by
          have hsq : (ExteriorAlgebra.ι R (u + v)) * (ExteriorAlgebra.ι R (u + v)) = 0 :=
            ExteriorAlgebra.ι_sq_zero _
          simp only [map_add, mul_add, add_mul, ExteriorAlgebra.ι_sq_zero] at hsq
          linear_combination (norm := noncomm_ring) hsq
        rw [← mul_assoc, anti, neg_mul, mul_assoc, ih, mul_smul_comm, ← mul_assoc, pow_succ,
          mul_smul]
        simp [Units.smul_def]
  intro i j α hα β hβ
  induction hα using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [Nat.mul_zero, pow_zero, one_smul, Algebra.commutes]
  | add x y i hx hy ihx ihy => rw [add_mul, mul_add, smul_add, ihx, ihy]
  | mem_mul m hm i x hx ih =>
      rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc, single_gen_comm m hm β hβ, smul_mul_assoc,
        smul_smul, mul_assoc, ← pow_add, Nat.mul_succ]

/-- Graded commutation of the two functorial embeddings: in `Λ(V×W)`, for `a ∈ ⋀^i V` and
`b ∈ ⋀^j W`, `(Λ jV)(a)·(Λ jW)(b) = (-1)^{ji}·(Λ jW)(b)·(Λ jV)(a)`. -/
theorem embed_commute (r s : ℕ) :
    ∀ ⦃i j : ℕ⦄ (a : (⋀[R]^i (Fin r → R))) (b : (⋀[R]^j (Fin s → R))),
      (ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R)) *
          (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R))
        = ((-1 : ℤˣ) ^ (j * i)) •
            ((ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R)) *
              (ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))) := by
  intro i j a b
  exact exteriorPower_mul_comm_aux _ (map_mem_extPow_aux _ _ _ a.2) _
    (map_mem_extPow_aux _ _ _ b.2)

/-- The backward `R`-algebra hom `G : Λ V ⊗̂ Λ W → Λ(V×W)`, `x ⊗ y ↦ (Λ jV)(x)·(Λ jW)(y)`. -/
noncomputable def tensorAppend_toExterior (r s : ℕ) :
    gradedTensorAppend R r s →ₐ[R] ExteriorAlgebra R ((Fin r → R) × (Fin s → R)) :=
  GradedTensorProduct.lift _ _
    (ExteriorAlgebra.map (jVAppend r s)) (ExteriorAlgebra.map (jWAppend r s))
    (embed_commute r s)

/-- `G ∘ F = id`: `tensorAppend_toExterior` is a left inverse of `exteriorAppend_toTensor`. -/
theorem exteriorAppend_left_inv (r s : ℕ) :
    (tensorAppend_toExterior r s).comp (exteriorAppend_toTensor (R := R) r s)
      = AlgHom.id R _ := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨v, w⟩ := x
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, AlgHom.id_apply]
  rw [exteriorAppend_toTensor, ExteriorAlgebra.lift_ι_apply]
  simp only [etaAppend, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  rw [map_add, GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply,
    tensorAppend_toExterior, GradedTensorProduct.lift_tmul, GradedTensorProduct.lift_tmul]
  simp only [map_one, mul_one, one_mul]
  rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι, jVAppend, jWAppend, ← map_add]
  simp

/-- `F ∘ G = id`: `tensorAppend_toExterior` is a right inverse of `exteriorAppend_toTensor`. -/
theorem exteriorAppend_right_inv (r s : ℕ) :
    (exteriorAppend_toTensor r s).comp (tensorAppend_toExterior (R := R) r s)
      = AlgHom.id R _ := by
  apply GradedTensorProduct.algHom_ext
  · apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.id_apply]
    rw [GradedTensorProduct.includeLeft_apply, tensorAppend_toExterior,
      GradedTensorProduct.lift_tmul]
    simp only [map_one, mul_one]
    rw [ExteriorAlgebra.map_apply_ι, jVAppend, exteriorAppend_toTensor,
      ExteriorAlgebra.lift_ι_apply]
    simp only [etaAppend, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.inl_apply, map_zero]
    rw [GradedTensorProduct.includeLeft_apply]
    simp
  · apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro w
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.id_apply]
    rw [GradedTensorProduct.includeRight_apply, tensorAppend_toExterior,
      GradedTensorProduct.lift_tmul]
    simp only [map_one, one_mul]
    rw [ExteriorAlgebra.map_apply_ι, jWAppend, exteriorAppend_toTensor,
      ExteriorAlgebra.lift_ι_apply]
    simp only [etaAppend, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.inr_apply, map_zero]
    rw [GradedTensorProduct.includeRight_apply]
    simp

/-- The canonical `R`-algebra isomorphism `Λ(V×W) ≅ Λ V ⊗̂ Λ W` onto the Koszul-signed graded
tensor product, with forward map `exteriorAppend_toTensor` and inverse
`tensorAppend_toExterior`. -/
@[sga "6 V 2.2.1" "special case"]
noncomputable def exteriorAppend_algEquiv (r s : ℕ) :
    ExteriorAlgebra R ((Fin r → R) × (Fin s → R)) ≃ₐ[R] gradedTensorAppend R r s :=
  AlgEquiv.ofAlgHom (exteriorAppend_toTensor r s) (tensorAppend_toExterior r s)
    (exteriorAppend_right_inv r s) (exteriorAppend_left_inv r s)

/-- The `R`-linear equivalence `⋀^n M ≃ ⋀^n N` induced by a linear equivalence `M ≃ N`. -/
@[ega "0 4.1.5" "special case"]
noncomputable def exteriorPowerCongr (n : ℕ) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofLinearMap (exteriorPower.map n (e : M →ₗ[R] N))
    (exteriorPower.map n (e.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp)
    (by rw [← exteriorPower.map_comp]; simp)

/-- The coercion of `exteriorPowerCongr n e z` into the exterior algebra is `map e ↑z`. -/
theorem exteriorPowerCongr_coe (n : ℕ) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (z : ⋀[R]^n M) :
    ((exteriorPowerCongr n e z : ⋀[R]^n N) : ExteriorAlgebra R N)
      = ExteriorAlgebra.map (e : M →ₗ[R] N) (z : ExteriorAlgebra R M) := by
  rw [exteriorPowerCongr, LinearEquiv.coe_ofLinearMap, ExtPow.map_coe]

/-- The `R`-linear isomorphism `Λ V ⊗ Λ W ≃ ⨁_{(p,q) : ℕ × ℕ} ⋀^p V ⊗ ⋀^q W` induced by the
grading decompositions of the two exterior algebras. -/
noncomputable def Phi_full (r s : ℕ) :
    (gradedTensorAppend R r s) ≃ₗ[R]
      (⨁ (pq : ℕ × ℕ), TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R))) :=
  (TensorProduct.congr
      (DirectSum.decomposeLinearEquiv (fun p : ℕ => (⋀[R]^p (Fin r → R))))
      (DirectSum.decomposeLinearEquiv (fun q : ℕ => (⋀[R]^q (Fin s → R)))))
    ≪≫ₗ (TensorProduct.directSum R R
      (fun p : ℕ => (⋀[R]^p (Fin r → R))) (fun q : ℕ => (⋀[R]^q (Fin s → R))))

/-- The `R`-linear isomorphism `Λ(V×W) ≃ ⨁_{(p,q) : ℕ × ℕ} ⋀^p V ⊗ ⋀^q W`, the composite of
`exteriorAppend_algEquiv` and `Phi_full`. -/
noncomputable def Psi_full (r s : ℕ) :
    ExteriorAlgebra R ((Fin r → R) × (Fin s → R)) ≃ₗ[R]
      (⨁ (pq : ℕ × ℕ), TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R))) :=
  (exteriorAppend_algEquiv r s).toLinearEquiv ≪≫ₗ Phi_full r s

/-- The projection of the `ℕ × ℕ`-indexed direct sum onto the total-degree-`n` block
`⨁_{p+q=n}`, sending the components with `p + q ≠ n` to zero. -/
noncomputable def blockProj (n : ℕ)
    (X : ℕ × ℕ → Type*) [∀ pq, AddCommGroup (X pq)] [∀ pq, Module R (X pq)] :
    (⨁ (pq : ℕ × ℕ), X pq) →ₗ[R]
      (⨁ (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}), X pq.1) :=
  DirectSum.toModule R _ _ (fun pq =>
    if h : pq.1 + pq.2 = n then
      DirectSum.lof R _ (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => X pq.1) ⟨pq, h⟩
    else 0)

/-- The degree-`n` extraction map `⋀^n(V×W) →ₗ ⨁_{p+q=n} ⋀^p V ⊗ ⋀^q W`: include `⋀^n(V×W)`
into `Λ(V×W)`, apply `Psi_full`, and project onto the `{p+q=n}` block. -/
noncomputable def extPow_fwd (r s n : ℕ) :
    (⋀[R]^n ((Fin r → R) × (Fin s → R)))
      →ₗ[R] DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R))) :=
  (blockProj n (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))).comp
    ((Psi_full r s).toLinearMap.comp
      (Submodule.subtype (⋀[R]^n ((Fin r → R) × (Fin s → R)))))

/-- Inclusion of the total-degree-`n` block back into the global ℕ×ℕ-indexed direct
sum (right inverse to `blockProj`). -/
noncomputable def blockIncl (n : ℕ)
    (X : ℕ × ℕ → Type*) [∀ pq, AddCommGroup (X pq)] [∀ pq, Module R (X pq)] :
    (⨁ (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}), X pq.1) →ₗ[R]
      (⨁ (pq : ℕ × ℕ), X pq) :=
  DirectSum.toModule R _ _
    (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} =>
      (DirectSum.lof R (ℕ × ℕ) X pq.1 : X pq.1 →ₗ[R] (⨁ (pq : ℕ × ℕ), X pq)))

/-- `blockProj ∘ blockIncl = id` on the total-degree-`n` block. -/
theorem blockProj_blockIncl (n : ℕ)
    (X : ℕ × ℕ → Type*) [∀ pq, AddCommGroup (X pq)] [∀ pq, Module R (X pq)] :
    (blockProj (R := R) n X).comp (blockIncl (R := R) n X) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro pq
  apply LinearMap.ext
  intro x
  obtain ⟨⟨p, q⟩, h⟩ := pq
  simp only [LinearMap.comp_apply, blockIncl, blockProj, LinearMap.id_coe, id_eq,
    DirectSum.toModule_lof]
  simp only [h, dite_eq_left]

/-- `blockProj ∘ blockIncl = id`, pointwise. -/
private theorem blockProj_blockIncl_apply (n : ℕ)
    (X : ℕ × ℕ → Type*) [∀ pq, AddCommGroup (X pq)] [∀ pq, Module R (X pq)]
    (z : ⨁ (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}), X pq.1) :
    blockProj (R := R) n X (blockIncl (R := R) n X z) = z :=
  LinearMap.congr_fun (blockProj_blockIncl n X) z

/-- The composite of `TensorProduct.congr` of the two grading decompositions with
`TensorProduct.directSum` sends `↑a ⊗ₜ ↑b`, for `a ∈ ⋀^p V` and `b ∈ ⋀^q W`, to
`lof (p, q) (a ⊗ₜ b)`. -/
theorem Phi_full_congr_directSum (r s p q : ℕ)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (TensorProduct.directSum R R (fun p => (⋀[R]^p (Fin r → R)))
        fun q => (⋀[R]^q (Fin s → R)))
      ((TensorProduct.congr (DirectSum.decomposeLinearEquiv fun p => ⋀[R]^p (Fin r → R))
          (DirectSum.decomposeLinearEquiv fun q => ⋀[R]^q (Fin s → R)))
        ((a : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (b : ExteriorAlgebra R (Fin s → R))))
      = DirectSum.lof R (ℕ × ℕ)
          (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
          (p, q) (a ⊗ₜ[R] b) := by
  rw [TensorProduct.congr_tmul, DirectSum.decomposeLinearEquiv_apply_coe,
    DirectSum.decomposeLinearEquiv_apply_coe, TensorProduct.directSum_lof_tmul_lof]

/-- `Phi_full` sends `↑a ⊗ₜ ↑b` (for `a ∈ ⋀^p V`, `b ∈ ⋀^q W`) to the single
component `lof (p,q) (a ⊗ b)` of the bigraded direct sum. -/
theorem Phi_full_tmul (r s p q : ℕ)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (Phi_full r s)
        ((a : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (b : ExteriorAlgebra R (Fin s → R))
          : gradedTensorAppend R r s)
      = DirectSum.lof R (ℕ × ℕ)
          (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
          (p, q) (a ⊗ₜ[R] b) := by
  rw [Phi_full, LinearEquiv.trans_apply]
  exact Phi_full_congr_directSum r s p q a b

/-- The value of `Psi_full.symm` on a block generator: it is the embedded decomposable
`(map jV ↑a)·(map jW ↑b)`. -/
private theorem psi_symm_lof_tmul_eq_aux (r s n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (Psi_full r s).symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)))
      = (ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
          * (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R)) := by
  have hPhi : (Phi_full r s).symm
      (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)))
      = ((a : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (b : ExteriorAlgebra R (Fin s → R))
          : gradedTensorAppend R r s) := by
    rw [LinearEquiv.symm_apply_eq]
    simp only [blockIncl, DirectSum.toModule_lof]
    rw [Phi_full_tmul]
  rw [Psi_full, LinearEquiv.trans_symm, LinearEquiv.trans_apply, hPhi,
    ← AlgEquiv.toLinearEquiv_symm, AlgEquiv.coe_toLinearEquiv]
  show (tensorAppend_toExterior r s)
      ((a : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (b : ExteriorAlgebra R (Fin s → R))
        : gradedTensorAppend R r s) = _
  rw [tensorAppend_toExterior]
  exact GradedTensorProduct.lift_tmul _ _ _ _ _ _ _

/-- For `p + q = n`, the embedded decomposable `(map jV ↑a)·(map jW ↑b)` lies in `⋀^n(V×W)`. -/
private theorem map_jV_mul_map_jW_mem (r s : ℕ) {n p q : ℕ} (h : p + q = n)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
        * (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R))
      ∈ (⋀[R]^n ((Fin r → R) × (Fin s → R))) := by
  have ha : (ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
      ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ p := map_mem_extPow_aux _ _ _ a.2
  have hb : (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R))
      ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ q := map_mem_extPow_aux _ _ _ b.2
  have := Submodule.mul_mem_mul ha hb
  rwa [← pow_add, h] at this

/-- For `p + q = n`, `a ∈ ⋀^p V` and `b ∈ ⋀^q W`, the preimage under `Psi_full` of the block
generator `lof ⟨(p, q), h⟩ (a ⊗ₜ b)` lies in `⋀^n(V×W)`. -/
theorem Psi_symm_lof_tmul_mem (r s n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (Psi_full r s).symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)))
      ∈ (⋀[R]^n ((Fin r → R) × (Fin s → R))) := by
  rw [psi_symm_lof_tmul_eq_aux]
  exact map_jV_mul_map_jW_mem r s h a b

/-- The preimage in `⋀^n(V×W)` of a single block generator lies in `⋀^n(V×W)`. -/
theorem Psi_symm_blockIncl_mem (r s n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (t : TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R))) :
    (Psi_full r s).symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R))) pq t))
      ∈ (⋀[R]^n ((Fin r → R) × (Fin s → R))) := by
  obtain ⟨⟨p, q⟩, h⟩ := pq
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, map_add]
      exact Submodule.add_mem _ hx hy
  | tmul a b => exact Psi_symm_lof_tmul_mem r s n p q h a b

/-- The degree-`n` extraction map `extPow_fwd` is surjective. -/
theorem extPow_fwd_surjective (r s n : ℕ) :
    Function.Surjective (extPow_fwd (R := R) r s n) := by
  intro y
  classical
  have hmem : ∀ z : DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R))),
      (Psi_full r s).symm (blockIncl (R := R) n
          (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R))) z)
        ∈ (⋀[R]^n ((Fin r → R) × (Fin s → R))) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of pq t => exact Psi_symm_blockIncl_mem r s n pq t
    | add x w hx hw => rw [map_add, map_add]; exact Submodule.add_mem _ hx hw
  refine ⟨⟨(Psi_full r s).symm (blockIncl (R := R) n
      (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R))) y),
      hmem y⟩, ?_⟩
  rw [extPow_fwd]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact blockProj_blockIncl_apply n
    (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R))) y

/-- The bidegree-`k` span inside `gradedTensorAppend R r s`: the submodule generated
by the pure tensors `↑a ⊗ₜ ↑b` with `a ∈ ⋀^p V`, `b ∈ ⋀^q W` and `p + q = k`. -/
noncomputable def bidegSpan (r s k : ℕ) :
    Submodule R (gradedTensorAppend R r s) :=
  Submodule.span R
    {z | ∃ (p q : ℕ) (_ : p + q = k) (a : ⋀[R]^p (Fin r → R)) (b : ⋀[R]^q (Fin s → R)),
      z = (a : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (b : ExteriorAlgebra R (Fin s → R))}

/-- The bidegree-`k` span is the span of the pure tensors `↑a ⊗ₜ ↑b` with `a ∈ ⋀^p V`,
`b ∈ ⋀^q W` and `p + q = k`. -/
theorem bidegSpan_eq (r s k : ℕ) :
    bidegSpan r s k = Submodule.span R
      {z | ∃ (p q : ℕ) (_ : p + q = k) (a : ⋀[R]^p (Fin r → R)) (b : ⋀[R]^q (Fin s → R)),
        z = (a : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (b : ExteriorAlgebra R (Fin s → R))} :=
  rfl

/-- A pure tensor `↑a ⊗ₜ ↑b` with `a ∈ ⋀^p V` and `b ∈ ⋀^q W` lies in the bidegree-`(p + q)`
span. -/
theorem tmul_mem_bidegSpan (r s : ℕ) {p q : ℕ} (a : ⋀[R]^p (Fin r → R))
    (b : ⋀[R]^q (Fin s → R)) :
    ((a : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (b : ExteriorAlgebra R (Fin s → R))
      : gradedTensorAppend R r s) ∈ bidegSpan r s (p + q) := by
  rw [bidegSpan_eq]
  exact Submodule.subset_span ⟨p, q, rfl, a, b, rfl⟩

/-- `Phi_full` sends the bidegree-`k` span into the total-degree-`k` block (range of
`blockIncl`). -/
theorem Phi_full_bidegSpan_le (r s k : ℕ) :
    Submodule.map (Phi_full r s).toLinearMap (bidegSpan r s k) ≤
      LinearMap.range (blockIncl (R := R) k
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))) := by
  rw [bidegSpan_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨z, ⟨p, q, h, a, b, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, LinearEquiv.coe_toLinearMap, Phi_full_tmul]
  refine ⟨DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = k}
      (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
      ⟨(p, q), h⟩ (a ⊗ₜ[R] b), ?_⟩
  simp only [blockIncl, DirectSum.toModule_lof]

/-- `1 ∈ bidegSpan r s 0`. -/
theorem one_mem_bidegSpan (r s : ℕ) :
    (1 : gradedTensorAppend R r s) ∈ bidegSpan r s 0 := by
  have h := tmul_mem_bidegSpan r s (p := 0) (q := 0)
    (1 : ⋀[R]^0 (Fin r → R)) (1 : ⋀[R]^0 (Fin s → R))
  have e1 : ((1 : ⋀[R]^0 (Fin r → R)) : ExteriorAlgebra R (Fin r → R)) = 1 := rfl
  have e2 : ((1 : ⋀[R]^0 (Fin s → R)) : ExteriorAlgebra R (Fin s → R)) = 1 := rfl
  rwa [e1, e2, ← Algebra.TensorProduct.one_def] at h

/-- The bidegree spans are closed under multiplication of the graded tensor product:
`bidegSpan r s p * bidegSpan r s q ⊆ bidegSpan r s (p+q)`. -/
theorem bidegSpan_mul_le (r s p q : ℕ) :
    (bidegSpan r s p : Submodule R (gradedTensorAppend R r s)) * bidegSpan r s q
      ≤ bidegSpan r s (p + q) := by
  apply Submodule.mul_le.mpr
  rw [bidegSpan_eq r s p, bidegSpan_eq r s q]
  intro u hu v hv
  induction hu using Submodule.span_induction with
  | mem u hu =>
      induction hv using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨i, j, rfl, a, b, rfl⟩ := hu
          obtain ⟨i', j', rfl, a', b', rfl⟩ := hv
          show GradedTensorProduct.tmul R (a : ExteriorAlgebra R (Fin r → R))
              (b : ExteriorAlgebra R (Fin s → R))
            * GradedTensorProduct.tmul R (a' : ExteriorAlgebra R (Fin r → R))
              (b' : ExteriorAlgebra R (Fin s → R))
            ∈ bidegSpan r s ((i + j) + (i' + j'))
          rw [GradedTensorProduct.tmul_coe_mul_coe_tmul]
          have maa := SetLike.mul_mem_graded a.2 a'.2
          have mbb := SetLike.mul_mem_graded b.2 b'.2
          set aa : ⋀[R]^(i + i') (Fin r → R) :=
            ⟨(a : ExteriorAlgebra R (Fin r → R)) * (a' : ExteriorAlgebra R (Fin r → R)), maa⟩
            with haa
          set bb : ⋀[R]^(j + j') (Fin s → R) :=
            ⟨(b : ExteriorAlgebra R (Fin s → R)) * (b' : ExteriorAlgebra R (Fin s → R)), mbb⟩
            with hbb
          have hmem : (((aa : ExteriorAlgebra R (Fin r → R))
                ⊗ₜ[R] (bb : ExteriorAlgebra R (Fin s → R)))
              : gradedTensorAppend R r s) ∈ bidegSpan r s ((i + j) + (i' + j')) := by
            have hd := tmul_mem_bidegSpan r s aa bb
            have hdeg : (i + i') + (j + j') = (i + j) + (i' + j') := by omega
            rwa [hdeg] at hd
          have key : ((-1 : ℤˣ) ^ (j * i')) •
              ((((a : ExteriorAlgebra R (Fin r → R)) * (a' : ExteriorAlgebra R (Fin r → R)))
                ⊗ₜ[R] ((b : ExteriorAlgebra R (Fin s → R)) * (b' : ExteriorAlgebra R (Fin s → R))))
                : gradedTensorAppend R r s)
              ∈ bidegSpan r s ((i + j) + (i' + j')) := Submodule.smul_mem _ _ hmem
          rw [show (((a : ExteriorAlgebra R (Fin r → R)) * (a' : ExteriorAlgebra R (Fin r → R)))
                ᵍ⊗ₜ[R] ((b : ExteriorAlgebra R (Fin s → R)) * (b' : ExteriorAlgebra R (Fin s → R)))
                : gradedTensorAppend R r s)
              = (((a : ExteriorAlgebra R (Fin r → R)) * (a' : ExteriorAlgebra R (Fin r → R)))
                ⊗ₜ[R] ((b : ExteriorAlgebra R (Fin s → R)) * (b' : ExteriorAlgebra R (Fin s → R))))
              from rfl]
          exact key
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add v₁ v₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul c v _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add u₁ u₂ _ _ ih₁ ih₂ => rw [add_mul]; exact Submodule.add_mem _ ih₁ ih₂
  | smul c u _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

/-- `etaAppend` lands in the bidegree-`1` span. -/
theorem etaAppend_mem_bidegSpan (r s : ℕ) (vw : (Fin r → R) × (Fin s → R)) :
    etaAppend r s vw ∈ bidegSpan r s 1 := by
  obtain ⟨v, w⟩ := vw
  simp only [etaAppend, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
  apply Submodule.add_mem
  · have h := tmul_mem_bidegSpan r s (p := 1) (q := 0)
      ⟨ExteriorAlgebra.ι R v, ι_mem_extPow_one v⟩ (1 : ⋀[R]^0 (Fin s → R))
    have e2 : ((1 : ⋀[R]^0 (Fin s → R)) : ExteriorAlgebra R (Fin s → R)) = 1 := rfl
    rw [e2] at h
    rw [show ((ExteriorAlgebra.ι R v) ᵍ⊗ₜ[R] (1 : ExteriorAlgebra R (Fin s → R))
          : gradedTensorAppend R r s)
        = ((ExteriorAlgebra.ι R v) ⊗ₜ[R] (1 : ExteriorAlgebra R (Fin s → R))) from rfl]
    exact h
  · have h := tmul_mem_bidegSpan r s (p := 0) (q := 1)
      (1 : ⋀[R]^0 (Fin r → R)) ⟨ExteriorAlgebra.ι R w, ι_mem_extPow_one w⟩
    have e1 : ((1 : ⋀[R]^0 (Fin r → R)) : ExteriorAlgebra R (Fin r → R)) = 1 := rfl
    rw [e1] at h
    rw [show ((1 : ExteriorAlgebra R (Fin r → R)) ᵍ⊗ₜ[R] (ExteriorAlgebra.ι R w)
          : gradedTensorAppend R r s)
        = ((1 : ExteriorAlgebra R (Fin r → R)) ⊗ₜ[R] (ExteriorAlgebra.ι R w)) from rfl]
    exact h

/-- The forward algebra hom `exteriorAppend_toTensor` carries `⋀^k(V×W)` into the
bidegree-`k` span. -/
theorem exteriorAppend_toTensor_mem_bidegSpan (r s : ℕ) :
    ∀ {k : ℕ} (x : ExteriorAlgebra R ((Fin r → R) × (Fin s → R))),
      x ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ k →
        exteriorAppend_toTensor r s x ∈ bidegSpan r s k := by
  intro k x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap c =>
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_bidegSpan r s)
  | add x y i hx hy ihx ihy =>
      rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
      obtain ⟨vw, rfl⟩ := hm
      rw [map_mul]
      have hηmem : exteriorAppend_toTensor r s (ExteriorAlgebra.ι R vw)
          ∈ bidegSpan r s 1 := by
        rw [exteriorAppend_toTensor, ExteriorAlgebra.lift_ι_apply]
        exact etaAppend_mem_bidegSpan r s vw
      have hle := bidegSpan_mul_le (R := R) r s 1 i (Submodule.mul_mem_mul hηmem ih)
      rwa [Nat.add_comm] at hle

/-- The degree-`n` extraction map `extPow_fwd` is injective. -/
theorem extPow_fwd_injective (r s n : ℕ) :
    Function.Injective (extPow_fwd (R := R) r s n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [extPow_fwd] at hx
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at hx
  have hsupp : (Psi_full r s) (x : ExteriorAlgebra R ((Fin r → R) × (Fin s → R)))
      ∈ LinearMap.range (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))) := by
    have halg : exteriorAppend_toTensor r s
        (x : ExteriorAlgebra R ((Fin r → R) × (Fin s → R))) ∈ bidegSpan r s n :=
      exteriorAppend_toTensor_mem_bidegSpan r s _ x.2
    have hmap : (Psi_full r s) (x : ExteriorAlgebra R ((Fin r → R) × (Fin s → R)))
        = (Phi_full r s) (exteriorAppend_toTensor r s
            (x : ExteriorAlgebra R ((Fin r → R) × (Fin s → R)))) := by
      rw [Psi_full, LinearEquiv.trans_apply]
      rfl
    rw [hmap]
    exact Phi_full_bidegSpan_le r s n ⟨_, halg, rfl⟩
  obtain ⟨w, hw⟩ := hsupp
  have hwzero : w = 0 := by
    have hxx : (blockProj (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R))))
        ((Psi_full r s) (x : ExteriorAlgebra R ((Fin r → R) × (Fin s → R)))) = 0 := hx
    rw [← hw] at hxx
    rwa [blockProj_blockIncl_apply] at hxx
  rw [hwzero, map_zero] at hw
  have hxval : (x : ExteriorAlgebra R ((Fin r → R) × (Fin s → R))) = 0 := by
    apply (Psi_full r s).injective
    rw [map_zero, ← hw]
  exact Subtype.ext hxval

/-- The degree-`n` extraction `⋀^n(V×W) ≃ₗ ⨁_{p+q=n} ⋀^p V ⊗ ⋀^q W` of `exteriorAppend_algEquiv`,
as a linear equivalence with forward map `extPow_fwd`. -/
@[sga "5 III 6.9" "6.9.0", sga "6 V 2.2.1" "special case"]
noncomputable def extPow_prod_equiv_directSum (r s : ℕ) (n : ℕ) :
    (⋀[R]^n ((Fin r → R) × (Fin s → R)))
      ≃ₗ[R] DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R))) :=
  LinearEquiv.ofBijective (extPow_fwd r s n)
    ⟨extPow_fwd_injective r s n, extPow_fwd_surjective r s n⟩

/-- For each `n`, the `R`-linear isomorphism
`⋀^n (Fin (r + s) → R) ≃ ⊕_{p+q=n} ⋀^p (Fin r → R) ⊗ ⋀^q (Fin s → R)`: the degree-`n` part of
`exteriorAppend_algEquiv`, transported along `finAppendProdEquiv`. -/
@[sga "5 III 6.9" "6.9.0", sga "6 V 2.2.1" "special case"]
noncomputable def exteriorPower_append_equiv_directSum {r s : ℕ} (n : ℕ) :
    (⋀[R]^n (Fin (r+s) → R))
      ≃ₗ[R] DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
        (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R))) :=
  (exteriorPowerCongr n (finAppendProdEquiv r s)) ≪≫ₗ extPow_prod_equiv_directSum r s n

/-- Graded Leibniz rule for `contractLeft`: if `u ∈ (range ι)^p` then
`contractLeft φ (u * v) = (contractLeft φ u) * v + (-1)^p • (u * contractLeft φ v)`. -/
@[ega "III 1.1.1" "i_f is an antiderivation"]
theorem contractLeft_graded_leibniz {N : Type*} [AddCommGroup N] [Module R N]
    (φ : Module.Dual R N) :
    ∀ (p : ℕ) (u : ExteriorAlgebra R N),
      u ∈ (LinearMap.range (ExteriorAlgebra.ι R : N →ₗ[R] _)) ^ p →
      ∀ (v : ExteriorAlgebra R N),
        CliffordAlgebra.contractLeft φ (u * v)
          = (CliffordAlgebra.contractLeft φ u) * v
            + ((-1 : R)^p) • (u * CliffordAlgebra.contractLeft φ v) := by
  intro p
  induction p with
  | zero =>
      intro u hu v
      rw [pow_zero, Submodule.mem_one] at hu
      obtain ⟨c, rfl⟩ := hu
      have h0 : CliffordAlgebra.contractLeft φ (algebraMap R (ExteriorAlgebra R N) c) = 0 := by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, CliffordAlgebra.contractLeft_one, smul_zero]
      rw [pow_zero, one_smul, h0, zero_mul, zero_add,
        ← Algebra.smul_def, map_smul, ← Algebra.smul_def]
  | succ p ih =>
      intro u hu v
      rw [pow_succ'] at hu
      refine Submodule.mul_induction_on hu ?_ ?_
      · intro g hg u' hu'
        obtain ⟨m, rfl⟩ := hg
        rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, ih u' hu' v,
          CliffordAlgebra.contractLeft_ι_mul, mul_add, sub_mul, smul_mul_assoc, mul_smul_comm,
          ← mul_assoc, pow_succ', neg_one_mul, neg_smul, mul_assoc ((ExteriorAlgebra.ι R) m) u']
        abel
      · intro x y hx hy
        rw [add_mul, map_add, map_add, hx, hy, add_mul, add_mul, smul_add]
        abel

/-- Naturality of `contractLeft` under `ExteriorAlgebra.map`, on power-graded elements:
`map g (contractLeft (φ∘g) x) = contractLeft φ (map g x)`. -/
@[ega "III 1.1.5" "Formula (1.1.5.2)"]
theorem map_contractLeft_pow {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂] (g : N₁ →ₗ[R] N₂) (φ : Module.Dual R N₂) :
    ∀ (p : ℕ) (x : ExteriorAlgebra R N₁),
      x ∈ (LinearMap.range (ExteriorAlgebra.ι R : N₁ →ₗ[R] _)) ^ p →
      ExteriorAlgebra.map g (CliffordAlgebra.contractLeft (φ.comp g) x)
        = CliffordAlgebra.contractLeft φ (ExteriorAlgebra.map g x) := by
  intro p
  induction p with
  | zero =>
      intro x hx
      rw [pow_zero, Submodule.mem_one] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [Algebra.algebraMap_eq_smul_one]
      simp [CliffordAlgebra.contractLeft_one]
  | succ p ih =>
      intro x hx
      rw [pow_succ'] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha y hy
        obtain ⟨m, rfl⟩ := ha
        rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
          ExteriorAlgebra.map_apply_ι, ih y hy,
          map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul]
        simp [LinearMap.comp_apply]
      · intro x y hx hy
        rw [map_add, map_add, map_add, map_add, hx, hy]

/-- The value of `Psi_full.symm` on a block generator: it is the embedded decomposable
`(map jV ↑a)·(map jW ↑b)`. -/
theorem Psi_symm_lof_tmul_eq (r s n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (Psi_full r s).symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)))
      = (ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
          * (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R)) :=
  psi_symm_lof_tmul_eq_aux r s n p q h a b

/-- The forward map `Psi_full` sends the embedded decomposable `(map jV ↑a)·(map jW ↑b)`
to the block generator `blockIncl (lof ⟨(p,q),h⟩ (a⊗ₜb))`. -/
theorem Psi_full_embed (r s n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (Psi_full r s) ((ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
          * (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R)))
      = blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 (Fin r → R)) (⋀[R]^pq.2 (Fin s → R)))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)) := by
  rw [← Psi_symm_lof_tmul_eq r s n p q h a b, LinearEquiv.apply_symm_apply]

/-- The degree-`n` extraction `extPow_fwd` sends the embedded decomposable
`⟨(map jV ↑a)·(map jW ↑b), _⟩` to the block generator `lof ⟨(p,q),h⟩ (a⊗ₜb)`. -/
theorem extPow_fwd_embed (r s n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R)))
    (mem : (ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
        * (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R))
        ∈ (⋀[R]^n ((Fin r → R) × (Fin s → R)))) :
    extPow_fwd (R := R) r s n
        ⟨(ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
          * (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R)), mem⟩
      = DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b) := by
  rw [extPow_fwd]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe]
  rw [Psi_full_embed r s n p q h a b]
  exact blockProj_blockIncl_apply n _ _

/-- `finAppendProdEquiv.symm (x, y) = Fin.append x y`. -/
theorem finAppendProdEquiv_symm_apply (r s : ℕ) (x : Fin r → R) (y : Fin s → R) :
    (finAppendProdEquiv r s).symm (x, y) = Fin.append x y := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [finAppendProdEquiv, LinearEquiv.funCongrLeft, LinearEquiv.sumArrowLequivProdArrow,
      Fin.append_left, Fin.append_right]

/-- The coercion of `(exteriorPower_append_equiv_directSum k).symm` applied to a block
generator `lof ⟨(p,q),h⟩ (a⊗ₜb)` (with `p+q=k`), as an element of the exterior algebra
`ExteriorAlgebra R (Fin (r+s) → R)`: it is the embedded decomposable
`map (e.symm ∘ jV) ↑a · map (e.symm ∘ jW) ↑b`. -/
theorem exteriorPower_append_equiv_directSum_symm_lof_coe (r s k p q : ℕ) (h : p + q = k)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (((exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) k).symm
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = k}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)) : ExteriorAlgebra R (Fin (r + s) → R)))
      = ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jVAppend r s))
          (a : ExteriorAlgebra R (Fin r → R))
        * ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jWAppend r s))
          (b : ExteriorAlgebra R (Fin s → R)) := by
  have hmem := map_jV_mul_map_jW_mem r s h a b
  have hP : (extPow_prod_equiv_directSum r s k).symm
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = k}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R)))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b))
      = ⟨(ExteriorAlgebra.map (jVAppend r s)) (a : ExteriorAlgebra R (Fin r → R))
          * (ExteriorAlgebra.map (jWAppend r s)) (b : ExteriorAlgebra R (Fin s → R)), hmem⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    show _ = extPow_fwd r s k _
    rw [extPow_fwd_embed r s k p q h a b hmem]
  rw [exteriorPower_append_equiv_directSum, LinearEquiv.trans_symm, LinearEquiv.trans_apply, hP,
    exteriorPowerCongr]
  simp only [LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap]
  rw [ExtPow.map_coe, Submodule.coe_mk, map_mul, ← ExteriorAlgebra.map_comp_map,
    ← ExteriorAlgebra.map_comp_map]
  rfl

/-- `e ∘ ιV = jV` where `ιV = e.symm ∘ jV`. -/
theorem finAppendProdEquiv_comp_ιV (r s : ℕ) :
    (finAppendProdEquiv (R := R) r s).toLinearMap.comp
        ((finAppendProdEquiv r s).symm.toLinearMap.comp (jVAppend r s))
      = jVAppend r s :=
  LinearMap.ext fun x => by simp

/-- `e ∘ ιW = jW` where `ιW = e.symm ∘ jW`. -/
theorem finAppendProdEquiv_comp_ιW (r s : ℕ) :
    (finAppendProdEquiv (R := R) r s).toLinearMap.comp
        ((finAppendProdEquiv r s).symm.toLinearMap.comp (jWAppend r s))
      = jWAppend r s :=
  LinearMap.ext fun x => by simp

/-- `map e (map ιV X * map ιW Y) = map jV X * map jW Y`. -/
theorem map_e_embed (r s : ℕ) (X : ExteriorAlgebra R (Fin r → R))
    (Y : ExteriorAlgebra R (Fin s → R)) :
    ExteriorAlgebra.map (finAppendProdEquiv (R := R) r s).toLinearMap
        (ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jVAppend r s)) X
          * ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jWAppend r s)) Y)
      = ExteriorAlgebra.map (jVAppend r s) X * ExteriorAlgebra.map (jWAppend r s) Y := by
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply (ExteriorAlgebra.map _)
    (ExteriorAlgebra.map _) Y, ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map,
    finAppendProdEquiv_comp_ιV, finAppendProdEquiv_comp_ιW]

/-- Contraction of a degree-`0` exterior element vanishes. -/
theorem contractLeft_extPow_zero {N : Type*} [AddCommGroup N] [Module R N]
    (φ : Module.Dual R N) (a : ⋀[R]^0 N) :
    CliffordAlgebra.contractLeft φ (a : ExteriorAlgebra R N) = 0 := by
  have : (a : ExteriorAlgebra R N) ∈ (LinearMap.range (ExteriorAlgebra.ι R : N →ₗ[R] _)) ^ 0 := a.2
  rw [pow_zero, Submodule.mem_one] at this
  obtain ⟨c, hc⟩ := this
  rw [← hc, Algebra.algebraMap_eq_smul_one, map_smul, CliffordAlgebra.contractLeft_one, smul_zero]
