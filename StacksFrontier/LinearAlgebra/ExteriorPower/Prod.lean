module

public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exterior algebra and the exterior powers of a direct sum

For modules `M` and `N` over a commutative ring `R`, the exterior algebra `Λ(M × N)` is
isomorphic as an algebra to the Koszul-signed graded tensor product `Λ M ⊗̂ Λ N`, and in degree
`n` this gives `⋀ⁿ (M × N) ≃ ⨁_{p + q = n} ⋀ᵖ M ⊗ ⋀^q N`.

## Main definitions

* `ExteriorAlgebra.prodAlgEquiv`: the `R`-algebra isomorphism `Λ(M × N) ≅ Λ M ⊗̂ Λ N`.
* `exteriorPower.prodEquivDirectSum`: the `R`-linear isomorphism
  `⋀ⁿ (M × N) ≃ ⨁_{p + q = n} ⋀ᵖ M ⊗ ⋀^q N`.
-/

@[expose] public section

open scoped DirectSum TensorProduct

namespace ExteriorAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- The ℕ-graded Koszul-signed tensor product `Λ M ⊗̂ Λ N` of two exterior algebras.  Its
degree-`n` part is `⨁_{p+q=n} ⋀ᵖ M ⊗ ⋀^q N`, and multiplication carries the Koszul sign
`(-1)^{|y||x'|}`. -/
abbrev gradedTensorProd (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (N : Type*) [AddCommGroup N] [Module R N] : Type _ :=
  GradedTensorProduct R (fun p : ℕ => (⋀[R]^p M)) (fun q : ℕ => (⋀[R]^q N))

/-- The `R`-linear map `η : M × N → Λ M ⊗̂ Λ N`, `η (m, n) = ι m ⊗ 1 + 1 ⊗ ι n`. -/
noncomputable def prodEta : (M × N) →ₗ[R] gradedTensorProd R M N :=
  (GradedTensorProduct.includeLeft (R := R) _ _).toLinearMap.comp
      ((ExteriorAlgebra.ι R).comp (LinearMap.fst R M N))
    + (GradedTensorProduct.includeRight (R := R) _ _).toLinearMap.comp
      ((ExteriorAlgebra.ι R).comp (LinearMap.snd R M N))

/-- `ι v` lies in the degree-one exterior power `⋀¹ M`. -/
private theorem ι_mem_extPow_one (v : M) : ExteriorAlgebra.ι R v ∈ (⋀[R]^1 M : Submodule R _) := by
  change ExteriorAlgebra.ι R v ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ 1
  rw [pow_one]; exact LinearMap.mem_range_self _ v

/-- The product of an element of `⋀ⁱ M` and an element of `⋀ʲ M` lies in `⋀ⁱ⁺ʲ M`. -/
private theorem mul_mem_extPow {i j : ℕ} {x y : ExteriorAlgebra R M}
    (hx : x ∈ (⋀[R]^i M : Submodule R _)) (hy : y ∈ (⋀[R]^j M : Submodule R _)) :
    x * y ∈ (⋀[R]^(i + j) M : Submodule R _) := by
  rw [show (⋀[R]^(i + j) M : Submodule R _) = (LinearMap.range (ExteriorAlgebra.ι R)) ^ (i + j)
    from rfl, pow_add]
  exact Submodule.mul_mem_mul hx hy

/-- The map `η` squares to zero: `η a * η a = 0` for every `a : M × N`. -/
theorem prodEta_sq_zero (a : M × N) :
    prodEta (R := R) a * prodEta (R := R) a = 0 := by
  obtain ⟨v, w⟩ := a
  simp only [prodEta, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  set L := (GradedTensorProduct.includeLeft (R := R)
    (fun p : ℕ => (⋀[R]^p M)) (fun q : ℕ => (⋀[R]^q N))) ((ExteriorAlgebra.ι R) v) with hL
  set Rr := (GradedTensorProduct.includeRight (R := R)
    (fun p : ℕ => (⋀[R]^p M)) (fun q : ℕ => (⋀[R]^q N))) ((ExteriorAlgebra.ι R) w) with hRr
  have hLL : L * L = 0 := by
    rw [hL, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  have hRR : Rr * Rr = 0 := by
    rw [hRr, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  have hcross : L * Rr + Rr * L = 0 := by
    rw [hL, hRr, GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
    have e1 : (ExteriorAlgebra.ι R v)
        = ((⟨ExteriorAlgebra.ι R v, ι_mem_extPow_one v⟩ : (⋀[R]^1 M)) : ExteriorAlgebra R M) := rfl
    have e2 : (ExteriorAlgebra.ι R w)
        = ((⟨ExteriorAlgebra.ι R w, ι_mem_extPow_one w⟩ : (⋀[R]^1 N)) : ExteriorAlgebra R N) := rfl
    rw [e1, e2, GradedTensorProduct.tmul_one_mul_one_tmul,
      GradedTensorProduct.tmul_coe_mul_coe_tmul]
    simp
  have expand : (L + Rr) * (L + Rr) = (L * L) + (L * Rr + Rr * L) + Rr * Rr := by
    noncomm_ring
  rw [expand, hLL, hRR, hcross]
  simp

/-- The forward `R`-algebra hom `Λ(M × N) → Λ M ⊗̂ Λ N` determined by
`ι (m, n) ↦ ι m ⊗ 1 + 1 ⊗ ι n`. -/
noncomputable def prodToGradedTensorProd :
    ExteriorAlgebra R (M × N) →ₐ[R] gradedTensorProd R M N :=
  ExteriorAlgebra.lift R ⟨prodEta, prodEta_sq_zero⟩

/-- Graded commutation of the two functorial embeddings `Λ M → Λ(M × N)` and `Λ N → Λ(M × N)`:
for `a ∈ ⋀ⁱ M` and `b ∈ ⋀ʲ N`, `(Λ inl) a * (Λ inr) b = (-1)^{ji} * (Λ inr) b * (Λ inl) a`. -/
theorem map_inl_mul_map_inr_comm :
    ∀ ⦃i j : ℕ⦄ (a : (⋀[R]^i M)) (b : (⋀[R]^j N)),
      (ExteriorAlgebra.map (LinearMap.inl R M N)) (a : ExteriorAlgebra R M) *
          (ExteriorAlgebra.map (LinearMap.inr R M N)) (b : ExteriorAlgebra R N)
        = ((-1 : ℤˣ) ^ (j * i)) •
            ((ExteriorAlgebra.map (LinearMap.inr R M N)) (b : ExteriorAlgebra R N) *
              (ExteriorAlgebra.map (LinearMap.inl R M N)) (a : ExteriorAlgebra R M)) := by
  intro i j a b
  exact exteriorPower_mul_comm_aux _
    (map_mem_extPow_aux (R := R) (N₂ := M × N) (LinearMap.inl R M N) i _ a.2) _
    (map_mem_extPow_aux (R := R) (N₂ := M × N) (LinearMap.inr R M N) j _ b.2)

/-- The backward `R`-algebra hom `Λ M ⊗̂ Λ N → Λ(M × N)`,
`x ⊗ y ↦ (Λ inl) x * (Λ inr) y`. -/
noncomputable def gradedTensorProdToProd :
    gradedTensorProd R M N →ₐ[R] ExteriorAlgebra R (M × N) :=
  GradedTensorProduct.lift _ _
    (ExteriorAlgebra.map (LinearMap.inl R M N)) (ExteriorAlgebra.map (LinearMap.inr R M N))
    map_inl_mul_map_inr_comm

/-- `gradedTensorProdToProd` is a left inverse of `prodToGradedTensorProd`. -/
theorem gradedTensorProdToProd_comp_prodToGradedTensorProd :
    (gradedTensorProdToProd (R := R) (M := M) (N := N)).comp prodToGradedTensorProd
      = AlgHom.id R _ := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨v, w⟩ := x
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, AlgHom.id_apply]
  rw [prodToGradedTensorProd, ExteriorAlgebra.lift_ι_apply]
  simp only [prodEta, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  rw [map_add, GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply,
    gradedTensorProdToProd, GradedTensorProduct.lift_tmul, GradedTensorProduct.lift_tmul]
  simp only [map_one, mul_one, one_mul]
  rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι, ← map_add]
  simp

/-- `gradedTensorProdToProd` is a right inverse of `prodToGradedTensorProd`. -/
theorem prodToGradedTensorProd_comp_gradedTensorProdToProd :
    (prodToGradedTensorProd (R := R) (M := M) (N := N)).comp gradedTensorProdToProd
      = AlgHom.id R _ := by
  apply GradedTensorProduct.algHom_ext
  · apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.id_apply]
    rw [GradedTensorProduct.includeLeft_apply, gradedTensorProdToProd,
      GradedTensorProduct.lift_tmul]
    simp only [map_one, mul_one]
    rw [ExteriorAlgebra.map_apply_ι, prodToGradedTensorProd, ExteriorAlgebra.lift_ι_apply]
    simp only [prodEta, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.inl_apply, map_zero]
    rw [GradedTensorProduct.includeLeft_apply]
    simp
  · apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro w
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.id_apply]
    rw [GradedTensorProduct.includeRight_apply, gradedTensorProdToProd,
      GradedTensorProduct.lift_tmul]
    simp only [map_one, one_mul]
    rw [ExteriorAlgebra.map_apply_ι, prodToGradedTensorProd, ExteriorAlgebra.lift_ι_apply]
    simp only [prodEta, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.inr_apply, map_zero]
    rw [GradedTensorProduct.includeRight_apply]
    simp

/-- **The exterior algebra of a direct sum.** The canonical `R`-algebra isomorphism
`Λ(M × N) ≅ Λ M ⊗̂ Λ N` onto the Koszul-signed graded tensor product. -/
noncomputable def prodAlgEquiv :
    ExteriorAlgebra R (M × N) ≃ₐ[R] gradedTensorProd R M N :=
  AlgEquiv.ofAlgHom prodToGradedTensorProd gradedTensorProdToProd
    prodToGradedTensorProd_comp_gradedTensorProdToProd
    gradedTensorProdToProd_comp_prodToGradedTensorProd

/-- `prodAlgEquiv.symm` carries a pure tensor to the product of the two embedded factors. -/
theorem prodAlgEquiv_symm_tmul (x : ExteriorAlgebra R M) (y : ExteriorAlgebra R N) :
    (prodAlgEquiv (R := R) (M := M) (N := N)).symm
        (GradedTensorProduct.tmul R x y : gradedTensorProd R M N)
      = (ExteriorAlgebra.map (LinearMap.inl R M N)) x
          * (ExteriorAlgebra.map (LinearMap.inr R M N)) y := by
  change gradedTensorProdToProd (GradedTensorProduct.tmul R x y : gradedTensorProd R M N) = _
  rw [gradedTensorProdToProd]
  exact GradedTensorProduct.lift_tmul _ _ _ _ _ _ _

end ExteriorAlgebra

namespace exteriorPower

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- The `R`-linear isomorphism `Λ M ⊗̂ Λ N ≃ ⨁_{(p,q) : ℕ × ℕ} ⋀ᵖ M ⊗ ⋀^q N` induced by the
grading decompositions of the two exterior algebras. -/
noncomputable def gradedTensorProdDecomposition :
    ExteriorAlgebra.gradedTensorProd R M N ≃ₗ[R]
      (⨁ (pq : ℕ × ℕ), TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)) :=
  (GradedTensorProduct.of R (fun p : ℕ => (⋀[R]^p M)) (fun q : ℕ => (⋀[R]^q N))).symm ≪≫ₗ
    (TensorProduct.congr
        (DirectSum.decomposeLinearEquiv (fun p : ℕ => (⋀[R]^p M)))
        (DirectSum.decomposeLinearEquiv (fun q : ℕ => (⋀[R]^q N))) ≪≫ₗ
      TensorProduct.directSum R R (fun p : ℕ => (⋀[R]^p M)) (fun q : ℕ => (⋀[R]^q N)))

/-- `gradedTensorProdDecomposition` sends the pure tensor `↑a ⊗ ↑b`, for `a ∈ ⋀ᵖ M` and
`b ∈ ⋀^q N`, to the single component `lof (p, q) (a ⊗ b)`. -/
theorem gradedTensorProdDecomposition_tmul (p q : ℕ) (a : (⋀[R]^p M)) (b : (⋀[R]^q N)) :
    gradedTensorProdDecomposition
        (GradedTensorProduct.tmul R (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N)
          : ExteriorAlgebra.gradedTensorProd R M N)
      = DirectSum.lof R (ℕ × ℕ)
          (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)) (p, q) (a ⊗ₜ[R] b) := by
  rw [gradedTensorProdDecomposition, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [show (GradedTensorProduct.of R (fun p : ℕ => (⋀[R]^p M))
        (fun q : ℕ => (⋀[R]^q N))).symm
      (GradedTensorProduct.tmul R (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N))
      = (a : ExteriorAlgebra R M) ⊗ₜ[R] (b : ExteriorAlgebra R N) from rfl]
  rw [TensorProduct.congr_tmul, DirectSum.decomposeLinearEquiv_apply_coe,
    DirectSum.decomposeLinearEquiv_apply_coe, TensorProduct.directSum_lof_tmul_lof]

/-- The `R`-linear isomorphism `Λ(M × N) ≃ ⨁_{(p,q) : ℕ × ℕ} ⋀ᵖ M ⊗ ⋀^q N`, the composite of
`ExteriorAlgebra.prodAlgEquiv` with `gradedTensorProdDecomposition`. -/
noncomputable def prodDecomposition :
    ExteriorAlgebra R (M × N) ≃ₗ[R]
      (⨁ (pq : ℕ × ℕ), TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)) :=
  (ExteriorAlgebra.prodAlgEquiv (R := R) (M := M) (N := N)).toLinearEquiv ≪≫ₗ
    gradedTensorProdDecomposition

/-- The degree-`n` extraction map `⋀ⁿ (M × N) →ₗ ⨁_{p+q=n} ⋀ᵖ M ⊗ ⋀^q N`: include `⋀ⁿ (M × N)`
into `Λ(M × N)`, apply `prodDecomposition`, and project onto the `{p + q = n}` block. -/
noncomputable def prodToDirectSum (n : ℕ) :
    (⋀[R]^n (M × N)) →ₗ[R] DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) :=
  (blockProj n (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))).comp
    (prodDecomposition.toLinearMap.comp (Submodule.subtype (⋀[R]^n (M × N))))

/-- For `p + q = n`, `a ∈ ⋀ᵖ M` and `b ∈ ⋀^q N`, the preimage under `prodDecomposition` of the
block generator `lof ⟨(p, q), h⟩ (a ⊗ b)` is the product `(Λ inl) ↑a * (Λ inr) ↑b` of the two
embedded factors. -/
theorem prodDecomposition_symm_lof_tmul (n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p M)) (b : (⋀[R]^q N)) :
    prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)))
      = (ExteriorAlgebra.map (LinearMap.inl R M N)) (a : ExteriorAlgebra R M)
          * (ExteriorAlgebra.map (LinearMap.inr R M N)) (b : ExteriorAlgebra R N) := by
  have hPhi : (gradedTensorProdDecomposition (R := R) (M := M) (N := N)).symm
      (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)))
      = (GradedTensorProduct.tmul R (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N)
          : ExteriorAlgebra.gradedTensorProd R M N) := by
    rw [LinearEquiv.symm_apply_eq]
    simp only [blockIncl, DirectSum.toModule_lof]
    rw [gradedTensorProdDecomposition_tmul]
  rw [prodDecomposition, LinearEquiv.trans_symm, LinearEquiv.trans_apply, hPhi,
    ← AlgEquiv.toLinearEquiv_symm, AlgEquiv.coe_toLinearEquiv]
  exact ExteriorAlgebra.prodAlgEquiv_symm_tmul _ _

/-- For `p + q = n`, `a ∈ ⋀ᵖ M` and `b ∈ ⋀^q N`, the preimage under `prodDecomposition` of the
block generator `lof ⟨(p, q), h⟩ (a ⊗ b)` lies in `⋀ⁿ (M × N)`. -/
theorem prodDecomposition_symm_lof_tmul_mem (n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p M)) (b : (⋀[R]^q N)) :
    prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b)))
      ∈ (⋀[R]^n (M × N)) := by
  rw [prodDecomposition_symm_lof_tmul]
  subst h
  exact ExteriorAlgebra.mul_mem_extPow
    (map_mem_extPow_aux (R := R) (N₂ := M × N) (LinearMap.inl R M N) p _ a.2)
    (map_mem_extPow_aux (R := R) (N₂ := M × N) (LinearMap.inr R M N) q _ b.2)

/-- The preimage under `prodDecomposition` of a single block generator lies in `⋀ⁿ (M × N)`. -/
theorem prodDecomposition_symm_blockIncl_mem (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (t : TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) :
    prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) pq t))
      ∈ (⋀[R]^n (M × N)) := by
  obtain ⟨⟨p, q⟩, h⟩ := pq
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [map_add, map_add, map_add]
      exact Submodule.add_mem _ hx hy
  | tmul a b => exact prodDecomposition_symm_lof_tmul_mem n p q h a b

/-- `prodToDirectSum` maps the preimage of a block element (when in `⋀ⁿ (M × N)`) back to it. -/
private theorem prodToDirectSum_symm_blockIncl (n : ℕ)
    (y : DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)))
    (hy : prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)) y) ∈ (⋀[R]^n (M × N))) :
    prodToDirectSum (R := R) (M := M) (N := N) n
      ⟨prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)) y), hy⟩ = y := by
  rw [prodToDirectSum]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact congrFun (congrArg (fun (f : _ →ₗ[R] _) ↦ (f : _ → _))
    (blockProj_blockIncl (R := R) n
      (fun pq ↦ TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)))) y

/-- The degree-`n` extraction map `prodToDirectSum` is surjective. -/
theorem prodToDirectSum_surjective (n : ℕ) :
    Function.Surjective (prodToDirectSum (R := R) (M := M) (N := N) n) := by
  intro y
  have hmem : ∀ z : DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)),
      prodDecomposition.symm (blockIncl (R := R) n
          (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)) z)
        ∈ (⋀[R]^n (M × N)) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of pq t => exact prodDecomposition_symm_blockIncl_mem n pq t
    | add x w hx hw => rw [map_add, map_add]; exact Submodule.add_mem _ hx hw
  exact ⟨_, prodToDirectSum_symm_blockIncl n y (hmem y)⟩

/-- The bidegree-`k` span inside `Λ M ⊗̂ Λ N`: the submodule generated by the pure tensors
`↑a ⊗ ↑b` with `a ∈ ⋀ᵖ M`, `b ∈ ⋀^q N` and `p + q = k`. -/
noncomputable def bidegSpanProd (k : ℕ) :
    Submodule R (ExteriorAlgebra.gradedTensorProd R M N) :=
  Submodule.span R
    {z | ∃ (p q : ℕ) (_ : p + q = k) (a : ⋀[R]^p M) (b : ⋀[R]^q N),
      z = GradedTensorProduct.tmul R (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N)}

/-- The bidegree-`k` span is the span of the pure tensors `↑a ⊗ ↑b` with `a ∈ ⋀ᵖ M`, `b ∈ ⋀^q N`
and `p + q = k`. -/
theorem bidegSpanProd_eq (k : ℕ) :
    bidegSpanProd (R := R) (M := M) (N := N) k = Submodule.span R
      {z | ∃ (p q : ℕ) (_ : p + q = k) (a : ⋀[R]^p M) (b : ⋀[R]^q N),
        z = GradedTensorProduct.tmul R (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N)} :=
  rfl

/-- A pure tensor `↑a ⊗ ↑b` with `a ∈ ⋀ᵖ M` and `b ∈ ⋀^q N` lies in the bidegree-`(p + q)`
span. -/
theorem tmul_mem_bidegSpanProd {p q : ℕ} (a : ⋀[R]^p M) (b : ⋀[R]^q N) :
    (GradedTensorProduct.tmul R (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N)
      : ExteriorAlgebra.gradedTensorProd R M N) ∈ bidegSpanProd (p + q) :=
  Submodule.subset_span ⟨p, q, rfl, a, b, rfl⟩

/-- `gradedTensorProdDecomposition` sends the bidegree-`k` span into the total-degree-`k` block,
i.e. into the range of `blockIncl`. -/
theorem gradedTensorProdDecomposition_bidegSpanProd_le (k : ℕ) :
    Submodule.map (gradedTensorProdDecomposition (R := R) (M := M) (N := N)).toLinearMap
        (bidegSpanProd k)
      ≤ LinearMap.range (blockIncl (R := R) k
          (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))) := by
  rw [bidegSpanProd_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨z, ⟨p, q, h, a, b, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, LinearEquiv.coe_toLinearMap, gradedTensorProdDecomposition_tmul]
  refine ⟨DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = k}
      (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) ⟨(p, q), h⟩ (a ⊗ₜ[R] b), ?_⟩
  simp only [blockIncl, DirectSum.toModule_lof]

/-- `1` lies in the bidegree-`0` span. -/
theorem one_mem_bidegSpanProd :
    (1 : ExteriorAlgebra.gradedTensorProd R M N) ∈ bidegSpanProd (R := R) (M := M) (N := N) 0 := by
  have h := tmul_mem_bidegSpanProd (p := 0) (q := 0) (1 : ⋀[R]^0 M) (1 : ⋀[R]^0 N)
  have e1 : ((1 : ⋀[R]^0 M) : ExteriorAlgebra R M) = 1 := rfl
  have e2 : ((1 : ⋀[R]^0 N) : ExteriorAlgebra R N) = 1 := rfl
  rwa [e1, e2] at h

/-- The bidegree spans are closed under the multiplication of the graded tensor product:
`bidegSpanProd p * bidegSpanProd q ≤ bidegSpanProd (p + q)`. -/
theorem bidegSpanProd_mul_le (p q : ℕ) :
    (bidegSpanProd (R := R) (M := M) (N := N) p) * bidegSpanProd q
      ≤ bidegSpanProd (p + q) := by
  apply Submodule.mul_le.mpr
  rw [bidegSpanProd_eq p, bidegSpanProd_eq q]
  intro u hu v hv
  induction hu using Submodule.span_induction with
  | mem u hu =>
      induction hv using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨i, j, rfl, a, b, rfl⟩ := hu
          obtain ⟨i', j', rfl, a', b', rfl⟩ := hv
          rw [GradedTensorProduct.tmul_coe_mul_coe_tmul]
          have hmem := tmul_mem_bidegSpanProd
            (⟨(a : ExteriorAlgebra R M) * (a' : ExteriorAlgebra R M),
              ExteriorAlgebra.mul_mem_extPow a.2 a'.2⟩ : ⋀[R]^(i + i') M)
            (⟨(b : ExteriorAlgebra R N) * (b' : ExteriorAlgebra R N),
              ExteriorAlgebra.mul_mem_extPow b.2 b'.2⟩ : ⋀[R]^(j + j') N)
          rw [show (i + i') + (j + j') = (i + j) + (i' + j') by lia] at hmem
          exact Submodule.smul_mem _ _ hmem
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add v₁ v₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul c v _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add u₁ u₂ _ _ ih₁ ih₂ => rw [add_mul]; exact Submodule.add_mem _ ih₁ ih₂
  | smul c u _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

/-- `ExteriorAlgebra.prodEta` lands in the bidegree-`1` span. -/
theorem prodEta_mem_bidegSpanProd (vw : M × N) :
    ExteriorAlgebra.prodEta (R := R) vw ∈ bidegSpanProd (R := R) (M := M) (N := N) 1 := by
  obtain ⟨v, w⟩ := vw
  simp only [ExteriorAlgebra.prodEta, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
  apply Submodule.add_mem
  · have h := tmul_mem_bidegSpanProd (p := 1) (q := 0)
      (⟨ExteriorAlgebra.ι R v, ExteriorAlgebra.ι_mem_extPow_one v⟩ : ⋀[R]^1 M) (1 : ⋀[R]^0 N)
    have e2 : ((1 : ⋀[R]^0 N) : ExteriorAlgebra R N) = 1 := rfl
    rwa [e2] at h
  · have h := tmul_mem_bidegSpanProd (p := 0) (q := 1)
      (1 : ⋀[R]^0 M) (⟨ExteriorAlgebra.ι R w, ExteriorAlgebra.ι_mem_extPow_one w⟩ : ⋀[R]^1 N)
    have e1 : ((1 : ⋀[R]^0 M) : ExteriorAlgebra R M) = 1 := rfl
    rwa [e1] at h

/-- The forward algebra hom `ExteriorAlgebra.prodToGradedTensorProd` carries `⋀^k (M × N)` into
the bidegree-`k` span. -/
theorem prodToGradedTensorProd_mem_bidegSpanProd :
    ∀ {k : ℕ} (x : ExteriorAlgebra R (M × N)),
      x ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ k →
        ExteriorAlgebra.prodToGradedTensorProd x ∈ bidegSpanProd (R := R) (M := M) (N := N) k := by
  intro k x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap c =>
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ one_mem_bidegSpanProd
  | add x y i hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
      obtain ⟨vw, rfl⟩ := hm
      rw [map_mul]
      have hηmem : ExteriorAlgebra.prodToGradedTensorProd (R := R) (M := M) (N := N)
          (ExteriorAlgebra.ι R vw) ∈ bidegSpanProd 1 := by
        rw [ExteriorAlgebra.prodToGradedTensorProd, ExteriorAlgebra.lift_ι_apply]
        exact prodEta_mem_bidegSpanProd vw
      have hle := bidegSpanProd_mul_le (R := R) (M := M) (N := N) 1 i
        (Submodule.mul_mem_mul hηmem ih)
      rwa [Nat.add_comm] at hle

/-- The degree-`n` extraction map `prodToDirectSum` is injective. -/
theorem prodToDirectSum_injective (n : ℕ) :
    Function.Injective (prodToDirectSum (R := R) (M := M) (N := N) n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [prodToDirectSum] at hx
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at hx
  have hsupp : prodDecomposition (x : ExteriorAlgebra R (M × N))
      ∈ LinearMap.range (blockIncl (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))) := by
    have halg : ExteriorAlgebra.prodToGradedTensorProd (x : ExteriorAlgebra R (M × N))
        ∈ bidegSpanProd (R := R) (M := M) (N := N) n :=
      prodToGradedTensorProd_mem_bidegSpanProd _ x.2
    have hmap : prodDecomposition (x : ExteriorAlgebra R (M × N))
        = gradedTensorProdDecomposition
            (ExteriorAlgebra.prodToGradedTensorProd (x : ExteriorAlgebra R (M × N))) := by
      rw [prodDecomposition, LinearEquiv.trans_apply]
      rfl
    rw [hmap]
    exact gradedTensorProdDecomposition_bidegSpanProd_le n ⟨_, halg, rfl⟩
  obtain ⟨w, hw⟩ := hsupp
  have hwzero : w = 0 := by
    have hxx : (blockProj (R := R) n
        (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)))
        (prodDecomposition (x : ExteriorAlgebra R (M × N))) = 0 := hx
    rw [← hw] at hxx
    have hid := LinearMap.congr_fun (blockProj_blockIncl (R := R) n
      (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N))) w
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at hid
    rwa [hid] at hxx
  rw [hwzero, map_zero] at hw
  have hxval : (x : ExteriorAlgebra R (M × N)) = 0 := by
    apply prodDecomposition.injective
    rw [map_zero, ← hw]
  exact Subtype.ext hxval

/-- **The exterior power of a direct sum.** For modules `M` and `N` over a commutative ring `R`,
the `R`-linear isomorphism `⋀ⁿ (M × N) ≃ ⨁_{p + q = n} ⋀ᵖ M ⊗ ⋀^q N`, the degree-`n` part of the
algebra isomorphism `Λ(M × N) ≅ Λ M ⊗̂ Λ N`. -/
@[sga "5 III 6.9" "6.9.0", sga "6 V 2.2.1" "special case"]
noncomputable def prodEquivDirectSum (n : ℕ) :
    (⋀[R]^n (M × N)) ≃ₗ[R] DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) :=
  LinearEquiv.ofBijective (prodToDirectSum n)
    ⟨prodToDirectSum_injective n, prodToDirectSum_surjective n⟩

/-- `prodEquivDirectSum` is given by `prodToDirectSum`. -/
theorem prodEquivDirectSum_apply (n : ℕ) (x : ⋀[R]^n (M × N)) :
    prodEquivDirectSum (N := N) n x = prodToDirectSum n x :=
  rfl

/-- The inverse of `prodEquivDirectSum` sends the block generator `lof ⟨(p, q), h⟩ (a ⊗ b)` to the
product of the two embedded factors `(Λ inl) ↑a * (Λ inr) ↑b`. -/
theorem prodEquivDirectSum_symm_lof_tmul_coe (n p q : ℕ) (h : p + q = n)
    (a : (⋀[R]^p M)) (b : (⋀[R]^q N)) :
    (((prodEquivDirectSum (R := R) (M := M) (N := N) n).symm
          (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
            (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N))
            ⟨(p, q), h⟩ (a ⊗ₜ[R] b)) : ⋀[R]^n (M × N)) : ExteriorAlgebra R (M × N))
      = (ExteriorAlgebra.map (LinearMap.inl R M N)) (a : ExteriorAlgebra R M)
          * (ExteriorAlgebra.map (LinearMap.inr R M N)) (b : ExteriorAlgebra R N) := by
  set y := DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
    (fun pq => TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) ⟨(p, q), h⟩ (a ⊗ₜ[R] b) with hy
  have hmem := prodDecomposition_symm_lof_tmul_mem (R := R) n p q h a b
  rw [← hy] at hmem
  have hsymm : ((prodEquivDirectSum (R := R) (M := M) (N := N) n).symm y)
      = ⟨prodDecomposition.symm (blockIncl (R := R) n
          (fun pq => TensorProduct R (⋀[R]^pq.1 M) (⋀[R]^pq.2 N)) y), hmem⟩ := by
    apply (prodEquivDirectSum (R := R) (M := M) (N := N) n).injective
    rw [LinearEquiv.apply_symm_apply, prodEquivDirectSum_apply,
      prodToDirectSum_symm_blockIncl n y hmem]
  rw [hsymm]
  exact prodDecomposition_symm_lof_tmul n p q h a b

end exteriorPower
