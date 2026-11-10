module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod

/-!
# The symmetric power of a direct sum

Let `R` be a commutative ring and `M`, `N` two `R`-modules. The symmetric algebra of a direct sum
is the tensor product of the symmetric algebras,

`Sym_R(M × N) ≅ Sym_R(M) ⊗_R Sym_R(N)`,

and both sides are graded — the left by the symmetric powers of `M × N`, the right by the
bidegrees of the two factors — so the isomorphism restricts in each total degree to the Künneth
decomposition

`Symⁿ_R(M × N) ≅ ⨁_{p + q = n} Symᵖ_R(M) ⊗_R Sym^q_R(N)`.

## Main definitions

* `SymmetricAlgebra.prodEta`: the `R`-linear map `M × N → Sym M ⊗ Sym N`,
  `(m, n) ↦ ι m ⊗ 1 + 1 ⊗ ι n`.
* `SymmetricAlgebra.prodToTensorProd` and `SymmetricAlgebra.tensorProdToProd`: the two algebra
  homomorphisms between `Sym(M × N)` and `Sym M ⊗ Sym N`, and
  `SymmetricAlgebra.prodAlgEquiv` the isomorphism of `R`-algebras they constitute.
* `SymPow.tensorProdDecomposition` and `SymPow.prodDecomposition`: the identifications of
  `Sym M ⊗ Sym N` and of `Sym(M × N)` with `⨁_{(p, q) : ℕ × ℕ} Symᵖ M ⊗ Sym^q N`.
* `SymPow.prodToDirectSum`: the degree-`n` extraction map
  `Symⁿ(M × N) → ⨁_{p + q = n} Symᵖ M ⊗ Sym^q N`.
* `SymPow.bidegSpanProd`: the bidegree-`k` span inside `Sym M ⊗ Sym N`.
* `SymPow.prodEquivDirectSum`: the Künneth decomposition
  `Symⁿ(M × N) ≃ₗ ⨁_{p + q = n} Symᵖ M ⊗ Sym^q N`.

## Main results

* `SymPow.bijective_prodToDirectSum`: the extraction map is bijective;
  `SymPow.exists_prodToDirectSum_eq` is its surjectivity half.
* `SymPow.prodEquivDirectSum_symm_lof_tmul_coe`: the inverse of the decomposition carries the
  `(p, q)` block generator `a ⊗ b` to the product of the two embedded factors.
* `SymPow.symMap_inl_injective` and `SymPow.symMap_inr_injective`:
  `Symⁿ(M) → Symⁿ(M × N)` and `Symⁿ(N) → Symⁿ(M × N)` are injective, with no hypothesis on the
  modules.

## Implementation notes

The index set of the degree-`n` decomposition is the subtype `{pq : ℕ × ℕ // pq.1 + pq.2 = n}`,
and the degree-`n` part of the full `ℕ × ℕ`-indexed decomposition is cut out with `blockProj`
and `blockIncl`. The grading of the symmetric algebra by its symmetric powers is
`SymmetricAlgebra.gradedAlgebra`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open scoped DirectSum TensorProduct

/-! ### Split injectivity of the symmetric power of an inclusion -/

namespace SymPow

variable {R : Type*} [CommSemiring R]

/-- `Symⁿ(M) → Symⁿ(M × N)` is injective, with no hypothesis on `M` or `N`. -/
theorem symMap_inl_injective (n : ℕ) {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] :
    Function.Injective (symMap n (LinearMap.inl R M N)) :=
  symMap_injective_of_leftInverse n _ (LinearMap.fst R M N) (LinearMap.ext fun _ => rfl)

/-- `Symⁿ(N) → Symⁿ(M × N)` is injective, with no hypothesis on `M` or `N`. -/
theorem symMap_inr_injective (n : ℕ) {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] :
    Function.Injective (symMap n (LinearMap.inr R M N)) :=
  symMap_injective_of_leftInverse n _ (LinearMap.snd R M N) (LinearMap.ext fun _ => rfl)

end SymPow

/-! ### The symmetric algebra of a direct sum -/

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- The `R`-linear map `η : M × N → Sym M ⊗ Sym N`, `η (m, n) = ι m ⊗ 1 + 1 ⊗ ι n`. -/
noncomputable def prodEta :
    (M × N) →ₗ[R] TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N) :=
  LinearMap.coprod
    ((Algebra.TensorProduct.includeLeft (R := R) (S := R)
      (A := SymmetricAlgebra R M) (B := SymmetricAlgebra R N)).toLinearMap.comp
        (SymmetricAlgebra.ι R M))
    ((Algebra.TensorProduct.includeRight (R := R)
      (A := SymmetricAlgebra R M) (B := SymmetricAlgebra R N)).toLinearMap.comp
        (SymmetricAlgebra.ι R N))

/-- `η (m, n) = ι m ⊗ 1 + 1 ⊗ ι n`. -/
@[simp] theorem prodEta_apply (mn : M × N) :
    prodEta (R := R) mn =
      (SymmetricAlgebra.ι R M mn.1) ⊗ₜ[R] (1 : SymmetricAlgebra R N) +
        (1 : SymmetricAlgebra R M) ⊗ₜ[R] (SymmetricAlgebra.ι R N mn.2) :=
  rfl

/-- The forward `R`-algebra homomorphism `Sym(M × N) → Sym M ⊗ Sym N` determined by
`ι (m, n) ↦ ι m ⊗ 1 + 1 ⊗ ι n`. -/
noncomputable def prodToTensorProd :
    SymmetricAlgebra R (M × N) →ₐ[R]
      TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N) :=
  SymmetricAlgebra.lift prodEta

/-- `prodToTensorProd (ι (m, n)) = η (m, n)`. -/
@[simp] theorem prodToTensorProd_ι (mn : M × N) :
    prodToTensorProd (SymmetricAlgebra.ι R (M × N) mn) = prodEta mn :=
  SymmetricAlgebra.lift_ι_apply _ mn

/-- The backward `R`-algebra homomorphism `Sym M ⊗ Sym N → Sym(M × N)`, the product of the two
functorial embeddings. -/
noncomputable def tensorProdToProd :
    TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N) →ₐ[R]
      SymmetricAlgebra R (M × N) :=
  Algebra.TensorProduct.lift (SymPow.symAlgMap (LinearMap.inl R M N))
    (SymPow.symAlgMap (LinearMap.inr R M N)) fun _ _ => Commute.all _ _

/-- `tensorProdToProd` carries `x ⊗ y` to the product of the two embedded factors. -/
@[simp] theorem tensorProdToProd_tmul (x : SymmetricAlgebra R M) (y : SymmetricAlgebra R N) :
    tensorProdToProd (x ⊗ₜ[R] y) =
      SymPow.symAlgMap (LinearMap.inl R M N) x * SymPow.symAlgMap (LinearMap.inr R M N) y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- `tensorProdToProd` is a left inverse of `prodToTensorProd`. -/
theorem tensorProdToProd_comp_prodToTensorProd :
    (tensorProdToProd (R := R) (M := M) (N := N)).comp prodToTensorProd =
      AlgHom.id R (SymmetricAlgebra R (M × N)) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun mn => ?_)
  change tensorProdToProd (prodToTensorProd (SymmetricAlgebra.ι R (M × N) mn)) =
    SymmetricAlgebra.ι R (M × N) mn
  rw [prodToTensorProd_ι, prodEta_apply, map_add, tensorProdToProd_tmul, tensorProdToProd_tmul,
    map_one, map_one, mul_one, one_mul, SymPow.symAlgMap_ι, SymPow.symAlgMap_ι, ← map_add]
  exact congrArg (SymmetricAlgebra.ι R (M × N)) (Prod.ext (add_zero mn.1) (zero_add mn.2))

/-- `tensorProdToProd` is a right inverse of `prodToTensorProd`. -/
theorem prodToTensorProd_comp_tensorProdToProd :
    (prodToTensorProd (R := R) (M := M) (N := N)).comp tensorProdToProd =
      AlgHom.id R (TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N)) := by
  refine Algebra.TensorProduct.ext' fun x y => ?_
  change prodToTensorProd (tensorProdToProd (x ⊗ₜ[R] y)) = x ⊗ₜ[R] y
  have hleft : ∀ u : SymmetricAlgebra R M,
      prodToTensorProd (SymPow.symAlgMap (LinearMap.inl R M N) u) =
        u ⊗ₜ[R] (1 : SymmetricAlgebra R N) := fun u =>
    AlgHom.congr_fun (φ₁ := (prodToTensorProd (R := R) (M := M) (N := N)).comp
        (SymPow.symAlgMap (LinearMap.inl R M N)))
      (φ₂ := Algebra.TensorProduct.includeLeft (R := R) (S := R))
      (SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => by simp [SymPow.symAlgMap_ι])) u
  have hright : ∀ v : SymmetricAlgebra R N,
      prodToTensorProd (SymPow.symAlgMap (LinearMap.inr R M N) v) =
        (1 : SymmetricAlgebra R M) ⊗ₜ[R] v := fun v =>
    AlgHom.congr_fun (φ₁ := (prodToTensorProd (R := R) (M := M) (N := N)).comp
        (SymPow.symAlgMap (LinearMap.inr R M N)))
      (φ₂ := Algebra.TensorProduct.includeRight (R := R))
      (SymmetricAlgebra.algHom_ext (LinearMap.ext fun n => by simp [SymPow.symAlgMap_ι])) v
  rw [tensorProdToProd_tmul, map_mul, hleft, hright, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- The canonical `R`-algebra isomorphism `Sym(M × N) ≅ Sym M ⊗ Sym N`. -/
noncomputable def prodAlgEquiv :
    SymmetricAlgebra R (M × N) ≃ₐ[R]
      TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N) :=
  AlgEquiv.ofAlgHom prodToTensorProd tensorProdToProd prodToTensorProd_comp_tensorProdToProd
    tensorProdToProd_comp_prodToTensorProd

/-- `prodAlgEquiv` is given by `prodToTensorProd`. -/
@[simp] theorem prodAlgEquiv_apply (x : SymmetricAlgebra R (M × N)) :
    prodAlgEquiv (N := N) x = prodToTensorProd x :=
  rfl

/-- `prodAlgEquiv.symm` carries a pure tensor to the product of the two embedded factors. -/
theorem prodAlgEquiv_symm_tmul (x : SymmetricAlgebra R M) (y : SymmetricAlgebra R N) :
    (prodAlgEquiv (R := R) (M := M) (N := N)).symm (x ⊗ₜ[R] y) =
      SymPow.symAlgMap (LinearMap.inl R M N) x * SymPow.symAlgMap (LinearMap.inr R M N) y :=
  tensorProdToProd_tmul x y

end SymmetricAlgebra

/-! ### The degreewise decomposition -/

namespace SymPow

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- The `R`-linear isomorphism `Sym M ⊗ Sym N ≃ ⨁_{(p, q) : ℕ × ℕ} Symᵖ M ⊗ Sym^q N` induced by
the grading decompositions of the two symmetric algebras. -/
noncomputable def tensorProdDecomposition :
    TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N) ≃ₗ[R]
      (⨁ (pq : ℕ × ℕ), TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N)) :=
  TensorProduct.congr
      (DirectSum.decomposeLinearEquiv (fun p : ℕ => symmetricPower p R M))
      (DirectSum.decomposeLinearEquiv (fun q : ℕ => symmetricPower q R N)) ≪≫ₗ
    TensorProduct.directSum R R (fun p : ℕ => symmetricPower p R M)
      (fun q : ℕ => symmetricPower q R N)

/-- `tensorProdDecomposition` sends the pure tensor `↑a ⊗ ↑b`, for `a ∈ Symᵖ M` and
`b ∈ Sym^q N`, to the single component `lof (p, q) (a ⊗ b)`. -/
theorem tensorProdDecomposition_tmul (p q : ℕ) (a : symmetricPower p R M)
    (b : symmetricPower q R N) :
    tensorProdDecomposition
        ((a : SymmetricAlgebra R M) ⊗ₜ[R] (b : SymmetricAlgebra R N)) =
      DirectSum.lof R (ℕ × ℕ)
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N)) (p, q)
        (a ⊗ₜ[R] b) := by
  rw [tensorProdDecomposition, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.decomposeLinearEquiv_apply_coe,
    TensorProduct.directSum_lof_tmul_lof]

/-- The `R`-linear isomorphism `Sym(M × N) ≃ ⨁_{(p, q) : ℕ × ℕ} Symᵖ M ⊗ Sym^q N`, the composite
of `SymmetricAlgebra.prodAlgEquiv` with `tensorProdDecomposition`. -/
noncomputable def prodDecomposition :
    SymmetricAlgebra R (M × N) ≃ₗ[R]
      (⨁ (pq : ℕ × ℕ), TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N)) :=
  (SymmetricAlgebra.prodAlgEquiv (R := R) (M := M) (N := N)).toLinearEquiv ≪≫ₗ
    tensorProdDecomposition

/-- The degree-`n` extraction map `Symⁿ(M × N) →ₗ ⨁_{p + q = n} Symᵖ M ⊗ Sym^q N`: include
`Symⁿ(M × N)` into `Sym(M × N)`, apply `prodDecomposition`, and project onto the `{p + q = n}`
block. -/
noncomputable def prodToDirectSum (n : ℕ) :
    (symmetricPower n R (M × N)) →ₗ[R] DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N)) :=
  (blockProj n (fun pq => TensorProduct R (symmetricPower pq.1 R M)
      (symmetricPower pq.2 R N))).comp
    (prodDecomposition.toLinearMap.comp (Submodule.subtype (symmetricPower n R (M × N))))

/-- For `p + q = n`, `a ∈ Symᵖ M` and `b ∈ Sym^q N`, the preimage under `prodDecomposition` of
the block generator `lof ⟨(p, q), h⟩ (a ⊗ b)` is the product of the two embedded factors. -/
theorem prodDecomposition_symm_lof_tmul (n p q : ℕ) (h : p + q = n)
    (a : symmetricPower p R M) (b : symmetricPower q R N) :
    prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b))) =
      SymPow.symAlgMap (LinearMap.inl R M N) (a : SymmetricAlgebra R M) *
        SymPow.symAlgMap (LinearMap.inr R M N) (b : SymmetricAlgebra R N) := by
  have hPhi : (tensorProdDecomposition (R := R) (M := M) (N := N)).symm
      (blockIncl (R := R) n
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b))) =
      (a : SymmetricAlgebra R M) ⊗ₜ[R] (b : SymmetricAlgebra R N) := by
    rw [LinearEquiv.symm_apply_eq]
    simp only [blockIncl, DirectSum.toModule_lof]
    rw [tensorProdDecomposition_tmul]
  rw [prodDecomposition, LinearEquiv.trans_symm, LinearEquiv.trans_apply, hPhi,
    ← AlgEquiv.toLinearEquiv_symm, AlgEquiv.coe_toLinearEquiv]
  exact SymmetricAlgebra.prodAlgEquiv_symm_tmul _ _

/-- For `p + q = n`, `a ∈ Symᵖ M` and `b ∈ Sym^q N`, the preimage under `prodDecomposition` of
the block generator `lof ⟨(p, q), h⟩ (a ⊗ b)` lies in `Symⁿ(M × N)`. -/
theorem prodDecomposition_symm_lof_tmul_mem (n p q : ℕ) (h : p + q = n)
    (a : symmetricPower p R M) (b : symmetricPower q R N) :
    prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N))
          ⟨(p, q), h⟩ (a ⊗ₜ[R] b))) ∈ symmetricPower n R (M × N) := by
  rw [prodDecomposition_symm_lof_tmul]
  have hmem := Submodule.mul_mem_mul
    (symAlgMap_mapsTo p (LinearMap.inl R M N) _ a.2)
    (symAlgMap_mapsTo q (LinearMap.inr R M N) _ b.2)
  rwa [show (symmetricPower p R (M × N)) * symmetricPower q R (M × N) =
      (LinearMap.range (SymmetricAlgebra.ι R (M × N))) ^ (p + q) from (pow_add _ p q).symm,
    h] at hmem

/-- The preimage under `prodDecomposition` of a single block generator lies in
`Symⁿ(M × N)`. -/
theorem prodDecomposition_symm_blockIncl_mem (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (t : TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N)) :
    prodDecomposition.symm (blockIncl (R := R) n
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))
        (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
          (fun pq => TensorProduct R (symmetricPower pq.1.1 R M)
            (symmetricPower pq.1.2 R N)) pq t)) ∈ symmetricPower n R (M × N) := by
  obtain ⟨⟨p, q⟩, h⟩ := pq
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [map_add, map_add, map_add]
      exact Submodule.add_mem _ hx hy
  | tmul a b => exact prodDecomposition_symm_lof_tmul_mem n p q h a b

/-- The extraction map sends the preimage of `blockIncl y` under `prodDecomposition` back to `y`. -/
private theorem prodToDirectSum_symm_blockIncl (n : ℕ)
    (y : DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N))
    (hmem : prodDecomposition.symm (blockIncl (R := R) n
      (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N)) y) ∈
        symmetricPower n R (M × N)) :
    prodToDirectSum n ⟨prodDecomposition.symm (blockIncl (R := R) n
      (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N)) y),
        hmem⟩ = y := by
  rw [prodToDirectSum]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (blockProj_blockIncl (R := R) n
    (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))) y

/-- Every element of the total-degree-`n` block has a preimage in `Symⁿ(M × N)` under
`prodDecomposition`, and that preimage is carried back to it by the extraction map. -/
theorem exists_prodToDirectSum_eq (n : ℕ)
    (y : DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N)) :
    ∃ w : symmetricPower n R (M × N), prodToDirectSum n w = y := by
  have hmem : ∀ z : DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N)),
      prodDecomposition.symm (blockIncl (R := R) n
          (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N)) z)
        ∈ symmetricPower n R (M × N) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of pq t => exact prodDecomposition_symm_blockIncl_mem n pq t
    | add x w hx hw => rw [map_add, map_add]; exact Submodule.add_mem _ hx hw
  exact ⟨⟨_, hmem y⟩, prodToDirectSum_symm_blockIncl n y _⟩

/-! ### The bidegree spans -/

/-- The bidegree-`k` span inside `Sym M ⊗ Sym N`: the submodule generated by the pure tensors
`↑a ⊗ ↑b` with `a ∈ Symᵖ M`, `b ∈ Sym^q N` and `p + q = k`. -/
noncomputable def bidegSpanProd (k : ℕ) :
    Submodule R (TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N)) :=
  Submodule.span R
    {z | ∃ (p q : ℕ) (_ : p + q = k) (a : symmetricPower p R M) (b : symmetricPower q R N),
      z = (a : SymmetricAlgebra R M) ⊗ₜ[R] (b : SymmetricAlgebra R N)}

/-- The bidegree-`k` span is the span of the pure tensors `↑a ⊗ ↑b` with `a ∈ Symᵖ M`,
`b ∈ Sym^q N` and `p + q = k`. -/
theorem bidegSpanProd_eq (k : ℕ) :
    bidegSpanProd (R := R) (M := M) (N := N) k = Submodule.span R
      {z | ∃ (p q : ℕ) (_ : p + q = k) (a : symmetricPower p R M) (b : symmetricPower q R N),
        z = (a : SymmetricAlgebra R M) ⊗ₜ[R] (b : SymmetricAlgebra R N)} :=
  rfl

/-- A pure tensor `↑a ⊗ ↑b` with `a ∈ Symᵖ M` and `b ∈ Sym^q N` lies in the bidegree-`(p + q)`
span. -/
theorem tmul_mem_bidegSpanProd {p q : ℕ} (a : symmetricPower p R M)
    (b : symmetricPower q R N) :
    (a : SymmetricAlgebra R M) ⊗ₜ[R] (b : SymmetricAlgebra R N) ∈ bidegSpanProd (p + q) :=
  Submodule.subset_span ⟨p, q, rfl, a, b, rfl⟩

/-- A pure tensor of elements of `Symᵖ M` and `Sym^q N` lies in the bidegree-`k` span if
`p + q = k`. -/
private theorem tmul_mem_bidegSpanProd_of_mem {p q k : ℕ} (hk : p + q = k)
    {a : SymmetricAlgebra R M} {b : SymmetricAlgebra R N} (ha : a ∈ symmetricPower p R M)
    (hb : b ∈ symmetricPower q R N) : a ⊗ₜ[R] b ∈ bidegSpanProd (R := R) k :=
  hk ▸ tmul_mem_bidegSpanProd ⟨a, ha⟩ ⟨b, hb⟩

/-- `tensorProdDecomposition` sends the bidegree-`k` span into the total-degree-`k` block, i.e.
into the range of `blockIncl`. -/
theorem tensorProdDecomposition_bidegSpanProd_le (k : ℕ) :
    Submodule.map (tensorProdDecomposition (R := R) (M := M) (N := N)).toLinearMap
        (bidegSpanProd k) ≤
      LinearMap.range (blockIncl (R := R) k
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))) := by
  rw [bidegSpanProd_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨z, ⟨p, q, h, a, b, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, LinearEquiv.coe_toLinearMap, tensorProdDecomposition_tmul]
  refine ⟨DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = k}
    (fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N))
    ⟨(p, q), h⟩ (a ⊗ₜ[R] b), ?_⟩
  simp only [blockIncl, DirectSum.toModule_lof]

/-- `1` lies in the bidegree-`0` span. -/
theorem one_mem_bidegSpanProd :
    (1 : TensorProduct R (SymmetricAlgebra R M) (SymmetricAlgebra R N)) ∈
      bidegSpanProd (R := R) (M := M) (N := N) 0 := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_bidegSpanProd_of_mem (p := 0) (q := 0) rfl (SetLike.one_mem_graded _)
    (SetLike.one_mem_graded _)

/-- The bidegree spans are closed under multiplication:
`bidegSpanProd k * bidegSpanProd l ≤ bidegSpanProd (k + l)`. -/
theorem bidegSpanProd_mul_le (k l : ℕ) :
    bidegSpanProd (R := R) (M := M) (N := N) k * bidegSpanProd l ≤ bidegSpanProd (k + l) := by
  apply Submodule.mul_le.mpr
  rw [bidegSpanProd_eq k, bidegSpanProd_eq l]
  intro u hu v hv
  induction hu using Submodule.span_induction with
  | mem u hu =>
      induction hv using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨i, j, rfl, a, b, rfl⟩ := hu
          obtain ⟨i', j', rfl, a', b', rfl⟩ := hv
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          exact tmul_mem_bidegSpanProd_of_mem (by omega) (SetLike.mul_mem_graded a.2 a'.2)
            (SetLike.mul_mem_graded b.2 b'.2)
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add v₁ v₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul c v _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add u₁ u₂ _ _ ih₁ ih₂ => rw [add_mul]; exact Submodule.add_mem _ ih₁ ih₂
  | smul c u _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

/-- `SymmetricAlgebra.prodEta` lands in the bidegree-`1` span. -/
theorem prodEta_mem_bidegSpanProd (mn : M × N) :
    SymmetricAlgebra.prodEta (R := R) mn ∈ bidegSpanProd (R := R) (M := M) (N := N) 1 := by
  rw [SymmetricAlgebra.prodEta_apply]
  refine Submodule.add_mem _ ?_ ?_
  · exact tmul_mem_bidegSpanProd_of_mem (p := 1) (q := 0) rfl (by simp [symmetricPower])
      (SetLike.one_mem_graded _)
  · exact tmul_mem_bidegSpanProd_of_mem (p := 0) (q := 1) rfl (SetLike.one_mem_graded _)
      (by simp [symmetricPower])

/-- The forward algebra homomorphism `SymmetricAlgebra.prodToTensorProd` carries `Sym^k(M × N)`
into the bidegree-`k` span. -/
theorem prodToTensorProd_mem_bidegSpanProd :
    ∀ {k : ℕ} (x : SymmetricAlgebra R (M × N)),
      x ∈ (LinearMap.range (SymmetricAlgebra.ι R (M × N))) ^ k →
        SymmetricAlgebra.prodToTensorProd x ∈
          bidegSpanProd (R := R) (M := M) (N := N) k := by
  intro k x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap c =>
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ one_mem_bidegSpanProd
  | add x y i hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
      obtain ⟨mn, rfl⟩ := hm
      rw [map_mul]
      have hηmem : SymmetricAlgebra.prodToTensorProd (R := R) (M := M) (N := N)
          (SymmetricAlgebra.ι R (M × N) mn) ∈ bidegSpanProd 1 := by
        rw [SymmetricAlgebra.prodToTensorProd_ι]
        exact prodEta_mem_bidegSpanProd mn
      have hle := bidegSpanProd_mul_le (R := R) (M := M) (N := N) 1 i
        (Submodule.mul_mem_mul hηmem ih)
      rwa [Nat.add_comm] at hle

/-- The degree-`n` extraction map `prodToDirectSum` is bijective. -/
theorem bijective_prodToDirectSum (n : ℕ) :
    Function.Bijective (prodToDirectSum (R := R) (M := M) (N := N) n) := by
  refine ⟨?_, fun y => exists_prodToDirectSum_eq n y⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [prodToDirectSum] at hx
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at hx
  have hsupp : prodDecomposition (x : SymmetricAlgebra R (M × N)) ∈
      LinearMap.range (blockIncl (R := R) n
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))) := by
    have halg : SymmetricAlgebra.prodToTensorProd (x : SymmetricAlgebra R (M × N)) ∈
        bidegSpanProd (R := R) (M := M) (N := N) n :=
      prodToTensorProd_mem_bidegSpanProd _ x.2
    have hmap : prodDecomposition (x : SymmetricAlgebra R (M × N)) =
        tensorProdDecomposition
          (SymmetricAlgebra.prodToTensorProd (x : SymmetricAlgebra R (M × N))) := by
      rw [prodDecomposition, LinearEquiv.trans_apply]
      rfl
    rw [hmap]
    exact tensorProdDecomposition_bidegSpanProd_le n ⟨_, halg, rfl⟩
  obtain ⟨w, hw⟩ := hsupp
  have hwzero : w = 0 := by
    have hxx : (blockProj (R := R) n
        (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N)))
        (prodDecomposition (x : SymmetricAlgebra R (M × N))) = 0 := hx
    rw [← hw] at hxx
    have hid := LinearMap.congr_fun (blockProj_blockIncl (R := R) n
      (fun pq => TensorProduct R (symmetricPower pq.1 R M) (symmetricPower pq.2 R N))) w
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at hid
    rwa [hid] at hxx
  rw [hwzero, map_zero] at hw
  have hxval : (x : SymmetricAlgebra R (M × N)) = 0 := by
    apply prodDecomposition.injective
    rw [map_zero, ← hw]
  exact Subtype.ext hxval

/-- For modules `M` and `N` over a commutative ring `R`, the `R`-linear isomorphism
`Symⁿ(M × N) ≃ ⨁_{p + q = n} Symᵖ M ⊗ Sym^q N`, the degree-`n` part of the algebra isomorphism
`Sym(M × N) ≅ Sym M ⊗ Sym N`. -/
noncomputable def prodEquivDirectSum (n : ℕ) :
    (symmetricPower n R (M × N)) ≃ₗ[R] DirectSum {pq : ℕ × ℕ // pq.1 + pq.2 = n}
      (fun pq => TensorProduct R (symmetricPower pq.1.1 R M) (symmetricPower pq.1.2 R N)) :=
  LinearEquiv.ofBijective (prodToDirectSum n) (bijective_prodToDirectSum n)

/-- `prodEquivDirectSum` is given by `prodToDirectSum`. -/
theorem prodEquivDirectSum_apply (n : ℕ) (x : symmetricPower n R (M × N)) :
    prodEquivDirectSum (N := N) n x = prodToDirectSum n x :=
  rfl

/-- The inverse of `prodEquivDirectSum` sends the block generator `lof ⟨(p, q), h⟩ (a ⊗ b)` to
the product of the two embedded factors. -/
theorem prodEquivDirectSum_symm_lof_tmul_coe (n p q : ℕ) (h : p + q = n)
    (a : symmetricPower p R M) (b : symmetricPower q R N) :
    (((prodEquivDirectSum (R := R) (M := M) (N := N) n).symm
          (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = n}
            (fun pq => TensorProduct R (symmetricPower pq.1.1 R M)
              (symmetricPower pq.1.2 R N))
            ⟨(p, q), h⟩ (a ⊗ₜ[R] b)) : symmetricPower n R (M × N)) :
        SymmetricAlgebra R (M × N)) =
      SymPow.symAlgMap (LinearMap.inl R M N) (a : SymmetricAlgebra R M) *
        SymPow.symAlgMap (LinearMap.inr R M N) (b : SymmetricAlgebra R N) := by
  have hmem := prodDecomposition_symm_lof_tmul_mem (R := R) n p q h a b
  rw [← prodDecomposition_symm_lof_tmul n p q h a b]
  exact congrArg Subtype.val ((prodEquivDirectSum n).symm_apply_eq.2
    (prodToDirectSum_symm_blockIncl n _ hmem).symm)

end SymPow

end
