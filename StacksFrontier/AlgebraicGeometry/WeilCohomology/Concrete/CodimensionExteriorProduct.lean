module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor

/-!
# The exterior product on Chow groups graded by codimension

Let `k` be a field and let `X` and `Y` be smooth over `k`. The exterior product of Stacks 0FBV,
`CH_n(X) ⊗ CH_m(Y) ⟶ CH_{n+m}(X ×_k Y)`, is graded by dimension. On the Chow groups graded by
codimension, `CH^i(X) = ∏_d CH_{d-i}(X_d)` (Chow Homology, Section 0FE2;
`Stacks.Chow.codimensionChowGroup`), it reads

  `× : CH^i(X) × CH^j(Y) ⟶ CH^{i+j}(X ×_k Y)`,

since `X_d ×_k Y_e` has dimension `d + e` and a class of dimension `(d - i) + (e - j)` on it has
codimension `i + j`. Concretely, the part of `α × β` on the part `(X ×_k Y)_n` of `X ×_k Y` of
dimension `n` is

  `(α × β)_n = Σ_{d + e = n} (ι_{d,*} α_d × ι_{e,*} β_e)|_{(X ×_k Y)_n}`,

the exterior product of the classes `α_d ∈ CH_{d-i}(X_d)` and `β_e ∈ CH_{e-j}(Y_e)`, pushed into
`X` and `Y`, restricted to `(X ×_k Y)_n`.

## Main definitions

* `Stacks.Chow.partProdIncl`: the open and closed immersion `X_d ×_k Y_{n-d} ⟶ (X ×_k Y)_n`.
* `Stacks.Chow.codimensionExteriorProduct`: the exterior product
  `CH^i(X) × CH^j(Y) ⟶ CH^{i+j}(X ×_k Y)`.

## References

* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Section 42.33 (Tag 0FE2)](https://stacks.math.columbia.edu/tag/0FE2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart prodBase)

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]

/-! ### The products of parts inside a part of the product -/

open Stacks.WeilCohomology (partProdMap range_partProdMap_subset partProdMap_fst partProdMap_snd
  partProdMap_comp_prodBase)

/-- The open and closed immersion `X_d ×_k Y_{n-d} ⟶ (X ×_k Y)_n` of the product of two parts into
the part of `X ×_k Y` of dimension `n`, for `d ≤ n`. -/
def partProdIncl (n : ℕ) (d : Fin (n + 1)) :
    (pullback (partBase sX d) (partBase sY (n - d)) : Scheme.{u}) ⟶
      (dimPart (prodBase sX sY) n).toScheme :=
  IsOpenImmersion.lift (dimPart (prodBase sX sY) n).ι (partProdMap sX sY d (n - d)) (by
    have h := range_partProdMap_subset k sX sY d (n - d)
    rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.1 d.2)] at h
    rwa [Scheme.Opens.range_ι])

/-- Composing `partProdIncl` with the inclusion `(X ×_k Y)_n ⟶ X ×_k Y` gives the product
`X_d ×_k Y_{n-d} ⟶ X ×_k Y` of the inclusions of the parts. -/
@[reassoc (attr := simp)]
theorem partProdIncl_ι (n : ℕ) (d : Fin (n + 1)) :
    partProdIncl k sX sY n d ≫ (dimPart (prodBase sX sY) n).ι = partProdMap sX sY d (n - d) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The morphism `partProdIncl` is an open immersion. -/
instance (n : ℕ) (d : Fin (n + 1)) : IsOpenImmersion (partProdIncl k sX sY n d) := by
  have : IsOpenImmersion (partProdIncl k sX sY n d ≫ (dimPart (prodBase sX sY) n).ι) := by
    rw [partProdIncl_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (dimPart (prodBase sX sY) n).ι

/-- The morphism `partProdIncl` commutes with the structure morphisms to `Spec k`: composed with
the structure morphism of `(X ×_k Y)_n`, it is the structure morphism of `X_d ×_k Y_{n-d}`. -/
theorem partProdIncl_comp_partBase (n : ℕ) (d : Fin (n + 1)) :
    partProdIncl k sX sY n d ≫ partBase (prodBase sX sY) n =
      prodBase (partBase sX d) (partBase sY (n - d)) := by
  show partProdIncl k sX sY n d ≫ (dimPart (prodBase sX sY) n).ι ≫ prodBase sX sY = _
  rw [partProdIncl_ι_assoc, partProdMap_comp_prodBase]

/-- For `X` and `Y` proper over `k`, the morphism `partProdIncl` is proper. -/
instance [IsProper sX] [IsProper sY] (n : ℕ) (d : Fin (n + 1)) :
    IsProper (partProdIncl k sX sY n d) := by
  have : IsProper (partProdIncl k sX sY n d ≫ partBase (prodBase sX sY) n) := by
    rw [partProdIncl_comp_partBase]; infer_instance
  exact IsProper.of_comp _ (partBase (prodBase sX sY) n)

/-- The image of a point of an open subscheme `U` under the inclusion lies in `U`. -/
private theorem opens_ι_apply_mem {Z : Scheme.{u}} (U : Z.Opens) (z : U.toScheme) : U.ι z ∈ U := by
  rw [← SetLike.mem_coe, ← U.range_ι]
  exact Set.mem_range_self _

/-- **`(X ×_k Y)_n = ∐_{d ≤ n} X_d ×_k Y_{n-d}`**: the images of the products of parts decompose
the part of `X ×_k Y` of dimension `n` into open and closed subschemes. -/
theorem isClopenDecomposition_partProdIncl (n : ℕ) :
    IsClopenDecomposition fun d : ULift.{u} (Fin (n + 1)) ↦
      (partProdIncl k sX sY n d.down).opensRange where
  disjoint d d' hdd' := by
    refine TopologicalSpace.Opens.coe_disjoint.1 (Set.disjoint_left.2 ?_)
    rintro _ ⟨p, rfl⟩ ⟨p', hp'⟩
    have h1 : (pullback.fst sX sY) (partProdMap sX sY d.down (n - d.down) p) =
        (pullback.fst sX sY) (partProdMap sX sY d'.down (n - d'.down) p') := by
      rw [← partProdIncl_ι, ← partProdIncl_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hp']
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, partProdMap_fst, partProdMap_fst,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
    have := (isClopenDecomposition_dimPart sX).eq_of_mem (h1 ▸ opens_ι_apply_mem _ _)
      (opens_ι_apply_mem (dimPart sX d'.down) _)
    exact hdd' (ULift.ext _ _ (Fin.ext this))
  iSup_eq_top := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    set z' := (dimPart (prodBase sX sY) n).ι z
    obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart sX).exists_mem (pullback.fst sX sY z')
    obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart sY).exists_mem (pullback.snd sX sY z')
    have hz : z' ∈ Set.range (partProdMap sX sY d e) := by
      rw [Scheme.Pullback.range_map]
      exact ⟨by rwa [Scheme.Opens.range_ι], by rwa [Scheme.Opens.range_ι]⟩
    have hde : d + e = n := (isClopenDecomposition_dimPart (prodBase sX sY)).eq_of_mem
      (range_partProdMap_subset k sX sY d e hz) (opens_ι_apply_mem _ _)
    have hdn : d < n + 1 := by omega
    have hen : n - d = e := by omega
    obtain ⟨p, hp⟩ := hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨d, hdn⟩⟩, ?_⟩
    subst hen
    refine ⟨p, (dimPart (prodBase sX sY) n).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, partProdIncl_ι]
    exact hp

variable [IsProper sX] [IsProper sY]

/-- The `d`-th term `ψ_{d,*}(α_d × β_{n-d})`, `ψ_d : X_d ×_k Y_{n-d} ⟶ (X ×_k Y)_n`, of the
exterior product on the part `(X ×_k Y)_n`, in `CH_{n-(i+j)}((X ×_k Y)_n)`. -/
def codimensionExteriorTerm (i j : ℤ) (n : ℕ) (d : Fin (n + 1)) :
    codimensionChowGroup k sX i →ₗ[ℤ] codimensionChowGroup k sY j →ₗ[ℤ]
      chowGroup (fieldChowSituation k) (partBase (prodBase sX sY) n) (n - (i + j)) :=
  LinearMap.mk₂ ℤ
    (fun α β ↦ properChowPushforward (fieldChowSituation k)
      (prodBase (partBase sX d) (partBase sY (n - d))) (partBase (prodBase sX sY) n)
      (partProdIncl k sX sY n d) (partProdIncl_comp_partBase k sX sY n d) _
      (properPushforwardDescends _ _ _ _ _ _)
      (chowGroupDegreeEquiv _ _
        (by have := d.2; push_cast [Nat.cast_sub (Nat.lt_succ_iff.1 this)]; ring)
        (chowExteriorProduct (fieldChowSituation k)
            (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
          (partBase sX d) (partBase sY (n - d)) ((d : ℕ) - i) ((n - d : ℕ) - j)
          (α d ⊗ₜ[ℤ] β (n - d)))))
    (fun _ _ _ ↦ by simp [TensorProduct.add_tmul])
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, map_zsmul, ← TensorProduct.smul_tmul'])
    (fun _ _ _ ↦ by simp [TensorProduct.tmul_add])
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, map_zsmul, TensorProduct.tmul_smul])

/-- **The exterior product `CH^i(X) × CH^j(Y) ⟶ CH^{i+j}(X ×_k Y)`** of Stacks 0FBV on Chow groups
graded by codimension, for `X` and `Y` smooth and proper over `k`: on the part `(X ×_k Y)_n` of
`X ×_k Y` of dimension `n` it is `Σ_{d = 0}^{n} ψ_{d,*}(α_d × β_{n-d})`, the exterior products of
the parts of `α` and `β` placed on `X_d ×_k Y_{n-d} ⊆ (X ×_k Y)_n`. -/
def codimensionExteriorProduct (i j : ℤ) :
    codimensionChowGroup k sX i →ₗ[ℤ] codimensionChowGroup k sY j →ₗ[ℤ]
      codimensionChowGroup k (prodBase sX sY) (i + j) :=
  LinearMap.mk₂ ℤ
    (fun α β n ↦ ∑ d : Fin (n + 1), codimensionExteriorTerm k sX sY i j n d α β)
    (fun _ _ _ ↦ funext fun _ ↦ by simp [Finset.sum_add_distrib])
    (fun _ _ _ ↦ funext fun _ ↦ by simp [Finset.smul_sum])
    (fun _ _ _ ↦ funext fun _ ↦ by simp [Finset.sum_add_distrib])
    (fun _ _ _ ↦ funext fun _ ↦ by simp [Finset.smul_sum])

/-- The part of `α × β` on `(X ×_k Y)_n` is the sum over `d ≤ n` of the terms
`codimensionExteriorTerm`. -/
theorem codimensionExteriorProduct_apply (i j : ℤ) (α : codimensionChowGroup k sX i)
    (β : codimensionChowGroup k sY j) (n : ℕ) :
    codimensionExteriorProduct k sX sY i j α β n =
      ∑ d : Fin (n + 1), codimensionExteriorTerm k sX sY i j n d α β :=
  rfl

end Stacks.Chow

end
