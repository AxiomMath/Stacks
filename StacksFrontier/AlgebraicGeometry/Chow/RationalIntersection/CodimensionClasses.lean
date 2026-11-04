module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.RationalIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphCodimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.OpenPieceDimension

/-!
# Classes of codimension `i` in `CH_*(X) ⊗ 𝐐`

Let `k` be a field and let `X` be a scheme smooth and quasi-compact over `k`. Chow Homology,
Section 0FE2 writes `CH^i(X) = ∏_d CH_{d-i}(X_d)`, `X_d` the open and closed part of `X` of
dimension `d`; `Stacks.Chow.codimensionToRationalChow` sends a class there to `CH_*(X) ⊗ 𝐐`, and
`Stacks.Chow.codimensionChowSubmodule` is the span in `CH_*(X) ⊗ 𝐐` of the classes of integral
closed subschemes whose local ring at the generic point has dimension `i`. This file shows that
the two notions of codimension agree: a class of `CH^i(X)` lands in `CH^i(X) ⊗ 𝐐`. The geometric
input is that on a scheme of constant dimension `d` over `k` a point `y` has
`dim 𝒪_{X,y} + δ(y) = d` (Stacks 0A21 and Stacks 02QO). It also identifies the image of the
fundamental class `[X] = ∑_d [X_d]_d ∈ CH^0(X)` with `[X] ∈ CH_*(X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.ringKrullDim_stalk_of_relativeDimension` — `dim 𝒪_{T,t} = d - δ(t)` on a scheme of
  constant dimension `d` over `k`.
* `Stacks.Chow.ringKrullDim_stalk_of_mem_dimPart` — the same on the part `X_d` of a smooth `X`.
* `Stacks.Chow.codimensionToRationalChow_mem_codimensionChowSubmodule` — `CH^i(X)` lands in
  `CH^i(X) ⊗ 𝐐`.
* `Stacks.Chow.codimensionToRationalChow_fundamentalClass` — the image of `∑_d [X_d]_d` is `[X]`.

## References

* [Stacks Project, Section 0FE2](https://stacks.math.columbia.edu/tag/0FE2)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart includePart)

variable (k : Type u) [Field k]

/-- **On a scheme of constant dimension `d` over `k`, `dim 𝒪_{T,t} = d - δ(t)`**, with
`δ(t) ≤ d`: the local dimension `d` at `t` is the dimension of the closure of `t`, which is
`δ(t)`, plus the dimension of the local ring (Stacks 0A21, Stacks 02QO). -/
theorem ringKrullDim_stalk_of_relativeDimension {T : Scheme.{u}} (q : T ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {d : ℕ} (h : AlgebraicGeometry.RelativeDimension q d) (t : T) :
    (relativeDimension (fieldChowSituation k).dimensionFunction q t).toNat ≤ d ∧
      ringKrullDim (T.presheaf.stalk t) =
        ((d - (relativeDimension (fieldChowSituation k).dimensionFunction q t).toNat : ℕ) :
          WithBot ℕ∞) := by
  have : Nonempty T := ⟨t⟩
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨heq, hdim⟩ :=
    AlgebraicGeometry.equidimensional_and_topologicalKrullDim_of_relativeDimension k q d h
  have h1 := topologicalKrullDimAt_eq_of_equidimensional k T q heq hdim t
  have h2 := AlgebraicGeometry.topologicalKrullDimAt_eq_add_ringKrullDim_stalk k q t
  rw [h1, topologicalKrullDim_closure_singleton_eq k q t] at h2
  obtain ⟨j, hj⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
    (T.presheaf.stalk t)
  rw [hj] at h2 ⊢
  have h3 : d = (relativeDimension (fieldChowSituation k).dimensionFunction q t).toNat + j := by
    exact_mod_cast h2
  refine ⟨by omega, ?_⟩
  rw [show j = d - (relativeDimension (fieldChowSituation k).dimensionFunction q t).toNat by
    omega]

variable {k} {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
  [Smooth sX]

omit [LocallyOfFiniteType sX] in
/-- **On the part `X_d` of a smooth `X`, `dim 𝒪_{X,y} = d - δ(y)`**, with `δ(y) ≤ d`. -/
theorem ringKrullDim_stalk_of_mem_dimPart {d : ℕ} {y : X} (hy : y ∈ dimPart sX d) :
    (relativeDimension (fieldChowSituation k).dimensionFunction sX y).toNat ≤ d ∧
      ringKrullDim (X.presheaf.stalk y) =
        ((d - (relativeDimension (fieldChowSituation k).dimensionFunction sX y).toNat : ℕ) :
          WithBot ℕ∞) := by
  let t : (dimPart sX d).toScheme := ⟨y, hy⟩
  have := ringKrullDim_stalk_of_relativeDimension k (partBase sX d)
    (relativeDimension_partBase sX d) t
  rw [relativeDimension_opensι_comp] at this
  rw [← ringKrullDim_eq_of_ringEquiv ((dimPart sX d).stalkIso t).commRingCatIsoToRingEquiv]
  exact this

/-- **A class of `CH^i(X) = ∏_d CH_{d-i}(X_d)` lands in `CH^i(X) ⊗ 𝐐`.** Its image in
`CH_*(X) ⊗ 𝐐` is a sum of pushforwards from the parts `X_d` of classes of dimension `d - i`, which
are combinations of the classes of integral closed subschemes `Z ⊆ X_d` of dimension `d - i`;
their generic points have local rings of dimension `i`. -/
theorem codimensionToRationalChow_mem_codimensionChowSubmodule [CompactSpace X] (i : ℕ)
    (a : codimensionChowGroup k sX i) :
    haveI := isNoetherian_of_compactSpace sX
    codimensionToRationalChow k sX i a ∈
      codimensionChowSubmodule (fieldChowSituation k) sX i := by
  have := isNoetherian_of_compactSpace sX
  rw [codimensionToRationalChow_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  rw [← DirectSum.lof_eq_of ℚ, rationalIncludePart_lof, includePart, LinearMap.baseChange_tmul,
    AddMonoidHom.coe_toIntLinearMap, DirectSum.lof_eq_of]
  have hcl := properChowPushforward_mem_closure_integralComponentAt (fieldChowSituation k) sX
    (partBase sX d) (dimPart sX d).ι rfl ((d : ℤ) - i) (properPushforwardDescends _ _ _ _ _ _)
    (a d)
  refine Submodule.span_mono (Set.image_mono ?_) (of_tmul_mem_span_integralComponentRationalClass
    (fieldChowSituation k) sX 1 (fun y hy => hy.2) hcl)
  rintro y ⟨⟨t, rfl⟩, hδ⟩
  have hy : (dimPart sX d).ι.base t ∈ dimPart sX d := t.2
  obtain ⟨hle, hdim⟩ := ringKrullDim_stalk_of_mem_dimPart sX hy
  have h0 := relativeDimension_fieldChowSituation_nonneg k sX ((dimPart sX d).ι.base t)
  rw [hδ] at hle hdim h0
  rw [Set.mem_setOf_eq, hdim]
  congr 1
  omega

/-- Transport along an equality of degrees does not change a rational class. -/
theorem directSum_of_one_tmul_chowGroupDegreeEquiv {T : Scheme.{u}}
    (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] {i j : ℤ} (h : i = j)
    (x : chowGroup (fieldChowSituation k) sT i) :
    DirectSum.of (fun m : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sT m) j
        ((1 : ℚ) ⊗ₜ[ℤ] chowGroupDegreeEquiv _ _ h x) =
      DirectSum.of (fun m : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sT m) i
        ((1 : ℚ) ⊗ₜ[ℤ] x) := by
  subst h
  rfl

/-- **The image of the fundamental class `∑_d [X_d]_d ∈ CH^0(X)` in `CH_*(X) ⊗ 𝐐` is `[X]`**: both
restrict to `[X_d]` on every part. -/
theorem codimensionToRationalChow_fundamentalClass [CompactSpace X] :
    haveI := isNoetherian_of_compactSpace sX
    codimensionToRationalChow k sX 0 (fun d ↦ chowGroupDegreeEquiv _ _ (sub_zero (d : ℤ)).symm
        (fundamentalChowClass (fieldChowSituation k) (partBase sX d) d)) =
      rationalFundamentalClass (fieldChowSituation k) sX := by
  have := isNoetherian_of_compactSpace sX
  conv_rhs => rw [← sum_rationalIncludePart_rationalRestrictPart k sX
    (rationalFundamentalClass (fieldChowSituation k) sX)]
  rw [codimensionToRationalChow_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [rationalRestrictPart_rationalFundamentalClass,
    rationalFundamentalClass_eq_of_relativeDimension k (partBase sX d)
      (relativeDimension_partBase sX d), directSum_of_one_tmul_chowGroupDegreeEquiv]

end Stacks.Chow

end
