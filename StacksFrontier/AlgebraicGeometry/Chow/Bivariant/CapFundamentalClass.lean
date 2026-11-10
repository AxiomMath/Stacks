module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport

/-!
# Capping a bivariant class with the fundamental class of the target

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` with `Y` Noetherian. The fundamental cycle of
`Y` is the cycle `[Y] = ∑_Z m_Z [Z]` associated to `Y` as a closed subscheme of itself (Stacks
02QU), the sum running over the irreducible components `Z` of `Y` and `m_Z` being the length of
the local ring at the generic point of `Z`; its part in delta-dimension `n` is `[Y]_n`. As `Y`
has finitely many irreducible components, only finitely many `[Y]_n` are nonzero, so the classes
of the `[Y]_n` assemble into an element of `CH_*(Y) = ⨁_n CH_n(Y)`.

A bivariant class `c ∈ A^p(X ⟶ Y)` caps that element:

  `c ∩ [Y] = ∑_n c ∩ [Y]_n ∈ ⨁_n CH_{n-p}(X)`,

the cap operation on the test scheme `Y ⟶ Y` landing in `CH_{n-p}(X ×_Y Y)`, which is identified
with `CH_{n-p}(X)` by proper pushforward along the isomorphism `X ×_Y Y ⟶ X`. With rational
coefficients this is the map `A^p(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, `c ↦ c ∩ [Y]`, of Proposition
42.57.1 (Stacks 0FEW).

## Main definitions

* `Stacks.Chow.fundamentalClassDegrees` — the finite set of the delta-dimensions of the
  irreducible components of `Y`.
* `Stacks.Chow.totalFundamentalClass` — `[Y] = ∑_n [Y]_n ∈ ⨁_n CH_n(Y)`.
* `Stacks.Chow.capFundamentalClassAt` — `c ↦ c ∩ [Y]_n`, read in `CH_{n-p}(X)`.
* `Stacks.Chow.capFundamentalClass` — `c ↦ c ∩ [Y] ∈ ⨁_j CH_j(X)`.
* `Stacks.Chow.rationalCapFundamentalClass` — its base change
  `A^p(X ⟶ Y) ⊗ 𝐐 ⟶ ⨁_j CH_j(X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees` — `[Y]_n = 0` unless
  `n` is the delta-dimension of an irreducible component of `Y`.
* `Stacks.Chow.capFundamentalClass_apply`, `Stacks.Chow.rationalCapFundamentalClass_tmul` — the
  values.

## Implementation notes

Stacks defines the fundamental class only for `Y` locally equidimensional (Remark 42.42.4, Stacks
0FE4), as `[Y] = ∑_n [Y_n]_n` for the decomposition `Y = ∐ Y_n` into open and closed pieces whose
irreducible components all have delta-dimension `n`. Each component of `Y` lies in exactly one
piece and has the same multiplicity there, so this is the cycle `[Y]` used here; taking the
associated cycle needs neither the decomposition nor the hypothesis.

## References

* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Degrees

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The delta-dimensions of the irreducible components of `Y`: the values of `δ_{Y/S}` at the
generic points of `Y`. -/
def fundamentalClassDegrees : Set ℤ :=
  relativeDimension C.dimensionFunction sY '' genericPoints Y

omit [LocallyOfFiniteType sY] in
/-- The set of delta-dimensions of the irreducible components of a Noetherian scheme is
finite. -/
theorem fundamentalClassDegrees_finite [IsNoetherian Y] : (fundamentalClassDegrees C sY).Finite :=
  (genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).image _

/-- The part `[Y]_n` of the fundamental cycle vanishes unless `n` is the delta-dimension of an
irreducible component of `Y`. -/
theorem fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees {n : ℤ}
    (hn : n ∉ fundamentalClassDegrees C sY) : fundamentalCycle C sY n = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero C sY (𝟙 Y) n x ?_
  rintro ⟨ξ, hξ, hdim⟩
  exact hn ⟨ξ.1, ξ.2, by simpa [← hξ] using hdim⟩

/-- **The fundamental class `[Y] = ∑_n [Y]_n ∈ CH_*(Y)`** of a Noetherian scheme locally of finite
type over the base. -/
def totalFundamentalClass [IsNoetherian Y] : DirectSum ℤ fun n => chowGroup C sY n :=
  ∑ n ∈ (fundamentalClassDegrees_finite C sY).toFinset,
    DirectSum.of (fun n => chowGroup C sY n) n (fundamentalChowClass C sY n)

/-- The degree `n` part of `[Y]` is the class of `[Y]_n`. -/
theorem totalFundamentalClass_apply [IsNoetherian Y] (n : ℤ) :
    totalFundamentalClass C sY n = fundamentalChowClass C sY n := by
  classical
  rw [totalFundamentalClass, DFinsupp.finsetSum_apply]
  by_cases hn : n ∈ fundamentalClassDegrees C sY
  · refine (Finset.sum_eq_single_of_mem n
      ((fundamentalClassDegrees_finite C sY).mem_toFinset.2 hn) fun m _ hmn => ?_).trans ?_
    · exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm hmn)
    · exact DirectSum.of_eq_same _ _
  · rw [Finset.sum_eq_zero fun m hm => DirectSum.of_eq_of_ne _ _ _ fun hmn => hn
      (by rw [hmn]; exact (fundamentalClassDegrees_finite C sY).mem_toFinset.1 hm),
      fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sY hn,
      map_zero]

end Degrees

section Cap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- The identification `CH_k(X ×_Y Y) ≃ CH_k(X)` by proper pushforward along the first
projection, which is an isomorphism because the second leg of the fibre product is the
identity. -/
def chowGroupPullbackIdEquiv (k : ℤ) :
    chowGroup C (pullback.fst f (𝟙 Y) ≫ sX) k ≃+ chowGroup C sX k :=
  chowGroupEquivOfIso C (pullback.fst f (𝟙 Y) ≫ sX) sX (pullback.fst f (𝟙 Y)) rfl k

/-- Cap product with `[Y]_n`, `c ↦ c ∩ [Y]_n ∈ CH_{n-p}(X)`: the cap operation of `c` on the
test scheme `Y ⟶ Y`, read on `X` through `Stacks.Chow.chowGroupPullbackIdEquiv`. -/
def capFundamentalClassAt (n : ℤ) :
    BivariantClass C G sX sY f hf p →+ chowGroup C sX (n - p) where
  toFun c := chowGroupPullbackIdEquiv C sX f (n - p)
    (c.cap (𝟙 Y) n (fundamentalChowClass C (𝟙 Y ≫ sY) n))
  map_zero' := map_zero (chowGroupPullbackIdEquiv C sX f (n - p))
  map_add' _ _ := map_add (chowGroupPullbackIdEquiv C sX f (n - p)) _ _

/-- The value of `c ∩ [Y]_n` is the cap of `c` with `[Y]_n` on the test scheme `Y ⟶ Y`,
transported to `CH_{n-p}(X)` by `Stacks.Chow.chowGroupPullbackIdEquiv`. -/
@[simp]
theorem capFundamentalClassAt_apply (n : ℤ) (c : BivariantClass C G sX sY f hf p) :
    capFundamentalClassAt C G sX sY f hf p n c = chowGroupPullbackIdEquiv C sX f (n - p)
      (c.cap (𝟙 Y) n (fundamentalChowClass C (𝟙 Y ≫ sY) n)) :=
  rfl

/-- **Cap product with the fundamental class of the target**, `c ↦ c ∩ [Y] = ∑_n c ∩ [Y]_n`, for
`c ∈ A^p(X ⟶ Y)` and `Y` Noetherian, with values in `CH_*(X) = ⨁_j CH_j(X)`. -/
def capFundamentalClass [IsNoetherian Y] :
    BivariantClass C G sX sY f hf p →+ DirectSum ℤ fun j => chowGroup C sX j :=
  ∑ n ∈ (fundamentalClassDegrees_finite C sY).toFinset,
    (DirectSum.of (fun j => chowGroup C sX j) (n - p)).comp
      (capFundamentalClassAt C G sX sY f hf p n)

/-- `c ∩ [Y]` is the sum over the degrees `n` of `[Y]` of `c ∩ [Y]_n`, placed in degree
`n - p` of `CH_*(X)`. -/
theorem capFundamentalClass_apply [IsNoetherian Y] (c : BivariantClass C G sX sY f hf p) :
    capFundamentalClass C G sX sY f hf p c =
      ∑ n ∈ (fundamentalClassDegrees_finite C sY).toFinset,
        DirectSum.of (fun j => chowGroup C sX j) (n - p)
          (capFundamentalClassAt C G sX sY f hf p n c) := by
  simp [capFundamentalClass]

/-- **The map `A^p(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, `c ↦ c ∩ [Y]`**, of Proposition 42.57.1: the base
change to `𝐐` of `Stacks.Chow.capFundamentalClass`, with `CH_*(X) ⊗ 𝐐` written as
`⨁_j CH_j(X) ⊗ 𝐐`. -/
def rationalCapFundamentalClass [IsNoetherian Y] :
    TensorProduct ℤ ℚ (BivariantClass C G sX sY f hf p) →ₗ[ℚ]
      DirectSum ℤ fun j => TensorProduct ℤ ℚ (chowGroup C sX j) :=
  (TensorProduct.directSumRight ℤ ℚ ℚ fun j => chowGroup C sX j).toLinearMap ∘ₗ
    (capFundamentalClass C G sX sY f hf p).toIntLinearMap.baseChange ℚ

/-- On a pure tensor `q ⊗ c`, the rational cap map is the sum over the degrees `n` of `[Y]` of
`q ⊗ (c ∩ [Y]_n)`, placed in degree `n - p` of `⨁_j CH_j(X) ⊗ 𝐐`. -/
theorem rationalCapFundamentalClass_tmul [IsNoetherian Y] (q : ℚ)
    (c : BivariantClass C G sX sY f hf p) :
    rationalCapFundamentalClass C G sX sY f hf p (q ⊗ₜ[ℤ] c) =
      ∑ n ∈ (fundamentalClassDegrees_finite C sY).toFinset,
        DirectSum.of (fun j => TensorProduct ℤ ℚ (chowGroup C sX j)) (n - p)
          (q ⊗ₜ[ℤ] capFundamentalClassAt C G sX sY f hf p n c) := by
  rw [rationalCapFundamentalClass, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    AddMonoidHom.coe_toIntLinearMap, capFundamentalClass_apply, TensorProduct.tmul_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => TensorProduct.directSumRight_tmul_lof ℤ ℚ q (n - p) _

end Cap

end Stacks.Chow

end
