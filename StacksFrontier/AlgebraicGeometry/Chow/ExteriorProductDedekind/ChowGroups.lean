module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Cycles

/-!
# The exterior product on Chow groups over a Dedekind base

Let `(S, δ)` be as in Stacks section 42.63: locally the spectrum of a Dedekind domain, with
`δ(s) = 0` at the closed points and `δ(s) = 1` elsewhere. For `X` and `Y` locally of finite type
over `S`, Stacks 0FC4 asserts that the exterior product descends to a well defined map

  `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`.

Given that the cycle-level exterior product `Stacks.Chow.exteriorProductDedekindCycles` carries
rational equivalences to rational equivalences in each variable
(`Stacks.Chow.ExteriorProductFactorsThroughRationalEquivalence`), it descends to a bilinear map on
Chow groups and hence to a map out of the tensor product `CH_n(X) ⊗_ℤ CH_m(Y)`.

## Main definitions

* `Stacks.Chow.ExteriorProductFactorsThroughRationalEquivalence` — compatibility of the
  cycle-level exterior product with rational equivalence, separately in each variable.
* `Stacks.Chow.exteriorProductDedekindChow` — the induced bilinear map
  `CH_n(X) ⟶ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`.
* `Stacks.Chow.exteriorProductDedekindTensor` — the map
  `CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`.

## Main results

* `Stacks.Chow.exteriorProductDedekindChow_mk_mk` — on the classes of two cycles the bilinear map
  is the class of their cycle-level exterior product.
* `Stacks.Chow.exteriorProductDedekindTensor_tmul` — the value on a pure tensor.

## References

* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

/-! ### Compatibility with rational equivalence -/

/-- The exterior product of cycles over a Dedekind base carries rational equivalences to
rational equivalences, separately in each variable. -/
def ExteriorProductFactorsThroughRationalEquivalence : Prop :=
  (∀ (α : CycleGroup C f n), ∀ β ∈ rationalEquivalences C g m,
      exteriorProductDedekindCycles C f g n m α β ∈
        rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1)) ∧
    (∀ (β : CycleGroup C g m), ∀ α ∈ rationalEquivalences C f n,
      exteriorProductDedekindCycles C f g n m α β ∈
        rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))

variable (hfac : ExteriorProductFactorsThroughRationalEquivalence C f g n m)

/-! ### Descent to Chow groups -/

/-- The exterior product with a fixed cycle on `X`, descended to the Chow group of `Y`. -/
def exteriorProductDedekindChowRight (α : CycleGroup C f n) :
    chowGroup C g m →+ chowGroup C (pullback.fst f g ≫ f) (n + m - 1) :=
  QuotientAddGroup.map (rationalEquivalences C g m)
    (rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))
    (exteriorProductDedekindCycles C f g n m α) fun β hβ ↦ hfac.1 α β hβ

/-- On the class of a cycle, the exterior product with a fixed cycle on `X` is the class of the
cycle-level exterior product. -/
@[simp]
theorem exteriorProductDedekindChowRight_mk (α : CycleGroup C f n) (β : CycleGroup C g m) :
    exteriorProductDedekindChowRight C f g n m hfac α
        (QuotientAddGroup.mk' (rationalEquivalences C g m) β) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))
        (exteriorProductDedekindCycles C f g n m α β) :=
  rfl

/-- The exterior product as a homomorphism from the cycle group of `X` to the group of
homomorphisms out of the Chow group of `Y`. -/
def exteriorProductDedekindChowAux :
    CycleGroup C f n →+
      (chowGroup C g m →+ chowGroup C (pullback.fst f g ≫ f) (n + m - 1)) where
  toFun α := exteriorProductDedekindChowRight C f g n m hfac α
  map_zero' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    induction x using QuotientAddGroup.induction_on with
    | H β =>
      change QuotientAddGroup.mk' _ (exteriorProductDedekindCycles C f g n m 0 β) = 0
      rw [map_zero]
      exact map_zero _
  map_add' α α' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    induction x using QuotientAddGroup.induction_on with
    | H β =>
      change QuotientAddGroup.mk' _ (exteriorProductDedekindCycles C f g n m (α + α') β) = _
      rw [map_add]
      exact map_add _ _ _

/-- The exterior product on Chow groups over a Dedekind base, as a bilinear map
`CH_n(X) ⟶ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`. -/
def exteriorProductDedekindChow :
    chowGroup C f n →+
      (chowGroup C g m →+ chowGroup C (pullback.fst f g ≫ f) (n + m - 1)) :=
  QuotientAddGroup.lift (rationalEquivalences C f n)
    (exteriorProductDedekindChowAux C f g n m hfac) fun α hα ↦ by
      refine AddMonoidHom.ext fun x ↦ ?_
      induction x using QuotientAddGroup.induction_on with
      | H β =>
        change QuotientAddGroup.mk' _ (exteriorProductDedekindCycles C f g n m α β) = 0
        exact (QuotientAddGroup.eq_zero_iff _).2 (hfac.2 β α hα)

/-- On the classes of two cycles the exterior product on Chow groups is the class of their
cycle-level exterior product. -/
@[simp]
theorem exteriorProductDedekindChow_mk_mk (α : CycleGroup C f n) (β : CycleGroup C g m) :
    exteriorProductDedekindChow C f g n m hfac
        (QuotientAddGroup.mk' (rationalEquivalences C f n) α)
        (QuotientAddGroup.mk' (rationalEquivalences C g m) β) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))
        (exteriorProductDedekindCycles C f g n m α β) :=
  rfl

/-! ### The map out of the tensor product -/

/-- The exterior product over a Dedekind base as a map out of the tensor product,

  `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m-1}(X ×_S Y)`,

determined by `[X'] ⊗ [Y'] ↦ [X' ×_S Y']_{n+m-1}` on integral closed subschemes `X' ⊆ X` and
`Y' ⊆ Y` of delta-dimensions `n` and `m` with one of them dominating an irreducible component of
the base, and by `[X'] ⊗ [Y'] ↦ 0` when neither does, given that the cycle-level exterior
product respects rational equivalence in each variable (`hfac`). -/
@[stacks 0FC4 "the map CH_n(X) ⊗_ℤ CH_m(Y) → CH_{n+m-1}(X ×_S Y) is well defined, given \
that the cycle-level exterior product carries rational equivalences to rational equivalences \
in each variable (the step the source proves with the bivariant classes of Stacks 0B78, 0B79 \
and 0B75, none of which is in this repository)"]
def exteriorProductDedekindTensor :
    TensorProduct ℤ (chowGroup C f n) (chowGroup C g m) →+
      chowGroup C (pullback.fst f g ≫ f) (n + m - 1) :=
  (TensorProduct.lift
    ((addMonoidHomLequivInt
        (A := chowGroup C g m)
        (B := chowGroup C (pullback.fst f g ≫ f) (n + m - 1)) ℤ).toLinearMap.comp
      (exteriorProductDedekindChow C f g n m hfac).toIntLinearMap)).toAddMonoidHom

/-- The value of the exterior product on a pure tensor of two Chow classes. -/
@[simp]
theorem exteriorProductDedekindTensor_tmul (a : chowGroup C f n) (b : chowGroup C g m) :
    exteriorProductDedekindTensor C f g n m hfac (TensorProduct.tmul ℤ a b) =
      exteriorProductDedekindChow C f g n m hfac a b :=
  rfl

/-- The value of the exterior product on the pure tensor of the classes of two cycles is the
class of their cycle-level exterior product. -/
@[simp]
theorem exteriorProductDedekindTensor_tmul_mk (α : CycleGroup C f n) (β : CycleGroup C g m) :
    exteriorProductDedekindTensor C f g n m hfac
        (TensorProduct.tmul ℤ (QuotientAddGroup.mk' (rationalEquivalences C f n) α)
          (QuotientAddGroup.mk' (rationalEquivalences C g m) β)) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f g ≫ f) (n + m - 1))
        (exteriorProductDedekindCycles C f g n m α β) :=
  rfl

end Stacks.Chow

end
