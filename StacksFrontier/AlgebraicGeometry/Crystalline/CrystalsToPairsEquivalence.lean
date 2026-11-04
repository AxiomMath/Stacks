module

public import Mathlib.CategoryTheory.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsToPairs

/-!
# Towards [Stacks, Tag 07JH]: the quasi-inverse of the functor to pairs `(M, ∇)`

[Stacks, Tag 07JH] asserts that the functor of [Stacks, Tag 07JG], from the crystals in
quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the pairs `(M, ∇)` satisfying its four
items (07JB), (07JC), (07JD) and (07JE), is an **equivalence of categories**.  The proof of
the tag runs in the other direction: given `(M, ∇)`, write `∇ m = ∑ θ_i(m) d x_i`, put
`θ_K = ∏ θ_i^{k_i}`, and for two divided power maps `f, g : D → B` agreeing modulo the divided
power ideal of `B` define the *Taylor comparison*

`c_{f,g} : M ⊗_{D,f} B → M ⊗_{D,g} B`,  `m ⊗ 1 ↦ ∑_K θ_K(m) ⊗ ∏ ξ_i^{[k_i]}`,

with `ξ_i = f(x_i) - g(x_i)`,
which is a finite sum because `∇` is topologically quasi-nilpotent, and satisfies `c_{f,f} = 1`
and `c_{g,h} ∘ c_{f,g} = c_{f,h}`; the crystal is then `T ↦ M ⊗_{D,f} B`.

This file carries out the **first-order part** of that construction — the part of the Taylor
series with `∑ k_i ≤ 1` — and draws the consequences for the functor this library has for
[Stacks, Tag 07JG], namely `Crystalline.firstOrderCrystalsToPairs`.  Over the first-order
thickening `D ⊕ Ω` of [Stacks, Tag 07J2] the Taylor comparison is just

`ε m = 1 ⊗ m + ι(∇ m)`,  `ι : Ω ⊗_D M → (D ⊕ Ω) ⊗_D M`,

and the content of this file is that this is a bijection between the comparison data of
`Crystalline.FirstOrderComparison` and the connections `∇ : M → Ω ⊗_D M`: the crystal structure
on the first-order thickening *is* the connection, with no information lost either way.

## Main definitions

* `Crystalline.firstOrderInclusion` — the inclusion `ι : Ω ⊗_D M → (D ⊕ Ω) ⊗_D M` of the
  square-zero summand.
* `Crystalline.FirstOrderConnection` — an additive map `∇ : M → Ω ⊗_D M` obeying the Leibniz
  rule `∇ (f m) = f ∇ m + d f ⊗ m` for a map `d : D → Ω`.  This is the uncompleted companion of
  `Crystalline.CompletedConnection`, which takes values in `M ⊗̂_D Ω`.
* `Crystalline.FirstOrderComparison.toFirstOrderConnection` and
  `Crystalline.FirstOrderComparison.ofConnection` — the two directions of the correspondence.
* `Crystalline.firstOrderComparisonEquivConnection` — **the first-order quasi-inverse**: the
  resulting bijection between comparison data and connections.
* `Crystalline.pairIsoOfNablaEq` — a pair assembled from a connection equal to that of `P` is
  isomorphic to `P`.

## Main results

* `Crystalline.firstOrderTensor_eq_add` and `Crystalline.firstOrderTensor_ext` — the splitting
  `(D ⊕ Ω) ⊗_D M ≅ M ⊕ (Ω ⊗_D M)` of a section over the first-order thickening into its
  reduction and its differential component, and the extensionality principle it gives.
* `Crystalline.firstOrderCrystalsToPairs_faithful` — **the functor of
  `Crystalline.firstOrderCrystalsToPairs` is faithful**, with no hypotheses.
* `Crystalline.firstOrderCrystalsToPairs_full_of_injective` — it is **full** as soon as the
  canonical map `M ⊗_D Ω → M ⊗̂_D Ω` is injective on the modules of its source.
* `Crystalline.exists_firstOrderConnection_of_bijective` — when that canonical map is bijective,
  the connection of a pair comes from the uncompleted tensor product.
* `Crystalline.firstOrderCrystalsToPairs_essSurj_of_exists_lift` — it is **essentially
  surjective** as soon as the connection of every pair comes from the uncompleted tensor
  product.
* `Crystalline.firstOrderCrystalsToPairs_isEquivalence` — the three together: an **equivalence
  of categories under two explicit hypotheses**.

## What is and is not proved

[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; **no `@[stacks 07JH]`
attribute is placed in this
file.**  Neither declaration here states 07JH — the source of this file's functor is the
first-order comparison data over `D` of `Crystalline.FirstOrderCrystal`, not the crystals in
quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`, and the equivalence below carries two hypotheses
that are not discharged here and are not expected to hold when the index set is infinite.  What
is proved is stated with no hypotheses:

* the splitting of `(D ⊕ Ω) ⊗_D M` and the bijection
  `Crystalline.firstOrderComparisonEquivConnection` between first-order comparison data and
  connections `M → Ω ⊗_D M`.  This is the first-order case of the construction that the proof of
  [Stacks, Tag 07JH] performs over every affine object of `Cris(X/S)`, and it is complete: both
  round trips are proved, in `Crystalline.FirstOrderComparison.ofConnection_connection` and in
  the `left_inv` field of the equivalence;
* faithfulness of `Crystalline.firstOrderCrystalsToPairs`.

Everything else is **conditional**, on the two hypotheses of
`Crystalline.firstOrderCrystalsToPairs_isEquivalence`:

1. `hinj`, injectivity of the canonical map `M ⊗_D Ω → M ⊗̂_D Ω` on the modules of the source
   category, which is what turns horizontality of a map of pairs — an identity in the completion
   — back into compatibility with the comparison data;
2. `hlift`, the requirement that the connection of a pair factor through `M ⊗_D Ω`.  By
   `Crystalline.exists_firstOrderConnection_of_bijective` this follows from bijectivity of the
   same canonical map.

Neither hypothesis is discharged here, and **nothing below shows that either holds in the
situation of [Stacks, Tag 07JH]**, where `Ω = Ω_D` is the `p`-adic completion of the free module
on the differentials `d x_i`.  They are conditions on the completion `M ⊗̂_D Ω` alone, not on the
crystalline situation.

[Stacks, Tag 07JH] itself is `...SmallSite.crystalPairFunctor_isEquivalence`, for the functor
`...SmallSite.crystalPairFunctor` out of the crystals in quasi-coherent modules; it does not go
through this file.  Three further differences separate the algebraic route of this file from the
tag, the same ones as for [Stacks, Tag 07JG] and `Crystalline.firstOrderCrystalsToPairs`:

* the source of `Crystalline.firstOrderCrystalsToPairs` is `Crystalline.FirstOrderCrystal`, the
  first-order comparison data over `D`, and **not** the crystals in quasi-coherent
  `𝒪_{X/S}`-modules on `Cris(X/S)`.  Reducing such a crystal to that datum needs the levels of
  [Stacks, Tag 07JN] and the sections of a pullback of sheaves of modules as a base change.  The
  levels are `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem`, `D(n)` is the
  limit of their section rings by `...SmallSite.envelopeLevelRingLimitEquiv`, and the module
  `M = lim_e Γ(T_e, ℱ)` over them is built, with its `D`-action and its functoriality, by
  `...SmallSite.LevelComparison07JG.functor`.  The base change is available from the
  presheaf-level crystal condition and not from the sheaf-level one;
* three of the four items (07JB)–(07JE) are *carried* as fields of
  `Crystalline.FirstOrderCrystal`, the source of the functor below, rather than derived from the
  crystal.  They are not fields of the source of the other algebraic functor: the source of
  `Crystalline.taylorCrystalsToPairs` is `Crystalline.TaylorCrystal`, which has the tower of
  levels and the composite coordinate operators in their place, and (07JB), (07JD) and (07JE) are
  theorems about it.  Those data are the source's own input and are not read off a crystal on
  `Cris(X/S)`;
* the Taylor comparison in degrees `∑ k_i ≥ 2`, the divided power coefficients
  `∏ ξ_i^{[k_i]}`, the convergence of the series and the cocycle identity
  `c_{g,h} ∘ c_{f,g} = c_{f,h}` do not appear **below**, and the quasi-nilpotence hypothesis
  (07JE) — which is what makes the series finite — is not used below.  The coefficients are
  `Crystalline.taylorMonomial`; the comparison `c_{f,g}` is
  `Crystalline.SecondDividedPowerMap.comparison`, inhabited over a divided power polynomial
  algebra by `Crystalline.exists_isTwistedTaylorComparison_dividedPowerPolynomial`, and Taylor's
  formula itself is `Crystalline.taylorFormula_polynomial`; the convergence is
  `Crystalline.exists_hasTaylorSum`, which uses (07JE); and the cocycle identity is proved at the
  level of the sums, for the tag's own three maps, as
  `Crystalline.hasTaylorSum_taylorComposite_diff`.

  None of those mentions `Crystalline.FirstOrderCrystal`, `...SmallSite.QuasiCoherentCrystal` or
  `...SmallSite.Reduction07JG`: their subject is one series in one module over two abstract
  divided power rings, with the operators `θ_i` carried as `Crystalline.IsThetaMonomialFamily`
  data rather than read off a crystal.  The assignment `T ↦ M ⊗_{D,f} B` of the source's proof,
  as a functor out of the pairs into crystals on `Cris(X/S)`, is the quasi-inverse
  `...SmallSite.pairCrystalFunctor`, built by descent of the Taylor stratification.

## Implementation notes

The correspondence is stated as an `Equiv` of types rather than as an equivalence of categories,
because the categorical statement would need a category of pairs with an *uncompleted*
connection, and the target of [Stacks, Tag 07JG] is the completed one; the passage between the
two is exactly the conditional part above.

`Crystalline.FirstOrderConnection` is parametrized by a bare map `d : D → Ω`, as
`Crystalline.CompletedConnection` is, so that it can be read against the derivation of a
divided power ring through `Crystalline.derivationFun`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w uA uI uM

namespace Crystalline

/-! ### The splitting of a section over the first-order thickening -/

section Splitting

variable (D : DividedPowerRing.{u}) (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] (M : Type w) [AddCommGroup M] [Module D M]
  (N : Type w) [AddCommGroup N] [Module D N]

/-- **The inclusion `ι : Ω ⊗_D M → (D ⊕ Ω) ⊗_D M`** of the square-zero summand of the
first-order thickening, tensored with `M`.  Together with `1 ⊗ (-)` it splits a section over the
first-order thickening; see `Crystalline.firstOrderTensor_eq_add`. -/
public noncomputable def firstOrderInclusion :
    (Omega ⊗[D] M) →ₗ[D] (firstOrderExtension D Omega ⊗[D] M) :=
  LinearMap.rTensor M (TrivSqZeroExt.inrHom (D : Type u) Omega)

/-- The inclusion sends `ω ⊗ m` to `(0, ω) ⊗ m`. -/
@[simp] public theorem firstOrderInclusion_tmul (omega : Omega) (m : M) :
    firstOrderInclusion D Omega M (omega ⊗ₜ[D] m) =
      (TrivSqZeroExt.inr omega : firstOrderExtension D Omega) ⊗ₜ[D] m := by
  simp [firstOrderInclusion]

/-- The reduction of a section in the square-zero summand vanishes. -/
@[simp] public theorem firstOrderReduction_firstOrderInclusion (z : Omega ⊗[D] M) :
    firstOrderReduction D Omega M (firstOrderInclusion D Omega M z) = 0 := by
  refine LinearMap.congr_fun
    (f := firstOrderReduction D Omega M ∘ₗ firstOrderInclusion D Omega M) (g := 0)
    (TensorProduct.ext' fun omega m => by simp) z

/-- The differential component recovers a section of the square-zero summand. -/
@[simp] public theorem firstOrderDifferentialPart_firstOrderInclusion (z : Omega ⊗[D] M) :
    firstOrderDifferentialPart D Omega M (firstOrderInclusion D Omega M z) = z := by
  refine LinearMap.congr_fun
    (f := firstOrderDifferentialPart D Omega M ∘ₗ firstOrderInclusion D Omega M) (g := .id)
    (TensorProduct.ext' fun omega m => by simp) z

/-- Taking the reduction commutes with a `D`-linear map of the module. -/
public theorem firstOrderReduction_lTensor (phi : M →ₗ[D] N)
    (z : firstOrderExtension D Omega ⊗[D] M) :
    firstOrderReduction D Omega N
        (LinearMap.lTensor (firstOrderExtension D Omega) phi z) =
      phi (firstOrderReduction D Omega M z) := by
  refine LinearMap.congr_fun
    (f := firstOrderReduction D Omega N ∘ₗ LinearMap.lTensor (firstOrderExtension D Omega) phi)
    (g := phi ∘ₗ firstOrderReduction D Omega M)
    (TensorProduct.ext' fun a m => by simp) z

/-- **The splitting of a section over the first-order thickening.**  Every element of
`(D ⊕ Ω) ⊗_D M` is the sum of `1 ⊗ (-)` applied to its reduction and of the inclusion of its
differential component, so `(D ⊕ Ω) ⊗_D M` is `M ⊕ (Ω ⊗_D M)`. -/
public theorem firstOrderTensor_eq_add (z : firstOrderExtension D Omega ⊗[D] M) :
    z = (1 : firstOrderExtension D Omega) ⊗ₜ[D] firstOrderReduction D Omega M z +
      firstOrderInclusion D Omega M (firstOrderDifferentialPart D Omega M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      have h : a.fst • (1 : firstOrderExtension D Omega) +
          (TrivSqZeroExt.inr a.snd : firstOrderExtension D Omega) = a := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp
      rw [firstOrderReduction_tmul, firstOrderDifferentialPart_tmul, firstOrderInclusion_tmul,
        ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, h]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add]
      conv_lhs => rw [hx, hy]
      abel

/-- **Extensionality for sections over the first-order thickening**: two of them agreeing on
their reduction and on their differential component are equal. -/
public theorem firstOrderTensor_ext {z w : firstOrderExtension D Omega ⊗[D] M}
    (hr : firstOrderReduction D Omega M z = firstOrderReduction D Omega M w)
    (hd : firstOrderDifferentialPart D Omega M z = firstOrderDifferentialPart D Omega M w) :
    z = w :=
  (firstOrderTensor_eq_add D Omega M z).trans
    (by rw [hr, hd]; exact (firstOrderTensor_eq_add D Omega M w).symm)

end Splitting

/-! ### Connections with values in the uncompleted tensor product -/

section Connections

variable (D : DividedPowerRing.{u}) (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  (dd : D → Omega)

/-- **A connection `∇ : M → Ω ⊗_D M` relative to a map `d : D → Ω`**: an additive map obeying
the Leibniz rule `∇ (f m) = f ∇ m + d f ⊗ m`.  This is the uncompleted companion of
`Crystalline.CompletedConnection`, whose values lie in the `p`-adic completion of `M ⊗_D Ω`; the
two differ by the canonical map to the completion, and that difference is the whole conditional
part of this file. -/
public structure FirstOrderConnection (M : Type w) [AddCommGroup M] [Module D M] where
  /-- The underlying map of a connection. -/
  toFun : M → Omega ⊗[D] M
  /-- A connection is additive. -/
  map_add' : ∀ m n : M, toFun (m + n) = toFun m + toFun n
  /-- The Leibniz rule for a connection. -/
  leibniz' : ∀ (f : D) (m : M), toFun (f • m) = f • toFun m + dd f ⊗ₜ[D] m

namespace FirstOrderConnection

variable {D Omega dd} {M : Type w} [AddCommGroup M] [Module D M]

/-- A connection coerces to its underlying function. -/
public instance : CoeFun (FirstOrderConnection D Omega dd M)
    (fun _ ↦ M → Omega ⊗[D] M) where
  coe nabla := nabla.toFun

/-- Connections are additive. -/
public theorem map_add (nabla : FirstOrderConnection D Omega dd M) (m n : M) :
    nabla (m + n) = nabla m + nabla n := nabla.map_add' m n

/-- The Leibniz rule for a connection. -/
public theorem leibniz (nabla : FirstOrderConnection D Omega dd M) (f : D) (m : M) :
    nabla (f • m) = f • nabla m + dd f ⊗ₜ[D] m := nabla.leibniz' f m

/-- Two connections agreeing on every element are equal. -/
@[ext] public theorem ext {nabla nabla' : FirstOrderConnection D Omega dd M}
    (h : ∀ m, nabla m = nabla' m) : nabla = nabla' := by
  cases nabla; cases nabla'; congr 1; exact funext h

end FirstOrderConnection

end Connections

/-! ### A first-order comparison datum is the same thing as a connection -/

section Comparison

variable (A : Type uA) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D)
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega]
  [IsCentralScalar D Omega] (d : DividedPowerDerivation A D g Omega)
  (M : Type w) [AddCommGroup M] [Module D M]

/-- Two first-order comparison data with the same underlying map are equal. -/
public theorem FirstOrderComparison.ext {c c' : FirstOrderComparison A D g Omega d M}
    (h : ∀ m, c m = c' m) : c = c' := by
  cases c; cases c'; congr 1; exact funext h

/-- **The connection of a first-order comparison datum**, bundled as a
`Crystalline.FirstOrderConnection`: the differential component of the comparison map, with the
Leibniz rule derived from semilinearity for `p₁` in
`Crystalline.FirstOrderComparison.connection_leibniz`. -/
public noncomputable def FirstOrderComparison.toFirstOrderConnection
    (c : FirstOrderComparison A D g Omega d M) :
    FirstOrderConnection D Omega (derivationFun A D g Omega d) M where
  toFun := c.connection
  map_add' := c.connection_add
  leibniz' := c.connection_leibniz

/-- Multiplying `1 ⊗ m` by `p₁ f = (f, d f)` gives `1 ⊗ f m` plus the inclusion of
`d f ⊗ m`: the first-order Taylor expansion of a scalar. -/
public theorem firstOrderP₁_smul_one_tmul (f : D) (m : M) :
    firstOrderP₁ A D g Omega d f • ((1 : firstOrderExtension D Omega) ⊗ₜ[D] m) =
      (1 : firstOrderExtension D Omega) ⊗ₜ[D] (f • m) +
        firstOrderInclusion D Omega M (derivationFun A D g Omega d f ⊗ₜ[D] m) := by
  have hp : firstOrderP₁ A D g Omega d f =
      f • (1 : firstOrderExtension D Omega) +
        (TrivSqZeroExt.inr (derivationFun A D g Omega d f) :
          firstOrderExtension D Omega) := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [derivationFun]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hp, TensorProduct.add_tmul,
    TensorProduct.smul_tmul, firstOrderInclusion_tmul]

/-- Multiplying a section of the square-zero summand by `p₁ f = (f, d f)` multiplies it by `f`:
the square-zero relation kills the differential term. -/
public theorem firstOrderP₁_smul_firstOrderInclusion (f : D) (z : Omega ⊗[D] M) :
    firstOrderP₁ A D g Omega d f • firstOrderInclusion D Omega M z =
      firstOrderInclusion D Omega M (f • z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero, smul_zero, map_zero]
  | tmul omega m =>
      have hm : firstOrderP₁ A D g Omega d f *
          (TrivSqZeroExt.inr omega : firstOrderExtension D Omega) =
            TrivSqZeroExt.inr (f • omega) := by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp
      have h1 : f • (omega ⊗ₜ[D] m) = (f • omega) ⊗ₜ[D] m :=
        TensorProduct.smul_tmul' f omega m
      have h2 : firstOrderP₁ A D g Omega d f •
          ((TrivSqZeroExt.inr omega : firstOrderExtension D Omega) ⊗ₜ[D] m) =
            (firstOrderP₁ A D g Omega d f •
              (TrivSqZeroExt.inr omega : firstOrderExtension D Omega)) ⊗ₜ[D] m :=
        TensorProduct.smul_tmul' _ _ _
      rw [firstOrderInclusion_tmul, h2, smul_eq_mul, hm, h1, firstOrderInclusion_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, smul_add, map_add]

/-- **The first-order quasi-inverse, on objects.**  A connection `∇ : M → Ω ⊗_D M` determines
the comparison datum `ε m = 1 ⊗ m + ι(∇ m)` of a crystal over the first-order thickening
`D ⊕ Ω` of [Stacks, Tag 07J2].  This is the part of the Taylor series of the proof of
[Stacks, Tag 07JH] in degrees `∑ k_i ≤ 1`; over the first-order thickening the higher degrees
vanish, so no quasi-nilpotence hypothesis is needed. -/
public noncomputable def FirstOrderComparison.ofConnection
    (nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) M) :
    FirstOrderComparison A D g Omega d M where
  toFun m := (1 : firstOrderExtension D Omega) ⊗ₜ[D] m +
    firstOrderInclusion D Omega M (nabla m)
  map_add' m n := by
    rw [nabla.map_add m n, _root_.map_add, TensorProduct.tmul_add]
    abel
  reduction' m := by
    rw [_root_.map_add, firstOrderReduction_tmul, firstOrderReduction_firstOrderInclusion,
      add_zero, TrivSqZeroExt.fst_one, one_smul]
  semilinear' f m := by
    rw [nabla.leibniz f m, _root_.map_add, smul_add, firstOrderP₁_smul_one_tmul,
      firstOrderP₁_smul_firstOrderInclusion]
    abel

/-- The comparison datum built from `∇` sends `m` to `1 ⊗ m + ι(∇ m)`. -/
@[simp] public theorem FirstOrderComparison.ofConnection_apply
    (nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) M) (m : M) :
    FirstOrderComparison.ofConnection A D g Omega d M nabla m =
      (1 : firstOrderExtension D Omega) ⊗ₜ[D] m +
        firstOrderInclusion D Omega M (nabla m) := rfl

/-- **The first round trip.**  The connection of the comparison datum built from `∇` is `∇`
again. -/
public theorem FirstOrderComparison.ofConnection_connection
    (nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) M) (m : M) :
    (FirstOrderComparison.ofConnection A D g Omega d M nabla).connection m = nabla m := by
  show firstOrderDifferentialPart D Omega M
      (FirstOrderComparison.ofConnection A D g Omega d M nabla m) = nabla m
  rw [FirstOrderComparison.ofConnection_apply, _root_.map_add,
    firstOrderDifferentialPart_tmul, firstOrderDifferentialPart_firstOrderInclusion,
    TrivSqZeroExt.snd_one, TensorProduct.zero_tmul, zero_add]

/-- **The first-order quasi-inverse.**  Over the first-order thickening `D ⊕ Ω` of
[Stacks, Tag 07J2], a comparison datum of a crystal in `𝒪_{X/S}`-modules is *the same thing as*
a connection `∇ : M → Ω ⊗_D M`: the datum is recovered from its differential component by
`ε m = 1 ⊗ m + ι(∇ m)`, and no information is lost in either direction.

This is the first-order case of the construction in the proof of [Stacks, Tag 07JH].  It is
**not** that tag: the tag's equivalence has the crystals in quasi-coherent `𝒪_{X/S}`-modules on
`Cris(X/S)` as its source and the pairs `(M, ∇)` with a *completed* connection as its target,
and the passage to the completion is `Crystalline.firstOrderCrystalsToPairs_isEquivalence`
below, which is conditional. -/
public noncomputable def firstOrderComparisonEquivConnection :
    FirstOrderComparison A D g Omega d M ≃
      FirstOrderConnection D Omega (derivationFun A D g Omega d) M where
  toFun c := c.toFirstOrderConnection
  invFun nabla := FirstOrderComparison.ofConnection A D g Omega d M nabla
  left_inv c := by
    refine FirstOrderComparison.ext A D g Omega d M fun m => ?_
    have h := firstOrderTensor_eq_add D Omega M (c m)
    rw [c.reduction m] at h
    exact h.symm
  right_inv nabla := by
    refine FirstOrderConnection.ext fun m => ?_
    exact FirstOrderComparison.ofConnection_connection A D g Omega d M nabla m

end Comparison

/-! ### The functor of [Stacks, Tag 07JG] -/

section Functor

variable (A : Type uA) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D)
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega]
  [IsCentralScalar D Omega] (d : DividedPowerDerivation A D g Omega) (p : ℕ)
  {ι : Type uI} (dx : ι → Omega)

/-- A pair assembled from a connection equal to the connection of `P`, on the same module, is
isomorphic to `P` by the identity map. -/
public noncomputable def pairIsoOfNablaEq
    (P : Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d))
    (nab : CompletedConnection p D Omega (derivationFun A D g Omega d) P.carrier)
    (hco : ∃ theta : ι → (P.carrier → P.carrier),
      IsCoordinateExpansion p D Omega dx nab theta)
    (hint : IsIntegrable p D Omega dx nab)
    (hqn : IsTopologicallyQuasiNilpotent p D Omega dx nab)
    (h : nab = P.nabla) :
    ({ carrier := P.carrier
       isPAdicallyComplete := P.isPAdicallyComplete
       nabla := nab
       hasCoordinateOperators := hco
       isIntegrable := hint
       isTopologicallyQuasiNilpotent := hqn } :
      Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d)) ≅ P := by
  subst h
  exact
    { hom := ⟨LinearMap.id, fun m => by simp⟩
      inv := ⟨LinearMap.id, fun m => by simp⟩
      hom_inv_id := by apply PairHom.ext; rfl
      inv_hom_id := by apply PairHom.ext; rfl }

/-- **The functor of [Stacks, Tag 07JG] is faithful.**  A morphism of first-order crystal data is
determined by its underlying `D`-linear map, which is what the functor keeps. -/
public theorem firstOrderCrystalsToPairs_faithful :
    Functor.Faithful
      (firstOrderCrystalsToPairs A D g Omega d p dx :
        FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx ⥤
          Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d)) where
  map_injective h := FirstOrderCrystalHom.ext (congrArg (fun phi => phi.toLinearMap) h)

/-- **The functor of [Stacks, Tag 07JG] is full once the completion map is injective.**  A
horizontal map of pairs is an identity in `M ⊗̂_D Ω`; injectivity of the canonical map
`M ⊗_D Ω → M ⊗̂_D Ω` turns it back into an identity in `M ⊗_D Ω`, which is compatibility with
the comparison data by the splitting `Crystalline.firstOrderTensor_ext`. -/
public theorem firstOrderCrystalsToPairs_full_of_injective
    (hinj : ∀ Q : FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier)) :
    Functor.Full
      (firstOrderCrystalsToPairs A D g Omega d p dx :
        FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx ⥤
          Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d)) where
  map_surjective {P Q} phi := by
    obtain ⟨psi, hpsi⟩ : ∃ psi : P.carrier →ₗ[(D : Type u)] Q.carrier,
        psi = phi.toLinearMap := ⟨phi.toLinearMap, rfl⟩
    have hhoriz : ∀ m : P.carrier, toCompletedTensor p D Omega Q.carrier
          (TensorProduct.comm D Omega Q.carrier (Q.comparison.connection (psi m))) =
        AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
          (TensorProduct.map psi (LinearMap.id (R := (D : Type u)) (M := Omega)))
          (toCompletedTensor p D Omega P.carrier
            (TensorProduct.comm D Omega P.carrier (P.comparison.connection m))) := by
      intro m
      rw [hpsi]
      exact phi.horizontal m
    refine ⟨⟨psi, fun m => ?_⟩, ?_⟩
    · refine firstOrderTensor_ext D Omega Q.carrier ?_ ?_
      · rw [Q.comparison.reduction, firstOrderReduction_lTensor, P.comparison.reduction]
      · rw [firstOrderDifferentialPart_lTensor]
        have hh := hhoriz m
        rw [AdicCompletion.map_of, ← comm_lTensor] at hh
        exact (TensorProduct.comm D Omega Q.carrier).injective (hinj Q hh)
    · exact PairHom.ext hpsi

omit [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] in
/-- **When the completion map is bijective the connection of a pair comes from `M ⊗_D Ω`.**  This
is the hypothesis `hlift` of `Crystalline.firstOrderCrystalsToPairs_essSurj_of_exists_lift`, and
the only place in this file where a hypothesis about the completion is turned into one about
connections. -/
public theorem exists_firstOrderConnection_of_bijective
    (P : Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d))
    (hbij : Function.Bijective (toCompletedTensor p D Omega P.carrier)) :
    ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
      ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
        (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m := by
  obtain ⟨hinj, hsurj⟩ := hbij
  choose F hF using hsurj
  have hadd : ∀ m n : P.carrier,
      F (P.nabla (m + n)) = F (P.nabla m) + F (P.nabla n) := by
    intro m n
    refine hinj ?_
    rw [hF, map_add, hF, hF, P.nabla.map_add m n]
  have hleib : ∀ (f : D) (m : P.carrier), F (P.nabla (f • m)) =
      f • F (P.nabla m) + m ⊗ₜ[D] derivationFun A D g Omega d f := by
    intro f m
    refine hinj ?_
    rw [hF, map_add, map_smul, hF, P.nabla.leibniz f m]
  refine ⟨{ toFun := fun m => (TensorProduct.comm D Omega P.carrier).symm (F (P.nabla m))
            map_add' := fun m n => by rw [hadd m n, map_add]
            leibniz' := fun f m => by
              rw [hleib f m, map_add, map_smul, TensorProduct.comm_symm_tmul] }, fun m => ?_⟩
  simp [hF]

/-- **The functor of [Stacks, Tag 07JG] is essentially surjective once the connection of every
pair comes from the uncompleted tensor product.**  The comparison datum of the preimage is
`Crystalline.FirstOrderComparison.ofConnection` applied to the lift, and its completed
connection is the connection of the pair, so the four carried pieces of data transport. -/
public theorem firstOrderCrystalsToPairs_essSurj_of_exists_lift
    (hlift : ∀ P : Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m) :
    Functor.EssSurj
      (firstOrderCrystalsToPairs A D g Omega d p dx :
        FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx ⥤
          Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d)) where
  mem_essImage P := by
    obtain ⟨nabla, hnabla⟩ := hlift P
    obtain ⟨theta, htheta⟩ := P.hasCoordinateOperators
    have hc : (FirstOrderComparison.ofConnection A D g Omega d P.carrier
        nabla).completedConnection p = P.nabla := by
      refine CompletedConnection.ext fun m => ?_
      rw [FirstOrderComparison.completedConnection_apply,
        FirstOrderComparison.ofConnection_connection]
      exact hnabla m
    refine ⟨{ carrier := P.carrier
              comparison := FirstOrderComparison.ofConnection A D g Omega d P.carrier nabla
              isPAdicallyComplete := P.isPAdicallyComplete
              hasCoordinateOperators := ⟨theta, hc ▸ htheta⟩
              isIntegrable := hc ▸ P.isIntegrable
              isTopologicallyQuasiNilpotent := hc ▸ P.isTopologicallyQuasiNilpotent },
            ⟨pairIsoOfNablaEq A D g Omega d p dx P _ _ _ _ hc⟩⟩

/-- **The functor of [Stacks, Tag 07JG] is an equivalence of categories under two hypotheses.**
The hypotheses are `hinj`, injectivity of the canonical map `M ⊗_D Ω → M ⊗̂_D Ω` on the modules
of the source category, and `hlift`, the requirement that the connection of every pair factor
through `M ⊗_D Ω`; by `Crystalline.exists_firstOrderConnection_of_bijective` the second follows
from bijectivity of the same map.  Neither is proved to hold in the situation of
[Stacks, Tag 07JH], and the source category here is the first-order crystal data over `D`, not
the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`. -/
public theorem firstOrderCrystalsToPairs_isEquivalence
    (hinj : ∀ Q : FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier))
    (hlift : ∀ P : Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m) :
    Functor.IsEquivalence
      (firstOrderCrystalsToPairs A D g Omega d p dx :
        FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx ⥤
          Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d)) where
  faithful := firstOrderCrystalsToPairs_faithful A D g Omega d p dx
  full := firstOrderCrystalsToPairs_full_of_injective A D g Omega d p dx hinj
  essSurj := firstOrderCrystalsToPairs_essSurj_of_exists_lift A D g Omega d p dx hlift

end Functor

end Crystalline

end
