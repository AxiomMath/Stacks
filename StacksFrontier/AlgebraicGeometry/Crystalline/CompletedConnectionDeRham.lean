module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology

/-!
# The complex `M ⊗^∧_D Ω^*_D` of a pair with a completed connection, and the statement of 07LG

[Stacks, Proposition 60.21.3, Tag 07LG] is the de Rham computation of crystalline cohomology in
the affine case: with the assumptions of [Stacks, Tag 07JN] but with `ℱ` a crystal in
quasi-coherent `𝒪_{X/S}`-modules, and with `(M, ∇)` the module with connection over `D`
corresponding to `ℱ` under [Stacks, Proposition 60.17.4, Tag 07JH], the complex

`M ⊗^∧_D Ω^*_D  =  (M ⊗̂_D D → M ⊗̂_D Ω¹_D → M ⊗̂_D Ω²_D → ⋯)`

computes `RΓ(Cris(X/S), ℱ)`.

This module builds that complex and writes the proposition down.

The complex is **not** the complex of the divided power Poincaré lemma.  That one,
`Crystalline.CompletedPoincare.completedTensorForms` of
`StacksFrontier/AlgebraicGeometry/Crystalline/DividedPowerPoincare.lean`, has the terms
`M ⊗̂_A Ω^i_D`, tensored over the *base* `A`, and its differential is the completion of
`1_M ⊗ d`: it is the de Rham complex with *constant* coefficients in an `A`-module.  The complex
of [Stacks, Tag 07LG] is tensored over `D` and its differential is built from the connection,

`∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`,

which is the whole content of the proposition: with `∇` replaced by anything else the terms would
be the same and the statement false.  Neither complex is obtainable from the other.  Nor is it
`Crystalline.connectionDeRhamComplex` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincare.lean`, which is the
same formula without any completion: there `∇` takes values in the ordinary tensor product
`M ⊗_B Ω` and all the terms are ordinary tensor products, whereas the `∇` of a
`Crystalline.Pair` takes values in `M ⊗̂_D Ω` and the terms are completed, so neither the
differential nor a single term of that complex is a term of this one.

## The differential is constructed, not assumed

The differential is **constructed** here, not carried as pinned data.  The two steps are:

* on the uncompleted tensor product the formula `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` is balanced over
  `D`, because the Leibniz rule for `∇` ([Stacks, Tag 07JC]) and the Leibniz rule
  `d (f ω) = f · d ω + d f ∧ ω` for the de Rham differential cancel when a scalar crosses the
  tensor sign.  This is `Crystalline.CompletedDeRham.rawDifferential`.
* that map is additive, hence `ℤ`-linear, hence carries `pⁿ · (M ⊗_D Ω^i_D)` into
  `pⁿ · (M ⊗̂_D Ω^{i+1}_D)`, so it descends to every level `pⁿ` and the levels assemble into a
  map out of the completion.  This is `Crystalline.CompletedDeRham.differential`, and
  `Crystalline.CompletedDeRham.differential_eq_of_val` records that these two properties
  determine it uniquely, so nothing about it is a choice.

The second step cannot be `AdicCompletion.map`: the completion is taken along `(p) ⊆ D` and the
differential is not `D`-linear — already the Leibniz rule forbids it — so it is the
`AdicCompletion.map` of no `D`-linear map.  Working at the levels is what replaces it.

## What is and is not proved

**No `@[stacks 07LG]` attribute is placed in this module.**  [Stacks, Tag 07LG] is
`Crystalline.GlobalCrystallineSituation.SmallSite.crystalPairDeRhamDerivedPlusIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalDeRhamDerived07LG.lean`,
stated for the pair `(M, ∇)` that the functor of [Stacks, Tag 07JG]
(`...SmallSite.crystalPairFunctor`) attaches to a crystal in quasi-coherent modules, over the
completed envelope of any surjective polynomial presentation.  What this module proves is
everything about the complex of an abstract completed connection: the terms, the differential,
its defining formula on pure tensors, and the uniqueness that pins it.  The `Prop`
`Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG` defined here is an earlier
rendering of the tag, over a reduction datum and an abstract graded family of forms; it takes
three inputs as named hypotheses:

1. `Crystalline.CompletedDeRham.IsSquareZero`, that consecutive differentials compose to zero.
   For an uncompleted connection this is exactly integrability, [Stacks, Tag 07JD], and the
   library proves it there (`Crystalline.extendedConnection_comp_self_eq_zero`).  A
   `Crystalline.Pair` records integrability in the coordinate form
   `Crystalline.IsIntegrable` — the coordinate operators `θ_i` commute — and this module does not
   derive from that the vanishing of the curvature of the *completed* differentials.  Without it
   there is no complex at all, so it is a hypothesis of `Crystalline.CompletedDeRham.complex`
   itself.
2. `Reduction07JG`, a reduction datum giving "the pair `(M, ∇)` corresponding to `ℱ`".  Its
   clauses are ring identifications of [Stacks, Tag 07JN] and the base change of the first-order
   ideal.  Its field `Reduction07JG.levelSystem_isLevel` pins a system of levels
   `ℕ ⥤ Cris(X/S)` of [Stacks, Tag 07JN], with `M = lim_e Γ(T_e, ℱ_{T_e})`, which exists only in
   the affine setting; that is why `crystalDeRhamComplex` below carries `[IsAffine S.X]`,
   `[IsAffine S.S.scheme]` and the nilpotence of `p`, and why the pair is one over the completed
   envelope `D`, as [Stacks, Tag 07LG] requires.  Without the pin the remaining clauses were
   satisfied by a datum over the empty open of `X`, at which the complex built here is zero while
   the cohomology it is claimed to compute is not — see
   `StacksFrontier/AlgebraicGeometry/Crystalline/Reduction07JGWitness.lean`.  The proved form of
   the tag does not go through this datum: the pair is the value of
   `...SmallSite.crystalPairFunctor`.
3. The implication (1) ⟹ (2) of [Stacks, Tag 07IT], that a quasi-coherent module on the
   crystalline site is a crystal.  It is a named hypothesis so that the hypothesis on `ℱ` can be
   the source's own, `SheafOfModules.IsQuasicoherentOnSite` alone: the source category of
   [Stacks, Tag 07JH] in this library is cut out by the *conjunction* of quasi-coherence and the
   crystal condition, and asking for both in the statement would be strictly stronger than
   [Stacks, Tag 07LG] asks.

[Stacks, Tag 07JN]'s own conclusion is not among the hypotheses, because it is not needed to
*state* 07LG: it is what the source's proof consumes, through the double complex
`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`, whose rows are complexes of the kind built here and whose
columns are the complex `M(0) → M(1) → ⋯` of
`Crystalline.GlobalCrystallineSituation.SmallSite.sectionsComplex`.  [Stacks, Tag 07JN] is
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` of
`SmallSite/WholeSpaceSystemCohomology.lean`, and [Stacks, Tag 07LA] is
`Crystalline.id_completedTensorCompletedForms_homotopic_zero`; both enter the proof of
`...SmallSite.crystalPairDeRhamDerivedPlusIso`.

The graded family `Ω^i_D` is carried as a parameter `Om : ℕ → Type u` with its wedge product and
its de Rham differential, subject to the Leibniz rule; the degree-one member `Om 1` is the module
`Ω_D` the connection of the pair differentiates into, so the identification of the parameter with
the genuine completed divided power forms of `D` is part of the data the proposition is applied
to, exactly as `AlgebraicGeometry/DeRham/ModuleConnection.lean` pins its differential by a
Leibniz field.  The proposition asserts nothing for a family of forms that is not that one.

## Main definitions

* `Crystalline.CompletedDeRham.IsGradedLeibniz` — the Leibniz rule
  `d (f ω) = f · d ω + d f ∧ ω` for the graded de Rham differential of the forms.
* `Crystalline.CompletedDeRham.wedgeMap` — left exterior multiplication by the one-form factor,
  read on completed tensor products.
* `Crystalline.CompletedDeRham.rawDifferential` — the differential on the *uncompleted* tensor
  product `M ⊗_D Ω^i_D`, with values in `M ⊗̂_D Ω^{i+1}_D`.
* `Crystalline.CompletedDeRham.differential` — **the differential of `M ⊗^∧_D Ω^*_D`**.
* `Crystalline.CompletedDeRham.IsSquareZero` and `Crystalline.CompletedDeRham.complex` —
  **the complex `M ⊗^∧_D Ω^*_D`** as a `CochainComplex` of abelian groups, given that the
  differentials compose to zero.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crystalDeRhamComplex` — that complex for the
  pair attached to a crystal in quasi-coherent `𝒪_{X/S}`-modules.
* `Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG` — **the statement of
  [Stacks, Tag 07LG]**, as a `Prop`.

## Main results

* `Crystalline.CompletedDeRham.rawDifferential_tmul` — the defining formula
  `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`.
* `Crystalline.CompletedDeRham.differential_of_tmul` — the same formula for the differential of
  the complex, on the image of `M ⊗_D Ω^i_D` in the completion.
* `Crystalline.CompletedDeRham.differential_eq_of_val` — that formula together with locality at
  each level `pⁿ` determines the differential.
* `Crystalline.CompletedDeRham.complex_X` and `Crystalline.CompletedDeRham.complex_d` — the
  degree-`i` term is `M ⊗̂_D Ω^i_D` and the differential is the one constructed here.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Lemma 60.14.3, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

open CategoryTheory
open DividedPowers
open scoped TensorProduct

universe u v w uI

namespace Crystalline

namespace CompletedDeRham

/-! ### Additive maps and the `p`-adic levels -/

section Levels

variable (p : ℕ) (D : Type u) [CommRing D]

/-- An element of `(p)ⁿ` annihilates the quotient of a `D`-module by `(p)ⁿ`. -/
public theorem smul_quotient_eq_zero {X : Type v} [AddCommGroup X] [Module D X] {n : ℕ} {c : D}
    (hc : c ∈ (pAdicIdeal (A := D) p) ^ n)
    (z : X ⧸ ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D X)) : c • z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

/-- **An additive map into a `p`-adic completion vanishes at level `n` on `pⁿ`.**  This is what
makes an additive — in particular a not `D`-linear — map descend to the levels of the completion:
the ideal `(p)ⁿ` is generated by the *integer* `pⁿ`, and every additive map is `ℤ`-linear. -/
public theorem val_eq_zero_of_mem {X : Type v} [AddCommGroup X] [Module D X] {Y : Type w}
    [AddCommGroup Y] [Module D Y] (φ : X →+ AdicCompletion (pAdicIdeal (A := D) p) Y) (n : ℕ)
    {x : X} (hx : x ∈ ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D X)) :
    (φ x).val n = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro c hc y _
    have hc' : c ∈ Ideal.span {(p : D) ^ n} := by
      rw [← Ideal.span_singleton_pow]; exact hc
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp hc'
    have hsm : (e * (p : D) ^ n) • y = (p ^ n : ℕ) • (e • y) := by
      rw [mul_comm, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [hsm, map_nsmul, AdicCompletion.val_smul_apply, ← Nat.cast_smul_eq_nsmul D, Nat.cast_pow]
    exact smul_quotient_eq_zero p D (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) _
  · intro a b ha hb
    rw [map_add, AdicCompletion.val_add_apply, ha, hb, add_zero]

/-- The transition map of a `p`-adic completion fixes the class of an element. -/
public theorem transitionMap_mk {X : Type v} [AddCommGroup X] [Module D X] {m n : ℕ}
    (hmn : m ≤ n) (y : X) :
    AdicCompletion.transitionMap (pAdicIdeal (A := D) p) X hmn (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk y := by
  simp [AdicCompletion.transitionMap]

end Levels

/-! ### The forms and their Leibniz rule -/

section Forms

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (dmap : D → Om 1)

/-- **The Leibniz rule `d (f ω) = f · d ω + d f ∧ ω`** for a graded de Rham differential on a
family of modules of forms, with the exact one-form `d f` on the left of the wedge.  This is the
identity, and not `D`-linearity, that the de Rham differential of [Stacks, Tag 07HZ] satisfies,
and it is the second half of what makes the differential of `M ⊗^∧_D Ω^*_D` well defined. -/
public def IsGradedLeibniz : Prop :=
  ∀ (i : ℕ) (f : D) (ω : Om i),
    deRham i (f • ω) = f • deRham i ω + wedge i ω (dmap f)

variable (M : Type w) [AddCommGroup M] [Module D M]

/-- **Left exterior multiplication by the one-form factor, on completed tensor products**: the
map `M ⊗̂_D Ω¹_D → M ⊗̂_D Ω^{i+1}_D` sending `m ⊗ η` to `m ⊗ (η ∧ ω)`, for a fixed `i`-form `ω`.
It is `D`-linear, being the completion of a `D`-linear map, which is why it may be applied to the
value `∇ m` of a connection and still leave the resulting formula balanced. -/
public noncomputable def wedgeMap (i : ℕ) (ω : Om i) :
    CompletedTensor p D (Om 1) M →ₗ[D] CompletedTensor p D (Om (i + 1)) M :=
  (AdicCompletion.map (pAdicIdeal (A := D) p) (LinearMap.lTensor M (wedge i ω))).restrictScalars D

/-- Left exterior multiplication by the one-form factor, on the image of an uncompleted pure
tensor. -/
public theorem wedgeMap_of_tmul (i : ℕ) (ω : Om i) (m : M) (eta : Om 1) :
    wedgeMap p D Om wedge M i ω (toCompletedTensor p D (Om 1) M (m ⊗ₜ[D] eta)) =
      toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] wedge i ω eta) :=
  AdicCompletion.map_of (pAdicIdeal (A := D) p) (LinearMap.lTensor M (wedge i ω)) _

/-- Left exterior multiplication by the zero form is zero. -/
public theorem wedgeMap_zero (i : ℕ) (x : CompletedTensor p D (Om 1) M) :
    wedgeMap p D Om wedge M i 0 x = 0 := by
  simp only [wedgeMap, map_zero, LinearMap.lTensor_zero]
  rfl

/-- Left exterior multiplication is additive in the form. -/
public theorem wedgeMap_add (i : ℕ) (ω ω' : Om i) (x : CompletedTensor p D (Om 1) M) :
    wedgeMap p D Om wedge M i (ω + ω') x =
      wedgeMap p D Om wedge M i ω x + wedgeMap p D Om wedge M i ω' x := by
  simp only [wedgeMap, map_add, LinearMap.lTensor_add]
  rfl

/-- Left exterior multiplication is `D`-linear in the form. -/
public theorem wedgeMap_smul (i : ℕ) (f : D) (ω : Om i) (x : CompletedTensor p D (Om 1) M) :
    wedgeMap p D Om wedge M i (f • ω) x = f • wedgeMap p D Om wedge M i ω x := by
  simp only [wedgeMap, map_smul, LinearMap.lTensor_smul]
  rfl

end Forms

/-! ### The differential on the uncompleted tensor product -/

section Raw

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)

/-- A completed connection as an additive map, so that its value at `0` and its behaviour on
`ℤ`-multiples are available. -/
public noncomputable def nablaHom : M →+ CompletedTensor p D (Om 1) M :=
  AddMonoidHom.mk' (fun m ↦ nabla m) nabla.map_add

/-- The value of `nablaHom` at `m` is `∇ m`. -/
@[simp] public theorem nablaHom_apply (m : M) : nablaHom p D Om M nabla m = nabla m := rfl

variable (dmap) in
/-- **The de Rham formula `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`, as a bi-additive map.** -/
public noncomputable def rawPair (i : ℕ) :
    M →+ (Om i →+ CompletedTensor p D (Om (i + 1)) M) where
  toFun m :=
    { toFun := fun ω ↦ wedgeMap p D Om wedge M i ω (nablaHom p D Om M nabla m) +
        toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω)
      map_zero' := by
        change wedgeMap p D Om wedge M i 0 (nablaHom p D Om M nabla m) +
            toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i 0) = 0
        simp [wedgeMap_zero p D Om wedge M i]
      map_add' := fun ω ω' ↦ by
        change wedgeMap p D Om wedge M i (ω + ω') (nablaHom p D Om M nabla m) +
            toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i (ω + ω')) =
          wedgeMap p D Om wedge M i ω (nablaHom p D Om M nabla m) +
              toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω) +
            (wedgeMap p D Om wedge M i ω' (nablaHom p D Om M nabla m) +
              toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω'))
        rw [wedgeMap_add p D Om wedge M i, map_add, TensorProduct.tmul_add, map_add]
        abel }
  map_zero' := AddMonoidHom.ext fun ω ↦ by
    change wedgeMap p D Om wedge M i ω (nablaHom p D Om M nabla 0) +
        toCompletedTensor p D (Om (i + 1)) M ((0 : M) ⊗ₜ[D] deRham i ω) = 0
    simp only [map_zero, TensorProduct.zero_tmul, zero_add]
  map_add' := fun m m' ↦ AddMonoidHom.ext fun ω ↦ by
    change wedgeMap p D Om wedge M i ω (nablaHom p D Om M nabla (m + m')) +
        toCompletedTensor p D (Om (i + 1)) M ((m + m') ⊗ₜ[D] deRham i ω) =
      wedgeMap p D Om wedge M i ω (nablaHom p D Om M nabla m) +
          toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω) +
        (wedgeMap p D Om wedge M i ω (nablaHom p D Om M nabla m') +
          toCompletedTensor p D (Om (i + 1)) M (m' ⊗ₜ[D] deRham i ω))
    rw [map_add, map_add, TensorProduct.add_tmul, map_add]
    abel

/-- The value of `rawPair` at `m` and `ω` is `∇(m) ∧ ω + m ⊗ d ω`. -/
@[simp] public theorem rawPair_apply (i : ℕ) (m : M) (ω : Om i) :
    rawPair p D Om wedge deRham dmap M nabla i m ω =
      wedgeMap p D Om wedge M i ω (nabla m) +
        toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω) := rfl

/-- **The de Rham formula is balanced over `D`**: moving a scalar `f` from the coefficient to the
form does not change the value.  The two Leibniz rules — the one for the connection,
[Stacks, Tag 07JC], and the one for the de Rham differential — cancel: the connection contributes
`m ⊗ d f` wedged against `ω`, the differential contributes `m ⊗ (d f ∧ ω)`, and these are the
same element. -/
public theorem rawPair_balance (hleib : IsGradedLeibniz D Om wedge deRham dmap) (i : ℕ)
    (f : D) (m : M) (ω : Om i) :
    rawPair p D Om wedge deRham dmap M nabla i (f • m) ω =
      rawPair p D Om wedge deRham dmap M nabla i m (f • ω) := by
  simp only [rawPair_apply, nabla.leibniz f m, hleib i f ω, map_add,
    wedgeMap_of_tmul p D Om wedge M i, wedgeMap_smul p D Om wedge M i,
    TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
  abel

/-- **The differential of `M ⊗^∧_D Ω^*_D` on the uncompleted tensor product**: the additive map
`M ⊗_D Ω^i_D → M ⊗̂_D Ω^{i+1}_D` determined by `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω`.  Its target is the
completion because `∇` takes its values there. -/
public noncomputable def rawDifferential (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (i : ℕ) : (M ⊗[D] Om i) →+ CompletedTensor p D (Om (i + 1)) M :=
  TensorProduct.liftAddHom (rawPair p D Om wedge deRham dmap M nabla i)
    (fun f m ω ↦ rawPair_balance p D Om wedge deRham M nabla hleib i f m ω)

/-- **The defining formula `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`.** -/
@[simp] public theorem rawDifferential_tmul (hleib : IsGradedLeibniz D Om wedge deRham dmap)
    (i : ℕ) (m : M) (ω : Om i) :
    rawDifferential p D Om wedge deRham M nabla hleib i (m ⊗ₜ[D] ω) =
      wedgeMap p D Om wedge M i ω (nabla m) +
        toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω) := rfl

end Raw

/-! ### The differential on the completed tensor product -/

section Differential

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- The differential of `M ⊗^∧_D Ω^*_D` at the level `pⁿ`.  The de Rham formula is additive, and
an additive map is `ℤ`-linear, so it kills `pⁿ` and descends here. -/
public noncomputable def levelDifferential (i n : ℕ) :
    (M ⊗[D] Om i) ⧸ ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om i)) →+
      (M ⊗[D] Om (i + 1)) ⧸
        ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om (i + 1))) :=
  QuotientAddGroup.lift _
    ((AdicCompletion.eval (pAdicIdeal (A := D) p) (M ⊗[D] Om (i + 1)) n).toAddMonoidHom.comp
      (rawDifferential p D Om wedge deRham M nabla hleib i))
    (fun _ hy ↦ val_eq_zero_of_mem p D _ n hy)

/-- The level-`pⁿ` differential of the class of `y` is the level-`pⁿ` component of the
differential of `y`. -/
@[simp] public theorem levelDifferential_mk (i n : ℕ) (y : M ⊗[D] Om i) :
    levelDifferential p D Om wedge deRham M nabla hleib i n (Submodule.Quotient.mk y) =
      (rawDifferential p D Om wedge deRham M nabla hleib i y).val n := rfl

/-- **The differential `M ⊗̂_D Ω^i_D → M ⊗̂_D Ω^{i+1}_D` of the complex
`M ⊗^∧_D Ω^*_D`** of [Stacks, Tag 07LG], as a function: at every level `pⁿ` it is the de Rham
formula `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`.  It is additive and not `D`-linear, as the Leibniz rule
requires; `Crystalline.CompletedDeRham.differential` is the additive map it underlies. -/
public noncomputable def differentialFun (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    CompletedTensor p D (Om (i + 1)) M :=
  ⟨fun n ↦ levelDifferential p D Om wedge deRham M nabla hleib i n (x.val n), by
    intro m n hmn
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
      ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om i)) (x.val n)
    have hxm : x.val m = Submodule.Quotient.mk y := by
      rw [← x.property hmn, ← hy, transitionMap_mk p D hmn]
    change AdicCompletion.transitionMap (pAdicIdeal (A := D) p) (M ⊗[D] Om (i + 1)) hmn
        (levelDifferential p D Om wedge deRham M nabla hleib i n (x.val n)) =
      levelDifferential p D Om wedge deRham M nabla hleib i m (x.val m)
    rw [hxm, ← hy, levelDifferential_mk, levelDifferential_mk]
    exact (rawDifferential p D Om wedge deRham M nabla hleib i y).property hmn⟩

/-- The level-`pⁿ` component of `differentialFun` at `x` is the level-`pⁿ` differential of the
level-`pⁿ` component of `x`. -/
@[simp] public theorem differentialFun_val (i n : ℕ) (x : CompletedTensor p D (Om i) M) :
    (differentialFun p D Om wedge deRham M nabla hleib i x).val n =
      levelDifferential p D Om wedge deRham M nabla hleib i n (x.val n) := rfl

/-- **The differential `M ⊗̂_D Ω^i_D → M ⊗̂_D Ω^{i+1}_D` of the complex `M ⊗^∧_D Ω^*_D`**, as an
additive map. -/
public noncomputable def differential (i : ℕ) :
    CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om (i + 1)) M :=
  AddMonoidHom.mk' (differentialFun p D Om wedge deRham M nabla hleib i) (fun x y ↦ by
    refine AdicCompletion.ext fun n ↦ ?_
    rw [differentialFun_val, AdicCompletion.val_add_apply, map_add,
      AdicCompletion.val_add_apply, differentialFun_val, differentialFun_val])

/-- The level-`pⁿ` component of `differential` at `x` is the level-`pⁿ` differential of the
level-`pⁿ` component of `x`. -/
@[simp] public theorem differential_val (i n : ℕ) (x : CompletedTensor p D (Om i) M) :
    (differential p D Om wedge deRham M nabla hleib i x).val n =
      levelDifferential p D Om wedge deRham M nabla hleib i n (x.val n) := rfl

/-- **The de Rham formula `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω` for the differential of the
complex**, on the image of the uncompleted tensor product in the completion.  That image is
`p`-adically dense, so this formula and locality at the levels pin the differential down; see
`Crystalline.CompletedDeRham.differential_eq_of_val`. -/
public theorem differential_of_tmul (i : ℕ) (m : M) (ω : Om i) :
    differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω)) =
      wedgeMap p D Om wedge M i ω (nabla m) +
        toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω) :=
  rfl

/-- **The differential is determined** by the de Rham formula together with locality at the
levels: any additive map whose level-`n` value is computed from any representative of the
level-`n` reduction by the formula of `Crystalline.CompletedDeRham.rawDifferential` is this one.
Nothing in the construction is a choice. -/
public theorem differential_eq_of_val (i : ℕ)
    (delta : CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om (i + 1)) M)
    (h : ∀ (n : ℕ) (x : CompletedTensor p D (Om i) M) (y : M ⊗[D] Om i),
      x.val n = Submodule.Quotient.mk y →
        (delta x).val n = (rawDifferential p D Om wedge deRham M nabla hleib i y).val n) :
    delta = differential p D Om wedge deRham M nabla hleib i := by
  refine AddMonoidHom.ext fun x ↦ ?_
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om i)) (x.val n)
  rw [h n x y hy.symm, differential_val, ← hy, levelDifferential_mk]

/-! ### The complex -/

/-- **The differentials of `M ⊗^∧_D Ω^*_D` compose to zero.**  For an uncompleted connection
this is exactly integrability, [Stacks, Tag 07JD], proved in the library as
`Crystalline.extendedConnection_comp_self_eq_zero`; for a completed connection the library has
integrability only in the coordinate form `Crystalline.IsIntegrable`, and the passage from that
to this vanishing is not available, so it is a hypothesis. -/
public def IsSquareZero : Prop :=
  ∀ i : ℕ, (differential p D Om wedge deRham M nabla hleib (i + 1)).comp
    (differential p D Om wedge deRham M nabla hleib i) = 0

/-- **The complex `M ⊗^∧_D Ω^*_D` of [Stacks, Tag 07LG]**: in degree `i` the completed tensor
product `M ⊗̂_D Ω^i_D`, with the de Rham differential of the connection,
`∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`, as its differential.  The hypothesis `hsq` is that consecutive
differentials compose to zero; see `Crystalline.CompletedDeRham.IsSquareZero`. -/
public noncomputable def complex
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib) :
    CochainComplex AddCommGrpCat.{max v w} ℕ :=
  CochainComplex.of (fun i ↦ AddCommGrpCat.of (CompletedTensor p D (Om i) M))
    (fun i ↦ AddCommGrpCat.ofHom (differential p D Om wedge deRham M nabla hleib i))
    (fun i ↦ AddCommGrpCat.ext fun x ↦ by
      exact DFunLike.congr_fun (hsq i) x)

/-- The degree-`i` term of `M ⊗^∧_D Ω^*_D` is `M ⊗̂_D Ω^i_D`. -/
public theorem complex_X (hsq : IsSquareZero p D Om wedge deRham M nabla hleib) (i : ℕ) :
    (complex p D Om wedge deRham M nabla hleib hsq).X i =
      AddCommGrpCat.of (CompletedTensor p D (Om i) M) := rfl

/-- The differential of `M ⊗^∧_D Ω^*_D` is the de Rham differential of the connection. -/
public theorem complex_d (hsq : IsSquareZero p D Om wedge deRham M nabla hleib) (i : ℕ) :
    (complex p D Om wedge deRham M nabla hleib hsq).d i (i + 1) =
      AddCommGrpCat.ofHom (differential p D Om wedge deRham M nabla hleib i) :=
  CochainComplex.of_d (fun i ↦ AddCommGrpCat.of (CompletedTensor p D (Om i) M))
    (fun i ↦ AddCommGrpCat.ofHom (differential p D Om wedge deRham M nabla hleib i)) i

end Differential

end CompletedDeRham

/-! ### The statement of [Stacks, Tag 07LG] -/

namespace GlobalCrystallineSituation.SmallSite

open AlgebraicGeometry Opposite

variable (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
  (Dr : DividedPowerRing.{u}) (g : A →+* Dr) (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module (Dr : Type u) (Om i)] [Module (Dr : Type u)ᵐᵒᵖ (Om 1)]
  [IsCentralScalar (Dr : Type u) (Om 1)] (der : DividedPowerDerivation A Dr g (Om 1)) (p : ℕ)
  {ι : Type uI} (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun A Dr g (Om 1) der))

/-- **The complex `M ⊗^∧_D Ω^*_D` of a pair `(M, ∇)` over `D`**, in the shape in which
[Stacks, Tag 07LG] speaks of it: the pair is an object of `Crystalline.Pair`, the category of
[Stacks, Tag 07JG], and the forms are the carried graded family with its wedge product and its
de Rham differential.  `hsq` is the hypothesis that the differentials compose to zero. -/
public noncomputable def pairDeRhamComplex
    (P : Pair.{u, u, uI, u} p Dr (Om 1) dx (derivationFun A Dr g (Om 1) der))
    (hsq : CompletedDeRham.IsSquareZero p Dr Om wedge deRham P.carrier P.nabla hleib) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CompletedDeRham.complex p Dr Om wedge deRham P.carrier P.nabla hleib hsq

/-- A quasi-coherent module on `Cris(X/S)` read as an object of the source category of
[Stacks, Tag 07JH], using the carried implication (1) ⟹ (2) of [Stacks, Tag 07IT]. -/
public def toQuasiCoherentCrystal
    (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
      F.IsQuasicoherentOnSite → IsSheafCrystal F)
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) :
    QuasiCoherentCrystal S :=
  ⟨F, hF, h07IT F hF⟩

/-- **The complex `M ⊗^∧_D Ω^*_D` attached to a crystal in quasi-coherent
`𝒪_{X/S}`-modules**, through the reduction datum of [Stacks, Tag 07JG]: the pair `(M, ∇)` is
`functor07JG R` applied to the crystal, which is the correspondence of
[Stacks, Proposition 60.17.4, Tag 07JH].

The affineness of `X` and of `S`, and the nilpotence of `p`, are carried because a reduction datum
carries them: its field `levelSystem_isLevel` names the system of finite levels of
[Stacks, Tag 07JN], which is constructed only there.  They are the source's own hypotheses, those
of [Stacks, Tag 07MD]. -/
public noncomputable def crystalDeRhamComplex [IsAffine S.X] [IsAffine S.S.scheme]
    {hp : IsNilpotent (S.p : Γ(S.X, ⊤))} (R : Reduction07JG S A Dr g (Om 1) der p dx hp)
    (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
      F.IsQuasicoherentOnSite → IsSheafCrystal F)
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
    (hsq : CompletedDeRham.IsSquareZero p Dr Om wedge deRham
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla hleib) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  pairDeRhamComplex A Dr g Om der p dx wedge deRham hleib
    ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)) hsq

/-- **The statement of [Stacks, Proposition 60.21.3, Tag 07LG]**: for `ℱ` a crystal in
quasi-coherent `𝒪_{X/S}`-modules on the small crystalline site, with `(M, ∇)` the module with
connection over `D` corresponding to it under [Stacks, Tag 07JH], the complex
`M ⊗^∧_D Ω^*_D` computes `RΓ(Cris(X/S), ℱ)` — in the graded form in which crystalline cohomology
is available here, namely that its cohomology in degree `j` is `H^j(Cris(X/S), ℱ)` for every `j`,
after lifting the complex to the universe `u + 1` in which that cohomology exists.

This is a proposition, not a theorem: nothing in this module proves it, and no attribute claims
it.  Its hypothesis on `ℱ` is the source's own, `SheafOfModules.IsQuasicoherentOnSite` and
nothing further.

The named inputs are, besides the forms data:

* `R`, the reduction datum of [Stacks, Tag 07JG], which is what "the corresponding `(M, ∇)`"
  means; its own clauses are the identification of `D` with the limit of the section rings of the
  levels of [Stacks, Tag 07JN] and the first-order base change, and its field
  `levelSystem_isLevel` is what makes the system the sections are taken over the system of
  [Stacks, Tag 07JN] rather than an arbitrary one.  Quantifying over a datum without that field
  would not be this tag: the field's absence made the hypothesis satisfiable over the empty open
  of `X`, where a zero complex would "compute" a nonzero cohomology.  The module `M` of the pair
  is `lim_e Γ(T_e, ℱ_{T_e})`, a module over the completed envelope `D`.
  The sections are not taken over one
  object: that would make the complex below the complex of a pair over one level `D_e`.
* `hleib`, the Leibniz rule for the de Rham differential of the forms.
* `h07IT`, the implication (1) ⟹ (2) of [Stacks, Tag 07IT], carried so that the hypothesis on
  `ℱ` is quasi-coherence alone rather than the strictly stronger conjunction that cuts out the
  source category of [Stacks, Tag 07JH] in this library.
* `hsq`, that the completed de Rham differentials of every such pair compose to zero.  For an
  uncompleted connection this is integrability, [Stacks, Tag 07JD]; see
  `Crystalline.CompletedDeRham.IsSquareZero`.  Without it there is no complex.

[Stacks, Tag 07JN] is not assumed here, because stating 07LG does not need its conclusion; a
*proof* would, and that conclusion is
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemCohomology.lean`, which is
proved and tagged.

The standing hypotheses `[IsAffine S.X]`, `[IsAffine S.S.scheme]` and `hp` are **not optional**.
[Stacks, Tag 07LG] opens "assumptions as in Proposition 07JN", and that proposition is set in the
affine case with `p` nilpotent on `Γ(X, ⊤)`; the library's 07JN carries exactly those.  Quantifying
over an arbitrary `Crystalline.GlobalCrystallineSituation` with none of them would assert
something strictly stronger than — and so not — the tag, and something 07JN cannot supply. -/
public def Computes07LG
    [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (R : Reduction07JG S A Dr g (Om 1) der p dx hp)
    (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
      F.IsQuasicoherentOnSite → IsSheafCrystal F)
    (hsq : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      CompletedDeRham.IsSquareZero p Dr Om wedge deRham
        ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier
        ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla hleib) : Prop :=
  ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
    Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((crystalDeRhamComplex S A Dr g Om der p dx wedge deRham hleib R h07IT F hF
          (hsq F hF)).homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf F))

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
