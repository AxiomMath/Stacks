module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing
public import StacksFrontier.LinearAlgebra.ExteriorPower.SignedTensorPowerCoinvariants
import StacksCore.Tactic.StacksAttribute

/-!
# The homology of a symmetric power is an exterior power

Let `C` be a small category with the chaotic topology, `B` a commutative ring and `F` a flat
`B̲`-module on `C` with `H_0(C, F) = 0`, and let `U_•` be a point resolution, so that we are in
the situation of Tag 08RD. Remark 08SG asserts that

`H_k(C, Sym^k_{B̲}(F)) = ∧^k_B(H_1(C, F))`,

deducing it from the statement that `H_k(C, Sym^k_{B̲}(F))` is the `S_k`-coinvariants of
`H^{-k}(Lπ_!(F) ⊗^L_B ⋯ ⊗^L_B Lπ_!(F)) = H_1(C, F)^{⊗ k}`, for the usual action of `S_k` on the
tensor product **multiplied by the sign character**.

The remark proves neither step: for the second it says "to prove this one has to work through
the sign conventions in the definition of the total complex associated to a multi-complex. We
omit the verification."

This file carries that coinvariants description — the whole of it, sign character included — as
the explicit hypothesis `Stacks.ChaoticSite.QuillenSignedCoinvariants` on the coefficient ring,
in the style of `Stacks.ChaoticSite.FlatEilenbergZilber`, and proves the remark's conclusion on
top of it, by the linear algebra of
`StacksFrontier.LinearAlgebra.ExteriorPower.SignedTensorPowerCoinvariants`: the sign-twisted
coinvariants of `H_1(C, F)^{⊗ k}` map onto `∧^k_B(H_1(C, F))`, canonically and surjectively,
with `2`-torsion kernel, bijectively when `2` is invertible in `B`.

The invertibility of `2` is not a defect of this formalization but of the remark: the remark's
two assertions are incompatible without it. For `B = ℤ` and `H_1(C, F) = ℤ` and `k = 2` the
sign-twisted coinvariants of `ℤ^{⊗ 2}` are `ℤ/2` while `∧²_ℤ ℤ = 0`; this is
`Stacks.SignedTensorPower.not_injective_toExteriorPower_int`.

## Main definitions

* `Stacks.ChaoticSite.QuillenSignedCoinvariants`: the coinvariants description of the remark, as
  a hypothesis on the coefficient ring.

## Main results

* `Stacks.ChaoticSite.exteriorPower_leftDerivedColim_symmetricPowerDiagram`: the remark's
  conclusion, on top of the carried coinvariants description.

## Why the theorem below carries no `@[stacks 08SG]` attribute

The hypothesis `hQ : Stacks.ChaoticSite.QuillenSignedCoinvariants B` is the remark's own
coinvariants description, carried whole because the remark does not prove it ("to prove this one
has to work through the sign conventions in the definition of the total complex associated to a
multi-complex. We omit the verification") and because its two inputs are unavailable here: the
identification of `H^{-k}` of the `k`-fold derived tensor power of `Lπ_!(ℱ)` with
`H_1(C, ℱ)^{⊗ k}`, and the `S_k`-equivariance of that identification for the Koszul-signed
symmetry of a multi-complex. The library's Künneth material
(`StacksFrontier.Algebra.Homology.SpectralSequence.Kunneth`) is a spectral sequence of filtered
complexes of modules, with no symmetric-group equivariance and no derived lower shriek as an
input; the monoidality of `Lπ_!` (Tag 08QC,
`Stacks.ChaoticSite.isIso_totalDerivedColimitTensorComparison`, itself conditional on six
carried derived-category inputs) gives only the `k`-fold derived tensor power, neither its
lowest homology nor the sign of the `S_k`-action on it, and nothing about
`H_k(C, Sym^k_{B̲}(ℱ))`.

That hypothesis is moreover **false** at `B = ℤ`, and that is a theorem of this library:
`Stacks.ChaoticSite.not_quillenSignedCoinvariants_int` in
`StacksFrontier.Cotangent.QuillenSignedCoinvariantsErratum` proves
`¬ Stacks.ChaoticSite.QuillenSignedCoinvariants ℤ`. The witness is the polynomial site of the
surjection `ℤ[x] → ℤ`, `x ↦ 0`, at `k = 2`: there `H_1(C_{B/A}, Ω)` is the conormal module
`I/I² = ℤ` of `I = (x)`, so the décalage computation
`Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram` makes the
left-hand side `H_2(C_{B/A}, Sym²_{ℤ̲}(Ω))` of the description equal to `∧²_ℤ ℤ = 0`, whereas
the sign-twisted coinvariants of `ℤ^{⊗ 2}` are `ℤ/2`: the class of `1 ⊗ 1` is nonzero there,
`Stacks.SignedTensorPower.mk_tprod_one_ne_zero`. So the theorem below is vacuous precisely
where the tag applies, and a tag counts only on a declaration proved under the source's own
hypotheses: the attribute has accordingly been taken off it, and this section is where its
explanation now lives. `hQ` is therefore not an open task but a refuted one.

None of this touches the remark's conclusion, which holds over every commutative ring with no
hypothesis on `2`: `H_k(C, Sym^k_{B̲}(ℱ)) = ∧^k_B(H_1(C, ℱ))` is
`Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerDecalage`, proved by
Illusie's and Quillen's décalage instead of the remark's coinvariants route, and that is where
the `@[stacks 08SG]` attribute lives. Only the remark's *proof* is in error, not its
statement.

## References

* [Stacks Project, Tag 08SG](https://stacks.math.columbia.edu/tag/08SG)
* [Stacks Project, Tag 08RD](https://stacks.math.columbia.edu/tag/08RD)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ChaoticSite

universe u

/-- **The coinvariants description of Remark 08SG**, as a hypothesis on the coefficient ring
`B`: in every situation of Tag 08RD — `C` a small category with the chaotic topology, `U_•` a
point resolution, `F` a flat `B̲`-module with `H_0(C, F) = 0` — the homology
`H_k(C, Sym^k_{B̲}(F))` is the `S_k`-coinvariants of `H_1(C, F)^{⊗ k}` for the permutation
action multiplied by the sign character, `Stacks.SignedTensorPower.signedPermRep`.

This is what Remark 08SG deduces "from the proof" of Tag 08RD together with the sign
computation whose verification it omits. It is carried because the two inputs it needs are not
available here: the identification of `H^{-k}` of the `k`-fold derived tensor product of
`Lπ_!(F)` with `H_1(C, F)^{⊗ k}`, and the `S_k`-equivariance of that identification for the
Koszul-signed symmetry of a multi-complex. The library's Künneth material
(`StacksFrontier.Algebra.Homology.SpectralSequence.Kunneth`) is a spectral sequence of filtered
complexes of modules, with no symmetric-group equivariance and no derived lower shriek as an
input. The monoidality of `Lπ_!` — Tag 08QC,
`Stacks.ChaoticSite.isIso_totalDerivedColimitTensorComparison`, itself conditional on six
carried derived-category inputs — is available, but it produces the `k`-fold derived tensor
power only, neither its lowest homology nor the sign of the `S_k`-action on it, and it says
nothing about `H_k(C, Sym^k_{B̲}(F))`.

Here `H_l(C, -) = L_lπ_!` is the `l`th left derived functor of the colimit over `Cᵒᵖ` at linear
coefficients, which is the definition of Tag 08PF. -/
public def QuillenSignedCoinvariants (B : Type u) [CommRing B] : Prop :=
  ∀ (C : Type u) [SmallCategory C] (U : CosimplicialObject C), IsPointResolution U →
    ∀ F : Cᵒᵖ ⥤ ModuleCat.{u} B, (∀ X, Module.Flat B (F.obj X)) →
      IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj F) →
        ∀ k : ℕ, Nonempty (SignedTensorPower.signedCoinvariants B
            (↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 1).obj F)) k ≃ₗ[B]
          ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived k).obj
            (symmetricPowerDiagram C B F k)))

/-- **Remark 08SG.** Let `C` be a small category with the chaotic topology, `B` a commutative
ring, `F` a flat `B̲`-module on `C` — a diagram `F : Cᵒᵖ ⥤ ModuleCat B`, every presheaf being a
sheaf for the chaotic topology — with `H_0(C, F) = 0`, and let `U_•` be a point resolution as in
Tag 08Q9: the situation of Tag 08RD. Assume the coefficient ring satisfies the coinvariants
description `Stacks.ChaoticSite.QuillenSignedCoinvariants`, which is the remark's own deduction
including the sign character. Then there is a comparison `e` of `H_k(C, Sym^k_{B̲}(F))` with
those coinvariants and a `B`-linear map

`φ : H_k(C, Sym^k_{B̲}(F)) → ∧^k_B(H_1(C, F))`

such that `φ` takes the class of `x_1 ⊗ ⋯ ⊗ x_k` to `x_1 ∧ ⋯ ∧ x_k`; `φ` is surjective, is the
only linear map with that property, has `2`-torsion kernel, and is bijective — so that
`H_k(C, Sym^k_{B̲}(F)) = ∧^k_B(H_1(C, F))` as the remark asserts — as soon as `2` is invertible
in `B`.

The invertibility of `2` cannot be dropped: see
`Stacks.SignedTensorPower.not_injective_toExteriorPower_int`.

This theorem carries no `@[stacks 08SG]` attribute, and must not be given one: its hypothesis
`hQ` is the remark's omitted step, and that step is false at `B = ℤ` by
`Stacks.ChaoticSite.not_quillenSignedCoinvariants_int`; see the module docstring section
`Why the theorem below carries no @[stacks 08SG] attribute`. The remark's conclusion itself is
true over every commutative ring and is
`Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram`, which carries
the tag. -/
public theorem exteriorPower_leftDerivedColim_symmetricPowerDiagram
    (C : Type u) [SmallCategory C] (B : Type u) [CommRing B]
    (hQ : QuillenSignedCoinvariants B)
    (U : CosimplicialObject C) (hU : IsPointResolution U)
    (F : Cᵒᵖ ⥤ ModuleCat.{u} B) (hF : ∀ X, Module.Flat B (F.obj X))
    (h₀ : IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj F))
    (k : ℕ) :
    ∃ (e : SignedTensorPower.signedCoinvariants B
          (↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 1).obj F)) k ≃ₗ[B]
        ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived k).obj
          (symmetricPowerDiagram C B F k)))
      (φ : ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived k).obj
          (symmetricPowerDiagram C B F k)) →ₗ[B]
        ⋀[B]^k ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 1).obj F)),
      Function.Surjective φ ∧
      (∀ x : Fin k → ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 1).obj F),
        φ (e (Representation.Coinvariants.mk _ (⨂ₜ[B] i, x i))) =
          exteriorPower.ιMulti B k x) ∧
      (∀ y, φ y = 0 → (2 : B) • y = 0) ∧
      (∀ ψ : ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived k).obj
            (symmetricPowerDiagram C B F k)) →ₗ[B]
          ⋀[B]^k ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 1).obj F),
        (∀ x, ψ (e (Representation.Coinvariants.mk _ (⨂ₜ[B] i, x i))) =
          exteriorPower.ιMulti B k x) → ψ = φ) ∧
      (IsUnit (2 : B) → Function.Bijective φ) := by
  obtain ⟨e⟩ := hQ C U hU F hF h₀ k
  have hker : ∀ y, (SignedTensorPower.toExteriorPower B _ k) (e.symm y) = 0 → (2 : B) • y = 0 := by
    intro y hy
    have h2 := SignedTensorPower.two_smul_eq_zero_of_mem_ker B _ k hy
    have he : e ((2 : B) • e.symm y) = (2 : B) • y := by
      rw [map_smul, e.apply_symm_apply]
    rw [h2, map_zero] at he
    exact he.symm
  have hsurj : Function.Surjective
      ((SignedTensorPower.toExteriorPower B _ k).comp e.symm.toLinearMap) :=
    (SignedTensorPower.toExteriorPower_surjective B _ k).comp e.symm.surjective
  refine ⟨e, (SignedTensorPower.toExteriorPower B _ k).comp e.symm.toLinearMap, hsurj, ?_, hker,
    ?_, ?_⟩
  · intro x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, SignedTensorPower.toExteriorPower_mk_tprod]
  · intro ψ hψ
    have h1 : ψ.comp e.toLinearMap = SignedTensorPower.toExteriorPower B _ k :=
      SignedTensorPower.toExteriorPower_unique B _ k _ fun x => hψ x
    refine LinearMap.ext fun y => ?_
    have h2 := LinearMap.congr_fun h1 (e.symm y)
    simpa using h2
  · intro h2
    refine ⟨fun y z hyz => ?_, hsurj⟩
    have hd := hker (y - z) (by rw [map_sub, map_sub]; exact sub_eq_zero.mpr hyz)
    exact sub_eq_zero.mp ((h2.smul_eq_zero).mp hd)

end Stacks.ChaoticSite

end
