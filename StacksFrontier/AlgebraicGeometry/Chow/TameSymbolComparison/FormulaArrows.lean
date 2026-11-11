module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.FormulaComparison
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.SectionComplex
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Transport
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0EAY at `i = 1` for the arrows built from the tame symbol of Section 42.5

Stacks 0EAY: for a discrete valuation ring, and more generally for a one-dimensional local
domain `A`, the tame symbol `∂_A : K^M_{i+1}(F) → K^M_i(κ)` is "defined as in Section 0EAH"; for a
Noetherian scheme `X` with a dimension function `δ` these tame symbols give the arrows

`⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_i(κ(x)) ⟶ ⨁_{δ(x) = j - 1} K^M_{i-1}(κ(x))`,

and "when `i = 1` and `j` arbitrary" their composition is zero "by Lemma 0EAX".

In degree two, Section 42.5 (Stacks 0EAH) constructs `∂_A : F^* × F^* → κ^*` by the recipe of
Stacks 0EAQ (`Stacks.Chow.formulaTameSymbol`). This file descends that symbol to
`K^M_2(F) → K^M_1(κ)` through the Steinberg relation 0EAK it satisfies
(`Stacks.Chow.formulaMilnorKTwoTameSymbol`), builds from it the first displayed arrow at `i = 1`
(`Stacks.Chow.sectionFormulaTameArrow`), and proves that its composite with the second arrow,
built from the orders of vanishing (`Stacks.Chow.sectionOrdArrow`), is zero
(`Stacks.Chow.sectionOrdArrow_comp_sectionFormulaTameArrow_eq_zero`).

The proof goes through the comparison `Stacks.Chow.regularModuleSymbol_eq_tameSymbolValue`: the
recipe of Stacks 0EAQ agrees with the periodic-determinant symbol `d_A` of Stacks 02Q1, so the
arrow built from the recipe is the arrow `Stacks.Chow.sectionTameArrow` built from `d_A`
(`Stacks.Chow.sectionFormulaTameArrow_eq_sectionTameArrow`), whose composite with the order arrow
vanishes by Lemma 0EAX (`Stacks.Chow.sectionOrdArrow_comp_sectionTameArrow_eq_zero`).

## Main definitions

* `Stacks.Chow.TameSymbol.milnorKTwo` — a tame symbol on the units of a field, descended to the
  degree-two Milnor K-group.
* `Stacks.Chow.formulaMilnorKTwoTameSymbol` — the tame symbol of Stacks 0EAQ on `K^M_2`.
* `Stacks.Chow.sectionFormulaTameArrow` — the first displayed arrow of Stacks 0EAY at `i = 1`,
  from the tame symbol of Section 42.5.

## Main results

* `Stacks.Chow.formulaMilnorKTwoTameSymbol_eq_milnorKTwoTameSymbol` — on `K^M_2` the symbol of
  Stacks 0EAQ is the symbol `d_A` of Stacks 02Q1.
* `Stacks.Chow.sectionOrdArrow_comp_sectionFormulaTameArrow_eq_zero` — Stacks 0EAY at `i = 1`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u v

namespace Stacks.Chow

/-! ### Descending a tame symbol to the degree-two Milnor K-group -/

namespace TameSymbol

variable {A : Type u} [CommRing A] [IsLocalRing A] {K : Type v} [Field K] [Algebra A K]
  [IsFractionRing A K] (symb : TameSymbol A K)

/-- A tame symbol read as a pairing additive in each variable. -/
def pairing : Additive Kˣ →+ Additive Kˣ →+ Additive (ResidueField A)ˣ where
  toFun x :=
    { toFun := fun y ↦ Additive.ofMul (symb (Additive.toMul x) (Additive.toMul y))
      map_zero' := congrArg Additive.ofMul (symb.one_right _)
      map_add' := fun _ _ ↦ congrArg Additive.ofMul (symb.map_mul_right _ _ _) }
  map_zero' := AddMonoidHom.ext fun _ ↦ congrArg Additive.ofMul (symb.one_left _)
  map_add' _ _ := AddMonoidHom.ext fun _ ↦ congrArg Additive.ofMul (symb.map_mul_left _ _ _)

/-- A tame symbol as a `ℤ`-linear map on the tensor square of the unit group. -/
def tensor : TensorProduct ℤ (Additive Kˣ) (Additive Kˣ) →ₗ[ℤ] Additive (ResidueField A)ˣ :=
  AddMonoidHom.toIntLinearMap (TensorProduct.liftAddHom symb.pairing fun r x y ↦ by
    rw [map_zsmul, map_zsmul, AddMonoidHom.coe_smul, Pi.smul_apply])

/-- On a pure tensor the linear tame symbol is the tame symbol. -/
theorem tensor_tmul (f g : Kˣ) :
    symb.tensor (Additive.ofMul f ⊗ₜ[ℤ] Additive.ofMul g) = Additive.ofMul (symb f g) := rfl

/-- **Stacks 0EAK.** The linear tame symbol kills the Steinberg tensors. -/
theorem milnorKTwoSteinbergSubmodule_le_ker :
    milnorKTwoSteinbergSubmodule K ≤ LinearMap.ker symb.tensor := by
  rw [milnorKTwoSteinbergSubmodule, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  refine LinearMap.mem_ker.2 ?_
  rw [tensor_tmul, symb.steinberg _ _ (by simp)]
  rfl

/-- **A tame symbol on the units of a field, descended to Milnor K-theory**: the homomorphism
`K^M_2(K) → K^M_1(κ)` sending `{f, g}` to `∂_A(f, g)`. -/
def milnorKTwo : MilnorKTheory K 2 →+ MilnorKTheory (ResidueField A) 1 :=
  (milnorKTheoryOneAddEquiv (ResidueField A)).symm.toAddMonoidHom.comp
    (((milnorKTwoSteinbergSubmodule K).liftQ symb.tensor
        symb.milnorKTwoSteinbergSubmodule_le_ker).toAddMonoidHom.comp
      (milnorKTwoEquivTensorProductQuotient K).toLinearMap.toAddMonoidHom)

/-- The descended tame symbol sends the pure symbol `{f, g}` to `∂_A(f, g)`. -/
theorem milnorKTwo_pureSymbol (f g : Kˣ) :
    symb.milnorKTwo (milnorKTwoPureSymbol K f g) =
      (milnorKTheoryOneAddEquiv (ResidueField A)).symm (Additive.ofMul (symb f g)) := by
  simp only [milnorKTwo, milnorKTwoPureSymbol, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    AddEquiv.coe_toAddMonoidHom, Submodule.liftQ_apply, tensor_tmul]

end TameSymbol

/-! ### The tame symbol of Stacks 0EAQ on `K^M_2` -/

section Formula

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] (hdim : ringKrullDim A = 1)

/-- On the units of the fraction field, the tame symbol of Stacks 0EAQ is the tame symbol of
Stacks 02Q1. -/
theorem formulaTameSymbol_apply_eq_tameSymbol (f g : Kˣ) :
    formulaTameSymbol hdim K f g = AlgebraicGeometry.tameSymbol (K := K) hdim f g := by
  rw [← tameSymbolOfKrullDimOne_eq_formulaTameSymbol hdim K]
  exact eq_tameSymbol hdim (tameSymbolOfKrullDimOneDomain (K := K) hdim) f g

/-- **The tame symbol of Section 42.5 in degree two**: the symbol of Stacks 0EAQ on the fraction
field of a one-dimensional Noetherian local domain, descended along the presentation of Milnor
K-theory to `K^M_2(F) → K^M_1(κ)`. -/
def formulaMilnorKTwoTameSymbol : MilnorKTheory K 2 →+ MilnorKTheory (ResidueField A) 1 :=
  (formulaTameSymbol hdim K).milnorKTwo

omit [IsDomain A] in
/-- The tame symbol of Stacks 0EAQ on `K^M_2` sends `{f, g}` to `∂_A(f, g)`. -/
theorem formulaMilnorKTwoTameSymbol_pureSymbol (f g : Kˣ) :
    formulaMilnorKTwoTameSymbol (K := K) hdim (milnorKTwoPureSymbol K f g) =
      (milnorKTheoryOneAddEquiv (ResidueField A)).symm
        (Additive.ofMul (formulaTameSymbol hdim K f g)) :=
  (formulaTameSymbol hdim K).milnorKTwo_pureSymbol f g

/-- **On `K^M_2` the tame symbol of Stacks 0EAQ is the symbol `d_A` of Stacks 02Q1**, both
descended along the presentation of Milnor K-theory. -/
theorem formulaMilnorKTwoTameSymbol_eq_milnorKTwoTameSymbol :
    formulaMilnorKTwoTameSymbol (K := K) hdim = milnorKTwoTameSymbol (K := K) hdim := by
  refine AddMonoidHom.ext fun α ↦ ?_
  refine milnorKTwo_induction (P := fun α ↦ formulaMilnorKTwoTameSymbol (K := K) hdim α =
    milnorKTwoTameSymbol (K := K) hdim α) (fun f g ↦ ?_)
    (fun a b ha hb ↦ by rw [map_add, map_add, ha, hb]) α
  rw [formulaMilnorKTwoTameSymbol_pureSymbol, milnorKTwoTameSymbol_pureSymbol,
    formulaTameSymbol_apply_eq_tameSymbol]

end Formula

/-! ### The boundary at a one-dimensional point -/

section Stalk

variable {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] {K : Type u} [Field K]
  (e : ↥W.functionField ≃+* K)

/-- **The tame symbol of Section 42.5 at a one-dimensional point of `W`**: the symbol of Stacks
0EAQ of the local ring at `z`, a one-dimensional Noetherian local domain with fraction field `K`,
on `K^M_2(K)`. -/
def stalkFormulaMilnorBoundary (z : W) (hdim : ringKrullDim (W.presheaf.stalk z) = 1) :
    MilnorKTheory K 2 →+ MilnorKTheory ↥(W.residueField z) 1 :=
  letI := stalkAlgebraOfFunctionFieldEquiv e z
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  formulaMilnorKTwoTameSymbol (A := ↥(W.presheaf.stalk z)) (K := K) hdim

/-- The boundary built from the symbol of Stacks 0EAQ is the boundary built from the symbol of
Stacks 02Q1. -/
theorem stalkFormulaMilnorBoundary_eq_stalkMilnorBoundary (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1) :
    stalkFormulaMilnorBoundary e z hdim = stalkMilnorBoundary e z hdim :=
  letI := stalkAlgebraOfFunctionFieldEquiv e z
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  formulaMilnorKTwoTameSymbol_eq_milnorKTwoTameSymbol (A := ↥(W.presheaf.stalk z)) (K := K) hdim

end Stalk

/-! ### The arrows of Stacks 0EAY at `i = 1` -/

attribute [local instance] isIntegral_integralComponentAt

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (δ : DimensionFunction X)

/-- **The degree-two local component, from the tame symbol of Section 42.5**: the symbol of
Stacks 0EAQ of the one-dimensional local ring `𝒪_{closure {x}, x'}` on `K^M_2(κ(x))`, read in
`K^M_1(κ(x'))`. -/
def sectionFormulaTameComponent (x x' : X) (h : x ⤳ x') (hd : δ x = δ x' + 1) :
    MilnorKTheory ↥(X.residueField x) (1 + 1) →+ MilnorKTheory ↥(X.residueField x') 1 :=
  letI : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  (milnorKOneTransport (pointClosureResidueFieldEquiv x (specializes_iff_mem_closure.mp h))).comp
    (stalkFormulaMilnorBoundary (pointClosureFunctionFieldEquiv x)
      (pointClosurePoint x (specializes_iff_mem_closure.mp h))
      (ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ h hd))

/-- The local components built from the symbol of Stacks 0EAQ are those built from the symbol of
Stacks 02Q1. -/
theorem sectionFormulaTameComponent_eq_sectionTameComponent :
    sectionFormulaTameComponent δ = sectionTameComponent δ := by
  funext x x' h hd
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  rw [sectionFormulaTameComponent, sectionTameComponent,
    stalkFormulaMilnorBoundary_eq_stalkMilnorBoundary]

/-- The degree-two local components from the tame symbol of Section 42.5 are locally finite. -/
theorem sectionFormulaTameComponent_locallyFinite :
    ChainArrowLocallyFinite (⇑δ) 1 (sectionFormulaTameComponent δ) := by
  rw [sectionFormulaTameComponent_eq_sectionTameComponent]
  exact sectionTameComponent_locallyFinite δ

/-- **The first displayed arrow of Stacks 0EAY at `i = 1`, from the tame symbol of Section 42.5**:
`⨁_{δ(x) = j + 1} K^M_2(κ(x)) → ⨁_{δ(x) = j} K^M_1(κ(x))`, whose coefficient at `x'` is the sum
over the points `x` specializing to `x'` of the tame symbol `∂_A` of Stacks 0EAQ of the
one-dimensional local ring `A = 𝒪_{closure {x}, x'}`. -/
def sectionFormulaTameArrow (j : ℤ) :
    DimMilnorChainGroup X δ (j + 1) (1 + 1) →+ DimMilnorChainGroup X δ j 1 :=
  chainArrow (⇑δ) 1 (sectionFormulaTameComponent δ) (sectionFormulaTameComponent_locallyFinite δ) j

/-- The arrow built from the symbol of Stacks 0EAQ is the arrow built from the symbol of Stacks
02Q1. -/
theorem sectionFormulaTameArrow_eq_sectionTameArrow (j : ℤ) :
    sectionFormulaTameArrow δ j = sectionTameArrow δ j := by
  unfold sectionFormulaTameArrow sectionTameArrow
  congr 1
  exact sectionFormulaTameComponent_eq_sectionTameComponent δ

/-- **Stacks 0EAY: at `i = 1` the composition of the two displayed arrows is zero.** Let `X` be a
locally Noetherian scheme with a dimension function `δ`. For every `j`, the arrow
`⨁_{δ(x) = j + 2} K^M_2(κ(x)) → ⨁_{δ(x) = j + 1} K^M_1(κ(x))` built from the tame symbols
`∂_A` of Section 42.5 (the recipe of Stacks 0EAQ) of the one-dimensional local rings
`A = 𝒪_{closure {x}, x'}`, followed by the arrow
`⨁_{δ(x) = j + 1} K^M_1(κ(x)) → ⨁_{δ(x) = j} K^M_0(κ(x))` built from their orders of vanishing,
is zero.

As the remark says, this follows from Lemma 0EAX: the arrow is the arrow built from the symbol
`d_A` of Stacks 02Q1 (`Stacks.Chow.sectionFormulaTameArrow_eq_sectionTameArrow`, by
`Stacks.Chow.regularModuleSymbol_eq_tameSymbolValue`), and for that arrow the vanishing is
`Stacks.Chow.sectionOrdArrow_comp_sectionTameArrow_eq_zero`, which runs through Lemma 0EAX at the
two-dimensional local rings `𝒪_{closure {x}, y}`. -/
@[stacks 0EAY "the remark's closing sentence for the arrows of a Noetherian (here: locally \
Noetherian) scheme X with a dimension function δ: when i = 1 and j is arbitrary the composition \
⊕_{δ(x) = j + 2} K^M_2(κ(x)) ⟶ ⊕_{δ(x) = j + 1} K^M_1(κ(x)) ⟶ ⊕_{δ(x) = j} K^M_0(κ(x)) of the \
two displayed arrows is zero, the first built from the tame symbols ∂_A of Section 42.5, i.e. the \
recipe of Stacks 0EAQ (Stacks.Chow.formulaTameSymbol, descended to K^M_2 by the relation 0EAK), \
of the one-dimensional local rings A = 𝒪_{closure {x}, x'}, the second from their orders of \
vanishing; the proof runs through Lemma 0EAX at the two-dimensional local rings \
𝒪_{closure {x}, y}. The remark's statement that it is not clear the composition is zero in \
general is not a claim, and the citation [Kato-Milnor-K] for excellent X is not formalized"]
theorem sectionOrdArrow_comp_sectionFormulaTameArrow_eq_zero (j : ℤ) :
    (sectionOrdArrow δ j).comp (sectionFormulaTameArrow δ (j + 1)) = 0 := by
  rw [sectionFormulaTameArrow_eq_sectionTameArrow]
  exact sectionOrdArrow_comp_sectionTameArrow_eq_zero δ j

end Stacks.Chow

end
