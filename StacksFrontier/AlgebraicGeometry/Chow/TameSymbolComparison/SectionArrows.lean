module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.ChainArrow
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.DimensionFunctionStalk
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.OrderFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocity
public import StacksCore.Tactic.StacksAttribute

/-!
# The arrows of Stacks 0EAY at `i = 1` from the tame symbol of Section 42.5

Let `X` be a locally Noetherian scheme with a dimension function `δ`. For a specialization
`x ⇝ x'` with `δ(x) = δ(x') + 1` the local ring `A = 𝒪_{closure {x}, x'}` is a one-dimensional
Noetherian local domain with fraction field `κ(x)`
(`Stacks.Chow.ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub`), so it carries

* the tame symbol `d_A` of Section 42.5 (Stacks 02Q1), descended to
  `K^M_2(κ(x)) → K^M_1(κ(x'))` (`Stacks.Chow.sectionTameComponent`), and
* the order of vanishing `ord_A : K^M_1(κ(x)) = κ(x)^* → ℤ = K^M_0(κ(x'))`
  (`Stacks.Chow.sectionOrdComponent`).

Both are locally finite in `x'`, so `Stacks.Chow.chainArrow` turns them into the two displayed
arrows of Stacks 0EAY at `i = 1`:

`⨁_{δ(x) = j + 2} K^M_2(κ(x)) ⟶ ⨁_{δ(x) = j + 1} K^M_1(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_0(κ(x))`

(`Stacks.Chow.sectionTameArrow`, `Stacks.Chow.sectionOrdArrow`).

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (δ : DimensionFunction X)

omit [IsLocallyNoetherian X] in
/-- A drop of one of a dimension function along a specialization makes the local ring of the
closure one-dimensional. -/
theorem ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction {x x' : X} (h : x ⤳ x')
    (hd : δ x = δ x' + 1) :
    ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp h))) = 1 := by
  rw [ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub δ x, hd,
    show (δ x' + 1 - δ x').toNat = 1 by omega]
  rfl

/-- **The degree-two local component**: the tame symbol of Section 42.5 of
`𝒪_{closure {x}, x'}`, descended to Milnor K-theory and read in `K^M_1(κ(x'))`. -/
def sectionTameComponent (x x' : X) (h : x ⤳ x') (hd : δ x = δ x' + 1) :
    MilnorKTheory ↥(X.residueField x) (1 + 1) →+ MilnorKTheory ↥(X.residueField x') 1 :=
  letI : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  (milnorKOneTransport (pointClosureResidueFieldEquiv x (specializes_iff_mem_closure.mp h))).comp
    (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x)
      (pointClosurePoint x (specializes_iff_mem_closure.mp h))
      (ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ h hd))

/-- The degree-two local component is locally finite. -/
theorem sectionTameComponent_locallyFinite :
    ChainArrowLocallyFinite (⇑δ) 1 (sectionTameComponent δ) := by
  intro x α U hU
  classical
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  have hV : IsCompact ((((integralComponentAt x).subschemeι ⁻¹ᵁ U) :
      Set (integralComponentAt x).subscheme) : Set (integralComponentAt x).subscheme) :=
    ((integralComponentAt x).subschemeι.isClosedEmbedding.isInducing.isCompact_preimage
      (integralComponentAt x).subschemeι.isClosedEmbedding.isClosed_range hU)
  have hfin := finite_stalkMilnorBoundary_ne_zero (pointClosureFunctionFieldEquiv x)
    ((integralComponentAt x).subschemeι ⁻¹ᵁ U) hV α
  refine (hfin.image fun z ↦ ((integralComponentAt x).subschemeι z.1 : X)).subset ?_
  rintro x' ⟨hx'U, h, hd, hne⟩
  have hm := specializes_iff_mem_closure.mp h
  refine ⟨⟨pointClosurePoint x hm,
    ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ h hd⟩, ⟨?_, ?_⟩,
    subschemeι_pointClosurePoint x hm⟩
  · show (integralComponentAt x).subschemeι (pointClosurePoint x hm) ∈ (U : Set X)
    rw [subschemeι_pointClosurePoint x hm]
    exact hx'U
  · intro hzero
    refine hne ?_
    show milnorKOneTransport _ (stalkMilnorBoundary _ _ _ α) = 0
    exact (congrArg _ hzero).trans (map_zero _)

/-- **The first displayed arrow of Stacks 0EAY at `i = 1`**, from the tame symbol of
Section 42.5. -/
@[stacks 0EAY "the first displayed arrow in the case i = 1: for a Noetherian (here: locally \
Noetherian) scheme X with a dimension function δ, the map ⊕_{δ(x) = j + 1} K^M_2(κ(x)) ⟶ \
⊕_{δ(x) = j} K^M_1(κ(x)) whose coefficient at x' is the sum over the points x specializing to x' \
of the tame symbol ∂_A of Section 42.5 of the one-dimensional local ring A = 𝒪_{closure {x}, x'}"]
def sectionTameArrow (j : ℤ) :
    DimMilnorChainGroup X δ (j + 1) (1 + 1) →+ DimMilnorChainGroup X δ j 1 :=
  chainArrow (⇑δ) 1 (sectionTameComponent δ) (sectionTameComponent_locallyFinite δ) j

/-- The order of vanishing of the one-dimensional local ring `𝒪_{closure {x}, x'}` on
`κ(x)^*`. -/
def sectionOrdHom (x x' : X) (h : x ⤳ x') (hd : δ x = δ x' + 1) :
    MilnorKTheory ↥(X.residueField x) 1 →+ ℤ :=
  letI : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  letI := stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (pointClosurePoint x (specializes_iff_mem_closure.mp h))
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (pointClosurePoint x (specializes_iff_mem_closure.mp h))
  haveI : Ring.KrullDimLE 1 ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp h))) :=
    Ring.krullDimLE_iff.2 (by
      rw [ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ h hd]; exact_mod_cast le_rfl)
  (MonoidHom.toAdditive (ordIntHom ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp h))) ↥(X.residueField x))).comp
    (milnorKTheoryOneAddEquiv ↥(X.residueField x)).toAddMonoidHom

/-- **The degree-one local component**: the order of vanishing of `𝒪_{closure {x}, x'}`, read in
`K^M_0(κ(x')) = ℤ`. -/
def sectionOrdComponent (x x' : X) (h : x ⤳ x') (hd : δ x = δ x' + 1) :
    MilnorKTheory ↥(X.residueField x) (0 + 1) →+ MilnorKTheory ↥(X.residueField x') 0 :=
  (milnorKTheoryZeroAddEquiv ↥(X.residueField x')).symm.toAddMonoidHom.comp
    (sectionOrdHom δ x x' h hd)

/-- The degree-one local component is locally finite: a unit of `κ(x)` comes from a unit of the
local rings on an open set containing the generic point of `closure {x}`. -/
theorem sectionOrdComponent_locallyFinite :
    ChainArrowLocallyFinite (⇑δ) 0 (sectionOrdComponent δ) := by
  intro x α U hU
  classical
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  set f := Additive.toMul (milnorKTheoryOneAddEquiv ↥(X.residueField x) α)
  have hV : IsCompact ((((integralComponentAt x).subschemeι ⁻¹ᵁ U) :
      Set (integralComponentAt x).subscheme) : Set (integralComponentAt x).subscheme) :=
    ((integralComponentAt x).subschemeι.isClosedEmbedding.isInducing.isCompact_preimage
      (integralComponentAt x).subschemeι.isClosedEmbedding.isClosed_range hU)
  obtain ⟨O, hO, hOu⟩ := exists_isOpen_forall_isUnit_stalk (pointClosureFunctionFieldEquiv x)
    (f : ↥(X.residueField x)) f.ne_zero
  have hfin := finite_coheight_eq_one_of_notMem_isOpen
    ((integralComponentAt x).subschemeι ⁻¹ᵁ U) O hV hO
  refine (hfin.image fun z ↦ ((integralComponentAt x).subschemeι z : X)).subset ?_
  rintro x' ⟨hx'U, h, hd, hne⟩
  have hm := specializes_iff_mem_closure.mp h
  have hdim := ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ h hd
  refine ⟨pointClosurePoint x hm, ⟨?_, ?_, ?_⟩, subschemeι_pointClosurePoint x hm⟩
  · show (integralComponentAt x).subschemeι (pointClosurePoint x hm) ∈ (U : Set X)
    rw [subschemeι_pointClosurePoint x hm]
    exact hx'U
  · intro hzO
    refine hne ?_
    obtain ⟨u, hu, hue⟩ := hOu _ hzO
    let := stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
      (pointClosurePoint x hm)
    have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
      (pointClosurePoint x hm)
    have : Ring.KrullDimLE 1 ((integralComponentAt x).subscheme.presheaf.stalk
        (pointClosurePoint x hm)) :=
      Ring.krullDimLE_iff.2 (by rw [hdim]; exact_mod_cast le_rfl)
    have h0 : sectionOrdHom δ x x' h hd α = 0 := by
      show ordInt _ (f : ↥(X.residueField x)) f.ne_zero = 0
      have hval : algebraMap _ ↥(X.residueField x) u = (f : ↥(X.residueField x)) := hue
      rw [← ordInt_val_congr ((integralComponentAt x).subscheme.presheaf.stalk
        (pointClosurePoint x hm)) hval (by rw [hval]; exact f.ne_zero) f.ne_zero]
      exact ordInt_eq_zero_of_isUnit _ hu _
    show (milnorKTheoryZeroAddEquiv _).symm (sectionOrdHom δ x x' h hd α) = 0
    rw [h0, map_zero]
  · exact coheight_eq_one_of_oneDimPoint ⟨pointClosurePoint x hm, hdim⟩

/-- **The second displayed arrow of Stacks 0EAY at `i = 1`**, from the order of vanishing. -/
@[stacks 0EAY "the second displayed arrow in the case i = 1: for a Noetherian (here: locally \
Noetherian) scheme X with a dimension function δ, the map ⊕_{δ(x) = j + 1} K^M_1(κ(x)) ⟶ \
⊕_{δ(x) = j} K^M_0(κ(x)) whose coefficient at x' is the sum over the points x specializing to x' \
of ∂_A = ord_A on κ(x)^* = K^M_1(κ(x)) for A = 𝒪_{closure {x}, x'}, with values in ℤ = K^M_0"]
def sectionOrdArrow (j : ℤ) :
    DimMilnorChainGroup X δ (j + 1) (0 + 1) →+ DimMilnorChainGroup X δ j 0 :=
  chainArrow (⇑δ) 0 (sectionOrdComponent δ) (sectionOrdComponent_locallyFinite δ) j

end Stacks.Chow

end
