module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.SectionArrows
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.Arrows
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureSummandIdentity
public import StacksCore.Tactic.StacksAttribute

/-!
# The arrows of Stacks 0EAY at `i = 1` form a complex, for any Noetherian dimension function

Let `X` be a locally Noetherian scheme with a dimension function `δ`. The two displayed arrows of
Stacks 0EAY at `i = 1`,

`⨁_{δ(x) = j + 2} K^M_2(κ(x)) ⟶ ⨁_{δ(x) = j + 1} K^M_1(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_0(κ(x))`,

are `Stacks.Chow.sectionTameArrow` (the tame symbol of Section 42.5 of the one-dimensional local
rings `𝒪_{closure {x}, x'}`) and `Stacks.Chow.sectionOrdArrow` (their order of vanishing). The
remark says: "When `i = 1` and `j` arbitrary, this [that the composition is zero] follows from
Lemma 0EAX." This file proves it:
`Stacks.Chow.sectionOrdArrow_comp_sectionTameArrow_eq_zero`.

## The argument

The coefficient of the composite at a point `y` with `δ(y) = j` is a double sum over the points
`x` with `δ(x) = j + 2` and `x'` with `δ(x') = j + 1`, of `ord_{𝒪_{closure {x'}, y}}` of the tame
symbol `∂_{𝒪_{closure {x}, x'}}` of the class at `x`. Its joint support is finite, so the two sums
may be interchanged, and it suffices to show that for each `x` the sum over `x'` vanishes. If `x`
does not specialize to `y` every term is zero. Otherwise the local ring `A = 𝒪_{closure {x}, y}`
is a two-dimensional Noetherian local domain, because `δ(x) - δ(y) = 2`
(`Stacks.Chow.ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub`). The points `x'` with
`δ(x') = j + 1` and `x ⇝ x' ⇝ y` are exactly the points of `closure {x}` cut out by the height-one
primes `𝔮` of `A` (`Stacks.Chow.heightOnePrimeEquivIntermediatePoint`), and the term at `x'` is the
term `ord_{A/𝔮}(∂_{A_𝔮}(α))` of the local reciprocity
(`Stacks.Chow.ord_eq_residueUnitOrder`, `Stacks.Chow.localMilnorBoundary_transport`). The sum of
those vanishes by Lemma 0EAX (`AlgebraicGeometry.sum_localMilnorBoundaryOrder_eq_zero`).

No excellence, Nagata or finite-normalization hypothesis appears, and no base scheme: the only
hypotheses are those of the remark, `X` (locally) Noetherian with a dimension function.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-! ### The order of vanishing of a local ring, read on the scheme -/

section Stalk

variable {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] {K : Type u} [Field K]
  (e : ↥W.functionField ≃+* K)

/-- At a point of an integral locally Noetherian scheme whose local ring is one-dimensional, the
order of vanishing `ordInt` of that local ring, computed in a field `K` identified with the
function field, is the order of vanishing of Stacks 02MD of the corresponding rational
function. -/
theorem ordInt_stalkAlgebraOfFunctionFieldEquiv_eq_ord (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1) (f : K) (hf : f ≠ 0) :
    letI := stalkAlgebraOfFunctionFieldEquiv e z
    haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
    haveI : Ring.KrullDimLE 1 ↥(W.presheaf.stalk z) :=
      Ring.krullDimLE_iff.2 (by rw [hdim]; exact_mod_cast le_rfl)
    ordInt (W.presheaf.stalk z) f hf = W.ord (e.symm f) z := by
  let := stalkAlgebraOfFunctionFieldEquiv e z
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  have : Ring.KrullDimLE 1 ↥(W.presheaf.stalk z) :=
    Ring.krullDimLE_iff.2 (by rw [hdim]; exact_mod_cast le_rfl)
  have hne : e.symm f ≠ 0 := (map_ne_zero e.symm).2 hf
  rw [ord_eq_ordInt z (coheight_eq_one_of_oneDimPoint ⟨z, hdim⟩) _ hne]
  let σ : ↥W.functionField ≃ₐ[↥(W.presheaf.stalk z)] K := { e with commutes' := fun a ↦ rfl }
  have hσ : σ (e.symm f) = f := e.apply_symm_apply _
  rw [← ordInt_algEquiv (↥(W.presheaf.stalk z)) σ (e.symm f) hne (by rwa [hσ])]
  exact ordInt_val_congr _ hσ.symm _ _

end Stalk

/-! ### The composite as a double sum -/

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (δ : DimensionFunction X)

open Classical in
/-- The contribution of a pair `(x, x')` to the coefficient at `y` of the composite of the two
arrows: `ord_{𝒪_{closure {x'}, y}}` of the tame symbol of `𝒪_{closure {x}, x'}` of the class of
`ξ` at `x`. -/
def sectionOrdTameTerm (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1))
    (y : {x : X | δ x = j}) (x : {x : X | δ x = j + 1 + 1}) (x' : {x : X | δ x = j + 1}) : ℤ :=
  if h : (x'.1 : X) ⤳ (y.1 : X) then
    sectionOrdHom δ x'.1 y.1 h (by rw [x'.2, y.2])
      (chainArrowTerm (⇑δ) 1 (sectionTameComponent δ) (j + 1) ξ x x')
  else 0

/-- If `x'` specializes to `y`, the term `sectionOrdTameTerm` is the order of vanishing
`sectionOrdHom` of the tame-symbol term `chainArrowTerm` from `x` to `x'`. -/
theorem sectionOrdTameTerm_of_specializes (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1))
    (y : {x : X | δ x = j}) (x : {x : X | δ x = j + 1 + 1}) (x' : {x : X | δ x = j + 1})
    (h : (x'.1 : X) ⤳ (y.1 : X)) :
    sectionOrdTameTerm δ j ξ y x x' = sectionOrdHom δ x'.1 y.1 h (by rw [x'.2, y.2])
      (chainArrowTerm (⇑δ) 1 (sectionTameComponent δ) (j + 1) ξ x x') := by
  rw [sectionOrdTameTerm, dite_eq_left h]

/-- If `x'` does not specialize to `y`, the term `sectionOrdTameTerm` vanishes. -/
theorem sectionOrdTameTerm_of_not_specializes (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j})
    (x : {x : X | δ x = j + 1 + 1}) (x' : {x : X | δ x = j + 1}) (h : ¬(x'.1 : X) ⤳ (y.1 : X)) :
    sectionOrdTameTerm δ j ξ y x x' = 0 := by
  rw [sectionOrdTameTerm, dite_eq_right h]

/-- If the tame-symbol term `chainArrowTerm` from `x` to `x'` vanishes, so does
`sectionOrdTameTerm`. -/
theorem sectionOrdTameTerm_of_chainArrowTerm_eq_zero (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j})
    (x : {x : X | δ x = j + 1 + 1}) (x' : {x : X | δ x = j + 1})
    (h : chainArrowTerm (⇑δ) 1 (sectionTameComponent δ) (j + 1) ξ x x' = 0) :
    sectionOrdTameTerm δ j ξ y x x' = 0 := by
  rw [sectionOrdTameTerm]
  split
  · rw [h, map_zero]
  · rfl

/-- **The coefficient of the composite is a double sum.** -/
theorem milnorKTheoryZeroAddEquiv_sectionOrdArrow_sectionTameArrow (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j}) :
    milnorKTheoryZeroAddEquiv ↥(X.residueField y.1)
        ((sectionOrdArrow δ j (sectionTameArrow δ (j + 1) ξ)).1 y) =
      ∑ᶠ x' : {x : X | δ x = j + 1}, ∑ᶠ x : {x : X | δ x = j + 1 + 1},
        sectionOrdTameTerm δ j ξ y x x' := by
  rw [sectionOrdArrow, chainArrow_apply, chainArrowCoeff, AddEquiv.map_finsum]
  refine finsum_congr fun x' ↦ ?_
  by_cases h : (x'.1 : X) ⤳ (y.1 : X)
  · rw [chainArrowTerm_of_specializes j _ x' y h]
    show milnorKTheoryZeroAddEquiv _ ((milnorKTheoryZeroAddEquiv _).symm
      (sectionOrdHom δ x'.1 y.1 h _ ((sectionTameArrow δ (j + 1) ξ).1 x'))) = _
    rw [AddEquiv.apply_symm_apply, sectionTameArrow, chainArrow_apply, chainArrowCoeff,
      (sectionOrdHom δ x'.1 y.1 h _).map_finsum (finite_support_chainArrowTerm (j + 1) ξ x')]
    exact finsum_congr fun x ↦ (sectionOrdTameTerm_of_specializes δ j ξ y x x' h).symm
  · rw [chainArrowTerm_of_not_specializes j _ x' y h, map_zero,
      finsum_congr fun x ↦ sectionOrdTameTerm_of_not_specializes δ j ξ y x x' h, finsum_zero]

/-- A nonzero term `sectionOrdTameTerm` forces `x ⤳ x'` and `x' ⤳ y`. -/
private theorem specializes_of_sectionOrdTameTerm_ne_zero (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j})
    (x : {x : X | δ x = j + 1 + 1}) (x' : {x : X | δ x = j + 1})
    (hne : sectionOrdTameTerm δ j ξ y x x' ≠ 0) :
    (x.1 : X) ⤳ (x'.1 : X) ∧ (x'.1 : X) ⤳ (y.1 : X) :=
  ⟨by
    by_contra hnot
    exact hne (sectionOrdTameTerm_of_chainArrowTerm_eq_zero δ j ξ y x x'
      (chainArrowTerm_of_not_specializes (j + 1) ξ x x' hnot)), by
    by_contra hnot
    exact hne (sectionOrdTameTerm_of_not_specializes δ j ξ y x x' hnot)⟩

/-- The local ring of `closure {x}` at `y` is two-dimensional if `δ x = δ y + 2`. -/
private theorem ringKrullDim_pointClosureStalk_eq_two {Y : Scheme.{u}} (δ : DimensionFunction Y)
    {x y : Y} (hy : y ∈ closure ({x} : Set Y)) (hd : δ x = δ y + 2) :
    ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk (pointClosurePoint x hy)) =
      2 := by
  rw [ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub δ x hy,
    show (δ x - δ y).toNat = 2 by omega]
  rfl

/-- **The joint support of the double sum is finite.** -/
theorem finite_support_sectionOrdTameTerm (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j}) :
    (Function.support fun z : {x : X | δ x = j + 1 + 1} × {x : X | δ x = j + 1} ↦
      sectionOrdTameTerm δ j ξ y z.1 z.2).Finite := by
  classical
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y.1) isOpen_univ
  have hU : IsCompact (U : Set X) := hUaff.isCompact
  have hF : {x : {x : X | δ x = j + 1 + 1} | (x.1 : X) ∈ (U : Set X) ∧ ξ.1 x ≠ 0}.Finite :=
    ξ.2 U hU
  refine (hF.biUnion (fun x _ ↦ (finite_chainArrowTerm_ne_zero
    (sectionTameComponent_locallyFinite δ) (j + 1) ξ x U hU).image
    (fun x' ↦ ((x, x') : {x : X | δ x = j + 1 + 1} × {x : X | δ x = j + 1})))).subset ?_
  rintro ⟨x, x'⟩ hz
  have hne : sectionOrdTameTerm δ j ξ y x x' ≠ 0 := hz
  have hterm : chainArrowTerm (⇑δ) 1 (sectionTameComponent δ) (j + 1) ξ x x' ≠ 0 := fun h ↦
    hne (sectionOrdTameTerm_of_chainArrowTerm_eq_zero δ j ξ y x x' h)
  have hax : ξ.1 x ≠ 0 := fun h ↦ hterm (chainArrowTerm_of_eq_zero (j + 1) ξ h x')
  obtain ⟨hspec, hspec'⟩ := specializes_of_sectionOrdTameTerm_ne_zero δ j ξ y x x' hne
  have hx'U : (x'.1 : X) ∈ (U : Set X) := hspec'.mem_open U.2 hyU
  have hxU : (x.1 : X) ∈ (U : Set X) := hspec.mem_open U.2 hx'U
  exact Set.mem_biUnion ⟨hxU, hax⟩ ⟨x', ⟨hx'U, hterm⟩, rfl⟩

/-- **The two sums may be interchanged.** -/
theorem finsum_sectionOrdTameTerm_comm (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j}) :
    (∑ᶠ x' : {x : X | δ x = j + 1}, ∑ᶠ x : {x : X | δ x = j + 1 + 1},
        sectionOrdTameTerm δ j ξ y x x') =
      ∑ᶠ x : {x : X | δ x = j + 1 + 1}, ∑ᶠ x' : {x : X | δ x = j + 1},
        sectionOrdTameTerm δ j ξ y x x' := by
  classical
  set T := fun (x : {x : X | δ x = j + 1 + 1}) (x' : {x : X | δ x = j + 1}) ↦
    sectionOrdTameTerm δ j ξ y x x'
  have hP := finite_support_sectionOrdTameTerm δ j ξ y
  set S : Set {x : X | δ x = j + 1 + 1} := Prod.fst '' Function.support
    (fun z : {x : X | δ x = j + 1 + 1} × {x : X | δ x = j + 1} ↦ T z.1 z.2)
  set S' : Set {x : X | δ x = j + 1} := Prod.snd '' Function.support
    (fun z : {x : X | δ x = j + 1 + 1} × {x : X | δ x = j + 1} ↦ T z.1 z.2)
  have hSfin : S.Finite := hP.image _
  have hS'fin : S'.Finite := hP.image _
  have hmemS : ∀ x x', T x x' ≠ 0 → x ∈ S := fun x x' h ↦ ⟨(x, x'), h, rfl⟩
  have hmemS' : ∀ x x', T x x' ≠ 0 → x' ∈ S' := fun x x' h ↦ ⟨(x, x'), h, rfl⟩
  have hinnerx : ∀ x', (∑ᶠ x, T x x') = ∑ᶠ x ∈ S, T x x' := fun x' ↦
    finsum_eq_finsum_mem_of_support_subset fun x hx ↦ hmemS x x' hx
  have hinnerx' : ∀ x, (∑ᶠ x', T x x') = ∑ᶠ x' ∈ S', T x x' := fun x ↦
    finsum_eq_finsum_mem_of_support_subset fun x' hx' ↦ hmemS' x x' hx'
  have houterx' : Function.support (fun x' ↦ ∑ᶠ x ∈ S, T x x') ⊆ S' := by
    intro x' hx'
    by_contra hnot
    exact hx' (finsum_mem_eq_zero_of_forall_eq_zero fun x _ ↦
      not_not.mp fun h ↦ hnot (hmemS' x x' h))
  have houterx : Function.support (fun x ↦ ∑ᶠ x' ∈ S', T x x') ⊆ S := by
    intro x hx
    by_contra hnot
    exact hx (finsum_mem_eq_zero_of_forall_eq_zero fun x' _ ↦
      not_not.mp fun h ↦ hnot (hmemS x x' h))
  calc (∑ᶠ x' : {x : X | δ x = j + 1}, ∑ᶠ x : {x : X | δ x = j + 1 + 1}, T x x')
      = ∑ᶠ x' : {x : X | δ x = j + 1}, ∑ᶠ x ∈ S, T x x' := finsum_congr hinnerx
    _ = ∑ᶠ x' ∈ S', ∑ᶠ x ∈ S, T x x' := finsum_eq_finsum_mem_of_support_subset houterx'
    _ = ∑ᶠ x ∈ S, ∑ᶠ x' ∈ S', T x x' := (finsum_mem_comm T hSfin hS'fin).symm
    _ = ∑ᶠ x : {x : X | δ x = j + 1 + 1}, ∑ᶠ x' ∈ S', T x x' :=
        (finsum_eq_finsum_mem_of_support_subset houterx).symm
    _ = ∑ᶠ x : {x : X | δ x = j + 1 + 1}, ∑ᶠ x' : {x : X | δ x = j + 1}, T x x' :=
        finsum_congr fun x ↦ (hinnerx' x).symm

/-! ### The order of vanishing component, read on the closure -/

/-- The degree-one local component is the order of vanishing of Stacks 02MD on `closure {x}`. -/
theorem sectionOrdHom_eq_ord (x x' : X) (h : x ⤳ x') (hd : δ x = δ x' + 1)
    (u : MilnorKTheory ↥(X.residueField x) 1) :
    letI : IsLocallyNoetherian (integralComponentAt x).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
    sectionOrdHom δ x x' h hd u =
      (integralComponentAt x).subscheme.ord
        ((pointClosureFunctionFieldEquiv x).symm
          ((Additive.toMul (milnorKTheoryOneAddEquiv ↥(X.residueField x) u) :
            (↥(X.residueField x))ˣ) : ↥(X.residueField x)))
        (pointClosurePoint x (specializes_iff_mem_closure.mp h)) := by
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  exact ordInt_stalkAlgebraOfFunctionFieldEquiv_eq_ord (pointClosureFunctionFieldEquiv x) _
    (ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ h hd) _ (Units.ne_zero _)

/-! ### The intermediate points, indexed by the dimension function -/

omit [IsLocallyNoetherian X] in
/-- An intermediate point of `closure {x}` lies one step below `x` for the dimension function. -/
theorem dimensionFunction_intermediatePointValue {x y : X} (hy : y ∈ closure ({x} : Set X))
    (z : PointClosureIntermediatePoint x hy) : δ (intermediatePointValue hy z) + 1 = δ x := by
  have h := ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub δ x
    (intermediatePointValue_mem_closure hy z)
  rw [show pointClosurePoint x (intermediatePointValue_mem_closure hy z) = z.1 from rfl,
    ringKrullDim_stalk_intermediatePoint_eq_one z.2.1] at h
  have h' : (δ x - δ (intermediatePointValue hy z)).toNat = 1 := by exact_mod_cast h.symm
  omega

/-- An intermediate point of `closure {x}`, read as a point of `X` one step below `x`. -/
def dimIntermediatePoint (j : ℤ) {x : X} (hx : δ x = j + 1 + 1) {y : X}
    (hy : y ∈ closure ({x} : Set X)) (z : PointClosureIntermediatePoint x hy) :
    {x : X | δ x = j + 1} :=
  ⟨intermediatePointValue hy z, by
    have := dimensionFunction_intermediatePointValue δ hy z
    change δ (intermediatePointValue hy z) = j + 1
    omega⟩

omit [IsLocallyNoetherian X] in
/-- The map `dimIntermediatePoint` from intermediate points of `closure {x}` to points of `X` is
injective. -/
theorem injective_dimIntermediatePoint (j : ℤ) {x : X} (hx : δ x = j + 1 + 1) {y : X}
    (hy : y ∈ closure ({x} : Set X)) : Function.Injective (dimIntermediatePoint δ j hx hy) := by
  intro z z' h
  have h' : (integralComponentAt x).subschemeι z.1 = (integralComponentAt x).subschemeι z'.1 :=
    congrArg (fun w : {x : X | δ x = j + 1} ↦ (w : X)) h
  exact Subtype.ext ((integralComponentAt x).subschemeι.isClosedEmbedding.injective h')

/-- A point between `x` and `y`, one step below `x`, is an intermediate point of `closure {x}`. -/
theorem exists_dimIntermediatePoint_eq (j : ℤ) {x : X} (hx : δ x = j + 1 + 1) {y : X}
    (hy : y ∈ closure ({x} : Set X)) (hyd : δ y = j) (x' : {x : X | δ x = j + 1})
    (hxx' : x ⤳ (x'.1 : X)) (hx'y : (x'.1 : X) ⤳ y) :
    ∃ z : PointClosureIntermediatePoint x hy, dimIntermediatePoint δ j hx hy z = x' := by
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  have hx'd : δ x'.1 = j + 1 := x'.2
  have hmem : (x'.1 : X) ∈ closure ({x} : Set X) := specializes_iff_mem_closure.mp hxx'
  have hone : Order.coheight (pointClosurePoint x hmem) = 1 :=
    coheight_eq_one_of_oneDimPoint ⟨pointClosurePoint x hmem,
      ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ hxx' (by omega)⟩
  have hdim2 := ringKrullDim_pointClosureStalk_eq_two δ hy (by omega)
  have htwo : Order.coheight (pointClosurePoint x hy) = 2 := by
    have h : ((Order.coheight (pointClosurePoint x hy) : ℕ∞) : WithBot ℕ∞) =
        ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hdim2]
      rfl
    exact WithBot.coe_inj.mp h
  have hspec2 : (integralComponentAt x).subschemeι (pointClosurePoint x hmem) ⤳
      (integralComponentAt x).subschemeι (pointClosurePoint x hy) := by
    rw [subschemeι_pointClosurePoint x hmem, subschemeι_pointClosurePoint x hy]
    exact hx'y
  have hle : pointClosurePoint x hy ≤ pointClosurePoint x hmem :=
    Scheme.le_iff_specializes.mpr
      ((integralComponentAt x).subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp hspec2)
  exact ⟨⟨pointClosurePoint x hmem,
    (coheight_eq_one_iff_isImmediateSpecialization_genericPoint _).mp hone,
    isImmediateSpecialization_of_coheight_eq_one_of_coheight_eq_two htwo hone hle⟩,
    Subtype.ext (subschemeι_pointClosurePoint x hmem)⟩

/-! ### The summand identity -/

/-- **The summand identity, at a height-one prime.** Let `x''` be a point of `W = closure {x}`
and `𝔮` a height-one prime of `𝒪_{W, x''}`, cutting out the point `x'`. The order of vanishing on
`closure {x'}` at `x''` of the tame symbol of `𝒪_{W, x'}` of a class `α ∈ K^M_2(κ(x))` is the order
along `𝒪_{W, x''} / 𝔮` of the Milnor `K_2` boundary at `𝔮` of the transport of `α`. -/
theorem sectionOrdHom_milnorKOneTransport_eq (x : X)
    [IsLocallyNoetherian (integralComponentAt x).subscheme]
    (x'' : (integralComponentAt x).subscheme)
    (q : {q : Ideal ↥((integralComponentAt x).subscheme.presheaf.stalk x'') //
      q.IsPrime ∧ q.height = 1}) [q.1.IsPrime]
    (hmem : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ∈
      closure ({x} : Set X))
    (hsp : (integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q) ⤳
      (integralComponentAt x).subschemeι x'')
    [IsLocallyNoetherian (integralComponentAt ((integralComponentAt x).subschemeι
      (intermediatePointOfHeightOnePrime x'' q))).subscheme]
    (hdimV : Order.coheight ((pointClosureInnerIso x
      (intermediatePointOfHeightOnePrime x'' q)).hom.base
        (intermediatePointClosurePoint x'' q)) = 1)
    (hw : (pointClosureInnerIso x (intermediatePointOfHeightOnePrime x'' q)).hom.base
        (intermediatePointClosurePoint x'' q) =
      pointClosurePoint ((integralComponentAt x).subschemeι
        (intermediatePointOfHeightOnePrime x'' q)) (specializes_iff_mem_closure.mp hsp))
    (hdim2 : ringKrullDim ↥((integralComponentAt x).subscheme.presheaf.stalk x'') = 2)
    (hB : ringKrullDim ↥((integralComponentAt x).subscheme.presheaf.stalk
      (intermediatePointOfHeightOnePrime x'' q)) = 1)
    (hd : δ ((integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q)) =
      δ ((integralComponentAt x).subschemeι x'') + 1)
    (α : MilnorKTheory ↥(X.residueField x) 2) :
    sectionOrdHom δ ((integralComponentAt x).subschemeι (intermediatePointOfHeightOnePrime x'' q))
        ((integralComponentAt x).subschemeι x'') hsp hd
        (milnorKOneTransport (pointClosureResidueFieldEquiv x hmem)
          (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x)
            (intermediatePointOfHeightOnePrime x'' q) hB α)) =
      localMilnorBoundaryOrder hdim2 q
        ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv x x'')).symm α) := by
  have h1 := toMul_milnorKOneRingEquiv (IsLocalRing.ResidueField.mapEquiv
    (stalkLocalizationAtPrimeEquiv x'' q))
    (localMilnorBoundary q ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv x x'')).symm α))
  rw [localMilnorBoundary_transport x x'' q hB α] at h1
  have hord := ord_eq_residueUnitOrder x x'' q hmem hsp hdimV
    (krullDimLE_one_quotient_heightOne hdim2 q) h1.symm
  rw [hw] at hord
  rwa [sectionOrdHom_eq_ord, toMul_milnorKOneTransport (pointClosureResidueFieldEquiv x hmem)
    (stalkMilnorBoundary (pointClosureFunctionFieldEquiv x)
      (intermediatePointOfHeightOnePrime x'' q) hB α)]

/-- **The summand identity.** For `x ⇝ y` with `δ(x) - δ(y) = 2` and a height-one prime `𝔮` of
the two-dimensional local ring `A = 𝒪_{closure {x}, y}`, the contribution of `x` and the point
cut out by `𝔮` to the composite is the contribution `ord_{A/𝔮}(∂_{A_𝔮}(α))` of `𝔮` to the local
reciprocity of Stacks 0EAX. -/
theorem sectionOrdTameTerm_dimIntermediatePoint (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j})
    (x : {x : X | δ x = j + 1 + 1}) (hxy : (x.1 : X) ⤳ (y.1 : X))
    [IsLocallyNoetherian (integralComponentAt (x.1 : X)).subscheme]
    (hdim2 : ringKrullDim ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy))) = 2)
    (q : {q : Ideal ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy))) //
        q.IsPrime ∧ q.height = 1}) :
    sectionOrdTameTerm δ j ξ y x
        (dimIntermediatePoint δ j x.2 (specializes_iff_mem_closure.mp hxy)
          (heightOnePrimeEquivIntermediatePoint hdim2 q)) =
      localMilnorBoundaryOrder hdim2 q
        ((milnorKTwoRingEquiv (pointClosureFractionRingEquiv (x.1 : X)
          (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)))).symm (ξ.1 x)) := by
  let _ : q.1.IsPrime := q.2.1
  have hmem := subschemeι_mem_closure (x.1 : X) (intermediatePointOfHeightOnePrime
    (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)
  have hsp : (integralComponentAt (x.1 : X)).subschemeι (intermediatePointOfHeightOnePrime
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q) ⤳ (y.1 : X) :=
    (specializes_intermediatePointOfHeightOnePrime _ q).map
      (integralComponentAt (x.1 : X)).subschemeι.continuous
  have hB : ringKrullDim ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (intermediatePointOfHeightOnePrime
        (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)) = 1 :=
    ringKrullDim_stalk_intermediatePoint_eq_one
      (isImmediateSpecialization_genericPoint_intermediatePointOfHeightOnePrime _ q)
  let _ : IsLocallyNoetherian (integralComponentAt ((integralComponentAt (x.1 : X)).subschemeι
      (intermediatePointOfHeightOnePrime
        (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q))).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt _).subschemeι
  have hw := pointClosureInnerIso_pointClosurePoint (x.1 : X) (intermediatePointOfHeightOnePrime
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)
    (specializes_intermediatePointOfHeightOnePrime _ q).mem_closure
    (specializes_iff_mem_closure.mp hsp)
  have hδ : δ ((integralComponentAt (x.1 : X)).subschemeι (intermediatePointOfHeightOnePrime
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)) = j + 1 :=
    (dimIntermediatePoint δ j x.2 (specializes_iff_mem_closure.mp hxy)
      (heightOnePrimeEquivIntermediatePoint hdim2 q)).2
  have hyd : δ y.1 = j := y.2
  have hd : δ ((integralComponentAt (x.1 : X)).subschemeι (intermediatePointOfHeightOnePrime
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)) = δ y.1 + 1 := by
    omega
  have hdimV : Order.coheight ((pointClosureInnerIso (x.1 : X) (intermediatePointOfHeightOnePrime
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)).hom.base
        (pointClosurePoint (intermediatePointOfHeightOnePrime
          (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q)
          (specializes_intermediatePointOfHeightOnePrime _ q).mem_closure)) = 1 := by
    rw [hw]
    exact coheight_eq_one_of_oneDimPoint ⟨_,
      ringKrullDim_pointClosureStalk_eq_one_of_dimensionFunction δ hsp hd⟩
  rw [show dimIntermediatePoint δ j x.2 (specializes_iff_mem_closure.mp hxy)
      (heightOnePrimeEquivIntermediatePoint hdim2 q) =
        (⟨(integralComponentAt (x.1 : X)).subschemeι (intermediatePointOfHeightOnePrime
          (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q), hδ⟩ :
          {x : X | δ x = j + 1}) from Subtype.ext rfl,
    sectionOrdTameTerm_of_specializes δ j ξ y x _ hsp,
    chainArrowTerm_of_specializes (j + 1) ξ x _ (specializes_iff_mem_closure.mpr hmem)]
  exact sectionOrdHom_milnorKOneTransport_eq δ (x.1 : X)
    (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy)) q hmem hsp hdimV hw hdim2 hB
    hd (ξ.1 x)

/-! ### The vanishing of the composite -/

/-- **The contribution of a single point vanishes.** For a chain `ξ`, a point `y` with
`δ(y) = j` and a point `x` with `δ(x) = j + 2`, the contributions of the pairs `(x, x')` sum to
zero. This is where Lemma 0EAX enters. -/
theorem finsum_sectionOrdTameTerm_eq_zero (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1 + 1) (1 + 1)) (y : {x : X | δ x = j})
    (x : {x : X | δ x = j + 1 + 1}) :
    (∑ᶠ x' : {x : X | δ x = j + 1}, sectionOrdTameTerm δ j ξ y x x') = 0 := by
  by_cases hxy : (x.1 : X) ⤳ (y.1 : X)
  swap
  · exact finsum_eq_zero_of_forall_eq_zero fun x' ↦ not_not.mp fun hne ↦
      hxy ((specializes_of_sectionOrdTameTerm_ne_zero δ j ξ y x x' hne).elim .trans)
  have hy := specializes_iff_mem_closure.mp hxy
  have hxd : δ x.1 = j + 1 + 1 := x.2
  have hyd : δ y.1 = j := y.2
  let _ : IsLocallyNoetherian (integralComponentAt (x.1 : X)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt (x.1 : X)).subschemeι
  have hdim2 := ringKrullDim_pointClosureStalk_eq_two δ hy (by omega)
  have hsub : Function.support (fun x' : {x : X | δ x = j + 1} ↦
      sectionOrdTameTerm δ j ξ y x x') ⊆ Set.range (dimIntermediatePoint δ j hxd hy) := by
    intro x' hx'
    have hne : sectionOrdTameTerm δ j ξ y x x' ≠ 0 := hx'
    obtain ⟨hxx', hx'y⟩ := specializes_of_sectionOrdTameTerm_ne_zero δ j ξ y x x' hne
    exact exists_dimIntermediatePoint_eq δ j hxd hy hyd x' hxx' hx'y
  rw [finsum_eq_finsum_mem_of_support_subset hsub,
    finsum_mem_range (injective_dimIntermediatePoint δ j hxd hy)]
  exact (finsum_comp_equiv (heightOnePrimeEquivIntermediatePoint hdim2)
    (f := fun z ↦ sectionOrdTameTerm δ j ξ y x (dimIntermediatePoint δ j hxd hy z))).symm.trans
    ((finsum_congr fun q ↦ sectionOrdTameTerm_dimIntermediatePoint δ j ξ y x hxy hdim2 q).trans
      (sum_localMilnorBoundaryOrder_eq_zero hdim2 _))

/-- **Stacks 0EAY: at `i = 1` the composition of the two displayed arrows is zero.** For a
locally Noetherian scheme `X` with a dimension function `δ` and every `j`, the arrow
`⨁_{δ(x) = j + 2} K^M_2(κ(x)) → ⨁_{δ(x) = j + 1} K^M_1(κ(x))` built from the tame symbols of
Section 42.5 of the one-dimensional local rings `𝒪_{closure {x}, x'}`, followed by the arrow
`⨁_{δ(x) = j + 1} K^M_1(κ(x)) → ⨁_{δ(x) = j} K^M_0(κ(x))` built from their orders of vanishing, is
zero. As the remark says, this follows from Lemma 0EAX
(`AlgebraicGeometry.sum_localMilnorBoundaryOrder_eq_zero`). -/
@[stacks 0EAY "the remark's closing sentence for the arrows of a Noetherian (here: locally \
Noetherian) scheme X with a dimension function δ: when i = 1 and j is arbitrary the composition \
⊕_{δ(x) = j + 2} K^M_2(κ(x)) ⟶ ⊕_{δ(x) = j + 1} K^M_1(κ(x)) ⟶ ⊕_{δ(x) = j} K^M_0(κ(x)) of the \
two displayed arrows, built from the tame symbols ∂_A of Section 42.5 of the one-dimensional local \
rings A = 𝒪_{closure {x}, x'}, is zero; the proof runs through Lemma 0EAX at the two-dimensional \
local rings 𝒪_{closure {x}, y}. The remark's statement that it is not clear the composition is \
zero in general is not a claim, and the citation [Kato-Milnor-K] for excellent X is not \
formalized"]
theorem sectionOrdArrow_comp_sectionTameArrow_eq_zero (j : ℤ) :
    (sectionOrdArrow δ j).comp (sectionTameArrow δ (j + 1)) = 0 := by
  refine AddMonoidHom.ext fun ξ ↦ Subtype.ext (funext fun y ↦ ?_)
  refine (milnorKTheoryZeroAddEquiv ↥(X.residueField y.1)).injective ?_
  show milnorKTheoryZeroAddEquiv _ ((sectionOrdArrow δ j (sectionTameArrow δ (j + 1) ξ)).1 y) =
    milnorKTheoryZeroAddEquiv _ 0
  rw [milnorKTheoryZeroAddEquiv_sectionOrdArrow_sectionTameArrow,
    finsum_sectionOrdTameTerm_comm,
    finsum_congr fun x ↦ finsum_sectionOrdTameTerm_eq_zero δ j ξ y x, finsum_zero, map_zero]

end Stacks.Chow

end
