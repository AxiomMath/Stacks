module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.DegreeTwo
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChowGroupOne
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainLocalization
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksCore.Tactic.StacksAttribute

/-!
# The arrows of Stacks 0EAY in degree one form a complex

Stacks 0EAY displays, for a Noetherian scheme `X` with a dimension function `δ`, the arrows

`⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_i(κ(x)) ⟶ ⨁_{δ(x) = j - 1} K^M_{i-1}(κ(x))`

built from the tame symbols `∂_A` of the one-dimensional local rings `A = 𝒪_{closure {x}, x'}`,
extended from discrete valuation rings by normalization and norm
(`Stacks.Chow.milnorChainBoundary`), and says: "When `i = 1` and `j` arbitrary, this [the
vanishing of the composition] follows from Lemma 0EAX." This file proves that sentence for the
arrows `Stacks.Chow.milnorChainBoundary`, for `X` locally of finite type over the base of chapter
42 with `δ` the induced dimension function, whenever the local rings `𝒪_{closure {x}, x'}` of
dimension one have finite normalization — the case of a Nagata `X`, in particular of an excellent
`X`, which is the setting in which the remark constructs `∂_A` (for a Noetherian local domain of
dimension one with infinite normalization the remark's construction "using normalization and norm
maps" is not available as such).

The proof identifies the two arrows at `i = 1` with the arrows of Stacks 0GU9 built from the tame
symbol of Stacks 02Q1 and the order of vanishing:

* in degree two, `∂_A = d_A` (`Stacks.Chow.oneDimTameSymbol_one_eq_milnorKTwoTameSymbol`), so the
  first arrow is `Stacks.Chow.pointwiseMilnorBoundary`
  (`Stacks.Chow.milnorChainBoundary_one_apply_eq`);
* in degree one, `∂_A = ord_A` (`Stacks.Chow.oneDimTameSymbol_zero_eq_ordInt`), so the second arrow
  is the divisor differential `Stacks.Chow.pointwiseDivisorDifferential`
  (`Stacks.Chow.milnorChainBoundary_zero_eq`);

and then the vanishing of the composite of those, which runs through Lemma 0EAX
(`Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary`), transfers.

## Main results

* `Stacks.Chow.milnorChainBoundary_comp_milnorChainBoundary_eq_zero` — the composite of the two
  displayed arrows at `i = 1` is zero.
* `Stacks.Chow.milnorChainBoundary_comp_milnorChainBoundary_eq_zero_of_isNagataRing` — the same
  when the local rings of the closures of points are Nagata.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.Chow

/-! ### Two facts on one-dimensional local domains -/

/-- The order of vanishing does not depend on the realization of the fraction field. -/
theorem ordInt_algEquiv (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K K' : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra R K'] [IsFractionRing R K'] (σ : K ≃ₐ[R] K') (x : K) (hx : x ≠ 0)
    (hx' : σ x ≠ 0) : ordInt R (σ x) hx' = ordInt R x hx := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) x
  have ha0 : a ≠ 0 := fun h ↦ hx (by rw [← hab, h, map_zero, zero_div])
  have key : ∀ {L : Type u} [Field L] [Algebra R L] [IsFractionRing R L] (y : L) (hy : y ≠ 0),
      y * algebraMap R L b = algebraMap R L a → ordInt R y hy =
        ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) -
          (Module.length R (R ⧸ Ideal.span {b})).toNat := by
    intro L _ _ _ y hy e
    have hbL := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := L) hb
    have h := ordInt_mul R y (algebraMap R L b) hy hbL
    rw [ordInt_val_congr R e _ (e ▸ mul_ne_zero hy hbL), ordInt_algebraMap R a ha0,
      ordInt_algebraMap R b (nonZeroDivisors.ne_zero hb)] at h
    linarith
  have e1 : x * algebraMap R K b = algebraMap R K a := by
    rw [← hab, div_mul_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)]
  refine (key (L := K') (σ x) hx' ?_).trans (key x hx e1).symm
  rw [← σ.commutes, ← map_mul, e1, σ.commutes]

/-- A finite normalization in one fraction field is a finite normalization in every fraction
field. -/
theorem module_finite_integralClosure_of_fractionRing (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [h : Module.Finite R ↥(integralClosure R (FractionRing R))] :
    Module.Finite R ↥(integralClosure R K) := by
  let σ := FractionRing.algEquiv R K
  rw [← integralClosure_map_algEquiv σ]
  exact Module.Finite.equiv
    ((integralClosure R (FractionRing R)).equivMapOfInjective σ.toAlgHom
      σ.injective).toLinearEquiv

/-! ### The local components at a point of an integral scheme -/

section Stalk

variable {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] {K : Type u} [Field K]
  (e : ↥W.functionField ≃+* K)

/-- **In degree two the general tame symbol at a one-dimensional point is the tame symbol of
Stacks 02Q1**, when the local ring there has finite normalization. -/
theorem stalkTameSymbol_one_eq_stalkMilnorBoundary (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1)
    [Module.Finite ↥(W.presheaf.stalk z)
      ↥(integralClosure ↥(W.presheaf.stalk z) (FractionRing ↥(W.presheaf.stalk z)))] :
    stalkTameSymbol e milnorKNormFamily_preservesGrading z hdim 1 =
      stalkMilnorBoundary e z hdim := by
  let := stalkAlgebraOfFunctionFieldEquiv e z
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  have := module_finite_integralClosure_of_fractionRing ↥(W.presheaf.stalk z) K
  exact oneDimTameSymbol_one_eq_milnorKTwoTameSymbol hdim

/-- **In degree one the general tame symbol at a one-dimensional point is the order of vanishing**
of Stacks 02MD there, when the local ring has finite normalization. -/
theorem milnorKTheoryZeroAddEquiv_stalkTameSymbol_zero (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1)
    [Module.Finite ↥(W.presheaf.stalk z)
      ↥(integralClosure ↥(W.presheaf.stalk z) (FractionRing ↥(W.presheaf.stalk z)))]
    (f : Kˣ) :
    milnorKTheoryZeroAddEquiv (W.residueField z)
        (stalkTameSymbol e milnorKNormFamily_preservesGrading z hdim 0
          ((milnorKTheoryOneAddEquiv K).symm (Additive.ofMul f))) =
      W.ord (e.symm (f : K)) z := by
  let := stalkAlgebraOfFunctionFieldEquiv e z
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  have := module_finite_integralClosure_of_fractionRing ↥(W.presheaf.stalk z) K
  have : Ring.KrullDimLE 1 ↥(W.presheaf.stalk z) :=
    Ring.krullDimLE_iff.2 (by rw [hdim]; exact_mod_cast le_rfl)
  refine (oneDimTameSymbol_zero_eq_ordInt (↥(W.presheaf.stalk z)) K hdim f).trans ?_
  have hne : e.symm (f : K) ≠ 0 := (map_ne_zero e.symm).2 f.ne_zero
  rw [ord_eq_ordInt z (coheight_eq_one_of_oneDimPoint ⟨z, hdim⟩) _ hne]
  have hσ := e.apply_symm_apply (f : K)
  rw [← ordInt_algEquiv (↥(W.presheaf.stalk z)) { e with commutes' := fun _ ↦ rfl } _ hne
    (hσ.trans_ne f.ne_zero)]
  exact ordInt_val_congr _ hσ.symm _ _

end Stalk


/-! ### The arrows at `i = 1` -/

section Scheme

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- The relative dimension, the dimension function of Stacks 02JW on `X`, is strictly decreasing
along proper specializations. -/
theorem relativeDimension_lt_of_specializes ⦃x y : X⦄ (h : x ⤳ y) (hne : x ≠ y) :
    relativeDimension C.dimensionFunction p y < relativeDimension C.dimensionFunction p x := by
  have := (deltaDimensionFunction C p).strictAnti_specializes h hne
  rwa [← deltaDimensionFunction_apply C p x, ← deltaDimensionFunction_apply C p y]

/-- **The local rings of dimension one of the closures of the points of `X` have finite
normalization.** Every Noetherian local domain of dimension one whose normalization is finite
carries the tame symbol of Stacks 0EAY by normalization and norm in the sense of the remark;
this holds whenever `X` is Nagata
(`Stacks.Chow.hasFiniteNormalizationPointClosureStalks_of_isNagataRing`), in particular when `X`
is excellent. -/
def HasFiniteNormalizationPointClosureStalks (X : Scheme.{u}) : Prop :=
  ∀ (x : X) (z : (integralComponentAt x).subscheme),
    ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk z) = 1 →
    Module.Finite ((integralComponentAt x).subscheme.presheaf.stalk z)
      (integralClosure ((integralComponentAt x).subscheme.presheaf.stalk z)
        (FractionRing ((integralComponentAt x).subscheme.presheaf.stalk z)))

/-- Nagata local rings have finite normalization. -/
theorem hasFiniteNormalizationPointClosureStalks_of_isNagataRing
    (hN : ∀ (x : X) (z : (integralComponentAt x).subscheme),
      IsNagataRing ((integralComponentAt x).subscheme.presheaf.stalk z)) :
    HasFiniteNormalizationPointClosureStalks X := fun x z hdim ↦
  have := hN x z
  let := dimensionLEOne_of_ringKrullDim_eq_one _ hdim
  Stacks.Normalization.module_finite_integralClosure_of_isNagataRing _ _ (hN x z)

variable {C p}

/-- **The first arrow at `i = 1`**: the component `∂_{𝒪_{closure {x}, x'}}` of
`Stacks.Chow.milnorChainBoundary` in degree two is the tame symbol of Stacks 02Q1 descended to
Milnor K-theory. -/
theorem pointClosureTameSymbol_one_eq_pointClosureMilnorBoundary
    (hfin : HasFiniteNormalizationPointClosureStalks X) (x : X) {x' : X}
    (h : x' ∈ closure ({x} : Set X))
    (hdim : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h)) = 1) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian p
    pointClosureTameSymbol milnorKNormFamily_preservesGrading x h hdim 1 =
      pointClosureMilnorBoundary C p x h hdim := by
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := hfin x (pointClosurePoint x h) hdim
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ p)
  refine AddMonoidHom.ext fun α ↦ ?_
  simp only [pointClosureTameSymbol, pointClosureMilnorBoundary, AddMonoidHom.comp_apply]
  rw [RingEquiv.toRingHom_eq_coe, milnorKTransport_eq_milnorKOneTransport,
    stalkTameSymbol_one_eq_stalkMilnorBoundary]

/-- **The second arrow at `i = 1`**: the component `∂_{𝒪_{closure {x'}, y}}` of
`Stacks.Chow.milnorChainBoundary` in degree one is the coefficient at `y` of the principal divisor
on `closure {x'}`, the order of vanishing. -/
theorem milnorKTheoryZeroAddEquiv_pointClosureTameSymbol_zero
    (hfin : HasFiniteNormalizationPointClosureStalks X) (x' : X) {y : X}
    (h : y ∈ closure ({x'} : Set X))
    (hdim : ringKrullDim ((integralComponentAt x').subscheme.presheaf.stalk
      (pointClosurePoint x' h)) = 1) (α : MilnorKTheory (X.residueField x') 1) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian p
    milnorKTheoryZeroAddEquiv (X.residueField y)
        (pointClosureTameSymbol milnorKNormFamily_preservesGrading x' h hdim 0 α) =
      pointClosureOrd C p x' α y := by
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := hfin x' (pointClosurePoint x' h) hdim
  let : IsLocallyNoetherian (integralComponentAt x').subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x').subschemeι ≫ p)
  simp only [pointClosureTameSymbol, AddMonoidHom.comp_apply]
  rw [milnorKTheoryZeroAddEquiv_milnorKTransport]
  obtain ⟨f, rfl⟩ : ∃ f, α = (milnorKTheoryOneAddEquiv _).symm (Additive.ofMul f) :=
    ⟨Additive.toMul (milnorKTheoryOneAddEquiv _ α), by simp⟩
  rw [milnorKTheoryZeroAddEquiv_stalkTameSymbol_zero, pointClosureOrd_eq_ord C p x' _ h]
  simp

variable (C p)

/-- **The second arrow of Stacks 0EAY at `i = 1` is the divisor differential**, when the local
rings of dimension one of the closures of points have finite normalization. -/
theorem milnorChainBoundary_zero_eq (hfin : HasFiniteNormalizationPointClosureStalks X) (j : ℤ)
    (a : DimMilnorChainGroup X (relativeDimension C.dimensionFunction p) (j + 1) 1) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian p
    milnorChainBoundary (relativeDimension C.dimensionFunction p)
        (relativeDimension_lt_of_specializes C p) 0 j a =
      pointwiseDivisorDifferential C p j a := by
  have := LocallyOfFiniteType.isLocallyNoetherian p
  refine Subtype.ext (funext fun (y : pointsOfDimension C p j) ↦ ?_)
  apply (milnorKTheoryZeroAddEquiv (X.residueField y.1)).injective
  refine Eq.trans ?_ (pointwiseDivisorDifferential_apply_eq_finsum C p j a y).symm
  refine ((milnorKTheoryZeroAddEquiv (X.residueField y.1)).toAddMonoidHom.map_finsum
    (finite_support_dimMilnorChainBoundaryTerm _ 0 j a y)).trans ?_
  refine finsum_congr fun (x' : pointsOfDimension C p (j + 1)) ↦ ?_
  by_cases hs : (x'.1 : X) ⤳ (y.1 : X)
  · exact (congrArg (milnorKTheoryZeroAddEquiv (X.residueField y.1))
      (dimMilnorChainBoundaryTerm_of_specializes _ _ _ _ _ _ hs)).trans
      (milnorKTheoryZeroAddEquiv_pointClosureTameSymbol_zero hfin _ _ _ _)
  · exact (congrArg (milnorKTheoryZeroAddEquiv (X.residueField y.1))
      (dimMilnorChainBoundaryTerm_of_not_specializes _ _ _ _ _ _ hs)).trans
      ((map_zero _).trans (pointClosureOrd_eq_zero_of_notMem_closure C p _ _
        (fun hm ↦ hs (specializes_iff_mem_closure.mpr hm))).symm)

/-- The points of relative dimension `j + 1 + 1` are the points of relative dimension `j + 2`. -/
def pointsOfDimensionAddOneAddOneEquiv (j : ℤ) :
    {x : X | relativeDimension C.dimensionFunction p x = j + 1 + 1} ≃
      pointsOfDimension C p (j + 2) :=
  Equiv.subtypeEquivRight fun x ↦ by
    simp only [Set.mem_ofPred_eq, mem_pointsOfDimension]
    constructor <;> intro h <;> omega

/-- A degree-two chain at the points of relative dimension `j + 1 + 1`, read at the points of
relative dimension `j + 2`. -/
def twoChainToPointwise (j : ℤ)
    (ξ : DimMilnorChainGroup X (relativeDimension C.dimensionFunction p) (j + 1 + 1) 2) :
    PointwiseKTwoGroup C p j :=
  ⟨fun x ↦ ξ.1 ((pointsOfDimensionAddOneAddOneEquiv C p j).symm x), fun U hU ↦
    ((ξ.2 U hU).image (pointsOfDimensionAddOneAddOneEquiv C p j)).subset fun x hx ↦
      ⟨(pointsOfDimensionAddOneAddOneEquiv C p j).symm x, hx, Equiv.apply_symm_apply _ _⟩⟩

/-- **The first arrow of Stacks 0EAY at `i = 1` is the tame-symbol differential of Stacks 0GU9**,
when the local rings of dimension one of the closures of points have finite normalization. -/
theorem milnorChainBoundary_one_apply_eq (hfin : HasFiniteNormalizationPointClosureStalks X)
    (j : ℤ) (ξ : DimMilnorChainGroup X (relativeDimension C.dimensionFunction p) (j + 1 + 1) 2) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian p
    milnorChainBoundary (relativeDimension C.dimensionFunction p)
        (relativeDimension_lt_of_specializes C p) 1 (j + 1) ξ =
      pointwiseMilnorBoundary C p j (twoChainToPointwise C p j ξ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian p
  refine Subtype.ext (funext fun (x' : pointsOfDimension C p (j + 1)) ↦ ?_)
  refine Eq.trans ?_ (pointwiseMilnorBoundary_apply C p j _ x').symm
  refine (finsum_comp_equiv (pointsOfDimensionAddOneAddOneEquiv C p j).symm).symm.trans ?_
  refine finsum_congr fun x ↦ ?_
  by_cases hs : (x.1 : X) ⤳ (x'.1 : X)
  · refine (dimMilnorChainBoundaryTerm_of_specializes _ _ _ _ _ _ hs).trans (Eq.trans ?_
      (pointwiseMilnorBoundaryTerm_of_specializes C p j _ x x' hs
        (ringKrullDim_eq_one_of_mem _ (relativeDimension_lt_of_specializes C p) (j + 1)
          (x := (pointsOfDimensionAddOneAddOneEquiv C p j).symm x) hs)).symm)
    exact DFunLike.congr_fun
      (pointClosureTameSymbol_one_eq_pointClosureMilnorBoundary (C := C) (p := p) hfin x.1
        (specializes_iff_mem_closure.mp hs) _) _
  · exact (dimMilnorChainBoundaryTerm_of_not_specializes _ _ _ _ _ _ hs).trans
      (pointwiseMilnorBoundaryTerm_of_not_specializes C p j _ x x' hs).symm

/-- **Stacks 0EAY, the case `i = 1`: the composition of the two displayed arrows is zero.** Let
`X` be locally of finite type over the base `(S, δ)` of chapter 42, with the induced dimension
function `δ_X` (the relative dimension, Stacks 02JW), and suppose the local rings of dimension
one of the closures of the points of `X` have finite normalization (as for `X` Nagata, in
particular excellent, which is the setting in which the remark constructs the tame symbols by
normalization and norm). Then for every `j` the composite

`⨁_{δ(x) = j + 2} K^M_2(κ(x)) ⟶ ⨁_{δ(x) = j + 1} K^M_1(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_0(κ(x))`

of the arrows `Stacks.Chow.milnorChainBoundary` is zero. As the remark says, this follows from
Lemma 0EAX: the two arrows are the tame-symbol and divisor differentials of Stacks 0GU9
(`Stacks.Chow.milnorChainBoundary_one_apply_eq`, `Stacks.Chow.milnorChainBoundary_zero_eq`),
whose composite vanishes by the key lemma 0EAX
(`Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary`). -/
@[stacks 0EAY "the remark's closing sentence for the displayed arrows built from the tame \
symbols ∂_A by normalization and norm: when i = 1 and j is arbitrary the composition \
⊕_{δ(x) = j + 2} K^M_2(κ(x)) ⟶ ⊕_{δ(x) = j + 1} K^M_1(κ(x)) ⟶ ⊕_{δ(x) = j} K^M_0(κ(x)) of the two \
arrows Stacks.Chow.milnorChainBoundary is zero, and it follows from Lemma 0EAX. Stated for X \
locally of finite type over the base of chapter 42 with the induced dimension function, and for X \
whose local rings of dimension one at the closures of points have finite normalization -- the \
case of a Nagata, in particular an excellent, X, which is the setting in which the remark \
constructs ∂_A by normalization and norm maps. There ∂_A is the tame symbol d_A of Section 42.5 in \
degree two and ord_A in degree one, so the arrows are the differentials of Stacks 0GU9, whose \
composite vanishes by Lemma 0EAX"]
theorem milnorChainBoundary_comp_milnorChainBoundary_eq_zero
    (hfin : HasFiniteNormalizationPointClosureStalks X) (j : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian p
    (milnorChainBoundary (relativeDimension C.dimensionFunction p)
        (relativeDimension_lt_of_specializes C p) 0 j).comp
      (milnorChainBoundary (relativeDimension C.dimensionFunction p)
        (relativeDimension_lt_of_specializes C p) 1 (j + 1)) = 0 := by
  have := LocallyOfFiniteType.isLocallyNoetherian p
  refine AddMonoidHom.ext fun ξ ↦ ?_
  rw [AddMonoidHom.comp_apply, milnorChainBoundary_one_apply_eq C p hfin j ξ,
    AddMonoidHom.zero_apply]
  exact (milnorChainBoundary_zero_eq C p hfin j _).trans
    (pointwiseDivisorDifferential_pointwiseMilnorBoundary C p j _)

/-- The local rings of the closures of the points of a scheme whose local rings are Nagata are
Nagata: the closed immersion of `closure {x}` is surjective on local rings. -/
theorem isNagataRing_pointClosureStalk (hN : ∀ x : X, IsNagataRing (X.presheaf.stalk x)) (x : X)
    (z : (integralComponentAt x).subscheme) :
    IsNagataRing ((integralComponentAt x).subscheme.presheaf.stalk z) :=
  MonogenicN1.isNagataRing_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective
      ((integralComponentAt x).subschemeι.stalkMap_surjective z))
    (MonogenicN1.isNagataRing_quotient (hN _) _)

/-- **Stacks 0EAY, the case `i = 1`, for `X` with Nagata local rings**, in particular for an
excellent `X`: the composition of the two displayed arrows is zero. -/
theorem milnorChainBoundary_comp_milnorChainBoundary_eq_zero_of_isNagataRing
    (hN : ∀ x : X, IsNagataRing (X.presheaf.stalk x)) (j : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian p
    (milnorChainBoundary (relativeDimension C.dimensionFunction p)
        (relativeDimension_lt_of_specializes C p) 0 j).comp
      (milnorChainBoundary (relativeDimension C.dimensionFunction p)
        (relativeDimension_lt_of_specializes C p) 1 (j + 1)) = 0 :=
  milnorChainBoundary_comp_milnorChainBoundary_eq_zero C p
    (hasFiniteNormalizationPointClosureStalks_of_isNagataRing
      (isNagataRing_pointClosureStalk hN)) j

end Scheme

end Stacks.Chow

end
