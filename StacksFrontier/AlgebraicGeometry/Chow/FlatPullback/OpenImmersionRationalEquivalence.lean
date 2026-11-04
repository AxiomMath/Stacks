module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.ClosureOfOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion

/-!
# Flat pullback along an open immersion preserves rational equivalence

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project and let `V ⊆ X` be an open subscheme. Restriction of cycles to `V` is flat pullback along
the inclusion `V ⟶ X`, which is flat and locally of finite type of relative dimension zero; this
is Stacks 02UC, recorded as `Stacks.Chow.cycleGroupOpensRestrict_eq_flatPullback`. This file
proves **Stacks 02S1 for that inclusion**: flat pullback along it carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero. Consequently restriction descends to
a map `A_k(X) ⟶ A_k(V)` of Chow groups carrying no hypothesis.

The argument restricts a presentation of a rational equivalence. Let `(W_j)_j` be a locally finite
family of integral closed subschemes of `X` of delta-dimension `k + 1`, let `g_j` be a nonzero
rational function on `W_j`, and suppose the given cycle has coefficients `∑_j (i_j)_* div(g_j)`.
The restricted family is the family of scheme-theoretic inverse images `W_j ×_X V`, and three
things happen.

* The inverse image may be empty, and it is integral as soon as the generic point of `W_j` lies in
  `V`: it is then the integral closed subscheme of `V` attached to that generic point read as a
  point of `V`, by `Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion`. The remaining
  members are dropped. They contribute nothing at a point of `V`, because an open neighbourhood of
  a point of the closure of `x` contains `x`, so a `W_j` whose generic point misses the open set
  `V` misses `V` altogether, while the pushforward of `div(g_j)` is supported on `W_j`. The
  surviving family is therefore indexed by the subtype of those indices whose generic point lies
  in `V`.
* Delta-dimension is unchanged, because `W_j ×_X V ⟶ W_j` is an open immersion of integral schemes
  over the base, and such a morphism preserves delta-dimension by
  `Stacks.Chow.schemeDeltaDimension_eq_of_isOpenImmersion`.
* The rational function restricts, and its principal divisor restricts with it. The order of
  vanishing of `g_j` at a point of `W_j ×_X V` is its order of vanishing at that point of `W_j`
  (`Stacks.Chow.principalCycle_rationalFunctionsRingEquivOfOpenImmersion_apply`), and pushforward
  along the closed immersion of a closed subscheme merely transports a coefficient from a point to
  its image; so the restricted term has at a point of `V` the coefficient that the original term
  has at the image of that point.

Local finiteness of the restricted family is local finiteness of the original one read on
preimages, the support of `W_j ×_X V` being the preimage of the support of `W_j`.

## Main definitions

* `Stacks.Chow.comapOpenImmersionMap` — the comparison morphism `W ×_X U ⟶ W` from the inverse
  image of a closed subscheme `W ⊆ X` along an open immersion `U ⟶ X`, itself an open immersion.
* `Stacks.Chow.comapRationalFunctionUnit` — the restriction to `W ×_X U` of a nonzero rational
  function on `W`.
* `Stacks.Chow.chowGroupOpensRestrictOfIsOpenImmersion` — restriction of Chow classes to an open
  subscheme, `A_k(X) ⟶ A_k(V)`, with no hypothesis.

## Main results

* `Stacks.Chow.principalDivisorPushforward_comap_opensι` — the coefficient at a point of `V` of
  the pushed-forward principal divisor of a restricted rational function is the coefficient of the
  pushed-forward principal divisor of the original function at the image of that point.
* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_opensι` — **Stacks 02S1 along the
  inclusion of an open subscheme**.

## References

* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The part of a closed subscheme lying over an open subscheme -/

section Comap

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (W : X.IdealSheafData)

/-- The comparison morphism `W ×_X U ⟶ W` from the scheme-theoretic inverse image along
`j : U ⟶ X` of a closed subscheme `W ⊆ X` to that closed subscheme. -/
def comapOpenImmersionMap : (W.comap j).subscheme ⟶ W.subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ j (W.le_map_comap j)

/-- The comparison morphism from the inverse image of a closed subscheme along an open immersion
is an open immersion: it is the base change of `j` along the closed immersion of `W`. -/
instance comapOpenImmersionMap_isOpenImmersion :
    IsOpenImmersion (comapOpenImmersionMap j W) := by
  rw [comapOpenImmersionMap, ← Scheme.IdealSheafData.comapIso_hom_snd]
  have : IsOpenImmersion (pullback.snd j W.subschemeι) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback j W.subschemeι) inferInstance
  exact IsOpenImmersion.comp _ _

omit [IsOpenImmersion j] in
/-- The comparison square commutes: the closed immersion of the inverse image of `W`, followed by
`j`, is the comparison morphism followed by the closed immersion of `W`. -/
theorem comapOpenImmersionMap_comp_subschemeι :
    comapOpenImmersionMap j W ≫ W.subschemeι = (W.comap j).subschemeι ≫ j :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ j _

/-- The comparison morphism of an integral closed subscheme with integral inverse image is
dominant: it is an open immersion with nonempty source into an irreducible scheme, so its image is
a nonempty open subset, hence dense. -/
theorem isDominant_comapOpenImmersionMap (hW : IsIntegral W.subscheme)
    (hW' : IsIntegral (W.comap j).subscheme) : IsDominant (comapOpenImmersionMap j W) := by
  have := hW
  have := hW'
  rw [isDominant_iff]
  exact (IsOpenImmersion.isOpen_range (comapOpenImmersionMap j W)).dense (Set.range_nonempty _)

/-- The restriction to the inverse image `W ×_X U` of a nonzero rational function on an integral
closed subscheme `W ⊆ X`, along an open immersion `j : U ⟶ X` for which that inverse image is
again integral. It is the restriction of rational functions of Stacks 01RU along the comparison
morphism, which is a dominant open immersion of integral schemes. -/
def comapRationalFunctionUnit (hW : IsIntegral W.subscheme)
    (hW' : IsIntegral (W.comap j).subscheme) (g : (rationalFunctions W.subscheme)ˣ) :
    (rationalFunctions (W.comap j).subscheme)ˣ :=
  letI := hW
  letI := hW'
  letI : IsDominant (comapOpenImmersionMap j W) := isDominant_comapOpenImmersionMap j W hW hW'
  rationalFunctionsUnitsMulEquivOfOpenImmersion (comapOpenImmersionMap j W) g

end Comap

/-! ### Restricting a pushed-forward principal divisor to an open subscheme -/

/-- The support of the inverse image of a closed subscheme is the preimage of its support. -/
private theorem coe_support_comap_opensι {X : Scheme.{u}} (V : X.Opens) (W : X.IdealSheafData) :
    (((W.comap V.ι).support : Set (V : Scheme.{u}))) = V.ι.base ⁻¹' (W.support : Set X) := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]

/-- **The pushforward of a principal divisor restricts to an open subscheme.** The coefficient at
a point `y` of an open subscheme `V ⊆ X` of the pushforward from `W ×_X V` of the principal
divisor of the restriction of a nonzero rational function `g` on an integral closed subscheme
`W ⊆ X` is the coefficient at the image of `y` of the pushforward from `W` of `div(g)`.

Pushforward along the closed immersion of a closed subscheme transports a coefficient from a point
to its image and vanishes off the image, so both sides are read off at the unique point above `y`
when there is one — and the two conditions agree, the support of `W ×_X V` being the preimage of
the support of `W`. At such a point the two orders of vanishing agree, which is
`Stacks.Chow.principalCycle_rationalFunctionsRingEquivOfOpenImmersion_apply` for the comparison
morphism. -/
theorem principalDivisorPushforward_comap_opensι (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (V : X.Opens) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) (hW' : IsIntegral (W.comap V.ι).subscheme)
    (g : (rationalFunctions W.subscheme)ˣ) (y : (V : Scheme.{u})) :
    principalDivisorPushforward C (V.ι ≫ f) (W.comap V.ι) hW'
        (comapRationalFunctionUnit V.ι W hW hW' g) y =
      principalDivisorPushforward C f W hW g (V.ι.base y) := by
  have := hW
  have := hW'
  have : IsDominant (comapOpenImmersionMap V.ι W) :=
    isDominant_comapOpenImmersionMap V.ι W hW hW'
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ f)
  have : IsLocallyNoetherian (W.comap V.ι).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((W.comap V.ι).subschemeι ≫ (V.ι ≫ f))
  rw [principalDivisorPushforward_eq, principalDivisorPushforward_eq]
  by_cases hy : y ∈ Set.range (W.comap V.ι).subschemeι.base
  · obtain ⟨w, rfl⟩ := hy
    have hsq : V.ι.base ((W.comap V.ι).subschemeι.base w) =
        W.subschemeι.base ((comapOpenImmersionMap V.ι W).base w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        comapOpenImmersionMap_comp_subschemeι]
    rw [closedSubschemeCyclePushforward_apply, hsq, closedSubschemeCyclePushforward_apply]
    exact principalCycle_rationalFunctionsRingEquivOfOpenImmersion_apply
      (comapOpenImmersionMap V.ι W) (g : rationalFunctions W.subscheme) w
  · have hy' : V.ι.base y ∉ Set.range W.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι] at hy ⊢
      rwa [coe_support_comap_opensι] at hy
    rw [closedSubschemeCyclePushforward_apply_of_notMem_range _ _ _ _ hy,
      closedSubschemeCyclePushforward_apply_of_notMem_range _ _ _ _ hy']

/-! ### Stacks 02S1 along the inclusion of an open subscheme -/

/-- **Stacks 02S1 along the inclusion of an open subscheme.** Flat pullback of `k`-cycles along
the inclusion of an open subscheme `V ⊆ X` carries cycles rationally equivalent to zero to cycles
rationally equivalent to zero.

A presentation `∑_j (i_j)_* div(g_j)` of a rational equivalence on `X`, by a locally finite family
of integral closed subschemes `W_j` of delta-dimension `k + 1`, restricts to the presentation by
the inverse images `W_j ×_X V` of those members whose generic point lies in `V`, carrying the
restrictions of the `g_j`. The members whose generic point misses `V` are supported off `V` and
contribute nothing there; the surviving inverse images are integral by
`Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion`, keep their delta-dimension by
`Stacks.Chow.schemeDeltaDimension_eq_of_isOpenImmersion`, form a locally finite family because
their supports are preimages, and their terms have the right coefficients by
`Stacks.Chow.principalDivisorPushforward_comap_opensι`. -/
@[stacks 02S1 "flat pullback along an open immersion preserves rational equivalence"]
theorem flatPullbackFactorsThroughRationalEquivalence_of_opensι (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (V : X.Opens) (k : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalence C (V.ι ≫ f) f V.ι rfl 0
      (relativeDimension_opensι V) k := by
  intro α hα
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  -- A member whose generic point misses `V` is supported off `V`.
  have hvanish : ∀ j : J, genericPointOf (W j) (hW j) ∉ V → ∀ y : (V : Scheme.{u}),
      principalDivisorPushforward C f (W j) (hW j) (g j) (V.ι.base y) = 0 := by
    intro j hj y
    by_contra hne
    refine hj ?_
    have hmem := support_principalDivisorPushforward_subset C f (W j) (hW j) (g j) hne
    rw [support_eq_closure_genericPointOf (W j) (hW j)] at hmem
    obtain ⟨x, hxV, hx⟩ := mem_closure_iff.mp hmem (V : Set X) V.2 y.2
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hxV
  -- The surviving inverse images are integral closed subschemes of `V`.
  have hW' : ∀ jj : {j : J // genericPointOf (W j) (hW j) ∈ V},
      IsIntegral ((W jj.1).comap V.ι).subscheme := by
    intro jj
    have hmem : genericPointOf (W jj.1) (hW jj.1) ∈ Set.range V.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact jj.2
    obtain ⟨z, hz⟩ := hmem
    have hcomap : (W jj.1).comap V.ι = integralComponentAt z := by
      rw [← comap_integralComponentAt_of_isOpenImmersion V.ι z, hz,
        integralComponentAt_genericPointOf (W jj.1) (hW jj.1)]
    rw [hcomap]
    exact isIntegral_integralComponentAt z
  refine ⟨{j : J // genericPointOf (W j) (hW j) ∈ V}, fun jj ↦ (W jj.1).comap V.ι, hW', ?_, ?_,
    fun jj ↦ comapRationalFunctionUnit V.ι (W jj.1) (hW jj.1) (hW' jj) (g jj.1), ?_⟩
  · intro jj
    have := hW jj.1
    have := hW' jj
    have hsq : comapOpenImmersionMap V.ι (W jj.1) ≫ ((W jj.1).subschemeι ≫ f) =
        ((W jj.1).comap V.ι).subschemeι ≫ (V.ι ≫ f) := by
      rw [← Category.assoc, comapOpenImmersionMap_comp_subschemeι, Category.assoc]
    rw [← schemeDeltaDimension_eq_of_isOpenImmersion C (comapOpenImmersionMap V.ι (W jj.1))
      ((W jj.1).subschemeι ≫ f) (((W jj.1).comap V.ι).subschemeι ≫ (V.ι ≫ f)) hsq, hDim jj.1]
    norm_num
  · simp_rw [coe_support_comap_opensι]
    exact (hLocal.preimage_continuous V.ι.continuous).comp_injective Subtype.val_injective
  · intro y
    have hval : (flatPullback C (V.ι ≫ f) f V.ι rfl 0 (relativeDimension_opensι V) k α).1 y =
        α.1 (V.ι.base y) := by
      rw [flatPullback_opensι C f V (relativeDimension_opensι V) k α]
      rfl
    rw [hval, hg (V.ι.base y)]
    simp only [principalDivisorFamilyCoefficient]
    have hterm : ∀ jj : {j : J // genericPointOf (W j) (hW j) ∈ V},
        principalDivisorPushforward C (V.ι ≫ f) ((W jj.1).comap V.ι) (hW' jj)
            (comapRationalFunctionUnit V.ι (W jj.1) (hW jj.1) (hW' jj) (g jj.1)) y =
          principalDivisorPushforward C f (W jj.1) (hW jj.1) (g jj.1) (V.ι.base y) :=
      fun jj ↦ principalDivisorPushforward_comap_opensι C f V (W jj.1) (hW jj.1) (hW' jj)
        (g jj.1) y
    rw [finsum_congr hterm]
    set F : J → ℤ := fun j ↦ principalDivisorPushforward C f (W j) (hW j) (g j) (V.ι.base y)
    have hinter : {j : J | genericPointOf (W j) (hW j) ∈ V} ∩ Function.support F =
        Set.univ ∩ Function.support F := by
      refine (Set.inter_eq_right.mpr ?_).trans (Set.univ_inter _).symm
      intro j hj
      by_contra hno
      exact hj (hvanish j hno y)
    refine Eq.symm (Eq.trans (finsum_set_coe_eq_finsum_mem (f := F)
      {j : J | genericPointOf (W j) (hW j) ∈ V}) ?_)
    exact (finsum_mem_inter_support_eq F _ Set.univ hinter).trans (finsum_mem_univ F)

/-! ### Restriction of Chow classes to an open subscheme -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (V : X.Opens) (k : ℤ)

/-- **Restriction of Chow classes to an open subscheme**, `A_k(X) ⟶ A_k(V)`.

This is `Stacks.Chow.chowGroupOpensRestrict` with its hypothesis discharged by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_opensι`. -/
def chowGroupOpensRestrictOfIsOpenImmersion : chowGroup C f k →+ chowGroup C (V.ι ≫ f) k :=
  chowGroupOpensRestrict C f V k
    (flatPullbackFactorsThroughRationalEquivalence_of_opensι C f V k)

/-- On the class of a cycle, restriction of Chow classes to an open subscheme is the class of the
restricted cycle. -/
@[simp]
theorem chowGroupOpensRestrictOfIsOpenImmersion_mk (c : CycleGroup C f k) :
    chowGroupOpensRestrictOfIsOpenImmersion C f V k
        (QuotientAddGroup.mk' (rationalEquivalences C f k) c) =
      QuotientAddGroup.mk' (rationalEquivalences C (V.ι ≫ f) k)
        (cycleGroupOpensRestrict C f V k c) :=
  rfl

end Stacks.Chow

end
