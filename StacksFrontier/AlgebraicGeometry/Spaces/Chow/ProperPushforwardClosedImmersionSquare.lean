module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFamilySums
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCyclesInDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SinglePointGlobalFunctions

/-!
# The square form of Stacks 0EP2

In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be proper over the base, let
`W ⊆ X` and `W' ⊆ Y` be integral closed subspaces with inclusions `i` and `i'`, and let
`p' : W ⟶ W'` be a morphism over `p`. This module proves

`p_* i_* c = i'_* p'_* c`

for every `k`-cycle `c` on `W`. Taking `W'` to be the integral closed image of `i ≫ p` and `p'`
the morphism of Stacks 0EEG, this is the identity `p_* i_* div(f) = i'_* p'_* div(f)` on which
the source's reductions of proper pushforward to the integral dominant case rest.

Stacks 0EP2 itself — functoriality `g_* ∘ f_* = (g ∘ f)_*` on `Z_k` — is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCyclesInDimension` as
`AlgebraicGeometry.Space.properPushforwardInDimension_comp`, and it does not by itself reach the
square: three pushforwards of `k`-cycles coexist in this chapter and were nowhere compared.
This module supplies the two missing comparisons.

* The two constructions of the pushforward of Stacks 0EP1 along a morphism agree on `k`-cycles:
  `AlgebraicGeometry.Space.properPushforwardInDimension`, whose weight tests
  `dim_δ(Z') = k`, and `AlgebraicGeometry.Space.properCyclePushforward`, whose degree tests
  `dim_δ(Z') = dim_δ(Z)`. Both degrees are `AlgebraicGeometry.Space.residueDegree` at the
  ambient generic point, and the two conditions coincide on the support of a `k`-cycle, where
  `dim_δ(Z) = k`. This transports Stacks 0EP2 to the second construction.
* Pushforward along the inclusion of an integral closed subspace, which is
  `AlgebraicGeometry.Space.integralClosedSubspacePushforward` of the localization sequence — the
  pushforward with which `AlgebraicGeometry.Space.IsRationallyEquivalentToZero` is defined — is
  the proper pushforward of Stacks 0EP1 along that inclusion.

## Main results

* `AlgebraicGeometry.Space.properPushforwardInDimension_eq_properCyclePushforward`: the two
  constructions of proper pushforward of `k`-cycles are the same map.
* `AlgebraicGeometry.Space.properCyclePushforward_comp`: Stacks 0EP2 for the second
  construction.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_eq_pushforward`: along a closed
  immersion the integral closed image is the image.
* `AlgebraicGeometry.Space.residueDegree_eq_one_of_isClosedImmersion` and
  `IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion`: the degree of a
  closed immersion at a point, and over the integral closed image, is `1`.
* `AlgebraicGeometry.Space.properCyclePushforward_ι_eq_integralClosedSubspacePushforward`: the
  pushforward of the localization sequence is the proper pushforward along the inclusion.
* `AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward` and
  `AlgebraicGeometry.Space.properPushforwardInDimension_integralClosedSubspacePushforward`: the
  square, in the two currencies.

## Implementation notes

The bridge over the closed immersion `i` needs three facts, and the module docstring of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap` names them. Two are
proved here: that the integral closed image along `i` is the image
(`AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_eq_pushforward`, below), which
holds because the image of
a closed set under a closed immersion is closed, so no closure is taken; and that the degree
over that image is `1`, which is Stacks 0EMX at every point of the source, a closed immersion
being a monomorphism. The third, invariance of the δ-dimension under enlarging the ambient
space, is `AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_pushforward` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps`. Together they make the
degree of Stacks 0EP1 along `i` equal to `1` with no δ-dimension drop, so the proper pushforward
along `i` is the indicator pushforward `Function.extend` of the localization sequence.

Goodness over the base of an integral closed subspace of a good algebraic space, which both
sides of the square need in order to speak of cycles on `W` and `W'` at all, is
`AlgebraicGeometry.Space.isGood_integralClosedSubspace` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantVanishing`; it is not a hypothesis anywhere
below. The module docstring of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles` records the same thing — that
this goodness is available and so need not be carried as a hypothesis.

The square is stated for an arbitrary `W'` and an arbitrary `p'` over `p`: neither the
dominance of `p'` nor the identification of `W'` with the integral closed image of `i ≫ p` is
used. Properness of `p'` is Stacks 0EEG,
`AlgebraicGeometry.Space.IntegralClosedSubspace.isProper_of_comp_ι_eq`, which also holds for an
arbitrary such target, and it is what lets `p'_*` be formed. Only properness of `p` is assumed,
as in the source; the constructions themselves need no more than quasi-compactness, but
Stacks 0EP2 is stated for proper morphisms and that is what is transported.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Residue fields and integral closed images along a closed immersion -/

section ClosedImmersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism to `X` from the spectrum of the residue field of `Y` at a point, along a closed
immersion `i : Y ⟶ X`, is a monomorphism: it is the monomorphic representative of that point
composed with `i`, and a closed immersion is a monomorphism. -/
theorem mono_residueFieldMorphism_comp_of_isClosedImmersion
    (hYdec : IsDecentSpace B S hS Y) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (y : points B S hS Y) :
    Mono (residueFieldMorphism B S hS Y hYdec y ≫ i) :=
  have := (residueFieldRepresentative B S hS Y hYdec y).2.2
  have := mono_of_isClosedImmersion B S hS i hi
  mono_comp _ _

/-- **Stacks 0EMX along a closed immersion.** A closed immersion `i : Y ⟶ X` induces a bijection
from the residue field of `X` at the image of a point of `Y` onto the residue field of `Y` at
that point. -/
theorem bijective_residueFieldHom_of_isClosedImmersion (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (y : points B S hS Y) :
    Function.Bijective (residueFieldHom B S hS Y X hX hYdec hXdec i y) := by
  have hiso : IsIso (CommRingCat.ofHom (residueFieldHom B S hS Y X hX hYdec hXdec i y)) :=
    (isIso_residueFieldHom_iff_mono B S hS Y X hX hYdec hXdec i y).2
      (mono_residueFieldMorphism_comp_of_isClosedImmersion B S hS hYdec hi y)
  simpa using ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (residueFieldHom B S hS Y X hX hYdec hXdec i y))

/-- The residue degree of a closed immersion is one at every point: the extension of residue
fields it induces is an isomorphism. -/
theorem residueDegree_eq_one_of_isClosedImmersion (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (y : points B S hS Y) :
    residueDegree B S hS Y X hX hYdec hXdec i y = 1 :=
  degreeOfFieldHom_eq_one_of_bijective
    (bijective_residueFieldHom_of_isClosedImmersion B S hS hX hXdec hYdec hi y)

/-- The degree of an integral closed subspace over its integral closed image along a closed
immersion is one. -/
theorem IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (Z : IntegralClosedSubspace B S hS Y) :
    IntegralClosedSubspace.degreeOverClosureImage B S hS hX hYdec hXdec i Z = 1 :=
  residueDegree_eq_one_of_isClosedImmersion B S hS hX hXdec hYdec hi _

/-- **The integral closed image along a closed immersion is the image.** For a closed immersion
`i : Y ⟶ X` the closure of the image of an integral closed subspace of `Y` is its image, so the
two maps on integral closed subspaces agree. -/
theorem IntegralClosedSubspace.closureImage_eq_pushforward (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (Z : IntegralClosedSubspace B S hS Y) :
    IntegralClosedSubspace.closureImage B S hS hX hXdec i Z =
      IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi Z := by
  refine injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext ?_)
  show subspacePointSet B S hS X
      (IntegralClosedSubspace.closureImage B S hS hX hXdec i Z).subspace =
    subspacePointSet B S hS X
      (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi Z).subspace
  rw [IntegralClosedSubspace.subspacePointSet_closureImage B S hS hX hXdec i Z,
    IntegralClosedSubspace.subspacePointSet_pushforward B S hS hX hY hXdec hi Z]
  exact (IntegralClosedSubspace.imagePoints B S hS hX hY hi Z).isClosed'.closure_eq

end ClosedImmersion

/-! ### The two proper pushforwards of cycles agree -/

section Compare

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The two degrees used by the two constructions of proper pushforward are the same number:
both are the degree of the residue field extension at the generic point. -/
theorem IntegralClosedSubspace.degreeOverImage_eq_functionFieldDegree (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace.degreeOverImage D sX sY hX hY f W =
      functionFieldDegree D sX hX sY hY f W :=
  rfl

/-- On an integral closed subspace of δ-dimension `k` the weight of the pushforward of
`k`-cycles is the degree of the pushforward of cycles: the two conditions tested, that the
integral closed image have δ-dimension `k` and that it have the δ-dimension of the subspace,
coincide there. -/
theorem properPushforwardWeightInDimension_eq_properCycleDegree (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k) :
    properPushforwardWeightInDimension D sX sY hX hY f k W =
      properCycleDegree D sX hX sY hY f W := by
  subst hW
  rfl

/-- The coefficients of the two proper pushforwards agree on a `k`-cycle: off the support both
vanish, and on the support the δ-dimension is `k`, where the two weights agree. -/
theorem properPushforwardCoeffInDimension_eq_properCyclePushforwardCoeff (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : α ∈ cyclesOfDimension D sX k)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    properPushforwardCoeffInDimension D sX sY hX hY f k α Z' =
      properCyclePushforwardCoeff D sX hX sY hY f α Z' := by
  rw [properPushforwardCoeffInDimension, finsum_mem_def]
  refine finsum_congr fun W => ?_
  by_cases hα0 : α W = 0
  · rw [hα0, zero_mul]
    by_cases hmem : W ∈ (fun W => cycleImageSubspace D sY hY f W) ⁻¹' {Z'}
    · rw [Set.indicator_of_mem hmem, hα0, zero_mul]
    · rw [Set.indicator_of_notMem hmem]
  · by_cases him : cycleImageSubspace D sY hY f W = Z'
    · rw [Set.indicator_of_mem (show W ∈ (fun W => cycleImageSubspace D sY hY f W) ⁻¹' {Z'} from
        him), properCycleMult, ite_eq_left him,
        properPushforwardWeightInDimension_eq_properCycleDegree D sX sY hX hY f k W
          (hα.2 W hα0)]
    · rw [Set.indicator_of_notMem
        (show W ∉ (fun W => cycleImageSubspace D sY hY f W) ⁻¹' {Z'} from him),
        properCycleMult, ite_eq_right him, mul_zero]

/-- **The two constructions of proper pushforward of `k`-cycles agree.** The pushforward of
Stacks 0EP1 built with the weight testing `dim_δ(Z') = k` and the one built with the degree
testing `dim_δ(Z') = dim_δ(Z)` are the same homomorphism `Z_k(X) → Z_k(Y)`. -/
theorem properPushforwardInDimension_eq_properCyclePushforward (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ) (α : CycleGroup D sX k) :
    properPushforwardInDimension D sX sY hX hY f hfB hf k α =
      properCyclePushforward D sX hX sY hY hfB hf.2.1.2 k α :=
  Subtype.ext (funext fun Z' =>
    properPushforwardCoeffInDimension_eq_properCyclePushforwardCoeff D sX sY hX hY f k α.1 α.2 Z')

/-- Proper pushforward of cycles does not see the name of the morphism: equal morphisms push
forward equally. -/
theorem properCyclePushforward_congr (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {f g : X ⟶ Y} (hfg : f = g) (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (hgB : g ≫ sY = sX)
    (hg : IsQuasiCompact D.site D.base D.base_mem g) (k : ℤ) (α : CycleGroup D sX k) :
    properCyclePushforward D sX hX sY hY hfB hf k α =
      properCyclePushforward D sX hX sY hY hgB hg k α := by
  subst hfg
  rfl

/-- **Stacks 0EP2 for the pushforward of cycles.** Pushing a `k`-cycle forward along `f : X ⟶ Y`
and then along `g : Y ⟶ Z` is pushing it forward along the composite. This is Stacks 0EP2,
transported along the agreement of the two constructions. -/
theorem properCyclePushforward_comp (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (sZ : Z ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (hZ : D.IsGood sZ) {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfB : f ≫ sY = sX) (hgB : g ≫ sZ = sY) (hf : IsProper D.site D.base D.base_mem f)
    (hg : IsProper D.site D.base D.base_mem g) (k : ℤ) (α : CycleGroup D sX k) :
    properCyclePushforward D sY hY sZ hZ hgB hg.2.1.2 k
        (properCyclePushforward D sX hX sY hY hfB hf.2.1.2 k α) =
      properCyclePushforward D sX hX sZ hZ (by rw [Category.assoc, hgB, hfB])
        (isProper_comp D.site D.base D.base_mem hX.1 hY.1 hZ.1 f g hf hg).2.1.2 k α := by
  rw [← properPushforwardInDimension_eq_properCyclePushforward D sX sY hX hY hfB hf k α,
    ← properPushforwardInDimension_eq_properCyclePushforward D sY sZ hY hZ hgB hg k,
    ← properPushforwardInDimension_eq_properCyclePushforward D sX sZ hX hZ
      (show (f ≫ g) ≫ sZ = sX by rw [Category.assoc, hgB, hfB])
      (isProper_comp D.site D.base D.base_mem hX.1 hY.1 hZ.1 f g hf hg) k α]
  exact properPushforwardInDimension_comp D sX sY sZ hX hY hZ f g hfB hgB hf hg k α

end Compare

/-! ### Pushforward along the inclusion of an integral closed subspace -/

section Inclusion

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The degree of Stacks 0EP1 along the inclusion of an integral closed subspace is `1`: the
δ-dimension cannot drop, because the integral closed image is the image and an immersion does
not change the δ-dimension, and the degree of the extension of residue fields is `1`. -/
theorem properCycleDegree_ι_eq_one (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) :
    properCycleDegree D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) sX hX
        W.subspace.ι V = 1 := by
  have hdim : deltaDimension D sX (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hX.1 (D.isDecentSpace_of_isGood sX hX) W.subspace.ι V) =
      deltaDimension D (W.subspace.ι ≫ sX) V := by
    rw [IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V]
    exact IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V
  have hone : functionFieldDegree D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) sX hX W.subspace.ι V = 1 :=
    IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion D.site D.base
      D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) W.isIntegralSpace.2.1
      W.isClosedSubspace.2 V
  rw [properCycleDegree, ite_eq_left hdim, hone, Nat.cast_one]

open scoped Classical in
/-- The multiplicity of Stacks 0EP1 along the inclusion of an integral closed subspace is the
indicator of the image. -/
theorem properCycleMult_ι (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCycleMult D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) sX hX
        W.subspace.ι V Z =
      if IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V = Z then 1 else 0 := by
  rw [properCycleMult, properCycleDegree_ι_eq_one D sX hX W V,
    IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V]

/-- **The coefficients of the two pushforwards along an inclusion agree.** The proper pushforward
of coefficient families along the inclusion of an integral closed subspace is the pushforward of
the localization sequence: both carry the coefficient at an integral closed subspace of `W` to
the coefficient at its image in `X`, and vanish at an integral closed subspace of `X` which is
not such an image. -/
theorem properCyclePushforwardCoeff_ι_eq_cycleClosedPushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (β : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor → ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCyclePushforwardCoeff D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        sX hX W.subspace.ι β Z =
      cycleClosedPushforward D hX.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
        W.isClosedSubspace.2 β Z := by
  by_cases hex : ∃ V, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V = Z
  · obtain ⟨V₀, rfl⟩ := hex
    rw [cycleClosedPushforward_apply_pushforward, properCyclePushforwardCoeff]
    refine (finsum_eq_single _ V₀ ?_).trans ?_
    · intro V hV
      rw [properCycleMult_ι D sX hX W V, ite_eq_right fun h => hV
        (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1
          W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 h),
        mul_zero]
    · rw [properCycleMult_ι D sX hX W V₀, ite_eq_left rfl, mul_one]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 β Z fun V hV => hex ⟨V, hV⟩,
      properCyclePushforwardCoeff]
    refine finsum_eq_zero_of_forall_eq_zero fun V => ?_
    rw [properCycleMult_ι D sX hX W V, ite_eq_right fun h => hex ⟨V, h⟩, mul_zero]

/-- **Proper pushforward along an inclusion is the pushforward of the localization sequence.**
The pushforward of `k`-cycles of Stacks 0EP1 along the inclusion of an integral closed subspace
`W ⊆ X` of a good algebraic space over the base is the pushforward
`AlgebraicGeometry.Space.integralClosedSubspacePushforward` with which rational equivalence is
defined. -/
theorem properCyclePushforward_ι_eq_integralClosedSubspacePushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) :
    properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) sX hX
        (f := W.subspace.ι) rfl (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem
          W.isClosedSubspace.2) k c =
      integralClosedSubspacePushforward D sX hX W k c :=
  Subtype.ext (funext fun Z =>
    properCyclePushforwardCoeff_ι_eq_cycleClosedPushforward D sX hX W c.1 Z)

end Inclusion

/-! ### The square -/

section Square

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The inclusion of an integral closed subspace of a good space is proper. -/
private theorem isProper_ι (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsProper D.site D.base D.base_mem W.subspace.ι :=
  isProper_of_isClosedImmersion D.site D.base D.base_mem W.isClosedSubspace.1 hX.1
    W.subspace.ι W.isClosedSubspace.2

/-- **The square form of Stacks 0EP2.** Let `p : X ⟶ Y` be a proper morphism of good algebraic
spaces over the base, let `W ⊆ X` be an integral closed subspace with inclusion `i`, let
`W' ⊆ Y` be an integral closed subspace with inclusion `i'` and let `p' : W ⟶ W'` be a morphism
over `p`. Then `p_* i_* = i'_* p'_*` on `k`-cycles of `W`.

Taking `W'` to be the integral closed image of `i ≫ p` and `p'` the morphism of Stacks 0EEG,
which exists and is proper and surjective, this is the identity
`p_* i_* div(f) = i'_* p'_* div(f)` the chapter uses on a principal divisor `div(f)`; nothing
below needs `W'` to be that image, nor `p'` to be dominant.

The two closed-immersion pushforwards are proper pushforwards, by
`AlgebraicGeometry.Space.properCyclePushforward_ι_eq_integralClosedSubspacePushforward`, and both
sides are then the pushforward along the one composite `i ≫ p = p' ≫ i'`, by Stacks 0EP2. -/
theorem properCyclePushforward_integralClosedSubspacePushforward (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (p' : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hp' : p' ≫ W'.subspace.ι = W.subspace.ι ≫ p) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) :
    properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (integralClosedSubspacePushforward D sX hX W k c) =
      integralClosedSubspacePushforward D sY hY W' k
        (properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W') (f := p')
          (show p' ≫ W'.subspace.ι ≫ sY = W.subspace.ι ≫ sX by
            rw [← Category.assoc, hp', Category.assoc, hpB])
          (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp
            W W' p' hp').2.1.2 k c) := by
  have hp'p : IsProper D.site D.base D.base_mem p' :=
    IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp
      W W' p' hp'
  have hp'B : p' ≫ W'.subspace.ι ≫ sY = W.subspace.ι ≫ sX := by
    rw [← Category.assoc, hp', Category.assoc, hpB]
  rw [← properCyclePushforward_ι_eq_integralClosedSubspacePushforward D sX hX W k c,
    ← properCyclePushforward_ι_eq_integralClosedSubspacePushforward D sY hY W' k
      (properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W') (f := p') hp'B
        hp'p.2.1.2 k c),
    properCyclePushforward_comp D (W.subspace.ι ≫ sX) sX sY
      (isGood_integralClosedSubspace D sX hX W) hX hY rfl hpB (isProper_ι D sX hX W) hp k c,
    properCyclePushforward_comp D (W.subspace.ι ≫ sX) (W'.subspace.ι ≫ sY) sY
      (isGood_integralClosedSubspace D sX hX W) (isGood_integralClosedSubspace D sY hY W') hY
      hp'B rfl hp'p (isProper_ι D sY hY W') k c]
  exact properCyclePushforward_congr D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W) sY hY hp'.symm _ _ _ _ k c

/-- **The square form of Stacks 0EP2 for the pushforward of `k`-cycles.** The same identity with
the proper pushforward of `AlgebraicGeometry.Space.properPushforwardInDimension`, the
construction Stacks 0EP2 is stated for, in place of
`AlgebraicGeometry.Space.properCyclePushforward`. -/
theorem properPushforwardInDimension_integralClosedSubspacePushforward (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (p' : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hp' : p' ≫ W'.subspace.ι = W.subspace.ι ≫ p) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) :
    properPushforwardInDimension D sX sY hX hY p hpB hp k
        (integralClosedSubspacePushforward D sX hX W k c) =
      integralClosedSubspacePushforward D sY hY W' k
        (properPushforwardInDimension D (W.subspace.ι ≫ sX) (W'.subspace.ι ≫ sY)
          (isGood_integralClosedSubspace D sX hX W) (isGood_integralClosedSubspace D sY hY W') p'
          (show p' ≫ W'.subspace.ι ≫ sY = W.subspace.ι ≫ sX by
            rw [← Category.assoc, hp', Category.assoc, hpB])
          (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp
            W W' p' hp') k c) := by
  rw [properPushforwardInDimension_eq_properCyclePushforward D sX sY hX hY hpB hp k,
    properPushforwardInDimension_eq_properCyclePushforward D (W.subspace.ι ≫ sX)
      (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sX hX W)
      (isGood_integralClosedSubspace D sY hY W') _ _ k c]
  exact properCyclePushforward_integralClosedSubspacePushforward D sX sY hX hY hpB hp W W' p' hp'
    k c

end Square

end AlgebraicGeometry.Space

end
