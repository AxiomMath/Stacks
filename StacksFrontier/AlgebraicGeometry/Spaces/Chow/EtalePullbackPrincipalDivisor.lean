module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleOfClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Étale pullback of a principal divisor

In Situation 0EDT let `f : X ⟶ Y` be an étale morphism of good algebraic spaces over `B`, let
`Y` be integral and let `g ∈ R(Y)^*`. Stacks 0EQ2 is the identity of cycles on `X`

`f^*(div_Y(g)) = ∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`,

the sum being over the irreducible components `X'` of `X` in the sense of Remark 0EE8. The
left-hand side is the flat pullback of Stacks 0EP8 at relative dimension `0`, an étale morphism
being flat (Stacks 0467); the right-hand side is the locally finite sum over the components of
the proper pushforward of Stacks 0EP1 of the principal divisor of Stacks 0EQ1 on the component,
formed with the pullback `g ∘ f|_{X'}` of `g` along the dominant morphism `f|_{X'} : X' ⟶ Y`.

## Main definitions

* `AlgebraicGeometry.Space.IrreducibleComponentSubspace`: the irreducible components of an
  algebraic space, as a type.
* `AlgebraicGeometry.Space.etalePullbackCycleMap`: the flat pullback of cycles along an étale
  morphism, of relative dimension `0`.
* `AlgebraicGeometry.Space.EtaleComponentDivisorData`: data on the irreducible components of `X`
  from which the right-hand side is formed, including the dominance of each `f|_{X'}`.
* `AlgebraicGeometry.Space.EtaleComponentDivisorData.componentRationalFunction`:
  `g ∘ f|_{X'} ∈ R(X')`, the image of `g` under the extension of function fields induced by the
  dominant morphism `f|_{X'}`.
* `AlgebraicGeometry.Space.EtaleComponentDivisorData.componentDivisorCycle`:
  `div_{X'}(g ∘ f|_{X'})` as an element of `Z_{n-1}(X')`.
* `AlgebraicGeometry.Space.EtaleComponentDivisorData.componentPushforwardCoeff`: the
  coefficient at an integral closed subspace `Z ⊆ X` of `∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`.

## Main results

* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_eq_deltaValue_genericPoint`: the
  δ-dimension of a good integral algebraic space is the value of `δ` at its generic point.
* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_irreducibleComponentSubspace`: an
  irreducible component `X'` of `X` along which `f` is dominant has `dim_δ(X') = dim_δ(Y)`.
* `AlgebraicGeometry.Space.EtaleComponentDivisorData.componentPushforwardCoeff_eq_zero`: the
  right-hand side vanishes at an integral closed subspace of δ-dimension other than `n - 1`.
* `AlgebraicGeometry.Space.etalePullback_principalDivisorCycle_eq_sum_components_iff`: the
  displayed identity, read coefficientwise, holds at every integral closed subspace of `X` if
  and only if it holds at those of δ-dimension `n - 1`.

## Implementation notes

The family of irreducible components of `X` is only locally finite, so
`∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})` is not a sum in the group `Z_{n-1}(X)`: it is the
cycle whose coefficient at each integral closed subspace is the finite sum
`AlgebraicGeometry.Space.EtaleComponentDivisorData.componentPushforwardCoeff`, and the identity
of cycles is the identity of coefficients at every integral closed subspace of `X`.

## References

* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0EML](https://stacks.math.columbia.edu/tag/0EML)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPL](https://stacks.math.columbia.edu/tag/0EPL)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The irreducible components of an algebraic space -/

/-- The *irreducible components* of an algebraic space `X` over `S`, as a type: the integral
closed subspaces of `X` whose set of points is an irreducible component of `|X|`, as in
description (3) of Remark 0EE8. -/
abbrev IrreducibleComponentSubspace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) :=
  {W : IntegralClosedSubspace B S hS X // IsIrreducibleComponent B S hS hX W.subspace}

/-! ### The δ-dimension of an integral space and of an irreducible component -/

/-- The δ-dimension of a good integral algebraic space `X/B` is the value of `δ_{X/B}` at the
generic point of `X`. -/
theorem deltaDimensionClosed_univ_eq_deltaValue_genericPoint
    (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X) :
    deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      ((D.deltaValue sX (genericPoint D.site D.base D.base_mem hX.1 hint) : ℤ) : EInt) := by
  have hirr : IrreducibleSpace (points D.site D.base D.base_mem X) := hint.2.2
  have h1 := deltaDimensionClosed_eq_deltaDimensionIrreducible D sX hX
    (⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ :
      IrreducibleCloseds (points D.site D.base D.base_mem X))
  have h2 := deltaDimensionIrreducible_eq_of_isGenericPoint D sX hX
    (⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ :
      IrreducibleCloseds (points D.site D.base D.base_mem X))
    (isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hint)
  rwa [h2] at h1

/-- In Situation 0EDT let `f : X ⟶ Y` be an étale morphism of
good algebraic spaces over `B`, let `Y` be integral with `dim_δ(Y) = n`, and let `X' ⊆ X` be an
irreducible component of `X` such that `f|_{X'}` carries the generic point of `X'` to the
generic point of `Y`. Then `dim_δ(X') = n`. -/
theorem deltaDimensionClosed_univ_irreducibleComponentSubspace
    (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) {n : ℤ}
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (hgood : D.IsGood (W.1.subspace.ι ≫ sX))
    (hdom : pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor (W.1.subspace.ι ≫ f)
          (genericPoint D.site D.base D.base_mem hgood.1 W.1.isIntegralSpace) =
        genericPoint D.site D.base D.base_mem hY.1 hintY) :
    deltaDimensionClosed D (W.1.subspace.ι ≫ sX) hgood Set.univ isClosed_univ = (n : EInt) := by
  have h1 := D.deltaValue_comp_of_isLocallyQuasiFinite hgood.1 hX.1 W.1.subspace.ι sX
    (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem W.1.subspace.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem W.1.isClosedSubspace.2))
    hX.2.2 (genericPoint D.site D.base D.base_mem hgood.1 W.1.isIntegralSpace)
  have h2 := D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 f sY
    (isLocallyQuasiFinite_of_isEtale D.site D.base D.base_mem hY.1 hetale) hY.2.2
    (pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor W.1.subspace.ι
      (genericPoint D.site D.base D.base_mem hgood.1 W.1.isIntegralSpace))
  rw [hbase] at h2
  have h3 : pointsMap D.site D.base D.base_mem X f
        (pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor W.1.subspace.ι
          (genericPoint D.site D.base D.base_mem hgood.1 W.1.isIntegralSpace)) =
      genericPoint D.site D.base D.base_mem hY.1 hintY := by
    simpa only [pointsMap_comp, Function.comp_apply] using hdom
  rw [deltaDimensionClosed_univ_eq_deltaValue_genericPoint D (W.1.subspace.ι ≫ sX) hgood
      W.1.isIntegralSpace, h1, h2, h3,
    ← deltaDimensionClosed_univ_eq_deltaValue_genericPoint D sY hY hintY]
  exact hnY

/-! ### The étale pullback of cycles -/

/-- The flat pullback `f^* : Z_k(Y) → Z_k(X)` of cycles along an étale morphism `f : X ⟶ Y` of
good algebraic spaces over `B` of relative dimension `0`. -/
def etalePullbackCycleMap (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hrel : HasRelativeDimension 0 D.site D.base D.base_mem f)
    (k : ℤ) :
    CycleGroup D sY k →+ CycleGroup D sX k :=
  flatPullbackMap D sX hX sY hY f hbase 0
    (isFlat_of_isEtale D.site D.base D.base_mem hetale) hrel k k (by simp)

/-! ### The principal divisors on the irreducible components -/

/-- Data on the irreducible components `X' ⊆ X` from which `div_{X'}(g ∘ f|_{X'})` is formed:
goodness of `X'/B`, the hypotheses of Stacks 0ENK on the henselian local rings at the generic
points of the prime divisors of `X'` with the embeddings `R(X') → Q(𝒪^h_{X',ξ})`, dominance of
`f|_{X'} : X' ⟶ Y`, invertibility of `g ∘ f|_{X'}` in `R(X')`, local finiteness of the support of
its divisor, and the dimension function `δ_{X'/B}` on `X'`. -/
structure EtaleComponentDivisorData (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) (n : ℤ)
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (g : rationalFunctions D.site D.base D.base_mem hY.1) where
  /-- Each irreducible component of `X` is good over the base. -/
  good : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    D.IsGood (W.1.subspace.ι ≫ sX)
  /-- The henselian local ring at the generic point of a prime divisor of an irreducible
  component is nontrivial. -/
  nontrivial : ∀ (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor),
    Nontrivial ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (good W).1
      W.1.isIntegralSpace.2.1)
  /-- That henselian local ring is Noetherian. -/
  noetherian : ∀ (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor),
    IsNoetherianRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (good W).1
      W.1.isIntegralSpace.2.1)
  /-- That henselian local ring has Krull dimension at most one. -/
  krullDimLE : ∀ (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor),
    Ring.KrullDimLE 1 ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (good W).1
      W.1.isIntegralSpace.2.1)
  /-- The embeddings `R(X') → Q(𝒪^h_{X',ξ})` at the generic points of the prime
  divisors of an irreducible component. -/
  emb : ∀ (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor),
    rationalFunctions D.site D.base D.base_mem (good W).1 →+*
      P.genericTotalFractionRing D.site D.base D.base_mem (good W).1
        W.1.isIntegralSpace.2.1
  /-- The restriction of `f` to an irreducible component is dominant: it carries the generic
  point of the component to the generic point of `Y`. -/
  dom : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor (W.1.subspace.ι ≫ f)
        (genericPoint D.site D.base D.base_mem (good W).1 W.1.isIntegralSpace) =
      genericPoint D.site D.base D.base_mem hY.1 hintY
  /-- `g ∘ f|_{X'}` lies in `R(X')^*`. -/
  unit : ∀ (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor),
    IsUnit (emb W P (rationalFunctionMap D.site D.base D.base_mem (good W).1 hY.1
      W.1.isIntegralSpace hintY (W.1.subspace.ι ≫ f) (dom W) g))
  /-- The prime divisors of `X'` along which `g ∘ f|_{X'}` has nonzero order of vanishing are
  locally finite in `|X'|`. -/
  locallyFinite : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    letI := nontrivial W
    letI := noetherian W
    letI := krullDimLE W
    LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor =>
      if principalDivisorCoefficients D.site D.base D.base_mem (good W).1
            W.1.isIntegralSpace.2.1 (emb W)
            (rationalFunctionMap D.site D.base D.base_mem (good W).1 hY.1
              W.1.isIntegralSpace hintY (W.1.subspace.ι ≫ f) (dom W) g) (unit W) P = 0 then ∅
        else P.support D.site D.base D.base_mem W.1.subspace.toFunctor
  /-- A dimension function on `|X'|`. -/
  dimFun : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    DimensionFunction (points D.site D.base D.base_mem W.1.subspace.toFunctor)
  /-- That dimension function is `δ_{X'/B}`. -/
  dimFun_eq : ∀ (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (x : points D.site D.base D.base_mem W.1.subspace.toFunctor),
    dimFun W x = D.deltaValue (W.1.subspace.ι ≫ sX) x

namespace EtaleComponentDivisorData

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {f : X ⟶ Y} {hbase : f ≫ sY = sX} {hetale : IsEtale D.site D.base D.base_mem f}
    {hintY : IsIntegralSpace D.site D.base D.base_mem Y} {n : ℤ}
    {hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)}
    {g : rationalFunctions D.site D.base D.base_mem hY.1}
    (data : EtaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g)
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)

/-- `g ∘ f|_{X'} ∈ R(X')`: the image of `g` under the extension of function fields induced by
the dominant morphism `f|_{X'} : X' ⟶ Y`. -/
def componentRationalFunction : rationalFunctions D.site D.base D.base_mem (data.good W).1 :=
  rationalFunctionMap D.site D.base D.base_mem (data.good W).1 hY.1 W.1.isIntegralSpace hintY
    (W.1.subspace.ι ≫ f) (data.dom W) g

/-- The principal divisor `div_{X'}(g ∘ f|_{X'}) = ∑_Z ord_Z(g ∘ f|_{X'}) [Z]` on an
irreducible component `X'`, as an element of `Z_{n-1}(X')`. -/
def componentDivisorCycle : CycleGroup D (W.1.subspace.ι ≫ sX) (n - 1) :=
  letI := data.nontrivial W
  letI := data.noetherian W
  letI := data.krullDimLE W
  principalDivisorCycle D (W.1.subspace.ι ≫ sX) (data.good W) W.1.isIntegralSpace.2.1
    (data.emb W) (data.componentRationalFunction W) (data.unit W) (data.locallyFinite W)
    W.1.isIntegralSpace (data.dimFun W) (data.dimFun_eq W)
    (deltaDimensionClosed_univ_irreducibleComponentSubspace D sX hX sY hY hbase hetale hintY
      hnY W (data.good W) (data.dom W))

/-- The pushforward `(X' → X)_* div_{X'}(g ∘ f|_{X'})` along the inclusion of an irreducible
component, as an element of `Z_{n-1}(X)`. -/
def componentDivisorPushforward : CycleGroup D sX (n - 1) :=
  properCyclePushforward D (W.1.subspace.ι ≫ sX) (data.good W) sX hX
    (f := W.1.subspace.ι) rfl
    (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem W.1.isClosedSubspace.2)
    (n - 1) (data.componentDivisorCycle W)

/-- The right-hand side of Stacks 0EQ2, coefficientwise: the coefficient at an integral closed
subspace `Z ⊆ X` of `∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`, the sum being over the
irreducible components `X'` of `X`. -/
def componentPushforwardCoeff (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  ∑ᶠ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    (data.componentDivisorPushforward W).1 Z

/-- The right-hand side of Stacks 0EQ2 vanishes at an integral closed subspace of `X` whose
δ-dimension is not `n - 1`. -/
theorem componentPushforwardCoeff_eq_zero
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sX Z ≠ n - 1) :
    data.componentPushforwardCoeff Z = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun W => by
    by_contra hne
    exact hZ ((data.componentDivisorPushforward W).2.2 Z hne)

end EtaleComponentDivisorData

/-! ### Stacks 0EQ2 -/

section Identity

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hrel : HasRelativeDimension 0 D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

variable [∀ P : PrimeDivisor D.site D.base D.base_mem Y,
    Nontrivial ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hintY.2.1)]
  [∀ P : PrimeDivisor D.site D.base D.base_mem Y,
    IsNoetherianRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hintY.2.1)]
  [∀ P : PrimeDivisor D.site D.base D.base_mem Y,
    Ring.KrullDimLE 1 ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hintY.2.1)]

variable (embY : ∀ P : PrimeDivisor D.site D.base D.base_mem Y,
    rationalFunctions D.site D.base D.base_mem hY.1 →+*
      P.genericTotalFractionRing D.site D.base D.base_mem hY.1 hintY.2.1)
  (g : rationalFunctions D.site D.base D.base_mem hY.1)
  (hg : ∀ P : PrimeDivisor D.site D.base D.base_mem Y, IsUnit (embY P g))
  (hfinY : LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem Y =>
    if principalDivisorCoefficients D.site D.base D.base_mem hY.1 hintY.2.1 embY g hg P = 0 then ∅
    else P.support D.site D.base D.base_mem Y)
  (dY : DimensionFunction (points D.site D.base D.base_mem Y))
  (hdY : ∀ y, dY y = D.deltaValue sY y) {n : ℤ}
  (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))

/-- The left-hand side of Stacks 0EQ2: the étale pullback `f^*(div_Y(g))` of the principal
divisor of `g ∈ R(Y)^*`, as an element of `Z_{n-1}(X)`. -/
def etalePullbackPrincipalDivisorCycle : CycleGroup D sX (n - 1) :=
  etalePullbackCycleMap D sX hX sY hY hbase hetale hrel (n - 1)
    (principalDivisorCycle D sY hY hintY.2.1 embY g hg hfinY hintY dY hdY hnY)

/-- In Situation 0EDT let `f : X ⟶ Y` be an étale morphism of good algebraic spaces over `B`, let
`Y` be integral with `dim_δ(Y) = n` and let `g ∈ R(Y)^*`. Then the identity of cycles on `X`

`f^*(div_Y(g)) = ∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`,

the sum being over the irreducible components `X'` of `X` (Remark 0EE8), holds at every integral
closed subspace `Z ⊆ X`, coefficientwise, if and only if it holds at those of δ-dimension
`n - 1`. -/
@[stacks 0EQ2 "REDUCED, not proved: the displayed equality of cycles on X — coefficientwise at
  every integral closed subspace, with the sum over the irreducible components of X — HOLDS IF
  AND ONLY IF it holds at the integral closed subspaces of δ-dimension n-1. Proved away from
  them, where both sides vanish, both being (n-1)-cycles. The coefficient identity at those
  subspaces is NOT proved and NOT assumed: it is the source's steps three to six, namely the
  square of henselian local rings of Remark 0EPL, the multiplicity one of Lemma 0EPY, the length
  equality along a flat unramified map of Lemma 02M1 and the length decomposition of Lemma 02QG.
  Hypotheses: hrel, the relative dimension 0 of the étale morphism, flatness itself being
  supplied from Stacks 0467; and, on each irreducible component, the fields of
  EtaleComponentDivisorData — goodness over the base, the
  three hypotheses of Stacks 0ENK with the embeddings they go with, the dominance of f restricted
  to the component (the source's first step, which makes g ∘ f|_{X'} defined), that g ∘ f|_{X'}
  is in R(X')^*, local finiteness of its divisor (Stacks 0ENN) and the dimension function of
  Stacks 0EDN. That dim_δ(X') = n for every component, the source's second paragraph, is
  proved"]
theorem etalePullback_principalDivisorCycle_eq_sum_components_iff
    (data : EtaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g) :
    (∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        (etalePullbackPrincipalDivisorCycle D sX hX sY hY hbase hetale hrel hintY embY g hg
            hfinY dY hdY hnY).1 Z =
          data.componentPushforwardCoeff Z) ↔
      ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        deltaDimension D sX Z = n - 1 →
          (etalePullbackPrincipalDivisorCycle D sX hX sY hY hbase hetale hrel hintY embY g hg
              hfinY dY hdY hnY).1 Z =
            data.componentPushforwardCoeff Z := by
  refine ⟨fun h Z _ => h Z, fun h Z => ?_⟩
  by_cases hZ : deltaDimension D sX Z = n - 1
  · exact h Z hZ
  · rw [data.componentPushforwardCoeff_eq_zero hZ]
    by_contra hne
    exact hZ ((etalePullbackPrincipalDivisorCycle D sX hX sY hY hbase hetale hrel hintY embY g
      hg hfinY dY hdY hnY).2.2 Z hne)

end Identity

end AlgebraicGeometry.Space

end
