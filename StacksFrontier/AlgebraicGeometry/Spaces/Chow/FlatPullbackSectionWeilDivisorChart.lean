module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisorLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentGenericFreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericResidueField

/-!
# The coefficients of the right-hand side of Stacks 0EQQ, read on a chart

In the situation of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisorLocal`
let `U ⟶ V` be a diagram of affine étale charts over `f`, with `ℒ` free over `V` on a generator
`e`, and `u` a point of `U`. Write `O = 𝒪_{U, u}` and

`c = φ(s / e) ∈ Q(O)`

for the image of the chart ratio of `s`, read at the image `v` of `u` in `Q(𝒪_{V, v})`, under the
stalk map `φ : 𝒪_{V, v} → O`, which is flat. For an irreducible component `W` of `X` and a point
`q` of the base change `U ×_X W` over `u` lying over the generic point of a prime divisor `Z_W`
of `W`, this file proves

`ord_{Z_W}(f|_W^*(s)) = ord_{𝒪_{U_W, q}}(π(c))`,

with `π : O → 𝒪_{U_W, q}` the surjective stalk map of the closed immersion `U ×_X W → U`. This is
`AlgebraicGeometry.Space.orderOfVanishingSection_pullbackMeromorphicSection_eq_ordTotalFracInt_map`
for `f|_W` on the chart diagram `U ×_X W ⟶ V`, the stalk map of the composite being `π ∘ φ`.

## Main definitions

* `AlgebraicGeometry.Space.flatChartReading`: the element `c = φ(s / e)` of `Q(𝒪_{U, u})`.

## Main results

* `AlgebraicGeometry.Space.componentDivisor_apply_eq_ordTotalFracInt`: the coefficient of
  `div_{f^*ℒ|_W}(f|_W^*(s))` at `Z_W` is `ord_{𝒪_{U_W, q}}(π(c))`.

## References

* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicFunctionAlgebra

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) {n : ℤ}
    (hn : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (hL : IsInvertibleSheaf D sY hY L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L) (hs : s ≠ 0)

/-! ### The data of a chart diagram carrying a generator -/

include hintY in
/-- The weakly associated points of an integral good space are points of codimension zero. -/
theorem localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood :
    ∀ z ∈ weaklyAssociatedPointsOfSpace D.site D.base D.base_mem ⟨Y, hY.1⟩,
      localRingDimension D.site D.base D.base_mem z = 0 :=
  localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    D.site D.base D.base_mem hY.1 hintY

include sY hY in
/-- A good space has locally finitely many irreducible components. -/
theorem hasLocallyFiniteIrreducibleComponents_of_isGood :
    HasLocallyFiniteIrreducibleComponents D.site D.base D.base_mem Y :=
  hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem Y hY.1
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)

include hflat in
/-- Along a flat morphism the stalk maps of a chart diagram carry nonzerodivisors to
nonzerodivisors. -/
theorem nonZeroDivisors_le_comap_stalkMap_of_isFlat
    (d : ChartDiagram D.site D.base D.base_mem X Y f) (u : chartScheme d.U) :
    ((chartScheme d.V).presheaf.stalk
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u))⁰ ≤
      ((chartScheme d.U).presheaf.stalk u)⁰.comap
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).stalkMap u).hom := by
  have : Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g) :=
    hflat d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  exact fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat _ u hx

/-- **The reading `c = φ(s / e)` of `s` at a point of the source chart of a chart diagram.** The
chart ratio `s / e ∈ 𝒦_Y(V)` read in `Q(𝒪_{V, v})` at the image `v` of `u`, pushed along the flat
stalk map `𝒪_{V, v} → 𝒪_{U, u}`. -/
def flatChartReading (d : ChartDiagram D.site D.base D.base_mem X Y f)
    (hV : IsAffine (chartScheme d.V))
    (e : (W : SmallEtale D.site D.base D.base_mem Y) → (W ⟶ d.V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V),
      Function.Bijective fun x : chartRing D.site D.base D.base_mem Y hY.1 W ↦ x • e W k)
    (u : chartScheme d.U) : FractionRing ((chartScheme d.U).presheaf.stalk u) :=
  IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
    (FractionRing ((chartScheme d.U).presheaf.stalk u))
    (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).stalkMap u).hom
    (nonZeroDivisors_le_comap_stalkMap_of_isFlat D f hflat d u)
    (chartPointMeromorphicMap D.site D.base D.base_mem ⟨Y, hY.1⟩ d.V hV
      (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨Y, hY.1⟩
        (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY
          hintY)
        (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) d.V hV)
      (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u)
      (chartRatio D.site D.base D.base_mem Y hY.1 L d.V e hecompat hebij s))

/-- A nonzero meromorphic section of an invertible sheaf on an integral good space is regular. -/
private theorem isRegularMeromorphicSection_of_ne_zero_of_isGood
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) (hL : IsInvertibleSheaf D sY hY L)
    (hs : s ≠ 0) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L s :=
  (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s).mpr hs

include hintY hL hs in
/-- The reading `c` is a unit: `s` is regular, so its chart ratio is a unit of `𝒦_Y(V)`. -/
theorem isUnit_flatChartReading (d : ChartDiagram D.site D.base D.base_mem X Y f)
    (hV : IsAffine (chartScheme d.V))
    (e : (W : SmallEtale D.site D.base D.base_mem Y) → (W ⟶ d.V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V),
      Function.Bijective fun x : chartRing D.site D.base D.base_mem Y hY.1 W ↦ x • e W k)
    (u : chartScheme d.U) :
    IsUnit (flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij u) := by
  have hreg := isRegularMeromorphicSection_of_ne_zero_of_isGood D sY hY L s hintY hL hs
  exact ((isUnit_chartRatio_of_isRegularMeromorphicSection D.site D.base D.base_mem ⟨Y, hY.1⟩
    (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY hintY)
    (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) L d.V hV e hecompat hebij s
    hreg).map _).map _

/-! ### The order of the pulled back section on a component, on the base-changed chart -/

include hX in
/-- An integral closed subspace of an irreducible component `W` of δ-dimension `n + r - 1`
underlies a prime divisor of `W` (Stacks 0EPZ on `W`). -/
theorem exists_primeDivisor_of_deltaDimension_component
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWd : deltaDimension D sX W = n + r)
    (Zw : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (hZwd : deltaDimension D (W.subspace.ι ≫ sX) Zw = n + r - 1) :
    ∃ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      P.toIntegralClosedSubspace D.site D.base D.base_mem = Zw := by
  obtain ⟨dW, hdW⟩ := exists_dimensionFunction_deltaValue_of_isGood D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W)
  have htfae := isPrimeDivisor_tfae_of_isIntegralSpace D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace dW hdW
    (n := n + r) (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hWd]) Zw
  obtain ⟨P, hP⟩ := (htfae.out 1 3).mpr hZwd
  exact ⟨P, IntegralClosedSubspace.ext hP⟩

/-- The generic point of a prime divisor is the ambient generic point of its underlying integral
closed subspace. -/
theorem PrimeDivisor.genericPoint_eq_ambientGenericPoint {T : (BigFppfOver D.site D.base
      D.base_mem)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace D.site D.base D.base_mem T)
    (P : PrimeDivisor D.site D.base D.base_mem T) :
    P.genericPoint D.site D.base D.base_mem T =
      (P.toIntegralClosedSubspace D.site D.base D.base_mem).ambientGenericPoint D.site D.base
        D.base_mem :=
  P.genericPoint_eq_pointsMap_ι D.site D.base D.base_mem hT

/-- Localization maps along equal ring homomorphisms agree. -/
theorem _root_.IsLocalization.map_congr_ringHom {R S P Q : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing P] [CommRing Q] [Algebra P Q] {M : Submonoid R} {T : Submonoid P}
    [IsLocalization M S] [IsLocalization T Q] {g g' : R →+* P} (h : g = g')
    (hy : M ≤ T.comap g) (hy' : M ≤ T.comap g') (x : S) :
    IsLocalization.map Q g hy x = IsLocalization.map Q g' hy' x := by
  subst h
  rfl

/-- The chart diagram `U ×_X W ⟶ V` over `f|_W`, the base change to `W` of a chart diagram
`U ⟶ V` over `f`. -/
abbrev componentChartDiagram (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (d : ChartDiagram D.site D.base D.base_mem X Y f) :
    ChartDiagram D.site D.base D.base_mem W.subspace.toFunctor Y
      (componentMorphism D sY hY f W).hom where
  U := closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace
    d.U
  V := d.V
  g := (ChartDiagram.comp D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)
    (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (closedSubspaceBaseChangeChartDiagram D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U).g d.g
    (closedSubspaceBaseChangeChartDiagram D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U).comm d.comm).g
  comm := (ChartDiagram.comp D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)
    (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (closedSubspaceBaseChangeChartDiagram D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U).g d.g
    (closedSubspaceBaseChangeChartDiagram D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U).comm d.comm).comm

include hflat hintY hL hs in
/-- **The order of `f|_W^*(s)` along a prime divisor of an irreducible component `W`, on the
base-changed chart.** With `q` a point of `U ×_X W` over `u` and over the generic point of the
prime divisor `Z_W` of `W`, the coefficient of `div_{f^*ℒ|_W}(f|_W^*(s))` at `Z_W` is the order
of vanishing of `π(c)` in `𝒪_{U_W, q}`, for `c` the reading of `s` at `u` and `π` the stalk map of
`U ×_X W → U`. -/
theorem componentDivisor_apply_eq_ordTotalFracInt
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X))
    (hWd : deltaDimension D sX W = n + r)
    (Zw : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (hZwd : deltaDimension D (W.subspace.ι ≫ sX) Zw = n + r - 1)
    (d : ChartDiagram D.site D.base D.base_mem X Y f)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (e : (W : SmallEtale D.site D.base D.base_mem Y) → (W ⟶ d.V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V),
      Function.Bijective fun x : chartRing D.site D.base D.base_mem Y hY.1 W ↦ x • e W k)
    (u : chartScheme d.U)
    (q : chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U))
    (hq : closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U q = u)
    (hqZ : chartSchemeToPoints D.site D.base D.base_mem W.subspace.toFunctor
      (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace
        d.U) q = Zw.ambientGenericPoint D.site D.base D.base_mem)
    [IsNoetherianRing ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)]
    [Ring.KrullDimLE 1 ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)] :
    (componentDivisor D sX hX sY hY f r hflat hintY L hL s hs W hW hWd).1 Zw =
      Ring.ordTotalFracInt ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem
          hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)
        (IsLocalization.map (T := ((chartScheme (closedSubspaceBaseChangeChart D.site D.base
            D.base_mem hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)⁰)
          (FractionRing ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem
            hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q))
          (closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1 W d.U u q hq)
          (nonZeroDivisors_le_comap_closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem
            hX.1 (D.isDecentSpace_of_isGood sX hX) W hW d.U u q hq)
          (flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij u))
        (((isUnit_flatChartReading D sY hY f hflat hintY L hL s hs d hV e hecompat hebij
          u)).map _) := by
  subst hq
  obtain ⟨P, rfl⟩ := exists_primeDivisor_of_deltaDimension_component D sX hX r W hWd Zw hZwd
  have hWdec : IsDecentSpace D.site D.base D.base_mem W.subspace.toFunctor :=
    W.isIntegralSpace.isDecentSpace
  have hWN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W)
  have hfm := pullbacksMeromorphicSections_componentMorphism D sX hX sY hY f hflat hintY W hW
  have hreg := isRegularMeromorphicSection_of_ne_zero_of_isGood D sY hY L s hintY hL hs
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
    W.subspace W.isClosedSubspace d.U
  have hUW : IsAffine (chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)) :=
    isAffine_of_isAffineHom (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)
  have hqP : chartSchemeToPoints D.site D.base D.base_mem W.subspace.toFunctor
      (componentChartDiagram D sX hX sY hY f W d).U q =
      P.genericPoint D.site D.base D.base_mem W.subspace.toFunctor :=
    hqZ.trans (P.genericPoint_eq_ambientGenericPoint D W.isClosedSubspace.1).symm
  have hψ : (((BigFppfOver.toScheme D.site D.base D.base_mem).map
        (componentChartDiagram D sX hX sY hY f W d).g).stalkMap q).hom =
      (closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1 W d.U _ q rfl).comp
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).stalkMap
          (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
            W.isClosedSubspace d.U q)).hom := by
    rw [closedSubspaceBaseChangeStalkMap_rfl]
    change ((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U ≫ (BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).stalkMap
        q).hom = _
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hφW : ((chartScheme (componentChartDiagram D sX hX sY hY f W d).V).presheaf.stalk
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map
          (componentChartDiagram D sX hX sY hY f W d).g).base q))⁰ ≤
      ((chartScheme (componentChartDiagram D sX hX sY hY f W d).U).presheaf.stalk q)⁰.comap
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map
          (componentChartDiagram D sX hX sY hY f W d).g).stalkMap q).hom := by
    rw [hψ]
    intro x hx
    exact nonZeroDivisors_le_comap_closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) W hW d.U _ q rfl
      (nonZeroDivisors_le_comap_stalkMap_of_isFlat D f hflat d _ hx)
  have hNq : IsNoetherianRing
      ((chartScheme (componentChartDiagram D sX hX sY hY f W d).U).presheaf.stalk q) :=
    ‹IsNoetherianRing ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)›
  have hKq : Ring.KrullDimLE 1
      ((chartScheme (componentChartDiagram D sX hX sY hY f W d).U).presheaf.stalk q) :=
    ‹Ring.KrullDimLE 1 ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)›
  obtain ⟨hc, heq⟩ := orderOfVanishingSection_pullbackMeromorphicSection_eq_ordTotalFracInt_map
    D.site D.base D.base_mem (X := ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩)
    (Y := ⟨Y, hY.1⟩) hWdec W.isIntegralSpace hWN (componentMorphism D sY hY f W) hfm
    (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY hintY)
    (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) P L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s hreg
    (componentChartDiagram D sX hX sY hY f W d) hUW hV e hecompat hebij q hqP hφW
  rw [componentDivisor, sectionWeilDivisor_apply_toIntegralClosedSubspace]
  refine heq.trans ?_
  have hread : IsLocalization.map (T := ((chartScheme (componentChartDiagram D sX hX sY hY f W
        d).U).presheaf.stalk q)⁰)
      (FractionRing ((chartScheme (componentChartDiagram D sX hX sY hY f W d).U).presheaf.stalk q))
      (((BigFppfOver.toScheme D.site D.base D.base_mem).map
        (componentChartDiagram D sX hX sY hY f W d).g).stalkMap q).hom hφW
      (chartPointMeromorphicMap D.site D.base D.base_mem ⟨Y, hY.1⟩ d.V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨Y, hY.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY
            hintY)
          (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) d.V hV)
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map
          (componentChartDiagram D sX hX sY hY f W d).g).base q)
        (chartRatio D.site D.base D.base_mem Y hY.1 L d.V e hecompat hebij s)) =
      IsLocalization.map (T := ((chartScheme (closedSubspaceBaseChangeChart D.site D.base
          D.base_mem hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)⁰)
        (FractionRing ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem
          hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q))
        (closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1 W d.U
          (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
            W.isClosedSubspace d.U q) q rfl)
        (nonZeroDivisors_le_comap_closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem
          hX.1 (D.isDecentSpace_of_isGood sX hX) W hW d.U
          (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
            W.isClosedSubspace d.U q) q rfl)
        (flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij
          (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
            W.isClosedSubspace d.U q)) :=
    (IsLocalization.map_congr_ringHom hψ _ _ _).trans (IsLocalization.map_map _ _ _).symm
  exact Ring.ordTotalFracInt_congr ((chartScheme (componentChartDiagram D sX hX sY hY f W
    d).U).presheaf.stalk q) _ _ hread


end AlgebraicGeometry.Space

end
