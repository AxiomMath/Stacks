module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatChartSectionOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPrimeAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartFreeGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteAffineChartFree
public import StacksFrontier.RingTheory.Length.FiniteAlgebraGenericRank
public import StacksFrontier.RingTheory.UniqueFactorizationDomain.HeightOneOrders
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentGenericFreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian

/-!
# The pushforward of the divisor of a pulled-back section, on one chart

This file is the chart computation behind Stacks 0EQS. Let `f : X ⟶ Y` be a morphism of
algebraic spaces, `d` a cartesian square of affine étale charts of `f` with finite vertical
morphism `U → V`, `ℒ` an invertible `𝒪_Y`-module free over `V` and `s` a regular meromorphic
section of `ℒ`, and `e` a point of `V`. Writing the chart ratio of `s` over `V` as `a / b` with
`a, b` regular functions on `V`, the chart ratio of `f^*s` over `U` against the inverse image of
the generator is `f^♯a / f^♯b`, and both orders of vanishing read on the charts become orders of
vanishing in localizations of `A = Γ(V, 𝒪_V)` and `B = Γ(U, 𝒪_U)`, where the fibre formula
`Stacks.Length.finsum_primeResidueDegree_mul_ord_eq_mul_ord` applies.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Orders of vanishing at a point of an affine chart, read in a localization of its ring -/

section ChartOrder

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (W : SmallEtale B S hS X) (hW : IsAffine (chartScheme W)) (w : chartScheme W)

/-- The germ at a point of a chart, as a ring homomorphism out of the ring of the chart. -/
abbrev chartGermHom : chartRing B S hS X hX W →+* (chartScheme W).presheaf.stalk w :=
  ((chartScheme W).presheaf.germ ⊤ w trivial).hom

include hW in
/-- The local ring of an affine chart at a point is the localization of the ring of the chart at
the prime of the point. -/
theorem isLocalization_stalk_chartPrimeAt :
    letI := (chartGermHom B S hS hX W w).toAlgebra
    IsLocalization (chartPrimeAt B S hS hX W w).primeCompl ((chartScheme W).presheaf.stalk w) := by
  let : Algebra Γ(chartScheme W, ⊤) ((chartScheme W).presheaf.stalk w) :=
    ((chartScheme W).presheaf.germ ⊤ w trivial).hom.toAlgebra
  have hU : IsAffineOpen (⊤ : (chartScheme W).Opens) := isAffineOpen_top _
  have hw : w ∈ (⊤ : (chartScheme W).Opens) := by simp
  have hloc₀ : IsLocalization.AtPrime ((chartScheme W).presheaf.stalk w)
      (hU.primeIdealOf ⟨w, hw⟩).asIdeal :=
    hU.isLocalization_stalk ⟨w, hw⟩
  have hP : (hU.primeIdealOf ⟨w, hw⟩).asIdeal =
      Ideal.comap ((chartScheme W).presheaf.germ ⊤ w trivial).hom
        (IsLocalRing.maximalIdeal ((chartScheme W).presheaf.stalk w)) :=
    (IsLocalization.AtPrime.under_maximalIdeal ((chartScheme W).presheaf.stalk w) _).symm
  have hSm : (hU.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl =
      (Ideal.comap ((chartScheme W).presheaf.germ ⊤ w trivial).hom
        (IsLocalRing.maximalIdeal ((chartScheme W).presheaf.stalk w))).primeCompl :=
    Submonoid.ext fun a => by simp only [Ideal.mem_primeCompl_iff, hP]
  have : IsLocalization (Ideal.comap ((chartScheme W).presheaf.germ ⊤ w trivial).hom
        (IsLocalRing.maximalIdeal ((chartScheme W).presheaf.stalk w))).primeCompl
      ((chartScheme W).presheaf.stalk w) := by
    rw [← hSm]
    exact hloc₀
  exact this

include hW in
/-- The order of vanishing at a point of an affine chart is the order of vanishing in the
localization of the ring of the chart at the prime of the point. -/
theorem ord_germ_eq_ord_localization (a : chartRing B S hS X hX W) :
    Ring.ord ((chartScheme W).presheaf.stalk w) (chartGermHom B S hS hX W w a) =
      Ring.ord (Localization.AtPrime (chartPrimeAt B S hS hX W w))
        (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS hX W w)) a) := by
  let := (chartGermHom B S hS hX W w).toAlgebra
  have := isLocalization_stalk_chartPrimeAt B S hS hX W hW w
  let e := IsLocalization.algEquiv (chartPrimeAt B S hS hX W w).primeCompl
    (Localization.AtPrime (chartPrimeAt B S hS hX W w)) ((chartScheme W).presheaf.stalk w)
  have he : e (algebraMap _ _ a) = chartGermHom B S hS hX W w a := e.commutes a
  rw [← he]
  exact Stacks.RingTheory.HeightOneOrders.ord_ringEquiv e.toRingEquiv _

end ChartOrder

section ChartReading

attribute [local instance] chartMeromorphicFunctionAlgebra

variable (Y : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Y.1) (hW : IsAffine (chartScheme W))
    (hK : IsFractionRing ((structurePresheaf B S hS Y.1).obj (op W))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W)))
    (w : chartScheme W)
    [IsNoetherianRing ((chartScheme W).presheaf.stalk w)]
    [Ring.KrullDimLE 1 ((chartScheme W).presheaf.stalk w)]

/-- The order of vanishing of a fraction of regular functions read at a point of an affine chart:
for `a, b` nonzerodivisors of `Γ(W, 𝒪_W)`, the order of vanishing at `w` of the reading of `a / b`
is the difference of the orders of vanishing of `a` and `b` in the localization of `Γ(W, 𝒪_W)` at
the prime of `w`. -/
theorem ordTotalFracInt_chartPointMeromorphicMap_mul_eq (a b : chartRing B S hS Y.1 Y.2 W)
    (ha : a ∈ (chartRing B S hS Y.1 Y.2 W)⁰) (hb : b ∈ (chartRing B S hS Y.1 Y.2 W)⁰)
    (c : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W))
    (hc : c * algebraMap ((structurePresheaf B S hS Y.1).obj (op W)) _ b =
      algebraMap ((structurePresheaf B S hS Y.1).obj (op W)) _ a)
    (hu : IsUnit (chartPointMeromorphicMap B S hS Y W hW hK w c)) :
    Ring.ordTotalFracInt ((chartScheme W).presheaf.stalk w)
        (chartPointMeromorphicMap B S hS Y W hW hK w c) hu =
      ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS Y.2 W w))
          (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS Y.2 W w)) a)).toNat : ℤ) -
        ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS Y.2 W w))
          (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS Y.2 W w)) b)).toNat : ℤ) := by
  have := hW
  have hga : chartGermHom B S hS Y.2 W w a ∈ ((chartScheme W).presheaf.stalk w)⁰ :=
    (chartScheme W).nonZeroDivisors_le_comap_germ_top w ha
  have hgb : chartGermHom B S hS Y.2 W w b ∈ ((chartScheme W).presheaf.stalk w)⁰ :=
    (chartScheme W).nonZeroDivisors_le_comap_germ_top w hb
  have hua : IsUnit (algebraMap ((chartScheme W).presheaf.stalk w)
      (FractionRing ((chartScheme W).presheaf.stalk w)) (chartGermHom B S hS Y.2 W w a)) :=
    IsLocalization.map_units _ ⟨_, hga⟩
  have hub : IsUnit (algebraMap ((chartScheme W).presheaf.stalk w)
      (FractionRing ((chartScheme W).presheaf.stalk w)) (chartGermHom B S hS Y.2 W w b)) :=
    IsLocalization.map_units _ ⟨_, hgb⟩
  have hread : chartPointMeromorphicMap B S hS Y W hW hK w c *
      algebraMap ((chartScheme W).presheaf.stalk w)
        (FractionRing ((chartScheme W).presheaf.stalk w)) (chartGermHom B S hS Y.2 W w b) =
      algebraMap ((chartScheme W).presheaf.stalk w)
        (FractionRing ((chartScheme W).presheaf.stalk w)) (chartGermHom B S hS Y.2 W w a) := by
    rw [show chartGermHom B S hS Y.2 W w b = ((chartScheme W).presheaf.germ ⊤ w trivial).hom b
        from rfl, show chartGermHom B S hS Y.2 W w a =
          ((chartScheme W).presheaf.germ ⊤ w trivial).hom a from rfl,
      ← chartPointMeromorphicMap_algebraMap B S hS Y W hW hK w b,
      ← chartPointMeromorphicMap_algebraMap B S hS Y W hW hK w a, ← map_mul, hc]
  have key := (Ring.ordTotalFracInt_congr ((chartScheme W).presheaf.stalk w)
    (K := FractionRing ((chartScheme W).presheaf.stalk w)) (hu.mul hub) hua hread).symm.trans
    (Ring.ordTotalFracInt_mul ((chartScheme W).presheaf.stalk w) _ _ hu hub)
  rw [Ring.ordTotalFracInt_algebraMap ((chartScheme W).presheaf.stalk w) _ hga,
    Ring.ordTotalFracInt_algebraMap ((chartScheme W).presheaf.stalk w) _ hgb,
    ord_germ_eq_ord_localization B S hS Y.2 W hW w a,
    ord_germ_eq_ord_localization B S hS Y.2 W hW w b] at key
  omega

end ChartReading


/-! ### The order of vanishing of a section, read on a trivializing affine chart -/

section SectionOrderChart

attribute [local instance] chartMeromorphicFunctionAlgebra

variable (Z : AlgebraicSpaces B S hS) (hdec : IsDecentSpace B S hS Z.1)
    (hInt : IsIntegralSpace B S hS Z.1)
    (hN : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))

include hInt hN in
/-- The order of vanishing of a meromorphic section along a prime divisor, on an affine chart
trivializing the module, as a difference of lengths: if over the affine étale chart `V` the chart
ratio of `t` is `a / b` for nonzerodivisors `a, b` of `Γ(V, 𝒪_V)`, and `v` is a point of `V` over
the generic point of the prime divisor `P`, then `ord_{P, ℳ}(t)` is the difference of the orders
of vanishing of `a` and `b` in the localization of `Γ(V, 𝒪_V)` at the prime of `v`. -/
theorem orderOfVanishingSection_eq_ord_sub_ord_of_chart (P : PrimeDivisor B S hS Z.1)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (hM : IsInvertibleModule (B := B) Z M)
    (t : MeromorphicSection.{u, u} B S hS Z.1 Z.2 M)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS Z.1 Z.2 M t)
    (V : SmallEtale B S hS Z.1) (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS Z.1) → (W ⟶ V) → M.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS Z.1) (k : W ⟶ V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS Z.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS Z.1 Z.2 W ↦ r • e W k)
    (v : chartScheme V) (hv : chartSchemeToPoints B S hS Z.1 V v = P.genericPoint B S hS Z.1)
    (a b : chartRing B S hS Z.1 Z.2 V) (ha : a ∈ (chartRing B S hS Z.1 Z.2 V)⁰)
    (hb : b ∈ (chartRing B S hS Z.1 Z.2 V)⁰)
    (c : (meromorphicFunctionSheaf B S hS Z.1 Z.2).obj.obj (op V))
    (hct : chartRatio B S hS Z.1 Z.2 M V e hecompat hebij t = c)
    (hc : c * algebraMap ((structurePresheaf B S hS Z.1).obj (op V)) _ b =
      algebraMap ((structurePresheaf B S hS Z.1).obj (op V)) _ a) :
    haveI : ∀ W : PrimeDivisor B S hS Z.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Z.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Z.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS Z.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Z.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Z.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS Z.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Z.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Z.2 hdec hInt hN
    orderOfVanishingSection.{u, u} B S hS Z.2 hdec P M t
        (P.canonicalLocalRatio B S hS Z.2 hdec M hM hInt hN) =
      ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS Z.2 V v))
          (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS Z.2 V v)) a)).toNat : ℤ) -
        ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS Z.2 V v))
          (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS Z.2 V v)) b)).toNat : ℤ) := by
  have hwa := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Z.2 hInt
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Z.1 Z.2 hN
  have : IsLocallyNoetherian (chartScheme V) := isLocallyNoetherian_chartScheme B S hS (X := Z) hN V
  have : Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v) :=
    P.krullDimLE_chartStalk B S hS Z.2 hdec V v hv
  have hcu := IsUnit.map
    (chartPointMeromorphicMap B S hS Z V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS Z hwa hfin V hV) v)
    (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS Z hwa hfin M V hV e hecompat hebij
      t ht)
  have hcu' : IsUnit (chartPointMeromorphicMap B S hS Z V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS Z hwa hfin V hV) v c) := by
    rw [← hct]
    exact hcu
  rw [P.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt B S hS hdec hInt hN hwa hfin
    M hM t ht V hV e hecompat hebij v hv hcu,
    Ring.ordTotalFracInt_congr _ hcu hcu' (congrArg _ hct)]
  exact ordTotalFracInt_chartPointMeromorphicMap_mul_eq B S hS Z V hV
    (isFractionRing_meromorphicFunctionSheaf_obj B S hS Z hwa hfin V hV) v a b ha hb c hc hcu'

end SectionOrderChart

/-! ### Generic points of charts and minimal primes of their rings -/

section ChartGeneric

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- On an affine chart, the prime of a point is minimal exactly when the point is a generic
point of an irreducible component of the chart. -/
theorem chartPrimeAt_mem_minimalPrimes_iff (W : SmallEtale B S hS X)
    (hW : IsAffine (chartScheme W)) (w : chartScheme W) :
    chartPrimeAt B S hS hX W w ∈ minimalPrimes (chartRing B S hS X hX W) ↔
      w ∈ genericPoints (chartScheme W) := by
  let := (chartGermHom B S hS hX W w).toAlgebra
  have : IsLocalization.AtPrime ((chartScheme W).presheaf.stalk w) (chartPrimeAt B S hS hX W w) :=
    isLocalization_stalk_chartPrimeAt B S hS hX W hW w
  rw [← ringKrullDim_stalk_eq_zero_iff_mem_genericPoints,
    IsLocalization.AtPrime.ringKrullDim_eq_height (chartPrimeAt B S hS hX W w)
      ((chartScheme W).presheaf.stalk w), ← Ideal.height_eq_zero_iff]
  exact ⟨fun h => by rw [h]; rfl, fun h => by exact_mod_cast h⟩

include hX in
/-- A point of an étale chart lies over a point of codimension zero exactly when it is a generic
point of an irreducible component of the chart (Stacks 0BAQ). -/
theorem localRingDimension_chartSchemeToPoints_eq_zero_iff (W : SmallEtale B S hS X)
    (w : chartScheme W) :
    localRingDimension B S hS (chartSchemeToPoints B S hS X W w) = 0 ↔
      w ∈ genericPoints (chartScheme W) := by
  have hEt : IsEtale B S hS W.obj.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).mpr W.property
  refine ⟨fun h => (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX _).mp h
    W.obj.left W.obj.hom w hEt (chartPoint_chartSchemeToPoints B S hS (X := ⟨X, hX⟩) W w),
    fun h => ?_⟩
  exact (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).mpr
    ⟨W.obj.left, W.obj.hom, w, hEt, chartPoint_chartSchemeToPoints B S hS (X := ⟨X, hX⟩) W w, h⟩

/-- On an integral algebraic space, a point of an étale chart lies over the generic point exactly
when it is a generic point of an irreducible component of the chart. -/
theorem chartSchemeToPoints_eq_genericPoint_iff (hInt : IsIntegralSpace B S hS X)
    (W : SmallEtale B S hS X) (w : chartScheme W) :
    chartSchemeToPoints B S hS X W w = genericPoint B S hS hX hInt ↔
      w ∈ genericPoints (chartScheme W) := by
  rw [← localRingDimension_chartSchemeToPoints_eq_zero_iff B S hS hX W w,
    ← mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hInt.2.1]
  let : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hInt.2.1
  let : IrreducibleSpace (points B S hS X) := hInt.2.2
  let : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hInt.2.1
  rw [genericPoints_eq_singleton]
  rfl

omit hX in
/-- The ring of an étale chart of an integral algebraic space is reduced. -/
theorem isReduced_chartRing_of_isIntegralSpace (Z : AlgebraicSpaces B S hS)
    (hInt : IsIntegralSpace B S hS Z.1) (W : SmallEtale B S hS Z.1) :
    _root_.IsReduced (chartRing B S hS Z.1 Z.2 W) := by
  have hred : IsReduced (chartScheme W) :=
    (exists_atlas_iff_forall_etale B S hS Z.1 (fun V : Scheme.{u} => IsReduced V) Z.2).mp
      (IsIntegralSpace.hasEtaleLocalProperty_isReduced B S hS Z.1 hInt) W.obj.left W.obj.hom
      W.property
  exact @IsReduced.component_reduced _ hred ⊤

omit hX in
/-- Minimal primes of the chart of `X` lie over minimal primes of the chart of `Y`, along a chart
diagram over a morphism of integral algebraic spaces carrying the generic point to the generic
point. -/
theorem comap_mem_minimalPrimes_chartDiagramRestrict {Z Y : AlgebraicSpaces B S hS}
    (hZint : IsIntegralSpace B S hS Z.1) (hYint : IsIntegralSpace B S hS Y.1) (f : Z ⟶ Y)
    (hgen : pointsMap B S hS Z.1 f.hom (genericPoint B S hS Z.2 hZint) =
      genericPoint B S hS Y.2 hYint)
    (d : ChartDiagram B S hS Z.1 Y.1 f.hom) (hU : IsAffine (chartScheme d.U))
    (hV : IsAffine (chartScheme d.V)) :
    ∀ Q ∈ minimalPrimes (chartRing B S hS Z.1 Z.2 d.U),
      Q.comap (chartDiagramRestrict B S hS f d) ∈ minimalPrimes (chartRing B S hS Y.1 Y.2 d.V) := by
  intro Q hQ
  have : Q.IsPrime := hQ.1.1
  obtain ⟨w, hw⟩ := (bijective_chartPrimeAt B S hS Z.2 d.U hU).2 ⟨Q, inferInstance⟩
  have hQw : chartPrimeAt B S hS Z.2 d.U w = Q := congrArg PrimeSpectrum.asIdeal hw
  subst hQw
  rw [comap_chartPrimeAt B S hS f d w, chartPrimeAt_mem_minimalPrimes_iff B S hS Y.2 d.V hV,
    ← chartSchemeToPoints_eq_genericPoint_iff B S hS Y.2 hYint,
    chartSchemeToPoints_map_chartDiagram B S hS d w,
    (chartSchemeToPoints_eq_genericPoint_iff B S hS Z.2 hZint d.U w).mpr
      ((chartPrimeAt_mem_minimalPrimes_iff B S hS Z.2 d.U hU w).mp hQ), hgen]

/-- The localization of the ring of an affine chart at the prime of a point has the Krull
dimension of the local ring of the chart at that point. -/
theorem krullDimLE_localization_chartPrimeAt (W : SmallEtale B S hS X)
    (hW : IsAffine (chartScheme W)) (w : chartScheme W) (n : ℕ)
    [Ring.KrullDimLE n ((chartScheme W).presheaf.stalk w)] :
    Ring.KrullDimLE n (Localization.AtPrime (chartPrimeAt B S hS hX W w)) := by
  let := (chartGermHom B S hS hX W w).toAlgebra
  have := isLocalization_stalk_chartPrimeAt B S hS hX W hW w
  rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv
    (chartPrimeAt B S hS hX W w).primeCompl (Localization.AtPrime (chartPrimeAt B S hS hX W w))
    ((chartScheme W).presheaf.stalk w)).toRingEquiv]
  exact Ring.krullDimLE_iff.mp ‹_›

omit hX in
/-- Pullbacks of meromorphic functions are defined along a morphism of integral algebraic spaces
carrying the generic point to the generic point (Stacks 0EN9, part (1)). -/
theorem pullbacksMeromorphicSections_of_genericPoint {Z Y : AlgebraicSpaces B S hS}
    (hZint : IsIntegralSpace B S hS Z.1) (hYint : IsIntegralSpace B S hS Y.1) (f : Z.1 ⟶ Y.1)
    (hgen : pointsMap B S hS Z.1 f (genericPoint B S hS Z.2 hZint) =
      genericPoint B S hS Y.2 hYint) :
    PullbacksMeromorphicSections B S hS f := by
  refine pullbacksMeromorphicSections_of_mapsTo_codimensionZero B S hS f fun x hx => ?_
  have h0 := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Z.2 hZint x hx
  let : QuasiSober (points B S hS Z.1) := quasiSober_points_of_isDecentSpace B S hS Z.2 hZint.2.1
  let : IrreducibleSpace (points B S hS Z.1) := hZint.2.2
  let : T0Space (points B S hS Z.1) := t0Space_points_of_isDecentSpace B S hS Z.2 hZint.2.1
  let : QuasiSober (points B S hS Y.1) := quasiSober_points_of_isDecentSpace B S hS Y.2 hYint.2.1
  let : IrreducibleSpace (points B S hS Y.1) := hYint.2.2
  let : T0Space (points B S hS Y.1) := t0Space_points_of_isDecentSpace B S hS Y.2 hYint.2.1
  have hx : x = genericPoint B S hS Z.2 hZint := by
    have := (mem_genericPoints_iff_localRingDimension_eq_zero B S hS Z.2 hZint.2.1 x).mpr h0
    rwa [genericPoints_eq_singleton] at this
  rw [hx, hgen, ← mem_genericPoints_iff_localRingDimension_eq_zero B S hS Y.2 hYint.2.1,
    genericPoints_eq_singleton]
  rfl

end ChartGeneric

/-! ### The chart identity -/

section ChartIdentity

attribute [local instance] chartMeromorphicFunctionAlgebra

/-- A finite sum in `ℕ∞` of finite products, read in `ℤ`. -/
theorem finsum_mem_natCast_mul_toNat_eq {ι : Type*} {s : Set ι} (hs : s.Finite) (n : ι → ℕ)
    (m : ι → ℕ∞) {K : ℕ∞} (hK : K ≠ ⊤) (h : ∑ᶠ i ∈ s, (n i : ℕ∞) * m i = K) :
    ∑ᶠ i ∈ s, (n i : ℤ) * ((m i).toNat : ℤ) = (K.toNat : ℤ) := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hs] at h ⊢
  have hterm : ∀ i ∈ hs.toFinset, (n i : ℕ∞) * m i ≠ ⊤ := fun i hi =>
    ne_top_of_le_ne_top (h ▸ hK) (Finset.single_le_sum (f := fun i => (n i : ℕ∞) * m i)
      (fun _ _ => zero_le) hi)
  rw [← h, ENat.toNat_sum hterm, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]

/-- A ring map into a reduced ring whose contraction preserves minimal primes preserves
nonzerodivisors. -/
private theorem map_mem_nonZeroDivisors_of_comap_mem_minimalPrimes {R T : Type*} [CommRing R]
    [CommRing T] [_root_.IsReduced T] (φ : R →+* T)
    (hmin : ∀ Q ∈ minimalPrimes T, Q.comap φ ∈ minimalPrimes R) {x : R} (hx : x ∈ R⁰) :
    φ x ∈ T⁰ :=
  Stacks.Length.mem_nonZeroDivisors_of_forall_notMem_minimalPrimes fun Q hQ hxQ =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (show x ∈ Q.comap φ from hxQ) (hmin Q hQ) hx

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfm : PullbacksMeromorphicSections B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (hU : IsAffine (chartScheme d.U))
    (hV : IsAffine (chartScheme d.V))
    (hKU : IsFractionRing ((structurePresheaf B S hS X.1).obj (op d.U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op d.U)))
    (hKV : IsFractionRing ((structurePresheaf B S hS Y.1).obj (op d.V))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)))

include hU hV in
/-- The chart identity of Stacks 0EQS, in the rings of the charts. Let `d` be a square of
affine étale charts over `f` with finite vertical morphism `g : U → V`, and `e` a point of `V`.
Write `A = Γ(V, 𝒪_V)`, `B = Γ(U, 𝒪_U)`, `φ : A → B` and `𝔭 ⊂ A` for the prime of `e`, and
assume `B` reduced with its minimal primes over minimal primes of `A`, `A_𝔭` reduced of
dimension at most one, and `B` of generic rank `deg` over `A` at the minimal primes inside `𝔭`.
For nonzerodivisors `a, b` of `A`,

`∑_{g(w) = e} [κ(w) : κ(e)] · (ord_{B_w}(φ a) - ord_{B_w}(φ b)) =
  deg · (ord_{A_𝔭}(a) - ord_{A_𝔭}(b))`. -/
theorem finsum_primeResidueDegree_mul_ord_sub_eq
    (hfinite : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map d.g))
    [IsNoetherianRing (chartRing B S hS Y.1 Y.2 d.V)]
    (e : chartScheme d.V)
    [_root_.IsReduced (chartRing B S hS X.1 X.2 d.U)]
    (hmin : ∀ Q ∈ minimalPrimes (chartRing B S hS X.1 X.2 d.U),
      Q.comap (chartDiagramRestrict B S hS f d) ∈ minimalPrimes (chartRing B S hS Y.1 Y.2 d.V))
    [_root_.IsReduced (Localization.AtPrime (chartPrimeAt B S hS Y.2 d.V e))]
    [Ring.KrullDimLE 1 (Localization.AtPrime (chartPrimeAt B S hS Y.2 d.V e))]
    (deg : ℕ)
    (hrank : letI := (chartDiagramRestrict B S hS f d).toAlgebra
      ∀ P : PrimeSpectrum (chartRing B S hS Y.1 Y.2 d.V), P.asIdeal ∈ minimalPrimes _ →
        P.asIdeal ≤ chartPrimeAt B S hS Y.2 d.V e →
        Module.length (Localization.AtPrime P.asIdeal)
            (LocalizedModule P.asIdeal.primeCompl (chartRing B S hS X.1 X.2 d.U)) =
          deg * Module.length (Localization.AtPrime P.asIdeal)
            (LocalizedModule P.asIdeal.primeCompl (chartRing B S hS Y.1 Y.2 d.V)))
    (hfinw : {w : chartScheme d.U | ((BigFppfOver.toScheme B S hS).map d.g).base w = e}.Finite)
    (a b : chartRing B S hS Y.1 Y.2 d.V) (ha : a ∈ (chartRing B S hS Y.1 Y.2 d.V)⁰)
    (hb : b ∈ (chartRing B S hS Y.1 Y.2 d.V)⁰) :
    ∑ᶠ w ∈ {w : chartScheme d.U | ((BigFppfOver.toScheme B S hS).map d.g).base w = e},
        (Stacks.Length.primeResidueDegree (chartDiagramRestrict B S hS f d)
            (chartPrimeAt B S hS Y.2 d.V e) (chartPrimeAt B S hS X.2 d.U w) : ℤ) *
          (((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w))
              (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w))
                (chartDiagramRestrict B S hS f d a))).toNat : ℤ) -
            ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w))
              (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w))
                (chartDiagramRestrict B S hS f d b))).toNat : ℤ)) =
      (deg : ℤ) * (((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS Y.2 d.V e))
            (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS Y.2 d.V e)) a)).toNat : ℤ) -
          ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS Y.2 d.V e))
            (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS Y.2 d.V e))
              b)).toNat : ℤ)) := by
  classical
  set r := (BigFppfOver.toScheme B S hS).map d.g
  set φ := chartDiagramRestrict B S hS f d
  let : Algebra (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U) := φ.toAlgebra
  have : IsAffine (chartScheme d.V) := hV
  have : IsAffine (chartScheme d.U) := hU
  have : _root_.AlgebraicGeometry.IsFinite r := hfinite
  have : Module.Finite (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U) :=
    (Scheme.Hom.finite_appTop r : φ.Finite)
  set p := chartPrimeAt B S hS Y.2 d.V e
  have hnzdp : ∀ x ∈ (chartRing B S hS Y.1 Y.2 d.V)⁰,
      algebraMap _ (Localization.AtPrime p) x ∈ (Localization.AtPrime p)⁰ :=
    fun x hx => map_mem_nonZeroDivisors_of_comap_mem_minimalPrimes _
      (fun _ hP => Stacks.Length.comap_mem_minimalPrimes_of_isLocalization p.primeCompl
        (Localization.AtPrime p) hP) hx
  simp only [mul_sub]
  have hbij := bijective_chartPrimeAt B S hS X.2 d.U hU
  have hbijV := bijective_chartPrimeAt B S hS Y.2 d.V hV
  have hcomap : ∀ w, (chartPrimeAt B S hS X.2 d.U w).comap φ =
      chartPrimeAt B S hS Y.2 d.V (r.base w) := fun w => comap_chartPrimeAt B S hS f d w
  let Qof : chartScheme d.U → PrimeSpectrum (chartRing B S hS X.1 X.2 d.U) := fun w =>
    ⟨chartPrimeAt B S hS X.2 d.U w, inferInstance⟩
  have hbijOn : Set.BijOn Qof {w | r.base w = e}
      {Q : PrimeSpectrum (chartRing B S hS X.1 X.2 d.U) |
        Q.asIdeal.comap (algebraMap (chartRing B S hS Y.1 Y.2 d.V) _) = p} := by
    refine ⟨fun w hw => ?_, hbij.1.injOn, fun Q hQ => ?_⟩
    · change (chartPrimeAt B S hS X.2 d.U w).comap φ = p
      rw [hcomap w, show r.base w = e from hw]
    · obtain ⟨w, rfl⟩ := hbij.2 Q
      exact ⟨w, hbijV.1 (PrimeSpectrum.ext ((hcomap w).symm.trans hQ)), rfl⟩
  have hfinQ : {Q : PrimeSpectrum (chartRing B S hS X.1 X.2 d.U) |
      Q.asIdeal.comap (algebraMap (chartRing B S hS Y.1 Y.2 d.V) _) = p}.Finite := by
    rw [← hbijOn.image_eq]
    exact hfinw.image _
  have key : ∀ x ∈ (chartRing B S hS Y.1 Y.2 d.V)⁰,
      ∑ᶠ w ∈ {w : chartScheme d.U | r.base w = e},
          (Stacks.Length.primeResidueDegree φ p (chartPrimeAt B S hS X.2 d.U w) : ℤ) *
            ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w))
              (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w)) (φ x))).toNat
                : ℤ) =
        (deg : ℤ) * ((Ring.ord (Localization.AtPrime p)
          (algebraMap _ (Localization.AtPrime p) x)).toNat : ℤ) := by
    intro x hx
    have hA3 := Stacks.Length.finsum_primeResidueDegree_mul_ord_eq_mul_ord p hmin deg hrank
      (hnzdp x hx)
    have hconv := finsum_mem_eq_of_bijOn (s := {w : chartScheme d.U | r.base w = e})
      (g := fun Q : PrimeSpectrum (chartRing B S hS X.1 X.2 d.U) =>
        (Stacks.Length.primeResidueDegree (algebraMap (chartRing B S hS Y.1 Y.2 d.V) _) p
          Q.asIdeal : ℤ) * ((Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap _ (Localization.AtPrime Q.asIdeal)
              (algebraMap (chartRing B S hS Y.1 Y.2 d.V) _ x))).toNat : ℤ))
      (f := fun w : chartScheme d.U =>
        (Stacks.Length.primeResidueDegree φ p (chartPrimeAt B S hS X.2 d.U w) : ℤ) *
            ((Ring.ord (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w))
              (algebraMap _ (Localization.AtPrime (chartPrimeAt B S hS X.2 d.U w)) (φ x))).toNat
                : ℤ)) Qof hbijOn (fun w _ => rfl)
    refine hconv.trans ?_
    have hK : (deg : ℕ∞) * Ring.ord (Localization.AtPrime p)
        (algebraMap _ (Localization.AtPrime p) x) ≠ ⊤ :=
      WithTop.mul_ne_top (ENat.natCast_ne_top deg) (Ring.ord_ne_top (hnzdp x hx))
    rw [finsum_mem_natCast_mul_toNat_eq hfinQ _ _ hK hA3, ENat.toNat_mul, ENat.toNat_natCast,
      Nat.cast_mul]
  refine (finsum_mem_sub_distrib _ _ hfinw).trans ?_
  rw [key a ha, key b hb]


omit hU hV in
/-- An element of a ring whose image in a total ring of fractions is a unit is a nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_isUnit_algebraMap {R K : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [IsFractionRing R K] {r : R} (h : IsUnit (algebraMap R K r)) : r ∈ R⁰ := by
  have key : ∀ y : R, y * r = 0 → y = 0 := fun y hy => by
    have h1 : algebraMap R K y * algebraMap R K r = 0 := by rw [← map_mul, hy, map_zero]
    exact IsFractionRing.injective R K ((h.mul_left_eq_zero).mp h1 |>.trans (map_zero _).symm)
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun y hy => key y (by rw [mul_comm]; exact hy), fun y hy => key y hy⟩

omit hU hV in
/-- Along a chart diagram whose minimal primes lie over minimal primes, with reduced source ring,
nonzerodivisors are carried to nonzerodivisors. -/
theorem chartDiagramRestrict_mem_nonZeroDivisors
    [_root_.IsReduced (chartRing B S hS X.1 X.2 d.U)]
    (hmin : ∀ Q ∈ minimalPrimes (chartRing B S hS X.1 X.2 d.U),
      Q.comap (chartDiagramRestrict B S hS f d) ∈ minimalPrimes (chartRing B S hS Y.1 Y.2 d.V))
    {x : chartRing B S hS Y.1 Y.2 d.V} (hx : x ∈ (chartRing B S hS Y.1 Y.2 d.V)⁰) :
    chartDiagramRestrict B S hS f d x ∈ (chartRing B S hS X.1 X.2 d.U)⁰ :=
  map_mem_nonZeroDivisors_of_comap_mem_minimalPrimes _ hmin hx

omit hU hV in
/-- The chart pullback of a fraction `a / b` is `f^♯a / f^♯b`. -/
theorem chartMeromorphicFunctionPullback_mul_algebraMap
    (c : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V))
    (a b : chartRing B S hS Y.1 Y.2 d.V)
    (hc : c * algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V)) _ b =
      algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V)) _ a) :
    chartMeromorphicFunctionPullback B S hS f hfm d c *
        algebraMap ((structurePresheaf B S hS X.1).obj (op d.U)) _
          (chartDiagramRestrict B S hS f d b) =
      algebraMap ((structurePresheaf B S hS X.1).obj (op d.U)) _
        (chartDiagramRestrict B S hS f d a) := by
  have hpull : ∀ x, chartMeromorphicFunctionPullback B S hS f hfm d
      (algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V)) _ x) =
      algebraMap ((structurePresheaf B S hS X.1).obj (op d.U)) _
        (chartDiagramRestrict B S hS f d x) := fun x =>
    RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS f hfm d) x
  have h := congrArg (chartMeromorphicFunctionPullback B S hS f hfm d) hc
  rw [map_mul, hpull b, hpull a] at h
  exact h

include hU hV in
/-- Stacks 0EQS on one chart, for a pulled-back section. Let `f : X ⟶ Y` be a morphism of
decent, locally Noetherian, integral algebraic spaces along which pullbacks of meromorphic
functions are defined, `ℒ` an invertible `𝒪_Y`-module free over the chart `V` of the square `d`,
`s` a regular meromorphic section of `ℒ`, `W` a prime divisor of `Y` and `e` a point of `V` over
its generic point. Let `α` assign to each point `w` of `U` over `e` the order of vanishing of
`f^*s` along a prime divisor of `X` with generic point the image of `w`. Under the ring
hypotheses of `AlgebraicGeometry.Space.finsum_primeResidueDegree_mul_ord_sub_eq`,

`∑_{g(w) = e} [κ(w) : κ(e)] · α(w) = deg · ord_{W, ℒ}(s)`. -/
theorem finsum_primeResidueDegree_mul_orderOfVanishingSection_eq
    (hXdec : IsDecentSpace B S hS X.1) (hYdec : IsDecentSpace B S hS Y.1)
    (hXint : IsIntegralSpace B S hS X.1) (hYint : IsIntegralSpace B S hS Y.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hYN : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hfinite : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map d.g))
    (L : Modules.{u, u} B S hS Y.1 Y.2) (hL : IsInvertibleModule (B := B) Y L)
    (σ : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)
    (hσ : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L σ)
    (eM : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → L.val.obj (op W))
    (hMcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (eM W k) = eM W' (g ≫ k))
    (hMfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k)
    (WY : PrimeDivisor B S hS Y.1) (e : chartScheme d.V)
    (he : chartSchemeToPoints B S hS Y.1 d.V e = WY.genericPoint B S hS Y.1)
    (hmin : ∀ Q ∈ minimalPrimes (chartRing B S hS X.1 X.2 d.U),
      Q.comap (chartDiagramRestrict B S hS f d) ∈ minimalPrimes (chartRing B S hS Y.1 Y.2 d.V))
    (deg : ℕ)
    (hrank : letI := (chartDiagramRestrict B S hS f d).toAlgebra
      ∀ P : PrimeSpectrum (chartRing B S hS Y.1 Y.2 d.V), P.asIdeal ∈ minimalPrimes _ →
        P.asIdeal ≤ chartPrimeAt B S hS Y.2 d.V e →
        Module.length (Localization.AtPrime P.asIdeal)
            (LocalizedModule P.asIdeal.primeCompl (chartRing B S hS X.1 X.2 d.U)) =
          deg * Module.length (Localization.AtPrime P.asIdeal)
            (LocalizedModule P.asIdeal.primeCompl (chartRing B S hS Y.1 Y.2 d.V)))
    (hfinw : {w : chartScheme d.U | ((BigFppfOver.toScheme B S hS).map d.g).base w = e}.Finite)
    (α : chartScheme d.U → ℤ)
    (hα : ∀ w, ((BigFppfOver.toScheme B S hS).map d.g).base w = e →
      ∃ P : PrimeDivisor B S hS X.1,
        P.genericPoint B S hS X.1 = chartSchemeToPoints B S hS X.1 d.U w ∧
        haveI : ∀ W : PrimeDivisor B S hS X.1,
            Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
          W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
        haveI : ∀ W : PrimeDivisor B S hS X.1,
            IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
          W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
        haveI : ∀ W : PrimeDivisor B S hS X.1,
            Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
          W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
        α w = orderOfVanishingSection.{u, u} B S hS X.2 hXdec P ((modulePullback B S hS f).obj L)
          (pullbackMeromorphicSection B S hS f L hfm σ)
          (P.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS f).obj L)
            (modulePullbackInvertible f L hL) hXint hXN)) :
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    ∑ᶠ w ∈ {w : chartScheme d.U | ((BigFppfOver.toScheme B S hS).map d.g).base w = e},
        (Stacks.Length.primeResidueDegree (chartDiagramRestrict B S hS f d)
            (chartPrimeAt B S hS Y.2 d.V e) (chartPrimeAt B S hS X.2 d.U w) : ℤ) * α w =
      (deg : ℤ) * orderOfVanishingSection.{u, u} B S hS Y.2 hYdec WY L σ
        (WY.canonicalLocalRatio B S hS Y.2 hYdec L hL hYint hYN) := by
  classical
  have hwaY := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Y.2 hYint
  have hfinY := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y.1 Y.2 hYN
  have hKV := isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY d.V hV
  set c : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V) :=
    chartRatio B S hS Y.1 Y.2 L d.V eM hMcompat hMfree σ
  have hcu : IsUnit c :=
    isUnit_chartRatio_of_isRegularMeromorphicSection B S hS Y hwaY hfinY L d.V hV eM hMcompat
      hMfree σ hσ
  obtain ⟨⟨a₀, b₀⟩, hab₀⟩ := IsLocalization.surj ((structurePresheaf B S hS Y.1).obj (op d.V))⁰ c
  simp only at hab₀
  obtain ⟨a, rfl⟩ : ∃ a : chartRing B S hS Y.1 Y.2 d.V, a = a₀ := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : chartRing B S hS Y.1 Y.2 d.V,
      b = (b₀ : (structurePresheaf B S hS Y.1).obj (op d.V)) := ⟨_, rfl⟩
  have hb : b ∈ (chartRing B S hS Y.1 Y.2 d.V)⁰ := hbb ▸ b₀.2
  have hab : c * algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V)) _ b =
      algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V)) _ a := by
    rw [hbb]
    exact hab₀
  have ha : a ∈ (chartRing B S hS Y.1 Y.2 d.V)⁰ := by
    have hu : IsUnit (algebraMap ((structurePresheaf B S hS Y.1).obj (op d.V))
        ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) a) := by
      rw [← hab, hbb]
      exact hcu.mul (IsLocalization.map_units _ b₀)
    exact mem_nonZeroDivisors_of_isUnit_algebraMap
      (R := (structurePresheaf B S hS Y.1).obj (op d.V))
      (K := (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op d.V)) hu
  have hY := orderOfVanishingSection_eq_ord_sub_ord_of_chart B S hS Y hYdec hYint hYN WY L hL σ hσ
    d.V hV eM hMcompat hMfree e he a b ha hb c rfl hab
  have : IsNoetherianRing (chartRing B S hS Y.1 Y.2 d.V) :=
    isNoetherianRing_chartRing_of_isAffine (hX := Y.2) hYN hV
  have : _root_.IsReduced (chartRing B S hS X.1 X.2 d.U) :=
    isReduced_chartRing_of_isIntegralSpace B S hS X hXint d.U
  have : _root_.IsReduced (chartRing B S hS Y.1 Y.2 d.V) :=
    isReduced_chartRing_of_isIntegralSpace B S hS Y hYint d.V
  have : Ring.KrullDimLE 1 ((chartScheme d.V).presheaf.stalk e) :=
    WY.krullDimLE_chartStalk B S hS Y.2 hYdec d.V e he
  have : Ring.KrullDimLE 1 (Localization.AtPrime (chartPrimeAt B S hS Y.2 d.V e)) :=
    krullDimLE_localization_chartPrimeAt B S hS Y.2 d.V hV e 1
  have hchart := finsum_primeResidueDegree_mul_ord_sub_eq B S hS f d hU hV hfinite e hmin deg
    hrank hfinw a b ha hb
  rw [hY, ← hchart]
  refine finsum_mem_congr rfl fun w hw => ?_
  congr 1
  obtain ⟨P, hP, hαw⟩ := hα w hw
  rw [hαw]
  have hL' := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have hLcompat := modulePullbackChartGenerator_compat B S hS f L d eM
  have hLfree := bijective_smul_modulePullbackChartGenerator B S hS f L hL' d eM hMcompat hMfree
  have hratio := chartRatio_pullbackMeromorphicSection_chartDiagram B S hS f hfm L d eM hMcompat
    hMfree (modulePullbackChartGenerator B S hS f L d eM) hLcompat hLfree
    (modulePullbackChartGenerator_id B S hS f L d eM) σ
  exact orderOfVanishingSection_eq_ord_sub_ord_of_chart B S hS X hXdec hXint hXN P _
    (modulePullbackInvertible f L hL) _
    (isRegularMeromorphicSection_pullbackMeromorphicSection B S hS f hfm L hL' σ hσ) d.U hU
    (modulePullbackChartGenerator B S hS f L d eM) hLcompat hLfree w hP.symm _ _
    (chartDiagramRestrict_mem_nonZeroDivisors B S hS f d hmin ha)
    (chartDiagramRestrict_mem_nonZeroDivisors B S hS f d hmin hb) _ hratio
    (chartMeromorphicFunctionPullback_mul_algebraMap B S hS f hfm d c a b hab)

end ChartIdentity

end AlgebraicGeometry.Space

end
