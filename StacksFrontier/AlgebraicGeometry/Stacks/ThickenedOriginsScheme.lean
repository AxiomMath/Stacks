module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImageCounterexample
public import StacksFrontier.RingTheory.NodalCurve
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.KrullSeparation

/-!
# The affine line with infinitely many thickened origins

Let `k` be a field and `A_n = k[x][ε]/(ε^(n+1), x·ε)`. Each `Spec A_n` contains the punctured line
`{x ≠ 0} = Spec k[x][1/x]` as an open subscheme, and glueing the `Spec A_n` along it gives a scheme
`T`: the affine line with infinitely many origins, the `n`-th thickened to order `n`. The sections
`ε` of the charts agree on the punctured line, where they vanish, and define a morphism
`f : T ⟶ 𝔸¹ = Spec k[t]`, `t ↦ ε`.

This scheme is the witness against the equality clause of Stacks 0DS4 as stated upstream, with no
quasi-compactness hypothesis on `f`. This file proves what that needs of `T` and `f`: `T` is
irreducible, Jacobson, locally Noetherian and universally catenary, `f` is locally of finite type,
every point of `T`, of `𝔸¹` and of every fibre of `f` has local dimension `1`, and — because `ε`
is nilpotent on each chart but of unbounded order — a closed immersion into `𝔸¹` through which
`f` factors is an isomorphism, so the scheme theoretic image of `f` is all of `𝔸¹` although its
set theoretic image is a point.

## Main definitions

* `AlgebraicGeometry.ThickenedOrigin.T`: the glued scheme, the colimit of the wide pushout
  diagram `AlgebraicGeometry.ThickenedOrigin.diagram` of open immersions.
* `AlgebraicGeometry.ThickenedOrigin.chart`: the open immersion `Spec A_n ⟶ T`.
* `AlgebraicGeometry.ThickenedOrigin.toLine`: the morphism `f : T ⟶ 𝔸¹`.

## Main results

* `AlgebraicGeometry.ThickenedOrigin.toLine_apply`: `f` maps every point to the origin.
* `AlgebraicGeometry.ThickenedOrigin.toLine_appTop_injective` and
  `AlgebraicGeometry.ThickenedOrigin.isIso_of_isClosedImmersion`: the scheme theoretic image of
  `f` is `𝔸¹`.
* `AlgebraicGeometry.ThickenedOrigin.topologicalKrullDimAt_T`,
  `AlgebraicGeometry.ThickenedOrigin.topologicalKrullDimAt_line` and
  `AlgebraicGeometry.ThickenedOrigin.topologicalKrullDimAt_fiber_toLine`: all local dimensions are
  `1`.
* `AlgebraicGeometry.ThickenedOrigin.isUniversallyCatenary_T`, and instances for irreducibility,
  the Jacobson property and local Noetherianity of `T` and for local finite type of `f`.

## Implementation notes

The glueing is Mathlib's colimit of a locally directed diagram of open immersions, here a wide
pushout over `ℕ` with the punctured line at its apex; the charts are the colimit inclusions and
every point lies on one of them (`AlgebraicGeometry.ThickenedOrigin.exists_chart_apply_eq`). The
local dimension at a point is computed on a chart, whose generic point `(ε)` is not closed and
specializes to every point; in the Jacobson space `Spec A_n` every neighbourhood therefore contains
the generic point and a distinct closed point, which bounds the local dimension below by `1`.

## References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.ThickenedOrigin

universe u

variable (k : Type u) [Field k]

/-- The ring `A n = k[x][ε]/(ε ^ (n + 1), x * ε)` of the `n`-th chart, as a commutative ring. -/
abbrev chartRing (n : ℕ) : CommRingCat.{u} := .of (Polynomial (Polynomial k) ⧸ chartIdeal k n)

/-- The ring `k[x][1/x]` of the punctured line, along which the charts are glued. -/
abbrev puncturedRing : CommRingCat.{u} := .of (Localization.Away (X : Polynomial k))

/-- The ring `k[t]` of the target line. -/
abbrev lineRing : CommRingCat.{u} := .of (Polynomial k)

/-- The restriction `A n ⟶ A n [1/x] ≅ k[x][1/x]` from the `n`-th chart to the punctured line. -/
def restrictionHom (n : ℕ) : chartRing k n ⟶ puncturedRing k :=
  CommRingCat.ofHom (algebraMap _ (Localization.Away (xCoord k n))) ≫
    (RingEquiv.toCommRingCatIso (awayEquiv k n).symm).hom

/-- The inclusion of the punctured line `{x ≠ 0}` into the `n`-th chart. -/
def chartInclusion (n : ℕ) : Spec (puncturedRing k) ⟶ Spec (chartRing k n) :=
  Spec.map (restrictionHom k n)

/-- The inclusion of the punctured line into the `n`-th chart is an open immersion. -/
instance (n : ℕ) : IsOpenImmersion (chartInclusion k n) := by
  rw [chartInclusion, restrictionHom, Spec.map_comp]
  infer_instance

/-- The diagram of the glueing: the punctured line, included into every chart. -/
def diagram : WidePushoutShape ℕ ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan (Spec (puncturedRing k)) (fun n => Spec (chartRing k n))
    (chartInclusion k)

/-- Every morphism of the glueing diagram is an open immersion. -/
instance {i j : WidePushoutShape ℕ} (g : i ⟶ j) : IsOpenImmersion ((diagram k).map g) := by
  rcases g with _ | n
  · exact (CategoryTheory.Functor.map_id (diagram k) i).symm ▸ inferInstance
  · exact (inferInstance : IsOpenImmersion (chartInclusion k n))

/-- **The affine line with infinitely many origins, the `n`-th thickened to order `n`**: the
glueing of the charts `Spec (A n)` along their common open `{x ≠ 0}`. -/
def T : Scheme.{u} := colimit (diagram k)

/-- The `n`-th chart `Spec (A n) ⟶ T`. -/
def chart (n : ℕ) : Spec (chartRing k n) ⟶ T k := colimit.ι (diagram k) (some n)

/-- Each chart `Spec (A n) ⟶ T` is an open immersion. -/
instance (n : ℕ) : IsOpenImmersion (chart k n) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram k) (some n)))

/-- The punctured line lies in the glueing compatibly with every chart. -/
theorem chartInclusion_chart (n : ℕ) :
    chartInclusion k n ≫ chart k n = colimit.ι (diagram k) none :=
  colimit.w (diagram k) (WidePushoutShape.Hom.init n)

/-- Every point of `T` lies on some chart. -/
theorem exists_chart_apply_eq (x : T k) :
    ∃ (n : ℕ) (y : Spec (chartRing k n)), chart k n y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram k) x
  cases i with
  | none =>
    let y' : Spec (puncturedRing k) := y
    refine ⟨0, chartInclusion k 0 y', ?_⟩
    rw [← hy, ← chartInclusion_chart k 0]
    rfl
  | some n => exact ⟨n, y, hy⟩

/-- The open cover of `T` by its charts. -/
def chartCover : (T k).OpenCover :=
  Scheme.Cover.mkOfCovers ℕ (fun n => Spec (chartRing k n)) (chart k) (exists_chart_apply_eq k)

/-- The composite `k[t] ⟶ A n ⟶ k[x][1/x]` does not depend on `n`: it sends `t` to `0`. -/
theorem chartHom_restrictionHom (n : ℕ) :
    CommRingCat.ofHom (chartHom k n) ≫ restrictionHom k n =
      CommRingCat.ofHom ((algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))).comp
        ((Polynomial.C).comp (Polynomial.evalRingHom 0))) := by
  let inst : Algebra (Polynomial k) (Localization.Away (xCoord k n)) := (awayHom k n).toAlgebra
  have : IsLocalization.Away (X : Polynomial k) (Localization.Away (xCoord k n)) :=
    isLocalization_away_X k n rfl
  have hsymm : ∀ p : Polynomial k, (awayEquiv k n).symm (awayHom k n p) =
      algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) p := fun p =>
    (IsLocalization.algEquiv (Submonoid.powers (X : Polynomial k))
      (Localization.Away (X : Polynomial k)) (Localization.Away (xCoord k n))).symm.commutes p
  ext1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · change (awayEquiv k n).symm (algebraMap _ _ (chartHom k n (C a))) = _
    rw [chartHom_C, show Ideal.Quotient.mk (chartIdeal k n) (C (C a)) = xHom k n (C a) from rfl,
      show algebraMap _ (Localization.Away (xCoord k n)) (xHom k n (C a)) = awayHom k n (C a)
        from rfl, hsymm]
    simp
  · change (awayEquiv k n).symm (algebraMap _ _ (chartHom k n X)) = _
    rw [chartHom_X, algebraMap_epsilon_eq_zero, map_zero]
    simp

/-- The morphism `f : T ⟶ 𝔸¹ = Spec k[t]`, given on the `n`-th chart by `t ↦ ε`. -/
def toLine : T k ⟶ Spec (lineRing k) :=
  colimit.desc (diagram k) (WidePushoutShape.mkCocone
    (Spec.map (CommRingCat.ofHom
      ((algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))).comp
        ((Polynomial.C).comp (Polynomial.evalRingHom 0)))))
    (fun n => Spec.map (CommRingCat.ofHom (chartHom k n)))
    (fun n => by
      change Spec.map (restrictionHom k n) ≫ _ = _
      rw [← Spec.map_comp, chartHom_restrictionHom]))

/-- On the `n`-th chart, `f` is `Spec` of the map `k[t] ⟶ A n`, `t ↦ ε`. -/
@[reassoc (attr := simp)]
theorem chart_toLine (n : ℕ) :
    chart k n ≫ toLine k = Spec.map (CommRingCat.ofHom (chartHom k n)) :=
  colimit.ι_desc _ _

/-- The structure morphism `𝔸¹ ⟶ Spec k` of the target line. -/
def lineToBase : Spec (lineRing k) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

/-- The line `𝔸¹` is locally of finite type over `k`. -/
instance : LocallyOfFiniteType (lineToBase k) := by
  rw [lineToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap k (Polynomial k)).FiniteType
  exact (RingHom.finiteType_algebraMap).2 inferInstance

/-- The morphism `f : T ⟶ 𝔸¹` is locally of finite type. -/
instance : LocallyOfFiniteType (toLine k) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (chartCover k)
    fun (n : ℕ) => ?_
  change LocallyOfFiniteType (chart k n ≫ toLine k)
  rw [chart_toLine, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact finiteType_toAlgebra_chartHom k n

/-- `T` is locally Noetherian. -/
instance : IsLocallyNoetherian (T k) := LocallyOfFiniteType.isLocallyNoetherian (toLine k)

/-- The underlying space of `T` is Jacobson. -/
instance : JacobsonSpace (T k) := LocallyOfFiniteType.jacobsonSpace (toLine k)

/-- `T` is universally catenary, being locally of finite type over the field `k`. -/
theorem isUniversallyCatenary_T : Scheme.IsUniversallyCatenary (T k) :=
  Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k (toLine k ≫ lineToBase k)

/-- The origin `t = 0` of the target line. -/
def lineOrigin : Spec (lineRing k) :=
  ⟨Ideal.span {(X : Polynomial k)}, (Stacks.NodalCurve.isMaximal_span_X k).isPrime⟩

/-- **`f` maps every point of `T` to the origin**, the section `ε` being nilpotent on every
chart. -/
theorem toLine_apply (x : T k) : toLine k x = lineOrigin k := by
  obtain ⟨n, y, rfl⟩ := exists_chart_apply_eq k x
  rw [← Scheme.Hom.comp_apply, chart_toLine, Spec.map_apply]
  refine PrimeSpectrum.ext ((Stacks.NodalCurve.isMaximal_span_X k).eq_of_le
    (PrimeSpectrum.comap _ y).isPrime.ne_top ?_).symm
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change chartHom k n X ∈ y.asIdeal
  rw [chartHom_X]
  exact y.isPrime.mem_of_pow_mem _ ((epsilon_pow_succ_eq_zero k n).symm ▸ y.asIdeal.zero_mem)

/-- **`f` kills no nonzero function on the line**: the map on global sections
`k[t] ⟶ Γ(T)` is injective, because a function killed on every chart is divisible by every power
of `t`. -/
theorem toLine_appTop_injective : Function.Injective (toLine k).appTop := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hn : ∀ n, chartHom k n ((Scheme.ΓSpecIso (lineRing k)).hom a) = 0 := fun n => by
    have h := congrArg (fun z => (Scheme.ΓSpecIso (chartRing k n)).hom
      ((chart k n).appTop z)) ha
    simp only [map_zero] at h
    rw [← h]
    change _ = ((chart k n ≫ toLine k).appTop ≫ (Scheme.ΓSpecIso (chartRing k n)).hom) a
    rw [chart_toLine, Scheme.ΓSpecIso_naturality]
    rfl
  have h0 := eq_zero_of_forall_chartHom_eq_zero k _ hn
  simpa using congrArg (Scheme.ΓSpecIso (lineRing k)).inv h0

/-- **The scheme theoretic image of `f` is the whole line**: a closed immersion into `𝔸¹` through
which `f` factors is an isomorphism. -/
theorem isIso_of_isClosedImmersion {W : Scheme.{u}} (i : W ⟶ Spec (lineRing k))
    [IsClosedImmersion i] (h : T k ⟶ W) (hh : h ≫ i = toLine k) : IsIso i := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  refine eq_bot_iff.2 ((Scheme.Hom.le_ker_comp h i).trans (hh ▸ le_of_eq ?_))
  rw [Scheme.ker_of_isAffine, ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
    (RingHom.injective_iff_ker_eq_bot _).1 (toLine_appTop_injective k), map_bot]

section Topology

/-- The punctured line `k[x][1/x]` is a nonzero ring. -/
instance : Nontrivial (puncturedRing k) := by
  have h := IsLocalization.injective (Localization.Away (X : Polynomial k))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Polynomial.X_ne_zero (R := k)))
  exact nontrivial_of_ne _ _ fun h1 => one_ne_zero (h (by simpa using h1))

/-- The punctured line has a point. -/
instance : Nonempty (Spec (puncturedRing k)) :=
  inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away (X : Polynomial k))))

/-- The nilradical `(ε)` of `A n` is prime: it is the kernel of the reduction onto the domain
`k[x]`. -/
theorem isPrime_span_epsilon (n : ℕ) : (Ideal.span {epsilon k n}).IsPrime :=
  ker_reduction k n ▸ RingHom.ker_isPrime (reduction k n)

/-- Each chart `Spec (A n)` is irreducible. -/
instance (n : ℕ) : IrreducibleSpace (Spec (chartRing k n)) := by
  change IrreducibleSpace (PrimeSpectrum (Polynomial (Polynomial k) ⧸ chartIdeal k n))
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical, nilradical_eq_span_epsilon]
  exact isPrime_span_epsilon k n


/-- The generic point `(ε)` of the `n`-th chart. -/
def chartGenericPoint (n : ℕ) : Spec (chartRing k n) :=
  ⟨Ideal.span {epsilon k n}, isPrime_span_epsilon k n⟩

/-- The generic point `(ε)` of a chart specializes to every point of the chart. -/
theorem chartGenericPoint_specializes (n : ℕ) (y : Spec (chartRing k n)) :
    chartGenericPoint k n ⤳ y := by
  refine (PrimeSpectrum.le_iff_specializes
    (chartGenericPoint k n : PrimeSpectrum (Polynomial (Polynomial k) ⧸ chartIdeal k n)) y).1 ?_
  change Ideal.span {epsilon k n} ≤ y.asIdeal
  rw [← nilradical_eq_span_epsilon]
  exact @nilradical_le_prime _ _ y.asIdeal y.isPrime

/-- The generic point of a chart is not closed: `(ε)` is not maximal, `x` lying outside it but in
the proper ideal `(ε, x)`. -/
theorem not_isClosed_chartGenericPoint (n : ℕ) : ¬ IsClosed {chartGenericPoint k n} := by
  intro hcl
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal
    (chartGenericPoint k n : PrimeSpectrum (Polynomial (Polynomial k) ⧸ chartIdeal k n))).1 hcl
  change (Ideal.span {epsilon k n}).IsMaximal at hmax
  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  exact Polynomial.not_isField k
    (MulEquiv.isField hfield (quotientSpanEpsilonEquiv k n).symm.toMulEquiv)

/-- **A point of a Jacobson space has local dimension at least `1`** as soon as the space has a
generic point which is not closed: every open neighbourhood contains that generic point and a
closed point, which are distinct and the first specializes to the second. -/
theorem one_le_topologicalKrullDimAt_of_specializes {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] [T0Space Y] (η : Y) (hη : ∀ y, η ⤳ y) (hc : ¬ IsClosed {η}) (y : Y) :
    1 ≤ topologicalKrullDimAt Y y := by
  refine le_iInf fun U => ?_
  obtain ⟨U, hyU, hU⟩ := U
  obtain ⟨c, hcU, hcc⟩ := nonempty_inter_closedPoints ⟨y, hyU⟩ hU.isLocallyClosed
  have hgU : η ∈ U := (hη y).mem_open hU hyU
  have hne : η ≠ c := fun h => hc (h ▸ hcc)
  exact one_le_topologicalKrullDim_of_specializes_of_ne (x := (⟨_, hgU⟩ : U)) (y := ⟨c, hcU⟩)
    (Topology.IsInducing.subtypeVal.specializes_iff.1 (hη c))
    (fun h => hne (congrArg Subtype.val h))

/-- **Every point of a chart has local dimension `1`.** -/
theorem topologicalKrullDimAt_chart (n : ℕ) (y : Spec (chartRing k n)) :
    topologicalKrullDimAt (Spec (chartRing k n)) y = 1 := by
  refine le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim y).trans ?_) ?_
  · change topologicalKrullDim (PrimeSpectrum (Polynomial (Polynomial k) ⧸ chartIdeal k n)) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_quotient_chartIdeal]
  · exact one_le_topologicalKrullDimAt_of_specializes (chartGenericPoint k n)
      (chartGenericPoint_specializes k n) (not_isClosed_chartGenericPoint k n) y

/-- **Every point of `T` has local dimension `1`.** -/
theorem topologicalKrullDimAt_T (x : T k) : topologicalKrullDimAt (T k) x = 1 := by
  obtain ⟨n, y, rfl⟩ := exists_chart_apply_eq k x
  rw [(chart k n).isOpenEmbedding.topologicalKrullDimAt_eq, topologicalKrullDimAt_chart]

/-- **`T` is irreducible**: every chart meets the image of the first chart in a dense open. -/
instance : IrreducibleSpace (T k) := by
  have hV : IsIrreducible (Set.range (chart k 0)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (chart k 0).continuous.continuousOn
  have hcl : closure (Set.range (chart k 0)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, y, rfl⟩ := exists_chart_apply_eq k x
    have hO : IsOpen (Set.range (chartInclusion k n)) :=
      (chartInclusion k n).isOpenEmbedding.isOpen_range
    have hy : y ∈ closure (Set.range (chartInclusion k n)) := by
      rw [(hO.dense (Set.range_nonempty _)).closure_eq]
      trivial
    refine closure_mono ?_ (image_closure_subset_closure_image (chart k n).continuous ⟨y, hy, rfl⟩)
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨chartInclusion k 0 z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, chartInclusion_chart,
      chartInclusion_chart]
  have h := hV.closure
  rw [hcl] at h
  exact (irreducibleSpace_def _).2 h

/-- The generic point `(0)` of the line. -/
def lineGenericPoint : Spec (lineRing k) := ⟨⊥, Ideal.isPrime_bot⟩

/-- **Every point of the line `𝔸¹` has local dimension `1`.** -/
theorem topologicalKrullDimAt_line (y : Spec (lineRing k)) :
    topologicalKrullDimAt (Spec (lineRing k)) y = 1 := by
  refine le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim y).trans ?_) ?_
  · change topologicalKrullDim (PrimeSpectrum (Polynomial k)) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_polynomial]
  · refine one_le_topologicalKrullDimAt_of_specializes (lineGenericPoint k) (fun z => ?_) ?_ y
    · exact (PrimeSpectrum.le_iff_specializes
        (lineGenericPoint k : PrimeSpectrum (Polynomial k)) z).1 bot_le
    · intro hcl
      have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal
        (lineGenericPoint k : PrimeSpectrum (Polynomial k))).1 hcl
      exact Polynomial.not_isField k ((Ring.isField_iff_maximal_bot).2 hmax)

/-- **The fibres of `f` have local dimension `1` everywhere**: `f` is constant, so its fibre
through any point is all of `T`, topologically. -/
theorem topologicalKrullDimAt_fiber_toLine (x : T k) :
    topologicalKrullDimAt ((toLine k).fiber (toLine k x)) ((toLine k).asFiber x) = 1 := by
  have huniv : (toLine k) ⁻¹' {toLine k x} = Set.univ :=
    Set.eq_univ_of_forall fun z => by
      change toLine k z = toLine k x
      rw [toLine_apply, toLine_apply]
  have hemb : Topology.IsOpenEmbedding (Subtype.val : (toLine k) ⁻¹' {toLine k x} → T k) :=
    (huniv ▸ isOpen_univ : IsOpen ((toLine k) ⁻¹' {toLine k x})).isOpenEmbedding_subtypeVal
  rw [topologicalKrullDimAt_eq_of_homeomorph ((toLine k).fiberHomeo (toLine k x)),
    ← hemb.topologicalKrullDimAt_eq]
  exact topologicalKrullDimAt_T k _

end Topology

end AlgebraicGeometry.ThickenedOrigin

end
