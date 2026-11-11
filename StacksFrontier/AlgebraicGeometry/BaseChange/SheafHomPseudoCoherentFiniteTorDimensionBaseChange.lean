module

public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomPseudoCoherentFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseBaseChangeIsoCharts
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PullDatumSheafHom
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseStalkMapTorAmplitude
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedSheafHomApproximation
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.AffineScheme
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.IsPerfectComparison
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChangeCartesian
public import StacksCore.Tactic.StacksAttribute

/-!
# Case (2) of Stacks 08IE, corrected: base change of finite Tor dimension

Case (2) of [Stacks, Tag 08IE] asserts that for `f : X ⟶ S` quasi-compact and quasi-separated, a
pseudo-coherent `E ∈ D(𝒪_X)` and a bounded complex `𝒢^•` of quasi-coherent `𝒪_X`-modules flat
over `S`, the canonical map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

is an isomorphism for every base change `g : S' ⟶ S`. As stated this is false
(`errata.md`, entry **08IE(2)**; the counterexample over `ℤ/4` is
`not_forall_isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent`, in the namespace
`Stacks.Examples.SheafHomCounterexample`).
The correction recorded there adds the hypothesis that `g` have finite Tor dimension, and leaves
case (1) unchanged. This module proves the corrected case (2), under the hypothesis on `g` read at
the stalks: every local ring `𝒪_{S', s'}` has finite Tor dimension over `𝒪_{S, g(s')}`. That is
implied by `g` having finite Tor dimension, and also by `g` having locally finite Tor dimension
(Stacks 09U9: Tor amplitude is a stalkwise condition), so the statement below is the corrected
case (2) and somewhat more.

## The proof

It is the source's proof with the correction of the erratum: Stacks 0DJ9 reduces the claim to
condition (1) of Stacks 0DJ8 for the comparison
`L(g')^*R𝓗om(E, 𝒢^•) ⟶ R𝓗om(L(g')^*E, (g')^*𝒢^•)`, the stalk check of the proof of Stacks 0A1D
gives that condition for `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`, and the corrected Stacks 0DJA (3) carries it to
the comparison for `R𝓗om`. The corrected 0DJA (3) is proved chart by chart: on a Cartesian
affine-open chart `U' = U ×_V V'` the pseudo-coherent `E|_U` is approximated in each degree by a
perfect complex (Stacks 08EQ), the comparison for that complex satisfies the condition by
Stacks 0DJA (2), and the Tor amplitude of the stalks of `g` bounds the error
(`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_approximation`).
Stacks 0DJ9 is used in its chartwise form
(`AlgebraicGeometry.isIso_derivedBaseChangeComp_of_chartwise`), and the comparison on a chart is
identified with the pulled-back comparison by
`Stacks.Cohomology.BaseChangeCover.pullDatum_baseChangeSheafHomComparison`.

## Main results

* `AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_hasFiniteTorDimension`:
  **Stacks 08IE, case (2), corrected**, with the condition on `g` at the stalks.
* `isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_hasFiniteTorDimension_appLE`:
  the same, with the condition on `g` on affine opens, as the erratum spells it out.

## References

* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 09U9](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeSheafHomComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.Cohomology.DerivedInternalHomPullback (derivedPullbackSheafHomMap
  isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent)
open Stacks.SheafOfModules (derivedSheafHom)
open Stacks.Cohomology.BaseChangeCover (pullDatum squareComparison)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- An object bounded below is locally bounded below. -/
private theorem isLocallyBoundedBelow_of_isGE {Y : Scheme.{u}} (M : DerivedCategory Y.Modules)
    (a : ℤ) (hM : M.IsGE a) : RingedSpace.IsLocallyBoundedBelow Y.toRingedSpace M :=
  fun _ => ⟨⊤, trivial, a, fun i hi => Functor.map_isZero _ (M.isZero_of_isGE a i hi)⟩

/-- **The corrected Stacks 0DJA (3) for the restricted datum on a chart.** On the square of spectra
of a Cartesian affine-open chart, the comparison `L(g_Z)^*R𝓗om(Lj^*E, Lj^*K) ⟶
R𝓗om(L(g_Z)^*Lj^*E, L(j')^*K')` at the pulled-back `φ` satisfies condition (1) of Stacks 0DJ8,
for `E` pseudo-coherent, `K` and `K'` bounded below, `φ` satisfying that condition on the whole
square, and stalk maps of `g` of finite Tor dimension. The proof approximates `Lj^*E` on the affine
`Spec A` by perfect complexes (Stacks 08EQ). -/
theorem isIso_baseChangeCohomologyMap_restrictedSheafHomComparison
    (hsq : IsPullback g' f' f g)
    (hg : ∀ s' : S', HasFiniteTorDimensionRingHom (g.stalkMap s').hom)
    (E K : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hsq.w K K' φ x' n))
    (a : ℤ) (hK : K.IsGE a) (hK' : K'.IsGE a) (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (n : ℤ) :
    IsIso (baseChangeCohomologyMap (Spec.map ch.a) (Spec.map ch.b) (Spec.map ch.d)
      (Spec.map ch.c) (isPullback_specMap ch.isPushout).w
      (((derivedSheafHom (Spec ch.A).sheaf).obj
        (op ((derivedPullback ch.incU.toLRSHom.toShHom).obj E))).obj
          ((derivedPullback ch.incU.toLRSHom.toShHom).obj K))
      (((derivedSheafHom (Spec ch.A').sheaf).obj
        (op ((derivedPullback (Spec.map ch.c).toLRSHom.toShHom).obj
          ((derivedPullback ch.incU.toLRSHom.toShHom).obj E)))).obj
          ((derivedPullback ch.incU'.toLRSHom.toShHom).obj K'))
      (baseChangeSheafHomComparison (Spec.map ch.c).toLRSHom.toShHom
        ((derivedPullback ch.incU.toLRSHom.toShHom).obj E)
        ((derivedPullback ch.incU.toLRSHom.toShHom).obj K)
        ((derivedPullback ch.incU'.toLRSHom.toShHom).obj K')
        (pullDatum (Spec.map ch.c).toLRSHom.toShHom ch.incU'.toLRSHom.toShHom
          ch.incU.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm ch.wU'U.symm)
          K K' φ)) y n) := by
  have := ch.isOpenImmersion_incU
  have := ch.isOpenImmersion_incV
  have := ch.isOpenImmersion_incV'
  have := ch.isOpenImmersion_incU' hsq
  have hpb := isPullback_specMap ch.isPushout
  have hj : AlgebraicGeometry.IsFlat ch.incU.toLRSHom.toShHom := fun x => Flat.stalkMap ch.incU x
  have hj' : AlgebraicGeometry.IsFlat ch.incU'.toLRSHom.toShHom :=
    fun x => Flat.stalkMap ch.incU' x
  have hKU : ((derivedPullback ch.incU.toLRSHom.toShHom).obj K).IsGE a :=
    Stacks.Cohomology.DerivedInternalHomPullback.isGE_derivedPullback_obj_of_isFlat _ hj K a hK
  have hK'U : ((derivedPullback ch.incU'.toLRSHom.toShHom).obj K').IsGE a :=
    Stacks.Cohomology.DerivedInternalHomPullback.isGE_derivedPullback_obj_of_isFlat _ hj' K' a hK'
  have hφU := fun y n => isIso_baseChangeCohomologyMap_pullDatum hsq hpb ch.incU ch.incU' ch.incV
    ch.incV' ch.wU'U.symm ch.wU.symm ch.wU'V'.symm ch.wV'.symm K K' φ y n (h _ n)
  obtain ⟨e₁, e₂, hT⟩ := exists_hasTorAmplitudeCanonical_baseStalkMap (Spec.map ch.a)
    (Spec.map ch.b) (Spec.map ch.d) (Spec.map ch.c) hpb.w g ch.incV ch.incV' ch.wV'.symm y
    (hg _)
  have hT' := hT
  rw [← neg_neg e₁] at hT'
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℤ, n + 1 < a - (m - 1) - -e₁ ∧ n + 1 < a - (m - 1) :=
    ⟨a - n - 3 - |e₁|, by have := neg_abs_le e₁; omega, by have := abs_nonneg e₁; omega⟩
  have hEU := Scheme.Hom.isPseudoCoherent_derivedPullback ch.incU E hE
  obtain ⟨r, hr⟩ := PerfectApproximation.hasApproximationByPerfectComplexes_of_isAffine
    (Spec ch.A) Set.univ isClosed_univ (by simp)
  obtain ⟨P, hP, -, α, hiso, hepi⟩ := hr ((derivedPullback ch.incU.toLRSHom.toShHom).obj E) m
    (fun i => isQuasicoherentDerived_of_isPseudoCoherent (Spec ch.A) _ hEU i)
    (by obtain ⟨K₀, hK₀, e⟩ := hEU; exact ⟨K₀, hK₀ (m - r), e⟩)
    (fun _ _ _ hx => absurd (Set.mem_univ _) hx)
  exact isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_approximation hpb _ _ _ _
    hφU a a hKU hK'U y n (-e₁) e₂ m hT' hm₁ hm₂ P
    ((RingedSpace.isPerfect_iff_perfectComplexes_isPerfect P).1 hP) α hiso hepi

/-- **The corrected Stacks 0DJA (3) on a chart.** For a cartesian square, a pseudo-coherent `E`, a
`K` bounded below by `a`, a `K'` bounded below by `a` and `φ : L(g')^*K ⟶ K'` satisfying condition
(1) of Stacks 0DJ8, if the stalk maps of `g` have finite Tor dimension then the comparison
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, pulled back to the square of spectra of a Cartesian
affine-open chart, satisfies condition (1) of Stacks 0DJ8 there. -/
theorem isIso_baseChangeCohomologyMap_pullDatum_baseChangeSheafHomComparison
    (hsq : IsPullback g' f' f g)
    (hg : ∀ s' : S', HasFiniteTorDimensionRingHom (g.stalkMap s').hom)
    (E K : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hsq.w K K' φ x' n))
    (a : ℤ) (hK : K.IsGE a) (hK' : K'.IsGE a) (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (n : ℤ) :
    IsIso (baseChangeCohomologyMap (Spec.map ch.a) (Spec.map ch.b) (Spec.map ch.d)
      (Spec.map ch.c) (isPullback_specMap ch.isPushout).w
      ((derivedPullback ch.incU.toLRSHom.toShHom).obj
        (((derivedSheafHom X.sheaf).obj (op E)).obj K))
      ((derivedPullback ch.incU'.toLRSHom.toShHom).obj
        (((derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K'))
      (pullDatum (Spec.map ch.c).toLRSHom.toShHom ch.incU'.toLRSHom.toShHom
        ch.incU.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm ch.wU'U.symm)
        _ _ (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)) y n) := by
  have := ch.isOpenImmersion_incU
  have := ch.isOpenImmersion_incU' hsq
  have hj : AlgebraicGeometry.IsFlat ch.incU.toLRSHom.toShHom := fun x => Flat.stalkMap ch.incU x
  have hj' : AlgebraicGeometry.IsFlat ch.incU'.toLRSHom.toShHom :=
    fun x => Flat.stalkMap ch.incU' x
  have hE' := (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).2 hE
  have hLE' := (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' _).2
    (Scheme.Hom.isPseudoCoherent_derivedPullback g' E hE)
  -- the target: transport along the canonical map of Tag 08I3 along `j'` and the comparison
  have hψ := IsIso.comp_isIso'
    (isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent
      ch.incU'.toLRSHom.toShHom hj' _ hLE' K' (isLocallyBoundedBelow_of_isGE K' a hK'))
    (((derivedSheafHom (Spec ch.A').sheaf).mapIso
      (squareComparison (Spec.map ch.c).toLRSHom.toShHom ch.incU'.toLRSHom.toShHom
        ch.incU.toLRSHom.toShHom g'.toLRSHom.toShHom
        (comp_toShHom_of_comm ch.wU'U.symm) E).op).app
          ((derivedPullback ch.incU'.toLRSHom.toShHom).obj K')).isIso_hom
  refine (isIso_baseChangeCohomologyMap_iff_of_isIso_target _ _ _ _ _ _ _ _ _ _ hψ y n).1 ?_
  refine (congrArg (fun t => IsIso (baseChangeCohomologyMap (Spec.map ch.a) (Spec.map ch.b)
    (Spec.map ch.d) (Spec.map ch.c) (isPullback_specMap ch.isPushout).w _ _ t y n))
    (Stacks.Cohomology.BaseChangeCover.pullDatum_baseChangeSheafHomComparison
      (Spec.map ch.c).toLRSHom.toShHom ch.incU'.toLRSHom.toShHom ch.incU.toLRSHom.toShHom
      g'.toLRSHom.toShHom (comp_toShHom_of_comm ch.wU'U.symm) E K K' φ)).mpr ?_
  -- the source: transport along the canonical map of Tag 08I3 along `j`
  refine (isIso_baseChangeCohomologyMap_iff_of_isIso_source _ _ _ _ _ _ _ _ _
    (isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent
      ch.incU.toLRSHom.toShHom hj E hE' K (isLocallyBoundedBelow_of_isGE K a hK)) _ y n).2 ?_
  exact isIso_baseChangeCohomologyMap_restrictedSheafHomComparison hsq hg E K hE K' φ h a hK hK'
    ch y n

/-- **Stacks 08IE, case (2), corrected.** Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes, let `E` be a pseudo-coherent object of `D(𝒪_X)` and let `𝒢^•` be a bounded
complex of quasi-coherent `𝒪_X`-modules whose terms are flat over `S`. For every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

in which `g` has finite Tor dimension at the stalks — every local ring `𝒪_{S', s'}` has finite Tor
dimension over `𝒪_{S, g(s')}`, the correction of case (2) recorded in `errata.md` (entry
**08IE(2)**) — the canonical map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

of `AlgebraicGeometry.sheafHomFlatBaseChangeMap`, with the **ordinary** pullback `(g')^*𝒢^•` on
the right, is an isomorphism. Without the condition on `g` the statement is false:
`not_forall_isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent` in
`Stacks.Examples.SheafHomCounterexample`.

The condition on `g` is the stalkwise form of "`𝒪_{S'}` has finite Tor dimension over
`g⁻¹𝒪_S`": it is implied by that condition, and also by its local version (Tor amplitude is a
stalkwise condition, Stacks 09U9). -/
@[stacks 08IE "case (2), with the correction of errata.md (entry 08IE(2)): f quasi-compact and \
quasi-separated, E pseudo-coherent, 𝒢^• bounded with terms quasi-coherent and flat over S, and g \
of finite Tor dimension, read at the stalks (each 𝒪_{S', s'} of finite Tor dimension over \
𝒪_{S, g(s')}, which finite Tor dimension of g implies); the canonical map of the source's proof, \
with the ORDINARY pullback (g')^*𝒢^• on the right, is an isomorphism. Without the condition on g \
case (2) is false (the counterexample over ℤ/4 of the erratum)"]
public theorem isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_hasFiniteTorDimension
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (hg : ∀ s' : S', HasFiniteTorDimensionRingHom (g.stalkMap s').hom)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (a b : ℤ) (hGge : G.IsStrictlyGE a)
    (hGle : G.IsStrictlyLE b)
    (hGqcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n)) :
    IsIso (sheafHomFlatBaseChangeMap f g f' g' sq E G) := by
  have := hqc
  have := hqs
  let G' := (pullbackComplex g'.toLRSHom.toShHom).obj G
  have hGa : (DerivedCategory.Q.obj G).IsGE a :=
    (DerivedCategory.isGE_Q_obj_iff G a).2 inferInstance
  have hG'ge : G'.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
      Functor.map_isZero _ (G.isZero_of_isStrictlyGE a i hi)
  have hG'a : (DerivedCategory.Q.obj G').IsGE a :=
    (DerivedCategory.isGE_Q_obj_iff G' a).2 inferInstance
  have hG'qcoh : ∀ n : ℤ, (G'.X n).IsQuasicoherent := fun n =>
    Stacks.Modules.isQuasicoherent_pullback g' (G.X n) (hGqcoh n)
  have hK := derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X E (DerivedCategory.Q.obj G) hE
    ⟨⟨a, fun n hn => (DerivedCategory.Q.obj G).isZero_of_isGE a n hn⟩,
      fun n => isQuasicoherent_derived_homology G hGqcoh n⟩
  have hK' := derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X'
    ((derivedPullback g'.toLRSHom.toShHom).obj E) (DerivedCategory.Q.obj G')
    (Scheme.Hom.isPseudoCoherent_derivedPullback g' E hE)
    ⟨⟨a, fun n hn => (DerivedCategory.Q.obj G').isZero_of_isGE a n hn⟩,
      fun n => isQuasicoherent_derived_homology G' hG'qcoh n⟩
  exact isIso_derivedBaseChangeComp_of_chartwise hsq _ _ _ hK hK' fun ch y n =>
    isIso_baseChangeCohomologyMap_pullDatum_baseChangeSheafHomComparison hsq hg E
      (DerivedCategory.Q.obj G) hE _ _
      (pointwiseBaseChangeOfFlatOver f g f' g' hsq hsq.w G ⟨b, hGle⟩ hGqcoh hGflat) a hGa hG'a
      ch y n

/-- **Stacks 08IE, case (2), corrected, with the condition on `g` on affine opens.** This is
`isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_hasFiniteTorDimension` with the correction
of `errata.md` (entry **08IE(2)**) read on affine opens as the erratum spells it out: for all affine
opens `V ⊆ S` and `V' ⊆ g⁻¹(V)` the ring `𝒪_{S'}(V')` has finite Tor dimension over `𝒪_S(V)`. The
hypotheses on `f`, `E` and `𝒢^•` are those of the source. -/
@[stacks 08IE "case (2), with the correction of errata.md (entry 08IE(2)) in the affine-open form \
the erratum spells out: for affine opens V ⊆ S and V' ⊆ g⁻¹(V), 𝒪_{S'}(V') has finite Tor \
dimension over 𝒪_S(V); f quasi-compact and quasi-separated, E pseudo-coherent, 𝒢^• bounded with \
terms quasi-coherent and flat over S; the canonical map, with the ORDINARY pullback (g')^*𝒢^•, is \
an isomorphism"]
public theorem isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_hasFiniteTorDimension_appLE
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (hg : ∀ (V : S.Opens) (V' : S'.Opens), IsAffineOpen V → IsAffineOpen V' →
      ∀ hle : V' ≤ g ⁻¹ᵁ V, HasFiniteTorDimensionRingHom (g.appLE V V' hle).hom)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (a b : ℤ) (hGge : G.IsStrictlyGE a)
    (hGle : G.IsStrictlyLE b)
    (hGqcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n)) :
    IsIso (sheafHomFlatBaseChangeMap f g f' g' sq E G) :=
  isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_hasFiniteTorDimension f g f' g' hsq hqc
    hqs (hasFiniteTorDimensionRingHom_stalkMap_of_appLE g hg) sq E hE G a b hGge hGle hGqcoh
    hGflat

end AlgebraicGeometry

end
