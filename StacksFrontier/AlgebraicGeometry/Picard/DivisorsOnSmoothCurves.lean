module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatCartierFibre
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Divisors on a smooth relative curve

Let `f : X ⟶ S` be smooth of relative dimension one and let `D ⊆ X` be a closed subscheme,
presented by its quasi-coherent sheaf of ideals. Four conditions on `D` are compared: that
`D → S` is finite locally free; that `D` is a relative effective Cartier divisor on `X/S`; that
`D → S` is locally quasi-finite, flat and locally of finite presentation; and that `D → S` is
locally quasi-finite and flat. The first implies the second, the second and third are
equivalent, and the third implies the fourth. Over a locally Noetherian base the third and
fourth are equivalent as well, and when `f` is proper so are the first and second.

The equivalence of the second and third conditions is local on the base and reduces to the case
of a smooth curve over a field, where the local rings at closed points are one-dimensional
regular local rings, hence discrete valuation rings. A closed subscheme of such a curve is an
effective Cartier divisor exactly when it contains no generic point, which for a subscheme of
finite type is exactly the condition that it be quasi-finite over the base.

## Main results

* `AlgebraicGeometry.isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree` is the
  implication (1) implies (2).
* `AlgebraicGeometry.isRelativeEffectiveCartierDivisor_iff_locallyQuasiFinite_flat` is the
  equivalence of (2) and (3).
* `AlgebraicGeometry.locallyQuasiFinite_flat_of_locallyOfFinitePresentation` is the implication
  (3) implies (4).
* `AlgebraicGeometry.isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper` is
  the equivalence of (1) and (2) for a proper `f`.

The remaining clause, the equivalence of (3) and (4) over a locally Noetherian base, is
`AlgebraicGeometry.locallyQuasiFinite_flat_locallyOfFinitePresentation_iff_of_isLocallyNoetherian`
in `StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension`.

## Implementation notes

The closed subscheme is `AlgebraicGeometry.Scheme.IdealSheafData`, and its structure morphism to
the base is the composite `I.subschemeι ≫ f`. "Locally quasi-finite" in the source means locally
of finite type with discrete fibres, whereas Mathlib's `AlgebraicGeometry.LocallyQuasiFinite`
asks only that the fibres be finite over the residue fields; so conditions (3) and (4) both
carry `AlgebraicGeometry.LocallyOfFiniteType` as a separate conjunct. In (3) that conjunct is
implied by local finite presentation, and is kept only so that (3) and (4) spell the source's
hypothesis the same way.

## References

* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- The closed subscheme cut out on a fibre of `f` by the restriction of an ideal sheaf `I` is
the fibre of the structure morphism of the closed subscheme cut out by `I`. -/
noncomputable def Scheme.IdealSheafData.comapFiberιSubschemeIso {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (s : S) :
    (I.comap (f.fiberι s)).subscheme ≅ (I.subschemeι ≫ f).fiber s :=
  I.comapIso (f.fiberι s) ≪≫ pullbackSymmetry (f.fiberι s) I.subschemeι ≪≫
    pullbackRightPullbackFstIso f (S.fromSpecResidueField s) I.subschemeι

/-- **Stacks Project, Tag 0B9D.** Each fibre of a relative effective Cartier divisor is an
effective Cartier divisor on the corresponding fibre of the ambient morphism: the divisor is
flat over the base, so it stays an effective Cartier divisor after base change to the residue
field at the point. -/
theorem isEffectiveCartierDivisor_comap_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (hI : IsRelativeEffectiveCartierDivisor f I) (s : S) :
    IsEffectiveCartierDivisor (I.comap (f.fiberι s)) := by
  have : Flat (I.subschemeι ≫ f) := hI.2
  have hswap : IsEffectiveCartierDivisor
      ((I.comap (pullback.snd (S.fromSpecResidueField s) f)).comap
        (pullbackSymmetry f (S.fromSpecResidueField s)).hom) :=
    isPullbackDefined_of_flat _ _
      (isEffectiveCartierDivisor_comap_pullback f (S.fromSpecResidueField s) I hI.1)
  rwa [← Scheme.IdealSheafData.comap_comp, pullbackSymmetry_hom_comp_snd] at hswap

private theorem maximalIdeal_ne_bot_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    [IsLocalRing R] (h : ringKrullDim R = 1) : IsLocalRing.maximalIdeal R ≠ ⊥ := by
  intro h'
  rw [ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h')] at h
  norm_num at h

/-- In an ideal sheaf whose closed subscheme is discrete, a point of the support that
specializes to another point of the support is equal to it. -/
private theorem Scheme.IdealSheafData.eq_of_specializes_of_mem_support {Y : Scheme.{u}}
    (J : Y.IdealSheafData) [DiscreteTopology J.subscheme] {x y : Y} (hx : x ∈ J.support)
    (hy : y ∈ J.support) (h : y ⤳ x) : y = x := by
  obtain ⟨z₀, hz₀⟩ := Set.mem_range.mp
    (show x ∈ Set.range J.subschemeι by rwa [J.range_subschemeι])
  obtain ⟨V, hV, hVpre⟩ :=
    J.subschemeι.isEmbedding.isOpen_iff.mp (isOpen_discrete ({z₀} : Set J.subscheme))
  have hxV : x ∈ V := by
    rw [← hz₀]
    show z₀ ∈ J.subschemeι ⁻¹' V
    rw [hVpre]
    simp
  obtain ⟨z, hz⟩ := Set.mem_range.mp
    (show y ∈ Set.range J.subschemeι by rwa [J.range_subschemeι])
  have hzV : z ∈ J.subschemeι ⁻¹' V := by
    show J.subschemeι z ∈ V
    rw [hz]
    exact h.mem_open hV hxV
  have hzEq : z = z₀ := by simpa [hVpre] using hzV
  rw [← hz, hzEq, hz₀]

/-- **Stacks Project, Tag 0B9D.** At a point of the support of an ideal sheaf whose closed
subscheme is discrete, the induced ideal in a one-dimensional regular local ring is nonzero. A
zero stalk would place the ideal inside the contraction of the zero ideal of the local ring,
a prime strictly below the point; the corresponding point of the scheme is then a proper
generalization of the given point that still lies in the support, contradicting the fact that
a discrete closed subscheme isolates each of its points. -/
theorem Scheme.IdealSheafData.stalk_ne_bot_of_discreteTopology_subscheme
    {Y : Scheme.{u}} (J : Y.IdealSheafData) [DiscreteTopology J.subscheme]
    (x : Y) (hx : x ∈ J.support)
    (hregular : IsRegularLocalRing (Y.presheaf.stalk x))
    (hdim : ringKrullDim (Y.presheaf.stalk x) = 1) :
    IdealSheafData.stalk J x ≠ ⊥ := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  set A := Γ(Y, U.1)
  set R := Y.presheaf.stalk x
  set p := U.2.primeIdealOf ⟨x, hxU⟩
  set germ := (Y.presheaf.germ U.1 x hxU).hom
  intro hzero
  have hmap : (J.ideal U).map germ = ⊥ :=
    (IdealSheafData.stalk_eq_map_germ J x U hxU).symm.trans hzero
  let : Algebra A R := Y.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime R p.asIdeal := U.2.isLocalization_stalk ⟨x, hxU⟩
  have : IsRegularLocalRing R := hregular
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hmaxbot := maximalIdeal_ne_bot_of_ringKrullDim_eq_one hdim
  let e := IsLocalization.AtPrime.orderIsoOfPrime R p.asIdeal
  let q₀ : {q : Ideal R // q.IsPrime} := ⟨⊥, inferInstance⟩
  let qₘ : {q : Ideal R // q.IsPrime} := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  let q : PrimeSpectrum A := ⟨(e q₀).1, (e q₀).2.1⟩
  have htop : e qₘ = ⟨p.asIdeal, p.isPrime, le_rfl⟩ :=
    Subtype.ext (IsLocalization.AtPrime.under_maximalIdeal R p.asIdeal)
  have hq_lt : q.asIdeal < p.asIdeal := by
    have hlt := e.strictMono (show q₀ < qₘ from
      Subtype.mk_lt_mk.mpr (lt_of_le_of_ne bot_le (Ne.symm hmaxbot)))
    rwa [htop] at hlt
  have hK : J.ideal U ≤ q.asIdeal := by
    intro a ha
    have hazero : germ a = 0 := by simpa [hmap] using Ideal.mem_map_of_mem germ ha
    show a ∈ Ideal.under A (⊥ : Ideal R)
    rwa [Ideal.mem_under, RingHom.algebraMap_toAlgebra]
  have hySupport : U.2.fromSpec q ∈ J.support := by
    have hyU : U.2.fromSpec q ∈ U.1 := by
      have hmem : q ∈ U.2.fromSpec ⁻¹ᵁ U.1 := by
        rw [U.2.fromSpec_preimage_self]
        trivial
      exact hmem
    refine (J.mem_support_iff_of_mem (U := U) hyU).2 ?_
    have hpre : q ∈ U.2.fromSpec ⁻¹'
        Y.zeroLocus (U := U.1) (J.ideal U : Set Γ(Y, U.1)) := by
      rw [U.2.fromSpec_preimage_zeroLocus]
      exact (PrimeSpectrum.mem_zeroLocus q _).2 hK
    exact hpre
  have hspec : U.2.fromSpec q ⤳ x := by
    have hsp := ((PrimeSpectrum.le_iff_specializes q p).mp hq_lt.le).map U.2.fromSpec.continuous
    rwa [U.2.fromSpec_primeIdealOf ⟨x, hxU⟩] at hsp
  have hqp : U.2.fromSpec q = U.2.fromSpec p :=
    (J.eq_of_specializes_of_mem_support hx hySupport hspec).trans
      (U.2.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
  exact hq_lt.ne (congrArg PrimeSpectrum.asIdeal (U.2.fromSpec.isOpenEmbedding.injective hqp))

private theorem smoothOfRelativeDimension_fiberToSpecResidueField {n : ℕ} {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (s : S) :
    SmoothOfRelativeDimension n (f.fiberToSpecResidueField s) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) inferInstance

/-- Every point of a fibre of a morphism smooth of relative dimension one has local dimension
one. -/
private theorem topologicalKrullDimAt_fiber_eq_one {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] (s : S) (x : f.fiber s) :
    topologicalKrullDimAt (f.fiber s) x = 1 :=
  @topologicalKrullDimAt_eq_one_of_smoothOfRelativeDimension_one
    (IsLocalRing.ResidueField (S.presheaf.stalk s)) inferInstance (f.fiber s)
    (f.fiberToSpecResidueField s) (smoothOfRelativeDimension_fiberToSpecResidueField f s) x

/-- A relative effective Cartier divisor on a scheme smooth of relative dimension one is locally
quasi-finite, flat and locally of finite presentation over the base. -/
private theorem locallyQuasiFinite_flat_of_isRelativeEffectiveCartierDivisor {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] (I : X.IdealSheafData)
    (hI : IsRelativeEffectiveCartierDivisor f I) :
    LocallyOfFiniteType (I.subschemeι ≫ f) ∧ LocallyQuasiFinite (I.subschemeι ≫ f) ∧
      Flat (I.subschemeι ≫ f) ∧ LocallyOfFinitePresentation (I.subschemeι ≫ f) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : Flat (I.subschemeι ≫ f) := hI.2
  have : LocallyOfFinitePresentation I.subschemeι :=
    (Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff I).2
      (fg_ideal_of_isEffectiveCartierDivisor I hI.1)
  refine ⟨inferInstance, ?_, hI.2, inferInstance⟩
  refine locallyQuasiFinite_iff_isDiscrete_preimage_singleton.2 fun s => ?_
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have hJ := isEffectiveCartierDivisor_comap_fiberι f I hI s
  have : IsLocallyNoetherian (I.comap (f.fiberι s)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (I.comap (f.fiberι s)).subschemeι
  have hdim (z : (I.comap (f.fiberι s)).subscheme) :
      topologicalKrullDimAt (I.comap (f.fiberι s)).subscheme z = 0 := by
    have hz := topologicalKrullDimAt_fiber_eq_one f s ((I.comap (f.fiberι s)).subschemeι z)
    have hlt := topologicalKrullDimAt_subscheme_lt (I.comap (f.fiberι s)) hJ z (by
      rw [hz]
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top 1))
    rw [hz] at hlt
    refine le_antisymm (ENat.WithBot.lt_add_one_iff.mp ?_) (topologicalKrullDimAt_nonneg z)
    simpa using hlt
  have : DiscreteTopology (I.comap (f.fiberι s)).subscheme :=
    discreteTopology_iff_isOpen_singleton.2 fun z =>
      (topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint _ z).mp (hdim z)
  have : DiscreteTopology ((I.subschemeι ≫ f).fiber s) :=
    (Scheme.IdealSheafData.comapFiberιSubschemeIso f I s).hom.homeomorph.discreteTopology
  exact isDiscrete_iff_discreteTopology.2 ((I.subschemeι ≫ f).fiberHomeo s).discreteTopology

/-- A closed subscheme of a scheme smooth of relative dimension one that is locally
quasi-finite, flat and locally of finite presentation over the base is a relative effective
Cartier divisor. -/
private theorem isRelativeEffectiveCartierDivisor_of_locallyQuasiFinite_flat {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] (I : X.IdealSheafData)
    (h : LocallyOfFiniteType (I.subschemeι ≫ f) ∧ LocallyQuasiFinite (I.subschemeι ≫ f) ∧
      Flat (I.subschemeι ≫ f) ∧ LocallyOfFinitePresentation (I.subschemeι ≫ f)) :
    IsRelativeEffectiveCartierDivisor f I := by
  obtain ⟨_, _, _, _⟩ := h
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  refine isRelativeEffectiveCartierDivisor_of_flat_of_fibres f I fun s => ?_
  have hqType : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have := smoothOfRelativeDimension_fiberToSpecResidueField (n := 1) f s
  have hqSmooth : Smooth (f.fiberToSpecResidueField s) :=
    SmoothOfRelativeDimension.smooth 1 (f.fiberToSpecResidueField s)
  have hregular (x : f.fiber s) : IsRegularLocalRing ((f.fiber s).presheaf.stalk x) :=
    IsRegular.isRegularLocalRing_stalk
      (@isRegular_of_smooth_over_field (IsLocalRing.ResidueField (S.presheaf.stalk s))
        inferInstance (f.fiber s) (f.fiberToSpecResidueField s) hqSmooth) x
  have : DiscreteTopology (I.comap (f.fiberι s)).subscheme :=
    Scheme.IdealSheafData.discreteTopology_subscheme_comap_fiberι f I s
  have hdim (x : f.fiber s) (hx : x ∈ (I.comap (f.fiberι s)).support) :
      ringKrullDim ((f.fiber s).presheaf.stalk x) = 1 := by
    have hstalk := @topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) inferInstance (f.fiber s)
      (f.fiberToSpecResidueField s) hqType x
      (Scheme.IdealSheafData.isClosed_singleton_of_discreteTopology_subscheme
        (I.comap (f.fiberι s)) x hx)
    rw [topologicalKrullDimAt_fiber_eq_one f s x] at hstalk
    exact hstalk.symm
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun x hx => ?_
  have : IsRegularLocalRing ((f.fiber s).presheaf.stalk x) := hregular x
  exact IsRegularLocalRing.exists_isRegular_and_span_singleton_eq (hdim x hx) _
    (Scheme.IdealSheafData.stalk_ne_bot_of_discreteTopology_subscheme
      (I.comap (f.fiberι s)) x hx (hregular x) (hdim x hx))

/-- **Stacks Project, Tag 0B9D (2) iff (3).** On a scheme smooth of relative dimension one over
a base, the relative effective Cartier divisors are exactly the closed subschemes that are
locally quasi-finite, flat and locally of finite presentation over the base.

Both directions are checked on the fibres, which are smooth curves over a field and hence
regular of dimension one at every point. An effective Cartier divisor drops the local dimension,
so its fibres are zero-dimensional, hence discrete, which is quasi-finiteness; conversely a
discrete closed subscheme of a smooth curve meets each local ring, a discrete valuation ring, in
a nonzero ideal, which is therefore generated by a nonzerodivisor. -/
@[stacks 0B9D "(2) iff (3)"]
theorem isRelativeEffectiveCartierDivisor_iff_locallyQuasiFinite_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] (I : X.IdealSheafData) :
    IsRelativeEffectiveCartierDivisor f I ↔
      LocallyOfFiniteType (I.subschemeι ≫ f) ∧ LocallyQuasiFinite (I.subschemeι ≫ f) ∧
        Flat (I.subschemeι ≫ f) ∧ LocallyOfFinitePresentation (I.subschemeι ≫ f) :=
  ⟨locallyQuasiFinite_flat_of_isRelativeEffectiveCartierDivisor f I,
    isRelativeEffectiveCartierDivisor_of_locallyQuasiFinite_flat f I⟩

/-- **Stacks Project, Tag 0B9D (1) implies (2).** A closed subscheme of a scheme smooth of
relative dimension one over a base that is finite locally free over the base is a relative
effective Cartier divisor: a finite locally free morphism is finite, flat and locally of finite
presentation, hence in particular locally quasi-finite. -/
@[stacks 0B9D "(1) implies (2)"]
theorem isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] (I : X.IdealSheafData)
    [Stacks.Morphisms.IsFiniteLocallyFree (I.subschemeι ≫ f)] :
    IsRelativeEffectiveCartierDivisor f I := by
  obtain ⟨hfin, hflat, hlfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (I.subschemeι ≫ f)).1 inferInstance
  have : IsFinite (I.subschemeι ≫ f) := hfin
  have : LocallyOfFinitePresentation (I.subschemeι ≫ f) := hlfp
  exact (isRelativeEffectiveCartierDivisor_iff_locallyQuasiFinite_flat f I).2
    ⟨inferInstance, inferInstance, hflat, hlfp⟩

/-- **Stacks Project, Tag 0B9D (3) implies (4).** Dropping the local finite presentation
conjunct from the third condition gives the fourth. -/
@[stacks 0B9D "(3) implies (4)"]
theorem locallyQuasiFinite_flat_of_locallyOfFinitePresentation {D S : Scheme.{u}} (g : D ⟶ S)
    (h : LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ Flat g ∧
      LocallyOfFinitePresentation g) :
    LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ Flat g :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **Stacks Project, Tag 0B9D (1) iff (2) for a proper morphism.** On a proper scheme smooth of
relative dimension one over a base, the relative effective Cartier divisors are exactly the
closed subschemes that are finite locally free over the base. Such a divisor is quasi-finite
over the base, and proper since it is a closed subscheme of a proper scheme, hence finite; being
also flat and locally of finite presentation it is finite locally free. -/
@[stacks 0B9D "(1) iff (2) when X over S is proper", sga "4 XVIII 1.5.10.3" "special case"]
theorem isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [IsProper f] (I : X.IdealSheafData) :
    Stacks.Morphisms.IsFiniteLocallyFree (I.subschemeι ≫ f) ↔
      IsRelativeEffectiveCartierDivisor f I := by
  refine ⟨fun _ => isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f I, fun h => ?_⟩
  obtain ⟨-, hqf, hflat, hlfp⟩ := locallyQuasiFinite_flat_of_isRelativeEffectiveCartierDivisor f I h
  have : LocallyQuasiFinite (I.subschemeι ≫ f) := hqf
  have : IsFinite (I.subschemeι ≫ f) :=
    IsFinite.of_isProper_of_locallyQuasiFinite (I.subschemeι ≫ f)
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    (I.subschemeι ≫ f)).2 ⟨inferInstance, hflat, hlfp⟩

end AlgebraicGeometry

end
