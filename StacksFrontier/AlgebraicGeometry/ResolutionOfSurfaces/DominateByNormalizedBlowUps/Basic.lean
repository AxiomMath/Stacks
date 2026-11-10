module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Reduced
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierAfterPointBlowups
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.KerDetected.RingColimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUpNagata
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusDVR
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.KrullDimension.GoingUpGoingDown
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion
public import StacksFrontier.Topology.Irreducible.GenericPoints
public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.PullbackStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dominating a surface modification by normalized blowups

A proper birational morphism to a Noetherian Nagata scheme of dimension two is dominated by a
finite succession of normalized blowups at closed points, starting from the normalization of the
scheme. The chain of normalized blowups is `AlgebraicGeometry.NormalizedBlowUpChain`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_dominating`: a proper birational
  morphism `f : Y ⟶ X` to a Noetherian Nagata scheme of dimension two admits a chain of
  normalized blowups over `X`, starting from the normalization of `X`, whose last scheme maps to
  `Y` over `X`.
* `Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_resolving_partialMap`: a rational
  map from a Noetherian Nagata scheme of dimension two over `S` to a scheme proper over `S`
  extends to a morphism on such a chain of normalized blowups.
* `Stacks.ResolutionOfSurfaces.finite_irreducibleComponents_isCompactOpen_of_isNoetherian`:
  on a Noetherian scheme every quasi-compact open has finitely many irreducible components,
  which is the hypothesis under which the normalization and the normalized blowups exist.

## Implementation notes

Both schemes are first replaced by their normalizations, so that the morphism becomes a proper
birational morphism of normal Noetherian Nagata schemes of dimension at most two. Such a
morphism is an isomorphism away from finitely many closed points, and over each of them the
fibre is a proper curve; the set of curves contracted by the morphism is therefore finite and
the argument is a double induction, the outer one on the number of contracted curves and the
inner one on the order of vanishing of a fraction whose residue at the contracted curve is
transcendental over the residue field of the image point. A normalized blowup at the image point
is an isomorphism over the locus where the two morphisms already agree, injects the contracted
curves of the normalized pullback into those of the original morphism, and strictly drops that
order of vanishing, because the exceptional divisor splits off a common factor from the
numerator and the denominator.

## References

* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
* [Stacks Project, Tag 0C5I](https://stacks.math.columbia.edu/tag/0C5I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Finiteness of irreducible components on a Noetherian scheme -/

/-- On a Noetherian scheme every quasi-compact open has finitely many irreducible components.
This is the hypothesis under which the normalization and the normalized blowups of the scheme
are available. -/
theorem finite_irreducibleComponents_isCompactOpen_of_isNoetherian {X : Scheme.{u}}
    [IsNoetherian X] :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  intro U _
  have hNoetherian : NoetherianSpace (U : Set X) := NoetherianSpace.set (U : Set X)
  exact @NoetherianSpace.finite_irreducibleComponents (U : Set X) inferInstance hNoetherian

/-! ### The isomorphism locus at a point of codimension at most one

The maximal open over which a proper birational morphism with reduced source is an isomorphism
contains every point whose local ring is a normal domain of dimension at most one. For a
generic point the local ring is a field, by birationality and reducedness of the source.
-/

/-- The maximal open over which a proper birational morphism with reduced source is an
isomorphism contains every point whose local ring is a normal domain of dimension at most one:
such a point has a neighbourhood over which the morphism is finite, hence a finite fibre. -/
private theorem mem_maximal_isomorphism_open_of_ringKrullDim_stalk_le_one
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (U : X.Opens)
    (hUmax : ∀ V : X.Opens, IsIso (f ∣_ V) → V ≤ U) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    x ∈ U := by
  obtain ⟨V, hxV, hfinite⟩ :=
    exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one f x hdim
      (Or.inl (residueField_isAlgebraic_of_isBirational f hf))
  let xV : V.toScheme := ⟨x, hxV⟩
  have hglobalFiber : (f ⁻¹' {x}).Finite :=
    ((f ∣_ V).finite_preimage_singleton xV).of_injective
    (fun y => by
      let yV : (f ⁻¹ᵁ V).toScheme := ⟨y.1, by
        change f y.1 ∈ V
        rw [show f y.1 = x from Set.mem_singleton_iff.mp y.2]
        exact hxV⟩
      exact ⟨yV, Subtype.ext ((morphismRestrict_base_coe f V yV).trans
        (Set.mem_singleton_iff.mp y.2))⟩)
    (fun y z h => Subtype.ext (congrArg (fun w => (w.1.1 : Y)) h))
  obtain ⟨W, hxW, hWiso⟩ :=
    exists_isIso_restrict_of_finite_fiber_of_normal f hf x hglobalFiber
  exact hUmax W hWiso hxW

/-- A point whose closure has codimension zero is a generic point of an irreducible
component. -/
private theorem mem_genericPoints_of_codimension_eq_zero {X : Scheme.{u}} {x : X}
    (hx : codimension (IrreducibleCloseds.closureSingleton x) = 0) :
    x ∈ genericPoints X := by
  have hmax : IsMax (IrreducibleCloseds.closureSingleton x) := by
    rwa [← Order.coheight_eq_zero, ← codimension_eq_coheight]
  refine ⟨isIrreducible_singleton.closure, fun s hs hsub => ?_⟩
  have hle : IrreducibleCloseds.closureSingleton x ≤
      (⟨closure s, hs.closure, isClosed_closure⟩ : IrreducibleCloseds X) :=
    hsub.trans subset_closure
  exact subset_closure.trans (hmax hle)

/-- The maximal open over which a proper birational morphism with reduced source is an
isomorphism contains every generic point of its target: the local ring there is a field, being
isomorphic to the local ring at a generic point of the reduced source. -/
private theorem mem_maximal_isomorphism_open_of_mem_genericPoints
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (U : X.Opens)
    (hU : IsGreatest {V : X.Opens | IsIso (f ∣_ V)} U) (x : X)
    (hx : x ∈ genericPoints X) :
    x ∈ U := by
  obtain ⟨y, hy, hfy⟩ := hf.bijOn.surjOn hx
  have : IsIso (f.stalkMap y) := hf.isIso_stalkMap y hy
  have hfieldY : IsField (Y.presheaf.stalk y) :=
    isField_stalk_of_closure_mem_irreducibleComponents Y y hy
  have hfieldX : IsField (X.presheaf.stalk (f y)) :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv.isField hfieldY
  rw [← hfy]
  let : Field (X.presheaf.stalk (f y)) := hfieldX.toField
  exact mem_maximal_isomorphism_open_of_ringKrullDim_stalk_le_one f hf U
    (fun V hV => hU.2 hV) (f y) ((ringKrullDim_eq_zero_of_isField hfieldX).trans_le zero_le_one)

/-- The maximal isomorphism open of a proper birational morphism with reduced source to a
Noetherian scheme contains every codimension-one point whose local ring is a discrete valuation
ring. -/
private theorem mem_maximal_isomorphism_open_of_codimension_eq_one_of_isDiscreteValuationRing
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (U : X.Opens) (_hUiso : IsIso (f ∣_ U))
    (hUmax : ∀ V : X.Opens, IsIso (f ∣_ V) → V ≤ U) (x : X)
    (_hcodim : codimension (IrreducibleCloseds.closureSingleton x) = 1)
    (hdvr : ∃ _ : IsDomain (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x)) :
    x ∈ U := by
  obtain ⟨hdom, hdvr⟩ := hdvr
  let : IsDomain (X.presheaf.stalk x) := hdom
  let : IsDiscreteValuationRing (X.presheaf.stalk x) := hdvr
  have hiff : IsDiscreteValuationRing (X.presheaf.stalk x) ↔
      IsIntegrallyClosed (X.presheaf.stalk x) ∧
        ∃! P : Ideal (X.presheaf.stalk x), P ≠ ⊥ ∧ P.IsPrime :=
    (IsDiscreteValuationRing.TFAE (X.presheaf.stalk x)
      (IsDiscreteValuationRing.not_isField (X.presheaf.stalk x))).out 1 4
  let : IsIntegrallyClosed (X.presheaf.stalk x) := (hiff.mp hdvr).1
  exact mem_maximal_isomorphism_open_of_ringKrullDim_stalk_le_one f hf U hUmax x
    (IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)).le

/-! ### Generic points of the normalization -/

/-- The normalization morphism carries the generic points of the normalization bijectively onto
the generic points of the scheme: this holds for a reduced scheme because the normalization is
then birational, and in general because the normalization of a scheme is the normalization of
its reduction, whose closed immersion is a homeomorphism. -/
private theorem bijOn_genericPoints_normalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Set.BijOn (Scheme.normalization X hX)
      (genericPoints (Scheme.normalizationScheme X hX)) (genericPoints X) := by
  have hred : IsReduced X.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  have hsurj : Function.Surjective X.nilradical.subschemeι := fun y ↦
    Set.mem_range.mp
      (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  have hι : Set.BijOn X.nilradical.subschemeι
      (genericPoints X.nilradical.subscheme) (genericPoints X) :=
    Homeomorph.bijOn_genericPoints
      (X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hsurj)
  have hν : Set.BijOn
      (X.nilradical.subscheme.normalization (X.finite_irreducibleComponents_reduction hX))
      (genericPoints (X.nilradical.subscheme.normalizationScheme
        (X.finite_irreducibleComponents_reduction hX)))
      (genericPoints X.nilradical.subscheme) :=
    (X.nilradical.subscheme.isBirational_normalization
      (X.finite_irreducibleComponents_reduction hX)).bijOn
  have hfun : ∀ z : Scheme.normalizationScheme X hX,
      Scheme.normalization X hX z =
        X.nilradical.subschemeι
          (X.nilradical.subscheme.normalization
            (X.finite_irreducibleComponents_reduction hX) (e.hom z)) := by
    intro z
    rw [← he]
    rfl
  have hiso : ∀ z : Scheme.normalizationScheme X hX,
      z ∈ genericPoints (Scheme.normalizationScheme X hX) →
      e.hom z ∈ genericPoints (X.nilradical.subscheme.normalizationScheme
        (X.finite_irreducibleComponents_reduction hX)) :=
    fun _ hz => mem_genericPoints_of_iso e hz
  refine ⟨fun z hz => ?_, fun z hz z' hz' heq => ?_, fun x hx => ?_⟩
  · rw [hfun z]
    exact hι.mapsTo (hν.mapsTo (hiso z hz))
  · rw [hfun z, hfun z'] at heq
    simpa using congrArg (fun w => e.inv w) (hν.injOn (hiso z hz) (hiso z' hz')
      (hι.injOn (hν.mapsTo (hiso z hz)) (hν.mapsTo (hiso z' hz')) heq))
  · obtain ⟨r, hr, hrx⟩ := hι.surjOn hx
    obtain ⟨w, hw, hwr⟩ := hν.surjOn hr
    have hwgen : e.inv w ∈ genericPoints (Scheme.normalizationScheme X hX) := by
      simpa using mem_genericPoints_of_iso e.symm hw
    refine ⟨e.inv w, hwgen, ?_⟩
    rw [hfun (e.inv w), show e.hom (e.inv w) = w by simp, hwr, hrx]

private lemma isDominant_of_isBirational {X Y : Scheme} (f : X ⟶ Y)
    (hf : IsBirational f) : IsDominant f := by
  apply (isDominant_iff f).mpr
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoints.closure (α := Y)]
  exact closure_mono fun y hy => (hf.bijOn.surjOn hy).imp fun _ hx => hx.2

private lemma surjective_functionFieldMap_of_isBirational
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (hf : IsBirational f) : Function.Surjective (functionFieldMap f) := by
  have : IsIso (f.stalkMap (genericPoint X)) := hf.isIso_stalkMap _ (by
    rw [genericPoints_eq_singleton]
    rfl)
  exact (asIso ((Y.presheaf.stalkCongr
    (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom ≫
      f.stalkMap (genericPoint X))).commRingCatIsoToRingEquiv.surjective

private lemma topologicalKrullDim_le_of_isBirational
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  have := isDominant_of_isBirational f hf
  let := (functionFieldMap f).toAlgebra
  have : Algebra.IsAlgebraic Y.functionField X.functionField := ⟨fun x => by
    obtain ⟨a, rfl⟩ := surjective_functionFieldMap_of_isBirational f hf x
    exact isAlgebraic_algebraMap a⟩
  simpa only [trdeg_eq_zero, map_zero, WithBot.coe_zero, add_zero] using
    AlgebraicGeometry.topologicalKrullDim_le_add_trdeg f

private lemma topologicalKrullDim_affineOpen_eq_ringKrullDim {X : Scheme}
    (U : X.Opens) (hU : IsAffineOpen U) :
    topologicalKrullDim U = ringKrullDim Γ(X, U) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph

private lemma topologicalKrullDim_le_of_isIntegralHom {X Y : Scheme} (f : X ⟶ Y)
    [IsIntegralHom f] : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let V : X.Opens := f ⁻¹ᵁ U
  calc
    TopologicalSpace.localKrullDim X x ≤ topologicalKrullDim V :=
      iInf_le_of_le V (iInf_le_of_le V.2 (iInf_le _ hxU))
    _ ≤ topologicalKrullDim U := by
      rw [topologicalKrullDim_affineOpen_eq_ringKrullDim V (hU.preimage f),
        topologicalKrullDim_affineOpen_eq_ringKrullDim U hU]
      exact (integral_dim_up (f.app U).hom (f.isIntegral_app U hU)).1
    _ ≤ topologicalKrullDim Y := topologicalKrullDim_subspace_le Y U

private lemma exists_maximal_isomorphism_open {X Y : Scheme} (f : Y ⟶ X) :
    ∃ U : X.Opens, IsGreatest {V : X.Opens | IsIso (f ∣_ V)} U := by
  let U : X.Opens := sSup {V : X.Opens | IsIso (f ∣_ V)}
  refine ⟨U, ?_, fun V hV => le_sSup hV⟩
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  have hx : x.1 ∈ sSup {V : X.Opens | IsIso (f ∣_ V)} := x.2
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hx
  refine ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))]
  change IsIso (f ∣_ U.ι ''ᵁ U.ι ⁻¹ᵁ V)
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr (le_sSup hV)]

private lemma isIso_morphismRestrict_of_le {X Y : Scheme} (f : Y ⟶ X)
    (U V : X.Opens) (hVU : V ≤ U) (hU : IsIso (f ∣_ U)) :
    IsIso (f ∣_ V) := by
  let W := U.ι ⁻¹ᵁ V
  have hW : IsIso ((f ∣_ U) ∣_ W) := inferInstance
  change (MorphismProperty.isomorphisms Scheme) ((f ∣_ U) ∣_ W) at hW
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U W)] at hW
  change IsIso (f ∣_ U.ι ''ᵁ U.ι ⁻¹ᵁ V) at hW
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr hVU] at hW

private lemma isDiscreteValuationRing_stalk_of_codimension_eq_one
    {X : Scheme} [IsLocallyNoetherian X] [IsNormal X]
    (x : X) (hx : codimension (IrreducibleCloseds.closureSingleton x) = 1) :
    ∃ _ : IsDomain (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x) := by
  apply ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp
  refine ⟨inferInstance, inferInstance, inferInstance,
    IsNormal.stalk_normal x, ?_⟩
  rw [ringKrullDim_stalk_eq_coheight,
    ← Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight, hx]
  rfl

private lemma isIso_of_finite_fibres {X Y : Scheme} [IsNoetherian X]
    [IsNormal X] [IsReduced Y] (f : Y ⟶ X) [IsProper f]
    (hf : IsBirational f) (hfin : ∀ x : X, (f ⁻¹' {x}).Finite) :
    IsIso f := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  have := IsNormal.stalk_normal x
  exact AlgebraicGeometry.exists_isIso_restrict_of_finite_fiber_of_normal
    f hf x (hfin x)

private lemma isClosed_singleton_of_le_codimension {X : Scheme} (n : ℕ)
    (hdim : topologicalKrullDim X ≤ n) (x : X)
    (hx : (n : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    IsClosed ({x} : Set X) := by
  let : PartialOrder X := specializationOrder X
  rw [Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight] at hx
  have hdim' : Order.krullDim X ≤ n := by
    rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  have hbound (y : X) : Order.coheight y ≤ (n : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim y).trans hdim'
  apply isClosed_of_closure_subset
  intro y hy
  change y = x
  by_contra hne
  have hyx : y < x := lt_of_le_of_ne (specializes_iff_mem_closure.mpr hy) hne
  have hfin : Order.coheight x < ⊤ := (hbound x).trans_lt (by simp)
  exact not_lt_of_ge ((hbound y).trans hx) (Order.coheight_strictAnti hyx hfin)

private alias finite_of_isClosed_of_closedPoints := finite_of_forall_isClosed_singleton

private lemma exists_finite_exceptional_set {X Y : Scheme} [IsNoetherian X]
    [IsNormal X] [IsReduced Y] (f : Y ⟶ X) [IsProper f]
    (hf : IsBirational f) (hdim : topologicalKrullDim X ≤ 2) :
    ∃ U : X.Opens, IsIso (f ∣_ U) ∧
      (Uᶜ : Set X).Finite ∧ (∀ x ∉ U, IsClosed ({x} : Set X)) ∧
      (∀ x ∉ U, ¬ (f ⁻¹' {x}).Finite) ∧
      ∀ x ∈ genericPoints X, x ∈ U := by
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open f
  have hclosed (x : X) (hx : x ∉ U) : IsClosed ({x} : Set X) := by
    apply isClosed_singleton_of_le_codimension 2 hdim x
    have hzero : codimension (IrreducibleCloseds.closureSingleton x) ≠ 0 := fun h =>
      hx (mem_maximal_isomorphism_open_of_mem_genericPoints f hf U hU x
        (mem_genericPoints_of_codimension_eq_zero h))
    have hone : codimension (IrreducibleCloseds.closureSingleton x) ≠ 1 := fun h =>
      hx (mem_maximal_isomorphism_open_of_codimension_eq_one_of_isDiscreteValuationRing
        f hf U hU.1 hU.2 x h (isDiscreteValuationRing_stalk_of_codimension_eq_one x h))
    cases he : codimension (IrreducibleCloseds.closureSingleton x) with
    | top => simp
    | coe n =>
      rw [he] at hzero hone
      norm_cast at hzero hone ⊢
      omega
  refine ⟨U, hU.1, finite_of_isClosed_of_closedPoints U.isOpen.isClosed_compl hclosed,
    hclosed, ?_, ?_⟩
  · intro x hx hfinite
    have := IsNormal.stalk_normal x
    obtain ⟨V, hxV, hV⟩ :=
      AlgebraicGeometry.exists_isIso_restrict_of_finite_fiber_of_normal
        f hf x hfinite
    exact hx (hU.2 hV hxV)
  · intro x hx
    exact mem_maximal_isomorphism_open_of_mem_genericPoints f hf U hU x hx

private lemma exists_common_finite_isomorphism_open
    {X Y Z : Scheme} [IsNoetherian X] [IsNormal X]
    [IsReduced Y] [IsReduced Z] (f : Y ⟶ X) (g : Z ⟶ X)
    [IsProper f] [IsProper g] (hf : IsBirational f)
    (hg : IsBirational g) (hdim : topologicalKrullDim X ≤ 2) :
    ∃ U : X.Opens, IsIso (f ∣_ U) ∧ IsIso (g ∣_ U) ∧
      (Uᶜ : Set X).Finite ∧ ∀ x ∈ genericPoints X, x ∈ U := by
  obtain ⟨U, hUf, hUfin, _, _, hUgen⟩ :=
    exists_finite_exceptional_set f hf hdim
  obtain ⟨V, hVg, hVfin, _, _, hVgen⟩ :=
    exists_finite_exceptional_set g hg hdim
  refine ⟨U ⊓ V,
    isIso_morphismRestrict_of_le f U (U ⊓ V) inf_le_left hUf,
    isIso_morphismRestrict_of_le g V (U ⊓ V) inf_le_right hVg, ?_, ?_⟩
  · simpa [Set.compl_inter] using hUfin.union hVfin
  · exact fun x hx => ⟨hUgen x hx, hVgen x hx⟩

private theorem exists_common_open_pullback_map
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (U : X.Opens) (hg : IsIso (g ∣_ U)) :
    ∃ r : (f ⁻¹ᵁ U).toScheme ⟶ Limits.pullback f g,
      r ≫ Limits.pullback.fst f g = (f ⁻¹ᵁ U).ι ∧
      r ≫ Limits.pullback.snd f g =
        (f ∣_ U) ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι := by
  let k : (f ⁻¹ᵁ U).toScheme ⟶ Z :=
    (f ∣_ U) ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι
  have hc : (f ⁻¹ᵁ U).ι ≫ f = k ≫ g := by
    calc
      (f ⁻¹ᵁ U).ι ≫ f = (f ∣_ U) ≫ U.ι := (morphismRestrict_ι f U).symm
      _ = (f ∣_ U) ≫ inv (g ∣_ U) ≫ ((g ∣_ U) ≫ U.ι) := by
        simp only [IsIso.inv_hom_id_assoc]
      _ = k ≫ g := by
        simp only [k, Category.assoc, ← morphismRestrict_ι g U]
  exact ⟨Limits.pullback.lift (f ⁻¹ᵁ U).ι k hc, Limits.pullback.lift_fst _ _ _,
    Limits.pullback.lift_snd _ _ _⟩

/-- The projection of a pullback square to its second factor is an isomorphism over an open of the
base on which the first leg is. -/
private lemma isIso_snd_morphismRestrict_of_isPullback
    {P X Y S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hP : IsPullback fst snd f g) (U : S.Opens) (hf : IsIso (f ∣_ U)) :
    IsIso (snd ∣_ (g ⁻¹ᵁ U)) := by
  have h := Scheme.Hom.isPullback_resLE hP
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U) le_rfl le_rfl
    (UY := snd ⁻¹ᵁ g ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hP.w]
      exact (inf_idem _).symm)
  have : IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    h.isIso_snd_of_isIso

private lemma isIso_pullback_fst_over_open
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (hg : IsIso (g ∣_ U)) :
    IsIso (Limits.pullback.fst f g ∣_ (f ⁻¹ᵁ U)) :=
  isIso_snd_morphismRestrict_of_isPullback (IsPullback.of_hasPullback f g).flip U hg

private lemma isIso_pullback_snd_over_open
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : S.Opens) (hf : IsIso (f ∣_ U)) :
    IsIso (Limits.pullback.snd f g ∣_ (g ⁻¹ᵁ U)) :=
  isIso_snd_morphismRestrict_of_isPullback (IsPullback.of_hasPullback f g) U hf

/-- **The second projection of a fibre product is an isomorphism over an open on which the first
morphism is one.** The restriction of `pullback f g ⟶ Y` to the inverse image of `U` is a base
change of the restriction of `f` to `U`, so it inherits being an isomorphism.

This is stated for the library rather than privately because the same step is wanted verbatim by
`AlgebraicGeometry.isIso_morphismRestrict_strictTransformToBlowUp`, which repeats it as a `have`
in a file that may not edit this one. -/
public alias isIso_pullback_snd_restrict_preimage_of_isIso_restrict := isIso_pullback_snd_over_open

/-- A section of a morphism over an open is an isomorphism onto the inverse image of that open
followed by the inclusion. -/
private lemma exists_isIso_comp_ι_eq_of_section_over_open
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (hf : IsIso (f ∣_ U)) (s : U.toScheme ⟶ Y)
    (hs : s ≫ f = U.ι) :
    ∃ t : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme, IsIso t ∧ t ≫ (f ⁻¹ᵁ U).ι = s := by
  let t : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
    (isPullback_morphismRestrict f U).lift (𝟙 _) s (by simpa using hs.symm)
  have ht : t ≫ (f ∣_ U) = 𝟙 _ := (isPullback_morphismRestrict f U).lift_fst _ _ _
  have : IsIso (t ≫ (f ∣_ U)) := ht ▸ inferInstance
  exact ⟨t, IsIso.of_isIso_comp_right t (f ∣_ U),
    (isPullback_morphismRestrict f U).lift_snd _ _ _⟩

/-- A section of a morphism over an open on which it is an isomorphism
identifies that open with its inverse image. -/
private lemma isOpenImmersion_of_section_over_iso_open
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (hf : IsIso (f ∣_ U)) (s : U.toScheme ⟶ Y)
    (hs : s ≫ f = U.ι) : IsOpenImmersion s := by
  obtain ⟨t, _, rfl⟩ := exists_isIso_comp_ι_eq_of_section_over_open f U hf s hs
  infer_instance

private lemma opensRange_section_over_iso_open
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (hf : IsIso (f ∣_ U)) (s : U.toScheme ⟶ Y)
    [IsOpenImmersion s] (hs : s ≫ f = U.ι) :
    s.opensRange = f ⁻¹ᵁ U := by
  obtain ⟨t, _, rfl⟩ := exists_isIso_comp_ι_eq_of_section_over_open f U hf s hs
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

private lemma isIso_morphismRestrict_opensRange_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso (f ∣_ f.opensRange) := by
  refine (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective]
  intro y
  obtain ⟨x, hx⟩ := y.2
  let z : (f ⁻¹ᵁ f.opensRange).toScheme := ⟨x, by
    change f x ∈ f.opensRange
    exact ⟨x, rfl⟩⟩
  exact ⟨z, Subtype.ext (by simpa only [morphismRestrict_base_coe] using hx)⟩

private lemma eq_of_le_of_not_isMin_of_not_isMax {α : Type*} [PartialOrder α]
    (hdim : Order.krullDim α ≤ 2) {a b : α} (hab : a ≤ b)
    (ha : ¬ IsMin a) (hb : ¬ IsMax b) : a = b := by
  by_contra hne
  obtain ⟨c, hc⟩ := not_isMin_iff.mp ha
  obtain ⟨d, hd⟩ := not_isMax_iff.mp hb
  let s : LTSeries α := ⟨3, ![c, a, b, d], by
    intro i
    fin_cases i
    · simpa using hc
    · simpa using lt_of_le_of_ne hab hne
    · simpa using hd⟩
  have h := (Order.LTSeries.length_le_krullDim s).trans hdim
  norm_num [s] at h

private lemma isClosed_singleton_of_isMin {X : Scheme} {x : X} (hx : IsMin x) :
    IsClosed ({x} : Set X) := by
  apply isClosed_of_closure_subset
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  exact ((specializes_iff_mem_closure.mpr hy).antisymm (hx hyx)).eq.symm

/-- Every point is a specialization of a generic point. -/
private lemma exists_mem_genericPoints_specializes {α : Type*} [TopologicalSpace α]
    [QuasiSober α] (x : α) : ∃ η ∈ genericPoints α, η ⤳ x :=
  ⟨_, (genericPoints.ofComponent ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩).2,
    (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent⟩

private lemma mem_genericPoints_of_isMax {X : Scheme} {x : X} (hx : IsMax x) :
    x ∈ genericPoints X := by
  obtain ⟨η, hη, hηx⟩ := exists_mem_genericPoints_specializes x
  exact (hηx.antisymm (hx hηx)).eq ▸ hη

private lemma finite_nonclosed_points_of_closed_disjoint_genericPoints
    {X : Scheme} [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 2)
    {E : Set X} (hE : IsClosed E) (hgen : Disjoint E (genericPoints X)) :
    {x ∈ E | ¬ IsClosed ({x} : Set X)}.Finite := by
  let : PartialOrder X := specializationOrder X
  have : QuasiSober E := hE.isClosedEmbedding_subtypeVal.quasiSober
  have hfin : (genericPoints E).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  apply (hfin.image (Subtype.val : E → X)).subset
  rintro x ⟨hxE, hx⟩
  obtain ⟨η, hη, hηz⟩ := exists_mem_genericPoints_specializes (⟨x, hxE⟩ : E)
  have hηx : η.1 ⤳ x := hηz.map continuous_subtype_val
  have hdim' : Order.krullDim X ≤ 2 := by
    rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  have heq : x = η.1 := eq_of_le_of_not_isMin_of_not_isMax hdim' hηx
    (fun h => hx (isClosed_singleton_of_isMin h))
    (fun h => Set.disjoint_left.mp hgen η.2 (mem_genericPoints_of_isMax h))
  exact ⟨η, hη, heq.symm⟩

/-- Two points of the source with the same image in an open on which `f` is an isomorphism
are equal. -/
private lemma eq_of_map_eq_of_isIso_restrict {X Y : Scheme} (f : Y ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (y z : Y) (hy : f y ∈ U) (hz : f z ∈ U) (h : f y = f z) : y = z :=
  congrArg Subtype.val ((f ∣_ U).homeomorph.injective <| Subtype.ext <|
    (morphismRestrict_base_coe f U ⟨y, hy⟩).trans
      (h.trans (morphismRestrict_base_coe f U ⟨z, hz⟩).symm))

private lemma isClosed_singleton_of_isIso_restrict {X Y : Scheme} (f : Y ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (y : Y) (hy : f y ∈ U)
    (hfy : IsClosed ({f y} : Set X)) : IsClosed ({y} : Set Y) := by
  have heq : f ⁻¹' {f y} = {y} := by
    ext z
    change f z = f y ↔ z = y
    exact ⟨fun hz => eq_of_map_eq_of_isIso_restrict f U z y (hz ▸ hy) hy hz,
      fun hz => congrArg f hz⟩
  rw [← heq]
  exact hfy.preimage f.continuous

private lemma genericPoint_mem_dense_open {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (U : Opens X) (hU : Dense (U : Set X))
    (x : X) (hx : x ∈ genericPoints X) : x ∈ U := by
  obtain ⟨V, hV, hVne, hVC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hx
  obtain ⟨y, hyV, hyU⟩ := (dense_iff_inter_open.mp hU) V hV hVne
  have hxy : Specializes x y :=
    (genericPoints.isGenericPoint ⟨x, hx⟩).specializes (hVC hyV)
  exact hxy.mem_open U.isOpen hyU

private lemma finite_contracted_nonclosed_points
    {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    [IsReduced Y] (f : Y ⟶ X) [IsProper f]
    (hf : IsBirational f) (hdim : topologicalKrullDim Y ≤ 2) :
    {y : Y | ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({f y} : Set X)}.Finite := by
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open f
  have : IsIso (f ∣_ U) := hU.1
  apply (finite_nonclosed_points_of_closed_disjoint_genericPoints hdim
    (U.isOpen.isClosed_compl.preimage f.continuous) ?_).subset
  · exact fun y hy =>
      ⟨fun hfy => hy.1 (isClosed_singleton_of_isIso_restrict f U y hfy hy.2), hy.1⟩
  · refine Set.disjoint_left.mpr fun y hy hyg => ?_
    exact hy (mem_maximal_isomorphism_open_of_mem_genericPoints f hf U hU (f y)
      (hf.bijOn.mapsTo hyg))

private lemma isIso_of_no_contracted_nonclosed_points
    {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    [IsNormal X] [IsReduced Y] (f : Y ⟶ X) [IsProper f]
    (hf : IsBirational f) (hdim : topologicalKrullDim X ≤ 2)
    (hcurves : ∀ y : Y, IsClosed ({f y} : Set X) → IsClosed ({y} : Set Y)) :
    IsIso f := by
  obtain ⟨U, hUiso, _, hclosed, hnotfinite, _⟩ := exists_finite_exceptional_set f hf hdim
  obtain rfl : U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    by_contra hx
    apply hnotfinite x hx
    apply finite_of_isClosed_of_closedPoints ((hclosed x hx).preimage f.continuous)
    intro y hy
    obtain rfl : f y = x := hy
    exact hcurves y (hclosed _ hx)
  exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) fun _ => ⟨⊤, trivial, hUiso⟩

private lemma injOn_preimage_nonclosed_points
    {X Y : Scheme} [IsNoetherian X] [IsNormal X] [IsReduced Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (hdim : topologicalKrullDim X ≤ 2) :
    Set.InjOn f {y : Y | ¬ IsClosed ({f y} : Set X)} := by
  obtain ⟨U, hUiso, _, hclosed, _, _⟩ := exists_finite_exceptional_set f hf hdim
  have := hUiso
  intro y hy z hz hyz
  have hyU : f y ∈ U := by_contra fun h => hy (hclosed (f y) h)
  have hzU : f z ∈ U := hyz ▸ hyU
  exact eq_of_map_eq_of_isIso_restrict f U y z hyU hzU hyz

private lemma isIso_stalkMap_over_nonclosed_point
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNormal X] [IsReduced Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (hdim : topologicalKrullDim X ≤ 2) (y : Y)
    (hy : ¬ IsClosed ({f y} : Set X)) : IsIso (f.stalkMap y) := by
  obtain ⟨U, hUiso, _, hclosed, _, _⟩ :=
    exists_finite_exceptional_set f hf hdim
  have hyU : f y ∈ U := by_contra fun h => hy (hclosed (f y) h)
  let y': (f ⁻¹ᵁ U).toScheme := ⟨y, hyU⟩
  exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
    (morphismRestrictStalkMap f U y')).mp
      (((isIso_iff_isIso_stalkMap (f ∣_ U)).mp hUiso).2 y')

private lemma isClosed_singleton_of_locallyQuasiFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) (hx : IsClosed ({f x} : Set Y)) :
    IsClosed ({x} : Set X) := by
  apply isClosed_of_closure_subset
  intro z hz
  have hspec : x ⤳ z := specializes_iff_mem_closure.mpr hz
  have hfz : f z = f x := by
    have hmem := specializes_iff_mem_closure.mp (hspec.map f.continuous)
    rwa [hx.closure_eq] at hmem
  exact ((f.isDiscrete_preimage_singleton (f x)).eq_of_specializes hspec rfl hfz).symm

private lemma isFinite_fromSpecResidueField_comp_of_isProper {X S : Scheme.{u}}
    (q : X ⟶ S) [IsProper q] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsFinite (X.fromSpecResidueField x ≫ q) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : LocallyQuasiFinite (X.fromSpecResidueField x ≫ q) :=
    .of_injective (fun _ _ _ => Subsingleton.elim _ _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

private lemma isFinite_fiberι_comp_of_finite_comparison
    {X X' Y Z : Scheme.{u}} (f : Y ⟶ X) (q : X' ⟶ X)
    (p : Z ⟶ Y) (g : Z ⟶ X') (h : p ≫ f = g ≫ q)
    [IsFinite (Limits.pullback.lift p g h)] [IsProper q]
    (x : X') (hx : IsClosed ({x} : Set X')) :
    IsFinite (g.fiberι x ≫ p) := by
  let i := X'.fromSpecResidueField x
  let r := Limits.pullback.lift p g h
  let k : Limits.pullback g i ⟶ Limits.pullback (Limits.pullback.snd f q) i :=
    Limits.pullback.lift (Limits.pullback.fst g i ≫ r) (Limits.pullback.snd g i) (by
      simp only [Category.assoc, r, Limits.pullback.lift_snd, Limits.pullback.condition])
  have hk : IsFinite k :=
    MorphismProperty.pullbackLift_fst_snd (P := @IsFinite) i
      (Limits.pullback.lift_snd p g h).symm inferInstance
  let e := Limits.pullbackLeftPullbackSndIso f q i
  have : IsFinite (i ≫ q) := isFinite_fromSpecResidueField_comp_of_isProper q x hx
  have heq : k ≫ e.hom ≫ Limits.pullback.fst f (i ≫ q) = g.fiberι x ≫ p := by
    rw [Limits.pullbackLeftPullbackSndIso_hom_fst]
    simp only [k, r, Limits.pullback.lift_fst_assoc, Category.assoc, Limits.pullback.lift_fst]
    rfl
  rw [← heq]
  apply MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsFinite) k _ hk
  apply MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsFinite) e.hom _
  · dsimp only [e]
    infer_instance
  · infer_instance

private lemma nonclosed_image_of_finite_comparison
    {X X' Y Z : Scheme.{u}} (f : Y ⟶ X) (q : X' ⟶ X)
    (p : Z ⟶ Y) (g : Z ⟶ X') (h : p ≫ f = g ≫ q)
    [IsFinite (Limits.pullback.lift p g h)] [IsProper q]
    (z : Z) (hz : ¬ IsClosed ({z} : Set Z))
    (hgz : IsClosed ({g z} : Set X')) : ¬ IsClosed ({p z} : Set Y) := by
  intro hpz
  have : IsClosedImmersion (X'.fromSpecResidueField (g z)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hgz
  have : IsFinite (g.fiberι (g z) ≫ p) :=
    isFinite_fiberι_comp_of_finite_comparison f q p g h (g z) hgz
  have hclosed : IsClosed ({g.asFiber z} : Set (g.fiber (g z))) := by
    apply isClosed_singleton_of_locallyQuasiFinite (g.fiberι (g z) ≫ p)
    simpa using hpz
  have : IsClosedImmersion (g.fiberι (g z)) := by
    change IsClosedImmersion (Limits.pullback.fst g (X'.fromSpecResidueField (g z)))
    infer_instance
  apply hz
  simpa only [Set.image_singleton, Scheme.Hom.fiberι_asFiber] using
    (g.fiberι (g z)).isClosedMap _ hclosed

private lemma mapsTo_contracted_nonclosed_points
    {X X' Y Y' : Scheme} (f : Y ⟶ X) (f' : Y' ⟶ X')
    (p : Y' ⟶ Y) (q : X' ⟶ X) (hcomm : p ≫ f = f' ≫ q)
    (hq : IsClosedMap q)
    (hp : ∀ y : Y', ¬ IsClosed ({y} : Set Y') → IsClosed ({f' y} : Set X') →
      ¬ IsClosed ({p y} : Set Y)) :
    Set.MapsTo p
      {y : Y' | ¬ IsClosed ({y} : Set Y') ∧ IsClosed ({f' y} : Set X')}
      {y : Y | ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({f y} : Set X)} := by
  intro y hy
  refine ⟨hp y hy.1 hy.2, ?_⟩
  have hc : f (p y) = q (f' y) := congrArg (fun (r : Y' ⟶ X) => r y) hcomm
  rw [hc]
  simpa only [Set.image_singleton] using hq ({f' y} : Set X') hy.2

private lemma mapsTo_contracted_points_of_finite_comparison
    {X X' Y Y' : Scheme.{u}} (f : Y ⟶ X) (g : Y' ⟶ X')
    (p : Y' ⟶ Y) (q : X' ⟶ X) (h : p ≫ f = g ≫ q)
    [IsProper q] [IsFinite (Limits.pullback.lift p g h)] :
    Set.MapsTo p
      {y : Y' | ¬ IsClosed ({y} : Set Y') ∧ IsClosed ({g y} : Set X')}
      {y : Y | ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({f y} : Set X)} :=
  mapsTo_contracted_nonclosed_points f g p q h q.isClosedMap
    (nonclosed_image_of_finite_comparison f q p g h)

private lemma injOn_contracted_points_of_finite_comparison
    {X X' Y Y' : Scheme.{u}} [IsNoetherian Y] [IsNormal Y] [IsReduced Y']
    (f : Y ⟶ X) (g : Y' ⟶ X') (p : Y' ⟶ Y) (q : X' ⟶ X)
    (h : p ≫ f = g ≫ q) [IsProper p] [IsProper q]
    (hp : IsBirational p) (hdim : topologicalKrullDim Y ≤ 2)
    [IsFinite (Limits.pullback.lift p g h)] :
    Set.InjOn p {y : Y' | ¬ IsClosed ({y} : Set Y') ∧ IsClosed ({g y} : Set X')} :=
  (injOn_preimage_nonclosed_points p hp hdim).mono fun y hy =>
    nonclosed_image_of_finite_comparison f q p g h y hy.1 hy.2

private lemma finite_contracted_points_of_finite_comparison
    {X X' Y Y' : Scheme.{u}} [IsNoetherian Y] [IsNormal Y]
    [IsReduced Y'] (f : Y ⟶ X) (g : Y' ⟶ X')
    (p : Y' ⟶ Y) (q : X' ⟶ X) (h : p ≫ f = g ≫ q)
    [IsProper p] [IsProper q] (hp : IsBirational p)
    (hdim : topologicalKrullDim Y ≤ 2)
    [IsFinite (Limits.pullback.lift p g h)]
    (ht : {y : Y | ¬ IsClosed ({y} : Set Y) ∧
      IsClosed ({f y} : Set X)}.Finite) :
    {y : Y' | ¬ IsClosed ({y} : Set Y') ∧
      IsClosed ({g y} : Set X')}.Finite ∧
      {y : Y' | ¬ IsClosed ({y} : Set Y') ∧
        IsClosed ({g y} : Set X')}.ncard ≤
      {y : Y | ¬ IsClosed ({y} : Set Y) ∧
        IsClosed ({f y} : Set X)}.ncard := by
  let s : Set Y' := {y | ¬ IsClosed ({y} : Set Y') ∧ IsClosed ({g y} : Set X')}
  let t : Set Y := {y | ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({f y} : Set X)}
  have hm : Set.MapsTo p s t :=
    mapsTo_contracted_points_of_finite_comparison f g p q h
  have hi : Set.InjOn p s :=
    injOn_contracted_points_of_finite_comparison f g p q h hp hdim
  have hs : s.Finite := Set.Finite.of_finite_image
    (ht.subset (Set.image_subset_iff.mpr hm)) hi
  exact ⟨hs, hi.ncard_image.symm.trans_le (Set.ncard_le_ncard (Set.image_subset_iff.mpr hm) ht)⟩

private lemma ncard_lt_of_injOn_with_missing_image
    {α β : Type*} {s : Set α} {t : Set β} (ht : t.Finite)
    (f : α → β) (hmaps : Set.MapsTo f s t) (hinj : Set.InjOn f s)
    (b : β) (hb : b ∈ t) (hmiss : b ∉ f '' s) :
    s.ncard < t.ncard := by
  have hsub : f '' s ⊆ t := Set.image_subset_iff.mpr hmaps
  have hproper : f '' s ⊂ t :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hmiss (heq.symm ▸ hb)⟩
  rw [← hinj.ncard_image]
  exact Set.ncard_lt_ncard hproper ht


/-! ### Tails of normalized point blowups

A tail records just the normalized point blowups after a specified initial scheme, so that the
induction can be run over the normalization of the base and the resulting sequence assembled
into a chain afterwards.
-/

/-- A finite sequence of normalized blowups at closed points starting from `S`, indexed by the
composite morphism to `S`. -/
private inductive NormalizedBlowUpTail (S : Scheme.{u}) :
    (Z : Scheme.{u}) → (Z ⟶ S) → Prop where
  | refl : NormalizedBlowUpTail S S (𝟙 S)
  | blow {Z : Scheme.{u}} {g : Z ⟶ S}
      (s : NormalizedBlowUpTail S Z g)
      (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) →
        (irreducibleComponents U).Finite)
      (z : Z) (hz : IsClosed ({z} : Set Z)) :
      NormalizedBlowUpTail S (Stacks.Blowup.normalizedBlowUpScheme Z hZ z hz)
        (Stacks.Blowup.normalizedBlowUp Z hZ z hz ≫ g)

private theorem NormalizedBlowUpTail.trans
    {S T U : Scheme.{u}} {f : T ⟶ S} {g : U ⟶ T}
    (a : NormalizedBlowUpTail S T f)
    (b : NormalizedBlowUpTail T U g) :
    NormalizedBlowUpTail S U (g ≫ f) := by
  induction b with
  | refl => simpa using a
  | @blow Z h b hZ z hz ih =>
      simpa only [Category.assoc] using NormalizedBlowUpTail.blow ih hZ z hz

/-- Along a tail of normalized point blowups over a Nagata scheme every intermediate scheme is
again Nagata, and its morphism down to the initial scheme is proper. -/
private theorem NormalizedBlowUpTail.isNagataScheme_and_isProper
    {S Z : Scheme.{u}} {g : Z ⟶ S} (s : NormalizedBlowUpTail S Z g)
    (hS : IsNagataScheme S) : IsNagataScheme Z ∧ IsProper g := by
  induction s with
  | refl => exact ⟨hS, inferInstance⟩
  | @blow W h t hW w hw ih =>
      obtain ⟨hWnag, hhproper⟩ := ih
      have : IsProper h := hhproper
      have : IsProper (Stacks.Blowup.normalizedBlowUp W hW w hw) :=
        Stacks.Blowup.isProper_normalizedBlowUp hW w hw hWnag
      exact ⟨Stacks.Blowup.isNagataScheme_normalizedBlowUpScheme hW w hw hWnag, inferInstance⟩

/-- A tail of normalized point blowups over the normalization of a Noetherian Nagata scheme `X`
is a chain of normalized blowups over `X` itself: the normalization is proper because `X` is
Nagata, and every normalized point blowup of a Nagata scheme is proper. -/
private theorem normalizedBlowUpChain_of_tail
    {X : Scheme.{u}} (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {Z : Scheme.{u}} {g : Z ⟶ Scheme.normalizationScheme X hX}
    (s : NormalizedBlowUpTail (Scheme.normalizationScheme X hX) Z g) :
    NormalizedBlowUpChain X hX Z (g ≫ Scheme.normalization X hX) := by
  have : IsFinite (Scheme.normalization X hX) := Scheme.isFinite_normalization hNagata hX
  have hνproper : IsProper (Scheme.normalization X hX) := inferInstance
  have hNagata₀ : IsNagataScheme (Scheme.normalizationScheme X hX) :=
    isNagataScheme_of_locallyOfFiniteType (Scheme.normalization X hX) hNagata
  induction s with
  | refl => simpa using NormalizedBlowUpChain.normalization hνproper
  | @blow W h t hW w hw ih =>
      obtain ⟨hWnag, hhproper⟩ := t.isNagataScheme_and_isProper hNagata₀
      have : IsProper h := hhproper
      have : IsProper (Stacks.Blowup.normalizedBlowUp W hW w hw) :=
        Stacks.Blowup.isProper_normalizedBlowUp hW w hw hWnag
      have hcomp : IsProper (Stacks.Blowup.normalizedBlowUp W hW w hw ≫
          (h ≫ Scheme.normalization X hX)) := inferInstance
      simpa only [Category.assoc] using NormalizedBlowUpChain.blowUp ih hW w hw hcomp

/-- Assemble a chain over `X` from a tail over the normalization of `X` that dominates a
morphism factoring through the normalization. -/
private theorem exists_normalizedBlowUpChain_dominating_of_tail
    {X Y : Scheme.{u}} (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (f : Y ⟶ X)
    (l : Y ⟶ Scheme.normalizationScheme X hX)
    (hl : l ≫ Scheme.normalization X hX = f)
    (hfactor : ∃ (Z : Scheme.{u})
        (g : Z ⟶ Scheme.normalizationScheme X hX),
      NormalizedBlowUpTail (Scheme.normalizationScheme X hX) Z g ∧
        ∃ h : Z ⟶ Y, h ≫ l = g) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ Y),
      NormalizedBlowUpChain X hX Z g ∧ h ≫ f = g := by
  obtain ⟨Z, g, hs, h, hh⟩ := hfactor
  refine ⟨Z, g ≫ Scheme.normalization X hX, h,
    normalizedBlowUpChain_of_tail hNagata hX hs, ?_⟩
  rw [← hl, ← hh, Category.assoc]

/-- An isomorphism is dominated by the normalization alone. -/
private theorem exists_normalizedBlowUpChain_dominating_of_isIso
    {X Y : Scheme.{u}} (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (f : Y ⟶ X) [IsIso f] :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ Y),
      NormalizedBlowUpChain X hX Z g ∧ h ≫ f = g := by
  have : IsFinite (Scheme.normalization X hX) := Scheme.isFinite_normalization hNagata hX
  refine ⟨Scheme.normalizationScheme X hX, Scheme.normalization X hX,
    Scheme.normalization X hX ≫ (asIso f).inv,
    NormalizedBlowUpChain.normalization inferInstance, ?_⟩
  simp

@[ega "IV 4.4.1" "special case"]
private theorem finite_irreducibleComponents_of_isProper
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] :
    ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite := by
  have : IsNoetherian Y := isNoetherian_of_isProper_over_noetherian f
  exact finite_irreducibleComponents_isCompactOpen_of_isNoetherian

private lemma finite_contracted_nonclosed_points_of_isIntegral
    {X Y : Scheme} [IsNoetherian X] [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (hdim : topologicalKrullDim X ≤ 2) :
    {y : Y | ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({f y} : Set X)}.Finite := by
  have : IsNoetherian Y := isNoetherian_of_isProper_over_noetherian f
  exact finite_contracted_nonclosed_points f hf
    ((topologicalKrullDim_le_of_isBirational f hf).trans hdim)

private theorem normalized_point_blowup_preserves_admissibility
    {X : Scheme.{u}} [IsNoetherian X] (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsNagataScheme (Stacks.Blowup.normalizedBlowUpScheme X hX x hx) ∧
      (∀ U : (Stacks.Blowup.normalizedBlowUpScheme X hX x hx).Opens,
        IsCompact (U : Set (Stacks.Blowup.normalizedBlowUpScheme X hX x hx)) →
          (irreducibleComponents U).Finite) := by
  let f := Stacks.Blowup.normalizedBlowUp X hX x hx
  let : IsProper f := Stacks.Blowup.isProper_normalizedBlowUp hX x hx hNagata
  have : IsNoetherian (Stacks.Blowup.normalizedBlowUpScheme X hX x hx) :=
    isNoetherian_of_isProper_over_noetherian f
  refine ⟨Stacks.Blowup.isNagataScheme_normalizedBlowUpScheme hX x hx hNagata, ?_⟩
  exact finite_irreducibleComponents_of_isProper f

/-- The normalization of a scheme proper over a Noetherian Nagata scheme is finite. -/
private theorem isFinite_normalization_of_isProper_to_nagata
    {X Y : Scheme.{u}} [IsNoetherian X] (hNagata : IsNagataScheme X)
    (f : Y ⟶ X) [IsProper f]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite) :
    IsFinite (Scheme.normalization Y hY) := by
  have : IsNoetherian Y := isNoetherian_of_isProper_over_noetherian f
  exact Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType f hNagata) hY

private theorem isProper_normalization_of_isProper_to_nagata
    {X Y : Scheme.{u}} [IsNoetherian X] (hNagata : IsNagataScheme X)
    (f : Y ⟶ X) [IsProper f]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite) :
    IsProper (Scheme.normalization Y hY) :=
  have := isFinite_normalization_of_isProper_to_nagata hNagata f hY
  inferInstance

private theorem normalization_isProper_and_birational_of_isProper_to_nagata
    {X Y : Scheme.{u}} [IsNoetherian X] (hNagata : IsNagataScheme X)
    (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite) :
    IsProper (Scheme.normalization Y hY) ∧
      IsBirational (Scheme.normalization Y hY) :=
  ⟨isProper_normalization_of_isProper_to_nagata hNagata f hY,
    AlgebraicGeometry.Scheme.isBirational_normalization Y hY⟩

private theorem exists_lift_to_normalization_of_isNormal
    {X Y : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (f : Y ⟶ X) [IsNormal Y]
    (hf : IsBirational f) :
    ∃ g : Y ⟶ Scheme.normalizationScheme X hX,
      g ≫ Scheme.normalization X hX = f := by
  obtain ⟨g, hg, _⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_lift_normalization
      hX f (fun η => (hf.1).1 η.2)
  exact ⟨g, hg⟩

private theorem exists_factor_through_blowUp_of_effective_cartier
    {X Z : Scheme.{u}} (I : X.IdealSheafData) (p : Z ⟶ X)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor
      (I.comap p)) :
    ∃ q : Z ⟶ (AlgebraicGeometry.blowUp I),
      q ≫ (AlgebraicGeometry.blowUpToBase I) = p := by
  obtain ⟨_, ⟨hterminal⟩⟩ := Stacks.Blowup.isTerminal_blowUp I
  let φ := hterminal.from (⟨Over.mk p, hI⟩ : Stacks.Blowup.CartierOver I)
  exact ⟨φ.hom.left, Over.w φ.hom⟩

private theorem blowUp_of_comap_factors_through_blowUp
    {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) :
    ∃ q : (AlgebraicGeometry.blowUp (I.comap f)) ⟶
        (AlgebraicGeometry.blowUp I),
      q ≫ (AlgebraicGeometry.blowUpToBase I) =
        (AlgebraicGeometry.blowUpToBase (I.comap f)) ≫ f := by
  let J := I.comap f
  obtain ⟨hJ, _⟩ := Stacks.Blowup.isTerminal_blowUp J
  let b : (AlgebraicGeometry.blowUp J) ⟶ Y := by
    simpa [AlgebraicGeometry.blowUp, reesSituation] using
      (AlgebraicGeometry.blowUpToBase J)
  have hJ' : Stacks.Divisors.IsEffectiveCartierDivisor
      (J.comap b) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      (J.comap (AlgebraicGeometry.blowUpToBase J)) at hJ
    simpa [b, AlgebraicGeometry.blowUp, reesSituation] using hJ
  have hpull : Stacks.Divisors.IsEffectiveCartierDivisor
      (I.comap (b ≫ f)) := by
    rwa [Scheme.IdealSheafData.comap_comp]
  exact exists_factor_through_blowUp_of_effective_cartier I
    (b ≫ f) hpull

private lemma isBirational_blowUp_of_genericPoints_disjoint_support
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (hgeneric : Disjoint (genericPoints X) I.supportSet) :
    IsBirational (AlgebraicGeometry.blowUpToBase I) := by
  let b := (AlgebraicGeometry.blowUpToBase I)
  let U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  have hgen (x : X) (hx : x ∈ genericPoints X) : x ∈ U := Set.disjoint_left.mp hgeneric hx
  have hbU : IsIso (b ∣_ U) :=
    AlgebraicGeometry.isIso_blowUp_restrict_compl_support I
  obtain ⟨hmap, -⟩ := AlgebraicGeometry.bijOn_genericPoints_blowUpToBase I
  exact isBirational_of_isIso_morphismRestrict b U hbU (fun x hx => hgen _ (hmap hx).1) hgen

private lemma isBirational_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : IsBirational f)
    (hg : IsBirational g) : IsBirational (f ≫ g) := by
  refine ⟨hg.bijOn.comp hf.bijOn, fun x hx => ?_⟩
  rw [Scheme.Hom.stalkMap_comp]
  exact IsIso.comp_isIso' (hg.isIso_stalkMap (f x) (hf.bijOn.mapsTo hx))
    (hf.isIso_stalkMap x hx)

private lemma isBirational_normalizedBlowUp_of_genericPoints_disjoint_center
    {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hgeneric : Disjoint (genericPoints X) ({x} : Set X)) :
    IsBirational (Stacks.Blowup.normalizedBlowUp X hX x hx) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have hsupport : I.supportSet = ({x} : Set X) := by
    change ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : Closeds X)).support : Set X) = {x}
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hBlowUp : IsBirational (AlgebraicGeometry.blowUpToBase I) :=
    isBirational_blowUp_of_genericPoints_disjoint_support I
      (hsupport ▸ hgeneric)
  have : IsReduced (AlgebraicGeometry.blowUp I) :=
    AlgebraicGeometry.isReduced_blowUp I
  have hNorm : IsBirational
      (Scheme.normalization (AlgebraicGeometry.blowUp I)
        (Stacks.Blowup.finite_irreducibleComponents_blowUp I hX)) :=
    AlgebraicGeometry.Scheme.isBirational_normalization _ _
  change IsBirational
    (Scheme.normalization (AlgebraicGeometry.blowUp I)
      (Stacks.Blowup.finite_irreducibleComponents_blowUp I hX) ≫
      (AlgebraicGeometry.blowUpToBase I))
  exact isBirational_comp _ _ hNorm hBlowUp

private theorem lift_to_normalizedBlowUp_of_normal
    {X Z : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X))
    (p : Z ⟶ X) [IsNormal Z]
    (q : Z ⟶ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))
    (hq : IsBirational q)
    (hqp : q ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) = p) :
    ∃ q' : Z ⟶ Stacks.Blowup.normalizedBlowUpScheme X hX x hx,
      q' ≫ Stacks.Blowup.normalizedBlowUp X hX x hx = p := by
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  let hBlowUp : ∀ U : (AlgebraicGeometry.blowUp J).Opens,
      IsCompact (U : Set (AlgebraicGeometry.blowUp J)) →
        (irreducibleComponents U).Finite :=
    Stacks.Blowup.finite_irreducibleComponents_blowUp J hX
  obtain ⟨q', hq'⟩ := exists_lift_to_normalization_of_isNormal hBlowUp q hq
  refine ⟨q', ?_⟩
  change (q' ≫ Scheme.normalization (AlgebraicGeometry.blowUp J) hBlowUp) ≫
    (AlgebraicGeometry.blowUpToBase J) = p
  rwa [hq']

private theorem exists_factor_through_normalized_pointBlowUp_of_effectiveCartier
    {X Z : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X))
    (p : Z ⟶ X) [IsNormal Z]
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).comap p))
    (hbirational : ∀ q : Z ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)),
        q ≫ AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) = p →
          IsBirational q) :
    ∃ q' : Z ⟶ Stacks.Blowup.normalizedBlowUpScheme X hX x hx,
      q' ≫ Stacks.Blowup.normalizedBlowUp X hX x hx = p := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  obtain ⟨q, hqp⟩ := exists_factor_through_blowUp_of_effective_cartier I p hI
  exact lift_to_normalizedBlowUp_of_normal hX x hx p q (hbirational q hqp) hqp

private lemma bijOn_genericPoints_of_bijOn_components {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.BijOn (fun Z => closure (f '' Z))
      (irreducibleComponents X) (irreducibleComponents Y)) :
    Set.BijOn f (genericPoints X) (genericPoints Y) := by
  have hclosure (x : X) : closure (f '' closure ({x} : Set X)) = closure {f x} := by
    rw [closure_image_closure f.continuous, Set.image_singleton]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change closure {f x} ∈ irreducibleComponents Y
    rw [← hclosure]
    exact hf.mapsTo hx
  · intro x hx z hz h
    have hc : closure ({x} : Set X) = closure {z} := by
      apply hf.injOn hx hz
      simp only [hclosure, h]
    exact isGenericPoint_closure.eq hc.symm
  · intro y hy
    obtain ⟨Z, hZ, hZy⟩ := hf.surjOn hy
    let x := genericPoints.ofComponent ⟨Z, hZ⟩
    refine ⟨x.1, x.2, ?_⟩
    have hxZ : closure ({x.1} : Set X) = Z :=
      genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
    dsimp only at hZy
    rw [← hxZ, hclosure] at hZy
    exact isGenericPoint_closure.eq hZy.symm

private lemma eq_of_specializes_of_mem_genericPoints {X : Scheme.{u}} {x y : X}
    (hy : y ∈ genericPoints X) (hxy : x ⤳ y) : x = y := by
  have hle : closure ({y} : Set X) ⊆ closure {x} :=
    (isClosed_closure.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr
      (specializes_iff_mem_closure.mp hxy))
  have hge : closure ({x} : Set X) ⊆ closure {y} :=
    hy.2 isIrreducible_singleton.closure hle
  exact (hxy.antisymm (specializes_iff_mem_closure.mpr
    (hge (subset_closure (Set.mem_singleton x))))).eq

private lemma mem_genericPoints_of_locallyQuasiFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X)
    (hx : f x ∈ genericPoints Y) : x ∈ genericPoints X := by
  obtain ⟨η, hη, hηx⟩ := exists_mem_genericPoints_specializes x
  have hfη : f η = f x := eq_of_specializes_of_mem_genericPoints hx (hηx.map f.continuous)
  have heq : η = x := (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes hηx hfη rfl
  exact heq ▸ hη

private lemma bijOn_genericPoints_of_commutative_square
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (p : Y' ⟶ Y) (q : X' ⟶ X)
    (l : Y' ⟶ X') [LocallyQuasiFinite q]
    (hf : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hp : Set.BijOn p (genericPoints Y') (genericPoints Y))
    (hq : Set.BijOn q (genericPoints X') (genericPoints X))
    (hl : l ≫ q = p ≫ f) :
    Set.BijOn l (genericPoints Y') (genericPoints X') := by
  have hpt (y : Y') : q (l y) = f (p y) := congrArg (fun r : Y' ⟶ X => r y) hl
  have hmap : Set.MapsTo l (genericPoints Y') (genericPoints X') := by
    intro y hy
    apply mem_genericPoints_of_locallyQuasiFinite q
    rw [hpt]
    exact hf.mapsTo (hp.mapsTo hy)
  refine ⟨hmap, ?_, ?_⟩
  · intro y hy z hz heq
    apply hp.injOn hy hz
    apply hf.injOn (hp.mapsTo hy) (hp.mapsTo hz)
    rw [← hpt, ← hpt, heq]
  · intro x hx
    obtain ⟨y, hy, hfy⟩ := hf.surjOn (hq.mapsTo hx)
    obtain ⟨y', hy', hpy'⟩ := hp.surjOn hy
    refine ⟨y', hy', hq.injOn (hmap hy') hx ?_⟩
    rw [hpt, hpy', hfy]

private theorem genericPoints_map_normalization
    {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (η : genericPoints (Scheme.normalizationScheme X hX)) :
    Scheme.normalization X hX η.1 ∈ genericPoints X :=
  Scheme.normalization_mem_genericPoints X hX η.2

@[ega "II 6.3.9" "partial"]
private theorem isNormal_normalizationScheme
    {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) :
    IsNormal (Scheme.normalizationScheme X hX) :=
  Scheme.isNormal_normalizationScheme X hX

private lemma isNormal_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : IsNormal X) : IsNormal Y := by
  rw [isNormal_iff_stalk_normal]
  intro y
  let r := (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  have : IsDomain (X.presheaf.stalk (e.inv y)) := hX.stalk_isDomain _
  have : IsDomain (Y.presheaf.stalk y) := r.isDomain_iff.mp inferInstance
  have : IsIntegrallyClosed (X.presheaf.stalk (e.inv y)) := hX.stalk_normal _
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv r⟩

private lemma isNormal_open {X : Scheme.{u}} (U : X.Opens)
    (hX : IsNormal X) : IsNormal U.toScheme := by
  rw [isNormal_iff_stalk_normal]
  intro z
  let x := U.ι z
  let e := (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv
  have : IsDomain (X.presheaf.stalk x) := hX.stalk_isDomain x
  have hD : IsDomain (U.toScheme.presheaf.stalk z) := e.isDomain_iff.mp inferInstance
  have : IsIntegrallyClosed (X.presheaf.stalk x) := hX.stalk_normal x
  exact ⟨hD, IsIntegrallyClosed.of_equiv e⟩

private lemma normalization_restrict_isIso_of_isNormal {X : Scheme.{u}}
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) →
      (irreducibleComponents V).Finite)
    (U : X.Opens) (hU : IsNormal U.toScheme) :
    IsIso (Scheme.normalization X hX ∣_ U) := by
  have hfiniteU : ∀ V : U.toScheme.Opens, IsCompact (V : Set U.toScheme) →
      (irreducibleComponents V).Finite :=
    AlgebraicGeometry.finite_irreducibleComponents_of_smooth U.ι hX
  have hnormU : IsIso (Scheme.normalization U.toScheme hfiniteU) :=
    (AlgebraicGeometry.Scheme.isIso_normalization_iff_isNormal U.toScheme hfiniteU).2 hU
  have hpb := AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale U.ι hX
  let e := hpb.isoPullback
  have hcmp : e.hom ≫ Limits.pullback.snd
      (Scheme.normalization X hX) U.ι =
      Scheme.normalization U.toScheme hfiniteU :=
    hpb.isoPullback_hom_snd
  have hpull : IsIso (Limits.pullback.snd (Scheme.normalization X hX) U.ι) :=
    IsIso.of_isIso_fac_left (f := e.hom) hcmp
  change IsIso ((pullbackRestrictIsoRestrict (Scheme.normalization X hX) U).inv ≫
    Limits.pullback.snd (Scheme.normalization X hX) U.ι)
  infer_instance

private lemma isReduced_schemeTheoreticImage_of_isReduced
    {S P : Scheme.{u}} (r : S ⟶ P) [IsReduced S] : IsReduced r.image := by
  have hker : r.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range r)) := by
    calc
      r.ker = (⊥ : S.IdealSheafData).map r := by
        symm
        simpa [Scheme.IdealSheafData.map] using
          (Scheme.Hom.ker_comp_of_isIso ((⊥ : S.IdealSheafData).subschemeι) r)
      _ = (Scheme.IdealSheafData.vanishingIdeal
          (⊤ : TopologicalSpace.Closeds S)).map r := by
        rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
      _ = Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range r)) := by
        simpa using Scheme.IdealSheafData.map_vanishingIdeal r
          (⊤ : TopologicalSpace.Closeds S)
  change IsReduced r.ker.subscheme
  rw [hker]
  exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range r))

private lemma isIso_imageι_of_isIso
    {S P : Scheme.{u}} (r : S ⟶ P) [IsIso r] : IsIso r.imageι := by
  change IsIso r.ker.subschemeι
  exact (Scheme.isIso_subschemeι_iff_eq_bot r.ker).2 r.ker_eq_bot_of_isIso

private lemma isIso_imageι_morphismRestrict_of_isIso
    {S P : Scheme.{u}} (r : S ⟶ P) [QuasiCompact r]
    (U : P.Opens) (hU : IsIso (r ∣_ U)) :
    IsIso (r.imageι ∣_ U) := by
  have hker : (r.imageι ∣_ U).ker = ⊥ := by
    rw [AlgebraicGeometry.ker_morphismRestrict_eq_comap, Scheme.Hom.imageι,
      Scheme.IdealSheafData.ker_subschemeι, ← AlgebraicGeometry.ker_morphismRestrict_eq_comap r U]
    exact (r ∣_ U).ker_eq_bot_of_isIso
  exact (IsClosedImmersion.isIso_iff_ker_eq_bot).2 hker

private lemma isIso_normalized_closed_subscheme_over_open
    {P : Scheme.{u}} (I : P.IdealSheafData)
    (hI : ∀ W : I.subscheme.Opens, IsCompact (W : Set I.subscheme) →
      (irreducibleComponents W).Finite)
    (V : P.Opens) (hV : IsIso (I.subschemeι ∣_ V))
    (hNormal : IsNormal (I.subschemeι ⁻¹ᵁ V).toScheme) :
    IsIso ((Scheme.normalization I.subscheme hI ≫ I.subschemeι) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso'
    (normalization_restrict_isIso_of_isNormal hI _ hNormal) hV

private theorem exists_normalized_pullback_closed_subscheme
    {X Y X' : Scheme.{u}} [IsNoetherian X] (hNagata : IsNagataScheme X)
    (f : Y ⟶ X) (g : X' ⟶ X) [IsProper f] [IsProper g]
    (I : (Limits.pullback f g).IdealSheafData) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ Y) (q : Z ⟶ X') (h : p ≫ f = q ≫ g),
      IsNormal Z ∧ IsProper p ∧ IsProper q ∧
        IsFinite (Limits.pullback.lift p q h) ∧
        (∀ V : (Limits.pullback f g).Opens,
          IsIso (I.subschemeι ∣_ V) →
          IsNormal (I.subschemeι ⁻¹ᵁ V).toScheme →
          IsIso (Limits.pullback.lift p q h ∣_ V)) ∧
        (∀ V : (Limits.pullback f g).Opens,
          Dense (I.subschemeι ⁻¹ᵁ V : Set I.subscheme) →
          ∀ z ∈ genericPoints Z, Limits.pullback.lift p q h z ∈ V) := by
  let w : I.subscheme ⟶ X := I.subschemeι ≫ Limits.pullback.fst f g ≫ f
  have : IsProper w := inferInstance
  have : IsNoetherian I.subscheme := isNoetherian_of_isProper_over_noetherian w
  let hW := finite_irreducibleComponents_of_isProper w
  have := isFinite_normalization_of_isProper_to_nagata hNagata w hW
  let r := Scheme.normalization I.subscheme hW ≫ I.subschemeι
  let p := r ≫ Limits.pullback.fst f g
  let q := r ≫ Limits.pullback.snd f g
  have h : p ≫ f = q ≫ g := by
    simp only [p, q, Category.assoc, Limits.pullback.condition]
  have heq : Limits.pullback.lift p q h = r :=
    Limits.pullback.hom_ext (Limits.pullback.lift_fst p q h) (Limits.pullback.lift_snd p q h)
  refine ⟨_, p, q, h, isNormal_normalizationScheme hW, inferInstance, inferInstance,
    ?_, ?_, ?_⟩
  · rw [heq]
    infer_instance
  · intro V hV hNormal
    rw [heq]
    exact isIso_normalized_closed_subscheme_over_open I hW V hV hNormal
  · intro V hDense z hz
    rw [heq]
    change I.subschemeι (Scheme.normalization I.subscheme hW z) ∈ V
    exact genericPoint_mem_dense_open (I.subschemeι ⁻¹ᵁ V) hDense _
      (genericPoints_map_normalization hW ⟨z, hz⟩)

private theorem exists_lift_normalization_of_proper_birational
    {X Y : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (hNagata : IsNagataScheme X) (f : Y ⟶ X) [IsProper f]
    (hf : IsBirational f)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite) :
    ∃ g : Scheme.normalizationScheme Y hY ⟶
        Scheme.normalizationScheme X hX,
      IsProper g ∧ g ≫ Scheme.normalization X hX =
        Scheme.normalization Y hY ≫ f := by
  have := isFinite_normalization_of_isProper_to_nagata hNagata f hY
  let : IsFinite (Scheme.normalization X hX) :=
    AlgebraicGeometry.Scheme.isFinite_normalization hNagata hX
  let : IsProper (Scheme.normalization Y hY) :=
    isProper_normalization_of_isProper_to_nagata hNagata f hY
  have : IsNormal (Scheme.normalizationScheme Y hY) :=
    isNormal_normalizationScheme hY
  have hgeneric : ∀ η : genericPoints (Scheme.normalizationScheme Y hY),
      (Scheme.normalization Y hY ≫ f) η.1 ∈ genericPoints X :=
    fun η => hf.bijOn.mapsTo (genericPoints_map_normalization hY η)
  obtain ⟨g, hg, _⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_lift_normalization
      hX (Scheme.normalization Y hY ≫ f) hgeneric
  have : IsProper (g ≫ Scheme.normalization X hX) := by
    rw [hg]
    infer_instance
  let : IsSeparated (Scheme.normalization X hX) := inferInstance
  exact ⟨g, IsProper.of_comp g (Scheme.normalization X hX), hg⟩

open IsLocalRing in
private lemma isNormal_spec_field (K : Type u) [Field K] :
    IsNormal (Spec (.of K)) := by
  apply (isNormal_iff_stalk_normal _).mpr
  intro x
  have hx : closure ({x} : Set (Spec (.of K))) ∈ irreducibleComponents (Spec (.of K)) := by
    change x ∈ genericPoints (Spec (.of K))
    rw [genericPoints_eq_singleton]
    exact Subsingleton.elim _ _
  let := (isField_stalk_of_closure_mem_irreducibleComponents (Spec (.of K)) x hx).toField
  exact ⟨inferInstance, inferInstance⟩

open IsLocalRing in
private lemma exists_section_fromSpecStalk {X Y : Scheme.{u}} (f : Y ⟶ X)
    (y : Y) (x : X) (hxy : f y = x) [IsIso (f.stalkMap y)] :
    ∃ s : Spec (X.presheaf.stalk x) ⟶ Y,
      s ≫ f = X.fromSpecStalk x ∧ s (closedPoint _) = y := by
  subst x
  let s := Spec.map (inv (f.stalkMap y)) ≫ Y.fromSpecStalk y
  refine ⟨s, ?_, ?_⟩
  · dsimp [s]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f (x := y)]
    rw [Spec.map_inv, IsIso.inv_hom_id_assoc]
  · change Y.fromSpecStalk y ((Spec.map (inv (f.stalkMap y))) (closedPoint _)) = y
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

open IsLocalRing in
private lemma isIso_stalkMap_of_generic_section {X Y : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) (x : X) (s : Spec (X.presheaf.stalk x) ⟶ Y)
    (hs : s ≫ f = X.fromSpecStalk x)
    (hgeneric : s (closedPoint _) ∈ genericPoints Y) :
    IsIso (f.stalkMap (s (closedPoint _))) := by
  let t : Spec (X.presheaf.stalk x) := closedPoint (X.presheaf.stalk x)
  let := (isField_stalk_of_closure_mem_irreducibleComponents Y (s t) hgeneric).toField
  have hcomp : IsIso ((s ≫ f).stalkMap t) := by
    rw [hs]
    exact AlgebraicGeometry.isIso_stalkMap_fromSpecStalk_closedPoint X x
  rw [Scheme.Hom.stalkMap_comp] at hcomp
  have : IsIso (f.stalkMap (s t) ≫ s.stalkMap t) := hcomp
  have : IsIso (s.stalkMap t) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨(s.stalkMap t).hom.injective, ?_⟩
    exact Function.Surjective.of_comp
      (ConcreteCategory.bijective_of_isIso (f.stalkMap (s t) ≫ s.stalkMap t)).2
  exact IsIso.of_isIso_comp_right (f.stalkMap (s t)) (s.stalkMap t)

open IsLocalRing in
private lemma exists_spec_stalk_lift_of_generic {X Y X' : Scheme.{u}} [IsReduced X'] (f : Y ⟶ X)
    (q : X' ⟶ X) (y : Y) (x' : X') [IsIso (f.stalkMap y)] (hxy : f y = q x')
    (hx' : x' ∈ genericPoints X') :
    ∃ s : Spec (X'.presheaf.stalk x') ⟶ Y,
      s ≫ f = X'.fromSpecStalk x' ≫ q ∧ ∀ z, s z = y := by
  obtain ⟨s₀, hs₀, hs₀point⟩ := exists_section_fromSpecStalk f y (q x') hxy
  let K := X'.presheaf.stalk x'
  let : Field K := (isField_stalk_of_closure_mem_irreducibleComponents X' x' hx').toField
  let S : Scheme.{u} := Spec (X'.presheaf.stalk x')
  have : Subsingleton S := by
    change Subsingleton (PrimeSpectrum K)
    infer_instance
  let t : S := closedPoint K
  refine ⟨Spec.map (q.stalkMap x') ≫ s₀, ?_, fun z => ?_⟩
  · rw [Category.assoc, hs₀, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · rw [Subsingleton.elim z t]
    change s₀ (Spec.map (q.stalkMap x') t) = y
    rw [Spec_closedPoint]
    exact hs₀point

private lemma eq_of_comp_normalization_eq {X S : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    [IsNormal S] {a b : S ⟶ Scheme.normalizationScheme X hX}
    (hb : ∀ η : genericPoints S, (b ≫ Scheme.normalization X hX) η.1 ∈ genericPoints X)
    (hab : a ≫ Scheme.normalization X hX = b ≫ Scheme.normalization X hX) : a = b :=
  (AlgebraicGeometry.Scheme.existsUnique_lift_normalization hX _ hb).unique hab rfl

open IsLocalRing in
private lemma isBirational_lift_normalizations
    {X Y : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite)
    (f : Y ⟶ X) (hf : IsBirational f)
    (l : Scheme.normalizationScheme Y hY ⟶ Scheme.normalizationScheme X hX)
    (hl : l ≫ Scheme.normalization X hX = Scheme.normalization Y hY ≫ f)
    [IsFinite (Scheme.normalization X hX)]
    [IsFinite (Scheme.normalization Y hY)]
    [IsReduced (Scheme.normalizationScheme X hX)]
    [IsReduced (Scheme.normalizationScheme Y hY)] : IsBirational l := by
  let X' := Scheme.normalizationScheme X hX
  let Y' := Scheme.normalizationScheme Y hY
  let p : Y' ⟶ Y := Scheme.normalization Y hY
  let q : X' ⟶ X := Scheme.normalization X hX
  have hp : Set.BijOn p (genericPoints Y') (genericPoints Y) :=
    bijOn_genericPoints_normalization Y hY
  have hq : Set.BijOn q (genericPoints X') (genericPoints X) :=
    bijOn_genericPoints_normalization X hX
  have hlbij := bijOn_genericPoints_of_commutative_square f p q l hf.bijOn hp hq hl
  refine ⟨hlbij, fun y' hy' => ?_⟩
  let x' : X' := l y'
  have hx' : x' ∈ genericPoints X' := hlbij.mapsTo hy'
  have hpy' : p y' ∈ genericPoints Y := hp.mapsTo hy'
  have : IsIso (f.stalkMap (p y')) := hf.isIso_stalkMap _ hpy'
  obtain ⟨s, hs, hspoints⟩ := exists_spec_stalk_lift_of_generic f q (p y') x'
    (congrArg (fun r : Y' ⟶ X => r y') hl).symm hx'
  let K := X'.presheaf.stalk x'
  let : Field K := (isField_stalk_of_closure_mem_irreducibleComponents X' x' hx').toField
  let S : Scheme.{u} := Spec (X'.presheaf.stalk x')
  have : Subsingleton S := by
    change Subsingleton (PrimeSpectrum K)
    infer_instance
  let t : S := closedPoint K
  have : IsNormal S := isNormal_spec_field K
  obtain ⟨s', hs', _⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_lift_normalization hY s
      (fun η => by rw [hspoints]; exact hpy')
  have hsl : s' ≫ l = X'.fromSpecStalk x' := by
    refine eq_of_comp_normalization_eq hX (fun η => ?_) ?_
    · have heq : (X'.fromSpecStalk x' ≫ q) η.1 = q x' := by
        rw [Subsingleton.elim η.1 t]
        exact congrArg q Scheme.fromSpecStalk_closedPoint
      rw [heq]
      exact hq.mapsTo hx'
    · calc
        (s' ≫ l) ≫ q = s' ≫ (p ≫ f) := by rw [Category.assoc, hl]
        _ = s ≫ f := by rw [← Category.assoc, hs']
        _ = X'.fromSpecStalk x' ≫ q := hs
  have hs'point : p (s' t) = p y' := (congrArg (fun r : S ⟶ Y => r t) hs').trans (hspoints t)
  have hs'gen : s' t ∈ genericPoints Y' :=
    mem_genericPoints_of_locallyQuasiFinite p (s' t) (hs'point ▸ hpy')
  have heq : s' t = y' := hp.injOn hs'gen hy' hs'point
  have hiso := isIso_stalkMap_of_generic_section l x' s' hsl hs'gen
  change IsIso (l.stalkMap (s' t)) at hiso
  rwa [heq] at hiso

open IsLocalRing in
private lemma nonunit_numerator_denominator_of_residue_not_mem_range
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] {a b : A} {u : B}
    (heq : φ a = u * φ b)
    (hu : residue B u ∉ Set.range (ResidueField.map φ)) :
    ¬ IsUnit a ∧ ¬ IsUnit b := by
  have hb : ¬ IsUnit b := by
    rintro ⟨v, rfl⟩
    apply hu
    refine ⟨residue A (a * (↑(v⁻¹) : A)), ?_⟩
    rw [ResidueField.map_residue]
    congr 1
    rw [map_mul, heq, mul_assoc, ← map_mul]
    simp
  exact ⟨fun ha => hb ((isUnit_map_iff φ b).mp (isUnit_of_mul_isUnit_right (heq ▸ ha.map φ))), hb⟩

open IsLocalRing in
private lemma min_addVal_pos_of_residue_not_mem_range
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsDomain B] [IsDiscreteValuationRing B]
    (φ : A →+* B) [IsLocalHom φ] {a b : A} {u : B}
    (heq : φ a = u * φ b)
    (hu : residue B u ∉ Set.range (ResidueField.map φ)) :
    0 < min (IsDiscreteValuationRing.addVal B (φ a))
      (IsDiscreteValuationRing.addVal B (φ b)) := by
  obtain ⟨ha, hb⟩ := nonunit_numerator_denominator_of_residue_not_mem_range φ heq hu
  exact lt_min
    (pos_iff_ne_zero.mpr fun h => ha ((isUnit_map_iff φ a).mp
      (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h)))
    (pos_iff_ne_zero.mpr fun h => hb ((isUnit_map_iff φ b).mp
      (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h)))

private theorem addVal_lt_of_mul_by_nonunit
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b d : R} (h : a = b * d) (hb : b ≠ 0) (hd : ¬ IsUnit d) :
    IsDiscreteValuationRing.addVal R b < IsDiscreteValuationRing.addVal R a := by
  have hdpos : 0 < IsDiscreteValuationRing.addVal R d :=
    pos_iff_ne_zero.mpr fun hz => hd (IsDiscreteValuationRing.addVal_eq_zero_iff.mp hz)
  have hbtop : IsDiscreteValuationRing.addVal R b ≠ ⊤ :=
    fun htop => hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
  rw [h, IsDiscreteValuationRing.addVal_mul, add_comm]
  exact ENat.lt_add_left hbtop hdpos

/-- A common nonunit factor strictly lowers the minimum order of two nonzero
elements after it is removed. This is the numerical step in the Zariski
induction used for surfaces. -/
private theorem exists_common_factor_of_principal_mapped_ideal
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) {a b : A} {d : B}
    (ha : a ∈ I) (hb : b ∈ I)
    (hI : I.map φ = Ideal.span {d}) :
    ∃ a' b' : B, φ a = a' * d ∧ φ b = b' * d := by
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (hI ▸ Ideal.mem_map_of_mem φ ha)
  obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp (hI ▸ Ideal.mem_map_of_mem φ hb)
  exact ⟨a', b', ha'.symm, hb'.symm⟩

private theorem nonunit_generator_of_mapped_ideal
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (I : Ideal A) {d : B}
    (hI : ∀ a ∈ I, ¬ IsUnit (φ a))
    (hgen : I.map φ = Ideal.span {d}) : ¬ IsUnit d := by
  have hle : I.map φ ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.mpr (hI a ha))
  have hd : d ∈ I.map φ := hgen ▸ Ideal.mem_span_singleton_self d
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).1 (hle hd))

private theorem exists_exceptionalIdeal_stalk_generator_on_affine
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : (AlgebraicGeometry.blowUp I))
    (hx : (AlgebraicGeometry.blowUpToBase I) x ∈ U.1) :
    ∃ a : I.ideal U,
      IdealSheafData.stalk (AlgebraicGeometry.exceptionalIdeal I) x =
        Ideal.span {((AlgebraicGeometry.blowUpToBase I).stalkMap x)
                      (X.presheaf.germ U.1 ((AlgebraicGeometry.blowUpToBase I) x) hx
                        (a : X.presheaf.obj (.op U.1)))} := by
  have hcover : x ∈ ((AlgebraicGeometry.blowUpToBase I) ⁻¹ᵁ U.1).1 := hx
  rw [← AlgebraicGeometry.blownUpAffine_chart_cover I U] at hcover
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hcover
  exact ⟨a, (AlgebraicGeometry.mem_affineBlowupStandardOpen_iff_exceptionalIdeal_stalk_eq_span
    I U a x hx).mp ha⟩

private theorem exceptionalIdeal_stalk_eq_map
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (z : (AlgebraicGeometry.blowUp I)) :
    IdealSheafData.stalk (AlgebraicGeometry.exceptionalIdeal I) z =
      (IdealSheafData.stalk I ((AlgebraicGeometry.blowUpToBase I) z)).map
        ((AlgebraicGeometry.blowUpToBase I).stalkMap z).hom :=
  AlgebraicGeometry.stalk_comap I (AlgebraicGeometry.blowUpToBase I) z

private theorem min_addVal_lt_of_common_factor
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b a' b' d : R} (ha : a = a' * d) (hb : b = b' * d)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hd : ¬ IsUnit d) :
    min (IsDiscreteValuationRing.addVal R a') (IsDiscreteValuationRing.addVal R b') <
      min (IsDiscreteValuationRing.addVal R a) (IsDiscreteValuationRing.addVal R b) :=
  lt_min ((min_le_left _ _).trans_lt (addVal_lt_of_mul_by_nonunit R ha ha' hd))
    ((min_le_right _ _).trans_lt (addVal_lt_of_mul_by_nonunit R hb hb' hd))

private theorem enat_toNat_strict_of_lt {m n : ℕ∞} (h : m < n)
    (hn : n < ⊤) : m.toNat < n.toNat := by
  cases m with
  | top => simp at h
  | coe m =>
      cases n with
      | top => simp at hn
      | coe n => simpa using h

open IsLocalRing in
private lemma min_addVal_toNat_pos_of_residue_not_mem_range
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsDomain B] [IsDiscreteValuationRing B]
    (φ : A →+* B) [IsLocalHom φ] {a b : A} {u : B}
    (heq : φ a = u * φ b) (hb : φ b ≠ 0)
    (hu : residue B u ∉ Set.range (ResidueField.map φ)) :
    0 < (min (IsDiscreteValuationRing.addVal B (φ a))
      (IsDiscreteValuationRing.addVal B (φ b))).toNat := by
  exact enat_toNat_strict_of_lt (min_addVal_pos_of_residue_not_mem_range φ heq hu)
    ((min_le_right _ _).trans_lt (lt_top_iff_ne_top.mpr fun h =>
      hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)))

/-- The order of a pair in a DVR is a finite natural number for nonzero
elements, and removing a common nonzero nonunit factor strictly lowers it. -/
private theorem min_addVal_toNat_lt_of_common_factor
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b a' b' d : R} (ha : a = a' * d) (hb : b = b' * d)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hd : ¬ IsUnit d) (hd0 : d ≠ 0) :
    (min (IsDiscreteValuationRing.addVal R a')
      (IsDiscreteValuationRing.addVal R b')).toNat <
    (min (IsDiscreteValuationRing.addVal R a)
      (IsDiscreteValuationRing.addVal R b)).toNat := by
  have ha0 : a ≠ 0 := ha ▸ mul_ne_zero ha' hd0
  exact enat_toNat_strict_of_lt (min_addVal_lt_of_common_factor R ha hb ha' hb' hd)
    ((min_le_left _ _).trans_lt (WithTop.lt_top_iff_ne_top.mpr fun h =>
      ha0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)))

private theorem min_addVal_toNat_lt_of_principal_mapped_ideal
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [IsDiscreteValuationRing B]
    (φ : A →+* B) (I : Ideal A) {a b : A} {d : B}
    (ha : a ∈ I) (hb : b ∈ I)
    (hI : I.map φ = Ideal.span {d})
    (ha0 : φ a ≠ 0) (hb0 : φ b ≠ 0)
    (hd : ¬ IsUnit d) (hd0 : d ≠ 0) :
    ∃ a' b' : B, φ a = a' * d ∧ φ b = b' * d ∧
      (min (IsDiscreteValuationRing.addVal B a')
        (IsDiscreteValuationRing.addVal B b')).toNat <
      (min (IsDiscreteValuationRing.addVal B (φ a))
        (IsDiscreteValuationRing.addVal B (φ b))).toNat := by
  obtain ⟨a', b', ha', hb'⟩ :=
    exists_common_factor_of_principal_mapped_ideal φ I ha hb hI
  have ha'0 : a' ≠ 0 := by
    intro h
    exact ha0 (ha'.trans (by simp [h]))
  have hb'0 : b' ≠ 0 := by
    intro h
    exact hb0 (hb'.trans (by simp [h]))
  exact ⟨a', b', ha', hb',
    min_addVal_toNat_lt_of_common_factor B ha' hb' ha'0 hb'0 hd hd0⟩

/-- A locally finite descent argument: if every positive measure admits a
strictly decreasing step, some finite string of steps reaches measure zero. -/
private theorem exists_finite_descent_to_zero
    {α : Type*} (μ : α → ℕ) (R : α → α → Prop)
    (hstep : ∀ a, 0 < μ a → ∃ b, R a b ∧ μ b < μ a)
    (a : α) : ∃ b, Relation.ReflTransGen R a b ∧ μ b = 0 := by
  suffices h : ∀ n a, μ a = n → ∃ b, Relation.ReflTransGen R a b ∧ μ b = 0 by
    exact h (μ a) a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a ha
      cases n with
      | zero => exact ⟨a, Relation.ReflTransGen.refl, ha⟩
      | succ n =>
          have hpos : 0 < μ a := by rw [ha]; omega
          obtain ⟨a', hR, hμ⟩ := hstep a hpos
          have hμ' : μ a' ≤ n := by rw [ha] at hμ; omega
          obtain ⟨b, hchain, hb⟩ := ih (μ a') (by omega) a' rfl
          exact ⟨b, .head hR hchain, hb⟩

private theorem exists_eventual_strict_drop
    {α : Type*} (cardinality measure : α → ℕ) (R : α → α → Prop)
    (hstep : ∀ a, ∃ b, R a b ∧ cardinality b ≤ cardinality a ∧
      (cardinality b < cardinality a ∨ measure b < measure a))
    (a : α) :
    ∃ b, Relation.ReflTransGen R a b ∧ cardinality b < cardinality a := by
  suffices h : ∀ n a, measure a = n →
      ∃ b, Relation.ReflTransGen R a b ∧ cardinality b < cardinality a by
    exact h (measure a) a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a ha
      obtain ⟨b, hab, hcard, hdrop⟩ := hstep a
      rcases hdrop with hdrop | hmeasure
      · exact ⟨b, .head hab .refl, hdrop⟩
      · obtain ⟨c, hbc, hcard'⟩ := ih (measure b) (by omega) b rfl
        exact ⟨c, .head hab hbc, lt_of_lt_of_le hcard' hcard⟩

/-- Assemble a chain over the original scheme from a tail of normalized blowups over its
normalization. The normalization of the source is used only to carry the tail's final map back
to the original proper birational source. -/
private theorem exists_normalizedBlowUpChain_dominating_of_normalizedTail
    {X Y : Scheme.{u}} (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite)
    (f : Y ⟶ X)
    (l : Scheme.normalizationScheme Y hY ⟶
      Scheme.normalizationScheme X hX)
    (hl : l ≫ Scheme.normalization X hX =
      Scheme.normalization Y hY ≫ f)
    (hfactor : ∃ (Z : Scheme.{u})
        (g : Z ⟶ Scheme.normalizationScheme X hX),
      NormalizedBlowUpTail (Scheme.normalizationScheme X hX) Z g ∧
        ∃ h : Z ⟶ Scheme.normalizationScheme Y hY, h ≫ l = g) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ Y),
      NormalizedBlowUpChain X hX Z g ∧ h ≫ f = g := by
  obtain ⟨Z, g, h, hs, hh⟩ :=
    exists_normalizedBlowUpChain_dominating_of_tail hNagata hX
      (Scheme.normalization Y hY ≫ f) l hl hfactor
  exact ⟨Z, g, h ≫ Scheme.normalization Y hY, hs, by rw [Category.assoc, hh]⟩


private alias isBirational_morphismRestrict := AlgebraicGeometry.birational_morphismRestrict

private alias isIntegral_of_reduced_birational_to_integral :=
  AlgebraicGeometry.integral_of_reduced_birational_to_integral

private lemma topologicalKrullDim_le_of_birational_of_locally_integral
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsReduced X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f)
    (hY : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsIntegral U.toScheme) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  obtain ⟨U, hxU, hU⟩ := hY (f x)
  have : IsIntegral U.toScheme := hU
  have hbir := isBirational_morphismRestrict f hf U
  have : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_reduced_birational_to_integral _ hbir
  calc
    TopologicalSpace.localKrullDim X x ≤ topologicalKrullDim (f ⁻¹ᵁ U) :=
      iInf_le_of_le _ (iInf_le_of_le (f ⁻¹ᵁ U).isOpen (iInf_le _ hxU))
    _ ≤ topologicalKrullDim U := topologicalKrullDim_le_of_isBirational (f ∣_ U) hbir
    _ ≤ topologicalKrullDim Y := topologicalKrullDim_subspace_le Y U

private lemma exists_integral_open_normalization
    {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite)
    (x : Scheme.normalizationScheme X hX) :
    ∃ U : (Scheme.normalizationScheme X hX).Opens,
      x ∈ U ∧ IsIntegral U.toScheme := by
  obtain ⟨e, -⟩ := X.exists_iso_normalizationScheme_sigma_reducedComponent hX
  let Z : irreducibleComponents X → Scheme.{u} := fun W =>
    (X.reducedComponent W).normalizationScheme
      (X.finite_irreducibleComponents_reducedComponent W)
  have hZint : ∀ i, IsIntegral (Z i) := fun i =>
    Scheme.isIntegral_normalizationScheme (X.reducedComponent i)
      (X.finite_irreducibleComponents_reducedComponent i)
  let 𝒰 := (sigmaOpenCover Z).pushforwardIso e.hom
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x
  let j := 𝒰.f i
  have : IsIntegral (𝒰.X i) := hZint i
  refine ⟨j.opensRange, ?_, ?_⟩
  · change x ∈ Set.range j
    exact ⟨z, hz⟩
  · have : Nonempty j.opensRange.toScheme := ⟨j.isoOpensRange.hom z⟩
    exact isIntegral_of_isOpenImmersion j.isoOpensRange.inv

private lemma codimension_eq_one_of_nonclosed_of_not_generic
    {X : Scheme.{u}} (hdim : topologicalKrullDim X ≤ 2) (x : X)
    (hx : ¬ IsClosed ({x} : Set X)) (hgen : x ∉ genericPoints X) :
    codimension (IrreducibleCloseds.closureSingleton x) = 1 := by
  have hzero : codimension (IrreducibleCloseds.closureSingleton x) ≠ 0 := by
    intro h
    apply hgen
    apply mem_genericPoints_of_isMax
    rwa [← Order.coheight_eq_zero,
      ← Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
  have hlt : ¬ (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := fun h =>
    hx (isClosed_singleton_of_le_codimension 2 hdim x h)
  cases he : codimension (IrreducibleCloseds.closureSingleton x) with
  | top => simp [he] at hlt
  | coe n =>
    rw [he] at hzero hlt
    norm_cast at hzero hlt ⊢
    omega

private lemma not_generic_image_of_contracted_nonclosed_point
    {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (y : Y) (hy : ¬ IsClosed ({y} : Set Y))
    (hfy : IsClosed ({f y} : Set X)) :
    f y ∉ genericPoints X := by
  intro hgen
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open f
  have : IsIso (f ∣_ U) := hU.1
  exact hy (isClosed_singleton_of_isIso_restrict f U y
    (mem_maximal_isomorphism_open_of_mem_genericPoints f hf U hU (f y) hgen) hfy)

private lemma not_generic_of_contracted_nonclosed_point
    {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (y : Y) (hy : ¬ IsClosed ({y} : Set Y)) (hfy : IsClosed ({f y} : Set X)) :
    y ∉ genericPoints Y := fun hgen =>
  not_generic_image_of_contracted_nonclosed_point f hf y hy hfy (hf.bijOn.mapsTo hgen)

private lemma exists_transcendental_residue_of_nonclosed
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsSeparated f]
    (y : Y) (hy : ¬ IsClosed ({y} : Set Y)) (hfy : IsClosed ({f y} : Set X)) :
    letI := (f.residueFieldMap y).hom.toAlgebra
    ∃ u : Y.presheaf.stalk y, Transcendental (X.residueField (f y)) (Y.residue y u) := by
  let := (f.residueFieldMap y).hom.toAlgebra
  have hnot : ¬ Algebra.IsAlgebraic (X.residueField (f y)) (Y.residueField y) := by
    intro h
    have : IsIntegralHom (Spec.map (f.residueFieldMap y)) := by
      rw [IsIntegralHom.SpecMap_iff]
      exact Algebra.IsIntegral.isIntegral
    have : IsClosedImmersion (X.fromSpecResidueField (f y)) :=
      isClosed_singleton_iff_isClosedImmersion.mp hfy
    have : IsIntegralHom (Y.fromSpecResidueField y ≫ f) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      infer_instance
    have := IsIntegralHom.of_comp (Y.fromSpecResidueField y) f
    apply hy
    simpa only [Scheme.range_fromSpecResidueField] using
      (Y.fromSpecResidueField y).isClosedMap.isClosed_range
  have hex : ∃ a : Y.residueField y, Transcendental (X.residueField (f y)) a := by
    by_contra! h
    exact hnot ⟨fun a => not_not.mp (h a)⟩
  obtain ⟨a, ha⟩ := hex
  obtain ⟨u, hu⟩ := Y.residue_surjective y a
  exact ⟨u, hu ▸ ha⟩

private lemma Transcendental.not_mem_range_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L] {a : L}
    (ha : Transcendental K a) :
    a ∉ Set.range (algebraMap K L) := by
  rintro ⟨b, rfl⟩
  exact ha (isAlgebraic_algebraMap b)

private lemma exists_stalk_numerator_denominator_of_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : IsBirational f) (y : Y)
    (u : Y.presheaf.stalk y) :
    ∃ a b : X.presheaf.stalk (f y), (f.stalkMap y).hom b ≠ 0 ∧
      (f.stalkMap y).hom a = u * (f.stalkMap y).hom b := by
  have hgen : f (genericPoint Y) = genericPoint X := by
    have h := hf.bijOn.mapsTo (show genericPoint Y ∈ genericPoints Y by
      simp [genericPoints_eq_singleton])
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using h
  have : IsIso (f.stalkMap (genericPoint Y)) :=
    hf.isIso_stalkMap _ (by simp [genericPoints_eq_singleton])
  let k : X.functionField ⟶ Y.functionField :=
    (X.presheaf.stalkCongr (inseparable_iff_eq.mpr hgen.symm)).hom ≫ f.stalkMap (genericPoint Y)
  have : IsIso k := by dsimp only [k]; infer_instance
  have hspecX : genericPoint X ⤳ f y := (genericPoint_spec X).specializes trivial
  have hspecY : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
  have hcomm : X.presheaf.stalkSpecializes hspecX ≫ k =
      f.stalkMap y ≫ Y.presheaf.stalkSpecializes hspecY := by
    have h1 : X.presheaf.stalkSpecializes hspecX ≫
        (X.presheaf.stalkCongr (inseparable_iff_eq.mpr hgen.symm)).hom =
        X.presheaf.stalkSpecializes
          ((inseparable_iff_eq.mpr hgen).specializes.trans hspecX) := by
      rw [TopCat.Presheaf.stalkCongr_hom]
      exact TopCat.Presheaf.stalkSpecializes_comp _ _ _
    dsimp only [k]
    rw [← Category.assoc, h1]
    exact f.stalkSpecializes_stalkMap _ _ _
  have hmap (a : X.presheaf.stalk (f y)) :
      k.hom (algebraMap (X.presheaf.stalk (f y)) X.functionField a) =
        algebraMap (Y.presheaf.stalk y) Y.functionField ((f.stalkMap y).hom a) :=
    congrArg (fun r : X.presheaf.stalk (f y) ⟶ Y.functionField => r a) hcomm
  let w : X.functionField := (inv k).hom (algebraMap (Y.presheaf.stalk y) Y.functionField u)
  have hw : k.hom w = algebraMap (Y.presheaf.stalk y) Y.functionField u := by
    change (inv k ≫ k) _ = _
    simp
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk (f y))) w
  refine ⟨a, b.1, ?_, ?_⟩
  · intro hb
    have hzero : k.hom (algebraMap (X.presheaf.stalk (f y)) X.functionField b.1) = 0 := by
      rw [hmap, hb, map_zero]
    have ha0 : algebraMap (X.presheaf.stalk (f y)) X.functionField b.1 = 0 :=
      k.hom.injective (hzero.trans (map_zero k.hom).symm)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp b.2)
      (IsFractionRing.injective (X.presheaf.stalk (f y)) X.functionField
        (ha0.trans (map_zero _).symm))
  · apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    simpa only [map_mul, hmap, hw] using (congrArg k.hom hab).symm

private lemma exists_numerator_denominator_of_arrow_iso
    {A B C D : CommRingCat.{u}} (φ : A ⟶ B) (ψ : C ⟶ D)
    (e : Arrow.mk φ ≅ Arrow.mk ψ)
    (hφ : ∀ u : B, ∃ a b : A, φ b ≠ 0 ∧ φ a = u * φ b) (u : D) :
    ∃ a b : C, ψ b ≠ 0 ∧ ψ a = u * ψ b := by
  have : IsIso e.hom.right := inferInstance
  have hcomm (a : A) : ψ (e.hom.left a) = e.hom.right (φ a) :=
    congrArg (fun r : A ⟶ D => r a) e.hom.w
  obtain ⟨a, b, hb, hab⟩ := hφ ((inv e.hom.right) u)
  refine ⟨e.hom.left a, e.hom.left b, ?_, ?_⟩
  · rw [hcomm]
    intro hzero
    exact hb ((ConcreteCategory.bijective_of_isIso e.hom.right).1
      (hzero.trans (map_zero _).symm))
  · rw [hcomm, hab, map_mul, hcomm]
    have heq : e.hom.right ((inv e.hom.right) u) = u := by
      change (inv e.hom.right ≫ e.hom.right) u = u
      simp
    rw [heq]

private lemma exists_stalk_numerator_denominator_of_locally_integral
    {X Y : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) (hf : IsBirational f)
    (hX : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIntegral U.toScheme)
    (y : Y) (u : Y.presheaf.stalk y) :
    ∃ a b : X.presheaf.stalk (f y), (f.stalkMap y).hom b ≠ 0 ∧
      (f.stalkMap y).hom a = u * (f.stalkMap y).hom b := by
  obtain ⟨U, hyU, hU⟩ := hX (f y)
  have : IsIntegral U.toScheme := hU
  have hbir := isBirational_morphismRestrict f hf U
  have : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_reduced_birational_to_integral _ hbir
  let y' : (f ⁻¹ᵁ U).toScheme := ⟨y, hyU⟩
  exact exists_numerator_denominator_of_arrow_iso _ _ (morphismRestrictStalkMap f U y')
    (exists_stalk_numerator_denominator_of_birational (f ∣_ U) hbir y') u

private theorem stalk_vanishingIdeal_singleton_eq_maximalIdeal
    {X : Scheme.{u}} (x : X) (hclosed : IsClosed ({x} : Set X)) :
    IdealSheafData.stalk
      (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hclosed⟩) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hUmem, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hUmem
  let Ua : X.affineOpens := ⟨U, hU⟩
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hpre : (hU.fromSpec.base ⁻¹' ({x} : Set X) :
      Set (PrimeSpectrum ↑Γ(X, U))) = {p} := by
    ext z
    change hU.fromSpec.base z = x ↔ z = p
    refine ⟨fun hz => hU.fromSpec.isOpenEmbedding.injective
      (by rwa [hU.fromSpec_primeIdealOf]), ?_⟩
    rintro rfl
    exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hideal : (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hclosed⟩ : Closeds X)).ideal Ua
      = p.asIdeal := by
    have h : PrimeSpectrum.vanishingIdeal
        (hU.fromSpec.base ⁻¹' ({x} : Set X)) = p.asIdeal := by
      rw [hpre, PrimeSpectrum.vanishingIdeal_singleton]
    exact (Scheme.IdealSheafData.vanishingIdeal_ideal _ _).trans h
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  rw [IdealSheafData.stalk_eq_map_germ _ x Ua hxU, hideal]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal (X.presheaf.stalk x)

private theorem exists_principal_stalk_comap_blowUp
    {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (t : Y ⟶ (AlgebraicGeometry.blowUp I)) (y : Y) :
    ∃ d : Y.presheaf.stalk y,
      (IdealSheafData.stalk I ((t ≫ (AlgebraicGeometry.blowUpToBase I)) y)).map
        ((t ≫ (AlgebraicGeometry.blowUpToBase I)).stalkMap y).hom = Ideal.span {d} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((AlgebraicGeometry.blowUpToBase I) (t y))) isOpen_univ
  obtain ⟨a, ha⟩ := exists_exceptionalIdeal_stalk_generator_on_affine I ⟨U, hU⟩ (t y) hxU
  have hstep : (IdealSheafData.stalk I ((t ≫ (AlgebraicGeometry.blowUpToBase I)) y)).map
      ((t ≫ (AlgebraicGeometry.blowUpToBase I)).stalkMap y).hom =
      ((IdealSheafData.stalk I ((AlgebraicGeometry.blowUpToBase I) (t y))).map
        (((AlgebraicGeometry.blowUpToBase I).stalkMap (t y)).hom)).map
          ((t.stalkMap y).hom) := by
    rw [Ideal.map_map]
    congr 1
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  rw [hstep, ← exceptionalIdeal_stalk_eq_map I (t y), ha, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

private theorem exists_principal_maximalIdeal_normalizedBlowUp
    {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X))
    (z : Stacks.Blowup.normalizedBlowUpScheme X hX x hx)
    (hz : Stacks.Blowup.normalizedBlowUp X hX x hx z = x) :
    ∃ d : (Stacks.Blowup.normalizedBlowUpScheme X hX x hx).presheaf.stalk z,
      (IsLocalRing.maximalIdeal (X.presheaf.stalk
        (Stacks.Blowup.normalizedBlowUp X hX x hx z))).map
        ((Stacks.Blowup.normalizedBlowUp X hX x hx).stalkMap z).hom = Ideal.span {d} := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have hstalk (t : X) (ht : t = x) :
      IdealSheafData.stalk I t = IsLocalRing.maximalIdeal (X.presheaf.stalk t) := by
    subst t
    exact stalk_vanishingIdeal_singleton_eq_maximalIdeal x hx
  rw [← hstalk _ hz]
  exact exists_principal_stalk_comap_blowUp I
    (Scheme.normalization _ (Stacks.Blowup.finite_irreducibleComponents_blowUp I hX)) z

private lemma isIntegral_residueFieldMap_of_closedPoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    (f.residueFieldMap y).hom.IsIntegral := by
  have hfin := isFinite_fromSpecResidueField_comp_of_isProper f y hy
  have : IsFinite (Spec.map (f.residueFieldMap y) ≫ X.fromSpecResidueField (f y)) := by
    rwa [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have : IsFinite (Spec.map (f.residueFieldMap y)) :=
    IsFinite.of_comp _ (X.fromSpecResidueField (f y))
  exact IsIntegralHom.SpecMap_iff.mp inferInstance

open IsLocalRing in
private lemma transcendental_of_integral_residue_extension
    {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing R]
    (ψ : A →+* B) (χ : B →+* R) [IsLocalHom ψ] [IsLocalHom χ]
    (hψ : (ResidueField.map ψ).IsIntegral) (u : R)
    (hu : letI := (ResidueField.map (χ.comp ψ)).toAlgebra
      Transcendental (ResidueField A) (residue R u)) :
    letI := (ResidueField.map χ).toAlgebra
    Transcendental (ResidueField B) (residue R u) := by
  let := (ResidueField.map ψ).toAlgebra
  let := (ResidueField.map χ).toAlgebra
  let := (ResidueField.map (χ.comp ψ)).toAlgebra
  have : IsScalarTower (ResidueField A) (ResidueField B) (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.map_comp ψ χ)
  have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := ⟨hψ⟩
  exact (Algebra.IsAlgebraic.transcendental_iff (ResidueField A) (ResidueField B)).mp hu

open IsLocalRing in
private lemma exists_fraction_of_principal_maximalIdeal
    {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    [IsLocalRing A] [IsLocalRing B] [IsDomain R] [IsDiscreteValuationRing R]
    (ψ : A →+* B) (χ : B →+* R) [IsLocalHom ψ] [IsLocalHom χ]
    {a b : A} {u : R} (hb : χ (ψ b) ≠ 0)
    (hab : χ (ψ a) = u * χ (ψ b))
    (hu : residue R u ∉ Set.range (ResidueField.map (χ.comp ψ)))
    (hprincipal : ∃ d : B, (maximalIdeal A).map ψ = Ideal.span {d}) :
    ∃ a' b' : B, χ b' ≠ 0 ∧ χ a' = u * χ b' ∧
      (IsDiscreteValuationRing.addVal R (χ b')).toNat <
        (IsDiscreteValuationRing.addVal R (χ (ψ b))).toNat := by
  obtain ⟨ha, hb'⟩ := nonunit_numerator_denominator_of_residue_not_mem_range
    (χ.comp ψ) hab hu
  obtain ⟨d, hd⟩ := hprincipal
  obtain ⟨a', b', ha', hb'⟩ := exists_common_factor_of_principal_mapped_ideal ψ
    (maximalIdeal A) ((mem_maximalIdeal _).mpr ha) ((mem_maximalIdeal _).mpr hb') hd
  have hbR : χ (ψ b) = χ b' * χ d := by rw [hb', map_mul]
  have hb'0 : χ b' ≠ 0 := left_ne_zero_of_mul (hbR ▸ hb)
  have hd0 : χ d ≠ 0 := right_ne_zero_of_mul (hbR ▸ hb)
  have hdunit : ¬ IsUnit (χ d) := by
    intro h
    have hdmem : d ∈ (maximalIdeal A).map ψ := by
      rw [hd]
      exact Ideal.subset_span (by simp)
    exact (mem_maximalIdeal _).mp ((map_maximalIdeal_le ψ) hdmem)
      ((isUnit_map_iff χ d).mp h)
  refine ⟨a', b', hb'0, ?_, ?_⟩
  · apply mul_right_cancel₀ hd0
    rw [mul_assoc, ← hbR, ← hab, ha', map_mul]
  · exact enat_toNat_strict_of_lt
      (addVal_lt_of_mul_by_nonunit R hbR hb'0 hdunit)
      (lt_top_iff_ne_top.mpr (fun h => hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)))

private lemma isLocalHom_ringEquiv {A B : Type*} [Semiring A] [Semiring B]
    (e : A ≃+* B) : IsLocalHom e.toRingHom where
  map_nonunit a ha := by simpa using ha.map e.symm.toRingHom

attribute [local instance] isLocalHom_ringEquiv

private alias residueField_map_surjective := isLocalRing_residueField_map_surjective

private lemma exists_fraction_descent_in_square
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (q : X' ⟶ X)
    (p : Y' ⟶ Y) (g : Y' ⟶ X') (hcomm : p ≫ f = g ≫ q)
    [IsProper q] (z : Y') [IsIso (p.stalkMap z)]
    (hz : IsClosed ({g z} : Set X'))
    (hprincipal : ∃ d : X'.presheaf.stalk (g z),
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (q (g z)))).map
        (q.stalkMap (g z)).hom = Ideal.span {d})
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (e : Y.presheaf.stalk (p z) ≃+* R) (u : R)
    (a b : X.presheaf.stalk (f (p z)))
    (hb : e ((f.stalkMap (p z)).hom b) ≠ 0)
    (hab : e ((f.stalkMap (p z)).hom a) = u * e ((f.stalkMap (p z)).hom b))
    (hu : letI := (IsLocalRing.ResidueField.map
      (e.toRingHom.comp (f.stalkMap (p z)).hom)).toAlgebra;
      Transcendental (IsLocalRing.ResidueField (X.presheaf.stalk (f (p z))))
        (IsLocalRing.residue R u)) :
    ∃ (e' : Y'.presheaf.stalk z ≃+* R) (a' b' : X'.presheaf.stalk (g z)),
      e' ((g.stalkMap z).hom b') ≠ 0 ∧
      e' ((g.stalkMap z).hom a') = u * e' ((g.stalkMap z).hom b') ∧
      (letI := (IsLocalRing.ResidueField.map
        (e'.toRingHom.comp (g.stalkMap z).hom)).toAlgebra;
        Transcendental (IsLocalRing.ResidueField (X'.presheaf.stalk (g z)))
          (IsLocalRing.residue R u)) ∧
      (IsDiscreteValuationRing.addVal R (e' ((g.stalkMap z).hom b'))).toNat <
        (IsDiscreteValuationRing.addVal R (e ((f.stalkMap (p z)).hom b))).toNat := by
  let i := X.presheaf.stalkCongr (inseparable_iff_eq.mpr
    (congrArg (fun k : Y' ⟶ X => k z) hcomm))
  let ie : X.presheaf.stalk (f (p z)) ≃+* X.presheaf.stalk (q (g z)) :=
    i.commRingCatIsoToRingEquiv
  let ψ := (q.stalkMap (g z)).hom.comp ie.toRingHom
  let pe := (asIso (p.stalkMap z)).commRingCatIsoToRingEquiv
  let e' := pe.symm.trans e
  let χ := e'.toRingHom.comp (g.stalkMap z).hom
  have hc : χ.comp ψ = e.toRingHom.comp (f.stalkMap (p z)).hom := by
    have hs := Scheme.Hom.stalkMap_congr_hom (p ≫ f) (g ≫ q) hcomm z
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hs
    ext a
    have heq := congrArg (fun k => (k : X.presheaf.stalk (f (p z)) ⟶
      Y'.presheaf.stalk z) a) hs
    change pe ((f.stalkMap (p z)).hom a) = (g.stalkMap z).hom (ψ a) at heq
    change e (pe.symm ((g.stalkMap z).hom (ψ a))) = _
    rw [← heq, pe.symm_apply_apply]
    rfl
  have hψ : (IsLocalRing.ResidueField.map ψ).IsIntegral := by
    rw [IsLocalRing.ResidueField.map_comp]
    exact RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (isLocalRing_residueField_map_surjective ie.toRingHom ie.surjective))
      (isIntegral_residueFieldMap_of_closedPoint q (g z) hz)
  have hprincipal' : ∃ d : X'.presheaf.stalk (g z),
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (f (p z)))).map ψ = Ideal.span {d} := by
    simpa only [ψ, ← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective
      ie.toRingHom ie.surjective] using hprincipal
  have hu' : let := (IsLocalRing.ResidueField.map (χ.comp ψ)).toAlgebra
      Transcendental (IsLocalRing.ResidueField (X.presheaf.stalk (f (p z))))
        (IsLocalRing.residue R u) := by
    have hc' : IsLocalRing.ResidueField.map (χ.comp ψ) =
        IsLocalRing.ResidueField.map (e.toRingHom.comp (f.stalkMap (p z)).hom) := by congr 1
    dsimp only
    rwa [hc']
  have hnot : IsLocalRing.residue R u ∉ Set.range (IsLocalRing.ResidueField.map (χ.comp ψ)) := by
    let := (IsLocalRing.ResidueField.map (χ.comp ψ)).toAlgebra
    exact Transcendental.not_mem_range_algebraMap hu'
  have hb' : χ (ψ b) ≠ 0 := by
    change (χ.comp ψ) b ≠ 0
    rwa [hc]
  have hab' : χ (ψ a) = u * χ (ψ b) := by
    change (χ.comp ψ) a = u * (χ.comp ψ) b
    rwa [hc]
  obtain ⟨a', b', hb'0, hab'', hlt⟩ :=
    exists_fraction_of_principal_maximalIdeal ψ χ hb' hab' hnot hprincipal'
  refine ⟨e', a', b', hb'0, hab'',
    transcendental_of_integral_residue_extension ψ χ hψ u hu', ?_⟩
  change (IsDiscreteValuationRing.addVal R (χ b')).toNat < _
  convert hlt using 1
  exact congrArg (fun k : X.presheaf.stalk (f (p z)) →+* R =>
    (IsDiscreteValuationRing.addVal R (k b)).toNat) hc.symm

private lemma isBirational_of_isIso_restrict_comp {T' P T : Scheme.{u}} {c : T' ⟶ P}
    {π : P ⟶ T} {f : T' ⟶ T} (hfc : c ≫ π = f) (W : T.Opens)
    (hc : IsIso (c ∣_ π ⁻¹ᵁ W)) (hπ : IsIso (π ∣_ W))
    (hgen : ∀ z ∈ genericPoints T', c z ∈ π ⁻¹ᵁ W) (hW : ∀ z ∈ genericPoints T, z ∈ W) :
    IsBirational f := by
  subst hfc
  refine isBirational_of_isIso_morphismRestrict _ W ?_ (fun z hz => ?_) hW
  · rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' hc hπ
  · rw [Scheme.Hom.comp_apply]
    exact hgen z hz

private lemma dense_imageι_preimage_opensRange {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsOpenImmersion r] [IsDominant r.toImage] :
    Dense (r.imageι ⁻¹ᵁ r.opensRange : Set r.image) := by
  apply r.toImage.denseRange.mono
  rintro z ⟨w, rfl⟩
  change r.imageι (r.toImage w) ∈ r.opensRange
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
  exact ⟨w, rfl⟩

private theorem exists_common_normal_modification
    {S T S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    [IsNormal S] [IsNormal T] [IsNormal S']
    [IsReduced T] [IsReduced S'] (hNagata : IsNagataScheme S)
    (hdim : topologicalKrullDim S ≤ 2)
    (l : T ⟶ S) (q : S' ⟶ S) [IsProper l] [IsProper q]
    (hlbir : IsBirational l) (hqbir : IsBirational q) :
    ∃ (T' : Scheme.{u}) (p : T' ⟶ T) (q' : T' ⟶ S') (h : p ≫ l = q' ≫ q),
      IsNormal T' ∧ IsProper p ∧ IsProper q' ∧
      IsFinite (Limits.pullback.lift p q' h) ∧
      IsBirational p ∧ IsBirational q' := by
  obtain ⟨U, hUl, hUq, hUfinite, hUgeneric⟩ :=
    exists_common_finite_isomorphism_open l q hlbir hqbir hdim
  have hfpOpen : IsIso
      (Limits.pullback.fst l q ∣_ (l ⁻¹ᵁ U)) :=
    isIso_pullback_fst_over_open l q U hUq
  obtain ⟨r, hrY, hrX⟩ := exists_common_open_pullback_map l q U hUq
  have : IsOpenImmersion r :=
    isOpenImmersion_of_section_over_iso_open
      (Limits.pullback.fst l q) (l ⁻¹ᵁ U) hfpOpen r hrY
  have hrange : r.opensRange = Limits.pullback.fst l q ⁻¹ᵁ (l ⁻¹ᵁ U) :=
    opensRange_section_over_iso_open
      (Limits.pullback.fst l q) (l ⁻¹ᵁ U) hfpOpen r hrY
  have : IsReduced (l ⁻¹ᵁ U).toScheme := inferInstance
  have : NoetherianSpace (l ⁻¹ᵁ U).toScheme :=
    NoetherianSpace.set (l ⁻¹ᵁ U : Set T)
  have : QuasiCompact r := inferInstance
  have : IsDominant r.toImage := inferInstance
  have hImageReduced : IsReduced r.image :=
    isReduced_schemeTheoreticImage_of_isReduced r
  have hImageιOpen : IsIso (r.imageι ∣_ r.opensRange) :=
    isIso_imageι_morphismRestrict_of_isIso r r.opensRange
      (isIso_morphismRestrict_opensRange_of_isOpenImmersion r)
  obtain ⟨T', p, q', hcomm, hT'normal, hpProper, hq'Proper, hcomparison,
    hcomparisonOpen, hcomparisonGeneric⟩ :=
    exists_normalized_pullback_closed_subscheme hNagata l q r.ker
  have : IsProper p := hpProper
  have : IsNoetherian T' := isNoetherian_of_isProper_over_noetherian p
  have : IsNormal T' := hT'normal
  have : IsReduced T' := isReduced_of_isReduced_stalk _
  have : IsProper q' := hq'Proper
  have : IsFinite (Limits.pullback.lift p q' hcomm) := hcomparison
  have hiso := hcomparisonOpen r.opensRange hImageιOpen <|
    isNormal_of_iso (asIso (r.imageι ∣_ r.opensRange)).symm <|
      isNormal_of_iso r.isoOpensRange <| isNormal_open (l ⁻¹ᵁ U) (inferInstance : IsNormal T)
  have hgen := hcomparisonGeneric r.opensRange (dense_imageι_preimage_opensRange r)
  rw [hrange] at hiso hgen
  refine ⟨T', p, q', hcomm, hT'normal, hpProper, hq'Proper, hcomparison,
    isBirational_of_isIso_restrict_comp (Limits.pullback.lift_fst p q' hcomm) (l ⁻¹ᵁ U)
      hiso hfpOpen hgen fun z hz => hUgeneric (l z) (hlbir.bijOn.mapsTo hz), ?_⟩
  have hV : Limits.pullback.fst l q ⁻¹ᵁ (l ⁻¹ᵁ U) = Limits.pullback.snd l q ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Limits.pullback.condition]
  rw [hV] at hiso hgen
  exact isBirational_of_isIso_restrict_comp (Limits.pullback.lift_snd p q' hcomm) (q ⁻¹ᵁ U)
    hiso (isIso_pullback_snd_over_open l q U hUl) hgen
    fun z hz => hUgeneric (q z) (hqbir.bijOn.mapsTo hz)

private abbrev contractedPoints {X Y : Scheme.{u}} (f : Y ⟶ X) : Set Y :=
  {y | ¬ IsClosed ({y} : Set Y) ∧ IsClosed ({f y} : Set X)}

private abbrev HasDominatingTail {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∃ (Z : Scheme.{u}) (g : Z ⟶ X), NormalizedBlowUpTail X Z g ∧
    ∃ h : Z ⟶ Y, h ≫ f = g

private lemma hasDominatingTail_of_square
    {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {q : X' ⟶ X}
    {p : Y' ⟶ Y} {g : Y' ⟶ X'} (s : NormalizedBlowUpTail X X' q)
    (hcomm : p ≫ f = g ≫ q) (hg : HasDominatingTail g) : HasDominatingTail f := by
  obtain ⟨Z, r, t, h, hh⟩ := hg
  refine ⟨Z, r ≫ q, s.trans t, h ≫ p, ?_⟩
  rw [Category.assoc, hcomm, ← Category.assoc, hh]

private lemma exists_normalizedBlowUp_at_closed_point
    {S : Scheme.{u}} [IsNoetherian S] [IsNormal S]
    (hNagata : IsNagataScheme S) (hdim : topologicalKrullDim S ≤ 2)
    (hlocal : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ IsIntegral U.toScheme)
    (x : S) (hx : IsClosed ({x} : Set S)) (hgen : x ∉ genericPoints S) :
    ∃ (S' : Scheme.{u}) (q : S' ⟶ S), IsProper q ∧ IsNoetherian S' ∧ IsNormal S' ∧
      IsNagataScheme S' ∧ (∀ x : S', ∃ U : S'.Opens, x ∈ U ∧ IsIntegral U.toScheme) ∧
      IsBirational q ∧ topologicalKrullDim S' ≤ 2 ∧ NormalizedBlowUpTail S S' q ∧
      ∀ w : S', q w = x → ∃ d : S'.presheaf.stalk w,
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (q w))).map (q.stalkMap w).hom =
          Ideal.span {d} := by
  have : IsReduced S := isReduced_of_isReduced_stalk S
  let hS : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompactOpen_of_isNoetherian
  let S' := Stacks.Blowup.normalizedBlowUpScheme S hS x hx
  let q : S' ⟶ S := Stacks.Blowup.normalizedBlowUp S hS x hx
  have : IsProper q := Stacks.Blowup.isProper_normalizedBlowUp hS x hx hNagata
  have : IsNoetherian S' := isNoetherian_of_isProper_over_noetherian q
  have : IsNormal S' := Stacks.Blowup.isNormal_normalizedBlowUpScheme hS x hx
  have : IsReduced S' := isReduced_of_isReduced_stalk S'
  have hqbir : IsBirational q :=
    isBirational_normalizedBlowUp_of_genericPoints_disjoint_center hS x hx
      (Set.disjoint_singleton_right.mpr hgen)
  refine ⟨S', q, inferInstance, inferInstance, inferInstance,
    Stacks.Blowup.isNagataScheme_normalizedBlowUpScheme hS x hx hNagata,
    exists_integral_open_normalization
      (Stacks.Blowup.finite_irreducibleComponents_blowUp
        (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) hS), hqbir,
    (topologicalKrullDim_le_of_birational_of_locally_integral q hqbir hlocal).trans hdim, ?_,
    exists_principal_maximalIdeal_normalizedBlowUp hS x hx⟩
  simpa only [Category.comp_id] using (NormalizedBlowUpTail.blow (.refl (S := S)) hS x hx)

private lemma hasDominatingTail_of_transcendental_residue (n : ℕ)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (u : R)
    (ih : ∀ {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] [IsNormal S] [IsNormal T],
      IsNagataScheme S → topologicalKrullDim S ≤ 2 →
      (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ IsIntegral U.toScheme) →
      ∀ (l : T ⟶ S) [IsProper l], IsBirational l → topologicalKrullDim T ≤ 2 →
      (contractedPoints l).ncard < n → HasDominatingTail l) :
    ∀ m {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] [IsNormal S] [IsNormal T],
      IsNagataScheme S → topologicalKrullDim S ≤ 2 →
      (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ IsIntegral U.toScheme) →
      ∀ (l : T ⟶ S) [IsProper l], IsBirational l →
      topologicalKrullDim T ≤ 2 →
      ∀ (y : T), ¬ IsClosed ({y} : Set T) → IsClosed ({l y} : Set S) →
      ∀ (e : T.presheaf.stalk y ≃+* R) (a b : S.presheaf.stalk (l y)),
      e ((l.stalkMap y).hom b) ≠ 0 →
      e ((l.stalkMap y).hom a) = u * e ((l.stalkMap y).hom b) →
      (letI := (IsLocalRing.ResidueField.map
        (e.toRingHom.comp (l.stalkMap y).hom)).toAlgebra;
        Transcendental (IsLocalRing.ResidueField (S.presheaf.stalk (l y)))
          (IsLocalRing.residue R u)) →
      (IsDiscreteValuationRing.addVal R (e ((l.stalkMap y).hom b))).toNat = m →
      (contractedPoints l).ncard ≤ n → HasDominatingTail l := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ihm =>
    intro S T _ _ _ _ hNagataS hdimS hlocalS l _ hl hdimT y hy hly e a b hb hab hu hm hcard
    have : IsReduced T := isReduced_of_isReduced_stalk T
    obtain ⟨S', q, _, _, _, hNagataS', hlocalS', hqbir, hdimS', hs, hprincipal⟩ :=
      exists_normalizedBlowUp_at_closed_point hNagataS hdimS hlocalS (l y) hly
        (not_generic_image_of_contracted_nonclosed_point l hl y hy hly)
    have : IsReduced S' := isReduced_of_isReduced_stalk S'
    obtain ⟨T', p, g, hcomm, hnormal, hp, hg, hfin, hpbir, hgbir⟩ :=
      exists_common_normal_modification hNagataS hdimS l q hl hqbir
    have : IsNormal T' := hnormal
    have : IsProper p := hp
    have : IsProper g := hg
    have : IsNoetherian T' := isNoetherian_of_isProper_over_noetherian p
    have : IsReduced T' := isReduced_of_isReduced_stalk T'
    have : IsFinite (Limits.pullback.lift p g hcomm) := hfin
    have hdimT' : topologicalKrullDim T' ≤ 2 :=
      (topologicalKrullDim_le_of_birational_of_locally_integral g hgbir hlocalS').trans hdimS'
    have hbadFinite := finite_contracted_nonclosed_points l hl hdimT
    have hmap := mapsTo_contracted_points_of_finite_comparison l g p q hcomm
    have hinj := injOn_contracted_points_of_finite_comparison l g p q hcomm hpbir hdimT
    obtain ⟨hfinite', hbound⟩ :=
      finite_contracted_points_of_finite_comparison l g p q hcomm hpbir hdimT hbadFinite
    apply hasDominatingTail_of_square hs hcomm
    by_cases hsmall : (contractedPoints g).ncard < n
    · exact ih hNagataS' hdimS' hlocalS' g hgbir hdimT' hsmall
    · have hmem : y ∈ p '' contractedPoints g := by
        by_contra hmissing
        have hdrop := ncard_lt_of_injOn_with_missing_image hbadFinite p hmap hinj
          y ⟨hy, hly⟩ hmissing
        exact hsmall (lt_of_lt_of_le hdrop hcard)
      obtain ⟨z, hz, hpz⟩ := hmem
      subst y
      have : IsIso (p.stalkMap z) := isIso_stalkMap_over_nonclosed_point p hpbir hdimT z hy
      have hqz : q (g z) = l (p z) := (congrArg (fun k : T' ⟶ S => k z) hcomm).symm
      obtain ⟨e', a', b', hb', hab', hu', hlt⟩ := exists_fraction_descent_in_square l q p g
        hcomm z hz.2 (hprincipal (g z) hqz) e u a b hb hab hu
      exact ihm _ (hlt.trans_le (by omega)) hNagataS' hdimS' hlocalS' g hgbir hdimT'
        z hz.1 hz.2 e' a' b' hb' hab' hu' rfl (hbound.trans hcard)

private theorem hasDominatingTail_of_normal
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [IsNormal X] [IsNormal Y]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIntegral U.toScheme)
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (hdimY : topologicalKrullDim Y ≤ 2) : HasDominatingTail f := by
  classical
  generalize hn : (contractedPoints f).ncard = n
  induction n using Nat.strong_induction_on generalizing X Y with
  | h n ih =>
    have : IsReduced Y := isReduced_of_isReduced_stalk Y
    by_cases hbad : (contractedPoints f).Nonempty
    · obtain ⟨y, hy, hfy⟩ := hbad
      have hycodim := codimension_eq_one_of_nonclosed_of_not_generic hdimY y hy
        (not_generic_of_contracted_nonclosed_point f hf y hy hfy)
      obtain ⟨_, hDVR⟩ := isDiscreteValuationRing_stalk_of_codimension_eq_one y hycodim
      have : IsDiscreteValuationRing (Y.presheaf.stalk y) := hDVR
      let R : Type u := Y.presheaf.stalk y
      obtain ⟨u, hu⟩ := exists_transcendental_residue_of_nonclosed f y hy hfy
      obtain ⟨a, b, hb, hab⟩ := exists_stalk_numerator_denominator_of_locally_integral
        f hf hlocal y u
      refine hasDominatingTail_of_transcendental_residue n u ?_ _ hNagata hdim hlocal f hf hdimY
        y hy hfy (RingEquiv.refl R) a b hb hab hu rfl hn.le
      intro S T _ _ _ _ hNagataS hdimS hlocalS l _ hl hdimT hlt
      exact ih _ hlt hNagataS hdimS hlocalS l hl hdimT rfl
    · have : IsIso f := isIso_of_no_contracted_nonclosed_points f hf hdim fun y hy => by
        by_contra h
        exact hbad ⟨y, h, hy⟩
      exact ⟨X, 𝟙 X, .refl, inv f, IsIso.inv_hom_id f⟩

/-! ### The main result -/

/-- **Stacks Project, Tag 0BBT.** Let `X` be a Noetherian Nagata scheme of dimension two and let
`f : Y ⟶ X` be a proper birational morphism. Then there is a scheme `Z` obtained from the
normalization of `X` by finitely many normalized blowups at closed points which dominates `Y`:
its structure morphism `g : Z ⟶ X` factors as `h ≫ f` for a morphism `h : Z ⟶ Y`, so the whole
diagram commutes over `X`. -/
@[stacks 0BBT]
theorem exists_normalizedBlowUpChain_dominating
    {X Y : Scheme.{u}} [IsNoetherian X] (hNagata : IsNagataScheme X)
    (hdim : topologicalKrullDim X = 2) (f : Y ⟶ X)
    [IsProper f] (hf : IsBirational f) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ Y),
      NormalizedBlowUpChain X finite_irreducibleComponents_isCompactOpen_of_isNoetherian Z g ∧
        h ≫ f = g := by
  classical
  let hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompactOpen_of_isNoetherian
  by_cases hiso : IsIso f
  · have := hiso
    exact exists_normalizedBlowUpChain_dominating_of_isIso hNagata hX f
  let hY := finite_irreducibleComponents_of_isProper f
  obtain ⟨l, hlproper, hl⟩ :=
    exists_lift_normalization_of_proper_birational hX hNagata f hf hY
  have : IsFinite (Scheme.normalization X hX) :=
    Scheme.isFinite_normalization hNagata hX
  have hdim₀ : topologicalKrullDim (Scheme.normalizationScheme X hX) ≤ 2 :=
    (topologicalKrullDim_le_of_isIntegralHom (Scheme.normalization X hX)).trans hdim.le
  have hNagata₀ : IsNagataScheme (Scheme.normalizationScheme X hX) :=
    isNagataScheme_of_locallyOfFiniteType (Scheme.normalization X hX) hNagata
  have : IsNormal (Scheme.normalizationScheme X hX) := isNormal_normalizationScheme hX
  have : IsNormal (Scheme.normalizationScheme Y hY) := isNormal_normalizationScheme hY
  have : IsReduced (Scheme.normalizationScheme Y hY) := isReduced_of_isReduced_stalk _
  have : IsNoetherian (Scheme.normalizationScheme X hX) :=
    isNoetherian_of_isProper_over_noetherian (Scheme.normalization X hX)
  have : IsProper l := hlproper
  have : IsReduced (Scheme.normalizationScheme X hX) := isReduced_of_isReduced_stalk _
  have := isFinite_normalization_of_isProper_to_nagata hNagata f hY
  have hlbir : IsBirational l := isBirational_lift_normalizations hX hY f hf l hl
  have hdimY₀ : topologicalKrullDim (Scheme.normalizationScheme Y hY) ≤ 2 :=
    (topologicalKrullDim_le_of_birational_of_locally_integral l hlbir
      (exists_integral_open_normalization hX)).trans hdim₀
  have : IsNoetherian (Scheme.normalizationScheme Y hY) :=
    isNoetherian_of_isProper_over_noetherian l
  exact exists_normalizedBlowUpChain_dominating_of_normalizedTail hNagata hX hY f l hl
    (hasDominatingTail_of_normal hNagata₀ hdim₀ (exists_integral_open_normalization hX)
      l hlbir hdimY₀)

/-! ### Extending a rational map by normalized blowups

The scheme-theoretic image of the graph of a rational map into a scheme proper over the base is
proper and birational over the surface, so a chain of normalized blowups dominating it turns the
rational map into an honest morphism.
-/

/-- A morphism becomes an isomorphism over an open subset of its target as soon as the second
projection from its pullback along that open subset is an isomorphism. -/
private lemma isIso_morphismRestrict_of_isIso_pullback_snd {A B : Scheme.{u}} (p : A ⟶ B)
    (U : B.Opens) (hiso : IsIso (Limits.pullback.snd p U.ι)) : IsIso (p ∣_ U) := by
  have hcomp : IsIso ((pullbackRestrictIsoRestrict p U).hom ≫ p ∣_ U) := by
    rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict]
  exact IsIso.of_isIso_comp_left (pullbackRestrictIsoRestrict p U).hom (p ∣_ U)

/-- A morphism of schemes with Noetherian underlying spaces is birational as soon as it becomes
an isomorphism over a dense open subset of its target whose preimage is dense in the source. -/
private lemma isBirational_of_isIso_pullback_snd_of_dense {A B : Scheme.{u}}
    [NoetherianSpace A] [NoetherianSpace B] (p : A ⟶ B) (U : B.Opens)
    (hU : Dense (U : Set B)) (hV : Dense ((p ⁻¹ᵁ U : A.Opens) : Set A))
    (hiso : IsIso (Limits.pullback.snd p U.ι)) : IsBirational p :=
  isBirational_of_isIso_morphismRestrict p U
    (isIso_morphismRestrict_of_isIso_pullback_snd p U hiso)
    (fun x hx => genericPoint_mem_dense_open (p ⁻¹ᵁ U) hV x hx)
    (fun y hy => genericPoint_mem_dense_open U hU y hy)

/-- If `s ≫ p = ι` and the projection `pullback p ι ⟶ V` is an isomorphism, then `s` is
inverse to it, so `pullback.fst p ι ≫ f'` and `pullback.snd p ι ≫ s ≫ f'` agree. -/
private lemma pullback_fst_comp_eq_of_section {V W X Y : Scheme.{u}} (s : V ⟶ W) (p : W ⟶ X)
    (ι : V ⟶ X) (hs : s ≫ p = ι) [IsIso (Limits.pullback.snd p ι)] {f' : W ⟶ Y} {φ : V ⟶ Y}
    (hφ : s ≫ f' = φ) :
    Limits.pullback.fst p ι ≫ f' = Limits.pullback.snd p ι ≫ φ := by
  let t : V ⟶ Limits.pullback p ι :=
    Limits.pullback.lift s (𝟙 _) (by simpa only [Category.id_comp] using hs)
  have ht : t ≫ Limits.pullback.snd p ι = 𝟙 _ := Limits.pullback.lift_snd _ _ _
  have hte : t = (asIso (Limits.pullback.snd p ι)).inv := by
    apply (cancel_mono (Limits.pullback.snd p ι)).1
    simp [ht]
  apply (cancel_epi (asIso (Limits.pullback.snd p ι)).inv).1
  rw [← hte]
  simp only [t, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc,
    Category.id_comp, hφ]

/-- An agreement of two maps over `pullback p ι` transfers to `pullback g ι` along any
factorisation `h ≫ p = g`. -/
private lemma pullback_fst_comp_eq_of_factor {U W X Y Z : Scheme.{u}} {g : Z ⟶ X} {h : Z ⟶ W}
    {p : W ⟶ X} (ι : U ⟶ X) (hcomm : h ≫ p = g) {f' : W ⟶ Y} {φ : U ⟶ Y}
    (hagree : Limits.pullback.fst p ι ≫ f' = Limits.pullback.snd p ι ≫ φ) :
    Limits.pullback.fst g ι ≫ h ≫ f' = Limits.pullback.snd g ι ≫ φ := by
  let k : Limits.pullback g ι ⟶ Limits.pullback p ι :=
    Limits.pullback.lift (Limits.pullback.fst g ι ≫ h) (Limits.pullback.snd g ι)
      (by rw [Category.assoc, hcomm]; exact Limits.pullback.condition)
  have hkfst : k ≫ Limits.pullback.fst p ι = Limits.pullback.fst g ι ≫ h :=
    Limits.pullback.lift_fst _ _ _
  have hksnd : k ≫ Limits.pullback.snd p ι = Limits.pullback.snd g ι :=
    Limits.pullback.lift_snd _ _ _
  rw [← hksnd, ← reassoc_of% hkfst, Category.assoc, hagree]

/-- **Stacks Project, Tag 0C5I.** Let `X` be a Noetherian Nagata scheme of dimension two over
`S` and let `Y` be proper over `S`. Any `S`-rational map from `X` to `Y` becomes an `S`-morphism
after passing to the normalization of `X` followed by finitely many normalized blowups at closed
points, and the resulting morphism agrees with the rational map over its domain. -/
@[stacks 0C5I]
theorem exists_normalizedBlowUpChain_resolving_partialMap
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] [IsNoetherian X] [IsProper (Y ↘ S)]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X = 2)
    (f : X.PartialMap Y) [f.IsOver S] :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ Y),
      NormalizedBlowUpChain X finite_irreducibleComponents_isCompactOpen_of_isNoetherian Z g ∧
        h ≫ (Y ↘ S) = g ≫ (X ↘ S) ∧
          Limits.pullback.fst g f.domain.ι ≫ h =
            Limits.pullback.snd g f.domain.ι ≫ f.hom := by
  have hcompat : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) := by
    simpa only [Scheme.Opens.ι_comp_over] using
      (Scheme.Hom.isOver_iff (f := f.hom) (S := S)).mp inferInstance
  have : NoetherianSpace f.domain.toScheme := NoetherianSpace.set (f.domain : Set X)
  -- The graph of the rational map inside `Y ×_S X`, and its scheme-theoretic image.
  let q : f.domain.toScheme ⟶ Limits.pullback (Y ↘ S) (X ↘ S) :=
    Limits.pullback.lift f.hom f.domain.ι hcompat
  let p : q.image ⟶ X := q.imageι ≫ Limits.pullback.snd (Y ↘ S) (X ↘ S)
  let f' : q.image ⟶ Y := q.imageι ≫ Limits.pullback.fst (Y ↘ S) (X ↘ S)
  have hq : q ≫ Limits.pullback.snd (Y ↘ S) (X ↘ S) = f.domain.ι :=
    Limits.pullback.lift_snd _ _ _
  have hqImage : q.toImage ≫ p = f.domain.ι := by
    change q.toImage ≫ q.imageι ≫ Limits.pullback.snd (Y ↘ S) (X ↘ S) = f.domain.ι
    rwa [← Category.assoc, Scheme.Hom.toImage_imageι]
  have : IsProper p := by
    change IsProper (q.imageι ≫ Limits.pullback.snd (Y ↘ S) (X ↘ S))
    infer_instance
  have hiso : IsIso (Limits.pullback.snd p f.domain.ι) := by
    change IsIso (Limits.pullback.snd
      (q.imageι ≫ Limits.pullback.snd (Y ↘ S) (X ↘ S)) f.domain.ι)
    exact isIso_pullback_snd_imageι_comp_of_section
      (Limits.pullback.snd (Y ↘ S) (X ↘ S)) f.domain
      (fun _ _ _ ↦ NoetherianSpace.isCompact _) q hq
  have : IsNoetherian q.image := isNoetherian_of_isProper_over_noetherian p
  have hVdense : Dense ((p ⁻¹ᵁ f.domain : q.image.Opens) : Set q.image) := by
    apply q.toImage.denseRange.mono
    rintro z ⟨w, rfl⟩
    have hpoint : p (q.toImage w) = f.domain.ι w := congrArg (fun k => k w) hqImage
    change p (q.toImage w) ∈ f.domain
    rw [hpoint]
    exact w.2
  have hpBir : IsBirational p :=
    isBirational_of_isIso_pullback_snd_of_dense p f.domain f.dense_domain hVdense hiso
  have hagree : Limits.pullback.fst p f.domain.ι ≫ f' =
      Limits.pullback.snd p f.domain.ι ≫ f.hom :=
    pullback_fst_comp_eq_of_section q.toImage p f.domain.ι hqImage (by
      simp only [f', ← Category.assoc, Scheme.Hom.toImage_imageι, q, Limits.pullback.lift_fst])
  have hfs : f' ≫ (Y ↘ S) = p ≫ (X ↘ S) := by
    change (q.imageι ≫ Limits.pullback.fst (Y ↘ S) (X ↘ S)) ≫ (Y ↘ S) =
      (q.imageι ≫ Limits.pullback.snd (Y ↘ S) (X ↘ S)) ≫ (X ↘ S)
    simp only [Category.assoc, Limits.pullback.condition]
  obtain ⟨Z, g, h, hchain, hcomm⟩ :=
    exists_normalizedBlowUpChain_dominating (X := X) (Y := q.image) hNagata hdim p hpBir
  refine ⟨Z, g, h ≫ f', hchain, ?_, ?_⟩
  · rw [Category.assoc, hfs, ← Category.assoc, hcomm]
  · exact pullback_fst_comp_eq_of_factor f.domain.ι hcomm hagree

end Stacks.ResolutionOfSurfaces

end
