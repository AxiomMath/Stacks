module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Etale.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSourceRefined
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallEtaleSite.SpfEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.RingTheory.AdicCompletion.DvrValuedPoints
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic
import all StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective

/-!
# A surjective étale morphism of formal algebraic spaces is rig-surjective

A morphism of locally Noetherian formal algebraic spaces which is representable by algebraic
spaces, étale and surjective is rig-surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_of_isRepresentableEtale_of_isSurjective'`: a
  representable étale surjective morphism of locally Noetherian formal algebraic spaces is
  rig-surjective.
-/

@[expose] public noncomputable section

open Cardinal

universe u

section Main

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of locally Noetherian formal algebraic spaces over `S` which is representable by
algebraic spaces, étale and surjective is rig-surjective. -/
@[stacks 0AQU]
theorem isRigSurjective_of_isRepresentableEtale_of_isSurjective'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hf : IsRepresentableEtale B S hS f) (hsurj : IsSurjective B S hS f) :
    IsRigSurjective B S hS f := by
  classical
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
  have hsq : IsPullback (pullback.fst p f) (pullback.snd p f) p f := IsPullback.of_hasPullback p f
  have hRcard : #R < B.cutoff := mk_lt_cutoff_of_quotientSystem hRadic hRcomplete D
  have hZ : IsFormalAlgebraicSpace B S hS (pullback p f) :=
    isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS p f hY.1
      (isAffineFormalAlgebraicSpace_formalSpectrum hRweak D
        (hasLargeSite_of_mk_lt_cutoff D hRcard)) hX.1
  obtain ⟨zpt⟩ := nonempty_pointsULift_formalSpectrum B S hS hRadic D
  obtain ⟨zZ, -⟩ := IsSurjective.of_isPullback B S hS hsq hsurj zpt
  obtain ⟨-, ιset, V, a, hVaff, hVet, hVsurj⟩ := hZ
  obtain ⟨i, Wsite, ⟨wpt⟩, ⟨t⟩⟩ := exists_section_of_pointsULift_of_isLocallySurjective
    B S hS a hVsurj ⟨zZ⟩
  obtain ⟨A, hAring, hAalg, hAetale, E, c, ε, hc, hε⟩ :=
    isEssentiallySurjectiveSpf B S hS R hRweak D (hasLargeSite_of_mk_lt_cutoff D hRcard) (V i)
      (a i ≫ pullback.fst p f)
      (hVaff i) (IsRepresentableEtale.comp B S hS (hVet i)
        (isRepresentableEtale_of_isPullback B S hS hsq.flip hf))
  have hnt : Nontrivial (TopologicalRing.CompletionOver (algebraMap R A)) :=
    nontrivial_of_section_formalSpectrum B S hS E wpt
      (ε.hom.hom.app (Opposite.op Wsite) t)
  have hAne : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≠ ⊤ :=
    map_ne_top_of_nontrivial_completionOver hRadic (algebraMap R A) hnt
  have hAcard : #A < B.cutoff :=
    (Cardinal.mk_le_max_aleph0_of_finiteType R A).trans_lt
      (max_lt B.aleph0_lt_cutoff hRcard)
  obtain ⟨W, hWring, hWdom, hWdvr, hRW, hWext, hWcomplete, g, hgcomp, hWcard⟩ :=
    exists_isAdicComplete_isDiscreteValuationRing_of_etale R A hAne B.cutoff
      B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hAcard
  let : CommRing W := hWring
  let : IsDomain W := hWdom
  let : IsDiscreteValuationRing W := hWdvr
  let : Algebra R W := hRW
  let : IsDiscreteValuationRing.IsExtension R W := hWext
  let : IsAdicComplete (IsLocalRing.maximalIdeal W) W := hWcomplete
  let : TopologicalSpace W := (IsLocalRing.maximalIdeal W).adicTopology
  have hWtopring : IsTopologicalRing W :=
    (IsLocalRing.maximalIdeal W).ringFilterBasis.isTopologicalRing
  have hWlin : IsLinearTopology W W := (IsLocalRing.maximalIdeal W).isLinearTopology
  have hWadic : _root_.IsAdic (IsLocalRing.maximalIdeal W) := rfl
  have hmle : (IsLocalRing.maximalIdeal R).map (algebraMap R W) ≤
      IsLocalRing.maximalIdeal W :=
    Ideal.map_le_iff_le_comap.mpr (by rw [IsLocalRing.maximalIdeal_comap])
  have hgle : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).map g ≤
      IsLocalRing.maximalIdeal W := by
    rwa [Ideal.map_map, hgcomp]
  obtain ⟨G, hGcont, hGofTarget⟩ :=
    exists_continuous_ringHom_completionOver hRadic hWadic (algebraMap R A) g hgle
  have hGcanon : G.comp (TopologicalRing.CompletionOver.canonicalMap (algebraMap R A)) =
      algebraMap R W := by
    rw [← TopologicalRing.CompletionOver.ofTarget_comp, ← RingHom.comp_assoc, hGofTarget, hgcomp]
  obtain ⟨DW, e, he⟩ := exists_quotientSystem_continuousHom hRweak D (algebraMap R W)
    (continuous_of_isAdic_of_map_le hRadic hWadic _ hmle) hWcard
  have hAcweak : TopologicalRing.IsWeaklyAdmissible
      (TopologicalRing.CompletionOver (algebraMap R A)) :=
    TopologicalRing.completionOver_isWeaklyAdmissible (algebraMap R A) hRweak
  obtain ⟨e', he'⟩ := exists_continuousHom_of_comp hRweak c e G hGcont (by rwa [he, hc])
  refine ⟨W, hWring, hWdom, hWdvr, hRW, hWext, inferInstance, hWtopring, hWlin, hWadic,
    hWcomplete, DW, e,
    formalSpectrumMap hAcweak e' ≫ ε.inv ≫ a i ≫ pullback.snd p f, he, ?_⟩
  have hcomp : ContinuousHom.comp hAcweak hRweak e' c = e :=
    continuousHom_ext B S hS (by rwa [ContinuousHom.comp_toRingHom, he', hc, he])
  rw [← hcomp, ← formalSpectrumMap_comp_eq hAcweak hRweak e' c]
  simp only [Category.assoc, ← hsq.w, ← reassoc_of% hε, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.FormalSpace

end Main

end
