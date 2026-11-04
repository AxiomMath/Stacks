module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.FlatModuleTorDimension
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleSquare

/-!
# Perfection of the derived direct image of a flat module over a Noetherian base

Let `S` be a Noetherian scheme, `f : X ⟶ S` a proper morphism and `ℱ` an `𝒪_X`-module of finite
presentation, flat over `S`. Then `Rf_*ℱ` is a perfect object of `D(𝒪_S)`.

This is the Noetherian case of the perfection half of [Stacks, Tag 0B91] (2), the case the
source reduces to by Noetherian approximation. By [Stacks, Tag 08CQ] perfectness is
pseudo-coherence together with locally finite Tor dimension. Pseudo-coherence is the
pseudo-coherence half of [Stacks, Tag 08EV], with [Stacks, Tag 02O5] supplied by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`; `ℱ` is
coherent because `X` is locally Noetherian ([Stacks, Tag 01XZ]). Locally finite Tor dimension is
read on the affine opens of `S` ([Stacks, Tag 08FE]) and there is
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_single_of_isFlatOver`.

## Main results

* `AlgebraicGeometry.isPerfect_derivedPushforwardModules_single_of_isNoetherian`.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.TorAmplitude
open Stacks.AlgebraicGeometry.ProperSupportCoherent
  (isPseudoCoherent_derivedPushforward_of_isProperOver_supp)
open Stacks.AlgebraicGeometry.PerfectProperDirectImage
  (locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The perfection half of [Stacks, Tag 0B91] (2) over a Noetherian base.** Let `S` be a
Noetherian scheme, `f : X ⟶ S` proper and `ℱ` an `𝒪_X`-module of finite presentation, flat over
`S`. Then `Rf_*ℱ` is a perfect object of `D(𝒪_S)`. -/
theorem isPerfect_derivedPushforwardModules_single_of_isNoetherian [IsNoetherian S] [IsProper f]
    (F : X.Modules) [F.IsFinitePresentation] (hF : IsFlatOver f.toLRSHom.toShHom F) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨hqcF, hftF⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation F
      inferInstance
  set E := (DerivedCategory.singleFunctor X.Modules 0).obj F with hE
  have hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent := by
    intro j
    by_cases hj : j = 0
    · subst hj
      exact isCoherent_of_moduleIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app F).symm
        (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
          F)
    · refine ProperCoherentFiniteType.isCoherent_of_isZero ?_
      rcases lt_or_gt_of_ne hj with h | h
      exacts [E.isZero_of_isGE 0 j h, E.isZero_of_isLE 0 j h]
  have hproper : ∀ T : Closeds X, IsProperOver f T := fun T => by
    show IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f)
    infer_instance
  have hpc : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
    isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh (fun _ => hproper _)
      AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase 0 0
      inferInstance inferInstance
  refine isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) _
    ((isPseudoCoherent_iff_isPseudoCoherent' (X := S.toRingedSpace) _).2 hpc) ?_
  refine locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen f E fun ⟨U, hU⟩ => ?_
  have : IsAffine U.toScheme := hU
  have : CompactSpace (f ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := f) _ U.isOpen hU.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ U).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ⁻¹ᵁ U).ι
  have hqcV : (F.restrict (f ⁻¹ᵁ U).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f := (f ⁻¹ᵁ U).ι) F
  have hflV : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      (F.restrict (f ⁻¹ᵁ U).ι) :=
    (isFlatOver_iff_of_iso _
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app F)).2
      (isFlatOver_restrict_of_flatOnPreimage f F U fun x _ => hF x)
  obtain ⟨a, b, hab⟩ := hasFiniteTorDimension_schemeDerivedPushforward_single_of_isFlatOver
    (f ∣_ U) _ hflV
  exact ⟨a, b, FlatOpcycles.hasTorAmplitude_of_iso
    (X := S.toRingedSpace.restrict U.isOpenEmbedding) hab
    ((schemeDerivedPushforward (f ∣_ U)).mapIso
      (((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapDerivedCategorySingleFunctor
        0).app F))⟩

end AlgebraicGeometry
