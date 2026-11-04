module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforward
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.InstanceIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardQuasiCoherence
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived direct image along a proper morphism preserves pseudo-coherence

Let `f : X ⟶ S` be a proper morphism of schemes with `S` Noetherian. Then `Rf_*` carries
pseudo-coherent objects of `D(𝒪_X)` to pseudo-coherent objects of `D(𝒪_S)`, where `Rf_*` is
`Stacks.Duality.derivedPushforward` and the derived categories are the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## Main results

* `isPseudoCoherent_derivedPushforward_of_isProper_of_isGE_of_isLE`: the bounded case, at the
  locally small model.
* `isPseudoCoherent_derivedPushforward_of_isProper_of_isLE`: the bounded above case, at the
  locally small model.
* `isPseudoCoherent_derivedPushforward_of_isProper`: `Rf_*` preserves pseudo-coherence, at the
  locally small model.
* `isPseudoCoherent_iff_isBoundedAbove_isCoherent_homology`: on a Noetherian scheme an object of
  the locally small `D(𝒪_Z)` is pseudo-coherent if and only if it is bounded above with coherent
  cohomology sheaves.

## References

* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

/-! ### At the standard model -/

section Standard

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A proper morphism to a Noetherian scheme has Noetherian source. -/
private theorem isNoetherian_of_isProper_of_isNoetherian {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [IsProper f] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- For `f` proper over a Noetherian base, `Rf_*` carries a bounded object with coherent
cohomology to a pseudo-coherent object. -/
theorem isPseudoCoherent_derivedPushforwardModules_of_isProper_of_isGE_of_isLE [IsNoetherian S]
    [IsProper f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh
    (fun _ => RelativelyPerfectProperPushforward.isProperOver_of_isProper f _)
    ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase a b hGE hLE

/-- The cohomology sheaves of a truncation from below of an object with coherent cohomology
sheaves are coherent. -/
theorem isCoherent_homology_truncGE (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (m j : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules j).obj
      ((DerivedCategory.TStructure.t.truncGE m).obj E)).IsCoherent := by
  by_cases hj : m ≤ j
  · have := AlgebraicGeometry.isIso_homology_truncGE E m j hj
    have : ((DerivedCategory.homologyFunctor X.Modules j).obj
        ((𝟭 (DerivedCategory X.Modules)).obj E)).IsCoherent := hcoh j
    exact CoherentDevissage.isCoherent_of_iso (R := X.ringCatSheaf)
      (asIso ((DerivedCategory.homologyFunctor X.Modules j).map
        ((DerivedCategory.TStructure.t.truncGEπ m).app E))).symm
  · exact CoherentDevissage.isCoherent_of_isZero (R := X.ringCatSheaf)
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.TStructure.t.truncGE m).obj E) m j
        (by omega))

/-- For `f` proper over a Noetherian base, `Rf_*` carries a pseudo-coherent object to a
pseudo-coherent object. -/
theorem isPseudoCoherent_derivedPushforwardModules_of_isProper [IsNoetherian S] [IsProper f]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) := by
  have : IsNoetherian X := isNoetherian_of_isProper_of_isNoetherian f
  have hqcE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent X E hE
  obtain ⟨⟨b, hb⟩, hcoh⟩ :=
    (isPseudoCoherent_iff_boundedAbove_coherent_homology X ⟨E, hqcE⟩).1 hE
  have hLE : E.IsLE b := (DerivedCategory.isLE_iff E b).2 hb
  obtain ⟨N, hN⟩ := Stacks.Duality.exists_isLE_derivedPushforward_obj f
  have hqcR : ∀ i : ℤ, ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((derivedPushforwardModules f).obj E)).IsQuasicoherent :=
    isQuasicoherent_homologyFunctor_derivedPushforward f E hqcE
  refine (isPseudoCoherent_iff_boundedAbove_coherent_homology S ⟨_, hqcR⟩).2
    ⟨⟨b + N, fun n hn => ?_⟩, fun n => ?_⟩
  · exact (DerivedCategory.isLE_iff _ _).1 (hN E hqcE b hLE) n hn
  · let T := (derivedPushforwardModules f).mapTriangle.obj
      ((DerivedCategory.TStructure.t.triangleLEGE (n - N - 1) (n - N) (by omega)).obj E)
    have hT : T ∈ distTriang (DerivedCategory S.Modules) :=
      (derivedPushforwardModules f).map_distinguished _
        (DerivedCategory.TStructure.t.triangleLEGE_distinguished _ _ (by omega) E)
    have h₁ : T.obj₁.IsLE (n - N - 1 + N) := hN _
      (AlgebraicGeometry.isQuasicoherent_homology_truncLE X E hqcE _) (n - N - 1) inferInstance
    have hz : IsZero ((DerivedCategory.homologyFunctor S.Modules n).obj T.obj₁) :=
      DerivedCategory.isZero_of_isLE _ (n - N - 1 + N) n (by omega)
    have hz' : IsZero ((DerivedCategory.homologyFunctor S.Modules (n + 1)).obj T.obj₁) :=
      DerivedCategory.isZero_of_isLE _ (n - N - 1 + N) (n + 1) (by omega)
    have : Mono ((DerivedCategory.homologyFunctor S.Modules n).map T.mor₂) :=
      ((DerivedCategory.homologyFunctor S.Modules 0).homologySequence_mono_shift_map_mor₂_iff
        T hT n).2 (hz.eq_of_src _ _)
    have : Epi ((DerivedCategory.homologyFunctor S.Modules n).map T.mor₂) :=
      ((DerivedCategory.homologyFunctor S.Modules 0).homologySequence_epi_shift_map_mor₂_iff
        T hT n (n + 1) rfl).2 (hz'.eq_of_tgt _ _)
    have hiso : IsIso ((DerivedCategory.homologyFunctor S.Modules n).map T.mor₂) :=
      isIso_of_mono_of_epi _
    have := hLE
    have hb₃ := derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp f
      ((DerivedCategory.TStructure.t.truncGE (n - N)).obj E) (isCoherent_homology_truncGE E hcoh _)
      (fun _ => RelativelyPerfectProperPushforward.isProperOver_of_isProper f _)
      ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase (n - N) b
      inferInstance inferInstance
    have : ((DerivedCategory.homologyFunctor S.Modules n).obj T.obj₃).IsCoherent := hb₃.2 n
    exact CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
      (@asIso _ _ _ _ _ hiso)

end Standard

/-! ### At the locally small model -/

section LocallySmall

variable {Z : Scheme.{u}}

/-- The cohomology sheaves of the object represented by a complex `K` are the same at the locally
small model and at the standard model: both are the cohomology sheaves of `K`. -/
def homologyQObjStandardIso (K : CochainComplex Z.Modules ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor Z.Modules n).obj (DerivedCategory.Q.obj K) ≅
      (@DerivedCategory.homologyFunctor Z.Modules _ _ (HasDerivedCategory.standard Z.Modules)
        n).obj ((@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard Z.Modules)).obj K) :=
  (DerivedCategory.homologyFunctorFactors Z.Modules n).app K ≪≫
    ((@DerivedCategory.homologyFunctorFactors Z.Modules _ _
      (HasDerivedCategory.standard Z.Modules) n).app K).symm

/-- The cohomology sheaves of an object `E` of the locally small `D(𝒪_Z)` are those of the
standard model object represented by a complex `K` with `Q K ≅ E`. -/
private def homologyIsoStandard {E : DerivedCategory Z.Modules} (K : CochainComplex Z.Modules ℤ)
    (eQ : DerivedCategory.Q.obj K ≅ E) (n : ℤ) :
    (DerivedCategory.homologyFunctor Z.Modules n).obj E ≅
      (@DerivedCategory.homologyFunctor Z.Modules _ _ (HasDerivedCategory.standard Z.Modules)
        n).obj ((@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard Z.Modules)).obj K) :=
  (DerivedCategory.homologyFunctor Z.Modules n).mapIso eQ.symm ≪≫ homologyQObjStandardIso K n

/-- On a Noetherian scheme an object of the locally small `D(𝒪_Z)` is pseudo-coherent if and only
if it is bounded above with coherent cohomology sheaves. -/
theorem isPseudoCoherent_iff_isBoundedAbove_isCoherent_homology [IsNoetherian Z]
    (E : DerivedCategory Z.Modules) :
    RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) E ↔
      DerivedCategoryB.IsBoundedAbove E ∧
        ∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj E).IsCoherent := by
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eH := homologyIsoStandard K eQ
  have hPC : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) E ↔
      @RingedSpace.IsPseudoCoherent Z.toRingedSpace (HasDerivedCategory.standard Z.Modules)
        ((@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard Z.Modules)).obj K) :=
    ⟨fun h => RingedSpace.isPseudoCoherent_Q_transfer _ _ K (h.of_iso eQ.symm),
      fun h => (RingedSpace.isPseudoCoherent_Q_transfer _ _ K h).of_iso eQ⟩
  rw [hPC]
  constructor
  · intro h
    have hqc := @isQuasicoherentDerived_of_isPseudoCoherent Z
      (HasDerivedCategory.standard Z.Modules) _ h
    obtain ⟨⟨b, hb⟩, hc⟩ := (isPseudoCoherent_iff_boundedAbove_coherent_homology Z ⟨_, hqc⟩).1 h
    refine ⟨⟨b, fun n hn => (hb n hn).of_iso (eH n)⟩, fun n => ?_⟩
    have := hc n
    exact CoherentDevissage.isCoherent_of_iso (R := Z.ringCatSheaf) (eH n)
  · rintro ⟨⟨b, hb⟩, hc⟩
    have hc' : ∀ n : ℤ, ((@DerivedCategory.homologyFunctor Z.Modules _ _
        (HasDerivedCategory.standard Z.Modules) n).obj
          ((@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard Z.Modules)).obj
            K)).IsCoherent := fun n => by
      have := hc n
      exact CoherentDevissage.isCoherent_of_iso (R := Z.ringCatSheaf) (eH n).symm
    have hqc : ∀ n : ℤ, ((@DerivedCategory.homologyFunctor Z.Modules _ _
        (HasDerivedCategory.standard Z.Modules) n).obj
          ((@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard Z.Modules)).obj
            K)).IsQuasicoherent := fun n => by
      have := hc' n
      exact isQuasicoherent_of_isCoherent _
    exact (isPseudoCoherent_iff_boundedAbove_coherent_homology Z ⟨_, hqc⟩).2
      ⟨⟨b, fun n hn => (hb n hn).of_iso (eH n).symm⟩, hc'⟩

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Pseudo-coherence of `Rf_*E` transports from the standard model to the locally small one.**
If `E` is represented by the complex `K` and `Rf_*` of the object represented by `K` at the
standard model is pseudo-coherent, then `Rf_*E` is pseudo-coherent at the locally small model. -/
theorem isPseudoCoherent_derivedPushforward_of_standard (E : DerivedCategory X.Modules)
    (K : CochainComplex X.Modules ℤ) (eQ : DerivedCategory.Q.obj K ≅ E)
    (h : @RingedSpace.IsPseudoCoherent S.toRingedSpace (HasDerivedCategory.standard S.Modules)
      ((derivedPushforwardModules f).obj
        ((@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard X.Modules)).obj K))) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((Stacks.Duality.derivedPushforward f).obj E) := by
  obtain ⟨I, s, hI, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X K
  let eStd := (derivedPushforwardModules f).mapIso
      ((@DerivedCategory.quotientCompQhIso X.Modules _ _
        (HasDerivedCategory.standard X.Modules)).app K).symm ≪≫
    @Stacks.Duality.derivedPushforwardObjIso X S f (HasDerivedCategory.standard X.Modules)
      (HasDerivedCategory.standard S.Modules) K I s hI hs
  let eLS := (Stacks.Duality.derivedPushforward f).mapIso
      (eQ.symm ≪≫ ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm) ≪≫
    Stacks.Duality.derivedPushforwardObjIso f s hI hs
  exact @RingedSpace.IsPseudoCoherent.of_iso _ (Scheme.Modules.hasDerivedCategory S) _ _
    (RingedSpace.isPseudoCoherent_Q_transfer (HasDerivedCategory.standard S.Modules)
      (Scheme.Modules.hasDerivedCategory S) _
      (@RingedSpace.IsPseudoCoherent.of_iso _ (HasDerivedCategory.standard S.Modules) _ _ h eStd))
    eLS.symm

/-- For `f` proper over a Noetherian base, `Rf_*` carries a bounded object of the locally small
`D(𝒪_X)` with coherent cohomology sheaves to a pseudo-coherent object of `D(𝒪_S)`. -/
theorem isPseudoCoherent_derivedPushforward_of_isProper_of_isGE_of_isLE [IsNoetherian S]
    [IsProper f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((Stacks.Duality.derivedPushforward f).obj E) := by
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eH := homologyIsoStandard K eQ
  refine isPseudoCoherent_derivedPushforward_of_standard f E K eQ
    (isPseudoCoherent_derivedPushforwardModules_of_isProper_of_isGE_of_isLE f _
      (fun j => ?_) a b
      ((@DerivedCategory.isGE_iff X.Modules _ _ (HasDerivedCategory.standard X.Modules) _ a).2
        fun i hi => ((DerivedCategory.isGE_iff E a).1 hGE i hi).of_iso (eH i).symm)
      ((@DerivedCategory.isLE_iff X.Modules _ _ (HasDerivedCategory.standard X.Modules) _ b).2
        fun i hi => ((DerivedCategory.isLE_iff E b).1 hLE i hi).of_iso (eH i).symm))
  have := hcoh j
  exact CoherentDevissage.isCoherent_of_iso (R := X.ringCatSheaf) (eH j).symm

/-- **`Rf_*` preserves pseudo-coherence at the locally small model.** For `f : X ⟶ S` proper
with `S` Noetherian, `Rf_*` carries a pseudo-coherent object of the locally small `D(𝒪_X)` to a
pseudo-coherent object of `D(𝒪_S)`. -/
theorem isPseudoCoherent_derivedPushforward_of_isProper [IsNoetherian S] [IsProper f]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((Stacks.Duality.derivedPushforward f).obj E) := by
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  exact isPseudoCoherent_derivedPushforward_of_standard f E K eQ
    (isPseudoCoherent_derivedPushforwardModules_of_isProper f _
      (RingedSpace.isPseudoCoherent_Q_transfer _ _ K (hE.of_iso eQ.symm)))

/-- For `f` proper with `S` Noetherian, `Rf_*` carries a bounded above object of the locally small
`D(𝒪_X)` with coherent cohomology sheaves to a pseudo-coherent object of `D(𝒪_S)`. -/
@[sga "6 III 2.2.1" "special case"]
theorem isPseudoCoherent_derivedPushforward_of_isProper_of_isLE [IsNoetherian S] [IsProper f]
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (b : ℤ) (hLE : E.IsLE b) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((Stacks.Duality.derivedPushforward f).obj E) := by
  have : IsNoetherian X := isNoetherian_of_isProper_of_isNoetherian f
  exact isPseudoCoherent_derivedPushforward_of_isProper f E
    ((isPseudoCoherent_iff_isBoundedAbove_isCoherent_homology E).2
      ⟨⟨b, (DerivedCategory.isLE_iff E b).1 hLE⟩, hcoh⟩)

end LocallySmall

end Stacks.AlgebraicGeometry.ProperSupportCoherent
