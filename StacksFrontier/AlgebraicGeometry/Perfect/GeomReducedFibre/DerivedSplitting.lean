module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.FlatModelSplitting
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseAlternatingCechModuleTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.BoundednessStandardModel

/-!
# The derived direct image over an affine base, read on the Čech model

Let `f : X ⟶ Spec A` be quasi-compact and quasi-separated and `G` a quasi-coherent
`𝒪_X`-module. The derived direct image `Rf_*G` has quasi-coherent cohomology, so it is the
derived sheafification `M̃` of an object `M` of `D(A)` ([Stacks, Tag 06Z0]), and `M` is the
derived global sections `RΓ(X, G)` (the unit of the derived `~ ⊣ Γ` adjunction and Leray,
[Stacks, Tag 0D5W]). With the Čech model this reads `Rf_*G ≅ Č(U, G)~` in `D(𝒪_{Spec A})`.

Everything here is at the standard model of the derived categories, named explicitly, which is
the model of the inputs.

## Main results

* `StacksDraft.Perfect.GeomReducedFibre.nonempty_derivedPushforward_iso_tilde`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- **`Rf_*G` over an affine base is the derived sheafification of `RΓ(X, G)`**, at the standard
model. -/
theorem nonempty_derivedPushforward_iso_tilde {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f] (G : X.Modules)
    [G.IsQuasicoherent] :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (Spec (.of A)).Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    Nonempty ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≅
      (tilde.functor (.of A)).mapDerivedCategory.obj (derivedGlobalSectionsOverBase f G)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (Spec (.of A)).Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let E := (derivedPushforwardModules f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj G)
  obtain ⟨M, ⟨e⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (.of A) E
    (isQuasicoherent_homology_derivedPushforward_single_zero f G ‹_›)
  have := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit (.of A)
  let eu : M ≅ (derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).obj
      ((derivedTilde (.of A) ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec (.of A)).Modules)
        (SheafOfModules.isQuasicoherent (Spec (.of A)).ringCatSheaf)).ι).obj M) :=
    asIso ((derivedTildeGlobalSectionsAdjunction (.of A)).val.unit.app M)
  obtain ⟨eB⟩ := nonempty_derivedGlobalSectionsOver_iso_derivedGlobalSectionsOverBase f G
  let e'' : M ≅ derivedGlobalSectionsOverBase f G :=
    eu ≪≫ (derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).mapIso
      ((derivedTildeCompι (.of A)).app M ≪≫ e) ≪≫
      ((derivedGlobalSectionsOverPushforwardIso f).app _).symm ≪≫ eB
  exact ⟨e.symm ≪≫ (tilde.functor (.of A)).mapDerivedCategory.mapIso e''⟩

/-- `D(R)` at the standard model has `Q (single M) ≅ single M`; a flat module placed in degree `0`
has a flat representative concentrated in degree `0`. -/
theorem hasFlatRepresentative_single_of_flat {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    [Module.Flat R M] :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    StacksDraft.TorAmplitude.HasFlatRepresentative.{u, u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) 0 0 := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  refine ⟨(CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M, fun i => ?_, inferInstance,
    inferInstance, ⟨(DerivedCategory.singleFunctorIsoCompQ _ 0).app M⟩⟩
  rcases eq_or_ne i 0 with rfl | hi
  · exact Module.Flat.of_linearEquiv
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).toLinearEquiv
  · have : Subsingleton ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M |>.X i) :=
      ModuleCat.isZero_iff_subsingleton.1
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
    infer_instance

/-- Tor amplitude of an object of `D(𝒪_X)` at the standard model, in the reading of
[Stacks, Tag 08CG] at the derived tensor product of [Stacks, Tag 06YU]. -/
abbrev HasTorAmplitudeStd (X : Scheme.{u})
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) (a b : ℤ) :
    Prop :=
  @Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
    (HasDerivedCategory.standard X.Modules) E a b

/-- Extending scalars along `R → R_a` termwise computes the derived localization functor. -/
private theorem nonempty_Q_extendScalarsCx_iso_localizationAwayFunctorAux {R : Type u}
    [CommRing R] (a : R) (D : CochainComplex (ModuleCat.{u} R) ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away a))
    Nonempty (DerivedCategory.Q.obj (extendScalarsCx (algebraMap R (Localization.Away a)) D) ≅
      (PseudoCoherence.localizationAwayFunctorAux.{u, u} a).obj (DerivedCategory.Q.obj D)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away a))
  let Fg := ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away a))
  let : Fg.Additive := extendScalars_additive.{u, u, u} _
  let : PreservesFiniteLimits Fg :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away a) (Submonoid.powers a)))
  let : PreservesColimitsOfSize.{0, 0} Fg :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap R (Localization.Away a))).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits Fg := PreservesColimitsOfSize.preservesFiniteColimits Fg
  exact ⟨(Fg.mapDerivedCategoryFactors.app D).symm⟩

section Splitting

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) [IsSeparated g]
  [QuasiCompact g] {I : Type u} [Fintype I] [LinearOrder I] (U : I → Y.Opens)
  (hU : (⊤ : Y.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))

include hUaff haff in
/-- **The splitting of the Čech model gives a splitting of the derived direct image.** If after
inverting `a` the Čech model `D` of `𝒪_Y` splits as `H⁰(D)_a[0] ⊕ P` in `D(R_a)`, with `H⁰(D)_a`
finite free and `P` a bounded complex of finite projective modules in degrees `[1, b]`, then for
the base change `g' : Y' ⟶ Spec R_a` the derived direct image `Rg'_*𝒪_{Y'}` splits as `X₁ ⊕ P'`
with `X₁` of Tor amplitude in `[0, 0]` and `P'` perfect of Tor amplitude in `[1, b]`. -/
theorem exists_derivedPushforward_splitting_of_away (a : R)
    (P : CochainComplex (ModuleCat.{u} (Localization.Away a)) ℤ) (b : ℤ)
    [P.IsStrictlyGE 1] [P.IsStrictlyLE b]
    (hPfin : ∀ j, Module.Finite (Localization.Away a) (P.X j))
    (hPproj : ∀ j, Module.Projective (Localization.Away a) (P.X j)) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away a))
    let H0g := (ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away a))).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
        (DerivedCategory.Q.obj (baseAlternatingCechComplex g U hU (Scheme.unitModule Y))))
    Module.Free (Localization.Away a) H0g →
    Nonempty ((PseudoCoherence.localizationAwayFunctorAux.{u, u} a).obj
        (DerivedCategory.Q.obj (baseAlternatingCechComplex g U hU (Scheme.unitModule Y))) ≅
      (DerivedCategory.singleFunctor _ 0).obj H0g ⊞ DerivedCategory.Q.obj P) →
    ∀ {Y' : Scheme.{u}} {g' : Y' ⟶ Spec (.of (Localization.Away a))} {q : Y' ⟶ Y}
      (_ : IsPullback q g' g
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a))))),
      letI := HasDerivedCategory.standard Y'.Modules
      letI := HasDerivedCategory.standard (Spec (.of (Localization.Away a))).Modules
      ∃ X₁ P' : DerivedCategory (Spec (.of (Localization.Away a))).Modules,
        Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g'
          (Scheme.unitModule Y') ≅ X₁ ⊞ P') ∧
        HasTorAmplitudeStd (Spec (.of (Localization.Away a))) X₁ 0 0 ∧
        Stacks.Duality.CompactBoundedness.IsPerfectStd P' ∧
        HasTorAmplitudeStd (Spec (.of (Localization.Away a))) P' 1 b := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} (Localization.Away a))
  intro H0g hfree ⟨e⟩ Y' g' q hsq
  let := HasDerivedCategory.standard Y'.Modules
  let := HasDerivedCategory.standard (Spec (.of (Localization.Away a))).Modules
  let Ra := Localization.Away a
  let D := baseAlternatingCechComplex g U hU (Scheme.unitModule Y)
  let T := (tilde.functor (.of Ra)).mapDerivedCategory
  have : QuasiCompact g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : QuasiSeparated g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : IsSeparated g' := isSeparated_of_isPullback (algebraMap R Ra) hsq
  obtain ⟨e₁⟩ := nonempty_derivedPushforward_iso_tilde g' (Scheme.unitModule Y')
  let U' : I → Y'.Opens := fun i => q ⁻¹ᵁ U i
  have hU' : (⊤ : Y'.Opens) = ⨆ i, U' i := top_eq_iSup_preimage q U hU
  have haff' : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U' (s k)) :=
    iInf_preimage_isAffineOpen (algebraMap R Ra) hsq U hUaff
  let e₂ := alternatingCechIsoDerivedGlobalSectionsOverBase g' U' hU' (Scheme.unitModule Y') haff'
  let e₃ : extendScalarsCx (algebraMap R Ra) D ≅
      baseAlternatingCechComplex g' U' hU' (Scheme.unitModule Y') :=
    baseAlternatingCechComplexBaseChangeIso (algebraMap R Ra) hsq
        (Scheme.unitModule Y) U hU hUaff ≪≫
      baseAlternatingCechComplexMapIso g' U' hU' (Scheme.Modules.pullbackUnitIso q)
  obtain ⟨t₅⟩ := nonempty_Q_extendScalarsCx_iso_localizationAwayFunctorAux a D
  have : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBiproducts _
  let eE : ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g'
        (Scheme.unitModule Y') ≅
      T.obj ((DerivedCategory.singleFunctor _ 0).obj H0g) ⊞ T.obj (DerivedCategory.Q.obj P) :=
    e₁ ≪≫ T.mapIso (e₂.symm ≪≫ DerivedCategory.Q.mapIso e₃.symm ≪≫ t₅ ≪≫ e) ≪≫ T.mapBiprod _ _
  refine ⟨_, _, ⟨eE⟩, ?_, ?_, ?_⟩
  · refine (hasTorAmplitude_tilde_iff _ 0 0).2 ?_
    refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ 0 0).2
      ?_
    have := hfree
    exact hasFlatRepresentative_single_of_flat H0g
  · exact (isPerfect_tilde_iff _).2 ⟨P, 1, b, inferInstance, inferInstance, hPfin, hPproj,
      ⟨Iso.refl _⟩⟩
  · refine (hasTorAmplitude_tilde_iff _ 1 b).2 ?_
    refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ 1 b).2
      ⟨P, fun j => ?_, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
    have := hPproj j
    infer_instance

end Splitting

end StacksDraft.Perfect.GeomReducedFibre

end
