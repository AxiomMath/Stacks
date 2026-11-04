module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.BaseChangeSplitting
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentCompactDualizable
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDegreeZeroDirectImage

/-!
# Identifying the first summand, and the passage to an arbitrary model

Two steps finish the proof of [Stacks, Tag 0G7Y] once `Rf_*𝒪_X ≅ X₁ ⊕ P` is known at the standard
model with `X₁` of Tor amplitude in `[0, 0]` and `P` of Tor amplitude in `[1, b]`:

* the first summand is `H⁰(Rf_*𝒪_X)[0] = f_*𝒪_X[0]`, because `X₁` has cohomology only in degree
  `0` and `P` none in degrees `≤ 0` (`nonempty_iso_singleFunctor_homology_biprod`);
* the decomposition, perfectness and Tor amplitude are carried from the standard model to any
  model of the derived categories along the comparison equivalence
  `StacksDraft.DerivedModel.modelEquiv` (`exists_splitting_any_model`).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StacksDraft.DerivedModel

universe w w' v u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- **An object split as a summand concentrated in degree `0` plus a summand concentrated in
degrees `≥ 1` is `H⁰[0]` plus that summand.** -/
theorem nonempty_iso_singleFunctor_homology_biprod {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {E A B : DerivedCategory C} (e : E ≅ A ⊞ B)
    (hA : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C i).obj A))
    (hB : ∀ i : ℤ, i ≤ 0 → IsZero ((DerivedCategory.homologyFunctor C i).obj B)) :
    Nonempty (E ≅ (DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C 0).obj E) ⊞ B) := by
  have : A.IsGE 0 := (DerivedCategory.isGE_iff A 0).2 fun i hi => hA i (by omega)
  have : A.IsLE 0 := (DerivedCategory.isLE_iff A 0).2 fun i hi => hA i (by omega)
  obtain ⟨Y, ⟨eY⟩⟩ := A.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  let H := DerivedCategory.homologyFunctor C 0
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts _
  let h₀ : H.obj E ≅ Y := H.mapIso e ≪≫ H.mapBiprod A B ≪≫ (isoBiprodZero (hB 0 le_rfl)).symm ≪≫
    H.mapIso eY ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y
  exact ⟨e ≪≫ biprod.mapIso (eY ≪≫ (DerivedCategory.singleFunctor C 0).mapIso h₀.symm)
    (Iso.refl B)⟩

/-- An object of Tor amplitude in `[a, b]` has no cohomology outside `[a, b]`, at any model. -/
theorem isZero_homology_of_hasTorAmplitude (X : RingedSpace.{u, u})
    (hd : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X))
    (E : @DerivedCategory _ _ _ hd) (a b : ℤ) (hab : a ≤ b)
    (hE : @Stacks.Cohomology.TorAmplitude.HasTorAmplitude X hd E a b) (i : ℤ)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ hd i).obj E) := by
  let := hd
  let : HasDerivedCategory.{w} (RingedSpace.KFlatDerivedPullback.Modules X) := hd
  obtain ⟨K, -, hK, ⟨eK⟩⟩ :=
    Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.exists_flat_representative_of_hasTorAmplitude
      E a b hab hE
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso eK.symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app K)
  exact ShortComplex.isZero_homology_of_isZero_X₂ (K.sc i) (hK i hi)

/-- Tor amplitude in `[a, b]` gives Tor amplitude in any larger interval. -/
theorem hasTorAmplitude_mono (X : RingedSpace.{u, u})
    (hd : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X))
    (E : @DerivedCategory _ _ _ hd) {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (hE : @Stacks.Cohomology.TorAmplitude.HasTorAmplitude X hd E a b) :
    @Stacks.Cohomology.TorAmplitude.HasTorAmplitude X hd E a' b' := fun F i hi =>
  hE F i fun h => hi ⟨ha.trans h.1, h.2.trans hb⟩

/-- **At the standard model, the first summand is `f_*𝒪_X[0]`.** -/
theorem exists_splitting_pushforward_std {Z T : Scheme.{u}} (φ : Z ⟶ T) (b : ℤ) :
    letI := HasDerivedCategory.standard Z.Modules
    letI := HasDerivedCategory.standard T.Modules
    (∃ X₁ P : DerivedCategory T.Modules,
      Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule φ
        (Scheme.unitModule Z) ≅ X₁ ⊞ P) ∧
      HasTorAmplitudeStd T X₁ 0 0 ∧ Stacks.Duality.CompactBoundedness.IsPerfectStd P ∧
      HasTorAmplitudeStd T P 1 b) →
    ∃ P : DerivedCategory T.Modules,
      Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule φ
        (Scheme.unitModule Z) ≅ (DerivedCategory.singleFunctor T.Modules 0).obj
          ((Scheme.Modules.pushforward φ).obj (Scheme.unitModule Z)) ⊞ P) ∧
      Stacks.Duality.CompactBoundedness.IsPerfectStd P ∧ HasTorAmplitudeStd T P 1 (max b 1) := by
  let := HasDerivedCategory.standard Z.Modules
  let := HasDerivedCategory.standard T.Modules
  rintro ⟨X₁, P, ⟨e⟩, h₁, hP, hPb⟩
  have hPb' : HasTorAmplitudeStd T P 1 (max b 1) :=
    hasTorAmplitude_mono _ _ P le_rfl (le_max_left b 1) hPb
  obtain ⟨e'⟩ := nonempty_iso_singleFunctor_homology_biprod e
    (fun i hi => isZero_homology_of_hasTorAmplitude _ _ X₁ 0 0 le_rfl h₁ i
      (fun h => hi (le_antisymm h.2 h.1)))
    (fun i hi => isZero_homology_of_hasTorAmplitude _ _ P 1 (max b 1) (le_max_right b 1) hPb' i
      (fun h => absurd h.1 (by omega)))
  have := Stacks.SchemeCohomology.pushforward_preservesFiniteLimits φ
  let h₀ : (Scheme.Modules.pushforward φ).obj (Scheme.unitModule Z) ≅
      (DerivedCategory.homologyFunctor T.Modules 0).obj
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule φ (Scheme.unitModule Z)) :=
    ((Scheme.Modules.pushforward φ).rightDerivedZeroIsoSelf.app _).symm ≪≫
      ProperFlatFibreEulerCharacteristic.hdiIsoHomologyDerivedPushforwardModule φ _ 0
  exact ⟨P, ⟨e' ≪≫ biprod.mapIso ((DerivedCategory.singleFunctor T.Modules 0).mapIso h₀.symm)
    (Iso.refl P)⟩, hP, hPb'⟩

/-- The comparison equivalence carries a module placed in degree `0` to the module placed in
degree `0`. -/
def modelEquivSingleIso {C : Type u} [Category.{v} C] [Abelian C] (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{w'} C) (N : C) :
    (modelEquiv h₁ h₂).functor.obj ((@DerivedCategory.singleFunctor C _ _ h₁ 0).obj N) ≅
      (@DerivedCategory.singleFunctor C _ _ h₂ 0).obj N :=
  (modelEquiv h₁ h₂).functor.mapIso ((@DerivedCategory.singleFunctorIsoCompQ C _ _ h₁ 0).app N) ≪≫
    (modelCompQIso h₁ h₂).app _ ≪≫ ((@DerivedCategory.singleFunctorIsoCompQ C _ _ h₂ 0).app N).symm

/-- **The splitting at an arbitrary model.** A splitting `Rφ_*𝒪 ≅ M[0] ⊕ P₀` at the standard model,
with `P₀` perfect of Tor amplitude in `[1, b]`, gives at every model of the derived categories a
splitting `M[0] ⊕ P ≅ Rφ_*𝒪` with `P` perfect of Tor amplitude in `[1, b]`. -/
theorem exists_splitting_any_model {Z T : Scheme.{u}} (φ : Z ⟶ T) (M : T.Modules) (b : ℤ)
    (hb : 1 ≤ b)
    (hstd : letI := HasDerivedCategory.standard Z.Modules
      letI := HasDerivedCategory.standard T.Modules
      ∃ P₀ : DerivedCategory T.Modules,
        Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule φ
            (Scheme.unitModule Z) ≅ (DerivedCategory.singleFunctor T.Modules 0).obj M ⊞ P₀) ∧
        Stacks.Duality.CompactBoundedness.IsPerfectStd P₀ ∧ HasTorAmplitudeStd T P₀ 1 b)
    (hZ : HasDerivedCategory.{w} Z.Modules) (hT : HasDerivedCategory.{w} T.Modules) :
    letI := hZ
    letI := hT
    letI : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace)) := hZ
    letI : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace)) := hT
    ∃ P : DerivedCategory T.Modules,
      @Stacks.Cohomology.PerfectComplexes.IsPerfect T.toRingedSpace hT P ∧
      @Stacks.Cohomology.TorAmplitude.HasTorAmplitude T.toRingedSpace hT P 1 b ∧
      Nonempty ((DerivedCategory.singleFunctor T.Modules 0).obj M ⊞ P ≅
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          φ.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor Z.Modules 0).obj (Scheme.unitModule Z))) := by
  obtain ⟨P₀, ⟨e⟩, hP, hPb⟩ := hstd
  let := hZ
  let := hT
  let : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace)) := hZ
  let : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace)) := hT
  let eT := (modelEquiv (HasDerivedCategory.standard T.Modules) hT).functor
  have : eT.Additive := modelEquiv_functor_additive (HasDerivedCategory.standard T.Modules) hT
  have : PreservesBinaryBiproducts eT := preservesBinaryBiproducts_of_preservesBiproducts _
  have ePush : eT.obj (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule φ
      (Scheme.unitModule Z)) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward φ.toLRSHom.toShHom).obj
        ((modelEquiv (HasDerivedCategory.standard Z.Modules) hZ).functor.obj
          ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard Z.Modules) 0).obj
            (Scheme.unitModule Z))) :=
    (derivedPushforwardModelEquivIso φ.toLRSHom.toShHom
      (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace)))
      (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace)))
      (inferInstance : HasDerivedCategory.{w}
        (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace)))
      (inferInstance : HasDerivedCategory.{w}
        (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace)))).app _
  refine ⟨eT.obj P₀, ?_, ?_, ⟨?_⟩⟩
  · exact (Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff T.toRingedSpace
      (HasDerivedCategory.standard T.Modules) hT P₀).2 hP
  · obtain ⟨K, hKflat, hK, ⟨eK⟩⟩ :=
      @Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.exists_flat_representative_of_hasTorAmplitude
        T.toRingedSpace (HasDerivedCategory.standard T.Modules) P₀ 1 b hb hPb
    refine (@Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative
      T.toRingedSpace hT (eT.obj P₀) 1 b hb).2 ⟨K, hKflat, hK, ⟨?_⟩⟩
    exact ((modelCompQIso (HasDerivedCategory.standard T.Modules) hT).app K).symm ≪≫ eT.mapIso eK
  · exact biprod.mapIso (modelEquivSingleIso (HasDerivedCategory.standard T.Modules) hT M).symm
        (Iso.refl _) ≪≫ (eT.mapBiprod _ _).symm ≪≫ eT.mapIso e.symm ≪≫ ePush ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        φ.toLRSHom.toShHom).mapIso
          (modelEquivSingleIso (HasDerivedCategory.standard Z.Modules) hZ (Scheme.unitModule Z))

end StacksDraft.Perfect.GeomReducedFibre

end
