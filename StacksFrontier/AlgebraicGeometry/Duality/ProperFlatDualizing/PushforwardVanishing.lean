module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.Endomorphisms
public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.DualTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# The direct image of the relative dualizing complex lives in nonpositive degrees

Let `Y` be quasi-compact and quasi-separated and `f : X ⟶ Y` proper, flat and of finite
presentation, with relative dualizing complex `ω = a(𝒪_Y)` ([Stacks, Remark 0B6S]). Then the
cohomology sheaves of `Rf_*ω` vanish in positive degrees: [Stacks, Tag 0E4L] (2).

By the first display of the proof of the tag at `E = 𝒪_X`
(`Stacks.Duality.StandardModel.pushforwardTensorDualIso`), `Rf_*ω` is the dual of the perfect
object `Rf_*𝒪_X`, which has Tor amplitude in `[0, b]` on every affine open of `Y` because `f` is
flat ([Stacks, Tag 0B91] and
`AlgebraicGeometry.exists_hasTorAmplitude_restrict_derivedPushforward_single`); the dual of such an
object has no cohomology in positive degrees
(`Stacks.Duality.StandardModel.isZero_homology_derivedDual_of_hasTorAmplitude`). This is the
source's argument, which computes `Hom(𝒪_Y[-i], Rf_*ω) = Hom(Rf_*𝒪_X[-i], 𝒪_Y) = 0` on an affine
base, read through the duality of perfect objects.

## Main results

* `Stacks.Duality.StandardModel.isZero_homology_derivedPushforward_relativeDualizingComplex` —
  **[Stacks, Tag 0E4L] (2)**.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality.StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- **[Stacks, Tag 0E4L] (2).** Let `Y` be a quasi-compact and quasi-separated scheme and
`f : X ⟶ Y` a proper, flat morphism of finite presentation, with relative dualizing complex
`ω_{X/Y} = a(𝒪_Y)` ([Stacks, Remark 0B6S]). Then `Rf_*ω_{X/Y}` has vanishing cohomology sheaves
in positive degrees. -/
@[stacks 0E4L "(2)"]
theorem isZero_homology_derivedPushforward_relativeDualizingComplex (i : ℤ) (hi : 0 < i) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj (relativeDualizingComplex f).obj)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let := monoidal X
  have h1 : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (𝟙_ (DerivedCategory X.Modules)) := by
    have hp := Stacks.SheafOfModules.isPerfect_derivedStructureSheaf_space.{u} X.toRingedSpace
    rw [show 𝟙_ (DerivedCategory X.Modules) = RingedSite.derivedStructureSheaf
      (Stacks.SheafOfModules.ringedSite X.sheaf) from
        Stacks.SheafOfModules.tensorUnit_derivedMonoidalStructure X.sheaf]
    exact hp
  have hP := isPerfect_derivedPushforward_dual f _ h1
  let P := (derivedPushforward f).obj (dual (𝟙_ (DerivedCategory X.Modules)))
  let : ExactPairing (𝟙_ (DerivedCategory X.Modules)) (dual (𝟙_ (DerivedCategory X.Modules))) :=
    exactPairingDual _ h1
  let eD : dual (𝟙_ (DerivedCategory X.Modules)) ≅ 𝟙_ (DerivedCategory X.Modules) :=
    rightDualIso (exactPairingDual _ h1) exactPairingUnit
  let eP : (schemeDerivedPushforward f).obj
      (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex
        (SheafOfModules.unit X.ringCatSheaf))) ≅ P :=
    (schemeDerivedPushforward f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm ≪≫
      (derivedPushforward f).mapIso eD.symm
  let P₀ := (schemeDerivedPushforward f).obj
      (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex
        (SheafOfModules.unit X.ringCatSheaf)))
  have hP₀ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) P₀ :=
    isPerfect_of_iso_scheme eP.symm hP
  have htor : ∀ V : Y.affineOpens, ∃ b : ℤ,
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude
        (Y.toRingedSpace.restrict (V : Y.Opens).isOpenEmbedding)
        ((Scheme.Modules.restrictFunctor (V : Y.Opens).ι).mapDerivedCategory.obj P₀) 0 b :=
    fun V =>
      open Stacks.AlgebraicGeometry.VanishingHigherDirectImages in
      exists_hasTorAmplitude_restrict_derivedPushforward_single
        f ⟨inferInstance, inferInstance, inferInstance⟩ (SheafOfModules.unit X.ringCatSheaf)
        inferInstance (isFlatOver_unit_of_flat f) V
  have hD := isZero_homology_derivedDual_of_hasTorAmplitude P₀ hP₀ 0 htor i (by omega)
  let := monoidal Y
  let : ExactPairing P (dual P) := exactPairingDual P hP
  let : ExactPairing P₀ (dual P₀) := exactPairingDual P₀ hP₀
  let eDual : dual P ≅ dual P₀ :=
    rightDualIso (exactPairingDual P hP) (exactPairingCongrLeft eP.symm)
  exact hD.of_iso ((DerivedCategory.homologyFunctor Y.Modules i).mapIso
    ((derivedPushforward f).mapIso (λ_ (relativeDualizingComplex f).obj).symm ≪≫
      pushforwardTensorDualIso f _ h1 hP ≪≫ eDual))

end Stacks.Duality.StandardModel

end
