module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite local freeness on the spectrum of a ring, and its one-sided consequences

On the spectrum of a ring, finite local freeness of a morphism of schemes is finite local
freeness of the module of global sections of the source over that of the target, and so is
finiteness together with flatness and local finite presentation.

For an arbitrary morphism, finite local freeness is
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`; this
module derives finiteness, flatness, local finite presentation and universal openness from it.

## Main results

* `Stacks.Morphisms.specMap_finiteLocallyFree_iff_module` and
  `Stacks.Morphisms.specMap_finiteLocallyFree_iff`: for a morphism of spectra, finite local
  freeness is finite local freeness of the module, and is finiteness, flatness and local finite
  presentation.
* `Stacks.Morphisms.IsFiniteLocallyFree.isFinite`,
  `Stacks.Morphisms.IsFiniteLocallyFree.flat` and
  `Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation`: a finite locally free
  morphism is finite, flat and locally of finite presentation.
* `Stacks.Morphisms.IsFiniteLocallyFree.universallyOpen` and
  `Stacks.Morphisms.IsFiniteLocallyFree.isOpenMap`: a finite locally free morphism is
  universally open, and in particular open on underlying spaces.

## Implementation notes

On spectra the statement reduces to `Module.isFiniteLocallyFree_iff` (a module is finite
locally free exactly when it is finitely presented and flat) through
`Stacks.Morphisms.specMapPushforwardIso`, which identifies the direct image of the structure
sheaf along `Spec φ` with the sheaf associated to `S` viewed as an `R`-module, and
`tilde_isFiniteLocallyFree_iff`.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u

namespace Stacks.Morphisms

/-- The direct image of the structure sheaf along `Spec φ` is the sheaf associated to `S`,
viewed as an `R`-module by restriction of scalars along `φ`. -/
def specMapPushforwardIso (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    pushforwardStructureSheaf (Spec.map φ) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) :=
  (Scheme.Modules.pushforward (Spec.map φ)).mapIso (tildeSelf (R := S)).symm ≪≫
    (pushforwardTildeIso R S φ).app (ModuleCat.of S S)

/-- On spectra, finite local freeness of the morphism is finite local freeness of the module of
global sections of the source over that of the target. -/
theorem specMap_finiteLocallyFree_iff_module (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    IsFiniteLocallyFree (Spec.map φ) ↔
      Module.IsFiniteLocallyFree R
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) := by
  rw [isFiniteLocallyFree_iff_pointwise]
  simp only [and_iff_right (show IsAffineHom (Spec.map φ) by infer_instance)]
  rw [← tilde_isFiniteLocallyFree_iff]
  exact ⟨fun h ↦ Stacks.Modules.isFiniteLocallyFree_of_iso (specMapPushforwardIso R S φ) h,
    fun h ↦ Stacks.Modules.isFiniteLocallyFree_of_iso (specMapPushforwardIso R S φ).symm h⟩

/-- On spectra, finite local freeness is finiteness, flatness and local finite presentation. -/
theorem specMap_finiteLocallyFree_iff (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    IsFiniteLocallyFree (Spec.map φ) ↔
      IsFinite (Spec.map φ) ∧ Flat (Spec.map φ) ∧
        LocallyOfFinitePresentation (Spec.map φ) := by
  rw [specMap_finiteLocallyFree_iff_module, IsFinite.SpecMap_iff,
    AlgebraicGeometry.Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff]
  algebraize [φ.hom]
  change Module.IsFiniteLocallyFree R S ↔
    Module.Finite R S ∧ Module.Flat R S ∧ Algebra.FinitePresentation R S
  rw [Module.isFiniteLocallyFree_iff]
  constructor
  · rintro ⟨hfp, hflat⟩
    exact ⟨inferInstance, hflat,
      (Module.FinitePresentation.iff_finitePresentation_of_finite R S).mp hfp⟩
  · rintro ⟨_, hflat, _⟩
    exact ⟨Module.FinitePresentation.of_finite_of_finitePresentation R S, hflat⟩

/-- `AlgebraicGeometry.IsFinite` is the affine-local property `affineAnd RingHom.Finite`. -/
private theorem isFiniteHasAffineProperty :
    HasAffineProperty (@IsFinite : MorphismProperty Scheme.{u}) (affineAnd RingHom.Finite) :=
  (HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
      RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan).mpr
    fun _ ↦ by simp [isFinite_iff]

/-- A morphism of affine schemes is finite locally free if and only if it is finite, flat and
locally of finite presentation. -/
private theorem affine_finiteLocallyFree_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] :
    IsFiniteLocallyFree f ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  have h1 : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h2 : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Flat)).toRespects
  have h3 : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.instIsZariskiLocalAtTarget _
      (Q := RingHom.FinitePresentation)).toRespects
  rw [MorphismProperty.arrow_mk_iso_iff
      (P := @IsFiniteLocallyFree) (arrowIsoSpecΓOfIsAffine f),
    MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) (arrowIsoSpecΓOfIsAffine f),
    MorphismProperty.arrow_mk_iso_iff (P := @Flat) (arrowIsoSpecΓOfIsAffine f),
    MorphismProperty.arrow_mk_iso_iff (P := @LocallyOfFinitePresentation)
      (arrowIsoSpecΓOfIsAffine f),
    specMap_finiteLocallyFree_iff]

/-- A morphism with affine target is finite locally free if and only if it is finite, flat and
locally of finite presentation. -/
private theorem affineTarget_finiteLocallyFree_iff {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] :
    IsFiniteLocallyFree f ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  constructor
  · intro h
    have : IsAffineHom f := h.toIsAffineHom
    have : IsAffine X := isAffine_of_isAffineHom f
    exact (affine_finiteLocallyFree_iff f).mp h
  · rintro ⟨hfin, hflat, hlfp⟩
    have : IsAffine X := isAffine_of_isAffineHom f
    exact (affine_finiteLocallyFree_iff f).mpr ⟨hfin, hflat, hlfp⟩

/-- A finite locally free morphism is finite. -/
theorem IsFiniteLocallyFree.isFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFiniteLocallyFree f] : IsFinite f :=
  ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp ‹_›).1

/-- A finite locally free morphism is flat. -/
theorem IsFiniteLocallyFree.flat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFiniteLocallyFree f] : Flat f :=
  ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp ‹_›).2.1

/-- A finite locally free morphism is locally of finite presentation. -/
theorem IsFiniteLocallyFree.locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFiniteLocallyFree f] : LocallyOfFinitePresentation f :=
  ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp ‹_›).2.2

/-- A finite locally free morphism is universally open. -/
@[sga "3 V 4.1.1" "more general"]
theorem IsFiniteLocallyFree.universallyOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFiniteLocallyFree f] : UniversallyOpen f := by
  have := IsFiniteLocallyFree.flat f
  have := IsFiniteLocallyFree.locallyOfFinitePresentation f
  infer_instance

/-- A finite locally free morphism is an open map on underlying topological spaces. -/
theorem IsFiniteLocallyFree.isOpenMap {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFiniteLocallyFree f] : IsOpenMap f.base := by
  have := IsFiniteLocallyFree.universallyOpen f
  exact f.isOpenMap

end Stacks.Morphisms

end
