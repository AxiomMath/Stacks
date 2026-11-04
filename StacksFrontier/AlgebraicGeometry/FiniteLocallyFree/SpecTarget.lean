module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Finite locally free morphisms over the spectrum of a ring

A morphism of schemes whose target is the spectrum of a ring is finite locally free exactly
when it is finite, flat and locally of finite presentation.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFree_iff_of_specTarget`: a morphism to `Spec R` is finite
  locally free if and only if it is finite, flat and locally of finite presentation.
* `Stacks.Morphisms.sheafOfModules_isFiniteLocallyFree_iff_module`: for an affine morphism to
  `Spec R`, the direct image of the structure sheaf is finite locally free if and only if the
  global sections of the source are a finite locally free `R`-module.

## Implementation notes

The base ring appears through `AlgebraicGeometry.Scheme.ΓSpecIso`, so the ring homomorphism
used throughout is the global-section map precomposed with that isomorphism rather than the
global-section map itself.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- For a morphism to the spectrum of a ring with affine source, the direct image of the
structure sheaf is finite locally free exactly when the global sections of the source form a
finite locally free module over that ring. -/
theorem sheafOfModules_isFiniteLocallyFree_iff_module {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsAffineHom f] :
    letI := ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom.toAlgebra
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (pushforwardStructureSheaf f) ↔
      Module.IsFiniteLocallyFree ↑R ↑Γ(X, ⊤) := by
  let : Algebra ↑R ↑Γ(X, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom.toAlgebra
  let M : (Spec R).Modules := pushforwardStructureSheaf f
  have hqc : M.IsQuasicoherent := by
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
    exact Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
      f _
  have hIso : IsIso M.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp hqc
  let : IsIso (Scheme.Modules.fromTildeΓ (R := R) M) := hIso
  let e : M ≅ AlgebraicGeometry.tilde (moduleSpecΓFunctor.obj M) :=
    (asIso (Scheme.Modules.fromTildeΓ (R := R) M)).symm
  constructor
  · intro hM
    have h₁ : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraicGeometry.tilde (moduleSpecΓFunctor.obj M)) :=
      SheafOfModules.IsFiniteLocallyFree.of_iso e
    have h₂ : Scheme.Modules.IsFiniteLocallyFree
        (AlgebraicGeometry.tilde (moduleSpecΓFunctor.obj M)) :=
      (Scheme.Modules.isFiniteLocallyFree_iff _).mpr h₁
    exact (tilde_isFiniteLocallyFree_iff ↑R ↑(moduleSpecΓFunctor.obj M)).mp h₂
  · intro hmod
    have h₂ : Scheme.Modules.IsFiniteLocallyFree
        (AlgebraicGeometry.tilde (moduleSpecΓFunctor.obj M)) :=
      (tilde_isFiniteLocallyFree_iff ↑R ↑(moduleSpecΓFunctor.obj M)).mpr hmod
    have h₁ : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraicGeometry.tilde (moduleSpecΓFunctor.obj M)) :=
      (Scheme.Modules.isFiniteLocallyFree_iff _).mp h₂
    exact SheafOfModules.IsFiniteLocallyFree.of_iso e.symm

/-- A morphism with affine source and target satisfies a property defined by a ring homomorphism
property exactly when the ring map `Γ(Spec R, ⊤) ⟶ Γ(X, ⊤)`, taken from `R`, satisfies it. -/
private theorem iff_comp_ΓSpecIso_inv {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    (hQ : RingHom.RespectsIso Q) {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [IsAffine X] : P f ↔ Q ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom := by
  rw [HasRingHomProperty.iff_of_isAffine (P := P), CommRingCat.hom_comp]
  exact (hQ.cancel_left_isIso (Scheme.ΓSpecIso R).inv f.appTop).symm

/-- The characterisation of finite local freeness over an affine base, for an affine source. -/
private theorem isFiniteLocallyFree_iff_aux {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsAffineHom f] [IsAffine X] :
    IsFiniteLocallyFree f ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  have h₁ : IsFiniteLocallyFree f ↔
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} (pushforwardStructureSheaf f) := by
    rw [isFiniteLocallyFree_iff]
    exact and_iff_right ‹IsAffineHom f›
  have hF : IsFinite f ↔ RingHom.Finite ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom := by
    have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) (arrowIsoSpecΓOfIsAffine f),
      IsFinite.SpecMap_iff, CommRingCat.hom_comp]
    exact (RingHom.finite_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso R).inv f.appTop).symm
  have hFl := iff_comp_ΓSpecIso_inv (P := @Flat) RingHom.Flat.respectsIso f
  have hP := iff_comp_ΓSpecIso_inv (P := @LocallyOfFinitePresentation)
    RingHom.finitePresentation_respectsIso f
  rw [h₁, sheafOfModules_isFiniteLocallyFree_iff_module f, hF, hFl, hP]
  algebraize [((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom]
  rw [Module.isFiniteLocallyFree_iff]
  constructor
  · rintro ⟨hfp, hflat⟩
    have hfin : Module.Finite ↑R ↑Γ(X, ⊤) := by infer_instance
    exact ⟨hfin, hflat,
      (Module.FinitePresentation.iff_finitePresentation_of_finite ↑R ↑Γ(X, ⊤)).mp hfp⟩
  · rintro ⟨hfin, hflat, halgfp⟩
    have : Module.Finite ↑R ↑Γ(X, ⊤) := hfin
    have : Algebra.FinitePresentation ↑R ↑Γ(X, ⊤) := halgfp
    exact ⟨Module.FinitePresentation.of_finite_of_finitePresentation ↑R ↑Γ(X, ⊤), hflat⟩

/-- A morphism of schemes to the spectrum of a ring is finite locally free if and only if it is
finite, flat and locally of finite presentation. -/
theorem isFiniteLocallyFree_iff_of_specTarget {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) :
    IsFiniteLocallyFree f ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : IsAffineHom f := h.toIsAffineHom
    have : IsAffine X := isAffine_of_isAffineHom f
    exact (isFiniteLocallyFree_iff_aux f).mp h
  · have : IsFinite f := h.1
    have : IsAffineHom f := inferInstance
    have : IsAffine X := isAffine_of_isAffineHom f
    exact (isFiniteLocallyFree_iff_aux f).mpr h

end Stacks.Morphisms

end
