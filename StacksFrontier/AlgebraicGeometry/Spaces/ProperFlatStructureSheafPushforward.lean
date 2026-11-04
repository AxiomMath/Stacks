module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageStructureSheafSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreOverFieldValuedPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGeometricFibresGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictedFibreGlobalFunctions

/-!
# `f_*𝒪_X = 𝒪_Y` for proper flat morphisms with good fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is proper, flat and of
finite presentation.

## Main results

* `AlgebraicGeometry.Space.isIso_structureSharp_of_bijective_algebraMap_fibre`: if
  `k = H⁰(X_k, 𝒪_{X_k})` for every morphism `Spec k ⟶ Y` from the spectrum of a field, then the
  structure map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism.
* `AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`:
  under the same hypothesis the structure map of `f` and of every base change of `f` is an
  isomorphism.
* `AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_geometricFibres`: if the
  geometric fibres of `f` are reduced and connected, the structure map of `f` and of every base
  change of `f` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces which is proper, flat and of finite
presentation, such that `k = H⁰(X_k, 𝒪_{X_k})` for every morphism `Spec k ⟶ Y` with `k` a field.
Then the structure map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism. -/
theorem isIso_structureSharp_of_bijective_algebraMap_fibre (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (h : ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f.hom p)))) :
    IsIso (structureSharp B S hS f) := by
  refine isIso_structureSharp_of_bijective_algebraMap B S hS f fun A _ hA g v _ => ?_
  have hF := isAlgebraicSpace_restrictedFibre B S hS f.hom X.2 Y.2 hA g v
  refine bijective_algebraMap_globalFunctions_of_residueField B hF _
    (isProper_restrictedFibre B S hS f.hom hA g v X.2 Y.2 hf).1
    (isFlat_restrictedFibre B S hS f.hom hA g v X.2 Y.2 hfl)
    (isFinitePresentation_restrictedFibre B S hS f.hom hA g v X.2 Y.2 hfp)
    fun P _ hP gP _ => ?_
  let p : FieldValuedPoint B S hS Y.1 :=
    { carrier := P.ResidueField
      contained := hP
      toBase := (gP ≫ g).hom
      value := Y.1.map (Over.homMk gP rfl).op v }
  exact (bijective_algebraMap_globalFunctions_congr B
    (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f.hom X.2 Y.2 p)
    (isAlgebraicSpace_relocalizeRestrict B _ _ hP hA gP _ hF)
    (nonempty_restrictedFibre_iso_relocalizeRestrict B S hS f.hom hA hP g gP v).some).mp (h p)

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces which is proper, flat and of finite
presentation, such that `k = H⁰(X_k, 𝒪_{X_k})` for every morphism `Spec k ⟶ Y` with `k` a field.
Then `f_*𝒪_X = 𝒪_Y` — the structure map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism — and this holds after
any base change `Y' ⟶ Y`. -/
@[stacks 0E6B "(a)"]
theorem isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (h : ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f.hom p)))) :
    IsIso (structureSharp B S hS f) ∧
      ∀ (Y' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y),
        IsIso (structureSharp B S hS (pullback.snd f g)) := by
  refine ⟨isIso_structureSharp_of_bijective_algebraMap_fibre B S hS f hf hfl hfp h,
    fun Y' g => ?_⟩
  refine isIso_structureSharp_of_bijective_algebraMap_fibre B S hS (pullback.snd f g)
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback f g) hf)
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback f g) hfl)
    ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback f g) hfp) fun p => ?_
  exact (bijective_algebraMap_globalFunctions_congr (A := p.carrier) (hA := p.contained) B
    (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS (pullback.snd f g).hom
      (pullback f g).2 Y'.2 p)
    (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f.hom X.2 Y.2
      (p.map B S hS Y'.1 g.hom))
    (fibreOverFieldValuedPointPullbackSndIso B S hS f g p)).mpr (h (p.map B S hS Y'.1 g.hom))

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces which is proper, flat and of finite
presentation, and whose geometric fibres are reduced and connected. Then `f_*𝒪_X = 𝒪_Y` — the
structure map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism — and this holds after any base change
`Y' ⟶ Y`. -/
@[stacks 0E0S]
theorem isIso_structureSharp_and_baseChange_of_geometricFibres (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hred : ∀ y : GeometricPoint B S hS Y.1,
      HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS f.hom y.1)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (hconn : ∀ y : GeometricPoint B S hS Y.1,
      ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS f.hom y.1)) :
    IsIso (structureSharp B S hS f) ∧
      ∀ (Y' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y),
        IsIso (structureSharp B S hS (pullback.snd f g)) :=
  isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B S hS f hf hfl hfp
    fun p => bijective_algebraMap_globalFunctions_fibre_of_geometricFibres B S hS f.hom X.2 Y.2
      hred hconn p _
      (isProper_restrictedFibre B S hS f.hom p.contained _ p.value X.2 Y.2 hf)

end AlgebraicGeometry.Space
