module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal homeomorphisms are local on the target

Being a universal homeomorphism is a Zariski-local property of the target: a morphism is a
universal homeomorphism exactly when its restriction over each member of an open cover of the
target is one.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_eq_universally_isHomeomorph` identifies the class
  `AlgebraicGeometry.UniversalHomeomorphism` with the morphism property
  `(topologically @IsHomeomorph).universally`.
* `AlgebraicGeometry.isZariskiLocalAtTarget_isIntegralHom`: being integral is Zariski-local at
  the target.
* `AlgebraicGeometry.instIsZariskiLocalAtTargetUniversalHomeomorphism`: being a universal
  homeomorphism is Zariski-local at the target.
* `AlgebraicGeometry.universalHomeomorphism_of_openCover` and
  `AlgebraicGeometry.universalHomeomorphism_iff_openCover` are the resulting open-cover
  criteria.

## References

* [Stacks Project, Tag 04DD](https://stacks.math.columbia.edu/tag/04DD)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The class of universal homeomorphisms is the morphism property
`(topologically @IsHomeomorph).universally`. -/
theorem universalHomeomorphism_eq_universally_isHomeomorph :
    (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) =
      (topologically @IsHomeomorph).universally := by
  ext X Y f
  exact universalHomeomorphism_iff f

/-- Being a universal homeomorphism respects isomorphisms. -/
instance :
    MorphismProperty.RespectsIso (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) := by
  rw [universalHomeomorphism_eq_universally_isHomeomorph]
  infer_instance

/-- Being a universal homeomorphism is stable under base change. -/
instance : MorphismProperty.IsStableUnderBaseChange
    (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) := by
  rw [universalHomeomorphism_eq_universally_isHomeomorph]
  infer_instance

/-- Being an integral morphism is Zariski-local at the target. -/
@[sga "4 IV 8.5.5" "special case"]
instance isZariskiLocalAtTarget_isIntegralHom :
    IsZariskiLocalAtTarget (@IsIntegralHom.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty

/-- Being a universal homeomorphism is Zariski-local at the target. -/
instance : IsZariskiLocalAtTarget (@UniversalHomeomorphism.{u}) := by
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U).flip hf
  · intro X Y f ι U hU hf
    have h : ∀ i, IsIntegralHom (f ∣_ U i) ∧ UniversallyInjective (f ∣_ U i) ∧
        Surjective (f ∣_ U i) := fun i ↦
      (universalHomeomorphism_iff_integral_universallyInjective_surjective
        (f ∣_ U i)).1 (hf i)
    exact (universalHomeomorphism_iff_integral_universallyInjective_surjective f).2
      ⟨IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsIntegralHom) U hU fun i ↦ (h i).1,
        IsZariskiLocalAtTarget.of_iSup_eq_top (P := @UniversallyInjective) U hU fun i ↦ (h i).2.1,
        IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Surjective) U hU fun i ↦ (h i).2.2⟩

/-- A morphism whose base change along every member of an open cover of the target is a
universal homeomorphism is a universal homeomorphism. -/
theorem universalHomeomorphism_of_openCover {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Y.OpenCover)
    (h : ∀ i, UniversalHomeomorphism (𝒰.pullbackHom f i)) : UniversalHomeomorphism f :=
  IsZariskiLocalAtTarget.of_openCover 𝒰 h

/-- A morphism is a universal homeomorphism exactly when its base change along every member of
an open cover of the target is one. -/
theorem universalHomeomorphism_iff_openCover {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Y.OpenCover) :
    UniversalHomeomorphism f ↔ ∀ i, UniversalHomeomorphism (𝒰.pullbackHom f i) :=
  IsZariskiLocalAtTarget.iff_of_openCover 𝒰

end AlgebraicGeometry

end
