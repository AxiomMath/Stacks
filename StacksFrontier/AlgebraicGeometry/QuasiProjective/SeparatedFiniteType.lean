module

public import StacksFrontier.AlgebraicGeometry.Blowup.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-projective morphisms are separated of finite type

A quasi-projective, H-quasi-projective or locally quasi-projective morphism of schemes is separated
and of finite type. Finite type is spelled as the conjunction of
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.

## Main results

* `AlgebraicGeometry.IsHQuasiProjective.locallyOfFiniteType`,
  `AlgebraicGeometry.IsHQuasiProjective.quasiCompact`,
  `AlgebraicGeometry.IsHQuasiProjective.isSeparated`: an H-quasi-projective morphism is locally of
  finite type, quasi-compact and separated.
* `AlgebraicGeometry.IsQuasiProjective.isSeparated`: a quasi-projective morphism is separated.
* `AlgebraicGeometry.IsLocallyQuasiProjective.locallyOfFiniteType`,
  `AlgebraicGeometry.IsLocallyQuasiProjective.quasiCompact` and
  `AlgebraicGeometry.IsLocallyQuasiProjective.isSeparated`: a locally quasi-projective morphism is
  locally of finite type, quasi-compact and separated.

That a quasi-projective morphism is of finite type is part of the definition of
`AlgebraicGeometry.IsQuasiProjective`, and is given by
`AlgebraicGeometry.IsQuasiProjective.locallyOfFiniteType` and
`AlgebraicGeometry.IsQuasiProjective.quasiCompact`.

## References

* [Stacks Project, Tag 01VX](https://stacks.math.columbia.edu/tag/01VX)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01T1](https://stacks.math.columbia.edu/tag/01T1)
* [Stacks Project, Tag 01VI](https://stacks.math.columbia.edu/tag/01VI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Being locally of finite type is Zariski-local at the target. -/
private theorem zariskiLocalAtTarget_locallyOfFiniteType :
    IsZariskiLocalAtTarget @LocallyOfFiniteType :=
  HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType

/-- Quasi-compactness is Zariski-local at the target. -/
private theorem zariskiLocalAtTarget_quasiCompact :
    IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat

namespace IsHQuasiProjective

/-- An H-quasi-projective morphism is a quasi-compact immersion followed by a proper morphism. -/
private theorem exists_immersion_comp_isProper (hf : IsHQuasiProjective f) :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (p : Y ⟶ S),
      IsImmersion i ∧ QuasiCompact i ∧ IsProper p ∧ f = i ≫ p := by
  obtain ⟨n, i, hi, hqc, hif⟩ := hf
  exact ⟨_, i, _, hi, hqc, isProper_projectiveSpaceOver n S, hif.symm⟩

/-- An H-quasi-projective morphism of schemes is locally of finite type. -/
@[stacks 01VX "finite_type"]
theorem locallyOfFiniteType (hf : IsHQuasiProjective f) : LocallyOfFiniteType f := by
  obtain ⟨Y, i, p, hi, hqc, hp, rfl⟩ := exists_immersion_comp_isProper hf
  infer_instance

/-- An H-quasi-projective morphism of schemes is quasi-compact. -/
@[stacks 01VX "finite_type"]
theorem quasiCompact (hf : IsHQuasiProjective f) : QuasiCompact f := by
  obtain ⟨Y, i, p, hi, hqc, hp, rfl⟩ := exists_immersion_comp_isProper hf
  infer_instance

/-- An H-quasi-projective morphism of schemes is separated. -/
@[stacks 01VX "separated"]
theorem isSeparated (hf : IsHQuasiProjective f) : IsSeparated f := by
  obtain ⟨Y, i, p, hi, hqc, hp, rfl⟩ := exists_immersion_comp_isProper hf
  infer_instance

end IsHQuasiProjective

namespace IsQuasiProjective

/-- A quasi-projective morphism of schemes is separated. -/
@[stacks 01VX "separated", ega "II 4.6.3" "special case"]
theorem isSeparated (hf : IsQuasiProjective f) : IsSeparated f := by
  obtain ⟨-, L, hL, hL'⟩ := hf
  exact Scheme.Modules.IsRelativelyAmple.isSeparated hL'

end IsQuasiProjective

namespace IsLocallyQuasiProjective

/-- A locally quasi-projective morphism of schemes is locally of finite type. -/
@[stacks 01VX "finite_type"]
theorem locallyOfFiniteType (hf : IsLocallyQuasiProjective f) : LocallyOfFiniteType f := by
  obtain ⟨𝒰, h⟩ := hf
  have := zariskiLocalAtTarget_locallyOfFiniteType
  exact (IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) 𝒰).mpr
    fun i => (h i).locallyOfFiniteType

/-- A locally quasi-projective morphism of schemes is quasi-compact. -/
@[stacks 01VX "finite_type"]
theorem quasiCompact (hf : IsLocallyQuasiProjective f) : QuasiCompact f := by
  obtain ⟨𝒰, h⟩ := hf
  have := zariskiLocalAtTarget_quasiCompact
  exact (IsZariskiLocalAtTarget.iff_of_openCover (P := @QuasiCompact) 𝒰).mpr
    fun i => (h i).quasiCompact

/-- A locally quasi-projective morphism of schemes is separated. -/
@[stacks 01VX "separated"]
theorem isSeparated (hf : IsLocallyQuasiProjective f) : IsSeparated f := by
  obtain ⟨𝒰, h⟩ := hf
  exact (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsSeparated) 𝒰).mpr
    fun i => (h i).isSeparated

end IsLocallyQuasiProjective

end AlgebraicGeometry

end
