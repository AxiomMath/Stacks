module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Pushout.Gluing

/-!
# Dominance of the integral map out of a pushout along a closed immersion

In the situation of [Stacks Project, Tag 0ECI] the structure sheaf of the pushout `Y ⨿_Z X` is
the fibre product of the structure sheaves of `Y` and `X` over that of `Z`. A fibre product of
rings over a monomorphism has a monomorphism as its other projection, so as soon as the
integral morphism `j : Z ⟶ Y` is scheme-theoretically dominant the canonical map `X ⟶ Y ⨿_Z X`
is injective on sections over every open, hence scheme-theoretically dominant itself.

Being integral it is also closed, and a closed dominant morphism is surjective. Consequently
the pushout is reduced as soon as `X` is.

## Main results

* `AlgebraicGeometry.pushoutInl_isSchemeTheoreticallyDominant`: the canonical map from `X` to
  the pushout is scheme-theoretically dominant.
* `AlgebraicGeometry.pushoutInl_surjective`: it is surjective.
* `AlgebraicGeometry.pushout_isReduced`: the pushout of a reduced scheme is reduced.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
  [IsSchemeTheoreticallyDominant s.j]

/-- The map from `X` to the pushout is injective on sections over every open: those sections
are a fibre product over the sections of `Z`, and the map from the sections of `Y` to those of
`Z` is injective. -/
theorem pushoutInl_app_injective (U : (pushoutScheme s).Opens) :
    Function.Injective ((pushoutInl s).app U) := by
  have : Mono (s.j.app (pushoutInr s ⁻¹ᵁ U)) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr (s.j.app_injective _)
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
    (pushoutStructureSheaf_isPullback s U).mono_snd_of_mono

/-- The map from `X` to the pushout is scheme-theoretically dominant. -/
instance pushoutInl_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (pushoutInl s) := by
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (pushoutInl_app_injective s U)

/-- The map from `X` to the pushout is surjective: it is dominant, and it is closed because it
is integral. -/
instance pushoutInl_surjective : Surjective (pushoutInl s) :=
  ⟨Set.range_eq_univ.mp <|
    (pushoutInl s).isClosedMap.isClosed_range.closure_eq ▸ (pushoutInl s).denseRange.closure_eq⟩

/-- The pushout of a reduced scheme along a closed immersion and a dominant integral morphism
is reduced. -/
instance pushout_isReduced [IsReduced s.X] : IsReduced (pushoutScheme s) :=
  IsSchemeTheoreticallyDominant.isReduced (pushoutInl s)

/-- The pushout of an irreducible scheme along a closed immersion and a dominant integral
morphism is irreducible. -/
instance pushout_irreducibleSpace [IrreducibleSpace s.X] :
    IrreducibleSpace (pushoutScheme s) :=
  (pushoutInl s).surjective.irreducibleSpace (pushoutInl s).continuous

/-- The pushout of a quasi-compact scheme along a closed immersion and a dominant integral
morphism is quasi-compact. -/
instance pushout_compactSpace [CompactSpace s.X] : CompactSpace (pushoutScheme s) :=
  (pushoutInl s).surjective.compactSpace (pushoutInl s).continuous

end AlgebraicGeometry

end
