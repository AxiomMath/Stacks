module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Separation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.LocallySeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Separation conditions for a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U`, arrow space `R`,
source-target morphism `j = (t, s) : R ⟶ U ×_B U` and stabilizer group algebraic space
`S ⟶ U` with unit section `e : U ⟶ S`. For each of the three separation axioms of
**Stacks 03HL** the three conditions

* `j` has the axiom,
* the structure morphism `S ⟶ U` of the stabilizer has the axiom,
* `e` is a closed immersion, respectively an immersion, respectively quasi-compact

are equivalent. This file proves the three equivalences, each as a pair of two-term
equivalences.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSeparated_sourceTarget_iff_stabilizer` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSeparated_stabilizer_iff_unit_closedImmersion`:
  **Stacks 0455**, the separated case.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallySeparated_sourceTarget_iff_stabilizer`
  and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallySeparated_stabilizer_iff_unit_immersion`:
  **Stacks 0455**, the locally separated case.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isQuasiSeparated_sourceTarget_iff_stabilizer` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isQuasiSeparated_stabilizer_iff_unit_quasiCompact`:
  **Stacks 0455**, the quasi-separated case.

## Implementation notes

The three separation axioms are all of the shape "the relative diagonal lies in `W`" for a
property `W` of morphisms of presheaves which is stable under base change: the relative
property attached to closed immersions of schemes, to immersions of schemes, and
quasi-compactness of **Stacks 03HE**. The step from the unit section to the relative diagonal
of `j` therefore only uses base-change stability of `W`, and is proved once for an arbitrary
such `W` in `diagonal_sourceTarget_of_stabilizerUnit`; it is the diagram of **Stacks 0454**,
whose right hand square exhibits the middle vertical morphism as a base change of the unit
section and whose two horizontal morphisms are isomorphisms. The relative properties are
handled through `diagonal_sourceTarget_of_stabilizerUnit_relative`, which supplies their
base-change stability.

The two remaining steps are quoted rather than reproved. That the stabilizer is the base
change of `j` along the diagonal of `U` holds by construction, so the implication from `j` to
the stabilizer is base-change stability of the axiom, which is **Stacks 03KL**. That the
structure morphism of a group algebraic space has the axiom exactly when its identity section
has the corresponding absolute property is **Stacks 06P6**, applied to the stabilizer group
algebraic space of **Stacks 0447**.

## References

* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 0454](https://stacks.math.columbia.edu/tag/0454)
* [Stacks Project, Tag 0455](https://stacks.math.columbia.edu/tag/0455)
* [Stacks Project, Tag 06P6](https://stacks.math.columbia.edu/tag/06P6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- A property `W` of morphisms of presheaves which is stable under base change and holds for
the unit section of the stabilizer holds for the relative diagonal of the source-target
morphism.

This is the step from the unit section to the diagonal in **Stacks 0455**, shared by the three
separation axioms. In the diagram of **Stacks 0454** the middle vertical morphism
`arrowsOverObjectsUnit` is a base change of the unit section, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_stabilizerUnit`, and the relative
diagonal of `j` differs from it by the two horizontal isomorphisms of that diagram. -/
private theorem diagonal_sourceTarget_of_stabilizerUnit
    {W : MorphismProperty ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u)}
    (hW : W.IsStableUnderBaseChange) (G : GroupoidInAlgebraicSpaces C S hS B)
    (he : W (η[stabilizer G]).left) :
    W (pullback.diagonal (sourceTarget G).hom) := by
  have := isIso_arrowToArrowsOverObjects G
  have := isIso_arrowPairsToArrowsOverStabilizer G
  have hmid : W (arrowsOverObjectsUnit G) :=
    hW.of_isPullback (isPullback_stabilizerUnit G) he
  have hdiag : W (arrowToArrowsOverObjects G ≫ arrowsOverObjectsUnit G) :=
    MorphismProperty.RespectsIso.precomp W (arrowToArrowsOverObjects G)
      (arrowsOverObjectsUnit G) hmid
  rw [← diagonal_comp_arrowPairsToArrowsOverStabilizer] at hdiag
  exact (MorphismProperty.cancel_right_of_respectsIso W
    (pullback.diagonal (sourceTarget G).hom) (arrowPairsToArrowsOverStabilizer G)).mp hdiag

/-- The relative property attached to a property `P` of morphisms of schemes, if it holds for
the unit section of the stabilizer, holds for the relative diagonal of the source-target
morphism.

This is `diagonal_sourceTarget_of_stabilizerUnit` for the separation axioms of **Stacks 03HL**
that are relative properties, namely separatedness and local separatedness; a relative property
is stable under base change by
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`. -/
private theorem diagonal_sourceTarget_of_stabilizerUnit_relative (P : MorphismProperty Scheme.{u})
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (he : MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme C S hS))
      (η[stabilizer G]).left) :
    MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme C S hS))
      (pullback.diagonal (sourceTarget G).hom) :=
  diagonal_sourceTarget_of_stabilizerUnit
    (MorphismProperty.relative_isStableUnderBaseChange _) G he

/-! ### The separated case -/

/-- **Stacks 0455.** The structure morphism of the stabilizer of a groupoid in algebraic spaces
is separated exactly when the unit section of the stabilizer is a closed immersion. -/
@[stacks 0455 "separated_equivalences"]
theorem isSeparated_stabilizer_iff_unit_closedImmersion
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsSeparated C S hS (stabilizer G).hom ↔
      Space.IsClosedImmersion C S hS (η[stabilizer G]).left :=
  Space.isSeparated_iff_identity_isClosedImmersion C S hS G.objects.property
    (stabilizerGroup G)

/-- **Stacks 0455.** The source-target morphism of a groupoid in algebraic spaces is separated
exactly when the structure morphism of its stabilizer is separated. -/
@[stacks 0455 "separated_equivalences"]
theorem isSeparated_sourceTarget_iff_stabilizer (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsSeparated C S hS (sourceTarget G).hom ↔
      Space.IsSeparated C S hS (stabilizer G).hom := by
  refine ⟨fun h => Space.isSeparated_pullbackSnd C S hS (diagonal G).hom h, fun h => ?_⟩
  exact diagonal_sourceTarget_of_stabilizerUnit_relative _ G
    ((isSeparated_stabilizer_iff_unit_closedImmersion G).mp h)

/-! ### The locally separated case -/

/-- **Stacks 0455.** The structure morphism of the stabilizer of a groupoid in algebraic spaces
is locally separated exactly when the unit section of the stabilizer is an immersion. -/
@[stacks 0455 "locally_separated_equivalences"]
theorem isLocallySeparated_stabilizer_iff_unit_immersion
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsLocallySeparated C S hS (stabilizer G).hom ↔
      Space.IsImmersion C S hS (η[stabilizer G]).left :=
  Space.isLocallySeparated_iff_identity_isImmersion C S hS G.objects.property
    (stabilizerGroup G)

/-- **Stacks 0455.** The source-target morphism of a groupoid in algebraic spaces is locally
separated exactly when the structure morphism of its stabilizer is locally separated. -/
@[stacks 0455 "locally_separated_equivalences"]
theorem isLocallySeparated_sourceTarget_iff_stabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsLocallySeparated C S hS (sourceTarget G).hom ↔
      Space.IsLocallySeparated C S hS (stabilizer G).hom := by
  refine ⟨fun h => Space.isLocallySeparated_baseChange C S hS (sourceTarget G).hom
    (diagonal G).hom h, fun h => ?_⟩
  exact diagonal_sourceTarget_of_stabilizerUnit_relative _ G
    ((isLocallySeparated_stabilizer_iff_unit_immersion G).mp h)

/-! ### The quasi-separated case -/

/-- **Stacks 0455.** The structure morphism of the stabilizer of a groupoid in algebraic spaces
is quasi-separated exactly when the unit section of the stabilizer is quasi-compact. -/
@[stacks 0455 "quasi_separated_equivalences"]
theorem isQuasiSeparated_stabilizer_iff_unit_quasiCompact
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsQuasiSeparated C S hS (stabilizer G).hom ↔
      Space.IsQuasiCompact C S hS (η[stabilizer G]).left :=
  Space.isQuasiSeparated_iff_identity_isQuasiCompact C S hS G.objects.property
    (stabilizerGroup G)

/-- **Stacks 0455.** The source-target morphism of a groupoid in algebraic spaces is
quasi-separated exactly when the structure morphism of its stabilizer is quasi-separated. -/
@[stacks 0455 "quasi_separated_equivalences"]
theorem isQuasiSeparated_sourceTarget_iff_stabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsQuasiSeparated C S hS (sourceTarget G).hom ↔
      Space.IsQuasiSeparated C S hS (stabilizer G).hom := by
  refine ⟨fun h => Space.isQuasiSeparated_pullback C S hS (sourceTarget G).hom
    (diagonal G).hom h, fun h => ?_⟩
  exact diagonal_sourceTarget_of_stabilizerUnit
    (W := Space.quasiCompactPresheafProperty C S hS) inferInstance G
    ((isQuasiSeparated_stabilizer_iff_unit_quasiCompact G).mp h)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces
