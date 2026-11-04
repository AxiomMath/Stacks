module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Permanence of quasi-separatedness and separatedness for schemes

Let `P` be one of the four properties of morphisms of schemes

* quasi-separated,
* separated,
* quasi-compact and quasi-separated,
* quasi-compact and separated,

and say that a scheme `X` *has* `P` when the morphism `X ⟶ ⊤_ Scheme` to the terminal scheme
has `P`. Then an affine scheme has `P`; for `f : X ⟶ Y` with `Y` having `P`, the morphism `f`
has `P` exactly when `X` does; and a fibre product of schemes having `P` over a base having `P`
again has `P`.

## Main results

The three clauses are proved once and for all, for an abstract morphism property, in
`CategoryTheory.MorphismProperty.terminal_from_iff` and
`CategoryTheory.MorphismProperty.terminal_from_pullback`: all that is used of `P` is that it is
stable under composition, stable under base change, and cancels on the left of a composition.

The four properties above are then instantiated one at a time, in the classes that
`Mathlib.AlgebraicGeometry` uses for them: `QuasiSeparatedSpace X` and `CompactSpace X` on the
carrier for quasi-separatedness and quasi-compactness, and `AlgebraicGeometry.Scheme.IsSeparated`
for separatedness.

* clause (1): `AlgebraicGeometry.quasiSeparatedSpace_of_isAffine` and
  `AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine` from Mathlib, together with
  `AlgebraicGeometry.compactSpace_and_quasiSeparatedSpace_of_isAffine` and
  `AlgebraicGeometry.compactSpace_and_isSeparated_of_isAffine`.
* clause (2): `AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace` from Mathlib, together
  with `AlgebraicGeometry.isSeparated_iff_scheme_isSeparated`,
  `AlgebraicGeometry.quasiCompact_and_quasiSeparated_iff` and
  `AlgebraicGeometry.quasiCompact_and_isSeparated_iff`.
* clause (3): `AlgebraicGeometry.quasiSeparatedSpace_pullback`,
  `AlgebraicGeometry.isSeparated_pullback`,
  `AlgebraicGeometry.compactSpace_and_quasiSeparatedSpace_pullback` and
  `AlgebraicGeometry.compactSpace_and_isSeparated_pullback`.

## Implementation notes

Bare quasi-compactness is deliberately absent from the list: clause (2) fails for it, since
`AlgebraicGeometry.quasiCompact_iff_compactSpace` needs the target to be quasi-separated as well
as quasi-compact. This is why the two conjunctive properties, and not quasi-compactness alone,
appear among the four.

For the two conjunctive properties the generic lemmas are run on the lattice meet
`@QuasiCompact ⊓ @QuasiSeparated` (resp. `@QuasiCompact ⊓ @IsSeparated`), whose closure
properties are assembled below from those of the two factors.

## References

* [Stacks Project, Tag 0816](https://stacks.math.columbia.edu/tag/0816)
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

add_to_stacks 0816 "(1), quasi-separated" AlgebraicGeometry.quasiSeparatedSpace_of_isAffine
add_to_ega "IV 1.9.6" "special case" AlgebraicGeometry.quasiSeparatedSpace_of_isAffine
add_to_stacks 0816 "(1), separated" AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine
add_to_ega "I 5.5.7" AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine
add_to_ega "II 1.2.4" "special case" AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine
add_to_stacks 0816 "(2), quasi-separated"
  AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace
add_to_sga "4 VI 1.14" "(ii), special case" AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace
add_to_sga "4 VI 1.8" "(iii), special case" AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace
add_to_sga "4 VI 1.9.1" "(iii), special case"
  AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace
add_to_ega "IV 1.2.3" AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace
add_to_ega "IV 1.2.6" "special case" AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] [HasTerminal C]

/-- If `f : X ⟶ Y` lies in `P` and `Y ⟶ ⊤_ C` lies in `P`, then so does `X ⟶ ⊤_ C`. -/
theorem terminal_from_of_comp (P : MorphismProperty C) [P.IsStableUnderComposition]
    {X Y : C} (f : X ⟶ Y) (hf : P f) (hY : P (terminal.from Y)) : P (terminal.from X) := by
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  exact P.comp_mem _ _ hf hY

/-- If both `X ⟶ ⊤_ C` and `Y ⟶ ⊤_ C` lie in `P`, then so does every `f : X ⟶ Y`. -/
theorem of_terminal_from (P : MorphismProperty C) [P.HasOfPostcompProperty P]
    {X Y : C} (f : X ⟶ Y) (hX : P (terminal.from X)) (hY : P (terminal.from Y)) : P f := by
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _] at hX
  exact P.of_postcomp f (terminal.from Y) hY hX

/-- For `P` stable under composition and cancelling on the left, and `Y ⟶ ⊤_ C` in `P`, a
morphism `f : X ⟶ Y` lies in `P` if and only if `X ⟶ ⊤_ C` does. -/
theorem terminal_from_iff (P : MorphismProperty C) [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] {X Y : C} (f : X ⟶ Y) (hY : P (terminal.from Y)) :
    P f ↔ P (terminal.from X) :=
  ⟨fun hf ↦ P.terminal_from_of_comp f hf hY, fun hX ↦ P.of_terminal_from f hX hY⟩

/-- For `P` stable under composition and base change and cancelling on the left, if each of
`X ⟶ ⊤_ C`, `Y ⟶ ⊤_ C` and `Z ⟶ ⊤_ C` lies in `P`, then so does `X ×_Y Z ⟶ ⊤_ C`. -/
theorem terminal_from_pullback (P : MorphismProperty C) [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] [P.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hX : P (terminal.from X)) (hY : P (terminal.from Y)) (hZ : P (terminal.from Z)) :
    P (terminal.from (pullback f g)) :=
  P.terminal_from_of_comp (pullback.snd f g)
    (MorphismProperty.pullback_snd f g (P.of_terminal_from f hX hY)) hZ

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

section ClosureInstances

/-- If `f ≫ g` and `g` are separated morphisms of schemes, then so is `f`. -/
instance : MorphismProperty.HasOfPostcompProperty @IsSeparated @IsSeparated :=
  MorphismProperty.HasOfPostcompProperty.of_le _ ⊤ le_top

/-- If `f ≫ g` and `g` are quasi-separated morphisms of schemes, then so is `f`. -/
instance : MorphismProperty.HasOfPostcompProperty @QuasiSeparated @QuasiSeparated :=
  MorphismProperty.HasOfPostcompProperty.of_le _ ⊤ le_top

/-- Quasi-compact quasi-separated morphisms of schemes are stable under composition. -/
instance : MorphismProperty.IsStableUnderComposition (@QuasiCompact ⊓ @QuasiSeparated) :=
  MorphismProperty.IsStableUnderComposition.inf

/-- Quasi-compact quasi-separated morphisms of schemes are stable under base change. -/
instance : MorphismProperty.IsStableUnderBaseChange (@QuasiCompact ⊓ @QuasiSeparated) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- If `f ≫ g` and `g` are quasi-compact quasi-separated morphisms of schemes, then so is `f`. -/
instance : MorphismProperty.HasOfPostcompProperty (@QuasiCompact ⊓ @QuasiSeparated)
    (@QuasiCompact ⊓ @QuasiSeparated) where
  of_postcomp f g hg hfg :=
    ⟨MorphismProperty.of_postcomp @QuasiCompact (W' := @QuasiSeparated) f g hg.2 hfg.1,
      MorphismProperty.of_postcomp @QuasiSeparated (W' := ⊤) f g trivial hfg.2⟩

/-- Quasi-compact separated morphisms of schemes are stable under composition. -/
instance : MorphismProperty.IsStableUnderComposition (@QuasiCompact ⊓ @IsSeparated) :=
  MorphismProperty.IsStableUnderComposition.inf

/-- Quasi-compact separated morphisms of schemes are stable under base change. -/
instance : MorphismProperty.IsStableUnderBaseChange (@QuasiCompact ⊓ @IsSeparated) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- If `f ≫ g` and `g` are quasi-compact separated morphisms of schemes, then so is `f`. -/
instance : MorphismProperty.HasOfPostcompProperty (@QuasiCompact ⊓ @IsSeparated)
    (@QuasiCompact ⊓ @IsSeparated) where
  of_postcomp f g hg hfg :=
    ⟨MorphismProperty.of_postcomp @QuasiCompact (W' := @QuasiSeparated) f g
        (have := hg.2; inferInstance) hfg.1,
      MorphismProperty.of_postcomp @IsSeparated (W' := ⊤) f g trivial hfg.2⟩

end ClosureInstances

/-!
### Clause (1): an affine scheme has `P`

The two single properties are `AlgebraicGeometry.quasiSeparatedSpace_of_isAffine` and
`AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine` in Mathlib.
-/

/-- An affine scheme is quasi-compact and quasi-separated. -/
@[stacks 0816 "(1), quasi-compact and quasi-separated"]
theorem compactSpace_and_quasiSeparatedSpace_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩

/-- An affine scheme is quasi-compact and separated. -/
@[stacks 0816 "(1), quasi-compact and separated"]
theorem compactSpace_and_isSeparated_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    CompactSpace X ∧ X.IsSeparated := ⟨inferInstance, inferInstance⟩

/-!
### Clause (2): over a target having `P`, the morphism has `P` iff the source does

The quasi-separated case is `AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace` in
Mathlib.
-/

/-- A morphism to a separated scheme is separated if and only if its source is a separated
scheme. The direction from the source to the morphism holds with no hypothesis on the target; it
is the converse that uses `Y.IsSeparated`. -/
@[stacks 0816 "(2), separated"]
theorem isSeparated_iff_scheme_isSeparated (f : X ⟶ Y) [Y.IsSeparated] :
    IsSeparated f ↔ X.IsSeparated := by
  rw [Scheme.isSeparated_iff]
  exact MorphismProperty.terminal_from_iff @IsSeparated f ((Scheme.isSeparated_iff Y).1 ‹_›)

/-- A morphism to a quasi-compact quasi-separated scheme is quasi-compact and quasi-separated if
and only if its source is a quasi-compact quasi-separated scheme. -/
@[stacks 0816 "(2), quasi-compact and quasi-separated"]
theorem quasiCompact_and_quasiSeparated_iff (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] :
    (QuasiCompact f ∧ QuasiSeparated f) ↔ (CompactSpace X ∧ QuasiSeparatedSpace X) :=
  and_congr (quasiCompact_iff_compactSpace f) (quasiSeparated_iff_quasiSeparatedSpace f)

/-- A morphism to a quasi-compact separated scheme is quasi-compact and separated if and only if
its source is a quasi-compact separated scheme. -/
@[stacks 0816 "(2), quasi-compact and separated"]
theorem quasiCompact_and_isSeparated_iff (f : X ⟶ Y) [CompactSpace Y] [Y.IsSeparated] :
    (QuasiCompact f ∧ IsSeparated f) ↔ (CompactSpace X ∧ X.IsSeparated) :=
  and_congr (quasiCompact_iff_compactSpace f) (isSeparated_iff_scheme_isSeparated f)

/-!
### Clause (3): a fibre product of schemes having `P` has `P`
-/

/-- A fibre product of quasi-separated schemes over a quasi-separated scheme is
quasi-separated. -/
@[stacks 0816 "(3), quasi-separated"]
theorem quasiSeparatedSpace_pullback (f : X ⟶ Y) (g : Z ⟶ Y)
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Z] :
    QuasiSeparatedSpace ↑(pullback f g) :=
  (quasiSeparatedSpace_iff_quasiSeparated _).2 <|
    MorphismProperty.terminal_from_pullback @QuasiSeparated f g
      ((quasiSeparatedSpace_iff_quasiSeparated X).1 ‹_›)
      ((quasiSeparatedSpace_iff_quasiSeparated Y).1 ‹_›)
      ((quasiSeparatedSpace_iff_quasiSeparated Z).1 ‹_›)

/-- A fibre product of separated schemes over a separated scheme is separated. -/
@[stacks 0816 "(3), separated"]
theorem isSeparated_pullback (f : X ⟶ Y) (g : Z ⟶ Y)
    [X.IsSeparated] [Y.IsSeparated] [Z.IsSeparated] : (pullback f g).IsSeparated :=
  (Scheme.isSeparated_iff _).2 <|
    MorphismProperty.terminal_from_pullback @IsSeparated f g
      ((Scheme.isSeparated_iff X).1 ‹_›) ((Scheme.isSeparated_iff Y).1 ‹_›)
      ((Scheme.isSeparated_iff Z).1 ‹_›)

/-- A fibre product of quasi-compact schemes over a quasi-compact quasi-separated scheme is
quasi-compact, if the schemes are quasi-separated over the base. -/
private theorem compactSpace_pullback (f : X ⟶ Y) (g : Z ⟶ Y)
    [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z]
    [QuasiSeparatedSpace Z] : CompactSpace ↑(pullback f g) :=
  have := (quasiCompact_iff_compactSpace f).2 ‹_›
  (quasiCompact_iff_compactSpace (pullback.snd f g)).1 inferInstance

/-- A fibre product of quasi-compact quasi-separated schemes over a quasi-compact
quasi-separated scheme is quasi-compact and quasi-separated. -/
@[stacks 0816 "(3), quasi-compact and quasi-separated"]
theorem compactSpace_and_quasiSeparatedSpace_pullback (f : X ⟶ Y) (g : Z ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z] :
    CompactSpace ↑(pullback f g) ∧ QuasiSeparatedSpace ↑(pullback f g) :=
  ⟨compactSpace_pullback f g, quasiSeparatedSpace_pullback f g⟩

/-- A fibre product of quasi-compact separated schemes over a quasi-compact separated scheme is
quasi-compact and separated. -/
@[stacks 0816 "(3), quasi-compact and separated"]
theorem compactSpace_and_isSeparated_pullback (f : X ⟶ Y) (g : Z ⟶ Y)
    [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated]
    [CompactSpace Z] [Z.IsSeparated] :
    CompactSpace ↑(pullback f g) ∧ (pullback f g).IsSeparated :=
  ⟨compactSpace_pullback f g, isSeparated_pullback f g⟩

end AlgebraicGeometry
