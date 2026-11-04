module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.SectionRange

/-!
# The relative projective line is stable under base change

For `f : X ⟶ S` the family `X ×_S ℙ¹_S` of `StacksFrontier.AlgebraicGeometry.Chow.FibreCycles` is
the projective line `ℙ¹_X` over `X`: both are the product of `X` with `ℙ¹_ℤ` over the terminal
scheme. This file gives that identification as a cartesian square, as an isomorphism, and as a
dictionary for the two distinguished sections, and deduces that the fibre of `ℙ¹_X ⟶ X` over a
point `x` is the projective line over the residue field `κ(x)`.

## Main definitions

* `Stacks.Chow.projectiveLineBaseChange` — the morphism `ℙ¹_X ⟶ ℙ¹_S` over `f : X ⟶ S`.
* `Stacks.Chow.relativeProjectiveLineIsoProjectiveLineProduct` — the isomorphism
  `ℙ¹_X ≅ X ×_S ℙ¹_S`.
* `Stacks.Chow.absoluteConstantSection` — the section `X ⟶ ℙ¹_X` at an integral point of `ℙ¹_ℤ`,
  the `ℙ¹_X`-side counterpart of `Stacks.Chow.constantSection`.
* `Stacks.Chow.fiberIsoRelativeProjectiveLine` — the identification of the fibre of `ℙ¹_X ⟶ X`
  over a point with `ℙ¹` over the residue field at that point.

## Main results

* `Stacks.Chow.isPullback_projectiveLineBaseChange` — the square
  `ℙ¹_X ⟶ ℙ¹_S`, `ℙ¹_X ⟶ X`, `X ⟶ S`, `ℙ¹_S ⟶ S` is cartesian; the isomorphism is
  `IsPullback.isoPullback` applied to it.
* `Stacks.Chow.projectiveLineBaseChange_id` and `Stacks.Chow.projectiveLineBaseChange_comp` —
  the base-change morphism is functorial.
* `Stacks.Chow.constantSection_eq`, `Stacks.Chow.zeroSection_eq` and
  `Stacks.Chow.infinitySection_eq` — under the identification the constant, zero and infinity
  sections of `X ×_S ℙ¹_S ⟶ X` are the corresponding sections of `ℙ¹_X ⟶ X`.
* `Stacks.Chow.isPullback_fiber_relativeProjectiveLine` — `ℙ¹` over the residue field at `x` is
  the scheme-theoretic fibre of `ℙ¹_X ⟶ X` at `x`.

## Implementation notes

### What this identifies, and what it does not

This file identifies the *ambient* family `X ×_S ℙ¹_S` with `ℙ¹_X`, together with its two
distinguished sections. It says nothing about a closed subscheme `W ⊆ X ×_S ℙ¹_S`: in particular
it does **not** by itself identify the generic fibre of `W ⟶ X` with a curve over a function
field, because `W` is not the whole family. For that, the fibre of a morphism as a base change is
`AlgebraicGeometry.Scheme.Hom.fiber`, which Mathlib already provides, and the statement needed by
part (2) of Stacks 02S4 in the dimension-drop case is about `W`, not about the ambient family. See
`StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward`.

### Why `IsPullback` and not a composite of isomorphisms

`Stacks.Chow.relativeProjectiveLine` is a pullback, hence an object whose limit cone the kernel
can be asked to compute; a named definition whose body composes canonical isomorphisms out of
such an object makes the kernel unfold that cone and does not typecheck in reasonable time.
Everything here is therefore stated as a cartesian square — a proposition, with no cone to unfold
— and the isomorphisms are produced one at a time by `CategoryTheory.IsPullback.isoPullback` and
never composed.

### `AlgebraicGeometry.Spec`

A root-level `Spec` is in scope through the transitive imports of this chapter, so
`AlgebraicGeometry.Spec` is written out in full below.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section BaseChange

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism `ℙ¹_X ⟶ ℙ¹_S` over `f : X ⟶ S`: it is `f` on the base and the identity on the
`ℙ¹_ℤ`-coordinate. -/
def projectiveLineBaseChange : relativeProjectiveLine X ⟶ relativeProjectiveLine S :=
  pullback.lift ((relativeProjectiveLine X ↘ X) ≫ f)
    (pullback.snd (terminal.from X) (terminal.from (projectiveLine (ULift.{u} ℤ))))
    (terminal.hom_ext _ _)

/-- The base-change morphism `ℙ¹_X ⟶ ℙ¹_S` followed by the projection `ℙ¹_S ⟶ S` is the
structure morphism of `ℙ¹_X` followed by `f`. -/
@[reassoc (attr := simp)]
theorem projectiveLineBaseChange_comp_fst :
    projectiveLineBaseChange f ≫
        pullback.fst (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))) =
      (relativeProjectiveLine X ↘ X) ≫ f :=
  pullback.lift_fst _ _ _

/-- The base-change morphism `ℙ¹_X ⟶ ℙ¹_S` commutes with the projections to `ℙ¹_ℤ`. -/
@[reassoc (attr := simp)]
theorem projectiveLineBaseChange_comp_snd :
    projectiveLineBaseChange f ≫
        pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))) =
      pullback.snd (terminal.from X) (terminal.from (projectiveLine (ULift.{u} ℤ))) :=
  pullback.lift_snd _ _ _

/-- The base-change morphism is a morphism over `f`. -/
@[reassoc (attr := simp)]
theorem projectiveLineBaseChange_over :
    projectiveLineBaseChange f ≫ (relativeProjectiveLine S ↘ S) =
      (relativeProjectiveLine X ↘ X) ≫ f :=
  projectiveLineBaseChange_comp_fst f

/-- **`ℙ¹_X` is the base change of `ℙ¹_S` along `f : X ⟶ S`.** The square

```
ℙ¹_X ---> ℙ¹_S
 |          |
 v          v
 X -- f --> S
```

is cartesian. Equivalently, `X ×_S ℙ¹_S` is `ℙ¹_X`; that reading is
`Stacks.Chow.relativeProjectiveLineIsoProjectiveLineProduct`. -/
theorem isPullback_projectiveLineBaseChange :
    IsPullback (relativeProjectiveLine X ↘ X) (projectiveLineBaseChange f) f
      (relativeProjectiveLine S ↘ S) := by
  refine (IsPullback.of_right
    (h₁₂ := pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))))
    ?_ (projectiveLineBaseChange_over f) (IsPullback.of_hasPullback _ _).flip).flip
  rw [projectiveLineBaseChange_comp_snd f,
    show f ≫ terminal.from S = terminal.from X from terminal.hom_ext _ _]
  exact (IsPullback.of_hasPullback _ _).flip

/-- **The identification `X ×_S ℙ¹_S ≅ ℙ¹_X`**, read from the cartesian square
`Stacks.Chow.isPullback_projectiveLineBaseChange`. It carries the structure morphism of `ℙ¹_X` to
the first projection and the base-change morphism to the second. -/
def relativeProjectiveLineIsoProjectiveLineProduct :
    relativeProjectiveLine X ≅ projectiveLineProduct f :=
  (isPullback_projectiveLineBaseChange f).isoPullback

/-- The identification `ℙ¹_X ≅ X ×_S ℙ¹_S` followed by the first projection is the structure
morphism of `ℙ¹_X`. -/
@[reassoc (attr := simp)]
theorem relativeProjectiveLineIsoProjectiveLineProduct_hom_fst :
    (relativeProjectiveLineIsoProjectiveLineProduct f).hom ≫
        pullback.fst f (relativeProjectiveLine S ↘ S) = relativeProjectiveLine X ↘ X :=
  (isPullback_projectiveLineBaseChange f).isoPullback_hom_fst

/-- The identification `ℙ¹_X ≅ X ×_S ℙ¹_S` followed by the second projection is the base-change
morphism `ℙ¹_X ⟶ ℙ¹_S`. -/
@[reassoc (attr := simp)]
theorem relativeProjectiveLineIsoProjectiveLineProduct_hom_snd :
    (relativeProjectiveLineIsoProjectiveLineProduct f).hom ≫
        pullback.snd f (relativeProjectiveLine S ↘ S) = projectiveLineBaseChange f :=
  (isPullback_projectiveLineBaseChange f).isoPullback_hom_snd

/-- The identification matches the two `ℙ¹_ℤ`-coordinates: the projection of `X ×_S ℙ¹_S` to
`ℙ¹_ℤ` of `Stacks.Chow.projectiveLineProjection` is the second projection of `ℙ¹_X`. -/
@[reassoc (attr := simp)]
theorem relativeProjectiveLineIsoProjectiveLineProduct_hom_projection :
    (relativeProjectiveLineIsoProjectiveLineProduct f).hom ≫ projectiveLineProjection f =
      pullback.snd (terminal.from X) (terminal.from (projectiveLine (ULift.{u} ℤ))) := by
  rw [projectiveLineProjection, ← Category.assoc,
    relativeProjectiveLineIsoProjectiveLineProduct_hom_snd,
    projectiveLineBaseChange_comp_snd]

end BaseChange

section Functoriality

/-- The base-change morphism along the identity of `X` is the identity of `ℙ¹_X`. -/
@[simp]
theorem projectiveLineBaseChange_id (X : Scheme.{u}) :
    projectiveLineBaseChange (𝟙 X) = 𝟙 (relativeProjectiveLine X) := by
  apply pullback.hom_ext <;> simp [relativeProjectiveLine_over_hom]

/-- The base-change morphism along a composite `g ≫ f` is the composite of the base-change
morphisms along `g` and along `f`. -/
theorem projectiveLineBaseChange_comp {T X S : Scheme.{u}} (g : T ⟶ X) (f : X ⟶ S) :
    projectiveLineBaseChange (g ≫ f) =
      projectiveLineBaseChange g ≫ projectiveLineBaseChange f := by
  apply pullback.hom_ext
  · rw [projectiveLineBaseChange_comp_fst, Category.assoc,
      projectiveLineBaseChange_comp_fst, projectiveLineBaseChange_over_assoc]
  · rw [projectiveLineBaseChange_comp_snd, Category.assoc,
      projectiveLineBaseChange_comp_snd, projectiveLineBaseChange_comp_snd]

end Functoriality

section Sections

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ))

/-- The second component of a constant section of `X ×_S ℙ¹_S ⟶ X` is the point of `ℙ¹_S` over
`f` with constant `ℙ¹_ℤ`-coordinate `e`. -/
@[reassoc (attr := simp)]
theorem constantSection_comp_snd :
    constantSection f e ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      pullback.lift f (terminal.from X ≫ e) (terminal.hom_ext _ _) :=
  pullback.lift_snd _ _ _

end Sections

section AbsoluteSections

variable (X : Scheme.{u}) (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ))

/-- The section `X ⟶ ℙ¹_X` of the structure morphism determined by an integral point `e` of
`ℙ¹_ℤ`. This is the `ℙ¹_X`-side form of `Stacks.Chow.constantSection`; the two agree under
`Stacks.Chow.relativeProjectiveLineIsoProjectiveLineProduct` by
`Stacks.Chow.constantSection_eq`. -/
def absoluteConstantSection : X ⟶ relativeProjectiveLine X :=
  pullback.lift (𝟙 X) (terminal.from X ≫ e) (terminal.hom_ext _ _)

/-- The absolute constant section followed by the projection `ℙ¹_X ⟶ X` is the identity. -/
@[reassoc (attr := simp)]
theorem absoluteConstantSection_comp_fst :
    absoluteConstantSection X e ≫
        pullback.fst (terminal.from X) (terminal.from (projectiveLine (ULift.{u} ℤ))) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The absolute constant section at `e` followed by the projection `ℙ¹_X ⟶ ℙ¹_ℤ` is the constant
morphism `X ⟶ ℙ¹_ℤ` with value `e`. -/
@[reassoc (attr := simp)]
theorem absoluteConstantSection_comp_snd :
    absoluteConstantSection X e ≫
        pullback.snd (terminal.from X) (terminal.from (projectiveLine (ULift.{u} ℤ))) =
      terminal.from X ≫ e :=
  pullback.lift_snd _ _ _

/-- An absolute constant section is a section of `ℙ¹_X ⟶ X`. -/
@[reassoc (attr := simp)]
theorem absoluteConstantSection_over :
    absoluteConstantSection X e ≫ (relativeProjectiveLine X ↘ X) = 𝟙 X :=
  absoluteConstantSection_comp_fst X e

/-- An absolute constant section is a split monomorphism, the structure morphism being its
retraction. -/
instance isSplitMono_absoluteConstantSection : IsSplitMono (absoluteConstantSection X e) :=
  IsSplitMono.mk' ⟨relativeProjectiveLine X ↘ X, absoluteConstantSection_over X e⟩

variable {X}

/-- The absolute constant sections are natural in the base. -/
theorem absoluteConstantSection_comp_projectiveLineBaseChange {S : Scheme.{u}} (f : X ⟶ S) :
    absoluteConstantSection X e ≫ projectiveLineBaseChange f =
      f ≫ absoluteConstantSection S e := by
  apply pullback.hom_ext <;> simp

/-- **The constant sections match under the identification.** The constant section of
`X ×_S ℙ¹_S ⟶ X` at an integral point `e` of `ℙ¹_ℤ` is the constant section of `ℙ¹_X ⟶ X` at `e`,
transported along `Stacks.Chow.relativeProjectiveLineIsoProjectiveLineProduct`. -/
theorem constantSection_eq {S : Scheme.{u}} (f : X ⟶ S) :
    constantSection f e =
      absoluteConstantSection X e ≫ (relativeProjectiveLineIsoProjectiveLineProduct f).hom := by
  apply pullback.hom_ext
  · rw [constantSection_comp_fst, Category.assoc,
      relativeProjectiveLineIsoProjectiveLineProduct_hom_fst, absoluteConstantSection_over]
  · rw [Category.assoc, relativeProjectiveLineIsoProjectiveLineProduct_hom_snd,
      constantSection_comp_snd, absoluteConstantSection_comp_projectiveLineBaseChange]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, absoluteConstantSection_comp_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, absoluteConstantSection_comp_snd,
        terminal.comp_from_assoc]

/-- The zero section of `X ×_S ℙ¹_S ⟶ X` is the zero section of `ℙ¹_X ⟶ X`. -/
theorem zeroSection_eq {S : Scheme.{u}} (f : X ⟶ S) :
    zeroSection f = absoluteConstantSection X integralZeroSection ≫
      (relativeProjectiveLineIsoProjectiveLineProduct f).hom :=
  constantSection_eq integralZeroSection f

/-- The infinity section of `X ×_S ℙ¹_S ⟶ X` is the infinity section of `ℙ¹_X ⟶ X`. -/
theorem infinitySection_eq {S : Scheme.{u}} (f : X ⟶ S) :
    infinitySection f = absoluteConstantSection X integralInfinitySection ≫
      (relativeProjectiveLineIsoProjectiveLineProduct f).hom :=
  constantSection_eq integralInfinitySection f

end AbsoluteSections

section Fibre

variable {X : Scheme.{u}}

/-- **The fibre of `ℙ¹_X ⟶ X` over a point is `ℙ¹` over the residue field there.** This is
`Stacks.Chow.isPullback_projectiveLineBaseChange` base-changed along
`AlgebraicGeometry.Scheme.fromSpecResidueField`. -/
theorem isPullback_fiber_relativeProjectiveLine (x : X) :
    IsPullback
      (relativeProjectiveLine (AlgebraicGeometry.Spec (X.residueField x)) ↘
        AlgebraicGeometry.Spec (X.residueField x))
      (projectiveLineBaseChange (X.fromSpecResidueField x))
      (X.fromSpecResidueField x) (relativeProjectiveLine X ↘ X) :=
  isPullback_projectiveLineBaseChange (X.fromSpecResidueField x)

/-- `ℙ¹` over the residue field at `x` is the scheme-theoretic fibre of `ℙ¹_X ⟶ X` at `x`. -/
def fiberIsoRelativeProjectiveLine (x : X) :
    relativeProjectiveLine (AlgebraicGeometry.Spec (X.residueField x)) ≅
      (relativeProjectiveLine X ↘ X : relativeProjectiveLine X ⟶ X).fiber x :=
  (isPullback_fiber_relativeProjectiveLine x).flip.isoPullback

end Fibre

end Stacks.Chow

end
