module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionCommonRefinement
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionTorsor
import StacksCore.Tactic.StacksAttribute

/-!
# The torsor of square-zero extensions under `Ext¹(𝖭𝖫_{X/S}, 𝒢)` (towards Stacks 0GPZ)

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. An
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension` is a square-zero extension
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras, which is the object **Stacks 0GPZ** counts.

The torsor formalism of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionTorsor.lean` asks for a difference
cocycle on the type of objects with values in the acting group. Here that cocycle is
*presentation-free*: `extClassDiff P₁ P₂` is the difference
`P₁.toPresented.extClass - P₂.toPresented.extClass` of the two classes in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` that
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationClass.lean` attaches to the
two extensions, each read over its *own* presentation. So it is defined for *every* pair of
extensions, no family of generators appears in its type, and the acting group is the group of
the tag, `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, rather than the `Ext¹` of a presentation.

Both of the formalism's requirements on the cocycle are therefore theorems rather than
hypotheses. That it is well defined on extensions — independent of the presentation used to
compute each class — is
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.presentedBy_extClass`, and
the cocycle identity is the group identity `(a - b) + (b - c) = a - c`. The separation statement
comes from the common refinement of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionCommonRefinement.lean`: the cocycle
vanishes exactly when the obstruction class of the difference homomorphism over
`𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` does.

What is *not* proved here is that the cocycle is surjective — that every class of
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the difference of two extensions. That is the pushout
construction of the proof of **Stacks 08UC**, and it is carried here as the single hypothesis
`realize`; it is discharged, unconditionally, by
`AlgebraicGeometry.RingedSpaceThickening.realizeExtClassDiff` of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionFromPushout.lean`, which cannot be
imported here because it consumes this file.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.extClassDiff`: the difference of the classes of two
  arbitrary square-zero extensions, an element of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.
* `AlgebraicGeometry.RingedSpaceThickening.extClassObstruction`: the obstruction data of
  **Stacks 08UC** on the type of square-zero extensions, with `extClassDiff` as its cocycle and
  `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` as its acting group.
* `AlgebraicGeometry.RingedSpaceThickening.extClassAddTorsor`: the principal homogeneous space
  structure the formalism then provides. The resulting bijection with
  `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is
  `AlgebraicGeometry.RingedSpaceThickening.classesEquivExtRelative` of
  `StacksFrontier/Deformation/RingedSpaceThickening/SquareZeroExtensionClasses.lean`, which is
  where the base point lives.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.extClassDiff_add`: **the cocycle identity for three
  arbitrary square-zero extensions**, with no common presentation in its statement.
* `AlgebraicGeometry.RingedSpaceThickening.extClassDiff_self`,
  `...extClassDiff_swap`: the cocycle vanishes on the diagonal and is antisymmetric.
* `AlgebraicGeometry.RingedSpaceThickening.extClassDiff_eq_zero_of_hom`: **a morphism of
  extensions makes the cocycle vanish**, so the quotient below is a quotient of the set of
  isomorphism classes.
* `AlgebraicGeometry.RingedSpaceThickening.extClassDiff_eq_zero_iff_pairRefinement`: the cocycle
  vanishes exactly when the obstruction class of the difference homomorphism over the common
  refinement vanishes, which by clause (1) of **Stacks 08U8** is the existence of a morphism
  between the two extensions.
* `AlgebraicGeometry.RingedSpaceThickening.extClassDiff_tripleRefinement`: the cocycle is the
  obstruction class of the difference homomorphism over the common refinement of the pair
  together with any third extension, so all three cocycles of a triple are taken over one
  presentation.

## Implementation notes

The reshaping relative to
`AlgebraicGeometry.RingedSpaceThickening.classesEquivExt` of
`StacksFrontier/Deformation/RingedSpaceThickening/SquareZeroExtensionClasses.lean` is the order of
the binders. There the two-term complex `P` of a presentation is fixed *before* the cocycle, so
the cocycle must land in one `P.conormal ⟶ 𝒢` for every pair of extensions at once; no family
of generators serves every extension, since the lift `α'` is part of the datum and
`𝒪_{X'} ⟶ 𝒪_X` is only locally surjective, so that cocycle cannot be constructed and the acting
group is the `Ext¹` of `P`. Here no presentation is fixed at all: each extension contributes the
class of its own presentation, the classes are compared in the group of `𝖭𝖫_{X/S}`, and the
presentation enters only inside the *proofs*, as the common refinement of whichever extensions
the statement at hand mentions.

One hypothesis remains, `realize`: for an extension `𝒪_{X'}` and a class `ξ`, an extension whose
cocycle against `𝒪_{X'}` is `ξ`. This is the pushout of the square-zero extension along
`ψ = φ|_{ℐ'} + δ ∘ (ℐ' ⟶ ℐ/ℐ²)` in the proof of **Stacks 08UC**, where `δ` is a conormal
homomorphism representing `ξ` over a suitable family of generators. Its two inputs are of
different kinds. The conormal homomorphism is **Stacks 08UB**, available as
`Stacks.SheafOfModules.ConormalRepresentative.exists_enlargement_conormalExtClass`; because the
acting group here is presentation-free, the family of generators that tag produces may be an
arbitrary one rather than a refinement of a prescribed one, which is why the hypothesis `rep` of
`AlgebraicGeometry.RingedSpaceThickening.liftingObstructionSolution` has no counterpart below.
The pushout itself is the square-zero pushout of
`StacksFrontier/CategoryTheory/Sites/Modules/SquareZeroPushout.lean`, read as a square-zero
extension of `f⁻¹𝒪_S`-algebras in
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionFromPushout.lean`.

`realize` is a subtype-valued function rather than an existence statement, as in
`SolutionTorsor.lean`: the action of the group on classes of extensions is `Quotient.liftOn` of
it, and an existence statement could not be acted with without choice.

The `Ext¹` groups are morphism groups of the derived category under
`HasDerivedCategory.standard`, enabled as a local instance in the `Derived` sections, exactly as
in `ExtensionPresentationClass.lean`; the objects are the named abbreviations
`PresentedSquareZeroExtension.relativeObj` and `PresentedSquareZeroExtension.shiftedSingleObj`
of that file and of `ExtensionPresentation.lean`, so that the ambient abelian category is pinned
before instance search runs.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

section Derived

attribute [local instance] HasDerivedCategory.standard

/-! ### The presentation-free difference cocycle -/

/-- **The difference of the classes of two arbitrary square-zero extensions**, as an element of
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.

Each extension contributes the class of its *own* presentation — the family of generators
underlying its structure sheaf, with `α'` the identity — and the two classes are subtracted in
the group of `𝖭𝖫_{X/S}`, where by
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.presentedBy_extClass` they
do not depend on the presentation used to compute them. So this is defined for *every* pair of
extensions, and no family of generators appears in its type. -/
def extClassDiff (P₁ P₂ : AlgebraSquareZeroExtension f G) :
    PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G :=
  P₁.toPresented.extClass - P₂.toPresented.extClass

/-- **The cocycle identity for three arbitrary square-zero extensions.** With the
presentation-free cocycle this is the group identity `(a - b) + (b - c) = a - c`; the content it
replaces — that all three differences can be computed by obstruction homomorphisms over one
presentation — is
`AlgebraicGeometry.RingedSpaceThickening.conormalExtClass_obstruction_add_tripleRefinement`. -/
theorem extClassDiff_add (P₁ P₂ P₃ : AlgebraSquareZeroExtension f G) :
    extClassDiff P₁ P₂ + extClassDiff P₂ P₃ = extClassDiff P₁ P₃ :=
  sub_add_sub_cancel _ _ _

/-- The cocycle vanishes on the diagonal. -/
theorem extClassDiff_self (P : AlgebraSquareZeroExtension f G) : extClassDiff P P = 0 :=
  sub_self _

/-- Reversing the direction negates the cocycle. -/
theorem extClassDiff_swap (P₁ P₂ : AlgebraSquareZeroExtension f G) :
    extClassDiff P₂ P₁ = -extClassDiff P₁ P₂ :=
  (neg_sub _ _).symm

/-- The cocycle vanishes exactly when the two extensions have the same class in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`. -/
theorem extClassDiff_eq_zero_iff (P₁ P₂ : AlgebraSquareZeroExtension f G) :
    extClassDiff P₁ P₂ = 0 ↔ P₁.toPresented.extClass = P₂.toPresented.extClass :=
  sub_eq_zero

/-- **A morphism of square-zero extensions makes the cocycle vanish.** A morphism
`θ : 𝒪_{X'₁} ⟶ 𝒪_{X'₂}` over `𝒪_X` compatible with the two identifications of the square-zero
ideal with `𝒢` suffices; such a morphism is in any case invertible by
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_hom`. So the quotient by the
vanishing of this cocycle is a quotient of the set of isomorphism classes of extensions, which
is the set **Stacks 0GPZ** counts. -/
theorem extClassDiff_eq_zero_of_hom (P₁ P₂ : AlgebraSquareZeroExtension f G)
    (θ : P₁.sheaf ⟶ P₂.sheaf) (hbase : P₁.base ≫ θ = P₂.base)
    (hred : θ ≫ P₂.reduction = P₁.reduction)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
      P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
        θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y) :
    extClassDiff P₁ P₂ = 0 :=
  (extClassDiff_eq_zero_iff P₁ P₂).2
    (AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom P₁ P₂ θ hbase hred hideal)

/-- **The cocycle is the obstruction class of the difference homomorphism over the common
refinement** `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`: the presentation-free difference on the left agrees
with the difference formula of **Stacks 08U8**, read over the refinement where both extensions
are presented. -/
theorem extClassDiff_pairRefinement (P₁ P₂ : AlgebraSquareZeroExtension f G) :
    extClassDiff P₁ P₂ =
      (PresentedSquareZeroExtension.naiveCotangentIso f (pairRefinementGenerators P₁ P₂)
          (pairRefinementMap P₁ P₂)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
            (pairRefinementMap P₁ P₂)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
            (pairRefinementSnd P₁ P₂)) :=
  extClass_sub_extClass_pairRefinement P₁ P₂

/-- **The cocycle vanishes exactly when the obstruction class of the difference homomorphism
over the common refinement vanishes.** By clause (1) of **Stacks 08U8** that class vanishes
exactly when a morphism from the one extension to the other exists, and such a morphism is
invertible by `AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_hom`; so this is the
separation half of **Stacks 0GPZ**, reduced to that clause and to nothing else. -/
theorem extClassDiff_eq_zero_iff_pairRefinement (P₁ P₂ : AlgebraSquareZeroExtension f G) :
    extClassDiff P₁ P₂ = 0 ↔
      (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
            (pairRefinementMap P₁ P₂)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
            (pairRefinementSnd P₁ P₂)) = 0 :=
  (extClassDiff_eq_zero_iff P₁ P₂).trans (extClass_eq_extClass_iff_pairRefinement P₁ P₂)

/-- **The cocycle of a pair, read over the common refinement of the pair together with an
arbitrary third extension.** Taking the third extension to be a fixed one, all three cocycles of
a triple become obstruction classes over the single presentation
`𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂} ×_{𝒪_X} 𝒪_{X'₃}`, and `extClassDiff_add` is then the cocycle identity
of **Stacks 08U8** for three extensions sharing no presentation, namely
`AlgebraicGeometry.RingedSpaceThickening.conormalExtClass_obstruction_add_tripleRefinement`. -/
theorem extClassDiff_tripleRefinement (P₁ P₂ P₃ : AlgebraSquareZeroExtension f G) :
    extClassDiff P₁ P₂ =
      (PresentedSquareZeroExtension.naiveCotangentIso f (tripleRefinementGenerators P₁ P₂ P₃)
          (tripleRefinementMap P₁ P₂ P₃)).inv ≫
        (PresentedSquareZeroExtension.twoTerm f (tripleRefinementGenerators P₁ P₂ P₃)
            (tripleRefinementMap P₁ P₂ P₃)).conormalExtClass G
          (PresentedSquareZeroExtension.obstruction (tripleRefinementFst P₁ P₂ P₃)
            (tripleRefinementSnd P₁ P₂ P₃)) :=
  extClass_sub_extClass_tripleRefinement₁₂ P₁ P₂ P₃

/-! ### The torsor -/

/-- **The obstruction data of Stacks 08UC on the type of square-zero extensions**, with the
presentation-free cocycle `extClassDiff` and with `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` — the group of the
tag — as its acting group.

Only one of the four fields is a hypothesis. The cocycle is `extClassDiff`, total on pairs of
extensions, and its cocycle identity is `extClassDiff_add`; what remains is the pushout
construction of the proof of **Stacks 08UC**, here the hypothesis `realize`, which realizes a
prescribed class as the cocycle against a prescribed extension. -/
def extClassObstruction
    (realize : ∀ (P : AlgebraSquareZeroExtension f G)
      (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G),
      { P' : AlgebraSquareZeroExtension f G // extClassDiff P P' = ξ }) :
    SolutionObstruction (AlgebraSquareZeroExtension f G)
      (PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G) where
  o := extClassDiff
  o_add := extClassDiff_add
  twist P ξ := (realize P ξ).1
  o_twist P ξ := (realize P ξ).2

/-- The cocycle of `extClassObstruction realize` is `extClassDiff`. -/
@[simp]
theorem extClassObstruction_o
    (realize : ∀ (P : AlgebraSquareZeroExtension f G)
      (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G),
      { P' : AlgebraSquareZeroExtension f G // extClassDiff P P' = ξ })
    (P₁ P₂ : AlgebraSquareZeroExtension f G) :
    (extClassObstruction realize).o P₁ P₂ = extClassDiff P₁ P₂ :=
  rfl

/-- The classes of square-zero extensions on which `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` acts: the quotient
of the type of extensions by the vanishing of the cocycle. By `extClassDiff_eq_zero_of_hom` this
is a quotient of the set of isomorphism classes, and by
`extClassDiff_eq_zero_iff_pairRefinement` together with clause (1) of **Stacks 08U8** it *is*
that set. -/
abbrev ExtensionClasses
    (realize : ∀ (P : AlgebraSquareZeroExtension f G)
      (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G),
      { P' : AlgebraSquareZeroExtension f G // extClassDiff P P' = ξ }) :=
  (extClassObstruction realize).IsomorphismClasses

/-- **The classes of square-zero extensions are a principal homogeneous space under
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`**, the group of **Stacks 0GPZ** itself. The base point is an
extension — the trivial one `𝒪_X ⋉ 𝒢` whenever it is available — and the only hypothesis
beyond it is `realize`. -/
@[instance_reducible]
noncomputable def extClassAddTorsor
    (realize : ∀ (P : AlgebraSquareZeroExtension f G)
      (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G),
      { P' : AlgebraSquareZeroExtension f G // extClassDiff P P' = ξ })
    (hne : Nonempty (AlgebraSquareZeroExtension f G)) :
    AddTorsor
      (PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G)
      (ExtensionClasses realize) :=
  letI := hne
  (extClassObstruction realize).addTorsor

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
