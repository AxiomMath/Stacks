module
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! Stacks tags of Chapter 4 (Categories) that Mathlib already states.

This file records Stacks Project tags from Chapter 4 (Categories) whose statements are already
available in Mathlib, by attaching each tag to the Mathlib declarations that state it. When a
tag is covered by several declarations, each registration names the part it covers.
Mathlib models a set of arrows `S` as a `MorphismProperty`, and a left (right) multiplicative
system as a morphism property with a left (right) calculus of fractions; a multiplicative system
is a morphism property with both. A Stacks pair `(f : X → Y', s : Y → Y')` with `s ∈ S` is a
`MorphismProperty.LeftFraction`, and `S⁻¹C` is `MorphismProperty.LeftFraction.Localization`.
Mathlib writes composition in diagrammatic order (`f ≫ g` is `g ∘ f`).
* 04VC: left, right and two-sided multiplicative systems.
* 04VD: the category `S⁻¹C` of a left multiplicative system.
* 04VG: the functor `Q : C → S⁻¹C` and its universal property.
* [Stacks: Localization in categories](https://stacks.math.columbia.edu/tag/04VB)
-/

@[expose] public section

-- Items (1) and (2) of Stacks 02XH: for `p : 𝒳 ⥤ 𝒮` and `S : 𝒮`, the objects of the fibre
-- category over `S` are the objects `a` with `p.obj a = S`, which are the lifts of `S`.
add_to_stacks 02XH "(1) objects of the fibre category, (2) lifts of an object"
  CategoryTheory.Functor.Fiber
-- Item (1) of Stacks 02XH: the morphisms of the fibre category over `S` are the morphisms `φ`
-- of `𝒳` with `p(φ) = 𝟙 S`, that is `p.IsHomLift (𝟙 S) φ`.
add_to_stacks 02XH "(1) morphisms of the fibre category"
  CategoryTheory.Functor.Fiber.fiberCategory
-- Item (3) of Stacks 02XH: `p.IsHomLift f φ` says that `φ` lies over `f`, that is `p(φ) = f`.
add_to_stacks 02XH "(3) lift of a morphism" CategoryTheory.Functor.IsHomLift
-- Stacks 02Y0: a category whose only morphisms are identities. Mathlib states this as the two
-- conditions that every morphism `X ⟶ Y` forces `X = Y` and that parallel morphisms coincide;
-- together these say that every morphism is the identity of its source.
add_to_stacks 02Y0 CategoryTheory.IsDiscrete
end

add_to_stacks 002W "colim over filtered commutes with finite lim"
  CategoryTheory.Limits.colimitLimitToLimitColimit_isIso
add_to_stacks 002W "finite products, fibre products, equalizers"
  CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types

-- Mathlib's `CategoryTheory.ExactPairing X Y` is the Stacks statement "`Y` is a left dual of `X`"
-- (equivalently, "`X` is a right dual of `Y`"). Mathlib's names for left and right duals are the
-- reverse of the Stacks ones: Mathlib's `HasRightDual X` provides a Stacks left dual of `X`.
add_to_stacks 0FFP CategoryTheory.ExactPairing

add_to_stacks 0FFY CategoryTheory.Functor.Braided

add_to_stacks 0FN8 CategoryTheory.BraidedCategory.exactPairing_swap

add_to_stacks 003R "objects: triples (A, B, f)" CategoryTheory.Limits.CategoricalPullback
add_to_stacks 003R "morphisms: compatible pairs (a, b)"
  CategoryTheory.Limits.CategoricalPullback.instCategory
add_to_stacks 003R "projections and the transformation ψ"
  CategoryTheory.Limits.CategoricalPullback.catCommSq

add_to_stacks 003Y "objects: functors p : S → C" CategoryTheory.BasedCategory
add_to_stacks 003Y "1-morphisms: functors G with p' ∘ G = p" CategoryTheory.BasedFunctor
add_to_stacks 003Y "2-morphisms" CategoryTheory.BasedNatTrans
add_to_stacks 003Y "the category Mor_{Cat/C}(S, S')" CategoryTheory.BasedNatTrans.homCategory
add_to_stacks 003Y "the 2-category structure" CategoryTheory.BasedCategory.bicategory

open CategoryTheory
add_to_stacks 04VC "LMS1 = RMS1: identities and composites of elements of S lie in S"
  MorphismProperty.IsMultiplicative
add_to_stacks 04VC "left multiplicative system: LMS1, LMS2 (exists_leftFraction), LMS3 (ext)"
  MorphismProperty.HasLeftCalculusOfFractions
add_to_stacks 04VC "right multiplicative system: RMS1, RMS2 (exists_rightFraction), RMS3 (ext)"
  MorphismProperty.HasRightCalculusOfFractions
add_to_stacks 04VD "the pairs (f : X → Y', s : Y → Y') with s ∈ S"
  MorphismProperty.LeftFraction
add_to_stacks 04VD "the relation on pairs" CategoryTheory.MorphismProperty.LeftFractionRel
add_to_stacks 04VD "(1) the relation is an equivalence relation"
  MorphismProperty.equivalenceLeftFractionRel
add_to_stacks 04VD "(2) the class of the composite does not depend on the square chosen by LMS2"
  MorphismProperty.LeftFraction.comp₀_rel
add_to_stacks 04VD "(2) composition of classes is computed on representatives"
  MorphismProperty.LeftFraction.Localization.Hom.comp_eq
add_to_stacks 04VD "(3) the category S⁻¹C"
  MorphismProperty.LeftFraction.Localization.instCategory
add_to_stacks 04VG "(1) the functor Q" CategoryTheory.MorphismProperty.LeftFraction.Localization.Q
add_to_stacks 04VG "(1) Q sends f to the class of (f, id)"
  MorphismProperty.LeftFraction.Localization.Q_map
add_to_stacks 04VG "(2) Q(s) is an isomorphism for s ∈ S"
  MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.inverts
add_to_stacks 04VG "(3) existence of H"
  MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.lift
add_to_stacks 04VG "(3) H ∘ Q = G"
  MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.fac
add_to_stacks 04VG "(3) uniqueness of H"
  MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.uniq

add_to_stacks 0BM2 "the pair `(f : X ⟶ Y', s : Y ⟶ Y')` with `s ∈ S`"
  CategoryTheory.MorphismProperty.LeftFraction
add_to_stacks 0BM2 "its equivalence class `s⁻¹f`, a morphism `X ⟶ Y` of `S⁻¹C`"
  CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk
