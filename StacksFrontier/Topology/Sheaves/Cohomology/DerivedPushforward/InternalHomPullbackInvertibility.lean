module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.BifunctorProdMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertibility of the derived pullback of a derived internal hom

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K, M ∈ D(𝒪_Y)`.  Tag 08I3
provides the canonical map

`Lh^* R𝓗om_{𝒪_Y}(K, M) ⟶ R𝓗om_{𝒪_X}(Lh^*K, Lh^*M)`

and Tag 0GM7 asserts that it is an isomorphism when `K` is perfect, and also when `K` is
pseudo-coherent and `M` is bounded below provided `h` is flat or `𝒪_X` has finite tor dimension
over `h^{-1}𝒪_Y`.  This file proves the case of a `K` which is a unit for the derived tensor
product — the case `K = 𝒪_Y[0]`, which is both perfect and pseudo-coherent, so it is the common
base instance of all three clauses — for an arbitrary morphism of ringed spaces and an
arbitrary `M`.

The proof is carried out over the abstract data of the construction of Tag 08I3: a functor `P`
between two categories with internal homs, tensor–internal-hom bijections and a monoidality
comparison.  There the statement is that an object `A` which is a tensor unit on the source and
whose image is a tensor unit on the target, compatibly with the monoidality comparison, has
invertible hom-comparison at every `B`.  The two internal homs are then identified with the two
objects by the evaluation out of a unit, and the comparison is identified with the image of one
identification followed by the inverse of the other.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.TensorHomEquivNaturalLeft`: naturality
  of a tensor–internal-hom bijection in its source variable.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.isIso_unitEvaluation`: for an object
  `A` which is a tensor unit, the evaluation `hom(A, B) ⟶ B` read through the unitor is an
  isomorphism, so `hom(A, -)` is the identity.
* `Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace`: the
  bijection of Tag 08DI on a ringed space is natural in its source variable, which is
  `Transpose.TensorHomEquivNaturalLeft` for it.  This is Tag 08J8 read on a ringed space, and
  it is what the invertibility statement below no longer carries as a hypothesis.
* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.isIso_homComparison_of_tensorUnit`:
  the hom-comparison of a functor with internal hom is invertible at a tensor unit whose image
  is a tensor unit, compatibly with the monoidality comparison.
* `Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_tensorUnit`:
  **Tag 0GM7 at a tensor unit**, the case `K = 𝒪_Y[0]` of the canonical map of Tag 08I3 being
  an isomorphism.

For that theorem with every remaining hypothesis supplied — Tag 0GM7 at `K = 𝒪_Y[0]` with no
hypothesis at all — see
`Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_singleUnit` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackUnit`.

## What is carried, and why

Three inputs are carried, all visible in the statement; none of them mentions invertibility of
the map of Tag 08I3.

*None of the three is a hypothesis of the statement of Tag 0GM7.*  The source's hypotheses are
`K` perfect (clause 1); `h` flat, `K` pseudo-coherent and `M` bounded below (clause 2); and
`𝒪_X` of finite tor dimension over `h^{-1}𝒪_Y` with `K` pseudo-coherent and `M` bounded below
(clause 3).  The binders below are instead steps of the *construction* of the map, carried
because the statements of this file are about an abstract internal hom and tensor product on two
arbitrary categories, where there is nothing to prove them from.  So each is a candidate for
discharge, and the paragraphs below record exactly how far each one gets.

*The naturality of the bijection of Tag 08DI in its source variable,* on `Y` and on `X`, is not
carried as a hypothesis.  It is `tensorHomEquivNaturalLeft_ringedSpace` below, proved from the
source
clause of Tag 08J8,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`.

How that discharge is arranged is worth recording, because the obvious routes all
fail.  The site lemma, instantiated at `Stacks.SheafOfModules.ringedSite Z.sheaf` with the
arguments `A' A B C φ ψ`, differs from `Transpose.TensorHomEquivNaturalLeft` for
`tensorHomEquiv Z` by the `Equiv`-versus-`AddEquiv` coercion and by the
uncurried-versus-curried spelling of the derived tensor product.  Three observations decide how
to bridge them.

*First, the uncurrying is affordable only in the abstract.*
`CategoryTheory.uncurry_map_mkHom_id` states it over three arbitrary categories and compiles at
once, whereas the same identity as a `rw`, a `simp only`, or a residual goal of `convert`, inside
a statement about derived categories of module sheaves, exceeds the budget.

*Second, the bijection and the internal hom have to enter at the spelling Tag 08J8 is proved
at.*  That is the ringed site `Stacks.SheafOfModules.ringedSite Z.sheaf`, with the bijection as
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` and the internal hom as
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` of that site.  Neither is written at the
ringed-space name — not as `Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf`, and not
as `Stacks.SheafOfModules.derivedSheafHom Z.sheaf`.  Nothing is weakened by that: the
space-level names are *definitionally* the site-level ones, `derivedSheafHom Rc` being an
`abbrev` for `RingedSite.derivedSheafHomBifunctor (ringedSite Rc)` at
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedInternalHom.lean:91-95` and
`derivedSheafHomTensorEquiv` an `abbrev`-like definition of `derivedCurryHomEquiv` at `:144-147`
there.  But under an *applied* coercion the two are not interchangeable in budget: the equation
`⇑(derivedSheafHomTensorEquiv Z.sheaf A B C) x = ⇑(derivedCurryHomEquiv _ A B C) x` by `rfl`
exceeds `maxRecDepth`, while the unapplied equation of the two families costs nothing.  So the
identification with the tagged Tag 08DI declaration is left at the family level, where it is
free, and the applied form is never asked for.

*Third, writing the internal hom at the site's own name is what closes the predicate, and it
replaces a reducibility attribute.*  `convert … using 1` stops at the `Iff` of the two
equations, and the congruence it builds there compares the coercion's `FunLike` instance
arguments — which carry the spellings of the derived tensor product and of the derived internal
hom — one at a time, at `.instances` transparency.  With the predicate's internal hom written as
`derivedSheafHom Z.sheaf` those arguments disagree at that transparency, since
`Stacks.SheafOfModules.Tensor.ringSheaf` is an ordinary definition and does not unfold there;
bridging the difference with `attribute [local instance_reducible]` on it would be a spelling
bridge by attribute, which is avoided.  Writing the predicate's internal
hom as `RingedSite.derivedSheafHomBifunctor (ringedSite Z.sheaf)` instead — the same bifunctor,
and the name the bijection itself declares its domain at — makes the two instance arguments
agree *syntactically*, and the residual then closes with no attribute at all.

Each of the alternatives fails without the attribute.  `exact` and the
plain term `fun A A' B C φ ψ => …` in place of the `convert` reach `maxRecDepth`; so do
`convert … using 1` followed by `Iff.rfl` or by `rfl`, `beta_reduce` before the `exact`, and a
`show` of the beta-reduced goal.  `convert … using 2` leaves the same `Iff` as `using 1`.
Ascribing the helper's statement helps only up to a point: ascribing its result type, or the
whole equivalence, to the uncurried spelling makes *the helper itself* elaborate, but handing it
to the predicate still reaches `maxRecDepth`.  Writing the internal hom at the site's own name
is the one route that closes.

*What does not work:* parameterising the `Transpose` section below by the additive
equivalence `Stacks.SheafOfModules.derivedSheafHomTensorEquiv` itself rather than by its `Equiv`
coercion.  That removes the coercion, but it replaces it with a worse mismatch — the `Add`
instance of a hom group reached through the section's `[Preadditive D]` binder against the one
synthesized directly at the derived category — and the instance of the predicate then exceeds
`maxRecDepth` in the same way.  Stating the predicate over the curried tensor product, or with
`Equiv.toFun` in place of the coercion, fails for the same reason.  Hence the interface of
`Transpose` is unchanged and nothing in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap` had to
move; in particular `tensorHomEquiv` and the canonical map of Tag 08I3 are the terms they were.

*The two unitors* `uY : W ⊗^L_{𝒪_Y} K ≅ W` and `uX : W' ⊗^L_{𝒪_X} Lh^*K ≅ W'`, *their
naturality* (`huY`, `huX`) *and the unitor coherence of the comparison of Tag 079U* (`hcoh`).
All five are still carried by the theorem below, and all five are now **discharged at
`K = 𝒪_Y[0]`**, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackUnit`:
`isIso_derivedPullbackSheafHomMap_singleUnit` there is this theorem with every one of them
supplied, so Tag 0GM7 at the structure sheaf is proved with no hypothesis at all.

They are discharged in another file rather than here, and at `K = 𝒪_Y[0]` rather than in place,
for two separate reasons.

*Why at the unit, and why that is not a loss.*  `uY` and `uX` are **data**, not propositions, so
a discharge has to *construct* them, and there is nothing to construct them from while `K` is an
arbitrary object; `huY`, `huX` and `hcoh` are propositions about those binders, so they cannot be
discharged either while the binders are open.  Pinning `K` to the unit object costs nothing,
since the unit case is the only case this theorem is about.  The naturality is
`Stacks.RingedSpace.derivedTensorRightUnitor_naturality`, which is already in exactly the
uncurried `(g ×ₘ 𝟙)` shape the binders ask for; the coherence is
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_unitObject`, which holds at
every object of `D(𝒪_Y)` with no hypothesis.  Both are stated at the *other* of the two derived
tensor products — the one Tag 079U is stated at — so the discharge is a transport along
`tensorBridge`, and for `uX` it also uses the unit comparison `ν : Lh^*(𝒪_Y[0]) ≅ 𝒪_X[0]`.

*Which unitor, and which `ν`.*  The repository carries two separately built right unitors for
that tensor product, `rightUnitIso` and `rightUnitorNatIso`, with no identification between them
proved, and likewise two separately built isomorphisms of the type of `ν`.  A transport has to
commit to one branch of each, and the choice is forced in both cases by
`rightUnitorCoherence_unitObject`: it is stated at the **natural** unitor `rightUnitorNatIso`,
whose naturality on both `X` and `Y` its chain consumes and which alone has an evaluation formula
at an image `Q K`, and at the `ν` of
`Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso` and not at the
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`.  Since `uY`, `uX` and `ν` all enter
the theorem below only through binders, that
is an *instantiation* of the binders and not a restatement of anything: the statement below fixes
no unitor and no unit comparison.

*The coherence was the one genuinely mathematical gap, and it is no longer one.*  At the level of
complexes it was already proved with no hypothesis, as
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_rightUnitor`, and
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat` reduced the derived
statement at every object to its value at a K-flat representative; what was missing was only the
localization bridge between those two, and that bridge is now
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_app_q_of_kFlat`.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0GM5](https://stacks.math.columbia.edu/tag/0GM5)
* [Stacks Project, Tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

-- `Stacks.SheafOfModules.Tensor.ringSheaf` carries NO reducibility attribute in this file, and
-- must not be given one: making it transparent is a spelling bridge by attribute, and the
-- statements below are instead written at one spelling throughout — see *Second* and *Third* in
-- the implementation notes above.
--
-- The line below is a different thing and stays: it is basic instance plumbing, not a spelling
-- bridge in effect.  Every statement here reaches the ring sheaf through the Mathlib accessor
-- `AlgebraicGeometry.SheafedSpace.sheaf` in the object `Z.sheaf`, while the abelian and
-- derived-category instances of `Modules Z` are registered at `Tensor.ringSheaf X.sheaf`, so
-- instance search cannot reach them through the accessor without it: without the line,
-- `CategoryStruct (DerivedCategory (Modules Z))` fails to synthesize.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Transpose

/-! ### The evaluation out of a tensor unit -/

section OneCategory

variable {D : Type*} [Category D] (H : Dᵒᵖ ⥤ D ⥤ D) (T : D × D ⥤ D)
  (e : ∀ A B C : D, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C))

/-- **Naturality of a tensor–internal-hom bijection in its source variable:** the transpose of a
morphism precomposed with `φ` is the transpose tensored on the left with `φ`.  Equivalently, the
bijection is determined by its value at an identity map, which is the evaluation. -/
def TensorHomEquivNaturalLeft : Prop :=
  ∀ (A A' B C : D) (φ : A ⟶ A') (ψ : A' ⟶ (H.obj (op B)).obj C),
    e A B C (φ ≫ ψ) = T.map (φ ×ₘ 𝟙 B) ≫ e A' B C ψ

/-- The inverse of a unitor is natural: `(u W)⁻¹ ≫ T(x ⊗ 1) = x ≫ (u W')⁻¹`. -/
private theorem unitor_inv_comp_map_prod {A : D} (u : ∀ W : D, T.obj (W, A) ≅ W)
    (hu : ∀ (W W' : D) (g : W ⟶ W'),
      T.map (g ×ₘ 𝟙 A) ≫ (u W').hom = (u W).hom ≫ g)
    {W W' : D} (x : W ⟶ W') :
    (u W).inv ≫ T.map (x ×ₘ 𝟙 A) = x ≫ (u W').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hu W W' x]
  simp

/-- Tensoring with `x` and then evaluating is the transpose of `x`. -/
private theorem map_prod_comp_evaluation (hnat : TensorHomEquivNaturalLeft H T e) {A B C : D}
    (x : C ⟶ (H.obj (op A)).obj B) :
    T.map (x ×ₘ 𝟙 A) ≫ evaluation H T e A B = e C A B x := by
  have hn := hnat C ((H.obj (op A)).obj B) A B x (𝟙 _)
  rw [Category.comp_id] at hn
  exact hn.symm

/-- **The evaluation out of a tensor unit is an isomorphism.**  If `A` is a unit for `T` in its
second variable, with unitor `u`, then `hom(A, B) ⟶ B`, the unitor followed by the evaluation,
is invertible; so `hom(A, -)` is the identity functor up to isomorphism. -/
theorem isIso_unitEvaluation (hnat : TensorHomEquivNaturalLeft H T e) (A : D)
    (u : ∀ W : D, T.obj (W, A) ≅ W)
    (hu : ∀ (W W' : D) (g : W ⟶ W'),
      T.map (g ×ₘ 𝟙 A) ≫ (u W').hom = (u W).hom ≫ g)
    (B : D) :
    IsIso ((u ((H.obj (op A)).obj B)).inv ≫ evaluation H T e A B) := by
  refine isIso_of_yoneda_map_bijective _ fun C => ?_
  have key : ∀ x : C ⟶ (H.obj (op A)).obj B,
      x ≫ (u ((H.obj (op A)).obj B)).inv ≫ evaluation H T e A B =
        (u C).inv ≫ e C A B x := by
    intro x
    rw [← Category.assoc, ← unitor_inv_comp_map_prod T u hu x, Category.assoc,
      map_prod_comp_evaluation H T e hnat x]
  have hfun : (fun x : C ⟶ (H.obj (op A)).obj B =>
      x ≫ (u ((H.obj (op A)).obj B)).inv ≫ evaluation H T e A B) =
      fun x => (u C).inv ≫ e C A B x := funext key
  rw [hfun]
  have hb : Function.Bijective (fun y : T.obj (C, A) ⟶ B => (u C).inv ≫ y) := by
    refine ⟨fun y y' hyy => ?_, fun z => ⟨(u C).hom ≫ z, ?_⟩⟩
    · simpa using congrArg (fun t : C ⟶ B => (u C).hom ≫ t) hyy
    · simp
  exact hb.comp (e C A B).bijective

end OneCategory

/-! ### The hom-comparison at a tensor unit -/

section TwoCategories

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- **The hom-comparison of a functor with internal hom is invertible at a tensor unit.**  If
`A` is a unit for `T₁` in its second variable and `P A` is a unit for `T₂`, with unitors `u₁`
and `u₂` compatible with the monoidality comparison `m`, then `P(hom(A, B)) ⟶ hom(P A, P B)` is
an isomorphism for every `B`: both sides are identified with `P B` by the evaluation out of a
unit, and the comparison is the image of one identification followed by the inverse of the
other. -/
theorem isIso_homComparison_of_tensorUnit
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A : D₁)
    (u₁ : ∀ W : D₁, T₁.obj (W, A) ≅ W)
    (u₂ : ∀ W : D₂, T₂.obj (W, P.obj A) ≅ W)
    (hu₁ : ∀ (W W' : D₁) (g : W ⟶ W'),
      T₁.map (g ×ₘ 𝟙 A) ≫ (u₁ W').hom = (u₁ W).hom ≫ g)
    (hu₂ : ∀ (W W' : D₂) (g : W ⟶ W'),
      T₂.map (g ×ₘ 𝟙 (P.obj A)) ≫ (u₂ W').hom = (u₂ W).hom ≫ g)
    (hcoh : ∀ W : D₁, m.hom.app (W, A) ≫ (u₂ (P.obj W)).hom = P.map (u₁ W).hom)
    (B : D₁) :
    IsIso (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) := by
  have h₁ := isIso_unitEvaluation H₁ T₁ e₁ hnat₁ A u₁ hu₁ B
  have h₂ := isIso_unitEvaluation H₂ T₂ e₂ hnat₂ (P.obj A) u₂ hu₂ (P.obj B)
  have hstep1 : (u₂ (P.obj ((H₁.obj (op A)).obj B))).inv ≫
        T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) =
      homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫
        (u₂ ((H₂.obj (op (P.obj A))).obj (P.obj B))).inv := by
    exact unitor_inv_comp_map_prod T₂ u₂ hu₂ _
  have hstep2 : T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) ≫
        evaluation H₂ T₂ e₂ (P.obj A) (P.obj B) =
      homComparisonDatum P H₁ T₁ T₂ e₁ m A B := by
    rw [map_prod_comp_evaluation H₂ T₂ e₂ hnat₂]
    exact homComparison_adjoint P H₁ H₂ T₁ T₂ e₁ e₂ m A B
  have hstep3 : (u₂ (P.obj ((H₁.obj (op A)).obj B))).inv ≫
      m.inv.app ((H₁.obj (op A)).obj B, A) = P.map (u₁ ((H₁.obj (op A)).obj B)).inv := by
    have hone : P.map (u₁ ((H₁.obj (op A)).obj B)).hom ≫
        (u₂ (P.obj ((H₁.obj (op A)).obj B))).inv ≫
          m.inv.app ((H₁.obj (op A)).obj B, A) = 𝟙 _ := by
      rw [← hcoh ((H₁.obj (op A)).obj B)]
      simp
    have htwo : P.map (u₁ ((H₁.obj (op A)).obj B)).hom ≫
        P.map (u₁ ((H₁.obj (op A)).obj B)).inv = 𝟙 _ := by
      rw [← P.map_comp, Iso.hom_inv_id, P.map_id]
    exact (cancel_epi (P.map (u₁ ((H₁.obj (op A)).obj B)).hom)).1 (hone.trans htwo.symm)
  have hdatum : homComparisonDatum P H₁ T₁ T₂ e₁ m A B =
      m.inv.app ((H₁.obj (op A)).obj B, A) ≫ P.map (evaluation H₁ T₁ e₁ A B) := rfl
  have hkey : homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫
        ((u₂ ((H₂.obj (op (P.obj A))).obj (P.obj B))).inv ≫
          evaluation H₂ T₂ e₂ (P.obj A) (P.obj B)) =
      P.map ((u₁ ((H₁.obj (op A)).obj B)).inv ≫ evaluation H₁ T₁ e₁ A B) := by
    rw [← Category.assoc, ← hstep1, Category.assoc, hstep2, hdatum, P.map_comp, ← hstep3,
      Category.assoc]
  have heq : homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B =
      P.map ((u₁ ((H₁.obj (op A)).obj B)).inv ≫ evaluation H₁ T₁ e₁ A B) ≫
        inv ((u₂ ((H₂.obj (op (P.obj A))).obj (P.obj B))).inv ≫
          evaluation H₂ T₂ e₂ (P.obj A) (P.obj B)) := by
    rw [← hkey, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

end TwoCategories

end Transpose

/-! ### Tag 08J8 in its source variable, at a ringed space -/

section SourceNaturality

variable (Z : RingedSpace.{u, u})

/-- **Tag 08J8 in its source variable, read on a ringed space at the uncurried spelling of the
derived tensor product.**  Precomposing `ψ : A' ⟶ R𝓗om(B, C)` with `φ : A ⟶ A'` corresponds,
under the bijection of Tag 08DI, to precomposing the transpose of `ψ` with `φ ⊗ 1`.

This is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` at
`Stacks.SheafOfModules.ringedSite Z.sheaf`, with the curried spelling of the derived tensor
product traded for the uncurried one by `CategoryTheory.uncurry_map_mkHom_id` and the additive
equivalence read as a bijection by `AddEquiv.coe_toEquiv`.  The internal hom is named
`RingedSite.derivedSheafHomBifunctor` of that same site, the name the bijection declares its own
domain at, rather than `Stacks.SheafOfModules.derivedSheafHom Z.sheaf`, which is an `abbrev` for
it; `tensorHomEquivNaturalLeft_ringedSpace` below is stated at that one name throughout, and
records why.

*Why the proof is a term and not a tactic script.*  Every step is applied at its arguments:
a `rw` or a `simp only` with any of these three lemmas has to match a pattern against terms of
this size, and each of those exceeds either `maxRecDepth` or the heartbeat
budget.  The same discipline is recorded in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality`. -/
theorem derivedCurryHomEquiv_naturality_source_uncurried
    (A A' B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    (φ : A ⟶ A')
    (ψ : A' ⟶ ((RingedSite.derivedSheafHomBifunctor
      (Stacks.SheafOfModules.ringedSite Z.sheaf)).obj (op B)).obj C) :
    (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv (φ ≫ ψ) =
      (internalHomTensorUncurried Z).map (φ ×ₘ 𝟙 B) ≫
        (RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A' B C).toEquiv ψ :=
  (congrFun (AddEquiv.coe_toEquiv (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C)) (φ ≫ ψ)).trans
    ((RingedSite.derivedCurryHomEquiv_naturality_source
          (Stacks.SheafOfModules.ringedSite Z.sheaf) φ ψ).trans
      ((congrArg (· ≫ RingedSite.derivedCurryHomEquiv
              (Stacks.SheafOfModules.ringedSite Z.sheaf) A' B C ψ)
          (CategoryTheory.uncurry_map_mkHom_id (internalHomTensorProduct Z).tensor φ B).symm).trans
        (congrArg ((internalHomTensorUncurried Z).map (φ ×ₘ 𝟙 B) ≫ ·)
          (congrFun (AddEquiv.coe_toEquiv (RingedSite.derivedCurryHomEquiv
            (Stacks.SheafOfModules.ringedSite Z.sheaf) A' B C)) ψ).symm)))

/-- **The bijection of Tag 08DI on a ringed space is natural in its source variable.**  This is
`Transpose.TensorHomEquivNaturalLeft` for the bijection of Tag 08DI, so it is the hypothesis
that the invertibility statement below no longer has to carry.

The bijection is presented as the site-level `RingedSite.derivedCurryHomEquiv` of
`Stacks.SheafOfModules.ringedSite Z.sheaf` rather than as
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf`, which is the same family of
additive equivalences — the latter is *defined* as the former, and the two are equal by `rfl`
as families.  Under an applied coercion they are not interchangeable within the elaborator's
budget: `⇑(derivedSheafHomTensorEquiv Z.sheaf A B C) x = ⇑(derivedCurryHomEquiv _ A B C) x`
by `rfl` exceeds `maxRecDepth`, while the unapplied equation of the two families
costs nothing.  So the family is written at the spelling Tag 08J8 is proved at, and the
identification with Tag 08DI is left where it is free.

*The internal hom is written at the site's own name.*  The predicate's internal hom is
`RingedSite.derivedSheafHomBifunctor (ringedSite Z.sheaf)`, not the ringed-space
`Stacks.SheafOfModules.derivedSheafHom Z.sheaf`.  That is the same bifunctor and so the same
statement — the space-level name is an `abbrev` for the site-level one at
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedInternalHom.lean:91-95` — but it is
the name the bijection above already declares its own domain at, and writing it here is what
makes the `convert` below close.

*The ambient category is pinned by hand*, at the naming the derived pullback uses, which is the
same category by `rfl`: `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z` is an
`abbrev` for `SheafOfModules (Tensor.ringSheaf Z.sheaf)`.  The pin is kept because every
consumer of this predicate — `isIso_derivedPullbackSheafHomMap_of_tensorUnit` below, and the
composition and restriction lemmas of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality` — reads
the category off `derivedPullbackFunctor` and so asks for it at that naming; dropping the pin
would move the reconciliation into each of them instead of settling it once here.

*Why the proof is a `convert` and not an `exact`, and why it needs no reducibility attribute.*
The one difference left between this predicate and
`derivedCurryHomEquiv_naturality_source_uncurried` is the curried-versus-uncurried spelling of
the derived tensor product, which sits in the `FunLike` instance argument of the bijection's
coercion.  Handing the helper straight back closes nothing: `exact`, the plain term
`fun A A' B C φ ψ => …`, `beta_reduce` before the `exact`, a `show` of the beta-reduced goal,
and `convert … using 1` followed by `Iff.rfl` or `rfl` each reach
`maxRecDepth`.  What does work is to never ask for the whole equation at once: `convert … using
1` stops at the `Iff` of the two equations and settles the coercion's instance arguments one at
a time.  That congruence runs at `.instances` transparency, where
`Stacks.SheafOfModules.Tensor.ringSheaf` — an ordinary definition — does not unfold; giving it
`attribute [local instance_reducible]` so that it would is a spelling bridge by attribute, which
is avoided.  With the internal hom written at the site's
own name the instance arguments agree syntactically instead, and the residual closes with no
attribute.  `convert … using 2` leaves the same `Iff` as `using 1`; ascribing the helper's
result type, or its whole equivalence, to the uncurried spelling makes the helper elaborate but
does not make it apply. -/
@[sga "4½ Etat_0 6.2" "partial"]
theorem tensorHomEquivNaturalLeft_ringedSpace :
    Transpose.TensorHomEquivNaturalLeft
      (D := DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
      (RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite Z.sheaf))
      (internalHomTensorUncurried Z)
      (fun A B C => (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv) := by
  intro A A' B C φ ψ
  refine Eq.trans ?_ (derivedCurryHomEquiv_naturality_source_uncurried Z A A' B C φ ψ)
  congr 1

end SourceNaturality

/-! ### Tag 0GM7 at a tensor unit -/

section RingedSpaces

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **Tag 0GM7 at a tensor unit.**  Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed
spaces and let `K ∈ D(𝒪_Y)` be a unit for the derived tensor product on `Y` whose derived
pullback is a unit on `X`, compatibly with the monoidality comparison of Tag 079U.  Then the
canonical map

`Lh^*R𝓗om_{𝒪_Y}(K, M) ⟶ R𝓗om_{𝒪_X}(Lh^*K, Lh^*M)`

of Tag 08I3 is an isomorphism for every `M ∈ D(𝒪_Y)`.  This is the case `K = 𝒪_Y[0]`, which is
both perfect and pseudo-coherent, so it is the common base instance of the three clauses of the
source, and it needs neither flatness of `h`, nor finite tor dimension, nor any bound on `M`.

The two unitors, their naturality and the unitor coherence of the comparison of Tag 079U are
carried as explicit hypotheses; the naturality of the bijection of Tag 08DI in its source
variable, which used to be carried too, is now discharged from Tag 08J8 by
`tensorHomEquivNaturalLeft_ringedSpace`.  See the implementation notes of this file.

All five of the hypotheses that remain are supplied at `K = 𝒪_Y[0]` by
`Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_singleUnit` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackUnit`, which is
therefore Tag 0GM7 at the structure sheaf with no hypothesis.  They are kept here because `uY`
and `uX` are data: this statement is the one that holds at *any* `K` carrying a unit structure,
and it fixes no particular unitor and no particular unit comparison. -/
theorem isIso_derivedPullbackSheafHomMap_of_tensorUnit
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (uY : ∀ W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y),
      (internalHomTensorUncurried Y).obj (W, K) ≅ W)
    (uX : ∀ W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X),
      (internalHomTensorUncurried X).obj (W, (derivedPullbackFunctor h).obj K) ≅ W)
    (huY : ∀ (W W' : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (g : W ⟶ W'),
      (internalHomTensorUncurried Y).map (g ×ₘ 𝟙 K) ≫ (uY W').hom = (uY W).hom ≫ g)
    (huX : ∀ (W W' : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) (g : W ⟶ W'),
      (internalHomTensorUncurried X).map
          (g ×ₘ 𝟙 ((derivedPullbackFunctor h).obj K)) ≫ (uX W').hom = (uX W).hom ≫ g)
    (hcoh : ∀ W : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y),
      (pullbackTensorIso h).hom.app (W, K) ≫
          (uX ((derivedPullbackFunctor h).obj W)).hom =
        (derivedPullbackFunctor h).map (uY W).hom)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso (derivedPullbackSheafHomMap h K M) :=
  Transpose.isIso_homComparison_of_tensorUnit (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
    (internalHomTensorUncurried X)
    (fun A B C => (RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite Y.sheaf) A B C).toEquiv)
    (fun A B C => (RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X.sheaf) A B C).toEquiv)
    (pullbackTensorIso h) (tensorHomEquivNaturalLeft_ringedSpace Y)
    (tensorHomEquivNaturalLeft_ringedSpace X) K uY uX huY huX hcoh M

end RingedSpaces

end Stacks.Cohomology.DerivedInternalHomPullback

end
