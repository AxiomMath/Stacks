module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ActionGroupoid
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.Sites.Stackification.Stackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.GroupoidStackification
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import Mathlib.CategoryTheory.Category.ULift

/-!
# The quotient stack `[X/G]` of Section 97.13

Let `d ≥ 1`. Criteria for Representability, Section 97.13 (**Stacks 05YL**) builds two objects:
the affine scheme `X` of free `d`-dimensional algebra structures, whose points over a scheme `T`
are the free `d`-dimensional algebras over `Γ(T, 𝒪_T)` (**Stacks 05YM**,
`AlgebraicGeometry.FiniteFreeAlgebra.representation`), and the group `G` of invertible matrices
fixing the first basis vector (`AlgebraicGeometry.FiniteFreeAlgebra.unitFixingSubgroup`), acting
on `X` by `a(g, m) = g⁻¹ ∘ m ∘ (g ⊗ g)`. The section's `[X/G]` is the quotient stack of that
action.

This file constructs `[X/G]` over the big fppf site of a base scheme `S`, and proves that it is
a stack in groupoids there. The construction is the one the source's own proof of **Stacks 05YQ**
names: `[X/G]` "is the stackification of the presheaf in groupoids `(X(T), G(T) × X(T), s, t, c)`"
attached to the action. That presheaf in groupoids is **Stacks 05YP**,
`AlgebraicGeometry.FiniteFreeAlgebra.ActionGroupoidPresheaf`, and the stackification is the
three-stage construction of Stacks 02ZN that
`AlgebraicGeometry.Stack.quotientStack` — part (1) of Stacks 044Q — uses for the quotient stack of
a groupoid in algebraic spaces. So nothing of the quotient is rebuilt here: what is new is only
that the action groupoid of Section 97.13 is transported to the big fppf site *over* `S`, where
`ℋ_d` lives, and that the stackification is taken there.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.actionGroupoidOver`: the action-groupoid presheaf of
  Stacks 05YP, read on the big fppf site over `S`.
* `AlgebraicGeometry.FiniteFreeAlgebra.freeAlgebraQuotientPrestack`: its pointwise groupoid
  fibration, with morphisms raised to the universe the stackification construction needs.
* `AlgebraicGeometry.FiniteFreeAlgebra.freeAlgebraQuotientStack`: **the quotient stack `[X/G]`
  of Stacks 05YL**, as a category over the big fppf site over `S`.
* `AlgebraicGeometry.FiniteFreeAlgebra.toFreeAlgebraQuotientStack`: the canonical 1-morphism
  from the presentation to the quotient.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.isStack_freeAlgebraQuotientStack`,
  `AlgebraicGeometry.FiniteFreeAlgebra.isFiberedInGroupoids_freeAlgebraQuotientStack` and
  `AlgebraicGeometry.FiniteFreeAlgebra.isStackInGroupoids_freeAlgebraQuotientStack`: `[X/G]` is a
  stack, is fibred in groupoids, and is therefore a stack in groupoids over the big fppf site
  over `S`, so the structure functor really is the morphism `[X/G] ⟶ (Sch/S)_{fppf}` the source
  names.
* `AlgebraicGeometry.FiniteFreeAlgebra.isLocallyBijective_toFreeAlgebraQuotientStack` and
  `AlgebraicGeometry.FiniteFreeAlgebra.essImage_toFreeAlgebraQuotientStack`: the two clauses of
  Stacks 02ZN exhibiting `[X/G]` as the stackification of the presentation.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_presheafOver_iso_actionGroupoidOver`: **`[X/G]` is
  the stackification of `FA_d`.** The presheaf in groupoids `FA_d` of Stacks 05YN, read over `S`,
  is isomorphic to the presentation of `[X/G]`. This is Stacks 05YP transported to the localized
  site, and it is the first of the two reductions the source's proof of Stacks 05YQ makes.

## What is *not* here

Stacks 05YQ itself — the equivalence `ℋ_d ≃ [X/G]` — is **not** proved here, and nothing below
should be read as proving it. What this file supplies is the right-hand object of that
equivalence, together with the identification of its presentation with `FA_d`. Given those, the
source's proof of 05YQ reduces to showing that `ℋ_d` is the stackification of `FA_d`, which needs
two further things that the library does not yet have: the relative-spectrum 1-morphism
`FA_d ⟶ ℋ_d` over the site, sending a structure `m` over `T` to `Spec_T` of its algebra; and the
globalization of the two clauses of Stacks 8.9.1 from an affine base to an arbitrary one. Those
clauses are proved over an affine base —
`AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivSpecIso` for clause (a) and the
local-unit-basis results of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/FiniteFreeAlgebra/LocalUnitBasis.lean` for clause
(b) — and `AlgebraicGeometry.Stack.isAlgebraicStack_finiteCoverFibered` proves the "In particular"
consequence of 05YQ by a different route, the presentation of Stacks 026O by the scheme of
structure constants.

## Implementation notes

The action groupoid of Stacks 05YP is stated over `B.Schemes`, the schemes of the ambient big
fppf site, because the action of `G` on `X` is defined over `Spec ℤ` and knows nothing of a base.
`ℋ_d` is a category over `BigFppfOver B S hS`, the schemes *over* `S`. The two are joined by
`AlgebraicGeometry.BigFppfOver.forget`, and `actionGroupoidOver` is the restriction of the action
groupoid along it. This is a restriction of presheaves only; the groupoids themselves, their
objects `X(T)` and their arrows `G(T) × X(T)`, are untouched.

Everything is stated at a **variable** `P : ActionGroupoidPresheaf B d laws` rather than at the
action groupoid of Stacks 05YP itself. Two reasons, and both are binding. First, Stacks 05YP is
formalized in the form of an existential over `laws` and `P`
(`AlgebraicGeometry.FiniteFreeAlgebra.presheaf_actionGroupoid`) and the witness it uses is
private to its file, so a concrete spelling is not available to name. Second, the concrete
witness is built from `AlgebraicGeometry.FiniteFreeAlgebra.representation`, a large
tactic-generated term, and the construction below compares functors whose arrow types mention it;
at a variable `P` that term cannot be reduced at all, which is what keeps the kernel's budget
intact. This is the same reason `ActionGroupoid.lean` conducts its own arguments at a variable
`rep`.

The stackification is `CategoryTheory.Functor.stageThreeProj`, whose input must have objects and
morphisms in one universe; the pointwise groupoid fibration has objects in `Type (u + 1)` and
morphisms in `Type u`, so the morphisms are raised by `CategoryTheory.ULiftHom` first, exactly as
in `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStack.lean`. The lift commutes
*strictly* with the projection to the site, so neither the base category nor the fppf topology
changes.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 05YL](https://stacks.math.columbia.edu/tag/05YL)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YN](https://stacks.math.columbia.edu/tag/05YN)
* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {d : ℕ} [NeZero d] {laws : ConjugationPreservesAlgebraLaws.{u} d}

/-- The action-groupoid presheaf `T ↦ (X(T), G(T) × X(T))` of **Stacks 05YP**, read on the big
fppf site over `S` by restriction along `AlgebraicGeometry.BigFppfOver.forget`. The groupoids are
unchanged: over a scheme `T` over `S` the objects are still the points `T ⟶ X` and the arrows
still the unit-fixing matrices carrying one to another. -/
noncomputable abbrev actionGroupoidOver (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) : (BigFppfOver B S hS)ᵒᵖ ⥤ Grpd.{u, u} :=
  (BigFppfOver.forget B S hS).op ⋙ P.toFunctor

/-- The pointwise groupoid fibration presenting `[X/G]`, with its morphisms lifted to the
universe needed by stackification. Its base remains the big fppf site over `S`. -/
noncomputable abbrev freeAlgebraQuotientPrestack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    ((ULiftHom.down : ULiftHom.{u + 1} (presheafOfGroupoids (actionGroupoidOver S hS P)).obj ⥤
      (presheafOfGroupoids (actionGroupoidOver S hS P)).obj) ⋙
      (presheafOfGroupoids (actionGroupoidOver S hS P)).p)

/-- The presentation of `[X/G]` is fibred in groupoids. -/
theorem isFiberedInGroupoids_freeAlgebraQuotientPrestack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    (freeAlgebraQuotientPrestack S hS P).p.IsFiberedInGroupoids :=
  Stack.isFiberedInGroupoids_uliftHom _ (isFiberedInGroupoids_presheafOfGroupoids _)

/-- The presentation of `[X/G]` is a fibred category. -/
instance isFibered_freeAlgebraQuotientPrestack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    (freeAlgebraQuotientPrestack S hS P).p.IsFibered :=
  (isFiberedInGroupoids_freeAlgebraQuotientPrestack S hS P).isFibered

/-- **The quotient stack `[X/G]` of Criteria for Representability, Section 97.13 (Stacks
05YL)**, as a category over the big fppf site over `S`: the stackification of the pointwise
groupoid fibration of the action groupoid of `G` on the scheme `X` of free `d`-dimensional
algebra structures.

This is the object the source's proof of Stacks 05YQ names when it says that `[X/G]` "is the
stackification of the presheaf in groupoids `(X(T), G(T) × X(T), s, t, c)`", and the
stackification is the same three-stage construction of Stacks 02ZN that
`AlgebraicGeometry.Stack.quotientStack`, part (1) of Stacks 044Q, uses. -/
noncomputable def freeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    ((freeAlgebraQuotientPrestack S hS P).p.stageThreeProj (BigFppfOver.topology B S hS))

/-- `[X/G]` is a fibred category. -/
instance isFibered_freeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    (freeAlgebraQuotientStack S hS P).p.IsFibered :=
  Functor.isFibered_stageThreeProj _ _

/-- The canonical 1-morphism from the presentation of `[X/G]` to `[X/G]`. -/
noncomputable def toFreeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    (freeAlgebraQuotientPrestack S hS P).obj ⥤ (freeAlgebraQuotientStack S hS P).obj :=
  (freeAlgebraQuotientPrestack S hS P).p.toStageThree (BigFppfOver.topology B S hS)

/-- The canonical map to `[X/G]` is a 1-morphism over the big fppf site over `S`. -/
theorem isFibredOneMorphism_toFreeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    (freeAlgebraQuotientPrestack S hS P).p.IsFibredOneMorphism
      (freeAlgebraQuotientStack S hS P).p (toFreeAlgebraQuotientStack S hS P) :=
  Functor.isFibredOneMorphism_toStageThree _ _

/-- **`[X/G]` satisfies descent for the fppf topology over `S`.** -/
theorem isStack_freeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    (freeAlgebraQuotientStack S hS P).p.IsStack (BigFppfOver.topology B S hS) :=
  Functor.isStack_stageThreeProj.{u, u, u + 1, u + 1} _ _

/-- `[X/G]` sheafifies the morphism presheaves of its presentation: clause (1) of Stacks 02ZN
for this witness. -/
theorem isLocallyBijective_toFreeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws)
    (U : BigFppfOver B S hS) (x y : (freeAlgebraQuotientPrestack S hS P).p.Fiber U) :
    Presheaf.IsLocallyInjective ((BigFppfOver.topology B S hS).over U)
        ((isFibredOneMorphism_toFreeAlgebraQuotientStack S hS P).morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over U)
        ((isFibredOneMorphism_toFreeAlgebraQuotientStack S hS P).morPresheafMap x y) :=
  Functor.isLocallyBijective_morPresheafMap_toStageThree.{u, u, u + 1, u + 1} _ _ U x y

/-- Every object of `[X/G]` over `T` is, locally on `T` for the fppf topology, the image of a
`T`-point of `X`: clause (2) of Stacks 02ZN for this witness. -/
theorem essImage_toFreeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws)
    (U : BigFppfOver B S hS) (x : (freeAlgebraQuotientStack S hS P).p.Fiber U) :
    ∃ R ∈ BigFppfOver.topology B S hS U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_toFreeAlgebraQuotientStack S hS P).comp_eq V).essImage
          (Functor.pullbackFiber (freeAlgebraQuotientStack S hS P).p x f) :=
  Functor.essImage_pullbackFiber_toStageThree.{u, u, u + 1, u + 1} _ _ U x

/-- **`[X/G]` is fibred in groupoids.** -/
theorem isFiberedInGroupoids_freeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    (freeAlgebraQuotientStack S hS P).p.IsFiberedInGroupoids :=
  Functor.Stackification.isFiberedInGroupoids_of_isStackification
    (isFiberedInGroupoids_freeAlgebraQuotientPrestack S hS P)
    (isStack_freeAlgebraQuotientStack S hS P)
    (isFibredOneMorphism_toFreeAlgebraQuotientStack S hS P)
    (isLocallyBijective_toFreeAlgebraQuotientStack S hS P)
    (essImage_toFreeAlgebraQuotientStack S hS P)

/-- **`[X/G]` is a stack in groupoids over the big fppf site over `S`**, in the sense of Stacks
02ZI: the structure functor really is the morphism `[X/G] ⟶ (Sch/S)_{fppf}` that Section 97.13
names. -/
theorem isStackInGroupoids_freeAlgebraQuotientStack (S : Scheme.{u}) (hS : B.Contains S)
    (P : ActionGroupoidPresheaf B d laws) :
    Functor.IsStackInGroupoids (freeAlgebraQuotientStack S hS P).p
      (BigFppfOver.topology B S hS) :=
  (isStack_freeAlgebraQuotientStack S hS P).isStackInGroupoids
    (isFiberedInGroupoids_freeAlgebraQuotientStack S hS P)

/-- **`[X/G]` is the stackification of `FA_d`.** The presheaf in groupoids `FA_d` of Stacks 05YN,
read on the big fppf site over `S`, is isomorphic to the presentation of `[X/G]` there — so the
stackification of `FA_d` over `S` is `[X/G]`.

This is **Stacks 05YP** transported along `AlgebraicGeometry.BigFppfOver.forget`, and it is the
first of the two reductions the source's proof of Stacks 05YQ makes: that proof identifies
`[X/G]` with the stackification of `FA_d` and is then left with showing that `ℋ_d` is the
stackification of `FA_d` too. The remaining conjuncts are the ones Stacks 05YP carries, read over
`S`: the isomorphism is the representing identification of Stacks 05YM on objects, and inverse
matrices on arrows, which is what the forward-algebra-map convention of Stacks 05YN forces. -/
theorem exists_presheafOver_iso_actionGroupoidOver (S : Scheme.{u}) (hS : B.Contains S)
    (F : Presheaf B d) :
    ∃ (laws : ConjugationPreservesAlgebraLaws.{u} d)
      (P : ActionGroupoidPresheaf B d laws)
      (η : (BigFppfOver.forget B S hS).op ⋙ F.functor ≅ actionGroupoidOver S hS P),
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : ((BigFppfOver.forget B S hS).op ⋙ F.functor).obj T),
        (η.hom.app T).obj x =
          ((representation.{u} d).equiv ((BigFppfOver.toScheme B S hS).obj T.unop)).symm
            (F.objectEquiv ((BigFppfOver.forget B S hS).op.obj T) x)) ∧
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ)
        (x y : ((BigFppfOver.forget B S hS).op ⋙ F.functor).obj T) (e : x ⟶ y),
        (P.arrowEquiv ((BigFppfOver.forget B S hS).op.obj T) _ _ ((η.hom.app T).map e)).1.1 =
          (F.arrowEquiv ((BigFppfOver.forget B S hS).op.obj T) x y e).matrix⁻¹) := by
  obtain ⟨laws, P, η, hobj, harrow⟩ := presheaf_actionGroupoid B d F
  exact ⟨laws, P, Functor.isoWhiskerLeft (BigFppfOver.forget B S hS).op η,
    fun T x => hobj _ x, fun T x y e => harrow _ x y e⟩

end AlgebraicGeometry.FiniteFreeAlgebra

end
