module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangePasting

/-!
# The pasting law for the derived base change map, with its six categories named

`Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app`
(`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianDerivedBaseChangePasting.lean`)
is the pasting law for the derived base change map, evaluated at an object.  Its six categories
are implicit there.  This file restates it with them explicit and their `Category`, `Abelian`
and `EnoughInjectives` structures named, so that a concrete application can pin them.

## Main results

* `Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app_named`: the pasting law with its six
  categories and their structures named.  It is `derived_eq_derivedPaste_app` applied once.

## Implementation notes

*What makes the hypothesis `hτ` cross at a concrete seating.*  The seating
is the `𝒪`-modules of the small étale ringed topoi of six algebraic spaces, where the degree-zero
law `hτ` asks for is proved as
`AlgebraicGeometry.Space.toposModuleBaseChangeMap_horizontal`, and the application is proved as
`AlgebraicGeometry.Space.toposModuleDerivedBaseChange_horizontal`.  It is recorded here because
`derived_eq_derivedPaste_app_named` exists for this application, and because the obvious
diagnosis is the wrong one.

The one thing that matters is which term the six *categories* are, and that is settled by the
three direct images supplied, not by pinning.  A bare
`Stacks.Sheaves.RingedToposModules.pushforwardModules` of a morphism of small étale ringed topoi
is typed at `SheafOfModules (structureRingSheaf (smallEtaleRingedTopos …))`, while every inverse
image at that seating is typed at `AlgebraicGeometry.Space.Modules`.  The two are one category by
definition and not one term, so with a bare direct image supplied the engine seats the whole law
— `hτ` included — in the ringed-topoi vocabulary, and comparing that `hτ` against the
degree-zero law is a `(deterministic) timeout at whnf`, even at `maxHeartbeats 4000000`.  The cure is a direct image whose *declared type* is
already at `Modules` — `AlgebraicGeometry.Space.toposModulePushforward` — supplied here and used
in the degree-zero law, in the square comparison and in the adjunction of **Stacks 03D7** it is
proved from.  Then every category position on the two sides is the same term, and `hτ` is
accepted with nothing pinned at all, and the whole application elaborates quickly.

Three observations locate the cause:

* It is **not** an instance problem and the `Additive`/`Preserves` binders cannot be the cause.
  `hτ` mentions no `Abelian`, no `Additive`, no `Preserves` and no derived category, and a
  short example containing none of them reproduces the identical timeout.
* Pinning the six `Category` arguments *does* work, but only with the right term.  With
  `(instA₀ := @SheafOfModules.instCategory _ _ _ _)` and the five others, the bare direct images
  still supplied, `hτ` is accepted.  With `(instA₀ := inferInstance)` it is
  not:  `inferInstance` is a reducible wrapper, so the stored argument is
  `@inferInstance (Category.{u+1} (Modules …)) …` where the law carries
  `@SheafOfModules.instCategory … (RingedSite.ringSheaf (smallEtaleRingedSite …))`, and a
  `pp.explicit` token diff of the two propositions diverges at exactly that argument.
* So the degree-zero law is not in a non-uniform seating.
  Its `Category` arguments are the canonical `Modules` ones throughout;  what matters
  is the *direct image*, whose two occurrences it wrote as bare `pushforwardModules` inside
  `@CategoryTheory.Functor.obj` and `@CategoryTheory.Functor.map` with the categories supplied
  positionally.  Naming the direct image removes both of those annotations as well.

What the `pp.explicit` diff is useful for, and what it is not:  with the pretty printer's default
elision the two propositions print at about 9,000 tokens each and the *first divergence* is the
whole answer, found in one pass.  Counting occurrences of `smallEtaleRingedTopos` and
`structureRingSheaf` is not — those counts agreed (8 against 8, none against none) in a
configuration that still timed out, because the divergence was a wrapper around an instance and
not a spelling of a ring sheaf.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

universe vA₀ vA₁ vA₂ vB₀ vB₁ vB₂ uA₀ uA₁ uA₂ uB₀ uB₁ uB₂

/-- **`Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app` with its six categories and
their structures supplied by name.**  The content is that theorem, applied once;  nothing is added
and nothing is assumed beyond what it assumes.

What the restatement is for is that a concrete instance of the law can be *stated*.  In
`derived_eq_derivedPaste_app` the six categories are implicit arguments, so they are not written
at an application:  they are solved from the type of the first direct image supplied, and
whatever *that* functor happens to be typed at becomes the seating of the whole law, including of
the hypothesis `hτ`.  At a concrete seating that is the wrong category — the same category by
definition, but a different term — and the comparison of `hτ` against a degree-zero law
does not finish.  Here the six categories are explicit and each of their three structures is a
*named* instance argument, so a caller may pin any of them positionally or with
`(instA₀ := …)`, `(abA₀ := …)`.  Two of those are not optional at the intended seating:
`Abelian` is not reachable by instance search there and has to be passed as a term, and the
`Category` arguments have to be pinned for the same reason the categories do — see the
implementation notes of this file, which record what pinning them buys and what it
does not. -/
theorem derived_eq_derivedPaste_app_named
    (A₀ : Type uA₀) (A₁ : Type uA₁) (A₂ : Type uA₂)
    (B₀ : Type uB₀) (B₁ : Type uB₁) (B₂ : Type uB₂)
    [instA₀ : Category.{vA₀} A₀] [instA₁ : Category.{vA₁} A₁] [instA₂ : Category.{vA₂} A₂]
    [instB₀ : Category.{vB₀} B₀] [instB₁ : Category.{vB₁} B₁] [instB₂ : Category.{vB₂} B₂]
    [abA₀ : Abelian A₀] [abA₁ : Abelian A₁] [abA₂ : Abelian A₂]
    [abB₀ : Abelian B₀] [abB₁ : Abelian B₁] [abB₂ : Abelian B₂]
    [eiA₀ : EnoughInjectives A₀] [eiA₁ : EnoughInjectives A₁] [eiA₂ : EnoughInjectives A₂]
    [eiB₀ : EnoughInjectives B₀] [eiB₁ : EnoughInjectives B₁]
    (P₀ : A₀ ⥤ B₀) (P₁ : A₁ ⥤ B₁) (P₂ : A₂ ⥤ B₂)
    (U₁ : B₀ ⥤ B₁) (U₂ : B₁ ⥤ B₂) (U : B₀ ⥤ B₂)
    (V₁ : A₀ ⥤ A₁) (V₂ : A₁ ⥤ A₂) (V : A₀ ⥤ A₂)
    [P₀.Additive] [P₁.Additive] [P₂.Additive]
    [U₁.Additive] [U₂.Additive] [U.Additive]
    [V₁.Additive] [V₂.Additive] [V.Additive]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V₂] [PreservesFiniteColimits V₂]
    (cU : U₁ ⋙ U₂ ≅ U) (cV : V₁ ⋙ V₂ ≅ V)
    (τ : P₀ ⋙ U ⟶ V ⋙ P₂) (τ₁ : P₀ ⋙ U₁ ⟶ V₁ ⋙ P₁) (τ₂ : P₁ ⋙ U₂ ⟶ V₂ ⋙ P₂)
    (hτ : ∀ X, τ.app X = cU.inv.app (P₀.obj X) ≫ U₂.map (τ₁.app X) ≫
      τ₂.app (V₁.obj X) ≫ P₂.map (cV.hom.app X))
    (M : DerivedCategory.Plus A₀) :
    (derived P₀ P₂ U V τ (asIso U.rightDerivedFunctorPlusUnith)).app M =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U cU).inv.app
          (P₀.rightDerivedFunctorPlus.obj M) ≫
        U₂.rightDerivedFunctorPlus.map
            ((derived P₀ P₁ U₁ V₁ τ₁ (asIso U₁.rightDerivedFunctorPlusUnith)).app M) ≫
          (derived P₁ P₂ U₂ V₂ τ₂ (asIso U₂.rightDerivedFunctorPlusUnith)).app
              (V₁.rightDerivedFunctorPlus.obj M) ≫
            P₂.rightDerivedFunctorPlus.map
              ((Functor.rightDerivedFunctorPlusCompIsoOfExact V₁ V₂ V cV).hom.app M) :=
  derived_eq_derivedPaste_app P₀ P₁ P₂ U₁ U₂ U V₁ V₂ V cU cV τ τ₁ τ₂ hτ M

end Stacks.Cohomology.BaseChange

end
