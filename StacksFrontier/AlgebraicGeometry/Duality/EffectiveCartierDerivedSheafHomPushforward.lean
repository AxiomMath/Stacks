module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTraceSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative

/-!
# The comparison morphism of Tag 0B4B after pushforward

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`.
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDerivedSheafHom.lean` constructs the
canonical comparison morphism of [Stacks, Tag 0B4B]

`φ : 𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)`,

as the adjunct of `Stacks.Divisors.pushforwardNormalShiftToStructureSheaf`,
`ψ : Ri_*(𝒩[-1]) ⟶ 𝒪_X`, under the adjunction `Ri_* ⊣ R ℰom(𝒪_D, -)` of [Stacks, Tag 0A76].
That `φ` is an isomorphism is proved in the source on the `X` side, after applying `i_*`; this
file is the passage between the two sides.

## The reduction

Derived pushforward reflects isomorphisms
(`…reflectsIsomorphisms_mapDerivedCategory_modulePushforward`), and [Stacks, Tag 0A77] identifies
`Ri_* R ℰom(𝒪_D, -)` with `R ℰom_{𝒪_X}(i_* 𝒪_D, -)`, so `φ` is an isomorphism exactly when the
morphism of `D(𝒪_X)`

`α : Ri_*(𝒩[-1]) ⟶ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)`,

`Ri_*(φ)` followed by [Stacks, Tag 0A77], is one. That is
`Stacks.Divisors.isIso_normalShiftToDerivedSheafHomExactSupport_iff`.

The point of `α` is that it is computable: composing it with the map
`R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X) ⟶ 𝒪_X` induced by the unit `𝒪_X ⟶ i_* 𝒪_D` — the derived evaluation
at one of [Stacks, Tag 0B6M] — returns `ψ`, which is the shifted connecting morphism of the
normal short exact sequence. This is
`Stacks.Divisors.pushforwardNormalShiftToDerivedHomSheaf_comp_derivedEvaluationAtOne`, and it is
what lets the computation of `R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` from the ideal sequence
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` see the comparison morphism at all: `φ` is *defined* by an
adjunction on the `D` side, and this identity is the only thing that transports it.

The input is the triangle of [Stacks, Tag 0B6M] at the level of ringed spaces, namely
`…derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne`: the
counit of [Stacks, Tag 0A76] is the isomorphism of [Stacks, Tag 0A77] followed by the derived
evaluation at one. Since `φ` is the adjunct of `ψ`, pushing `φ` forward and composing with the
counit gives `ψ` by the adjunction, and the triangle rewrites that counit into the two arrows
`α` is built from.

## Main definitions

* `Stacks.Divisors.pushforwardNormalShiftToDerivedHomSheaf`: the morphism `α` above.

## Main results

* `Stacks.Divisors.pushforwardNormalShiftToDerivedHomSheaf_comp_derivedEvaluationAtOne`:
  `α` followed by the derived evaluation at one is `ψ`.
* `Stacks.Divisors.isIso_normalShiftToDerivedSheafHomExactSupport_iff`: the comparison
  morphism of [Stacks, Tag 0B4B] is an isomorphism if and only if `α` is.
* `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff`: the same, for the
  comparison morphism written with the normal sheaf.

## What is not done

The isomorphism assertion of [Stacks, Tag 0B4B] itself is still not proved: what remains after
this file is to show that `α` is an isomorphism, by computing
`R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` from the ideal sequence. That computation needs the identification
of the internal Hom complex `SheafHom^•((ℐ_D ⟶ 𝒪_X), 𝒪_X)` with `(𝒪_X ⟶ 𝒪_X(D))`, which
collapses the product over the pairs `p + n = q` defining its degree-`n` term, and a
distinguished triangle on `R ℰom_{𝒪_X}(-, 𝒪_X)` whose connecting morphism is canonical — the
library's [Stacks, Tag 08I0] (`Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first`)
only asserts that a connecting morphism exists.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0B6M](https://stacks.math.columbia.edu/tag/0B6M)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- The comparison morphism of [Stacks, Tag 0B4B] pushed forward and read through
[Stacks, Tag 0A77]:

`α : Ri_*(𝒩[-1]) ⟶ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` in `D(𝒪_X)`,

where `𝒩 = i^* 𝒪_X(D)`. This is the form in which the source computes the comparison morphism:
the right-hand side is the one the ideal sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` computes. -/
def pushforwardNormalShiftToDerivedHomSheaf :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ⟶
      (closedQuotient D).derivedHomSheafFromPushforwardStructureSheaf.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) :=
  (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
      (normalShiftToDerivedSheafHomExactSupport D) ≫
    (closedQuotient D).derivedModulePushforwardDerivedSheafHomExactSupportIso.hom.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))

/-- **The comparison morphism of [Stacks, Tag 0B4B] transported to the `X` side.** The morphism
`α` of `Stacks.Divisors.pushforwardNormalShiftToDerivedHomSheaf`, followed by the map
`R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X) ⟶ 𝒪_X` induced by the unit `𝒪_X ⟶ i_* 𝒪_D`, is the morphism
`Ri_*(𝒩[-1]) ⟶ 𝒪_X` determined by the normal extension class.

The comparison morphism of [Stacks, Tag 0B4B] is defined on the `D` side, as an adjunct under
[Stacks, Tag 0A76]; this identity is what says what it becomes on the `X` side, where the
computation of `R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` happens. It is the triangle of [Stacks, Tag 0B6M]
(`…derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne`),
which rewrites the counit of [Stacks, Tag 0A76] into the isomorphism of [Stacks, Tag 0A77]
followed by the derived evaluation at one, applied to the adjunction equation
`Stacks.Divisors.normalShiftToDerivedSheafHomExactSupport_adjunct`. -/
theorem pushforwardNormalShiftToDerivedHomSheaf_comp_derivedEvaluationAtOne :
    pushforwardNormalShiftToDerivedHomSheaf D ≫
        (closedQuotient D).derivedEvaluationAtOne.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) =
      pushforwardNormalShiftToStructureSheaf D := by
  rw [pushforwardNormalShiftToDerivedHomSheaf, Category.assoc,
    show (closedQuotient D).derivedModulePushforwardDerivedSheafHomExactSupportIso.hom.app
            ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) ≫
          (closedQuotient D).derivedEvaluationAtOne.app
            ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) =
        (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) from
      (NatTrans.comp_app _ _ _).symm.trans (NatTrans.congr_app (closedQuotient
        D).derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne
        _)]
  exact (Adjunction.homEquiv_counit _ _ _ _).symm.trans
    (normalShiftToDerivedSheafHomExactSupport_adjunct D)

/-- A functor takes an invertible morphism to an invertible morphism.

Stated with `hf` an explicit argument rather than an instance: at the derived categories below,
instance search does not find `IsIso f` from a local hypothesis of that type, because the
`Category` instance in the hypothesis and the one in the goal are reached by different paths. -/
private theorem isIso_map {C E : Type*} [Category C] [Category E] (F : C ⥤ E) {A B : C}
    (f : A ⟶ B) (hf : IsIso f) : IsIso (F.map f) := by
  have := hf
  exact Functor.map_isIso F f

/-- **The isomorphism assertion of [Stacks, Tag 0B4B] is equivalent to an assertion on `X`.**
The canonical comparison morphism `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` is an isomorphism if and only if
the morphism `α : Ri_*(𝒩[-1]) ⟶ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` of
`Stacks.Divisors.pushforwardNormalShiftToDerivedHomSheaf` is.

Derived pushforward along the closed immersion of `D` reflects isomorphisms
([Stacks, Tag 08KS]; `…reflectsIsomorphisms_mapDerivedCategory_modulePushforward`) and the
isomorphism of [Stacks, Tag 0A77] is invertible, so the two assertions differ by an
isomorphism and a conservative functor. -/
theorem isIso_normalShiftToDerivedSheafHomExactSupport_iff :
    IsIso (normalShiftToDerivedSheafHomExactSupport D) ↔
      IsIso (pushforwardNormalShiftToDerivedHomSheaf D) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (isIso_comp_right_iff
      ((modulePushforward (closedQuotient D).i).mapDerivedCategory.map
        (normalShiftToDerivedSheafHomExactSupport D))
      ((closedQuotient D).derivedModulePushforwardDerivedSheafHomExactSupportIso.app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))).hom).mpr
      (isIso_map _ _ h)
  · have : IsIso ((modulePushforward (closedQuotient D).i).mapDerivedCategory.map
        (normalShiftToDerivedSheafHomExactSupport D)) :=
      (isIso_comp_right_iff _
        ((closedQuotient D).derivedModulePushforwardDerivedSheafHomExactSupportIso.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))).hom).mp h
    exact Functor.ReflectsIsomorphisms.reflects
      (modulePushforward (closedQuotient D).i).mapDerivedCategory
      (normalShiftToDerivedSheafHomExactSupport D)

/-- **The isomorphism assertion of [Stacks, Tag 0B4B] for the comparison morphism written with
the normal sheaf** is equivalent to the same assertion on `X`: the two spellings of the
comparison morphism differ by the normal-sheaf clause of [Stacks, Tag 0B3P], which is an
isomorphism. -/
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) ↔
      IsIso (pushforwardNormalShiftToDerivedHomSheaf D) :=
  (isIso_comp_left_iff ((DerivedCategory.singleFunctor D.subscheme.Modules 1).mapIso
        (normalSheafIsoInvertibleSheaf D)).hom
      (normalShiftToDerivedSheafHomExactSupport D)).trans
    (isIso_normalShiftToDerivedSheafHomExactSupport_iff D)

end Stacks.Divisors

end
