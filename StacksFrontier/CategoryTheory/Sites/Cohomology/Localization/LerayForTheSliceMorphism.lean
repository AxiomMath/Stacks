module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedSquareCommutes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackContinuity
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients

/-!
# Leray for the slice morphism, on abelian sheaves

Let `(C, J)` be a site and `f : X ⟶ Y` a morphism of `C`. Composing with `f` is a continuous and
cocontinuous functor `Over.map f : C/X ⥤ C/Y`, so it induces a morphism of topoi
`Sh(C/X) ⟶ Sh(C/Y)` whose inverse image is the restriction
`Stacks.Cohomology.Localization.overPullback` and whose direct image is
`Stacks.Cohomology.Localization.overPushforward`. This file proves, for abelian sheaves,

`RΓ(Y, -) ∘ Rf_* ≅ RΓ(X, -)`  as functors  `D(Ab(C/X)) ⥤ D(Ab)`,

together with its degreewise consequence `H^m(Y, Rf_*K) ≅ H^m(X, K)`. Here `RΓ(X, -)` and
`RΓ(Y, -)` are the unbounded total right derived functors of the global sections of the two
localized sites, that is of sections over the final objects `𝟙 X` of `C/X` and `𝟙 Y` of `C/Y`.

Two inputs make the argument short, and both are already in this development. The underived
identity `Γ(Y, f_*ℱ) = Γ(X, ℱ)` holds because `Over.map f` has the right adjoint
`Over.pullback f`, so the direct image attached to cocontinuity of `Over.map f` is the direct
image attached to continuity of `Over.pullback f`
(`CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso`, Stacks 00XX (1)) — that is, plain
restriction along `Over.pullback f` — and `Over.pullback f` carries the final object of `C/Y` to
the final object of `C/X`, being a right adjoint. Second, `f_*` carries K-injective complexes to
K-injective complexes, `overPushforward_map_isKInjective`, because its left adjoint `f^{-1}` is
exact. The two together feed `Stacks.Cohomology.LerayUnbounded.derivedCompIso`.

## Main results

All in the namespace `Stacks.Cohomology.Localization`.

* `overPushforwardGlobalSectionsIso`: the underived identity `Γ(Y, f_*ℱ) ≅ Γ(X, ℱ)`.
* `derivedGlobalSectionsOverPushforwardIso`: `RΓ(Y, -) ∘ Rf_* ≅ RΓ(X, -)`.
* `cohomologyOverPushforwardIso`: its degreewise form `H^m(Y, Rf_*K) ≅ H^m(X, K)`.

## Why this is unconditional, and what it costs instead

The same statement for sheaves of modules on ringed sites is
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIso`
(`CategoryTheory/Sites/Cohomology/DerivedPushforward/LerayForUnboundedSections.lean`), and there
it is *conditional*: it carries the named hypothesis `h093Y` that degreewise direct image
preserves K-injectivity, discharged only for a flat morphism of ringed sites in
`derivedSectionsOverObjectPushforwardIsoOfFlat`. For the slice morphism no such hypothesis is
needed, and none is carried here: the left adjoint of `f_*` is the restriction `f^{-1}`, which is
both a left and a right adjoint and hence exact with no assumption at all
(`overPullback_preservesFiniteLimits`, `overPullback_preservesFiniteColimits`), so the adjoint
criterion for K-injectivity (Stacks 08BJ) applies outright.

What is assumed instead is `Limits.HasPullbacksAlong f`: base change of the one morphism `f`
against the arrows into `Y`. It is used only to name `f_*` concretely — it is what `Over.pullback
f` and the adjunction `Over.mapPullbackAdj f` are defined under, and without that right adjoint
to `Over.map f` the direct image is the right Kan extension along `(Over.map f).op`, so the
underived identity would have to be read off that limit rather than from
`Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal`. It is a hypothesis on the morphism, not
on the sheaves or on the conclusion, and it does not reinstate the `h093Y` of the module version:
the K-injectivity half above is proved without it.

The per-morphism form, rather than `Limits.HasPullbacks C`, is what makes the statement usable
on a site with base change along some arrows only, such as the comparison situation of
Stacks 0EZ3 for the arrows of its distinguished class. Mathlib states continuity of
`Over.pullback f` between the localized topologies under the global hypothesis, so that step is
taken here from `CategoryTheory.GrothendieckTopology.isContinuous_overPullback`
(`CategoryTheory/Sites/Localization/OverPullbackContinuity.lean`), which is the same proof under
`HasPullbacksAlong f`.

## The Stacks tag

The tag registered below is 0D6H, Cohomology on Sites Lemma 21.20.5, whose second clause is
`RΓ(V, -) ∘ Rf_* = RΓ(U, -)` for an object `V` of the target site with `U = u(V)`. Here `u` is
`Over.pullback f`, which is continuous, `V` is the final object `𝟙 Y` of `C/Y`, and `u(V) ≅ 𝟙 X`
is the final object of `C/X`. The source states the lemma for a morphism of ringed sites and
sheaves of modules; this is the case of abelian sheaves, where the structure sheaf plays no part.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 00XX](https://stacks.math.columbia.edu/tag/00XX)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.Localization

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [∀ U : C, HasSheafify (J.over U) Ab.{max u v}]

/-- **The underived identity behind Leray for the slice morphism:** the global sections on `C/Y`
of the direct image along `f : X ⟶ Y` of an abelian sheaf on `C/X` are the global sections of
that sheaf on `C/X`.

The direct image attached to cocontinuity of `Over.map f` is the direct image attached to
continuity of its right adjoint `Over.pullback f` (Stacks 00XX (1)), hence plain restriction;
and `Over.pullback f` sends the final object of `C/Y` to the final object of `C/X`. -/
def overPushforwardGlobalSectionsIso {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    overPushforward J f ⋙
        (sheafSections (J.over Y) Ab.{max u v}).obj (op (Over.mk (𝟙 Y))) ≅
      (sheafSections (J.over X) Ab.{max u v}).obj (op (Over.mk (𝟙 X))) :=
  Functor.isoWhiskerRight ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{max u v})
      ((sheafSections (J.over Y) Ab.{max u v}).obj (op (Over.mk (𝟙 Y)))) ≪≫
    Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal (Over.pullback f) Ab.{max u v}
      (J.over Y) (J.over X)
      (Stacks.ConstantSheaf.Localization.overPullbackObjTerminalIsoOfHasPullbacksAlong f)

attribute [local instance] HasDerivedCategory.standard sheaf_isGrothendieckAbelian

/-- **Stacks 0D6H for the slice morphism, on abelian sheaves.** For a morphism `f : X ⟶ Y` of a
site `C`, the unbounded derived global sections on `C/Y` of the unbounded derived direct image
along `f` are the unbounded derived global sections on `C/X`:
`RΓ(Y, -) ∘ Rf_* ≅ RΓ(X, -)`.

Both sides are total right derived functors of one and the same functor on the unbounded homotopy
category of abelian sheaves on `C/X`, by `overPushforwardGlobalSectionsIso`; the comparison for
`Rf_*` is invertible on a K-injective complex, and the comparison for `RΓ(Y, -)` is invertible at
`f_*I`, which is again K-injective by `overPushforward_map_isKInjective`. Uniqueness of right
derived functors then identifies the two, which is
`Stacks.Cohomology.LerayUnbounded.derivedCompIso`. -/
@[stacks 0D6H "the clause `RGamma(V, -) . Rf_* = RGamma(U, -)` on sections over an object, for \
ABELIAN sheaves and for the SLICE morphism of topoi `Sh(C/X) -> Sh(C/Y)` of a morphism \
`f : X -> Y` of the site, at the final object `V = id Y` of `C/Y`, where `u = Over.pullback f` \
and `u(V) = id X`.  Unconditional: no analogue of the `h093Y` K-injectivity hypothesis, nor of \
the flatness, of `Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIso` and \
`...IsoOfFlat`, which carry this tag for sheaves of MODULES on ringed sites.  Assumed instead is \
`Limits.HasPullbacksAlong f`, base change of the single morphism `f`, used only to present \
`f_*` as restriction along `Over.pullback f`.  NOT \
covered: the clause on global sections into `D(Gamma(O_D))` for a general morphism of ringed \
sites, and sections over a non-final object of `C/Y`"]
def derivedGlobalSectionsOverPushforwardIso {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    DerivedFunctor.totalRightDerived (overPushforward J f) ⋙
        DerivedFunctor.totalRightDerived
          ((sheafSections (J.over Y) Ab.{max u v}).obj (op (Over.mk (𝟙 Y)))) ≅
      DerivedFunctor.totalRightDerived
        ((sheafSections (J.over X) Ab.{max u v}).obj (op (Over.mk (𝟙 X)))) :=
  LerayUnbounded.derivedCompIso (overPushforward J f)
    ((sheafSections (J.over Y) Ab.{max u v}).obj (op (Over.mk (𝟙 Y))))
    ((sheafSections (J.over X) Ab.{max u v}).obj (op (Over.mk (𝟙 X))))
    (overPushforwardGlobalSectionsIso J f) (overPushforward_map_isKInjective J f)

/-- **`H^m(Y, Rf_*K) ≅ H^m(X, K)`.** The degreewise form of
`derivedGlobalSectionsOverPushforwardIso`: for every `m`, the `m`-th cohomology of the derived
global sections on `C/Y` of `Rf_*K` is the `m`-th cohomology of the derived global sections of `K`
on `C/X`, naturally in `K`. -/
def cohomologyOverPushforwardIso {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] (m : ℤ) :
    (DerivedFunctor.totalRightDerived (overPushforward J f) ⋙
          DerivedFunctor.totalRightDerived
            ((sheafSections (J.over Y) Ab.{max u v}).obj (op (Over.mk (𝟙 Y))))) ⋙
        DerivedCategory.homologyFunctor Ab.{max u v} m ≅
      DerivedFunctor.totalRightDerived
          ((sheafSections (J.over X) Ab.{max u v}).obj (op (Over.mk (𝟙 X)))) ⋙
        DerivedCategory.homologyFunctor Ab.{max u v} m :=
  Functor.isoWhiskerRight (derivedGlobalSectionsOverPushforwardIso J f)
    (DerivedCategory.homologyFunctor Ab.{max u v} m)

end Stacks.Cohomology.Localization

end
