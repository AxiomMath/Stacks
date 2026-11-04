module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductInstance
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.ChangeBaseConnectedLimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigModuleAbelianComparison
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Change of divided power base carries injective abelian sheaves on `CRIS(X/S)` to injectives

Let `u = changeBase S S' f g h : CRIS(X/S) ⥤ CRIS(Y/S')` be change of divided power base.  This
file proves, **at abelian coefficients and for every `g`**, that restriction along `u` carries
injective abelian sheaves on `CRIS(Y/S')` to injective abelian sheaves on `CRIS(X/S)`, hence a
fortiori to `Γ(CRIS(X/S), -)`-acyclic ones.  In particular that holds of the Frobenius
endofunctor `(F_X)_cris` of [Stacks, Tag 07IC] in a Frobenius crystal situation
[Stacks, Tag 07N2], which is change of base along `Spec(σ)` and the absolute Frobenius of `X`.

The route is the one `SmallSite/Formula07MKInjectives.lean` takes for the small sites:

* restriction along `u` is the right adjoint of the abelian lower shriek `u_!`
  (`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`), change of base
  being continuous;
* `u_!` is exact by [Stacks, Tag 00X4], `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`,
  whose hypotheses are that the source site have fibre products and equalizers which `u`
  preserves: `CRIS(X/S)` has fibre products ([Stacks, Tag 07I9]) and therefore equalizers, and
  `u` preserves both because they are *connected* shapes and change of base leaves the underlying
  thickening and both components of a morphism untouched,
  `...changeBase_preservesLimitsOfShape`;
* a right adjoint of a monomorphism-preserving functor preserves injective objects,
  [Stacks, Tag 015Z].

No localization and no covering argument is involved, and nothing is assumed of `g` — in
particular the absolute Frobenius of `X`, which is not an open immersion, is covered.

## What this settles, and what it does not

At **abelian** coefficients this is the full input of [Stacks, Tag 015M] for the pair
`(u^{-1}, Γ)`: the comparison `R(Γ ∘ u^{-1}) ⟶ RΓ ∘ u^{-1}` of [Stacks, Tag 05T2] is invertible,
there being nothing left to check once `u^{-1}` is exact and preserves injectives.

At **module** coefficients the same statement is *not* a consequence of this one and is not
proved anywhere, the underlying abelian sheaf of an injective sheaf of `𝒪_{X/S}`-modules being
`Γ`-acyclic ([Stacks, Tag 03FD], `...SmallSite.isZero_bigRightDerived_bigToAbelianSheaf_succ`)
but not injective; the obstruction is the one
`SmallSite/LowerShriekModules.lean` records for the inclusion, namely that the module-level lower
shriek is `V ↦ (u_!^{Ab}M)(V) ⊗_{A_V} 𝒪_{X/S}(V)` and is exact only where `𝒪_{X/S}(V)` is flat
over `A_V`.  **It is also not needed**: the canonical map of [Stacks, Tag 07N5] is built in
`SmallSite/FrobeniusDerivedGlobalSections.lean` out of the [Stacks, Tag 05T2] comparison, which
runs in the direction the construction uses without any acyclicity hypothesis.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `changeBaseAbelianRestriction` — restriction of abelian sheaves along change of divided power
  base on the big crystalline sites.
* `FCrystalSituation.frobeniusAbelianRestriction` — `(F_X)_cris^{-1}` on abelian sheaves.

## Main results

* `preservesFiniteLimits_changeBaseAbelianLowerShriek` — **the abelian `u_!` is exact**,
  [Stacks, Tag 00X4].
* `preservesInjectiveObjects_changeBaseAbelianRestriction` — **restriction along change of base
  carries injective abelian sheaves to injective abelian sheaves**, [Stacks, Tag 015Z].
* `FCrystalSituation.preservesInjectiveObjects_frobeniusAbelianRestriction` and
  `FCrystalSituation.isZero_bigRightDerived_frobeniusAbelianRestriction_succ` — the same for the
  Frobenius endofunctor, and its consequence: **`(F_X)_cris^{-1}` carries an injective abelian
  sheaf to a `Γ(CRIS(X/S), -)`-acyclic one**, in every positive degree.

## What is and is not proved

Everything is unconditional: no affineness, no hypothesis on `g` or on `f`, and no hypothesis on
the sheaf beyond injectivity where it is stated.

**No `@[stacks]` attribute is placed.**  [Stacks, Tag 00X4] and [Stacks, Tag 015Z] are registered
on the general statements this file instantiates, and no numbered clause of the chapter asserts
what is proved here.

## References

* [Stacks Project, Tag 00X4](https://stacks.math.columbia.edu/tag/00X4)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

section ChangeBase

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **Restriction of abelian sheaves along change of divided power base** on the big crystalline
sites, at the coefficient universe `u + 1` of this chapter.  Change of base is continuous,
`...changeBase_isContinuous`, so no sheafification is involved and on sections this is
`G ↦ G ∘ changeBase`. -/
def changeBaseAbelianRestriction :
    Sheaf (topology S') AddCommGrpCat.{u + 1} ⥤ Sheaf (topology S) AddCommGrpCat.{u + 1} :=
  (changeBase S S' f g h).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology S) (topology S')

/-- **The lower shriek along change of divided power base is exact on abelian sheaves**,
[Stacks, Tag 00X4] in the form `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`: the
lower shriek is the sheafification of a pointwise colimit over a costructured-arrow category, and
that category is pseudofiltered as soon as the source site has fibre products and equalizers
which the functor preserves.

`CRIS(X/S)` has fibre products by [Stacks, Tag 07I9] and hence equalizers, and change of base
preserves limits of every connected shape — both of these are connected — by
`...changeBase_preservesLimitsOfShape`. -/
theorem preservesFiniteLimits_changeBaseAbelianLowerShriek :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (changeBase S S' f g h) AddCommGrpCat.{u + 1} (topology S) (topology S')) :=
  have : HasEqualizers (Thickening S) := hasEqualizers_of_hasPullbacks_and_binary_products
  have : PreservesLimitsOfShape WalkingCospan (changeBase S S' f g h) :=
    changeBase_preservesLimitsOfShape _
  have : PreservesLimitsOfShape WalkingParallelPair (changeBase S S' f g h) :=
    changeBase_preservesLimitsOfShape _
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1} (changeBase S S' f g h) _ _

/-- **Restriction along change of divided power base carries injective abelian sheaves on
`CRIS(Y/S')` to injective abelian sheaves on `CRIS(X/S)`.**

Restriction is the right adjoint of the lower shriek, which the previous theorem makes exact and
hence monomorphism-preserving; a right adjoint of a monomorphism-preserving functor preserves
injective objects, [Stacks, Tag 015Z]. -/
instance preservesInjectiveObjects_changeBaseAbelianRestriction :
    (changeBaseAbelianRestriction S S' f g h).PreservesInjectiveObjects :=
  haveI := preservesFiniteLimits_changeBaseAbelianLowerShriek S S' f g h
  haveI : (Functor.sheafPullbackConstruction.sheafPullback (changeBase S S' f g h)
      AddCommGrpCat.{u + 1} (topology S) (topology S')).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (changeBase S S' f g h)
      AddCommGrpCat.{u + 1} (topology S) (topology S'))

end ChangeBase

namespace FCrystalSituation

variable (T : FCrystalSituation.{u})

/-- **`(F_X)_cris^{-1}` on abelian sheaves**, restriction along the Frobenius endofunctor of the
big crystalline category of [Stacks, Tag 07IC]. -/
def frobeniusAbelianRestriction :
    Sheaf (topology T.global) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology T.global) AddCommGrpCat.{u + 1} :=
  changeBaseAbelianRestriction T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma

/-- **The Frobenius pullback of abelian sheaves carries injectives to injectives.**  The Frobenius
endofunctor is change of divided power base along `Spec(σ)` and the absolute Frobenius of `X`, so
this is `preservesInjectiveObjects_changeBaseAbelianRestriction`; that the absolute Frobenius is
not an open immersion is irrelevant, nothing in that proof being about `g`. -/
instance preservesInjectiveObjects_frobeniusAbelianRestriction :
    (frobeniusAbelianRestriction T).PreservesInjectiveObjects :=
  preservesInjectiveObjects_changeBaseAbelianRestriction T.global T.global T.specSigma
    T.frobenius T.toClosedFiber_comp_closedFiberMap_specSigma

/-- **The Frobenius pullback carries an injective abelian sheaf to a `Γ(CRIS(X/S), -)`-acyclic
one**: `H^{n+1}(CRIS(X/S), (F_X)_cris^{-1} J) = 0` for `J` an injective abelian sheaf on
`CRIS(X/S)`.

It carries it to an *injective* abelian sheaf, by
`preservesInjectiveObjects_frobeniusAbelianRestriction`, and the higher right derived functors of
any additive functor vanish on injective objects.

This is the abelian-coefficient form of the acyclicity that [Stacks, Tag 015M] asks for the pair
`((F_X)_cris^{-1}, Γ)`.  Its module-coefficient form is **not** a consequence of it; see the
module documentation. -/
theorem isZero_bigRightDerived_frobeniusAbelianRestriction_succ
    (J : Sheaf (topology T.global) AddCommGrpCat.{u + 1}) [Injective J] (n : ℕ) :
    IsZero (((SmallSite.bigGlobalSections T.global).rightDerived (n + 1)).obj
      ((frobeniusAbelianRestriction T).obj J)) :=
  have : Injective ((frobeniusAbelianRestriction T).obj J) :=
    (frobeniusAbelianRestriction T).injective_obj J
  Functor.isZero_rightDerived_obj_injective_succ _ n _

end FCrystalSituation

end Crystalline.GlobalCrystallineSituation

end

end
