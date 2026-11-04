module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import StacksCore.Tactic.StacksAttribute

/-!
# The four base-change functors of a map of quasi-coherent modules

In the situation of Stacks 083F — a scheme `S`, a morphism `f : X ⟶ Y` of algebraic spaces over
`S`, and a map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — every scheme `T` over `Y` carries
the base change `u_T : ℱ_T ⟶ 𝒢_T`, the pullback of `u` along the projection `X_T = X ×_Y T ⟶ X`.
Stacks 083F displays the functor

`F_iso : (Sch/Y)ᵒᵖ ⟶ Sets`,  `T ↦ {∗}` if `u_T` is an isomorphism and `∅` otherwise,

as Equation 77.7.1.1, and names the variants `F_inj`, `F_surj`, `F_zero` obtained by asking
instead that `u_T` be injective, surjective, or zero.

This file names those four assignments for the inverse image of modules this development
actually has — `AlgebraicGeometry.Space.modulePullback`, the inverse image of Stacks 03LU for
the small étale ringed sites, packaged as `AlgebraicGeometry.Space.modulePullbackSystem`.  The
general machinery of `StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapSituation.lean` is stated
relative to a `AlgebraicGeometry.Space.ModulePullbackSystem` supplied as a hypothesis; nothing
here carries such a hypothesis, so each declaration below depends on the standing data of the
situation and on nothing else.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.isoFunctorSmallEtale` is `F_iso`, Equation
  77.7.1.1 itself.
* `AlgebraicGeometry.Space.ModuleMapSituation.surjFunctorSmallEtale` is `F_surj`.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroFunctorSmallEtale` is `F_zero`.
* `AlgebraicGeometry.Space.ModuleMapSituation.IsInjAt` is the condition of the variant `F_inj`:
  that `u_T` is a monomorphism.  See the warning below — it is a condition and not a functor.
* `AlgebraicGeometry.Space.ModuleMapSituation.injFunctorSmallEtale` is the universal-injectivity
  functor, the reading of `F_inj` under which Stacks 083H and Stacks 083I are proved in this
  development.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isInjAt_iff` unfolds the injectivity condition.
* `AlgebraicGeometry.Space.ModuleMapSituation.isUniversallyInjectiveAt_iff_forall_isInjAt`:
  universal injectivity at `T` is exactly injectivity at every test scheme over `T`.  So
  `injFunctorSmallEtale` is the largest subfunctor of the final object whose sections are
  injectivity conditions — see below.

The three functors are `AlgebraicGeometry.Space.ModuleMapSituation.subterminalFunctor`s, so the
characterisations `AlgebraicGeometry.Space.ModuleMapSituation.nonempty_isoFunctor_obj_iff` and
its siblings, and the `*Functor_obj_subsingleton` instances, apply to them as they stand: each
value is a singleton exactly when the corresponding condition holds at the test scheme, and is
empty otherwise.  The five definitions below are `abbrev`s and a `def` over the general ones for
that reason, so that no part of the existing interface has to be restated.

## `F_inj` is not a presheaf

**The assignment `T ↦ {∗ | u_T injective}` of Stacks 083F is not a subfunctor of the final
object, and this development does not claim that it is.**  A subterminal presheaf on `Sch/Y`
needs its condition to be stable under restriction along a morphism `T' ⟶ T` of test schemes,
and injectivity is not: the inverse image `f^*(-) = 𝒪 ⊗_{f⁻¹𝒪} f⁻¹(-)` is a left adjoint, hence
right exact, and tensoring does not carry a monomorphism to a monomorphism.

Concretely, take a field `k`, let `X = Y = Spec k[x]` with `f` the identity, let `ℱ = 𝒢 = 𝒪_X`
and let `u` be multiplication by `x`.  At the test scheme `T = Spec k[x]` with the identity map
to `Y` we have `X_T = X` and `u_T` is multiplication by `x` on `k[x]`, which is injective
because `k[x]` is a domain.  At `T' = Spec k[x]/(x) = Spec k`, with the closed immersion
`T' ⟶ T` as a morphism of test schemes over `Y`, we have `X_{T'} = Spec k` and `u_{T'}` is
multiplication by `x` on `k`, that is the zero map on a nonzero module, which is not injective.
So the assignment takes the value `{∗}` at `T` and the value `∅` at `T'`, while a presheaf would
have to produce a function `{∗} ⟶ ∅` from the morphism `T' ⟶ T`.

No hypothesis is invented here to rescue the claim.  What is registered against Stacks 083F for
this variant is the *condition* `IsInjAt`, which is what the source writes down, and nothing
more.  The repair that this development uses for the later lemmas of the section is universal
injectivity, `AlgebraicGeometry.Space.ModuleMapSituation.IsUniversallyInjectiveAt`: injectivity
after every further base change.  That condition *is* restriction-stable, by
`AlgebraicGeometry.Space.ModuleMapSituation.isUniversallyInjectiveAt_of_hom`, and
`isUniversallyInjectiveAt_iff_forall_isInjAt` identifies it as the largest restriction-stable
condition implying `IsInjAt`, so `injFunctorSmallEtale` is the largest subfunctor of the final
object contained in the assignment of `F_inj`.  Stacks 083H and Stacks 083I, which quantify over
`F_inj` as though it were a functor, are proved in this development for that functor —
`AlgebraicGeometry.Space.ModuleMapSituation.isSheaf_injFunctor` and
`.injFunctor_and_zeroFunctor_pullbackSituation_eq` — and `injFunctorSmallEtale` is the name of
its value here.  In this
file only the three genuine functors and the injectivity condition carry a Stacks 083F
registration; the standing data of the situation carries its own, where it is declared.

## Implementation notes

The module universe is the universe `u` of the structure rings, not a free one: the inverse
image `AlgebraicGeometry.Space.modulePullback` and its adjunction exist only there, because the
direct image they are adjoint to is assembled from the comparison equivalence of Stacks 03G1,
which is available only at `Type u`.  So `modulePullbackSystem` exists only at that universe and
the situation is taken at `Modules.{u, u}`.  The standing data
`AlgebraicGeometry.Space.ModuleMapSituation` itself leaves the module universe free, and the
general loci built on a hypothetical system stay polymorphic in it.

## References

* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 083H](https://stacks.math.columbia.edu/tag/083H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : ModuleMapSituation.{u, u} B S hS)

/-! ### The isomorphism functor -/

/-- **Stacks 083F, Equation 77.7.1.1.**  The functor `F_iso` of a map `u : ℱ ⟶ 𝒢` of
quasi-coherent `𝒪_X`-modules: it sends a scheme `T` over `Y` to a one-element set if the base
change `u_T` along `X ×_Y T ⟶ X` is an isomorphism, and to the empty set otherwise.

The base change is taken for the inverse image of modules of Stacks 03LU for the small étale
ringed sites, `AlgebraicGeometry.Space.modulePullback`. -/
@[stacks 083F "the functor F_iso of Equation 77.7.1.1"]
abbrev isoFunctorSmallEtale : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.isoFunctor (modulePullbackSystem B S hS)

/-! ### The surjectivity functor -/

/-- **Stacks 083F, the variant `F_surj`.**  The functor sending a scheme `T` over `Y` to a
one-element set if the base change `u_T` is surjective, and to the empty set otherwise.

Surjectivity is restriction-stable because the inverse image of modules is a left adjoint and so
preserves epimorphisms; that is
`AlgebraicGeometry.Space.ModuleMapSituation.isSurjectiveAt_of_hom`. -/
@[stacks 083F "the variant F_surj"]
abbrev surjFunctorSmallEtale : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.surjFunctor (modulePullbackSystem B S hS)

/-! ### The vanishing functor -/

/-- **Stacks 083F, the variant `F_zero`.**  The functor sending a scheme `T` over `Y` to a
one-element set if the base change `u_T` is zero, and to the empty set otherwise. -/
@[stacks 083F "the variant F_zero"]
abbrev zeroFunctorSmallEtale : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.zeroFunctor (modulePullbackSystem B S hS)

/-! ### The injectivity variant -/

/-- **Stacks 083F, the variant `F_inj`.**  The condition the source asks of a scheme `T` over
`Y` for its variant `F_inj`: that the base change `u_T` of `u` along `X ×_Y T ⟶ X` is injective,
which for a map of sheaves of modules is being a monomorphism.

This is a condition on test schemes and *not* a subterminal presheaf on them: it is not stable
under restriction along a morphism of test schemes, because the inverse image of modules is only
right exact.  The file's notes give the counterexample.  The restriction-stable condition this
development uses in its place is
`AlgebraicGeometry.Space.ModuleMapSituation.IsUniversallyInjectiveAt`. -/
@[stacks 083F "the variant F_inj: the condition that u_T is injective"]
def IsInjAt (T : D.SchemesOver) : Prop :=
  Mono (D.baseChangeHom (modulePullbackSystem B S hS) T)

/-- The injectivity condition at a test scheme, unfolded: the elaborator does not unfold the
definition on its own. -/
theorem isInjAt_iff (T : D.SchemesOver) :
    D.IsInjAt T ↔ Mono (D.baseChangeHom (modulePullbackSystem B S hS) T) :=
  Iff.rfl

/-- The universal-injectivity functor of the situation, for the inverse image of modules of
Stacks 03LU: the functor sending a scheme `T` over `Y` to a one-element set if the base change
of `u` is injective at every test scheme over `T`, and to the empty set otherwise.

This is the reading of the variant `F_inj` of Stacks 083F under which Stacks 083H and
Stacks 083I are proved in this development, and
`AlgebraicGeometry.Space.ModuleMapSituation.isUniversallyInjectiveAt_iff_forall_isInjAt`
identifies it as the largest subfunctor of the final object contained in the assignment
`T ↦ {∗ | u_T injective}` that the source writes.  It carries no Stacks 083F registration,
because that assignment is not a functor and this one is a different, stronger condition; the
registration for the variant is on
`AlgebraicGeometry.Space.ModuleMapSituation.IsInjAt`. -/
abbrev injFunctorSmallEtale : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.injFunctor (modulePullbackSystem B S hS)

/-- **Universal injectivity is injectivity at every test scheme over the given one.**  Together
with `AlgebraicGeometry.Space.ModuleMapSituation.isUniversallyInjectiveAt_of_hom` this says that
the universal-injectivity functor is the largest subfunctor of the final object whose value at
`T` is nonempty only when `u_T` is injective. -/
theorem isUniversallyInjectiveAt_iff_forall_isInjAt (T : D.SchemesOver) :
    D.IsUniversallyInjectiveAt (modulePullbackSystem B S hS) T ↔
      ∀ (T' : D.SchemesOver) (_g : T' ⟶ T), D.IsInjAt T' :=
  Iff.rfl

end ModuleMapSituation

end AlgebraicGeometry.Space

end
