module

public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Dualizing complexes on a locally Noetherian scheme

A dualizing complex over a Noetherian commutative ring is the notion of
`Dualizing.IsDualizingComplex` ([Stacks, Tag 0A7B]): an object of `D(A)` of finite injective
dimension, with finite cohomology modules, whose homothety map `A → RHom_A(K, K)` is a
quasi-isomorphism. This file globalises it. An object `K` of `D(𝒪_X)` on a locally Noetherian
scheme `X` is a *dualizing complex* when over every affine open `U ⊆ X` it is the associated
sheaf of a dualizing complex over `Γ(X, U)`, in the sense that `K|_U` becomes isomorphic to
`ω^~` in `D(𝒪_U)` for some dualizing `ω ∈ D(Γ(X, U))` — this is [Stacks, Tag 0A87], read through
the all-affine-open form of the equivalent conditions of [Stacks, Tag 0A86].

Both the restriction `𝒪_X`-modules ⥤ `𝒪_U`-modules along the open immersion `U ⟶ X` and the
associated-sheaf functor `ModuleCat Γ(X, U) ⥤ (Spec Γ(X, U)).Modules` are exact, so each induces
a functor of unbounded derived categories, which is what lets the condition be phrased in
`D(𝒪_U)` rather than only on cochain complexes. The canonical isomorphism
`U ≅ Spec Γ(X, U)` of an affine open transports the second into `D(𝒪_U)`.

## Main definitions

* `Stacks.Duality.HasDualizingModelOn` — the local condition at one affine open: `K` restricted
  to `U` is the associated sheaf of a dualizing complex over `Γ(X, U)`. This is the predicate
  whose all-affine-open and affine-cover forms [Stacks, Tag 0A86] identifies.
* `Stacks.Duality.IsDualizingComplex` — **[Stacks, Tag 0A87]**, a dualizing complex on a
  locally Noetherian scheme: `Stacks.Duality.HasDualizingModelOn` at every affine open.

## Main results

* `Stacks.Duality.hasDualizingModelOn_of_iso` and `Stacks.Duality.isDualizingComplex_of_iso` —
  both conditions depend on `K` only through its isomorphism class in `D(𝒪_X)`.

## Implementation notes

The definition is the all-affine-open condition, not the existence of one affine open cover on
which the condition holds. The two are equivalent — that equivalence is the content of
[Stacks, Tag 0A86] — but the equivalence is not proved here, and the all-affine-open form is the
one a consumer can use at a given affine open with no further argument. Consequently no
`@[stacks 0A86]` attribute appears below: the tag's content is the equivalence, which is open,
and the audit scanner keys on the bare four-character tag.

`IsLocallyNoetherian.component_noetherian` supplies `IsNoetherianRing Γ(X, U)` from an affine
open of a locally Noetherian scheme, which is what makes `Dualizing.IsDualizingComplex`
applicable to a complex of `Γ(X, U)`-modules; it is introduced by a `letI` inside the
definition rather than assumed, so the predicate needs no instance argument at the call site.

`D(𝒪_X)` is an **instance argument**: both predicates take `[HasDerivedCategory.{w} X.Modules]`,
so a consumer may read them at whatever model it already works in — in particular at the locally
small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the model
`Stacks.Duality.quasiCoherentDerivedPushforward` and `Stacks.Duality.relativeDualizingModule`
live at. That is possible because `Dualizing.IsDualizingComplex` now carries a free
`HasDerivedCategory` binder of its own; it does matter, because `HasDerivedCategory` is
`CategoryTheory.MorphismProperty.HasLocalization`, a *data*-carrying class, so there is no
proof irrelevance to make two routes to it agree and a statement proved at one model says
nothing about another.

The two derived categories that `HasDualizingModelOn` mentions *besides* `D(𝒪_X)` cannot be
binders: `D(𝒪_U)` and `D(Γ(X, U))` depend on the affine open `U`, which
`Stacks.Duality.IsDualizingComplex` universally quantifies. They are therefore chosen inside the
body of `HasDualizingModelOn`, at `HasDerivedCategory.standard`, by the two `letI`s below. That
choice is sealed: it is invisible in the type of either predicate (verified with
`set_option pp.explicit`: zero occurrences of `HasDerivedCategory.standard`), and it is harmless
because the condition is an existential over the objects of `D(Γ(X, U))` and no coproduct of
either category is taken. A proof reading `HasDualizingModelOn` must introduce the same two
instances — see `Stacks.Duality.isFiniteTildeOn_homology_of_hasDualizingModelOn`.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- An affine open `U` of a locally Noetherian scheme carries a *dualizing model* of
`K ∈ D(𝒪_X)` when there is a dualizing complex `ω` over `Γ(X, U)` ([Stacks, Tag 0A7B]) whose
associated sheaf, transported along `U ≅ Spec Γ(X, U)`, is isomorphic to `K|_U` in `D(𝒪_U)`.

This is the local condition appearing in both equivalent forms of [Stacks, Tag 0A86]. -/
def HasDualizingModelOn (K : DerivedCategory X.Modules) (U : X.Opens) (hU : IsAffineOpen U) :
    Prop :=
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := HasDerivedCategory.standard U.toScheme.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
    Dualizing.IsDualizingComplex ω ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
        (tilde.functor Γ(X, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)

/-- **Stacks Project, Tag 0A87.** A *dualizing complex* on a locally Noetherian scheme `X` is an
object of `D(𝒪_X)` which, over every affine open `U ⊆ X`, is the associated sheaf of a dualizing
complex over `Γ(X, U)`.

By [Stacks, Tag 0A86] it is enough to check this on the members of a single affine open cover. -/
@[stacks 0A87]
abbrev IsDualizingComplex (K : DerivedCategory X.Modules) : Prop :=
  ∀ (U : X.Opens) (hU : IsAffineOpen U), HasDualizingModelOn K U hU

/-- Carrying a dualizing model at an affine open depends on `K` only through its isomorphism
class: restriction to `U` takes an isomorphism of `D(𝒪_X)` to one of `D(𝒪_U)`. -/
theorem hasDualizingModelOn_of_iso {K L : DerivedCategory X.Modules} (e : K ≅ L)
    {U : X.Opens} {hU : IsAffineOpen U} (h : HasDualizingModelOn K U hU) :
    HasDualizingModelOn L U hU := by
  let := HasDerivedCategory.standard U.toScheme.Modules
  obtain ⟨ω, hω, ⟨i⟩⟩ := h
  exact ⟨ω, hω, ⟨(Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.mapIso e.symm ≪≫ i⟩⟩

/-- Being a dualizing complex depends on `K` only through its isomorphism class in `D(𝒪_X)`. -/
theorem isDualizingComplex_of_iso {K L : DerivedCategory X.Modules} (e : K ≅ L)
    (h : IsDualizingComplex K) : IsDualizingComplex L :=
  fun U hU => hasDualizingModelOn_of_iso e (h U hU)

end Stacks.Duality

end
