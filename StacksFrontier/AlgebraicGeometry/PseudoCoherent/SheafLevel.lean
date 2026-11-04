module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands

/-!
# Pseudo-coherent complexes of modules on a ringed space

Let `X` be a ringed space. A complex of `𝒪_X`-modules is `m`-pseudo-coherent if every point of
`X` has an open neighbourhood on which the complex receives a map from a strictly perfect complex
which is an isomorphism on cohomology in degrees above `m` and an epimorphism on cohomology in
degree `m`; it is pseudo-coherent if it is `m`-pseudo-coherent for every integer `m`. An object of
the derived category is `m`-pseudo-coherent, resp. pseudo-coherent, if some complex representing
it is.

## Main definitions

* `AlgebraicGeometry.RingedSpace.restrictModules` is the restriction functor on sheaves of
  modules along the inclusion of an open subspace.
* `AlgebraicGeometry.RingedSpace.restrictComplex` applies it degreewise to a cochain complex.
* `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom` and
  `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplex` are `m`-pseudo-coherence and
  pseudo-coherence of a complex.
* `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom` and
  `AlgebraicGeometry.RingedSpace.IsPseudoCoherent` are the corresponding conditions on an object
  of the derived category.

## Implementation notes

The category of `𝒪_X`-modules is `StrictlyPerfect.OXMod X`, the sheaves of modules over the
structure sheaf of `X` viewed as a sheaf of rings, and strict perfection is
`StrictlyPerfect.IsStrictlyPerfect` (Stacks 08C4). The local category is that of modules on the
restricted ringed space `X.restrict U.isOpenEmbedding`, and restriction is the pushforward of
sheaves of modules along the continuous functor `U.isOpenEmbedding.functor` on opens; the two
structure sheaves of rings agree, so the identity is an admissible morphism of sheaves of rings
for that pushforward.

The clause `∀ x, ∃ U, x ∈ U ∧ …` presents an open covering of `X` without choosing an index
type, which is how the source phrases the local condition.

The ring and space universes of the ringed space are kept equal, and so is the module universe of
the complexes: that is what makes the sheafification typeclasses which give complexes of
`𝒪_X`-modules cohomology — on `X` and on each of its open subspaces — available by instance search
rather than by hypothesis. This is exactly the case `X.toRingedSpace` with
`X : AlgebraicGeometry.Scheme.{u}`, where the category of modules is `X.Modules`. The restriction
functor itself needs none of that, so `restrictModules` and `restrictComplex` stay polymorphic in
the module universe `w`.

`restrictModules` is `implicit_reducible`, as
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` is: the two are the same
pushforward, the latter at independent universes for the rings and the sections, and their
agreement has to be visible at the transparency instance search uses. `restrictComplex` and the
four predicates are `abbrev`s, so that the identification of `restrictComplex E U` with
`((restrictModules X U).mapHomologicalComplex _).obj E` stays visible at reducible transparency; as
semireducible `def`s, the elaborator unfolds them repeatedly under metavariables.

`StrictlyPerfect.OXMod.{u, w, v}` takes the ring universe first, then the module universe and
the carrier universe, matching `AlgebraicGeometry.RingedSpace.{u, v}`, whose first universe is
also the ring one.

## References

* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Definition 20.46.1 (08C4)](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

universe u d w

variable {X : RingedSpace.{u, u}}

/-- Restriction of sheaves of modules to an open subspace of a ringed space, as the pushforward
along the functor on opens induced by the inclusion. -/
@[implicit_reducible]
public def restrictModules (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    StrictlyPerfect.OXMod.{u, w, u} X ⥤
      StrictlyPerfect.OXMod.{u, w, u} (X.restrict U.isOpenEmbedding) :=
  letI : (U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
    U.isOpenEmbedding.functor_isContinuous
  SheafOfModules.pushforward (F := U.isOpenEmbedding.functor)
    (𝟙 (StrictlyPerfect.structureSheafOfRings (X.restrict U.isOpenEmbedding)))

/-- Restriction to an open subspace does not change the sections of a morphism, so it preserves
zero morphisms. -/
public instance restrictModules_preservesZeroMorphisms (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : (restrictModules.{u, w} X U).PreservesZeroMorphisms where
  map_zero _ _ := by ext _ _; rfl

/-- Restriction of a cochain complex of `𝒪_X`-modules to an open subspace, applied degreewise. -/
public abbrev restrictComplex (E : CochainComplex (StrictlyPerfect.OXMod.{u, w, u} X) ℤ)
    (U : Opens X.carrier) :
    CochainComplex (StrictlyPerfect.OXMod.{u, w, u} (X.restrict U.isOpenEmbedding)) ℤ :=
  ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

/-- A complex of `𝒪_X`-modules is `m`-pseudo-coherent if every point of `X` has an open
neighbourhood on which the complex admits a strictly perfect approximation in degrees at
least `m`: a map from a strictly perfect complex which is an isomorphism on cohomology in every
degree above `m` and an epimorphism on cohomology in degree `m`. -/
@[stacks 08CB "part (1)"]
public abbrev IsPseudoCoherentComplexFrom
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ) (m : ℤ) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ P : CochainComplex
        (StrictlyPerfect.OXMod.{u, u, u} (X.restrict U.isOpenEmbedding)) ℤ,
      StrictlyPerfect.IsStrictlyPerfect P ∧
      ∃ α : P ⟶ restrictComplex E U,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m)

/-- A complex of `𝒪_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
@[stacks 08CB "part (2)"]
public abbrev IsPseudoCoherentComplex
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ) : Prop :=
  ∀ m : ℤ, IsPseudoCoherentComplexFrom E m

/-- An object of the derived category of `𝒪_X`-modules is `m`-pseudo-coherent if it is
represented by an `m`-pseudo-coherent complex. -/
@[stacks 08CB "part (3), m-pseudo-coherent"]
public abbrev IsPseudoCoherentFrom
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X)]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X)) (m : ℤ) : Prop :=
  ∃ K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ,
    IsPseudoCoherentComplexFrom K m ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- An object of the derived category of `𝒪_X`-modules is pseudo-coherent if it is represented by
a pseudo-coherent complex. -/
@[stacks 08CB "part (3), pseudo-coherent"]
public abbrev IsPseudoCoherent
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X)]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X)) : Prop :=
  ∃ K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ,
    IsPseudoCoherentComplex K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

end AlgebraicGeometry.RingedSpace

end
