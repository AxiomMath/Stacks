module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical

/-!
# Relative dualizing complexes, at the genuine notion of relative perfectness

Let `f : X ⟶ S` be flat and locally of finite presentation and let `W ⊆ X ×_S X` be an open
through which the relative diagonal factors as a closed immersion `Δ : X ⟶ W`. A relative
dualizing complex is a pair `(K, ξ)` consisting of an object `K` of `D(𝒪_X)` and a map
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` in `D(𝒪_W)` such that

1. `K` is `S`-perfect, and
2. `ξ` defines an isomorphism of `Δ_*𝒪_X` with `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`.

This is Stacks 0E2T. Every object in it is the canonical one of the library, and no parameter
other than the source's data `f`, `W`, `K` and `ξ` enters.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingPair` is the property of a pair `(K, ξ)` of
  being a relative dualizing complex, Stacks 0E2T.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativeDualizingPair_iff` unfolds the predicate into its two
  defining conditions.
* `AlgebraicGeometry.Scheme.Hom.isRelativeDualizingComplex_iff_isRelativeDualizingPair`: the
  predicate `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex`, stated over a family of
  derived tensor certificates on `(X, f^{-1}𝒪_S)`, is this one at every family whose underived
  tensor products are those of sheaves of modules, in particular at the canonical family.

## Implementation notes

*Condition (1).* `S`-perfectness is `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, Stacks
0DI0: `K` is pseudo-coherent (Stacks 08CB) and, after restriction of scalars along
`f^{-1}𝒪_S ⟶ 𝒪_X`, locally has finite Tor dimension on `(X, f^{-1}𝒪_S)` (Stacks 08CG), read
against the derived tensor product `Stacks.Cohomology.TorAmplitude.derTensor` of Stacks 06YU on
each open subspace. That derived tensor product is computed on K-flat representatives from the
tensor product of sheaves of modules, so no tensor product enters as a parameter. The models of
the derived categories of `(X, f^{-1}𝒪_S)` and of its open subspaces are arbitrary.

*Condition (2) and the objects it involves.* They are those of
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex`, used as they are:

* `Δ_*𝒪_X` is `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalObject`, the pushforward of the
  structure sheaf along `Δ` as a sheaf of `𝒪_W`-algebras, placed in degree zero in `D(𝒪_W)`;
* `L pr₁^*K|_W` is `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.derivedPullbackProj`, the derived
  pullback `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` of Stacks 06YJ
  along `W → X ×_S X → X`. Restriction to the open `W` is pullback along its open immersion,
  which is exact and agrees with its derived pullback
  (`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback`), and the derived
  pullback of the composite is the composite of the derived pullbacks by Stacks 0D5S
  (`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`);
* `R SheafHom_{𝒪_W}` is `Stacks.SheafOfModules.derivedSheafHom`, and the map that `ξ` defines is
  `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalAction`, the image under the
  tensor–internal-hom bijection of Stacks 08DI of the derived multiplication of `Δ_*𝒪_X`
  followed by `ξ`.

These live in the derived categories of `𝒪_X` and `𝒪_W` at the model
`CategoryTheory.HasDerivedCategory.standard`, the one in which the derived pullback and the
derived internal hom of the library are stated; `K` is therefore an object of `D(𝒪_X)` at that
model.

Flatness and local finite presentation of `f` are the standing hypotheses of the source; they
are instance arguments.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d' u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- **Stacks 0E2T.** A relative dualizing complex for a flat, locally finitely presented
morphism `f : X ⟶ S`, relative to an open `W ⊆ X ×_S X` through which the relative diagonal
factors as a closed immersion `Δ : X ⟶ W`: a pair `(K, ξ)` consisting of an object `K` of
`D(𝒪_X)` and a map `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` in `D(𝒪_W)` such that `K` is `S`-perfect
(Stacks 0DI0) and `ξ` defines an isomorphism of `Δ_*𝒪_X` with
`R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`. -/
@[stacks 0E2T]
structure IsRelativeDualizingPair [Flat f] [LocallyOfFinitePresentation f]
    (D : DiagonalOpen f) (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) : Prop where
  /-- Condition (1): `K` is `S`-perfect. -/
  isRelativelyPerfect : f.IsRelativelyPerfect K
  /-- Condition (2): `ξ` defines an isomorphism of `Δ_*𝒪_X` with
  `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`. -/
  isIso_diagonalAction : IsIso (D.diagonalAction K ξ)

/-- A pair `(K, ξ)` is a relative dualizing complex exactly when `K` is `S`-perfect and the map
that `ξ` defines is an isomorphism. -/
theorem isRelativeDualizingPair_iff [Flat f] [LocallyOfFinitePresentation f]
    (D : DiagonalOpen f) (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    IsRelativeDualizingPair f D K ξ ↔
      f.IsRelativelyPerfect K ∧ IsIso (D.diagonalAction K ξ) :=
  ⟨fun h => ⟨h.isRelativelyPerfect, h.isIso_diagonalAction⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/-- **At a family of genuine tensor certificates the parameterised predicate is Stacks 0E2T.**
When the underived tensor product of every member of `Dten` is that of sheaves of modules over
`f^{-1}𝒪_S`, relative perfectness read against `Dten` is relative perfectness, by
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_iff_isRelativelyPerfect`, and the second
condition is the same in both predicates. -/
theorem isRelativeDualizingComplex_iff_isRelativeDualizingPair [Flat f]
    [LocallyOfFinitePresentation f]
    (Dten : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f Dten)
    (D : DiagonalOpen f) (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    IsRelativeDualizingComplex f Dten D K ξ ↔ IsRelativeDualizingPair f D K ξ := by
  rw [isRelativeDualizingComplex_iff, isRelativeDualizingPair_iff,
    isPerfectRelativeTo_iff_isRelativelyPerfect f Dten hD]

end AlgebraicGeometry.Scheme.Hom

end
