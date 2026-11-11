module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAlgebraMultiplication
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional

/-!
# Relative dualizing complexes

Let `f : X ⟶ S` be flat and locally of finite presentation and let `W ⊆ X ×_S X` be an open
through which the relative diagonal factors as a closed immersion `Δ : X ⟶ W`. A relative
dualizing complex is a pair `(K, ξ)` consisting of an object `K` of `D(𝒪_X)` and a map
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` in `D(𝒪_W)` such that `K` is `S`-perfect and `ξ` identifies
`Δ_*𝒪_X` with `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen` is an open `W ⊆ X ×_S X` together with the
  factorization of the relative diagonal through it as a closed immersion.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalAction` is the map
  `Δ_*𝒪_X ⟶ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)` that `ξ` defines.
* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex` is the property of being a relative
  dualizing complex, with `S`-perfectness read against a family `Dten` of derived tensor
  certificates. It is a generalisation of Stacks 0E2T, which it equals at a genuine family
  (`AlgebraicGeometry.Scheme.Hom.isRelativeDualizingComplex_iff_isRelativeDualizingPair`);
  Stacks 0E2T itself is `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingPair`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativeDualizingComplex_iff` unfolds the predicate into its
  two defining conditions.

## Implementation notes

The second condition of the source is a condition on `ξ`, not the assertion that some
isomorphism exists, so it needs the morphism that `ξ` induces. `Δ_*𝒪_X` is a sheaf of
`𝒪_W`-algebras, and that morphism is the image of its derived multiplication followed by `ξ`
under the tensor–internal-hom bijection of Stacks 08DI.

`L pr₁^*K|_W` is the derived pullback along the composite `W → X ×_S X → X`: restriction to an
open is pullback along its open immersion, so the composite is the source's `L pr₁^*K|_W`. The
module categories of `D(𝒪_W)` used by relative perfectness, by the derived pullback and by the
derived internal hom agree on the nose, so no comparison isomorphism intervenes.

The open `W` is a parameter, as in the source, which fixes it before speaking of the pair; the
type of `ξ` mentions it. That the condition does not depend on the choice of `W` is a theorem
about the notion and is not part of the definition.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect

universe d' u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- An open `W ⊆ X ×_S X` through which the relative diagonal `Δ_{X/S} : X ⟶ X ×_S X` factors
as a closed immersion `Δ : X ⟶ W`. -/
structure DiagonalOpen where
  /-- The open subscheme `W` of `X ×_S X`. -/
  W : Scheme.{u}
  /-- The open immersion exhibiting `W` as an open of `X ×_S X`. -/
  ι : W ⟶ Limits.pullback f f
  /-- `ι` is an open immersion. -/
  isOpenImmersion : IsOpenImmersion ι
  /-- The factorization `Δ : X ⟶ W` of the relative diagonal. -/
  diag : X ⟶ W
  /-- `Δ` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion diag
  /-- `Δ` followed by the open immersion is the relative diagonal of `f`. -/
  fac : diag ≫ ι = Limits.pullback.diagonal f

namespace DiagonalOpen

variable {f} (D : DiagonalOpen f)

/-- The first projection restricted to `W`, that is `pr₁|_W : W ⟶ X`. -/
abbrev proj : D.W ⟶ X := D.ι ≫ Limits.pullback.fst f f

/-- `Δ_*𝒪_X`, the pushforward of the structure sheaf of `X` along `Δ`, as a sheaf of
commutative `𝒪_W`-algebras. -/
abbrev diagonalAlgebra : Stacks.RelativeSpec.AlgebraSheaf D.W :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebra D.diag

/-- `Δ_*𝒪_X` as an object of `D(𝒪_W)`. -/
abbrev diagonalObject :
    DerivedCategory (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) :=
  DerivedCategory.Q.obj (Stacks.RelativeSpec.AlgebraSheaf.single D.diagonalAlgebra)

/-- `L pr₁^*K|_W` for `K` an object of `D(𝒪_X)`: the derived pullback of `K` along
`pr₁|_W : W ⟶ X`. -/
abbrev derivedPullbackProj (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    DerivedCategory (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    D.proj.toLRSHom.toShHom).obj K

/-! The universes of the site `Opens W` and of the sections of `𝒪_W` coincide, so the
additivity of the tensor product and the existence of the total tensor complexes are named
rather than synthesized: the search would have to solve `max ?u ?v =?= u` with both unknown. -/

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The map that `ξ` defines**, `Δ_*𝒪_X ⟶ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`: the image
under the tensor–internal-hom bijection of Stacks 08DI of the derived multiplication of the
sheaf of algebras `Δ_*𝒪_X` followed by `ξ`. -/
def diagonalAction (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    D.diagonalObject ⟶
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
        (D.derivedPullbackProj K) :=
  (Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
      D.diagonalObject (D.derivedPullbackProj K)).symm
    (Stacks.RelativeSpec.AlgebraSheaf.derivedMul D.diagonalAlgebra ≫ ξ)

end DiagonalOpen

variable
  [HasDerivedCategory.{d'}
    (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- A relative dualizing complex for a flat, locally finitely presented morphism `f : X ⟶ S`,
relative to an open `W ⊆ X ×_S X` through which the relative diagonal factors as a closed
immersion `Δ : X ⟶ W`, read against a family `Dten` of derived tensor certificates on
`(X, f^{-1}𝒪_S)`: a pair `(K, ξ)` consisting of an object `K` of `D(𝒪_X)` and a map
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` in `D(𝒪_W)` such that `K` is perfect relative to `S` in the sense
of `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` at `Dten`, and `ξ` defines an isomorphism
of `Δ_*𝒪_X` with `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`.

This is a generalisation of Stacks 0E2T, not the definition itself: the underived tensor
product of a certificate is free data, so at a general `Dten` the first condition is weaker
than `S`-perfectness (Stacks 0DI0); at the zero certificate it is pseudo-coherence alone. At a
family whose underived tensor products are those of sheaves of modules it is Stacks 0E2T, by
`AlgebraicGeometry.Scheme.Hom.isRelativeDualizingComplex_iff_isRelativeDualizingPair`.
Stacks 0E2T is `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingPair`. -/
structure IsRelativeDualizingComplex [Flat f] [LocallyOfFinitePresentation f]
    (Dten : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (D : DiagonalOpen f) (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) : Prop where
  /-- Condition (1): `K` is `S`-perfect. -/
  isPerfectRelativeTo : IsPerfectRelativeTo f Dten K
  /-- Condition (2): `ξ` defines an isomorphism of `Δ_*𝒪_X` with
  `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`. -/
  isIso_diagonalAction : IsIso (D.diagonalAction K ξ)

/-- Characterization of a relative dualizing complex by relative perfectness of `K` and the
isomorphism condition on the map that `ξ` defines. -/
theorem isRelativeDualizingComplex_iff [Flat f] [LocallyOfFinitePresentation f]
    (Dten : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (D : DiagonalOpen f) (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    IsRelativeDualizingComplex f Dten D K ξ ↔
      IsPerfectRelativeTo f Dten K ∧ IsIso (D.diagonalAction K ξ) :=
  ⟨fun h => ⟨h.isPerfectRelativeTo, h.isIso_diagonalAction⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

end AlgebraicGeometry.Scheme.Hom

end
