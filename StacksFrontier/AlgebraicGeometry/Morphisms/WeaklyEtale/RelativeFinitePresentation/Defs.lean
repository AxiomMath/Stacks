module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.RingTheory.FinitePresentation.Relative
public import StacksCore.Tactic.StacksAttribute

/-!
# Relatively finitely presented sheaves

A sheaf of modules on a scheme is of finite presentation relative to a base scheme if, on
suitable affine open covers of the base and of their inverse images, its modules of sections are
finitely presented relative to the corresponding rings of functions on the base.

This file also packages the standing situation in which relative finite presentation is studied
along a short exact sequence.

## Main definitions

* `AlgebraicGeometry.IsFinitelyPresentedRelative` is finite presentation of a sheaf of modules
  relative to a morphism of schemes.
* `AlgebraicGeometry.RelativeFinitePresentationExactSequenceSituation` packages a locally finite
  type morphism together with a short exact sequence of quasi-coherent modules on its source.

## Implementation notes

The affine coverings are represented by families of affine open subsets whose suprema are the
opens they cover. The containment of each source open in the relevant inverse image supplies the
canonical algebra structure on its ring of functions. The definition makes sense for an
arbitrary sheaf of modules and morphism; the Stacks Project uses it for a quasi-coherent sheaf
and a locally finite type morphism.

In the situation structure, the displayed sequence beginning and ending in zero is represented by
a `ShortComplex` together with its `ShortExact` property. Its three objects are the sheaves
denoted by `F'`, `F`, and `F''` in the source, respectively.

## References

* [Stacks Project, Tag 05H1](https://stacks.math.columbia.edu/tag/05H1)
* [Stacks Project, Tag 09TD](https://stacks.math.columbia.edu/tag/09TD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A sheaf of modules `M` on `X` is finitely presented relative to `S` if there is an affine
open cover of `S` and, over each member, an affine open cover of its inverse image such that
the corresponding module of sections of `M` is finitely presented relative to the ring of
functions on the base open. -/
@[stacks 05H1]
abbrev IsFinitelyPresentedRelative {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∃ (J : Type u) (V : J → S.Opens), IsOpenCover V ∧ (∀ j, IsAffineOpen (V j)) ∧
    ∀ j, ∃ (I : Type u) (U : I → X.Opens) (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
      (∀ i, IsAffineOpen (U i)) ∧
        ∀ i,
          letI : Algebra Γ(S, V j) Γ(X, U i) :=
            (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom.toAlgebra;
          Module.FinitePresentationRel Γ(S, V j) Γ(X, U i) Γ(M, U i)

/-- The standing situation of a locally finite type morphism `X ⟶ S` and a short exact
sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of quasi-coherent modules on `X`. -/
structure RelativeFinitePresentationExactSequenceSituation where
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The morphism from the source to the base. -/
  f : X ⟶ S
  /-- The morphism is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType f]
  /-- The three-term complex `F' ⟶ F ⟶ F''`. -/
  sequence : ShortComplex X.Modules
  /-- The complex `sequence` is short exact. -/
  shortExact : sequence.ShortExact
  /-- The left-hand module `F'` is quasi-coherent. -/
  [leftQuasicoherent : sequence.X₁.IsQuasicoherent]
  /-- The middle module `F` is quasi-coherent. -/
  [middleQuasicoherent : sequence.X₂.IsQuasicoherent]
  /-- The right-hand module `F''` is quasi-coherent. -/
  [rightQuasicoherent : sequence.X₃.IsQuasicoherent]

attribute [instance]
  RelativeFinitePresentationExactSequenceSituation.locallyOfFiniteType
  RelativeFinitePresentationExactSequenceSituation.leftQuasicoherent
  RelativeFinitePresentationExactSequenceSituation.middleQuasicoherent
  RelativeFinitePresentationExactSequenceSituation.rightQuasicoherent

end AlgebraicGeometry
