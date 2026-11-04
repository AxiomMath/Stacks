module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Flattening a module by blowing up an algebraic space

Let `A` be a quasi-compact and quasi-separated algebraic space, let `f : X ⟶ A` be locally of
finite presentation with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite
type and let `U ⊆ A` be a quasi-compact open subspace over which `F` is of finite presentation
and flat.  Stacks 087C asserts that there is a `U`-admissible blowup `A' ⟶ A` such that the
strict transform of `F` is an `𝒪_{X ×_A A'}`-module of finite presentation, flat over `A'`.

This file fixes the vocabulary in which that statement and its proof are written.

## Main definitions

* `AlgebraicGeometry.Space.OpenSubspaces.toSpace` and
  `AlgebraicGeometry.Space.OpenSubspaces.toSpaceι`: an open subspace as an algebraic space, with
  its inclusion.
* `AlgebraicGeometry.Space.restrictOver`: the restriction `X_U = X ×_A U` of `f : X ⟶ A` over an
  open subspace `U ⊆ A`, with its inclusion `AlgebraicGeometry.Space.restrictOverι` into `X` and
  its structure morphism `AlgebraicGeometry.Space.restrictOverHom` to `U`.  The module `F_U` of
  the source is the pullback of `F` along the inclusion.
* `AlgebraicGeometry.Space.IsFlatteningBlowup`: `b : A' ⟶ A` is the blowup of `A` in a
  finitely presented closed subspace `Z` avoiding `U`, after which the strict transform of `F`
  is of finite presentation and flat over `A'`.

## Main results

* `AlgebraicGeometry.Space.IsFlatteningBlowup.isAdmissibleBlowup`: a flattening blowup is
  `U`-admissible.

## Implementation notes

The centre `Z` is part of the data of a flattening blowup and not only of the proof that the
blowup is admissible, because the strict transform of Stacks 0862 depends on the centre and not
only on the morphism `A' ⟶ A`.  Finite presentation of a module is
`SheafOfModules.IsFinitePresentationOnSite` on the small étale site, and flatness over the base
is `AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV.

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {A X : AlgebraicSpaces B S hS}

/-- An open subspace of an algebraic space, as an algebraic space. -/
abbrev OpenSubspaces.toSpace (U : OpenSubspaces B S hS A.1) : AlgebraicSpaces B S hS :=
  ⟨U.1.toFunctor, U.2.1⟩

/-- The inclusion of an open subspace, as a morphism of algebraic spaces. -/
abbrev OpenSubspaces.toSpaceι (U : OpenSubspaces B S hS A.1) : U.toSpace ⟶ A :=
  ObjectProperty.homMk U.1.ι

/-- The restriction `X_U = X ×_A U` of `f : X ⟶ A` over an open subspace `U ⊆ A`. -/
abbrev restrictOver (f : X ⟶ A) (U : OpenSubspaces B S hS A.1) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS f U.toSpaceι

/-- The inclusion `X_U ⟶ X`. -/
abbrev restrictOverι (f : X ⟶ A) (U : OpenSubspaces B S hS A.1) : restrictOver f U ⟶ X :=
  ObjectProperty.homMk (pullback.fst f.hom U.toSpaceι.hom)

/-- The restriction `f_U : X_U ⟶ U`. -/
abbrev restrictOverHom (f : X ⟶ A) (U : OpenSubspaces B S hS A.1) :
    restrictOver f U ⟶ U.toSpace :=
  ObjectProperty.homMk (pullback.snd f.hom U.toSpaceι.hom)

/-- **A flattening blowup.**  `b : A' ⟶ A` is the blowup of `A` in a finitely presented closed
subspace `Z` whose points avoid those of `U` -- so a `U`-admissible blowup -- such that the strict
transform of `F` with respect to `b` is an `𝒪_{X ×_A A'}`-module of finite presentation, flat
over `A'`. -/
abbrev IsFlatteningBlowup {A' : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (F : Modules.{u, u} B S hS X.1 X.2) (U : OpenSubspaces B S hS A.1)
    (Z : ClosedSubspaces B S hS A.1) (b : A' ⟶ A) : Prop :=
  IsFinitePresentation B S hS Z.1.ι ∧
    Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
    IsBlowupAlong B S hS Z b ∧
    (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F).IsFinitePresentationOnSite ∧
    IsFlatOver B S hS (strictTransformPullback B S hS f b).2
      (strictTransformPullbackToBlowUp B S hS f b).hom
      (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F)

/-- A flattening blowup is a `U`-admissible blowup in the sense of Stacks 086B. -/
theorem IsFlatteningBlowup.isAdmissibleBlowup {A' : AlgebraicSpaces B S hS} {f : X ⟶ A}
    {F : Modules.{u, u} B S hS X.1 X.2} {U : OpenSubspaces B S hS A.1}
    {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A} (h : IsFlatteningBlowup f F U Z b) :
    IsAdmissibleBlowup B S hS U b :=
  ⟨Z, h.1, h.2.1, h.2.2.1⟩

end AlgebraicGeometry.Space

end
