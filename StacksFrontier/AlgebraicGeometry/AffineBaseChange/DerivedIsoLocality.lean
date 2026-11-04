module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Being an isomorphism in `D(𝒪_X)` is local on an open covering of a scheme

Let `X` be a scheme and let `U : I → X.Opens` be an open covering. Restriction of
`𝒪_X`-modules along the open immersion `(U i).ι` is exact, so it induces a functor
`D(𝒪_X) ⥤ D(𝒪_{U i})`. This file records that the resulting family of functors jointly
reflects isomorphisms: a morphism of `D(𝒪_X)` whose restriction to each `U i` is an
isomorphism is an isomorphism.

The abelian statement — the same for a morphism of `𝒪_X`-modules — is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`. The passage to the derived
category is `DerivedCategory.isIso_iff`, which reduces invertibility to invertibility of every
homology map, together with
`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`, which says that an exact functor
inverts a morphism of derived categories exactly when it inverts each of its homology maps.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_derived_of_isIso_restrict` — the criterion
  for an arbitrary open covering.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_derived_of_isIso_restrict_affineOpens` — the
  specialization to the covering of `X` by all of its affine opens, which is the form a
  statement proved affine-locally is consumed at.

## Implementation notes

`D(𝒪_X)` and each `D(𝒪_{U i})` are instance arguments, so a consumer may read the statement at
whatever model of the derived category it already works in; the two universes are independent
because nothing below compares objects of `D(𝒪_X)` with objects of `D(𝒪_{U i})` other than
through `Functor.mapDerivedCategory`.

An equivalent statement for the *slice-site* model of restriction is
`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`. The two are not
interchangeable: that one restricts along `SheafOfModules.overFunctor` to the site of opens
contained in `U`, whereas `AlgebraicGeometry.Scheme.Modules.restrictFunctor` lands in the
modules of the open subscheme `U`, which is the model every statement about dualizing complexes
on a scheme in this development is phrased in.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w w'

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-- **Being an isomorphism in `D(𝒪_X)` is local on an open covering.** A morphism of the
derived category of `𝒪_X`-modules whose restriction to every member of an open covering of the
scheme `X` is an isomorphism is itself an isomorphism. -/
theorem isIso_derived_of_isIso_restrict {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    {I : Type*} (U : I → X.Opens) (hU : IsOpenCover U)
    [∀ i, HasDerivedCategory.{w'} (U i).toScheme.Modules]
    {M N : DerivedCategory X.Modules} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_restrict _ U hU fun i => ?_
  exact ((Scheme.Modules.restrictFunctor (U i).ι).isIso_mapDerivedCategory_map_iff φ).mp (h i) n

/-- The covering of a scheme by all of its affine opens, as an open covering. -/
theorem isOpenCover_affineOpens (X : Scheme.{u}) :
    IsOpenCover (fun V : X.affineOpens => (V : X.Opens)) :=
  IsOpenCover.mk (iSup_affineOpens_eq_top X)

/-- **An affine-local criterion.** A morphism of `D(𝒪_X)` whose restriction to every affine open
of the scheme `X` is an isomorphism is an isomorphism. -/
theorem isIso_derived_of_isIso_restrict_affineOpens {X : Scheme.{u}}
    [HasDerivedCategory.{w} X.Modules]
    [∀ V : X.affineOpens, HasDerivedCategory.{w'} (V : X.Opens).toScheme.Modules]
    {M N : DerivedCategory X.Modules} (φ : M ⟶ N)
    (h : ∀ V : X.affineOpens,
      IsIso ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).mapDerivedCategory.map φ)) :
    IsIso φ :=
  isIso_derived_of_isIso_restrict _ (isOpenCover_affineOpens X) φ h

end Stacks.AlgebraicGeometry.AffineBaseChange

end
