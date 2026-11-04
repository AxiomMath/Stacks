module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekDerivedTorsion
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleAdjunction

import StacksCore.Tactic.StacksAttribute

/-!
# `f_!` on derived categories with coefficients preserves torsion cohomology

Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let `Λ` be a ring. The functor
`f_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` of Stacks 0F5N sends a complex with torsion cohomology
sheaves to a complex with torsion cohomology sheaves. This is Stacks 0GJX.

## Main results

In the namespace `AlgebraicGeometry.SmallEtale`:

* `moduleTorsionSheafProperty_fShriekMod_obj` — the direct image with compact support with
  coefficients in `Λ` sends torsion étale sheaves of `Λ`-modules to torsion étale sheaves of
  `Λ`-modules.
* `moduleTorsionCohomologyProperty_moduleFShriekDerivedFunctor_fShriekMod` — the functor
  `f_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` sends complexes with torsion cohomology sheaves to
  complexes with torsion cohomology sheaves.

## Implementation notes

The two statements are
`AlgebraicGeometry.SmallEtale.moduleTorsionSheafProperty_fShriekMod` and
`AlgebraicGeometry.SmallEtale.moduleTorsionCohomologyProperty_moduleFShriekDerivedFunctor` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekDerivedTorsion` read at the actual direct image with
compact support with coefficients in `Λ`, the functor
`AlgebraicGeometry.SmallEtale.fShriekMod`, with
`AlgebraicGeometry.SmallEtale.fShriekModForgetIso` for the comparison with `f_!` on underlying
abelian sheaves. Those statements take the `Λ`-linear lift of `f_!` as data; here nothing is
assumed beyond `f` being locally quasi-finite and `Λ` being a ring, which are the hypotheses of
the source.

The `CategoryTheory.Functor.IsLeftAdjoint` hypothesis carried by the derived functor of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekDerivedTorsion` is discharged by
`AlgebraicGeometry.SmallEtale.fShriekMod_isLeftAdjoint`, i.e. by Stacks 0F59 part (3). It is
kept rather than removed because the functor the source speaks of is the `f_!` of Stacks 0F5N,
which is constructed there as the left adjoint of `Rf^!`: the adjoint is what makes the
statement be about that functor, and
`AlgebraicGeometry.SmallEtale.moduleFShriekRUpperShriekAdjunction` exhibits it.

## References

* [Stacks Project, Tag 0GJX](https://stacks.math.columbia.edu/tag/0GJX)
* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F59](https://stacks.math.columbia.edu/tag/0F59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The direct image with compact support with coefficients in a ring `Λ` sends torsion étale
sheaves of `Λ`-modules to torsion étale sheaves of `Λ`-modules: on underlying abelian sheaves it
is `f_!`, which preserves torsion by the stalk description of Stacks 0F5F. -/
@[stacks 0GJX "the sheaf-level input, for f_! with coefficients in Λ itself"]
public theorem moduleTorsionSheafProperty_fShriekMod_obj (F : ModuleSheaf.{u, v, r} B X Λ)
    (hF : moduleTorsionSheafProperty.{u, v, r} B X Λ F) :
    moduleTorsionSheafProperty.{u, v, r} B Y Λ ((fShriekMod.{u, v, r} B Λ f).obj F) :=
  moduleTorsionSheafProperty_fShriekMod.{u, v, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
    (fShriekModForgetIso.{u, v, r} B Λ f) F hF

variable [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{w} (ModuleSheaf.{u, v, r} B Y Λ)]

/-- **Stacks 0GJX.** Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let `Λ` be
a ring. The functor `f_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` of Stacks 0F5N sends complexes with
torsion cohomology sheaves to complexes with torsion cohomology sheaves.

The functor `f_!` with coefficients in `Λ` is exact, so the cohomology of `f_! K` is `f_!` of the
cohomology of `K`; torsion of a sheaf of `Λ`-modules is torsion of its underlying abelian sheaf,
which is the image under `f_!` of the underlying abelian sheaf of the cohomology; and `f_!`
preserves torsion abelian sheaves, which the source reads off the stalk description of `f_!` in
Stacks 0F5F. -/
@[stacks 0GJX "f_! on D(X_étale, Λ) ⟶ D(Y_étale, Λ) sends complexes with torsion cohomology \
sheaves to complexes with torsion cohomology sheaves"]
public theorem moduleTorsionCohomologyProperty_moduleFShriekDerivedFunctor_fShriekMod
    (K : DerivedCategory (ModuleSheaf.{u, v, r} B X Λ))
    (hK : moduleTorsionCohomologyProperty.{u, v, w, r} B X Λ K) :
    moduleTorsionCohomologyProperty.{u, v, w, r} B Y Λ
      ((moduleFShriekDerivedFunctor.{u, v, w, r} B Λ f (fShriekMod.{u, v, r} B Λ f)
        (fShriekModForgetIso.{u, v, r} B Λ f)).obj K) :=
  moduleTorsionCohomologyProperty_moduleFShriekDerivedFunctor.{u, v, w, r} B Λ f
    (fShriekMod.{u, v, r} B Λ f) (fShriekModForgetIso.{u, v, r} B Λ f) K hK

end AlgebraicGeometry.SmallEtale

end
