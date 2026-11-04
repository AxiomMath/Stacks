module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkFunctorDecomposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks and exactness of the proper-support direct image of a quasi-finite separated morphism

Let `f : X ⟶ Y` be a separated and locally quasi-finite morphism of a big étale site. The direct
image with proper support `f_!` of Stacks 0F4X — the subsheaf of `f_*F` of sections whose support
is proper over the base — has, at a geometric point `ȳ` of `Y`, the stalk
`(f_!F)_ȳ = ⊕_{f(x̄) = ȳ} F_x̄`, functorially in `F`, and is an exact functor. This is
Stacks 0F57.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properSupportStalkFunctorIso` — the stalk decomposition
  `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄` as an isomorphism of functors in `F`.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportFunctor_exact` — `f_!` is exact.

## Implementation notes

For a separated locally quasi-finite morphism the proper-support direct image is the
sheafification of the finite-support direct image presheaf, which is Stacks 0F6N
(`AlgebraicGeometry.SmallEtale.fShriekFunctorIsoProperSupport`). Both parts are transported along
that identification from the corresponding statements for the sheafified model, which is
Stacks 0F5F: the stalk decomposition there is the germ decomposition of Stacks 0F6P, and
exactness there is deduced from the stalk decomposition through the stalk criterion of
Stacks 03PU. This replaces the proof of the source, which reaches the same stalk computation
through the discreteness of the geometric fibre `X_ȳ`.

Abelian sheaves take values in `AddCommGrpCat.{max (u + 1) v}`, as for the sheafified model.
The source's hypothesis "locally quasi-finite" is the conjunction of Mathlib's
`LocallyOfFiniteType` and `LocallyQuasiFinite`, the latter not including finite type.

## References

* [Stacks Project, Tag 0F57](https://stacks.math.columbia.edu/tag/0F57)
* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]

/-- **Stacks 0F57, part (1).** For a separated locally quasi-finite morphism `f : X ⟶ Y` and a
geometric point `ȳ` of `Y`, the stalk at `ȳ` of the proper-support direct image `f_!F` is the
direct sum of the stalks of `F` at the geometric points `x̄` of `X` with `f(x̄) = ȳ`,
functorially in the abelian étale sheaf `F`. -/
@[stacks 0F57 "part (1)"]
public def properSupportStalkFunctorIso (s : GeometricPoint Y.obj) :
    properSupportFunctor.{u, max (u + 1) v} B f ⋙
        (geometricPointSitePoint B Y.obj Y.property s).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v}) ≅
      Adjunction.sigmaFamily (fun x : GeometricFiberPoint B f s =>
        (geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})) :=
  Functor.isoWhiskerRight (fShriekFunctorIsoProperSupport.{u, v} B f).symm _ ≪≫
    fShriekStalkFunctorIso.{u, v} B f s

/-- **Stacks 0F57, part (2).** For a separated locally quasi-finite morphism the proper-support
direct image `f_!` on abelian étale sheaves is an exact functor. -/
@[stacks 0F57 "part (2)", sga "4 XVII 6.1.4" "more general"]
public theorem properSupportFunctor_exact :
    exactFunctor _ _ (properSupportFunctor.{u, max (u + 1) v} B f) :=
  let e := fShriekFunctorIsoProperSupport.{u, v} B f
  have hex := (exactFunctor_iff _).mp (fShriekFunctor_exact.{u, v} B f)
  have := hex.1
  have := hex.2
  (exactFunctor_iff _).2
    ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

end AlgebraicGeometry.SmallEtale
