module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# The associated sheaf on the two small étale sites

A quasi-coherent module `F` on a scheme `S` has an associated abelian sheaf on each of the two
small étale sites of `S`:

* on the size-bounded site of Stacks 021B,
  `AlgebraicGeometry.SmallEtale.associatedAbelianSheaf`, the abelian sheaf underlying the
  associated module `Fᵃ`;
* on Mathlib's small étale site, `AlgebraicGeometry.smallEtaleAssociatedSheaf`.

This file identifies the second, restricted along the embedding of the first, with the first.

The content is that the two are the same presheaf.  Each is a restriction of the single
presheaf `AlgebraicGeometry.quasiCoherentPresheafFunctor S F`, which sends a scheme over `S` to
the global sections of the pullback of `F`: the bounded one along
`AlgebraicGeometry.SmallEtale.toOver`, Mathlib's along `AlgebraicGeometry.Scheme.Etale.forget`.
Composing the embedding of the bounded site with the latter gives the former on the nose, so the
comparison is an equality of presheaves, and the only step with content is Stacks 070S, that `Fᵃ`
is the sections presheaf — `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf`.

## Main results

* `AlgebraicGeometry.SmallEtale.toEtaleSite_comp_etaleForget`: the embedding of the bounded
  small étale site into Mathlib's, followed by the forgetful functor to schemes over `S`, is the
  forgetful functor of the bounded site.
* `AlgebraicGeometry.SmallEtale.sheafPushforward_smallEtaleAssociatedSheafIso`: the associated
  sheaf on Mathlib's small étale site restricts to the associated sheaf on the bounded one.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The embedding of the size-bounded small étale site into Mathlib's, followed by the
forgetful functor to schemes over `S`, is the forgetful functor of the bounded site.**  Both
send an object to its underlying scheme with its structure morphism to `S`, and a morphism to
the underlying morphism of schemes. -/
theorem toEtaleSite_comp_etaleForget :
    toEtaleSite B S hS ⋙ Scheme.Etale.forget S = toOver B S hS := rfl

variable (F : S.Modules) [F.IsQuasicoherent]

/-- **The associated sheaf on Mathlib's small étale site restricts to the associated sheaf on
the size-bounded one.**  Both are the sections presheaf of `F` restricted along the forgetful
functor of the bounded site, by `toEtaleSite_comp_etaleForget`; the identification of the
associated module with the sections presheaf is Stacks 070S. -/
def sheafPushforward_smallEtaleAssociatedSheafIso :
    ((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
        (topology B S hS) S.smallEtaleTopology).obj (smallEtaleAssociatedSheaf S F) ≅
      associatedAbelianSheaf B S hS F :=
  (SheafOfModules.toSheaf (structureSheaf B S hS)).mapIso
    (associatedModuleIsoSectionsSheaf B S hS F).symm

end AlgebraicGeometry.SmallEtale

end
