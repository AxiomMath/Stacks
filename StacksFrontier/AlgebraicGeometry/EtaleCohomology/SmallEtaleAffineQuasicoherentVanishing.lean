module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DenseSubsiteSheafCohomologyTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAssociatedSheafComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLiftVanishing

/-!
# The first étale cohomology of a quasi-coherent module on an affine scheme vanishes

This is Stacks 03DW clause (2) together with Stacks 01XB, in the shape the internal-hom
vanishing of Stacks 061J consumes it: on the **size-bounded** small étale site of an affine
scheme, at coefficients one universe above the sections of the module.

The route has four steps, each of which is proved elsewhere and is only instantiated here.
The first cohomology of a quasi-coherent module on an affine scheme vanishes on the Zariski
site (Stacks 01XB); that transfers to the first cohomology of the associated sheaf on Mathlib's
small étale site (Stacks 03DW clause (2)); the coefficient universe is raised there; and the
vanishing is carried to the size-bounded site, of which Mathlib's is a dense supersite.

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_uliftFunctor_associatedAbelianSheaf`:
  the vanishing, for the associated sheaf of a quasi-coherent module on an affine scheme.

## Implementation notes

The coefficient universe of the conclusion is `u + 1` and that of the input is `u`; the
passage between them is `AlgebraicGeometry.subsingleton_H_uliftFunctor_smallEtale`.  It is not a
transport along an equivalence — the universe-lifting functor on abelian groups is not
essentially surjective — but it does not need to be one: it is a bijection on `Ext` groups, the
lift being exact, fully faithful and injectivity-preserving.

The commutation of the coefficient lift with restriction along the embedding of the bounded site
is `CategoryTheory.Functor.sheafComposeSheafPushforwardIso`, which holds by `Iso.refl`:
restriction is postcomposition on underlying presheaves.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.EtaleCohomology.ConstantTransport

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent]

/-- The universe lift of the associated sheaf on Mathlib's small étale site restricts to the
universe lift of the associated sheaf on the size-bounded one: restriction is postcomposition
on underlying presheaves, so it commutes with the lift on the nose. -/
private def restrictUliftAssociatedIso :
    ((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (topology B S hS) S.smallEtaleTopology).obj
        ((sheafCompose S.smallEtaleTopology
          AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (smallEtaleAssociatedSheaf S F)) ≅
      (sheafCompose (topology B S hS)
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (associatedAbelianSheaf B S hS F) :=
  (sheafCompose (topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso
    (sheafPushforward_smallEtaleAssociatedSheafIso B S hS F)

variable [HasSheafify (topology B S hS) AddCommGrpCat.{u + 1}]

/-- The image of the lifted associated sheaf under the equivalence of sheaf categories between
the two small étale sites is the lifted associated sheaf on Mathlib's site. -/
private def sheafEquivUliftAssociatedIso :
    (Functor.IsDenseSubsite.sheafEquiv (topology B S hS) S.smallEtaleTopology
        (toEtaleSite B S hS) AddCommGrpCat.{u + 1}).functor.obj
        ((sheafCompose (topology B S hS)
          AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (associatedAbelianSheaf B S hS F)) ≅
      (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (smallEtaleAssociatedSheaf S F) :=
  (Functor.IsDenseSubsite.sheafEquiv (topology B S hS) S.smallEtaleTopology
      (toEtaleSite B S hS) AddCommGrpCat.{u + 1}).functor.mapIso
    (restrictUliftAssociatedIso B S hS F).symm ≪≫
    (Functor.IsDenseSubsite.sheafEquiv (topology B S hS) S.smallEtaleTopology
      (toEtaleSite B S hS) AddCommGrpCat.{u + 1}).counitIso.app _

variable [AlgebraicGeometry.IsAffine S]
  [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (S : Type u)) AddCommGrpCat.{u})]

attribute [local instance 0] Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale in
/-- **The first cohomology of the associated sheaf of a quasi-coherent module on an affine
scheme vanishes**, on the size-bounded small étale site and at the coefficient universe one
above the sections.  This is Stacks 03DW clause (2) with Stacks 01XB. -/
theorem subsingleton_sheafH_one_uliftFunctor_associatedAbelianSheaf :
    Subsingleton (Sheaf.H.{w}
      ((sheafCompose (topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (associatedAbelianSheaf B S hS F)) 1) := by
  have h₁ := Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine S F 1 one_pos
  have h₂ := subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup S F 1 one_pos h₁
  have h₃ := subsingleton_H_uliftFunctor_smallEtale.{u + 1, u, u + 1, u} S _ 1 h₂
  refine subsingleton_H_boundedSmallEtale_of_smallEtale_sheaf B S hS _ 1 ?_
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    (sheafEquivUliftAssociatedIso B S hS F).symm 1 h₃

end AlgebraicGeometry.SmallEtale

end
