module

public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre

/-!
# Finite locally constant abelian sheaves on the small étale site

Let `B` be a big étale site containing a scheme `S`. The finite locally constant sheaves of
abelian groups on the small étale site `AlgebraicGeometry.SmallEtale.topology` of `S` form a weak
Serre subcategory of all abelian sheaves, with coefficients in `AddCommGrpCat.{max (u + 1) w}`.
This is the site-generic
`Stacks.ConstantSheaf.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf` at the universes of
the small étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.hasSheafify_addCommGrp` and
  `AlgebraicGeometry.SmallEtale.hasSheafifyOver_addCommGrp`: abelian presheaves on the small
  étale site of `S`, and on its localization at an object, can be sheafified with coefficients in
  `AddCommGrpCat.{max (u + 1) w}` for every `w`.
* `AlgebraicGeometry.SmallEtale.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf`: the finite
  locally constant abelian sheaves on the small étale site of `S`, at those coefficients, form a
  weak Serre subcategory.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on the small étale site of `S` can be sheafified with coefficients in
`AddCommGrpCat.{max (u + 1) w}`. -/
public theorem hasSheafify_addCommGrp :
    HasSheafify (topology B S hS) AddCommGrpCat.{max (u + 1) w} :=
  have : EssentiallySmall.{max (u + 1) w} (SmallEtale B S hS) := inferInstance
  hasSheafifyEssentiallySmallSite (topology B S hS) AddCommGrpCat.{max (u + 1) w}

/-- Abelian presheaves on the localization of the small étale site of `S` at one of its objects
can be sheafified with coefficients in `AddCommGrpCat.{max (u + 1) w}`. -/
public theorem hasSheafifyOver_addCommGrp (U : SmallEtale B S hS) :
    HasSheafify ((topology B S hS).over U) AddCommGrpCat.{max (u + 1) w} :=
  have : EssentiallySmall.{max (u + 1) w} (Over U) := inferInstance
  hasSheafifyEssentiallySmallSite ((topology B S hS).over U) AddCommGrpCat.{max (u + 1) w}

attribute [local instance] hasSheafify_addCommGrp hasSheafifyOver_addCommGrp

/-- The finite locally constant sheaves of abelian groups on the small étale site of `S`, with
coefficients in `AddCommGrpCat.{max (u + 1) w}`, form a weak Serre subcategory of all abelian
sheaves on that site. -/
public theorem isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf :
    (Stacks.ConstantSheaf.isFiniteLocallyConstantAbelianSheaf.{u, u + 1, w}
      (topology B S hS)).IsWeakSerreClass :=
  Stacks.ConstantSheaf.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf.{u, u + 1, w} _

end AlgebraicGeometry.SmallEtale

end
