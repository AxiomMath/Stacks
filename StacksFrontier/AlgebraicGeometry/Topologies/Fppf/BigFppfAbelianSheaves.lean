module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# Abelian sheaves on the big fppf site and on its localizations

The big fppf site of a scheme and each of its localizations are essentially small, so their
categories of abelian sheaves admit sheafification, are Grothendieck abelian categories, have
enough injectives, and have `Ext`-groups in the universe of the schemes; and the topologies
satisfy `W = locally bijective`. These are the instances that cohomology over an object of the
big fppf site uses (`Stacks.Cohomology.Torsors.torsorClassOver`).

## Main results

* `AlgebraicGeometry.BigFppfOver.hasSheafify_abelian`,
  `AlgebraicGeometry.BigFppfOver.hasSheafify_over_abelian`: sheafification.
* `AlgebraicGeometry.BigFppfOver.enoughInjectives_abelian`: enough injectives.
* `AlgebraicGeometry.BigFppfOver.hasExt_abelian`,
  `AlgebraicGeometry.BigFppfOver.hasExt_over_abelian`: `Ext`-groups in the universe of the
  schemes.
* `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_abelian`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on the big fppf site over `S` admit sheafification. -/
theorem hasSheafify_abelian : HasSheafify (topology B S hS) AddCommGrpCat.{u} := by
  let : HasSheafify ((equivSmallModel.{u} (BigFppfOver B S hS)).inverse.inducedTopology
    (topology B S hS)) AddCommGrpCat.{u} := inferInstance
  exact hasSheafifyEssentiallySmallSite _ _

/-- Abelian presheaves on a localization of the big fppf site over `S` admit sheafification. -/
theorem hasSheafify_over_abelian (U : BigFppfOver B S hS) :
    HasSheafify ((topology B S hS).over U) AddCommGrpCat.{u} := by
  have : EssentiallySmall.{u} (Over U) := Stacks.essentiallySmall_over U
  let : HasSheafify ((equivSmallModel.{u} (Over U)).inverse.inducedTopology
    ((topology B S hS).over U)) AddCommGrpCat.{u} := inferInstance
  exact hasSheafifyEssentiallySmallSite _ _

/-- The abelian sheaves on the big fppf site over `S` form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_abelian :
    letI := hasSheafify_abelian B S hS
    IsGrothendieckAbelian.{u} (Sheaf (topology B S hS) AddCommGrpCat.{u}) := by
  let := hasSheafify_abelian B S hS
  let : HasSheafify ((equivSmallModel.{u} (BigFppfOver B S hS)).inverse.inducedTopology
    (topology B S hS)) AddCommGrpCat.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _

/-- The abelian sheaves on a localization of the big fppf site form a Grothendieck abelian
category. -/
theorem isGrothendieckAbelian_over_abelian (U : BigFppfOver B S hS) :
    letI := hasSheafify_over_abelian B S hS U
    IsGrothendieckAbelian.{u} (Sheaf ((topology B S hS).over U) AddCommGrpCat.{u}) := by
  let := hasSheafify_over_abelian B S hS U
  have : EssentiallySmall.{u} (Over U) := Stacks.essentiallySmall_over U
  let : HasSheafify ((equivSmallModel.{u} (Over U)).inverse.inducedTopology
    ((topology B S hS).over U)) AddCommGrpCat.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _

/-- The abelian sheaves on the big fppf site over `S` have enough injectives. -/
theorem enoughInjectives_abelian :
    letI := hasSheafify_abelian B S hS
    EnoughInjectives (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  letI := hasSheafify_abelian B S hS
  letI := isGrothendieckAbelian_abelian B S hS
  IsGrothendieckAbelian.enoughInjectives

/-- The abelian sheaves on the big fppf site over `S` have `Ext`-groups in the universe of the
schemes. -/
theorem hasExt_abelian :
    letI := hasSheafify_abelian B S hS
    HasExt.{u} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  letI := hasSheafify_abelian B S hS
  letI := isGrothendieckAbelian_abelian B S hS
  letI := enoughInjectives_abelian B S hS
  hasExt_of_enoughInjectives _

/-- The abelian sheaves on a localization of the big fppf site have `Ext`-groups in the universe
of the schemes. -/
theorem hasExt_over_abelian (U : BigFppfOver B S hS) :
    letI := hasSheafify_over_abelian B S hS U
    HasExt.{u} (Sheaf ((topology B S hS).over U) AddCommGrpCat.{u}) :=
  letI := hasSheafify_over_abelian B S hS U
  letI := isGrothendieckAbelian_over_abelian B S hS U
  letI : EnoughInjectives (Sheaf ((topology B S hS).over U) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  hasExt_of_enoughInjectives _

/-- On the big fppf site over `S`, a morphism of abelian presheaves becomes an isomorphism after
sheafification exactly when it is locally bijective. -/
theorem wEqualsLocallyBijective_abelian :
    (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end AlgebraicGeometry.BigFppfOver

end
