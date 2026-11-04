module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AbelianSheafification
public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedNakayamaProEtale

/-!
# Pro-étale coefficient categories at the universe of the sections

For a scheme `X : Scheme.{u}`, sheaves on the small pro-étale site take their sections in
`Type (u + 1)`. The general statements about the coefficient categories
`Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}` and
`Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)` leave the universe `v` free, so
typeclass search at `AddCommGrpCat.{u + 1}` is stuck on `u + 1 =?= max (u + 1) ?v`. This file
records them with the universe pinned to `u + 1`, for use as local instances.

## Main results

* `AlgebraicGeometry.ProEtale.hasSheafify_proEt_moduleCat_succ` and
  `AlgebraicGeometry.ProEtale.isGrothendieckAbelian_proetaleModuleSheaf_succ` for sheaves of
  `Λ`-modules, `Λ : Type (u + 1)`.
* `AlgebraicGeometry.ProEtale.isGrothendieckAbelian_proetale_ab_succ` for abelian sheaves (whose
  sheafification is the base `AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat_succ`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Presheaves of `Λ`-modules on the small pro-étale site admit sheafification. -/
theorem hasSheafify_proEt_moduleCat_succ (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleCat.{u + 1, u, u + 1, u + 1} _ _

attribute [local instance] hasSheafify_proEt_moduleCat_succ

/-- Pro-étale sheaves of `Λ`-modules form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_proetaleModuleSheaf_succ (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  isGrothendieckAbelian_proetaleModuleSheaf.{u, u + 1, 0} Λ X

/-- Pro-étale sheaves of `Λ`-modules have enough injectives. -/
theorem enoughInjectives_proetaleModuleSheaf_succ (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  have := isGrothendieckAbelian_proetaleModuleSheaf_succ Λ X
  IsGrothendieckAbelian.enoughInjectives

attribute [local instance] hasSheafify_proetale_addCommGrpCat_succ

/-- Pro-étale abelian sheaves form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_proetale_ab_succ (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_proetale.{0, u} X

/-- Pro-étale abelian sheaves have enough injectives. -/
theorem enoughInjectives_proetale_ab_succ (X : Scheme.{u}) :
    EnoughInjectives (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  enoughInjectives_sheaf_proetale.{0, u} X

/-- Passing to underlying abelian groups commutes with pro-étale sheafification. -/
theorem preservesSheafification_forget₂_proetale_succ (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  preservesSheafification_forget₂_moduleCat_ofLeftAdjoint.{u + 1, 0} Λ _

end AlgebraicGeometry.ProEtale

end
