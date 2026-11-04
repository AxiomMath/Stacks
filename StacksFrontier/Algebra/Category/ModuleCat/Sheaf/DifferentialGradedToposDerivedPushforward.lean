module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRightDerivedExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPushforwardHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms

/-!
# The derived pushforward along a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `A` be a sheaf of
differential graded `O_C`-algebras, let `B` be a sheaf of differential graded `O_D`-algebras and
let `φ : B ⟶ f_*A` be a unital homomorphism. The direct image of right differential graded
modules `f_* : Mod^dg(A) ⥤ Mod^dg(B)` descends to the homotopy categories, and the derived
pushforward

`Rf_* : D(A, d) ⥤ D(B, d)`

of [Stacks, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP) (2) is the right derived
extension of `K(f_*)` followed by the localization `K(B) ⥤ D(B, d)`. It exists because every
right differential graded `A`-module has a quasi-isomorphism into a graded injective K-injective
one ([Stacks, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)), and it is computed on such
modules.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedToposPushforward`: **the derived pushforward
  `Rf_* : D(A, d) ⥤ D(B, d)`.**
* `SheafOfModules.DifferentialGradedModule.derivedToposPushforwardUnit`: its comparison map
  `K(f_*) ⋙ Q_B ⟶ Q_A ⋙ Rf_*`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isRightDerivedFunctor_derivedToposPushforward`:
  `Rf_*` with its comparison map is the right derived functor of `K(f_*) ⋙ Q_B`.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedToposPushforwardUnit_app`: the
  comparison map is invertible at a graded injective K-injective module.

## Implementation notes

The ringed topoi have their sites, morphisms and structure sheaves in one universe `u`, and the
modules have their sections there too; this is the setting in which the K-injective resolutions
of Tag 0FT0 are constructed. The sheafification and topology conditions under which the
categories of modules are formed hold in that setting and are discharged by instance search, and
the condition that the forgetful functor from commutative rings to rings is compatible with
sheaves is an instance argument, as throughout the ringed-topos files, and it holds on every
ringed topos by `AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat`.

## References

* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe v u w

namespace AlgebraicGeometry.RingedTopos

/-- The forgetful functor from commutative rings to rings is compatible with sheaves on the site
of a ringed topos. -/
theorem hasSheafCompose_forget₂_ringCat (X : RingedTopos.{v, u, w}) :
    X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
  X.toRingedSite.hasSheafCompose_forget₂_ringCat

/-- Sheaves of abelian groups on the site of a ringed topos in one universe admit
sheafification. -/
theorem hasSheafify_addCommGrpCat (X : RingedTopos.{u, u, u}) :
    HasSheafify X.J AddCommGrpCat.{u} :=
  inferInstance

/-- On the site of a ringed topos in one universe, sheafification of abelian groups inverts
exactly the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_addCommGrpCat (X : RingedTopos.{u, u, u}) :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

end AlgebraicGeometry.RingedTopos

namespace SheafOfModules.DifferentialGradedModule

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
  (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)

/-- The direct image on homotopy categories followed by the localization `K(B) ⥤ D(B, d)`: the
functor whose right derived extension is the derived pushforward. -/
abbrev toposPushforwardToDerived :
    HomotopyCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} B :=
  homotopyToposPushforward (toposDirectImageModules f) φ hφ ⋙ toDerivedCategory B

/-- **The derived pushforward `Rf_* : D(A, d) ⥤ D(B, d)`** along a morphism of ringed topoi and a
unital homomorphism `φ : B ⟶ f_*A`: the right derived extension of the direct image on homotopy
categories followed by the localization. -/
def derivedToposPushforward :
    derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} B :=
  rightDerivedExtension.{u, u, u} (X := X.toRingedSite) (A := A)
    (toposPushforwardToDerived f A B φ hφ)

/-- The comparison map `K(f_*) ⋙ Q_B ⟶ Q_A ⋙ Rf_*` of the derived pushforward. -/
def derivedToposPushforwardUnit :
    toposPushforwardToDerived f A B φ hφ ⟶
      toDerivedCategory A ⋙ derivedToposPushforward f A B φ hφ :=
  rightDerivedExtensionUnit.{u, u, u} (X := X.toRingedSite) (A := A)
    (toposPushforwardToDerived f A B φ hφ)

/-- The derived pushforward, with its comparison map, is the right derived functor of the direct
image on homotopy categories followed by the localization. -/
instance isRightDerivedFunctor_derivedToposPushforward :
    (derivedToposPushforward f A B φ hφ).IsRightDerivedFunctor
      (derivedToposPushforwardUnit f A B φ hφ) (quasiIsomorphisms.{u, u, u} A) :=
  isRightDerivedFunctor_rightDerivedExtension.{u, u, u} (X := X.toRingedSite) (A := A)
    (toposPushforwardToDerived f A B φ hφ)

/-- The comparison map of the derived pushforward is invertible at a graded injective
K-injective right differential graded module: there the derived pushforward is the direct
image. -/
theorem isIso_derivedToposPushforwardUnit_app {I : DifferentialGradedModule.{u, u, u} A}
    (hI : IsDGInjective I) :
    IsIso ((derivedToposPushforwardUnit f A B φ hφ).app ((HomotopyCategory.quotient A).obj I)) :=
  isIso_rightDerivedExtensionUnit_app.{u, u, u} (X := X.toRingedSite) (A := A)
    (toposPushforwardToDerived f A B φ hφ) hI

end SheafOfModules.DifferentialGradedModule
