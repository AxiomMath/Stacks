module

import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Yoneda
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification

/-!
# The sheaf of rings underlying a sheaf of commutative rings

A sheaf of commutative rings on a site is regarded as a sheaf of rings by composing with the
forgetful functor from commutative rings to rings.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.underlyingRingSheafOfSite`: The sheaf of rings underlying a
  sheaf of commutative rings.
-/

@[expose] public section

open CategoryTheory

universe v v₁ u u₁ w₀

namespace AlgebraicGeometry.SheafOfModules

/-- A sheaf of commutative rings, regarded as a sheaf of rings. -/
noncomputable abbrev underlyingRingSheafOfSite {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O

/-- The sheaf of rings underlying a sheaf of commutative rings, described by its underlying
presheaf together with the sheaf condition. -/
private abbrev explicitUnderlyingRingSheaf {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  ⟨O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    GrothendieckTopology.HasSheafCompose.isSheaf O.obj O.property⟩

universe w

end AlgebraicGeometry.SheafOfModules
