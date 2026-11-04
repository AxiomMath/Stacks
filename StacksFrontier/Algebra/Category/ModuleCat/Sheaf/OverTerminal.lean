module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal

/-!
# Sheaves of modules on the slice over a terminal object

Let `(C, J)` be a site, `R` a sheaf of rings on it and `T` a terminal object of `C`. The
forgetful functor `C/T ⥤ C` is then an equivalence of sites, so restriction of sheaves of
`R`-modules to the slice site, `SheafOfModules.overFunctor R T`, is an equivalence of categories
from sheaves of `R`-modules to sheaves of `R|_T`-modules: nothing is lost by passing to the slice
over a terminal object.

## Main definitions

* `Stacks.SheafOfModules.overTerminalEquivalence`: the equivalence
  `Mod(R) ≌ Mod(R|_T)`, whose functor is `SheafOfModules.overFunctor R T`.

## Main results

* `Stacks.SheafOfModules.overTerminalEquivalence_functor`: its functor is the restriction.
* `Stacks.SheafOfModules.isEquivalence_overFunctor`: restriction to the slice over a terminal
  object is an equivalence.

## Implementation notes

The equivalence is `SheafOfModules.pushforwardPushforwardEquivalence` along
`CategoryTheory.Over.equivalenceOfIsTerminal`, whose functor `Over.forget T` is a dense subsite
inclusion (`CategoryTheory.GrothendieckTopology.isDenseSubsite_overForget`), so that both it and
its inverse are continuous. The ring sheaf `R|_T` is by definition the pushforward of `R` along
`Over.forget T`, so both comparison maps of ring sheaves are identities.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe m w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  {T : C}

/-- **Restriction to the slice over a terminal object is an equivalence of categories of sheaves
of modules.** For a terminal object `T` of the site, sheaves of `R`-modules are equivalent to
sheaves of modules over the restriction `R|_T` of `R` to the slice site `C/T`; the functor of
the equivalence is the restriction `SheafOfModules.overFunctor R T`. -/
def overTerminalEquivalence (hT : IsTerminal T) :
    _root_.SheafOfModules.{m} R ≌ _root_.SheafOfModules.{m} (R.over T) :=
  letI : (Over.equivalenceOfIsTerminal hT).symm.inverse.IsDenseSubsite (J.over T) J :=
    GrothendieckTopology.isDenseSubsite_overForget J hT
  letI : (Over.equivalenceOfIsTerminal hT).functor.IsContinuous (J.over T) J :=
    inferInstanceAs ((Over.forget T).IsContinuous (J.over T) J)
  letI : (Over.equivalenceOfIsTerminal hT).inverse.IsContinuous J (J.over T) :=
    inferInstanceAs ((Over.equivalenceOfIsTerminal hT).symm.functor.IsContinuous J (J.over T))
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (Over.equivalenceOfIsTerminal hT)
    (𝟙 _) ⟨𝟙 R.obj⟩
    (by ext U x; exact ConcreteCategory.congr_hom (R.obj.map_id U) x)
    (by ext U x; exact ConcreteCategory.congr_hom (R.obj.map_id (Opposite.op U.unop.left)) x)

/-- The functor of `Stacks.SheafOfModules.overTerminalEquivalence` is restriction to the slice
site. -/
theorem overTerminalEquivalence_functor (hT : IsTerminal T) :
    (overTerminalEquivalence R hT :
        _root_.SheafOfModules.{m} R ≌ _root_.SheafOfModules.{m} (R.over T)).functor =
      _root_.SheafOfModules.overFunctor.{m} R T :=
  rfl

/-- **Restriction of sheaves of modules to the slice over a terminal object is an
equivalence.** -/
theorem isEquivalence_overFunctor (hT : IsTerminal T) :
    (_root_.SheafOfModules.overFunctor.{m} R T).IsEquivalence :=
  (overTerminalEquivalence R hT :
    _root_.SheafOfModules.{m} R ≌ _root_.SheafOfModules.{m} (R.over T)).isEquivalence_functor

end Stacks.SheafOfModules
