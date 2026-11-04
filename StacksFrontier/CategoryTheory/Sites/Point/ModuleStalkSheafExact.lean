module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk functor on sheaves of modules: exactness, and invariance under sheafification

Let `(C, J)` be a site, `Φ` a point of it and `R` a sheaf of rings on `C`. This file records
the two sheaf-level halves of Stacks 04EQ: taking the stalk at `Φ` of a sheaf of `R`-modules is
an exact functor to modules over the stalk of `R`, and sheafification of a presheaf of modules
does not change its stalk.

## Main definitions

* `Stacks.moduleFiberSheafificationComparison`: the canonical map from the stalk of a presheaf
  of modules to the stalk of its sheafification, naturally in the presheaf.

## Main results

* `Stacks.exactFunctor_sheafModuleFiber`: part (1) of the source, the stalk functor on sheaves
  of modules is exact.
* `Stacks.isIso_moduleFiberSheafificationComparison`: part (3) of the source, sheafification
  does not change the module-valued stalk.
* `Stacks.exactFunctor_sheafModuleFiberOfCommRing`: the untagged specialisation of part (1) to
  modules over the ring sheaf of a sheaf of commutative rings.

Part (2), the presheaf-level half, is `Stacks.exactFunctor_presheafModuleFiber`.

## Implementation notes

The source states part (3) as an equality of stalks. It is rendered here as a natural
isomorphism of functors to modules over the stalk of the structure sheaf, so that it records
both that the identification respects the module structures and that it is natural in the
presheaf.

## References

* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

universe w v u

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w})

section Exactness

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 04EQ, part (1).** Taking the stalk at a point of a site is an exact
functor from sheaves of `R`-modules to modules over the stalk of `R`. -/
@[stacks 04EQ "part (1)"]
theorem exactFunctor_sheafModuleFiber :
    exactFunctor (SheafOfModules.{w} R)
      (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R.obj))
      (sheafModuleFiber Φ R) := by
  have := preservesFiniteLimits_of_natIso (sheafModuleFiberCompForget₂ Φ R).symm
  have := preservesFiniteColimits_of_natIso (sheafModuleFiberCompForget₂ Φ R).symm
  exact (exactFunctor_iff _).mpr
    ⟨preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ _ AddCommGrpCat.{w}),
     preservesFiniteColimits_of_reflects_of_preserves _ (forget₂ _ AddCommGrpCat.{w})⟩

/-- Taking the stalk at a point of a site is an exact functor from sheaves of modules over the
ring sheaf of a sheaf of commutative rings `O` to modules over the stalk of `O`.

It is left untagged: the structure sheaf of a ringed site is a sheaf of rings, so the tag of
Stacks 04EQ part (1) is on the `RingCat`-valued form `Stacks.exactFunctor_sheafModuleFiber`. -/
theorem exactFunctor_sheafModuleFiberOfCommRing (O : Sheaf J CommRingCat.{w})
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    exactFunctor (SheafOfModules.{w} (commRingSheafToRingSheaf O))
      (ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj))
      (sheafModuleFiberOfCommRing Φ O) := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp
    (exactFunctor_sheafModuleFiber Φ (commRingSheafToRingSheaf O))
  have : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom) :=
    preservesFiniteLimits_restrictScalars _
  have : PreservesFiniteColimits
      (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom) :=
    preservesFiniteColimits_restrictScalars _
  exact (exactFunctor_iff _).mpr
    ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

end Exactness

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The canonical map from the module-valued stalk of a presheaf of modules to the stalk of its
sheafification, naturally in the presheaf: the stalk functor applied to the unit of the
sheafification adjunction for presheaves of modules. -/
noncomputable def moduleFiberSheafificationComparison :
    presheafModuleFiber Φ R.obj ⟶
      PresheafOfModules.sheafification (𝟙 R.obj) ⋙ sheafModuleFiber Φ R :=
  Functor.whiskerRight
    (PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit
    (presheafModuleFiber Φ R.obj)

/-- **Stacks Project, Tag 04EQ, part (3).** Sheafification of a presheaf of modules does not
change its module-valued stalk. -/
@[stacks 04EQ "part (3)"]
theorem isIso_moduleFiberSheafificationComparison :
    IsIso (moduleFiberSheafificationComparison Φ R) := by
  have : ∀ M, IsIso ((moduleFiberSheafificationComparison Φ R).app M) := fun M ↦
    isIso_presheafModuleFiber_map_sheafificationAdjunction_unit Φ R M
  exact NatIso.isIso_of_isIso_app _

end Sheafification

end Stacks
