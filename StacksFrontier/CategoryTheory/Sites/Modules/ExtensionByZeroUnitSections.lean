module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
import StacksCore.Tactic.StacksAttribute

/-!
# Maps out of the extension by zero of the structure sheaf

Let `(C, O)` be a ringed site and `U` an object of `C`. Stacks 0G1V is the chain of
identifications
`Hom_O(j_{U!} O_U, F) = Hom_{O_U}(O_U, j_U^* F) = F(U)`:
a morphism out of the extension by zero of the structure sheaf of the slice site is the same
thing as a section of `F` over `U`.

The first identification is the adjunction `j_{U!} ⊣ j_U^*` of Stacks 03DI. The second is the
composite of two Mathlib bijections: morphisms out of the unit sheaf of modules are its
sections (`SheafOfModules.unitHomEquiv`), and the global sections of a sheaf of modules on the
slice site over `U` are its sections over `U`, because `U ⟶ U` is a terminal object of `C/U`.

## Main definitions

* `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv`: the bijection between morphisms
  `j_{U!} O_U ⟶ F` and sections of `F` over `U`.

## Main results

* `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality`: the bijection is
  natural in `F`, i.e. it carries composition with `g : F ⟶ G` to the action of `g` on
  sections over `U`.

## Implementation notes

The statement is for an arbitrary sheaf of rings on a site, so it applies to the structure
sheaf of every ringed site.

The second identification is `Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv`, which
is already available; evaluating at the terminal object `U ⟶ U` of the slice site is exactly
what it does, so no separate sections-at-a-terminal-object bijection is introduced here.

Nothing here specialises a universe: the site is `C : Type u₁` with `Category.{v₁} C` and the
sheaf of rings and the module sections live in an independent universe `w`. Existence of the
extension-by-zero functor — the left adjoint of restriction along `Over.forget U` — is carried
as the instance hypothesis
`(SheafOfModules.pushforward (𝟙 (R.over U))).IsRightAdjoint`, because Mathlib's construction of
that left adjoint is available only for a small site whose module sections are in the universe
of the site. On a small site the hypothesis is discharged by
`Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint`, so the statements below
specialise to the previous ones verbatim.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{w}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint]

/-- **Stacks 0G1V.** Morphisms `j_{U!} O_U ⟶ F` are canonically the sections of `F` over `U`:
transpose along the extension-by-zero adjunction, then read the resulting morphism out of the
unit sheaf of modules on `C/U` as a section at the terminal object `U ⟶ U`. -/
@[stacks 0G1V]
noncomputable def extensionByZeroUnitHomEquiv (F : SheafOfModules.{w} R) :
    ((SheafOfModules.pullback.{w} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj
        (SheafOfModules.unit (R.over U)) ⟶ F) ≃
      (F.val.obj (op U) : Type w) :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{w} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).homEquiv
      (SheafOfModules.unit (R.over U)) F).trans
    ((F.over U).unitHomEquiv.trans
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv F U))

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Stacks 0G1V.** The identification of `Hom_O(j_{U!} O_U, F)` with `F(U)` is natural in
`F`: composing with `g : F ⟶ G` corresponds to applying `g` to sections over `U`. -/
@[stacks 0G1V "naturality"]
theorem extensionByZeroUnitHomEquiv_naturality {F G : SheafOfModules.{w} R}
    (f : (SheafOfModules.pullback.{w} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj
        (SheafOfModules.unit (R.over U)) ⟶ F)
    (g : F ⟶ G) :
    extensionByZeroUnitHomEquiv J R U G (f ≫ g) =
      ((SheafOfModules.evaluation R (op U)).map g)
        (extensionByZeroUnitHomEquiv J R U F f) := by
  show ((G.over U).unitHomEquiv
      ((SheafOfModules.pullbackPushforwardAdjunction.{w} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).homEquiv
          (SheafOfModules.unit (R.over U)) G (f ≫ g))).val (op (Over.mk (𝟙 U))) =
    ((SheafOfModules.evaluation R (op U)).map g)
      (((F.over U).unitHomEquiv
        ((SheafOfModules.pullbackPushforwardAdjunction.{w} (F := Over.forget U)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).homEquiv
            (SheafOfModules.unit (R.over U)) F f)).val (op (Over.mk (𝟙 U))))
  rw [(SheafOfModules.pullbackPushforwardAdjunction.{w} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).homEquiv_naturality_right]
  rfl

end Stacks.Sites.ExtensionByZero
