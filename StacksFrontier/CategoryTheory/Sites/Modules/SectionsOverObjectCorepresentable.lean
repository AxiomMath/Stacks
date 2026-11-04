module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Sections over an object are corepresented by the extension by zero of the structure sheaf

Let `(C, O)` be a ringed site and `U` an object of `C`. Stacks 0G1V identifies morphisms
`j_{U!} O_U ⟶ F` with the sections of `F` over `U`. This file upgrades that bijection to an
additive one and assembles the components into an isomorphism of functors

`Hom(j_{U!} O_U, -) ≅ Γ(U, -)`

valued in abelian groups. That is the shape in which the sections functor can be fed to the
`Hom`-complex machinery: the degreewise `Hom(X, -)` of a complex is Mathlib's `Hom` complex out
of `X[0]`, whose cohomology is a group of morphisms in the homotopy category.

Additivity is not automatic from Stacks 0G1V — a natural bijection of the underlying types of
two additive functors need not be additive — so it is checked here, through the three factors
of which `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv` is the composite: the
transposition along `j_{U!} ⊣ j_U^*`, which is composition with the unit followed by the
additive functor `j_U^*`; `CategoryTheory.SheafOfModules.unitHomEquiv`, whose additivity is the
same section-by-section check as in
`Stacks.Cohomology.SiteModules.unitSectionsAddEquiv`; and evaluation of a global section of the
restriction at the terminal object `U ⟶ U` of `C/U`.

## Main definitions

* `Stacks.Sites.ExtensionByZero.extensionByZeroUnitObj`: the sheaf of modules `j_{U!} O_U`.
* `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomAddEquiv`: Stacks 0G1V as an additive
  equivalence.
* `Stacks.Sites.ExtensionByZero.coyonedaExtensionByZeroUnitIso`: the isomorphism of functors
  `Hom(j_{U!} O_U, -) ≅ Γ(U, -)`.

## Implementation notes

The universes are collapsed to a single `u`, which is what the ringed sites of the derived
development (`AlgebraicGeometry.RingedSite.{u, u, u}`) provide, and what makes the hom universe
of `SheafOfModules.{u} R` — in which `CategoryTheory.preadditiveCoyoneda` lands — agree with
the universe `u` of the module sections, in which `Γ(U, -)` lands. At unequal universes the two
sides of `coyonedaExtensionByZeroUnitIso` are functors into different categories of abelian
groups and the statement does not typecheck; the generality that is lost is not used anywhere
in this development.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The extension by zero `j_{U!} O_U` of the structure sheaf of the slice site over `U`. -/
noncomputable abbrev extensionByZeroUnitObj : SheafOfModules.{u} R :=
  (SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj (SheafOfModules.unit (R.over U))

/-- The bijection of Stacks 0G1V, spelled out: transpose along `j_{U!} ⊣ j_U^*`, then take the
value of the resulting morphism out of the unit at the terminal object `U ⟶ U` of `C/U` on the
unit section. In this spelling the transposed morphism carries the type
`O_U ⟶ j_U^* F` that `CategoryTheory.Adjunction.homEquiv_unit` is stated for. -/
theorem extensionByZeroUnitHomEquiv_apply_val (F : SheafOfModules.{u} R)
    (f : extensionByZeroUnitObj J R U ⟶ F) :
    extensionByZeroUnitHomEquiv J R U F f =
      (((SheafOfModules.pushforward.{u} (F := Over.forget U)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj F).unitHomEquiv
        (((SheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).homEquiv
            (SheafOfModules.unit (R.over U)) F) f)).val (op (Over.mk (𝟙 U))) :=
  rfl

/-- Restriction of sheaves of modules to the slice site is additive: it is precomposition with
`Over.forget U` and restriction of scalars along an identity, neither of which moves the
underlying additive group. -/
local instance additive_pushforward_over :
    (SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).Additive where
  map_add := rfl

/-- **Stacks 0G1V as an additive equivalence.** Morphisms `j_{U!} O_U ⟶ F` are the sections of
`F` over `U`, and the bijection is additive: transposition along the adjunction is composition
with the unit followed by the additive functor `j_U^*`, and evaluating a morphism out of the
unit at a section is additive. -/
noncomputable def extensionByZeroUnitHomAddEquiv (F : SheafOfModules.{u} R) :
    (extensionByZeroUnitObj J R U ⟶ F) ≃+ (F.val.obj (op U) : Type u) where
  toEquiv := extensionByZeroUnitHomEquiv J R U F
  map_add' f g := by
    simp only [Equiv.toFun_as_coe, extensionByZeroUnitHomEquiv_apply_val,
      Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add,
      SheafOfModules.unitHomEquiv_apply_coe]
    rfl

/-- **`Hom(j_{U!} O_U, -) = Γ(U, -)`.** Sections over `U` of sheaves of modules, read in
abelian groups, are corepresented by the extension by zero of the structure sheaf of the slice
site over `U`.

The components are `extensionByZeroUnitHomAddEquiv` and naturality is Stacks 0G1V's
`extensionByZeroUnitHomEquiv_naturality`. -/
noncomputable def coyonedaExtensionByZeroUnitIso :
    preadditiveCoyoneda.obj (op (extensionByZeroUnitObj J R U)) ≅
      SheafOfModules.evaluation.{u} R (op U) ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun F => (extensionByZeroUnitHomAddEquiv J R U F).toAddCommGrpIso) (by
    intro F G g
    ext f
    change extensionByZeroUnitHomEquiv J R U G (f ≫ g) =
      ((SheafOfModules.evaluation R (op U)).map g) (extensionByZeroUnitHomEquiv J R U F f)
    exact extensionByZeroUnitHomEquiv_naturality J R U f g)

end Stacks.Sites.ExtensionByZero

end
