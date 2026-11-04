module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero is the sheafification of the presheaf extension

Let `R` be a sheaf of rings on a site `(C, J)` and let `U` be an object of `C`. Extension by zero
of *sheaves* of modules from the localized site `C/U` is the sheafification of the extension of
*presheaves* of modules, i.e. the square

```
Mod(O_U)  --j_{U!}-->  Mod(O)
   |                      |
 forget                sheafify
   |                      |
   v                      v
PMod(O_U) --j_{U!}--> PMod(O)
```

commutes up to a canonical isomorphism, for the presheaf extension supplied by any
`PresheafModuleAdjunctionsOver`.

## Main definitions

* `Stacks.Sites.OverModules.sheafExtensionPullbackIso`: extension by zero of sheaves of modules
  from `C/U` as "forget to presheaves, extend as presheaves, sheafify", for Mathlib's extension of
  presheaves of modules.
* `Stacks.Sites.OverModules.presheafExtensionComparison`: the comparison between Mathlib's
  presheaf-level extension and the extension functor supplied by a
  `PresheafModuleAdjunctionsOver`.
* `Stacks.Sites.OverModules.extensionSheafificationIso`: the canonical isomorphism between
  extension by zero of sheaves of modules and the sheafification of the presheaf extension.

## Main results

* `Stacks.Sites.OverModules.extensionSheafificationIso_hom_app`: the isomorphism at a sheaf of
  modules `M`, as Mathlib's comparison followed by the sheafification of
  `presheafExtensionComparison` at the presheaf underlying `M`.
* `Stacks.Sites.OverModules.unit_comp_presheafExtensionComparison_hom_app`: the comparison is
  compatible with the units of the two presheaf-level adjunctions.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.Sites.OverModules

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)

/-- Extension by zero of sheaves of modules from `C/U` is "forget to presheaves, extend as
presheaves, sheafify", for Mathlib's extension of presheaves of modules: Mathlib's
`SheafOfModules.pullbackIso` at the morphism of sheaves of rings `𝟙 (R.over U)`. -/
noncomputable def sheafExtensionPullbackIso :
    SheafOfModules.pullback.{u}
        (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)) ≅
      SheafOfModules.forget.{u} (R.over U) ⋙
        PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
          (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
        PresheafOfModules.sheafification (𝟙 R.obj) :=
  have := Stacks.Sites.ExtensionByZero.presheafRestrictionIsRightAdjoint J R U
  SheafOfModules.pullbackIso.{u} (φ := (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)))

variable (A : PresheafModuleAdjunctionsOver.{u, u, u, u} R.obj U)

/-- The comparison between Mathlib's extension of presheaves of modules from `C/U` and the functor
`j_{U!}` supplied by `A`, given by the uniqueness of left adjoints to restriction along
`Over.forget U`. -/
noncomputable def presheafExtensionComparison :
    PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ≅ A.extension :=
  Adjunction.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom)
    A.extensionRestriction

/-- The comparison of the two presheaf-level extensions is compatible with the units of the two
adjunctions. -/
lemma unit_comp_presheafExtensionComparison_hom_app
    (P : PresheafOfModules.{u} (R.over U).obj) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U) (R := R.obj)
          (S := (R.over U).obj)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app P ≫
        (restrictionFunctor R.obj U).map ((presheafExtensionComparison J R U A).hom.app P) =
      A.extensionRestriction.unit.app P :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ P

/-- Extension by zero of a sheaf of modules is naturally the sheafification of its extension
as a presheaf of modules from the slice category over `U`. -/
@[stacks 03EJ "the square `j_{U!} ∘ forget = ( )^# ∘ j_{U!}`"]
noncomputable def extensionSheafificationIso :
    SheafOfModules.pullback.{u}
        (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)) ≅
      SheafOfModules.forget.{u} (R.over U) ⋙ A.extension ⋙
        PresheafOfModules.sheafification (𝟙 R.obj) :=
  sheafExtensionPullbackIso J R U ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.forget.{u} (R.over U))
        (presheafExtensionComparison J R U A))
      (PresheafOfModules.sheafification (𝟙 R.obj))

/-- The isomorphism `extensionSheafificationIso` at a sheaf of `O_U`-modules `M` is Mathlib's
comparison of extension by zero with "forget, extend presheaves, sheafify", followed by the
sheafification of the comparison of the two presheaf-level extensions at the presheaf underlying
`M`. -/
lemma extensionSheafificationIso_hom_app (M : SheafOfModules.{u} (R.over U)) :
    (extensionSheafificationIso J R U A).hom.app M =
      (sheafExtensionPullbackIso J R U).hom.app M ≫
        (PresheafOfModules.sheafification (𝟙 R.obj)).map
          ((presheafExtensionComparison J R U A).hom.app M.val) :=
  rfl

/-- The inverse of the isomorphism `extensionSheafificationIso` at a sheaf of `O_U`-modules `M`. -/
lemma extensionSheafificationIso_inv_app (M : SheafOfModules.{u} (R.over U)) :
    (extensionSheafificationIso J R U A).inv.app M =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map
          ((presheafExtensionComparison J R U A).inv.app M.val) ≫
        (sheafExtensionPullbackIso J R U).inv.app M :=
  rfl

end Stacks.Sites.OverModules
