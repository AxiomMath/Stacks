module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of the structure sheaf is flat

Let `O` be a presheaf of commutative rings on a category and `U` an object. The extension from
the slice category over `U` of the rank-one `O|_U`-module is a flat presheaf of `O`-modules,
and on a site the corresponding extension by zero of the structure sheaf of the localized site
is a flat sheaf of modules.

## Main results

* `Stacks.Sites.OverModules.presheafExtensionUnit_isFlat`: the extension of the rank-one
  `O|_U`-module from the slice category over `U` is a flat presheaf of `O`-modules.
* `Stacks.Sites.OverModules.sheafExtensionUnit_isFlat`: the extension by zero of the structure
  sheaf of the localized site is a flat sheaf of modules.

## References

* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.OverModules

open AlgebraicGeometry.SheafOfModules (ringPresheaf)

universe u v w

/-- The extension from the slice category over `U` of the rank-one module is a flat presheaf of
modules. -/
@[stacks 03EV "part (1)"]
theorem presheafExtensionUnit_isFlat {C : Type u} [Category.{v} C]
    (O : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (U : C) :
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat
      ((presheafModuleAdjunctionsOver (ringPresheaf O) U).extension.obj
        (PresheafOfModules.unit (overRingPresheaf (ringPresheaf O) U))) := by
  classical
  apply AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat
  intro V
  obtain ⟨e, _⟩ := extensionObjLinearEquivDirectSum (ringPresheaf O) U
    (presheafModuleAdjunctionsOver (ringPresheaf O) U)
    (PresheafOfModules.unit (overRingPresheaf (ringPresheaf O) U))
  have : Module.Flat ((ringPresheaf O).obj V)
      (extensionFormula.{v, u, max u v w, max u w} (ringPresheaf O) U V.unop
        (PresheafOfModules.unit (overRingPresheaf (ringPresheaf O) U))) := by
    change Module.Flat ((ringPresheaf O).obj V)
      (DirectSum (V.unop ⟶ U) fun φ ↦
        (PresheafOfModules.unit (overRingPresheaf (ringPresheaf O) U)).obj (op (Over.mk φ)))
    refine Module.Flat.directSum_iff.2 fun _ ↦ ?_
    change Module.Flat ((ringPresheaf O).obj V) ((ringPresheaf O).obj V)
    infer_instance
  exact Module.Flat.of_linearEquiv (e V.unop)

/-- The extension by zero from the localized site of the structure sheaf is a flat sheaf of
modules. -/
@[stacks 03EV "part (2)"]
theorem sheafExtensionUnit_isFlat {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (O : Sheaf J CommRingCat.{u}) (U : C) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.pullback.{u} (F := Over.forget U)
        (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf O).over U) :
          ((Stacks.SheafOfModules.Tensor.ringSheaf O).over U) ⟶
            ((Stacks.SheafOfModules.Tensor.ringSheaf O).over U))).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over U))) := by
  classical
  let R : Sheaf J RingCat.{u} := Stacks.SheafOfModules.Tensor.ringSheaf O
  let A := presheafModuleAdjunctionsOver R.obj U
  let a : ringPresheaf O.obj ⟶ R.obj := 𝟙 R.obj
  have : Presheaf.IsLocallyInjective J a :=
    Presheaf.isLocallyInjective_of_injective J a fun _ _ _ h => h
  have : Presheaf.IsLocallySurjective J a :=
    Presheaf.isLocallySurjective_of_surjective J a fun _ x => ⟨x, rfl⟩
  have hH : exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj
      ((SheafOfModules.forget (R.over U) ⋙ A.extension ⋙
        PresheafOfModules.sheafification (𝟙 R.obj)).obj (SheafOfModules.unit (R.over U)))) :=
    Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J a _
      (presheafExtensionUnit_isFlat O.obj U)
  exact (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.mapIso
      ((extensionSheafificationIso J R U A).app (SheafOfModules.unit (R.over U))).symm) hH

end Stacks.Sites.OverModules

end
