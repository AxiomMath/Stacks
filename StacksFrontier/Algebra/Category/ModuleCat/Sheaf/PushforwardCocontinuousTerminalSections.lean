module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Sections of a direct image over a final object

Let `F : X ⥤ Y` be a cocontinuous functor of sites, `f^♯ : O_Y ⟶ {}_sF O_X` a structure map of
sheaves of rings, and `f_*` the direct image of sheaves of modules
`Stacks.SheafOfModules.pushforwardCocontinuous`. If `y` is a final object of `Y`, then every
object `x` of `X` has a unique arrow `F(x) ⟶ y`, so the index category of the limit computing
`(f_* M)(y)` is the opposite of `X`, and `(f_* M)(y)` is the module of compatible families of
sections of `M` on all of `X`: `Γ(y, f_* M) = Γ(X, M)`. The identification is linear over
`O_Y(y)`, which acts on `Γ(X, M)` through the ring map `O_Y(y) ⟶ Γ(X, O_X)` that `f^♯` cuts out
on the legs, and it is natural in `M`.

## Main definitions

* `Stacks.SheafOfModules.pushforwardCocontinuousBaseRingHom`: the ring map
  `O_Y(y) ⟶ Γ(X, O_X)` attached to a final object `y`.
* `Stacks.SheafOfModules.pushforwardCocontinuousObjSectionsEquiv`: `Γ(y, f_* M) ≃ Γ(X, M)`.
* `Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoGlobalSections`: the natural
  isomorphism of `O_Y(y)`-modules `Γ(y, f_* -) ≅ Γ(X, -)`, after a universe lift.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Stacks.Cohomology.SiteModules

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

section Index

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] {F : X ⥤ Y}
  {y : Y} (ht : IsTerminal y)

/-- The object `(U, op y ⟶ F.op(U))` of the index category of the right Kan extension along
`F.op` at `op y` given by the unique arrow `F(U) ⟶ y` to the final object. -/
abbrev structuredArrowOfIsTerminal (U : Xᵒᵖ) : StructuredArrow (op y) F.op :=
  StructuredArrow.mk (Y := U) (ht.from (F.obj U.unop)).op

/-- The morphism `structuredArrowOfIsTerminal U ⟶ structuredArrowOfIsTerminal U'` lying over a
morphism `U ⟶ U'` of `Xᵒᵖ`. -/
def structuredArrowHomOfIsTerminal {U U' : Xᵒᵖ} (g : U ⟶ U') :
    structuredArrowOfIsTerminal (F := F) ht U ⟶ structuredArrowOfIsTerminal ht U' :=
  StructuredArrow.homMk g (Quiver.Hom.unop_inj (ht.hom_ext _ _))

variable {H : Type*} [Category H] [∀ G : Xᵒᵖ ⥤ H, F.op.HasRightKanExtension G]

/-- Every leg of the right Kan extension along `F.op` at a final object is the leg at
`structuredArrowOfIsTerminal`. -/
theorem ranπ_structuredArrowOfIsTerminal (N : Xᵒᵖ ⥤ H) (j : StructuredArrow (op y) F.op) :
    ranπ F.op N (op y) (structuredArrowOfIsTerminal ht j.right) = ranπ F.op N (op y) j := by
  obtain ⟨⟨⟨⟩⟩, U, g⟩ := j
  obtain rfl : g = (ht.from (F.obj U.unop)).op := Quiver.Hom.unop_inj (ht.hom_ext _ _)
  rfl

end Index

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] {F : X ⥤ Y}
  {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y} [F.IsCocontinuous JX JY]
  [∀ G : Xᵒᵖ ⥤ RingCat.{r}, F.op.HasPointwiseRightKanExtension G]
  [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{v}, F.op.HasPointwiseRightKanExtension G]
  {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}}
  (fSharp : OY ⟶ (F.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX)
  {y : Y} (ht : IsTerminal y)

/-- **The ring map `O_Y(y) ⟶ Γ(X, O_X)` at a final object `y`**: the component at `U` of the
image of `a` is the image of `a` under the ring map `O_Y(y) ⟶ O_X(U)` that the structure map cuts
out at the leg `(U, F(U) ⟶ y)`. -/
def pushforwardCocontinuousBaseRingHom : OY.obj.obj (op y) →+* GlobalSectionRing OX where
  toFun a := ⟨fun U => (scalarπ F (structureMapPresheaf F fSharp) (op y)
      (structuredArrowOfIsTerminal ht U)).hom a, fun {U U'} g => by
    change (OX.obj.map g).hom ((scalarπ F (structureMapPresheaf F fSharp) (op y)
      (structuredArrowOfIsTerminal ht U)).hom a) = _
    exact scalarπ_naturality F _ (structuredArrowHomOfIsTerminal ht g) a⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

omit [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{v}, F.op.HasPointwiseRightKanExtension G] in
/-- The component at `U` of `pushforwardCocontinuousBaseRingHom` is the ring map cut out at the
leg `structuredArrowOfIsTerminal U`. -/
theorem pushforwardCocontinuousBaseRingHom_apply (a : OY.obj.obj (op y)) (U : Xᵒᵖ) :
    (pushforwardCocontinuousBaseRingHom fSharp ht a).1 U =
      (scalarπ F (structureMapPresheaf F fSharp) (op y) (structuredArrowOfIsTerminal ht U)).hom a :=
  rfl

variable (M : _root_.SheafOfModules.{v} OX)

/-- **Sections of a direct image over a final object** are the compatible families of sections
on the whole source site: `Γ(y, f_* M) ≃ Γ(X, M)`, sending a section to its family of legs. -/
def pushforwardCocontinuousObjSectionsEquiv :
    ((pushforwardCocontinuous.{v} F fSharp).obj M).val.obj (op y) ≃ M.sections where
  toFun x := ⟨fun U => (ranπ F.op M.val.presheaf (op y) (structuredArrowOfIsTerminal ht U)).hom x,
    fun {U U'} g => ConcreteCategory.congr_hom
      (ranπ_naturality F.op M.val.presheaf (structuredArrowHomOfIsTerminal ht g)) x⟩
  invFun s := (Types.isLimitEquivSections (isLimitOfPreserves (forget AddCommGrpCat.{v})
      (ranIsLimit F.op M.val.presheaf (op y)))).symm
    ⟨fun j => s.1 j.right, fun {_ _} φ => s.2 φ.right⟩
  left_inv x := by
    refine (Equiv.symm_apply_eq _).2 (Subtype.ext (funext fun j => ?_))
    exact ConcreteCategory.congr_hom (ranπ_structuredArrowOfIsTerminal ht M.val.presheaf j) x
  right_inv s := Subtype.ext (funext fun U =>
    Types.isLimitEquivSections_symm_apply (isLimitOfPreserves (forget AddCommGrpCat.{v})
      (ranIsLimit F.op M.val.presheaf (op y))) ⟨fun j => s.1 j.right, fun {_ _} φ => s.2 φ.right⟩
      (structuredArrowOfIsTerminal ht U))

/-- The component at `U` of the family attached to a section of the direct image is its leg at
`structuredArrowOfIsTerminal U`. -/
theorem pushforwardCocontinuousObjSectionsEquiv_apply_eval
    (x : ((pushforwardCocontinuous.{v} F fSharp).obj M).val.obj (op y)) (U : Xᵒᵖ) :
    (pushforwardCocontinuousObjSectionsEquiv fSharp ht M x).eval U =
      (ranπ F.op M.val.presheaf (op y) (structuredArrowOfIsTerminal ht U)).hom x :=
  rfl

/-- `Γ(y, f_* M) ≃ Γ(X, M)` as `O_Y(y)`-modules, after lifting the left side to the universe of
the global sections; `O_Y(y)` acts on `Γ(X, M)` through `pushforwardCocontinuousBaseRingHom`. -/
def pushforwardCocontinuousObjSectionsLinearEquiv :
    (ModuleCat.uliftFunctor.{u₁} (OY.obj.obj (op y))).obj
        ((PresheafOfModules.evaluation OY.obj (op y)).obj
          ((pushforwardCocontinuous.{v} F fSharp).obj M).val) ≃ₗ[OY.obj.obj (op y)]
      (ModuleCat.restrictScalars (pushforwardCocontinuousBaseRingHom fSharp ht)).obj
        ((globalSectionsFunctor OX).obj M) :=
  { Equiv.ulift.trans (pushforwardCocontinuousObjSectionsEquiv fSharp ht M) with
    map_add' := fun x x' => Subtype.ext (funext fun U =>
      map_add (ranπ F.op M.val.presheaf (op y) (structuredArrowOfIsTerminal ht U)).hom
        x.down x'.down)
    map_smul' := fun a x => Subtype.ext (funext fun U => ConcreteCategory.congr_hom
      (ranSMul_π F (structureMapPresheaf F fSharp) M.val (op y) a
        (structuredArrowOfIsTerminal ht U)) x.down) }

/-- **`Γ(y, f_* -) ≅ Γ(X, -)` at a final object `y`**, naturally in the module and linearly over
`O_Y(y)`, which acts on global sections through `pushforwardCocontinuousBaseRingHom`. The left
side is lifted to the universe of the global sections of the source. -/
def pushforwardCocontinuousSectionsIsoGlobalSections :
    pushforwardCocontinuous.{v} F fSharp ⋙ _root_.SheafOfModules.forget OY ⋙
        PresheafOfModules.evaluation OY.obj (op y) ⋙
          ModuleCat.uliftFunctor.{u₁} (OY.obj.obj (op y)) ≅
      globalSectionsFunctor OX ⋙
        ModuleCat.restrictScalars (pushforwardCocontinuousBaseRingHom fSharp ht) :=
  NatIso.ofComponents
    (fun M => (pushforwardCocontinuousObjSectionsLinearEquiv fSharp ht M).toModuleIso)
    (fun {M N} φ => by
      ext x
      refine Subtype.ext (funext fun U => ?_)
      exact ConcreteCategory.congr_hom
        (ranπ_map_functor F.op (presheafMap φ.val) (op y) (structuredArrowOfIsTerminal ht U))
        x.down)

end Stacks.SheafOfModules
