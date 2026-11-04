module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# Colimits of modules on an algebraic space are detected on affine charts

Let `F` be an algebraic space over a scheme `S`.  A cocone of `𝒪_F`-modules on the small étale
site is a colimit as soon as, over every étale chart with *affine* underlying scheme, its cocone
of sections is a colimit of abelian groups.  Over a filtered diagram that is an elementwise
condition: the sections of the vertex over an affine chart are jointly hit by the members, and
two sections of one member with the same image agree at a later index.

This is the form in which the proof of Stacks 0GV1 computes a direct image as a colimit,
`π_*ℐ = colim π_{i,*}ℐ_i`: both sides are read on the affine charts of the base, where the
sections are those of affine schemes.

## Main results

* `AlgebraicGeometry.Space.isColimit_modules_of_affineChartSections`: the criterion for any
  shape over which abelian groups have colimits.
* `AlgebraicGeometry.Space.isColimit_modules_of_affineChartSections_of_isFiltered`: the
  elementwise criterion over a filtered shape.

## Implementation notes

The underlying abelian sheaf functor `SheafOfModules.toSheaf` preserves colimits
(`SheafOfModules.preservesColimitsOfShape_toSheaf`) and reflects isomorphisms, so it reflects
colimits; a cocone of abelian sheaves on the small étale site is detected on the affine charts by
`AlgebraicGeometry.Space.isColimit_sheaf_of_affineChartSections`, which rests on Stacks 04JS.  For
the filtered criterion the forgetful functor from abelian groups to sets reflects filtered
colimits, and the elementwise recognition of a filtered colimit of sets is
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf`.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The abelian group of sections of an `𝒪_F`-module over an étale chart `U`, as a functor. -/
abbrev moduleAbSectionsFunctor (U : SmallEtale B S hS F) :
    Modules.{u, u} B S hS F hF ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf _ ⋙ (sheafSections (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
    (op U)

/-- **A cocone of `𝒪_F`-modules is a colimit as soon as its cocones of sections over the affine
étale charts are colimits.** -/
def isColimit_modules_of_affineChartSections {J : Type u} [SmallCategory J]
    {Φ : J ⥤ Modules.{u, u} B S hS F hF} (c : Cocone Φ)
    (h : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        IsColimit ((moduleAbSectionsFunctor U).mapCocone c)) :
    IsColimit c :=
  haveI : PreservesColimitsOfShape J
      (SheafOfModules.toSheaf.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
    SheafOfModules.preservesColimitsOfShape_toSheaf _
  haveI : ReflectsColimitsOfShape J
      (SheafOfModules.toSheaf.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  isColimitOfReflects
    (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (isColimit_sheaf_of_affineChartSections B S hS F hF _ fun U hU => h U hU)

/-- **The elementwise criterion over a filtered shape.**  A cocone of `𝒪_F`-modules over a
filtered diagram is a colimit as soon as, over every affine étale chart, every section of the
vertex comes from a member, and two sections of one member with the same image in the vertex
already agree at a later index. -/
def isColimit_modules_of_affineChartSections_of_isFiltered {J : Type u} [SmallCategory J]
    [IsFiltered J] {Φ : J ⥤ Modules.{u, u} B S hS F hF} (c : Cocone Φ)
    (hsurj : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ x : c.pt.val.obj (op U), ∃ (k : J) (y : (Φ.obj k).val.obj (op U)),
          (c.ι.app k).val.app (op U) y = x)
    (hinj : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ (k : J) (y : (Φ.obj k).val.obj (op U)),
          (c.ι.app k).val.app (op U) y = 0 →
            ∃ (l : J) (g : k ⟶ l), (Φ.map g).val.app (op U) y = 0) :
    IsColimit c :=
  haveI : ReflectsColimitsOfShape J (forget AddCommGrpCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  isColimit_modules_of_affineChartSections c fun U hU =>
    isColimitOfReflects (forget AddCommGrpCat.{u}) <|
      Types.FilteredColimit.isColimitOf _ _
        (fun x => by
          obtain ⟨k, y, hy⟩ := hsurj U hU x
          exact ⟨k, y, hy.symm⟩)
        (fun i j xi xj hij => by
          let k := IsFiltered.max i j
          let f : i ⟶ k := IsFiltered.leftToMax i j
          let g : j ⟶ k := IsFiltered.rightToMax i j
          have e1 : (c.ι.app k).val.app (op U) ((Φ.map f).val.app (op U) xi) =
              (c.ι.app i).val.app (op U) xi :=
            congrArg (fun φ => φ.val.app (op U) xi) (c.w f)
          have e2 : (c.ι.app k).val.app (op U) ((Φ.map g).val.app (op U) xj) =
              (c.ι.app j).val.app (op U) xj :=
            congrArg (fun φ => φ.val.app (op U) xj) (c.w g)
          have hij' : (c.ι.app i).val.app (op U) xi = (c.ι.app j).val.app (op U) xj := hij
          have h0 : (c.ι.app k).val.app (op U)
              ((Φ.map f).val.app (op U) xi - (Φ.map g).val.app (op U) xj) = 0 := by
            rw [map_sub, e1, e2, hij', sub_self]
          obtain ⟨l, h, hh⟩ := hinj U hU k _ h0
          refine ⟨l, f ≫ h, g ≫ h, ?_⟩
          have e3 : (Φ.map (f ≫ h)).val.app (op U) xi =
              (Φ.map h).val.app (op U) ((Φ.map f).val.app (op U) xi) :=
            congrArg (fun φ => φ.val.app (op U) xi) (Φ.map_comp f h)
          have e4 : (Φ.map (g ≫ h)).val.app (op U) xj =
              (Φ.map h).val.app (op U) ((Φ.map g).val.app (op U) xj) :=
            congrArg (fun φ => φ.val.app (op U) xj) (Φ.map_comp g h)
          change (Φ.map (f ≫ h)).val.app (op U) xi = (Φ.map (g ≫ h)).val.app (op U) xj
          rw [e3, e4, ← sub_eq_zero, ← map_sub]
          exact hh)

end AlgebraicGeometry.Space

end
