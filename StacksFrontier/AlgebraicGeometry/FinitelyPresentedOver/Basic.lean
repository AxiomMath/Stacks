module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension

/-!
# The finitely presented modules over a given module

For a module `F` on a scheme `X`, the objects of `X.Modules` that are of finite presentation
and come with a morphism to `F` form a category, and those morphisms assemble into a canonical
cocone with point `F`.  That category is the index category through which a quasi-coherent
module on a quasi-compact quasi-separated scheme is exhibited as a filtered colimit of finitely
presented ones ([Stacks Project, Tag 01PJ]); this file establishes the properties of the index
category itself, which are independent of that scheme-theoretic statement.

## Main definitions

* `Stacks.AlgebraicGeometry.isFinitePresentationProperty`: finite presentation as an
  `ObjectProperty` of `X.Modules`.
* `Stacks.AlgebraicGeometry.FinitelyPresentedOver`: the full subcategory of `Over F` on the
  objects whose source is of finite presentation.
* `Stacks.AlgebraicGeometry.FinitelyPresentedOver.diagram` and
  `...FinitelyPresentedOver.cocone`: that category viewed as a diagram in `X.Modules`, and its
  canonical cocone with point `F`.
* `Stacks.AlgebraicGeometry.FinitelyPresentedOver.toCostructuredArrow`: the fully faithful
  comparison with `CostructuredArrow (isFinitePresentationProperty X).ι F`, which is what makes
  the category essentially small.

## Main results

* `Stacks.AlgebraicGeometry.isFinitePresentation_zero`: the zero module is of finite
  presentation.
* `Stacks.AlgebraicGeometry.FinitelyPresentedOver.exists_hom_comp_eq`: any two parallel
  morphisms are equalised by a morphism to a further object.  This is the `cocone_maps` half of
  filteredness.
* `Stacks.AlgebraicGeometry.FinitelyPresentedOver.essentiallySmall`: the category is
  essentially small in the universe of the scheme.
* `Stacks.AlgebraicGeometry.FinitelyPresentedOver.nonempty`: the category is nonempty.

## Implementation notes

`isFinitePresentationProperty` is a plain `def` rather than a local abbreviation inside each
proof: the `Category` instance on `ObjectProperty.FullSubcategory` is found for a named
property and is not found for one introduced by `let`, and that — not transparency — is what
makes the comparison functor below elaborate without any option being set.

The remaining half of filteredness, `cocone_objs`, asks for a single finitely presented object
receiving maps from two given ones over `F`, for which the biproduct is the natural candidate.
It is not proved here because the closure of finite presentation under binary biproducts is not
available in this development: the one construction of a presentation of a biproduct,
`biprod_presentation`, carries no universe parameters
and so exists only for modules in `Type 0`.  Once that is generalised, `IsFiltered` for this
category follows from `exists_hom_comp_eq`, `nonempty` and nothing else.

## References

* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
* [Stacks Project, Tag 01BC](https://stacks.math.columbia.edu/tag/01BC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules
open scoped ZeroObject

universe u

namespace Stacks.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Finite presentation, as a property of the objects of `X.Modules`. -/
def isFinitePresentationProperty (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun M => M.IsFinitePresentation

/-- The category of finitely presented modules over a given module `F`: the full subcategory of
`Over F` on the objects whose source is of finite presentation. -/
abbrev FinitelyPresentedOver {X : Scheme.{u}} (F : X.Modules) :=
  ObjectProperty.FullSubcategory (fun A : Over F => isFinitePresentationProperty X A.left)

namespace FinitelyPresentedOver

/-- `FinitelyPresentedOver F` viewed as a diagram in `X.Modules`. -/
noncomputable def diagram {X : Scheme.{u}} (F : X.Modules) :
    FinitelyPresentedOver F ⥤ X.Modules where
  obj A := A.1.left
  map f := f.1.left
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical cocone on `diagram F` with point `F`, whose legs are the structural
morphisms. -/
noncomputable def cocone {X : Scheme.{u}} (F : X.Modules) : Cocone (diagram F) where
  pt := F
  ι :=
    { app := fun A => A.1.hom
      naturality _ _ f := Over.w f.1 }

/-- The category `FinitelyPresentedOver F` is nonempty: it contains the zero morphism from the
zero module. -/
instance nonempty {X : Scheme.{u}} (F : X.Modules) : Nonempty (FinitelyPresentedOver F) :=
  ⟨⟨Over.mk (0 : (0 : X.Modules) ⟶ F), AlgebraicGeometry.isFinitePresentation_zero X⟩⟩

/-- Any two parallel morphisms of `FinitelyPresentedOver F` become equal after composing with a
morphism to a further object of `FinitelyPresentedOver F`. -/
theorem exists_hom_comp_eq {X : Scheme.{u}} (F : X.Modules)
    (A B : FinitelyPresentedOver F) (f g : A ⟶ B) :
    ∃ (Z : FinitelyPresentedOver F) (q : B ⟶ Z), f ≫ q = g ≫ q := by
  have hB : B.1.left.IsFinitePresentation := B.2
  have hA : A.1.left.IsFinitePresentation := A.2
  have : A.1.left.IsFiniteType :=
    _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} A.1.left
  set d : A.1.left ⟶ B.1.left := f.1.left - g.1.left with hdef
  have hd : d ≫ B.1.hom = 0 := by
    rw [hdef, Preadditive.sub_comp, Over.w f.1, Over.w g.1, sub_self]
  refine ⟨⟨Over.mk (cokernel.desc d B.1.hom hd), SheafOfModules.isFinitePresentation_cokernel d⟩,
    ObjectProperty.homMk (Over.homMk (cokernel.π d)),
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)⟩
  change f.1.left ≫ cokernel.π d = g.1.left ≫ cokernel.π d
  rw [← sub_eq_zero, ← Preadditive.sub_comp]
  exact cokernel.condition d

/-- The comparison functor from `FinitelyPresentedOver F` to the costructured arrows over `F`
from the full subcategory of finitely presented modules. -/
noncomputable def toCostructuredArrow {X : Scheme.{u}} (F : X.Modules) :
    FinitelyPresentedOver F ⥤ CostructuredArrow (isFinitePresentationProperty X).ι F where
  obj A := CostructuredArrow.mk (Y := ObjectProperty.FullSubcategory.mk _ A.2) A.1.hom
  map f := CostructuredArrow.homMk (ObjectProperty.homMk f.1.left) (Over.w f.1)

/-- The functor `toCostructuredArrow F` is full. -/
instance toCostructuredArrow_full {X : Scheme.{u}} (F : X.Modules) :
    (toCostructuredArrow F).Full :=
  ⟨fun {_ _} f => ⟨ObjectProperty.homMk (Over.homMk f.left.hom (by exact f.w)), rfl⟩⟩

/-- The functor `toCostructuredArrow F` is faithful. -/
instance toCostructuredArrow_faithful {X : Scheme.{u}} (F : X.Modules) :
    (toCostructuredArrow F).Faithful :=
  ⟨fun h => ObjectProperty.hom_ext _ (Over.OverMorphism.ext (congrArg (fun t => t.left.hom) h))⟩

/-- The category `FinitelyPresentedOver F` is essentially small in the universe of the scheme. -/
instance essentiallySmall {X : Scheme.{u}} (F : X.Modules) :
    EssentiallySmall.{u} (FinitelyPresentedOver F) := by
  have h₁ : ObjectProperty.EssentiallySmall.{u} (fun M : X.Modules => M.IsFiniteType) :=
    SheafOfModules.essentiallySmall_isFiniteType X.toRingedSpace
  have h₂ : ObjectProperty.EssentiallySmall.{u} (isFinitePresentationProperty X) :=
    ObjectProperty.EssentiallySmall.of_le (P := isFinitePresentationProperty X)
      (Q := fun M : X.Modules => M.IsFiniteType)
      (fun M h => by
        have : M.IsFinitePresentation := h
        exact _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M)
  exact essentiallySmall_of_fully_faithful (toCostructuredArrow F)

end FinitelyPresentedOver

end Stacks.AlgebraicGeometry

end
