module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.FilteredCardIndex.Basic

/-!
# A quasi-coherent module as a directed colimit of finitely presented modules

[Stacks, Tag 01PK] asserts that a quasi-coherent module `F` on a quasi-compact and
quasi-separated scheme `X` is the colimit of a system of finitely presented `𝒪_X`-modules indexed
by a directed partially ordered set in the universe of `X`. This file shows that this conclusion is
equivalent to `CategoryTheory.ObjectProperty.ind` applied to `SheafOfModules.isFinitePresentation`,
and derives it from three properties of `SheafOfModules.isFinitePresentation`: closure under finite
colimits, essential `u`-smallness, and density at `F`.

## Main definitions

* `Stacks.Tag01PKDirectedColimit.FinitePresentationOver`: the category of finitely presented
  `𝒪_X`-modules equipped with a morphism to `F`.

## Main results

* `Stacks.Tag01PKDirectedColimit.exists_partialOrder_index_of_isFiltered`: a colimit over a
  filtered, essentially `w`-small index category is a colimit over a nonempty directed partial
  order in `Type w`, preserving any property of the objects of the diagram.
* `Stacks.Tag01PKDirectedColimit.exists_directed_system_of_ind`: if `F` is a filtered colimit of
  finitely presented modules, then it is the colimit of a system of finitely presented modules
  over a nonempty directed partial order in `Type u`.
* `Stacks.Tag01PKDirectedColimit.ind_iff_exists_directed_system`: `F` is a filtered colimit of
  finitely presented modules if and only if it is the colimit of such a directed system.
* `Stacks.Tag01PKDirectedColimit.exists_directed_system_of_isDenseAt`: the directed system exists
  when the category of finitely presented modules over `F` is filtered and essentially `u`-small
  and has `F` as its colimit.
* `Stacks.Tag01PKDirectedColimit.exists_directed_system_of_essentiallySmall_of_isDenseAt`: the
  directed system exists when finite presentation is closed under finite colimits, the finitely
  presented modules form an essentially `u`-small family, and they are dense at `F`.

## References

* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Alexander Grothendieck and Jean-Louis Verdier, *Exposé I : Préfaisceaux*, SGA 4 I 8.1.6]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v₂ u₂ v₁ u₁ u

namespace Stacks.Tag01PKDirectedColimit

section General

variable {C : Type u₁} [Category.{v₁} C]

/-- If `D` is a filtered, essentially `w`-small category and `A` is the colimit of a diagram
`G : D ⥤ C` under the cocone `t`, then `A` is also the colimit of a diagram indexed by a nonempty
directed partially ordered set in `Type w`, every object of which is an object of `G`; so any
property `P` holding throughout `G` holds throughout the new diagram. -/
theorem exists_partialOrder_index_of_isFiltered {D : Type u₂} [Category.{v₂} D]
    [IsFiltered D] [EssentiallySmall.{w} D] {G : D ⥤ C} {A : C}
    (t : G ⟶ (Functor.const D).obj A) (ht : IsColimit (Cocone.mk A t))
    (P : C → Prop) (hP : ∀ d, P (G.obj d)) :
    ∃ (I : Type w) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ C) (s : F ⟶ (Functor.const I).obj A) (_ : IsColimit (Cocone.mk A s)),
      ∀ i, P (F.obj i) := by
  have : IsFiltered (SmallModel.{w} D) := IsFiltered.of_equivalence (equivSmallModel.{w} D)
  obtain ⟨α, _, _, _, F₀, _⟩ := IsFiltered.exists_directed (SmallModel.{w} D)
  let e : SmallModel.{w} D ≌ D := (equivSmallModel.{w} D).symm
  refine ⟨α, inferInstance, inferInstance, inferInstance, F₀ ⋙ e.functor ⋙ G,
    (((Cocone.mk A t).whisker e.functor).whisker F₀).ι, ?_, fun i => hP _⟩
  exact (Functor.Final.isColimitWhiskerEquiv F₀ _).symm (ht.whiskerEquivalence e)

end General

section Scheme

variable {X : Scheme.{u}}

/-- The category whose objects are the finitely presented `𝒪_X`-modules equipped with a
morphism to `F`, and whose morphisms are the `𝒪_X`-module maps commuting with those morphisms. -/
abbrev FinitePresentationOver (F : SheafOfModules.{u} X.ringCatSheaf) : Type (u + 1) :=
  CostructuredArrow (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι F

/-- An object of `Stacks.Tag01PKDirectedColimit.FinitePresentationOver` has finitely presented
source. -/
theorem isFinitePresentation_of_finitePresentationOver
    {F : SheafOfModules.{u} X.ringCatSheaf} (Y : FinitePresentationOver F) :
    Y.left.obj.IsFinitePresentation := Y.left.property

/-- If `F` is a filtered colimit of finitely presented `𝒪_X`-modules indexed by a small
category in `Type u`, in the sense of `CategoryTheory.ObjectProperty.ind`, then it is the colimit
of a system of finitely presented modules over a nonempty directed partially ordered set in
`Type u`. -/
theorem exists_directed_system_of_ind (F : X.Modules)
    (h : ObjectProperty.ind.{u} (SheafOfModules.isFinitePresentation X.ringCatSheaf) F) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ X.Modules) (φ : D ⟶ (Functor.const I).obj F)
      (_ : IsColimit (Cocone.mk F φ)), ∀ i, (D.obj i).IsFinitePresentation := by
  obtain ⟨J, _, _, pres, hJ⟩ := h
  exact exists_partialOrder_index_of_isFiltered pres.ι pres.isColimit
    (fun M => SheafOfModules.IsFinitePresentation M) hJ

/-- If `F` is the colimit of a system of finitely presented `𝒪_X`-modules over a nonempty
directed partially ordered set in `Type u`, then it is a filtered colimit of finitely presented
modules in the sense of `CategoryTheory.ObjectProperty.ind`. -/
theorem ind_of_exists_directed_system (F : X.Modules)
    (h : ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ X.Modules) (φ : D ⟶ (Functor.const I).obj F)
      (_ : IsColimit (Cocone.mk F φ)), ∀ i, (D.obj i).IsFinitePresentation) :
    ObjectProperty.ind.{u} (SheafOfModules.isFinitePresentation X.ringCatSheaf) F := by
  obtain ⟨I, _, _, _, D, φ, hcolim, hfp⟩ := h
  exact ObjectProperty.of_essentiallySmall_index ⟨D, φ, hcolim⟩ hfp

/-- `F` is a filtered colimit of finitely presented `𝒪_X`-modules, in the sense of
`CategoryTheory.ObjectProperty.ind`, if and only if it is the colimit of a system of finitely
presented modules over a nonempty directed partially ordered set in `Type u`. -/
theorem ind_iff_exists_directed_system (F : X.Modules) :
    ObjectProperty.ind.{u} (SheafOfModules.isFinitePresentation X.ringCatSheaf) F ↔
      ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : I ⥤ X.Modules) (φ : D ⟶ (Functor.const I).obj F)
        (_ : IsColimit (Cocone.mk F φ)), ∀ i, (D.obj i).IsFinitePresentation :=
  ⟨exists_directed_system_of_ind F, ind_of_exists_directed_system F⟩

/-- If the category of finitely presented `𝒪_X`-modules equipped with a morphism to `F` is
filtered and essentially `u`-small, and `F` is the colimit of that canonical diagram, then `F` is
a filtered colimit of finitely presented modules in the sense of
`CategoryTheory.ObjectProperty.ind`. -/
theorem ind_of_isDenseAt (F : SheafOfModules.{u} X.ringCatSheaf)
    [IsFiltered.{u, u + 1} (FinitePresentationOver F)]
    [EssentiallySmall.{u, u, u + 1} (FinitePresentationOver F)]
    (h : (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι.isDenseAt F) :
    ObjectProperty.ind.{u} (SheafOfModules.isFinitePresentation X.ringCatSheaf) F := by
  obtain ⟨hc⟩ := h
  exact ObjectProperty.of_essentiallySmall_index ⟨_, _, hc⟩ fun Y => Y.left.2

/-- If the category of finitely presented `𝒪_X`-modules equipped with a morphism to `F` is
filtered and essentially `u`-small, and `F` is the colimit of that canonical diagram, then `F` is
the colimit of a system of finitely presented modules over a nonempty directed partially ordered
set in `Type u`. -/
theorem exists_directed_system_of_isDenseAt (F : SheafOfModules.{u} X.ringCatSheaf)
    [IsFiltered.{u, u + 1} (FinitePresentationOver F)]
    [EssentiallySmall.{u, u, u + 1} (FinitePresentationOver F)]
    (h : (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι.isDenseAt F) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ X.Modules) (φ : D ⟶ (Functor.const I).obj F)
      (_ : IsColimit (Cocone.mk F φ)), ∀ i, (D.obj i).IsFinitePresentation :=
  exists_directed_system_of_ind F (ind_of_isDenseAt F h)

/-- If finite presentation of `𝒪_X`-modules is closed under finite colimits, then the category
of finitely presented `𝒪_X`-modules equipped with a morphism to `F` is filtered. -/
theorem isFiltered_finitePresentationOver (F : SheafOfModules.{u} X.ringCatSheaf)
    [(SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteColimits] :
    IsFiltered.{u, u + 1} (FinitePresentationOver F) :=
  @IsFiltered.of_hasFiniteColimits _ _ CostructuredArrow.hasFiniteColimits

/-- `F` is the colimit of a system of finitely presented `𝒪_X`-modules over a nonempty directed
partially ordered set in `Type u`, provided that

1. finite presentation of `𝒪_X`-modules is closed under finite colimits;
2. the finitely presented `𝒪_X`-modules form an essentially `u`-small family;
3. the inclusion of the finitely presented modules is dense at `F`, i.e. `F` is the colimit of
   the finitely presented modules over it. -/
theorem exists_directed_system_of_essentiallySmall_of_isDenseAt
    (F : SheafOfModules.{u} X.ringCatSheaf)
    [(SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteColimits]
    [ObjectProperty.EssentiallySmall.{u} (SheafOfModules.isFinitePresentation X.ringCatSheaf)]
    (h : (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι.isDenseAt F) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ X.Modules) (φ : D ⟶ (Functor.const I).obj F)
      (_ : IsColimit (Cocone.mk F φ)), ∀ i, (D.obj i).IsFinitePresentation :=
  have := isFiltered_finitePresentationOver F
  exists_directed_system_of_isDenseAt F h

end Scheme

end Stacks.Tag01PKDirectedColimit

end
