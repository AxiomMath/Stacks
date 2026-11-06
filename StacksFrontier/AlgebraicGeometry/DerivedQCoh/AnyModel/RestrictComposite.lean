module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.CoverDetection
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens

/-!
# Composites of restrictions on derived categories, at an arbitrary model

Restriction of sheaves of modules along an open immersion is exact, so it acts on unbounded
derived categories with no derivation; and Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` says that restricting along a composite of
open immersions is restricting twice. This file carries that coherence to derived categories with
the model of each of the three categories left free, and draws the two consequences the
compact-generation cluster needs:

* an object vanishing on an open subscheme vanishes on every open immersion whose image lands in
  that open — the step `M|_U = 0 ⟹ M|_{U ∩ V} = 0` of the proof of [Stacks, Tag 09IS];
* restriction along an *isomorphism* of schemes is an equivalence on derived categories, in the
  three forms used there: it reflects the zero object, it is faithful, and it reflects the
  vanishing of the morphisms out of all shifts of an object.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompIsoId` — on sheaves of modules, the
  composite of the restrictions along two morphisms composing to the identity is the identity.
* `Stacks.DerivedQCoh.AnyModel.derivedRestrictCompObjIso` — the composite coherence on derived
  categories, evaluated at an object.
* `Stacks.DerivedQCoh.AnyModel.derivedRestrictCompIsoId` — the derived form of
  `restrictFunctorCompIsoId`.

## Main results

* `Stacks.DerivedQCoh.AnyModel.isZero_derivedRestrict_of_range_le` — an object of `D(𝒪_X)`
  restricting to zero on an open subscheme restricts to zero along any open immersion with image
  inside it.
* `Stacks.DerivedQCoh.AnyModel.faithful_derivedRestrict_of_compEqId` — restriction along a
  morphism with a section is faithful on derived categories.
* `Stacks.DerivedQCoh.AnyModel.isZero_of_isZero_derivedRestrict_of_compEqId` — and it reflects the
  zero object.
* `Stacks.DerivedQCoh.AnyModel.forall_hom_shift_eq_zero_of_faithful` — a faithful
  shift-compatible functor reflects the vanishing of all morphisms out of all shifts of an
  object.

## Implementation notes

**The model of each derived category is a binder.** The results below are the ones
[Stacks, Tag 09IS] consumes, and that tag has content only at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`; a statement proved at
`CategoryTheory.HasDerivedCategory.standard` says nothing about it. Nothing in the arguments
needs a particular model: they are composites of
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso`,
`CategoryTheory.Functor.mapDerivedCategoryCongr` and
`CategoryTheory.Functor.mapDerivedCategoryId`, all three of which carry their models as instance
arguments.

**Relation to the two statements this generalises.**
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCompInvIso` is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCompIsoId` in the case where the section is the
inverse, and `Stacks.DerivedQCoh.derivedRestrictCompIso` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/EventualExtVanishing.lean` is
`Stacks.DerivedQCoh.AnyModel.derivedRestrictCompIsoId` for an isomorphism of schemes and at the
standard model, that file installing `CategoryTheory.HasDerivedCategory.standard` as a local
instance throughout. The dedup-correct move is to generalise those two in place — taking two
morphisms and an equation instead of a morphism and its inverse, and adding the two model binders
— and keep one declaration of each; neither file is this one's to change, and the one-line form of
both changes is recorded in the report of the work that produced this file.

## References

* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v₁ v₂ u₁ u₂ u w w'

namespace AlgebraicGeometry.Scheme.Modules

/-- **Restriction along two morphisms composing to the identity composes to the identity.** For
open immersions `a : Y ⟶ Z` and `b : Z ⟶ Y` with `a ≫ b = 𝟙 Y`, restricting a sheaf of
`𝒪_Y`-modules along `b` and then along `a` returns it.

This is `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` followed by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` at the equation and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorId`. -/
def restrictFunctorCompIsoId {Y Z : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] (hab : a ≫ b = 𝟙 Y) :
    restrictFunctor b ⋙ restrictFunctor a ≅ 𝟭 Y.Modules :=
  (restrictFunctorComp a b).symm ≪≫ restrictFunctorCongr hab ≪≫ restrictFunctorId

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.DerivedQCoh.AnyModel

/-! ### Restriction along a composite -/

section Composite

variable {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  [HasDerivedCategory.{w} Z.Modules]

/-- **Restricting twice is restricting along the composite**, on derived categories and at an
object. This is `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` carried across the
localization by `CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso`. -/
def derivedRestrictCompObjIso (M : DerivedCategory X.Modules) :
    (Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj M) ≅
      (Scheme.Modules.restrictFunctor (g ≫ j)).mapDerivedCategory.obj M :=
  (Functor.mapDerivedCategoryCompIsoOfCompIso (Scheme.Modules.restrictFunctorComp g j).symm).app M

/-- An object of `D(𝒪_X)` vanishing on `Y` vanishes on `Z`, for open immersions `Z ⟶ Y ⟶ X`. -/
theorem isZero_derivedRestrict_comp {M : DerivedCategory X.Modules}
    (hM : IsZero ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor (g ≫ j)).mapDerivedCategory.obj M) :=
  (((Scheme.Modules.restrictFunctor g).mapDerivedCategory).map_isZero hM).of_iso
    (derivedRestrictCompObjIso g j M).symm

/-- An object of `D(𝒪_X)` vanishing along a composite `Z ⟶ Y ⟶ X` of open immersions vanishes
after restricting first to `Y` and then to `Z`. -/
theorem isZero_derivedRestrict_derivedRestrict_of_comp {M : DerivedCategory X.Modules}
    (hM : IsZero ((Scheme.Modules.restrictFunctor (g ≫ j)).mapDerivedCategory.obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj M)) :=
  hM.of_iso (derivedRestrictCompObjIso g j M)

end Composite

/-- Restriction along equal open immersions gives the same vanishing on derived categories. -/
theorem isZero_derivedRestrict_congr {X Z : Scheme.{u}} {g g' : Z ⟶ X} (h : g = g')
    [IsOpenImmersion g] [IsOpenImmersion g']
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Z.Modules]
    {M : DerivedCategory X.Modules}
    (hM : IsZero ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor g').mapDerivedCategory.obj M) :=
  hM.of_iso ((Functor.mapDerivedCategoryCongr
    (Scheme.Modules.restrictFunctorCongr h)).app M).symm

/-- **An object vanishing on an open subscheme vanishes on anything inside it.** Let `U ⊆ X` be an
open subscheme and let `g : Z ⟶ X` be an open immersion whose image is contained in `U`. If `M`
restricts to zero on `U` then it restricts to zero along `g`.

This is the step `M|_U = 0 ⟹ M|_{U ∩ V} = 0` of the proof of [Stacks, Tag 09IS]. The containment
of the images lets `g` be factored as `Z ⟶ U ⟶ X` by
`AlgebraicGeometry.IsOpenImmersion.lift`, and
`Stacks.DerivedQCoh.AnyModel.isZero_derivedRestrict_comp` applies to that factorization. -/
theorem isZero_derivedRestrict_of_range_le {X Z : Scheme.{u}} (U : X.Opens) (g : Z ⟶ X)
    [IsOpenImmersion g] (hg : Set.range g.base ⊆ (U : Set X))
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} U.toScheme.Modules]
    [HasDerivedCategory.{w} Z.Modules]
    {M : DerivedCategory X.Modules}
    (hM : IsZero ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj M) :=
  have hrange : Set.range g.base ⊆ Set.range U.ι.base := by simpa using hg
  isZero_derivedRestrict_congr (IsOpenImmersion.lift_fac U.ι g hrange)
    (isZero_derivedRestrict_comp (IsOpenImmersion.lift U.ι g hrange) U.ι hM)

/-! ### Restriction along a morphism with a section -/

section Section

variable {Y Z : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b]
  (hab : a ≫ b = 𝟙 Y)
  [HasDerivedCategory.{w} Y.Modules] [HasDerivedCategory.{w} Z.Modules]

include hab

/-- **The derived form of `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompIsoId`**: for open
immersions `a : Y ⟶ Z` and `b : Z ⟶ Y` with `a ≫ b = 𝟙 Y`, restricting along `b` and then along
`a` is the identity of `D(𝒪_Y)`. -/
def derivedRestrictCompIsoId :
    (Scheme.Modules.restrictFunctor b).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor a).mapDerivedCategory ≅
      𝟭 (DerivedCategory Y.Modules) :=
  Functor.mapDerivedCategoryCompIsoOfCompIso (Scheme.Modules.restrictFunctorCompIsoId a b hab) ≪≫
    Functor.mapDerivedCategoryId Y.Modules

/-- Restriction along a morphism admitting a section is faithful on derived categories: composing
it with restriction along the section gives the identity, by
`Stacks.DerivedQCoh.AnyModel.derivedRestrictCompIsoId`. -/
theorem faithful_derivedRestrict_of_compEqId :
    (Scheme.Modules.restrictFunctor b).mapDerivedCategory.Faithful :=
  Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp
    (Scheme.Modules.restrictFunctor b) (Scheme.Modules.restrictFunctor a)
    (Scheme.Modules.restrictFunctorCompIsoId a b hab)

/-- Restriction along a morphism admitting a section reflects the zero object of the derived
category. -/
theorem isZero_of_isZero_derivedRestrict_of_compEqId {M : DerivedCategory Y.Modules}
    (hM : IsZero ((Scheme.Modules.restrictFunctor b).mapDerivedCategory.obj M)) :
    IsZero M :=
  (((Scheme.Modules.restrictFunctor a).mapDerivedCategory).map_isZero hM).of_iso
    ((derivedRestrictCompIsoId a b hab).app M).symm

end Section

/-! ### Reflecting the vanishing of maps out of all shifts -/

/-- **A faithful shift-compatible functor reflects the vanishing of the morphisms out of all
shifts of an object.** If every morphism `(G K)⟦n⟧ ⟶ M'` vanishes and `G M ≅ M'`, then every
morphism `K⟦n⟧ ⟶ M` vanishes.

Transport a morphism `g : K⟦n⟧ ⟶ M` to `G (K⟦n⟧) ⟶ G M ≅ M'`, read the source as `(G K)⟦n⟧`
through `CategoryTheory.Functor.commShiftIso`, and conclude `G g = 0` by cancelling the two
isomorphisms; faithfulness then gives `g = 0`. -/
theorem forall_hom_shift_eq_zero_of_faithful {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    (G : C ⥤ D) [G.Faithful] [G.PreservesZeroMorphisms] [G.CommShift ℤ]
    {K M : C} {M' : D} (eM : G.obj M ≅ M')
    (h : ∀ (n : ℤ) (gg : (G.obj K)⟦n⟧ ⟶ M'), gg = 0) (n : ℤ) (g : K⟦n⟧ ⟶ M) :
    g = 0 := by
  refine G.map_injective ((cancel_mono eM.hom).1 ((cancel_epi ((G.commShiftIso n).inv.app K)).1 ?_))
  rw [Functor.map_zero, zero_comp, comp_zero, ← Category.assoc]
  exact h n _

end Stacks.DerivedQCoh.AnyModel

end
