module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.AbsoluteRightDerived
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.ChaoticRingedSites

/-!
# A right derived functor followed by an exact functor's derived functor

Let `w : A ⥤ B` be additive, let `Rw : D(A) ⥤ D(B)` be a right derived functor of
`w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh` with unit `α`, and let
`G : B ⥤ C` be additive and exact. This file shows that `Rw ⋙ G.mapDerivedCategory` is a right
derived functor of `(w ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh`, and
names its unit.

**Why this statement exists.** It is one of the two derived-category statements the
*post-composition* coherence for the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` needs — the other is
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Qh`. The coherence reads the bridge
for `w ⋙ G` *at* `Rw ⋙ G.mapDerivedCategory`, and "at" presupposes that the composite is a right
derived functor of `w ⋙ G`, with a unit written in terms of `α`. The implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` record that presupposition as
undischarged.

## Main definitions and results

* `Stacks.DerivedFunctor.postcomposeSourceIso`: the identification of the two sources,
  `(w ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh` with
  `(w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh) ⋙ G.mapDerivedCategory`.
* `Stacks.DerivedFunctor.postcomposeUnit`: the unit — that identification followed by `α`
  pushed through `G.mapDerivedCategory`.
* `Stacks.DerivedFunctor.postcomposeUnit_app`: **the unit at an object is
  `G.mapDerivedCategoryFactorsh` inverted, followed by `G.mapDerivedCategory` applied to `α`.**
  The reassociation and the comparison of `(w ⋙ G).mapHomotopyCategory` with
  `w.mapHomotopyCategory ⋙ G.mapHomotopyCategory` contribute identity morphisms only.
* `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`: **`Rw ⋙ G.mapDerivedCategory` is a
  right derived functor of `w ⋙ G` with that unit**, as soon as every cochain complex in `A`
  admits a quasi-isomorphism into a K-injective one.

## Implementation notes

The proof is two steps. Absoluteness of a right derived functor computed by K-injective
resolutions —
`Stacks.SmallDerivedCategory.isRightDerivedFunctor_comp_of_exists_quasiIso_isKInjective` — gives
that `Rw ⋙ G.mapDerivedCategory` is a right derived functor of
`(w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh) ⋙ G.mapDerivedCategory`, with the bare
whiskered unit; `CategoryTheory.Functor.isRightDerivedFunctor_of_iso` then moves the source along
`postcomposeSourceIso`.

`postcomposeSourceIso` repeats, at explicit `HasDerivedCategory` universes, the composite of
`CategoryTheory.Functor.mapHomotopyCategoryQhCompMapDerivedCategoryIso`: that declaration states
its three categories with `Category*` and finds `HasDerivedCategory` by instance search, which
fixes the derived categories to the locally small model and so does not instantiate at the
universes this file's consumers use.

In `postcomposeUnit_app` the identity morphism contributed by
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` at `CategoryTheory.Iso.refl (w ⋙ G)` is
removed by a `congrArg` into `CategoryTheory.Functor.map_id`, and the final `𝟙` is cancelled by
the file-scoped `id_comp_comp` rather than by `simp only [Category.id_comp]`: the identity sits at
the spelling `Qh.obj ((w.mapHomotopyCategory _ ⋙ G.mapHomotopyCategory _).obj K)` while the
morphism after it starts at
`Qh.obj (G.mapHomotopyCategory _ |>.obj (w.mapHomotopyCategory _ |>.obj K))`, and across those
two spellings of one object a rewrite is not type-correct.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB wC vC uC

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (w : A ⥤ B) [w.Additive] (G : B ⥤ C) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)

/-- An identity morphism at the head of a composite. Stated at an arbitrary category with the
objects implicit, so that the identity may be given at either of two spellings of its object. -/
private theorem id_comp_comp {D : Type*} [Category* D] {x y z : D} (i : x ⟶ x) (f : x ⟶ y)
    (g : y ⟶ z) (hi : i = CategoryStruct.id x) : (i ≫ f) ≫ g = f ≫ g := by
  rw [hi, Category.id_comp]

/-- **The two sources of the units agree.** For `G` exact, the homotopy-category functor of
`w ⋙ G` followed by `Qh` is the homotopy-category functor of `w` followed by `Qh` and then by
`G.mapDerivedCategory`: the comparison of `(w ⋙ G).mapHomotopyCategory` with
`w.mapHomotopyCategory ⋙ G.mapHomotopyCategory`, then
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted. -/
def postcomposeSourceIso :
    (w ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        G.mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (w ⋙ G)) (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (w.mapHomotopyCategory (ComplexShape.up ℤ))
          G.mapDerivedCategoryFactorsh.symm ≪≫
        (Functor.associator _ _ _).symm

/-- **The unit of `Rw ⋙ G.mapDerivedCategory` as a right derived functor of `w ⋙ G`**: the
identification of the two sources, followed by `α` pushed through `G.mapDerivedCategory`. -/
def postcomposeUnit :
    (w ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rw ⋙ G.mapDerivedCategory :=
  (postcomposeSourceIso w G).hom ≫
    Functor.whiskerRight α G.mapDerivedCategory ≫ (Functor.associator _ _ _).hom

variable [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **A right derived functor followed by an exact functor's derived functor is a right derived
functor.** If every cochain complex in `A` admits a quasi-isomorphism into a K-injective one, and
`Rw` is a right derived functor of `w` with unit `α`, then `Rw ⋙ G.mapDerivedCategory` is a right
derived functor of `w ⋙ G` with unit `Stacks.DerivedFunctor.postcomposeUnit`.

This is what "the bridge for `w ⋙ G` taken at `Rw ⋙ G.mapDerivedCategory`" presupposes. -/
theorem isRightDerivedFunctor_postcompose
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    (Rw ⋙ G.mapDerivedCategory).IsRightDerivedFunctor (postcomposeUnit w G Rw α)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  let := Stacks.SmallDerivedCategory.isRightDerivedFunctor_comp_of_exists_quasiIso_isKInjective
    hres (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Rw α
    G.mapDerivedCategory
  Functor.isRightDerivedFunctor_of_iso (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Rw ⋙ G.mapDerivedCategory)
    (Functor.whiskerRight α G.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (postcomposeSourceIso w G)

omit [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] in
/-- **The unit at an object.** The comparison of the two homotopy-category functors and the
reassociations contribute identity morphisms, so what is left is
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted followed by `G.mapDerivedCategory`
applied to `α`. This is the form the post-composition coherence consumes, and it is the analogue
of the hypothesis `hα'` of
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp`. -/
theorem postcomposeUnit_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (postcomposeUnit w G Rw α).app K =
      G.mapDerivedCategoryFactorsh.inv.app
          ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (α.app K) := by
  have h0 : (Functor.mapHomotopyCategoryCompIso (Iso.refl (w ⋙ G))
      (ComplexShape.up ℤ)).inv.app K = CategoryStruct.id
        ((w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := rfl
  have h1 : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (w ⋙ G))
        (ComplexShape.up ℤ)).inv.app K)
      = CategoryStruct.id (DerivedCategory.Qh.obj
        ((w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    (congrArg DerivedCategory.Qh.map h0).trans (DerivedCategory.Qh.map_id _)
  have h2 : (postcomposeUnit w G Rw α).app K =
      (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (w ⋙ G))
            (ComplexShape.up ℤ)).inv.app K) ≫ CategoryStruct.id _ ≫
          G.mapDerivedCategoryFactorsh.inv.app
              ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ CategoryStruct.id _) ≫
        G.mapDerivedCategory.map (α.app K) ≫ CategoryStruct.id _ := rfl
  rw [h2, h1]
  simp only [Category.id_comp, Category.comp_id]
  exact id_comp_comp _ _ _ rfl

end Stacks.DerivedFunctor

end
