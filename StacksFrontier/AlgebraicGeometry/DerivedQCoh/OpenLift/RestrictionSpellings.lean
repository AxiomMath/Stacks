module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticModelTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens

/-!
# The two spellings of derived restriction to an open, on morphism groups

Derived restriction to an open `U` of a ringed space comes in two spellings.  The *slice* one,
`Stacks.SheafOfModules.derivedRestrict`, restricts to the site of opens contained in `U`; it is
the spelling [Stacks, Tag 08DK], [Stacks, Tag 08DL] and [Stacks, Tag 08JA] over an object of the
site are stated in.  The *open-subspace* one,
`Stacks.Cohomology.OpenSubspace.derivedRestriction`, restricts to the topological space `U`; it
is the spelling the Koszul lifting machinery behind [Stacks, Tag 08DD] uses.

`Stacks.SheafOfModules.derivedRestrictToSubspaceIso` identifies the first, followed by the
equivalence between the two models of `𝒪_U`-modules, with the second.  That equivalence is an
equivalence of abelian categories, so it induces an equivalence of derived categories, and
conjugating by the identification therefore carries morphisms between restrictions from the slice
spelling to the open-subspace spelling bijectively, compatibly with composition, carrying the
restriction of a morphism of `D(𝒪_X)` to its restriction and reflecting invertibility.

## Main definitions

* `Stacks.SheafOfModules.derivedRestrictSpellingMap`: the map on morphism groups.

## Main results

* `Stacks.SheafOfModules.derivedRestrictSpellingMap_map`: it takes the slice restriction of a
  morphism of `D(𝒪_X)` to its open-subspace restriction.
* `Stacks.SheafOfModules.derivedRestrictSpellingMap_comp`: it is compatible with composition.
* `Stacks.SheafOfModules.derivedRestrictSpellingMap_injective`: it is injective.
* `Stacks.SheafOfModules.derivedRestrictSpellingMap_surjective`: it is surjective.
* `Stacks.SheafOfModules.isIso_derivedRestrictSpellingMap` and
  `Stacks.SheafOfModules.isIso_of_isIso_derivedRestrictSpellingMap`: it preserves and reflects
  invertibility.

## Implementation notes

The map is conjugation by the identification: `g ↦ e.inv ≫ S(g) ≫ e.hom`, where `S` is the
passage between the two models of `𝒪_U`-modules on derived categories and `e` is
`derivedRestrictToSubspaceIso`.  That `S` is an equivalence is
`Stacks.ModulesOnACategory.mapDerivedCategory_isEquivalence_of_equivalence` applied to Mathlib's
`TopologicalSpace.Opens.sheafOfModulesEquivOver`; it is what makes the map injective and
iso-reflecting, through the fullness and faithfulness of `S`.

The map is not bundled as an equivalence of morphism groups.  It is one — `S` is full — but the
inverse would have to be built from `CategoryTheory.Functor.preimage`, which computes nothing,
and every use is of the properties above.  Surjectivity is the one statement that does appeal to
`CategoryTheory.Functor.preimage`, and it is used only to produce a slice-spelling
representative of a given morphism between open-subspace restrictions.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]

/-- **Passing between the two models of `𝒪_U`-modules is an equivalence of derived
categories.**  It is induced by an additive equivalence of abelian categories. -/
instance sliceToSubspaceFunctor_mapDerivedCategory_isEquivalence :
    (sliceToSubspaceFunctor Rc U).mapDerivedCategory.IsEquivalence :=
  Stacks.ModulesOnACategory.mapDerivedCategory_isEquivalence_of_equivalence
    (U.sheafOfModulesEquivOver (structureSheaf Rc))

variable [(homotopyRestriction (structureSheaf Rc) U).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Rc)) (ComplexShape.up ℤ))]
  {L M N : DerivedCategory (StructureSheafModules Rc)}

/-- **A morphism between the slice restrictions of two objects of `D(𝒪_X)`, read between their
restrictions to the open subspace `U`.**  It is conjugation by
`Stacks.SheafOfModules.derivedRestrictToSubspaceIso`. -/
def derivedRestrictSpellingMap (g : (derivedRestrict Rc U).obj L ⟶ (derivedRestrict Rc U).obj M) :
    (derivedRestriction (structureSheaf Rc) U).obj L ⟶
      (derivedRestriction (structureSheaf Rc) U).obj M :=
  ((derivedRestrictToSubspaceIso Rc U).app L).inv ≫
    (sliceToSubspaceFunctor Rc U).mapDerivedCategory.map g ≫
      ((derivedRestrictToSubspaceIso Rc U).app M).hom

/-- Conjugating back recovers the morphism between the two models of `𝒪_U`-modules. -/
theorem derivedRestrictSpellingMap_conj
    (g : (derivedRestrict Rc U).obj L ⟶ (derivedRestrict Rc U).obj M) :
    ((derivedRestrictToSubspaceIso Rc U).app L).hom ≫
        derivedRestrictSpellingMap Rc U g ≫
          ((derivedRestrictToSubspaceIso Rc U).app M).inv =
      (sliceToSubspaceFunctor Rc U).mapDerivedCategory.map g := by
  unfold derivedRestrictSpellingMap
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- **The slice restriction of a morphism of `D(𝒪_X)` goes to its open-subspace restriction.**
This is the naturality of `Stacks.SheafOfModules.derivedRestrictToSubspaceIso`. -/
theorem derivedRestrictSpellingMap_map (f : L ⟶ M) :
    derivedRestrictSpellingMap Rc U ((derivedRestrict Rc U).map f) =
      (derivedRestriction (structureSheaf Rc) U).map f :=
  Eq.trans
    (congrArg (fun t ↦ ((derivedRestrictToSubspaceIso Rc U).app L).inv ≫ t)
      ((derivedRestrictToSubspaceIso Rc U).hom.naturality f))
    (Iso.inv_hom_id_assoc ((derivedRestrictToSubspaceIso Rc U).app L)
      ((derivedRestriction (structureSheaf Rc) U).map f))

/-- **The map is compatible with composition.** -/
theorem derivedRestrictSpellingMap_comp
    (g : (derivedRestrict Rc U).obj L ⟶ (derivedRestrict Rc U).obj M)
    (g' : (derivedRestrict Rc U).obj M ⟶ (derivedRestrict Rc U).obj N) :
    derivedRestrictSpellingMap Rc U (g ≫ g') =
      derivedRestrictSpellingMap Rc U g ≫ derivedRestrictSpellingMap Rc U g' := by
  unfold derivedRestrictSpellingMap
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **The map is injective**, the passage between the two models of `𝒪_U`-modules being
faithful on derived categories. -/
theorem derivedRestrictSpellingMap_injective :
    Function.Injective
      (derivedRestrictSpellingMap Rc U (L := L) (M := M)) := by
  intro g g' h
  refine (sliceToSubspaceFunctor Rc U).mapDerivedCategory.map_injective ?_
  rw [← derivedRestrictSpellingMap_conj Rc U g, ← derivedRestrictSpellingMap_conj Rc U g', h]

/-- **The map is surjective**, the passage between the two models of `𝒪_U`-modules being full
on derived categories.  Every morphism between the restrictions of two objects of `D(𝒪_X)` to the
open subspace `U` therefore comes from one between their slice restrictions. -/
theorem derivedRestrictSpellingMap_surjective :
    Function.Surjective
      (derivedRestrictSpellingMap Rc U (L := L) (M := M)) := by
  intro h
  refine ⟨(sliceToSubspaceFunctor Rc U).mapDerivedCategory.preimage
    (((derivedRestrictToSubspaceIso Rc U).app L).hom ≫ h ≫
      ((derivedRestrictToSubspaceIso Rc U).app M).inv), ?_⟩
  unfold derivedRestrictSpellingMap
  rw [CategoryTheory.Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- **The map preserves invertibility.** -/
instance isIso_derivedRestrictSpellingMap
    (g : (derivedRestrict Rc U).obj L ⟶ (derivedRestrict Rc U).obj M) [IsIso g] :
    IsIso (derivedRestrictSpellingMap Rc U g) := by
  unfold derivedRestrictSpellingMap
  infer_instance

/-- **The map reflects invertibility**, the passage between the two models of `𝒪_U`-modules
being an equivalence on derived categories. -/
theorem isIso_of_isIso_derivedRestrictSpellingMap
    (g : (derivedRestrict Rc U).obj L ⟶ (derivedRestrict Rc U).obj M)
    (h : IsIso (derivedRestrictSpellingMap Rc U g)) : IsIso g := by
  have h' : IsIso ((sliceToSubspaceFunctor Rc U).mapDerivedCategory.map g) := by
    rw [← derivedRestrictSpellingMap_conj Rc U g]
    infer_instance
  exact isIso_of_reflects_iso g (sliceToSubspaceFunctor Rc U).mapDerivedCategory

end Stacks.SheafOfModules

end
