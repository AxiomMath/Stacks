module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction

/-!
# The induced adjunction on homotopy categories, in its conjugated spelling

`CategoryTheory.Adjunction.mapHomotopyCategory` has the degreewise unit and counit as its unit
and counit directly, with no comparison isomorphism inserted: the images of `𝟭` and of a
composite under `Functor.mapHomotopyCategory` are, on an object of the homotopy category, the
honest degreewise functors. One can also write the same transformations in the *conjugated*
spelling, by transporting `CategoryTheory.NatTrans.mapHomotopyCategory` of the degreewise unit
and counit along the comparison isomorphisms for `𝟭` and for a composite. This file records
that the two spellings agree.

That is the form in which a consumer phrasing the unit and the counit by hand — rather than
through an adjunction — meets them, so these two lemmas are what identify such a
hand-written transformation with `Adjunction.mapHomotopyCategory`'s own, and hence what let a
factorization statement proved for one be read off for the other.

## Main definitions

* `CategoryTheory.Functor.mapHomotopyCategoryIdIso`: the functor induced on homotopy categories
  by the identity functor is the identity functor.

## Main results

* `CategoryTheory.Adjunction.mapHomotopyCategory_unit_eq` and
  `CategoryTheory.Adjunction.mapHomotopyCategory_counit_eq`: the unit and the counit of the
  induced adjunction, written through the comparison isomorphisms for `𝟭` and for a composite.

## Implementation notes

Both proofs are in term mode. The two sides are `HomotopyCategory.quotient`-images of
morphisms of complexes whose sources and targets agree only definitionally — `K` against
`((𝟭 V).mapHomologicalComplex c).obj K`, and the image of a composite against the composite of
the images — so the goal is not type-correct at the `implicit` transparency level at which `rw`
and `simp` unify, and both report that they find no occurrence of a pattern that is visibly
present. Term mode type-checks at default transparency, so the degreewise identity of chain
maps and two applications of `Functor.map_comp` close the goal with no transparency lever.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe v u v' u'

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {W : Type u'}
  [Category.{v'} W] [Preadditive W]

/-- The functor induced on homotopy categories of homological complexes by the identity functor
is isomorphic to the identity functor. This is the homotopy-category analogue of
`CategoryTheory.Functor.mapHomologicalComplexIdIso`, and is obtained from it by descending along
the quotient functor. -/
def Functor.mapHomotopyCategoryIdIso (V : Type u) [Category.{v} V] [Preadditive V]
    (c : ComplexShape ι) :
    (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) :=
  show (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) from
    Quotient.natIsoLift _ (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso V c) (HomotopyCategory.quotient V c))

variable {F : V ⥤ W} {G : W ⥤ V} [F.Additive] [G.Additive]

/-- A functor sends a morphism equal to a triple composite to the triple composite of images. -/
private theorem map_comp_comp_eq_of_comp_comp_eq {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) {X Y Z T : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T} {k : X ⟶ T}
    (key : f ≫ g ≫ h = k) : Q.map k = Q.map f ≫ Q.map g ≫ Q.map h := by
  rw [← key, Q.map_comp, Q.map_comp]

/-- The unit of the adjunction induced on the homotopy categories is the degreewise unit
transported along the comparison isomorphisms for the identity functor and for the composite
`F ⋙ G`. -/
theorem Adjunction.mapHomotopyCategory_unit_eq (adj : F ⊣ G) (c : ComplexShape ι) :
    (adj.mapHomotopyCategory c).unit =
      (Functor.mapHomotopyCategoryIdIso V c).inv ≫
        NatTrans.mapHomotopyCategory adj.unit c ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).inv := by
  ext X
  obtain ⟨K⟩ := X
  have key : (Functor.mapHomologicalComplexIdIso V c).inv.app K ≫
      (NatTrans.mapHomologicalComplex adj.unit c).app K ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).inv.app K =
      (NatTrans.mapHomologicalComplex adj.unit c).app K := by
    ext i
    simp
  exact (map_comp_comp_eq_of_comp_comp_eq (HomotopyCategory.quotient _ c) key)

/-- The counit of the adjunction induced on the homotopy categories is the degreewise counit
transported along the comparison isomorphisms for the composite `G ⋙ F` and for the identity
functor. -/
theorem Adjunction.mapHomotopyCategory_counit_eq (adj : F ⊣ G) (c : ComplexShape ι) :
    (adj.mapHomotopyCategory c).counit =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F)) c).hom ≫
        NatTrans.mapHomotopyCategory adj.counit c ≫
        (Functor.mapHomotopyCategoryIdIso W c).hom := by
  ext X
  obtain ⟨K⟩ := X
  have key : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) c).hom.app K ≫
      (NatTrans.mapHomologicalComplex adj.counit c).app K ≫
      (Functor.mapHomologicalComplexIdIso W c).hom.app K =
      (NatTrans.mapHomologicalComplex adj.counit c).app K := by
    ext i
    simp
  exact (map_comp_comp_eq_of_comp_comp_eq (HomotopyCategory.quotient _ c) key)

end CategoryTheory

end
