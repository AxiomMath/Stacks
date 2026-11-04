module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.CategoryTheory.Monoidal.PullbackComparisonDevissage

/-!
# The map of Equation 48.8.0.1 commutes with the shift

Let `F : C ⥤ D` be a monoidal functor with adjunctions `F ⊣ G ⊣ a`, all three functors carrying
shift structures for which both adjunctions are compatible with the shift, and suppose the
projection-formula map is invertible. The map `F K ⊗ a 𝟙 ⟶ a K` of Equation 48.8.0.1
([Stacks, Tag 0A9S]), `CategoryTheory.MonoidalProjectionFormula.comparisonUnit`, is a morphism of
functors of `K`. This file shows that it commutes with the shift as soon as the three monoidal
ingredients it is built from do so in the first variable:

* the action of the tensor product on morphisms in the second variable, `K ↦ K ◁ g`, on `C` and on
  `D` (`CategoryTheory.MonoidalProjectionFormula.tensorRightMap`);
* the cotensorator `F (K ⊗ M) ⟶ F K ⊗ F M` of `F`, read in `K` at a fixed `M`
  (`CategoryTheory.MonoidalProjectionFormula.oplaxNatTransLeft`);
* the right unitor `K ⊗ 𝟙 ≅ K`.

The proof writes the projection-formula map and the comparison map as composites of whiskerings
of the units of the two adjunctions, of these three transformations, and of the counits, so that
the compatibility with the shift follows from the closure of `CategoryTheory.NatTrans.CommShift`
under composition and whiskering.

## Main results

* `CategoryTheory.MonoidalProjectionFormula.commShift_projectionFormulaNatTransLeft` — the
  projection-formula map `K ⊗ G E ⟶ G (F K ⊗ E)` commutes with the shift in `K`.
* `CategoryTheory.MonoidalProjectionFormula.commShift_comparisonUnit` — the map of
  Equation 48.8.0.1 commutes with the shift.

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
-/

@[expose] public noncomputable section

namespace CategoryTheory.MonoidalProjectionFormula

open MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- The action of the tensor product on a morphism `g : M ⟶ M'` in the second variable, as a
morphism of functors `K ↦ K ◁ g : (- ⊗ M) ⟶ (- ⊗ M')`. -/
@[simps]
def tensorRightMap {M M' : C} (g : M ⟶ M') : tensorRight M ⟶ tensorRight M' where
  app K := K ◁ g
  naturality _ _ f := (whisker_exchange f g).symm

variable (F : C ⥤ D) [F.Monoidal]

/-- The cotensorator `δ F K M : F (K ⊗ M) ⟶ F K ⊗ F M` of a monoidal functor at a fixed `M`, as
a morphism of functors of `K`. -/
@[simps]
def oplaxNatTransLeft (M : C) : tensorRight M ⋙ F ⟶ F ⋙ tensorRight (F.obj M) where
  app K := Functor.OplaxMonoidal.δ F K M
  naturality _ _ f := (Functor.OplaxMonoidal.δ_natural_left F f M).symm

variable {F} {G : D ⥤ C} (adj : F ⊣ G)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]
  [F.CommShift A] [G.CommShift A] [adj.CommShift A]
  [∀ M : C, (tensorRight M).CommShift A] [∀ M : D, (tensorRight M).CommShift A]

/-- The projection-formula map at a fixed `E`, written as a composite of whiskerings of the unit
of `F ⊣ G`, of the cotensorator of `F` and of `F K` tensored with the counit of `F ⊣ G`. -/
theorem projectionFormulaNatTransLeft_eq (E : D) :
    projectionFormulaNatTransLeft adj E =
      (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (tensorRight (G.obj E)) adj.unit ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (oplaxNatTransLeft F (G.obj E) ≫
            Functor.whiskerLeft F (tensorRightMap (adj.counit.app E))) G ≫
          (Functor.associator _ _ _).hom := by
  ext K
  apply ext_of_counit adj
  simp [map_projectionFormulaMap_comp_counit]

/-- **The projection-formula map commutes with the shift** in the variable `K`, as soon as the
cotensorator of `F` does in its first variable and the tensor product of `D` acts on morphisms in
the second variable compatibly with the shift. -/
theorem commShift_projectionFormulaNatTransLeft
    [∀ M : C, NatTrans.CommShift (oplaxNatTransLeft F M) A]
    [∀ {M M' : D} (g : M ⟶ M'), NatTrans.CommShift (tensorRightMap g) A] (E : D) :
    NatTrans.CommShift (projectionFormulaNatTransLeft adj E) A := by
  rw [projectionFormulaNatTransLeft_eq]
  infer_instance

variable {a : C ⥤ D} (adj' : G ⊣ a) [∀ (E : D) (K : C), IsIso (projectionFormulaMap adj E K)]
  [a.CommShift A] [adj'.CommShift A]

/-- The projection-formula map at a fixed `E`, as an isomorphism of functors of `K`. -/
def projectionFormulaNatIsoLeft (E : D) : tensorRight (G.obj E) ≅ F ⋙ tensorRight E ⋙ G :=
  NatIso.ofComponents (fun K => asIso (projectionFormulaMap adj E K))
    (fun f => projectionFormulaMap_naturality_left adj E f)

/-- The components of the inverse of `projectionFormulaNatIsoLeft`. -/
@[simp]
theorem projectionFormulaNatIsoLeft_inv_app (E : D) (K : C) :
    (projectionFormulaNatIsoLeft adj E).inv.app K = inv (projectionFormulaMap adj E K) :=
  rfl

/-- The map of Equation 48.8.0.1, written as a composite of whiskerings of the unit of `G ⊣ a`,
of the inverse of the projection-formula map, of `K` tensored with the counit of `G ⊣ a`, and of
the right unitor. -/
theorem comparisonUnit_eq :
    comparisonUnit adj adj' =
      (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ adj'.unit ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight ((Functor.associator _ _ _).hom ≫
            (projectionFormulaNatIsoLeft adj (a.obj (𝟙_ C))).inv ≫
              tensorRightMap (adj'.counit.app (𝟙_ C)) ≫ (rightUnitorNatIso C).hom) a ≫
          (Functor.leftUnitor _).hom := by
  ext K
  simp [comparison, Adjunction.homEquiv_unit]

/-- **The map of Equation 48.8.0.1 commutes with the shift.** For a monoidal functor `F` with
adjunctions `F ⊣ G ⊣ a` compatible with the shift, if the cotensorator of `F` commutes with the
shift in its first variable, the tensor products of `C` and `D` act on morphisms in the second
variable compatibly with the shift, and the right unitor of `C` commutes with the shift, then
`comparisonUnit adj adj' : F ⋙ (- ⊗ a 𝟙) ⟶ a` commutes with the shift. -/
theorem commShift_comparisonUnit
    [∀ M : C, NatTrans.CommShift (oplaxNatTransLeft F M) A]
    [∀ {M M' : C} (g : M ⟶ M'), NatTrans.CommShift (tensorRightMap g) A]
    [∀ {M M' : D} (g : M ⟶ M'), NatTrans.CommShift (tensorRightMap g) A]
    [NatTrans.CommShift (rightUnitorNatIso C).hom A] :
    NatTrans.CommShift (comparisonUnit adj adj') A := by
  have : NatTrans.CommShift (projectionFormulaNatIsoLeft adj (a.obj (𝟙_ C))).hom A :=
    commShift_projectionFormulaNatTransLeft adj A (a.obj (𝟙_ C))
  rw [comparisonUnit_eq]
  infer_instance

end CategoryTheory.MonoidalProjectionFormula

end
