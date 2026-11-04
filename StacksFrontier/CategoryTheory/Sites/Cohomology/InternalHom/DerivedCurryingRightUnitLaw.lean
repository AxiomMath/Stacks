module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingRightUnitLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality

/-!
# The right unit law of the derived currying isomorphism, at representatives

Let `(C, O)` be a ringed site. The derived currying isomorphism of **Stacks 08J9**

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_O L, M)`

is read here at `L = O[0]`. Its source then collapses by
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` applied inside `RSheafHom(K, -)`, and
what survives is the map induced by the right unit collapse `ρ_ A : Tot(A ⊗_O O[0]) ≅ A` of
Tag 0FNG. This is stated at an arbitrary complex `A` and a K-injective `I`, where both sides are
the classes of internal Hom complexes.

## Main results

* `AlgebraicGeometry.RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`:
  the right unit law at representatives, with the collapse spelled
  `AlgebraicGeometry.RingedSite.structureSheafComplexTensorRightIso`.
* `AlgebraicGeometry.RingedSite.homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso`:
  the same with the collapse spelled `ρ_ A`.

## Implementation notes

The statement is phrased with the representative isomorphisms
`AlgebraicGeometry.RingedSite.iteratedHomRepresentativeIso` and
`AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` rather than with the right unitor of
`D(O)`, so that it needs no instance pinning for the monoidal structure of `D(O)`.

Some goals in the proof carry the source of the iterated representative isomorphism at two
definitionally equal spellings, so they are not type-correct at the `implicit` transparency level
and no rewriting tactic acts on them. Those steps are closed by `exact` against lemmas over an
arbitrary category with every object and morphism a variable (`map_comp_paste`, `paste_left`,
`inv_comp_eq_inv_of_hom_eq`).

The K-flatness of `O[0]` is an argument of the statements rather than supplied from
`Stacks.SheafOfModules.isKFlat_single_unit`, so that the proof term appearing inside
`tensorHomRepresentativeIso` is a variable and the rewrite with `derivedCurryIso_comparison`
matches it syntactically.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ### Diagram lemmas over an abstract category -/

/-- If `A.hom = c.hom ≫ q.hom` for isomorphisms `A`, `c` and `q`, then
`A.inv ≫ c.hom = q.inv`. -/
private lemma inv_comp_eq_inv_of_hom_eq {D : Type*} [Category D] {a b m : D}
    (A : a ≅ b) (c : a ≅ m) (q : m ≅ b) (h : A.hom = c.hom ≫ q.hom) :
    A.inv ≫ c.hom = q.inv := by
  rw [Iso.inv_comp_eq, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- For a functor `G`, `G.map f ≫ (G.map g ≫ h) ≫ k = G.map (f ≫ g) ≫ h ≫ k`. -/
private lemma map_comp_paste {D E : Type*} [Category D] [Category E] (G : D ⥤ E)
    {a b c : D} {p q : E} (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ p) (k : p ⟶ q) :
    G.map f ≫ (G.map g ≫ h) ≫ k = G.map (f ≫ g) ≫ h ≫ k := by
  simp

/-- If `u ≫ v = s ≫ t`, then `u ≫ v ≫ w = s ≫ t ≫ w`. -/
private lemma paste_left {D : Type*} [Category D] {a b c e p : D}
    (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ e) (s : a ⟶ p) (t : p ⟶ c)
    (h : u ≫ v = s ≫ t) :
    u ≫ v ≫ w = s ≫ t ≫ w := by
  rw [← Category.assoc, h, Category.assoc]

variable (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-! ### The right unit coherence at representatives -/

/-- The right unit law of the derived currying isomorphism, at an arbitrary source complex `A`
and a K-injective target `I`, with the collapse spelled
`AlgebraicGeometry.RingedSite.structureSheafComplexTensorRightIso`.

Identifying `RSheafHom(QA, QI)` and `RSheafHom(QA ⊗^L_O O[0], QI)` with the classes of internal
Hom complexes, the collapse `RSheafHom(O[0], QI) ≅ QI` run backwards inside `RSheafHom(QA, -)`
and followed by the derived currying isomorphism is the map induced by the right unit collapse
`Tot(A ⊗_O O[0]) ≅ A`. -/
theorem homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso'
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) [I.IsKInjective] :
    (derivedSheafHomComparison X A I).inv ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
            (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).inv ≫
          (derivedCurryIso X (DerivedCategory.Q.obj A) (derivedStructureSheaf X)
              (DerivedCategory.Q.obj I)).hom ≫
            (tensorHomRepresentativeIso X A (structureSheafComplex X) I hO).hom =
      DerivedCategory.Q.map
        (homMap X (structureSheafComplexTensorRightIso X A).hom (𝟙 I)) := by
  have := isKInjective_sheafHomComplex_of_isKFlat X (structureSheafComplex X) I hO
  have hiterhom : (iteratedHomRepresentativeIso X A (structureSheafComplex X) I hO).hom =
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
          (derivedSheafHomComparison X (structureSheafComplex X) I).hom ≫
        (derivedSheafHomComparison X A
          (sheafHomComplex X (structureSheafComplex X) I).obj).hom := rfl
  have hd : (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).inv ≫
        (derivedSheafHomComparison X (structureSheafComplex X) I).hom =
      DerivedCategory.Q.map (structureSheafHomIso X I).inv :=
    inv_comp_eq_inv_of_hom_eq _ _ (DerivedCategory.Q.mapIso (structureSheafHomIso X I))
      (derivedStructureSheafHomIso_model X I)
  have hnat := derivedSheafHomComparison_naturality X (𝟙 A) (structureSheafHomIso X I).inv
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hnat
  refine (Iso.inv_comp_eq _).2 ?_
  rw [derivedCurryIso_comparison X A (structureSheafComplex X) I hO, hiterhom]
  refine Eq.trans (map_comp_paste _ _ _ _ _) ?_
  rw [hd]
  refine Eq.trans (paste_left _ _ _ _ _ hnat) ?_
  rw [← CategoryTheory.Functor.map_comp,
    homMap_structureSheafHomIso_inv_comp_sheafHomTensorCurryIso' X A I]

/-- The right unit law of the derived currying isomorphism, at an arbitrary source complex `A`
and a K-injective target `I`, with the collapse spelled `ρ_ A`: the collapse
`RSheafHom(O[0], QI) ≅ QI` run backwards inside `RSheafHom(QA, -)` and followed by the derived
currying isomorphism is the map induced by `ρ_ A`. -/
theorem homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) [I.IsKInjective] :
    (derivedSheafHomComparison X A I).inv ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
            (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).inv ≫
          (derivedCurryIso X (DerivedCategory.Q.obj A) (derivedStructureSheaf X)
              (DerivedCategory.Q.obj I)).hom ≫
            (tensorHomRepresentativeIso X A (structureSheafComplex X) I hO).hom =
      DerivedCategory.Q.map (homMap X (ρ_ A).hom (𝟙 I)) :=
  homMap_derivedStructureSheafHomIso_inv_comp_derivedCurryIso' X A I hO

end AlgebraicGeometry.RingedSite

end
