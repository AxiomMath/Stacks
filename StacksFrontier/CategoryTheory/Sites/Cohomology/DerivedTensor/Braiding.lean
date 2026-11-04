module

public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningTensorSections
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

/-!
# The commutativity constraint of a derived tensor product on a ringed site

Let `(C, O)` be a ringed site whose objects may live one universe above its morphisms and rings,
and let `T` be a derived tensor product on `D(Mod(O))`. For objects `K`, `L` of `D(Mod(O))` there
is an isomorphism `K ⊗^L_O L ≅ L ⊗^L_O K`: the braiding of the symmetric monoidal structure of
Stacks 0FPT on `D(Mod(O))`, conjugated by the comparison
`Stacks.SheafOfModules.DerivedTensorProduct.monoidalTensorIso` of its tensor product with the
bifunctor of `T`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.braiding`: the isomorphism
  `K ⊗^L_O L ≅ L ⊗^L_O K`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u w d

namespace CategoryTheory.MonoidalCategory

/-- The braiding of a re-seated monoidal structure is the given braiding conjugated by the
re-seating isomorphism. -/
private theorem reseatBraided_braiding_hom_aux {C : Type*} [Category C] [MonoidalCategory C]
    {T : C ⥤ C ⥤ C} {U : C} [BraidedCategory C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (X Y : C) :
    (@BraidedCategory.braiding C _ (reseat e ε) (reseatBraided e ε) X Y).hom =
      (reseatIso e X Y).inv ≫ (β_ X Y).hom ≫ (reseatIso e Y X).hom :=
  (𝟭 C).map_injective (by
    unfold reseatBraided BraidedCategory.ofFullyFaithful BraidedCategory.ofFaithful
    exact Functor.map_preimage (𝟭 C) _)

end CategoryTheory.MonoidalCategory

namespace Stacks.SheafOfModules.DerivedTensorProduct

open _root_.Stacks.AlgebraicGeometry AlgebraicGeometry.RingedSite

variable {Y : AlgebraicGeometry.RingedSite.{w, u, u}}
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{w, u, u} Y)]
  (T : DerivedTensorProduct.{w, u, u, d} Y)

/-- **Commutativity of the derived tensor product**: `K ⊗^L L ≅ L ⊗^L K`, the braiding of the
symmetric monoidal structure of Stacks 0FPT on `D(Mod(O))` read through the comparison of its
tensor product with the bifunctor of `T`. -/
def braiding (K L : AlgebraicGeometry.RingedSite.DerivedModules.{w, u, u, d} Y) :
    (T.tensor.obj K).obj L ≅ (T.tensor.obj L).obj K :=
  ((T.monoidalTensorIso.app K).app L).symm ≪≫
    @BraidedCategory.braiding _ _ (DerivedMonoidalGeneral.derivedMonoidal Y.O)
      (DerivedMonoidalGeneral.derivedSymmetric Y.O).toBraidedCategory K L ≪≫
    (T.monoidalTensorIso.app L).app K

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory

/-- **The commutativity constraint is natural in both objects.** -/
theorem braiding_hom_naturality
    {A A' B B' : AlgebraicGeometry.RingedSite.DerivedModules.{w, u, u, d} Y} (a : A ⟶ A')
    (b : B ⟶ B') :
    (T.tensor.map a).app B ≫ (T.tensor.obj A').map b ≫ (T.braiding A' B').hom =
      (T.braiding A B).hom ≫ (T.tensor.map b).app A ≫ (T.tensor.obj B').map a := by
  let := T.monoidal
  let : BraidedCategory (AlgebraicGeometry.RingedSite.DerivedModules.{w, u, u, d} Y) :=
    @reseatBraided _ _ (DerivedMonoidalGeneral.derivedMonoidal Y.O) _ _
      (DerivedMonoidalGeneral.derivedSymmetric Y.O).toBraidedCategory T.monoidalTensorIso
      (DerivedMonoidalGeneral.canonicalUnitIso Y.O)
  have e (A B : AlgebraicGeometry.RingedSite.DerivedModules.{w, u, u, d} Y) :
      (T.braiding A B).hom = (β_ A B).hom :=
    (@reseatBraided_braiding_hom_aux _ _ (DerivedMonoidalGeneral.derivedMonoidal Y.O) _ _
      (DerivedMonoidalGeneral.derivedSymmetric Y.O).toBraidedCategory T.monoidalTensorIso
      (DerivedMonoidalGeneral.canonicalUnitIso Y.O) A B).symm
  rw [e, e]
  show a ▷ B ≫ A' ◁ b ≫ (β_ A' B').hom = (β_ A B).hom ≫ b ▷ A ≫ B' ◁ a
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def, BraidedCategory.braiding_naturality,
    MonoidalCategory.tensorHom_def]

/-- **The commutativity constraint is natural in its second object.** -/
theorem braiding_hom_naturality_right
    (A : AlgebraicGeometry.RingedSite.DerivedModules.{w, u, u, d} Y)
    {B B' : AlgebraicGeometry.RingedSite.DerivedModules.{w, u, u, d} Y} (b : B ⟶ B') :
    (T.tensor.obj A).map b ≫ (T.braiding A B').hom =
      (T.braiding A B).hom ≫ (T.tensor.map b).app A := by
  simpa using T.braiding_hom_naturality (𝟙 A) b

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{w, u, u} Y)] in
private lemma conj_comp_eq_of_comp_eq {𝒞 : Type*} [Category 𝒞] {A B A' B' P Q : 𝒞} (e₁ : A ≅ P)
    (e₂ : B ≅ Q) {β : A ⟶ B} {k₁ : A ⟶ A'} {k₂ : B ⟶ B'} {q : A' ⟶ B'}
    (h : β ≫ k₂ = k₁ ≫ q) : (e₁.inv ≫ β ≫ e₂.hom) ≫ e₂.inv ≫ k₂ = (e₁.inv ≫ k₁) ≫ q := by
  simp [h]

/-- **The commutativity constraint of a derived tensor product is the Koszul symmetry of the
total tensor product of complexes**: on K-flat complexes `K`, `L` the K-flat comparisons carry
`Stacks.SheafOfModules.DerivedTensorProduct.braiding` to `Q(β_{K,L})`. -/
theorem comparison_braiding
    (K L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{w, u, u} Y) ℤ)
    (hK : IsKFlat Y.O K) (hL : IsKFlat Y.O L) :
    (T.braiding (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (T.comparison L K hL hK).hom =
      (T.comparison K L hK hL).hom ≫ DerivedCategory.Q.map (β_ K L).hom := by
  have hb := DerivedMonoidalGeneral.kFlatComparison_braiding Y.O hK hL
  rw [T.comparison_eq K L hK hL, T.comparison_eq L K hL hK]
  simp only [braiding, Iso.trans_hom, Iso.symm_hom, reseatIso]
  exact conj_comp_eq_of_comp_eq _ _ hb

end Stacks.SheafOfModules.DerivedTensorProduct

end
