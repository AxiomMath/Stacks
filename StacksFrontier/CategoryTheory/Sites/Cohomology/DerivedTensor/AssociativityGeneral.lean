module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorConstraintsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparisonGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TensorProduct

/-!
# Associativity of the derived tensor product, for a site with objects in their own universe

Let `(C, O)` be a ringed site whose objects live in a universe `w` and whose morphisms and
sections live in the universe `u` of the sheaf of rings, and let `T` be a derived tensor product
on `D(Mod(O))`. The monoidal structure of Stacks 0FPT re-seated onto `T` gives an associator
`(K ⊗^L L) ⊗^L M ≅ K ⊗^L (L ⊗^L M)` and a left unitor, natural in each variable, and on K-flat
complexes the K-flat comparisons carry the associator to that of the total tensor product.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.monoidal`: the monoidal structure on `D(Mod(O))`
  whose tensor product is `T`, and `Stacks.SheafOfModules.DerivedTensorProduct.monoidalTensorIso`.
* `Stacks.SheafOfModules.DerivedTensorProduct.associatorGeneral`,
  `Stacks.SheafOfModules.DerivedTensorProduct.leftUnitor`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.associatorGeneral_naturality_left`, `_middle`,
  `_right` and `associatorGeneral_naturality`.
* `Stacks.SheafOfModules.DerivedTensorProduct.comparison_associator` and
  `comparison_tensorComplexAssociator`.
* `Stacks.SheafOfModules.DerivedTensorProduct.leftUnitor_tensor`: the triangle identity.
* `Stacks.SheafOfModules.DerivedTensorProduct.tensor_map_obj_map_app_eq_zero_general`.

## Implementation notes

`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity` states the associator
for a `RingedSite.{u, u, u}`, through the small-site form of Stacks 0FPT. Here the site is a
`RingedSite.{w, u, u}`; the monoidal structure is that of
`Stacks.SheafOfModules.DerivedMonoidalGeneral.derivedMonoidal`, re-seated onto `T` by
`CategoryTheory.MonoidalCategory.reseat`, so that its associator is computed on K-flat pairs.
This applies to the small étale ringed site of an algebraic space.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry AlgebraicGeometry.RingedSite

variable {Y : AlgebraicGeometry.RingedSite.{w, u, u}}
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules.{w, u, u} Y)]
  (T : DerivedTensorProduct.{w, u, u, d} Y)

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory DerivedMonoidalGeneral.kFlatQ_isLocalization
  DerivedMonoidalGeneral.kFlatQLeft_isLocalization

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided DerivedMonoidalGeneral.derivedMonoidal
  DerivedMonoidalGeneral.derivedSymmetric

attribute [local instance] DerivedMonoidalGeneral.homQMonoidal DerivedMonoidalGeneral.homQBraided
  DerivedMonoidalGeneral.kFlatQMonoidal DerivedMonoidalGeneral.kFlatQBraided
  DerivedMonoidalGeneral.kFlatQuotientMonoidal DerivedMonoidalGeneral.kFlatQuotientLaxBraided
  DerivedMonoidalGeneral.kFlatComplexQMonoidal DerivedMonoidalGeneral.kFlatComplexQLaxBraided

/-- The tensor product of the monoidal derived category of Tag 0FPT descends the total tensor
product of K-flat complexes, the lifting isomorphism being the K-flat comparison
`Stacks.SheafOfModules.DerivedMonoidalGeneral.kFlatComparison`. -/
@[instance_reducible]
def monoidalTensorLifting :
    Localization.Lifting₂ (DerivedMonoidalGeneral.kFlatComplexQ Y.O)
      (DerivedMonoidalGeneral.kFlatComplexQ Y.O) (DerivedMonoidalGeneral.kFlatComplexQuasiIso Y.O)
      (DerivedMonoidalGeneral.kFlatComplexQuasiIso Y.O)
      (DerivedMonoidalGeneral.kFlatTensorSource Y.O)
      (curriedTensor (DerivedModules.{w, u, u, d} Y)) where
  iso := NatIso.ofComponents
    (fun A ↦ NatIso.ofComponents (fun B ↦ DerivedMonoidalGeneral.kFlatComparison Y.O A.2 B.2)
      (fun {_ _} g ↦
        Functor.LaxMonoidal.μ_natural_right (DerivedMonoidalGeneral.kFlatComplexQ Y.O) _ g))
    (fun {_ _} f ↦ by
      ext B
      exact Functor.LaxMonoidal.μ_natural_left (DerivedMonoidalGeneral.kFlatComplexQ Y.O) f B)

attribute [local instance] monoidalTensorLifting
  DerivedMonoidalGeneral.interfaceTensorLifting

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- **The tensor product of the monoidal derived category of Tag 0FPT is the bifunctor of a
derived tensor product**, as an isomorphism of bifunctors: both descend the total tensor
product of K-flat complexes along the same localization. -/
def monoidalTensorIso :
    @curriedTensor (DerivedModules.{w, u, u, d} Y) _ (DerivedMonoidalGeneral.derivedMonoidal Y.O) ≅
      T.tensor :=
  letI := monoidalTensorLifting (Y := Y)
  letI := DerivedMonoidalGeneral.interfaceTensorLifting Y T
  Localization.lift₂NatIso (DerivedMonoidalGeneral.kFlatComplexQ Y.O)
    (DerivedMonoidalGeneral.kFlatComplexQ Y.O) (DerivedMonoidalGeneral.kFlatComplexQuasiIso Y.O)
    (DerivedMonoidalGeneral.kFlatComplexQuasiIso Y.O) (DerivedMonoidalGeneral.kFlatTensorSource Y.O)
    (DerivedMonoidalGeneral.kFlatTensorSource Y.O) (curriedTensor (DerivedModules.{w, u, u, d} Y))
    T.tensor (Iso.refl _)

/-- **The comparison of the two bifunctors on a pair of K-flat complexes** is the K-flat
comparison of Tag 0FPT followed by the inverse of the K-flat comparison of the derived tensor
product. -/
theorem monoidalTensorIso_hom_app_app (K L : CochainComplex (Modules.{w, u, u} Y) ℤ)
    (hK : IsKFlat Y.O K) (hL : IsKFlat Y.O L) :
    (T.monoidalTensorIso.hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
      (DerivedMonoidalGeneral.kFlatComparison Y.O hK hL).hom ≫ (T.comparison K L hK hL).inv := by
  let := monoidalTensorLifting (Y := Y)
  let := DerivedMonoidalGeneral.interfaceTensorLifting Y T
  refine (Localization.lift₂NatTrans_app_app (DerivedMonoidalGeneral.kFlatComplexQ Y.O)
    (DerivedMonoidalGeneral.kFlatComplexQ Y.O) (DerivedMonoidalGeneral.kFlatComplexQuasiIso Y.O)
    (DerivedMonoidalGeneral.kFlatComplexQuasiIso Y.O) (DerivedMonoidalGeneral.kFlatTensorSource Y.O)
    (DerivedMonoidalGeneral.kFlatTensorSource Y.O) (curriedTensor (DerivedModules.{w, u, u, d} Y))
    T.tensor (Iso.refl _).hom
    (⟨K, hK⟩ : (DerivedMonoidalGeneral.KFlatComplexes Y.O).FullSubcategory)
    (⟨L, hL⟩ : (DerivedMonoidalGeneral.KFlatComplexes Y.O).FullSubcategory)).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- **`D(Mod(O))` is monoidal with a prescribed derived tensor product as its tensor product**,
on the nose, and the structure sheaf in degree zero as its unit. The coherence is that of
Tag 0FPT, transported by `CategoryTheory.MonoidalCategory.reseat`. -/
@[instance_reducible]
def monoidal : MonoidalCategory (DerivedModules.{w, u, u, d} Y) :=
  @reseat (DerivedModules.{w, u, u, d} Y) _ (DerivedMonoidalGeneral.derivedMonoidal Y.O) _ _
    T.monoidalTensorIso (DerivedMonoidalGeneral.canonicalUnitIso Y.O)

/-- The tensor product of `Stacks.SheafOfModules.DerivedTensorProduct.monoidal` is the bifunctor
of the derived tensor product, as an equality of bifunctors. -/
theorem curriedTensor_monoidal :
    @curriedTensor (DerivedModules.{w, u, u, d} Y) _ T.monoidal = T.tensor :=
  rfl

/-- **Associativity of the derived tensor product**: `(K ⊗^L L) ⊗^L M ≅ K ⊗^L (L ⊗^L M)`. -/
def associatorGeneral (K L M : DerivedModules.{w, u, u, d} Y) :
    (T.tensor.obj ((T.tensor.obj K).obj L)).obj M ≅
      (T.tensor.obj K).obj ((T.tensor.obj L).obj M) :=
  letI := T.monoidal
  α_ K L M

/-- **The left unit law of the derived tensor product**: `O ⊗^L K ≅ K`, for the structure sheaf
`O` in degree zero. -/
def leftUnitor :
    T.tensor.obj ((DerivedCategory.singleFunctor (Modules.{w, u, u} Y) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{w, u, u} Y.O))) ≅
      𝟭 _ :=
  letI := T.monoidal
  NatIso.ofComponents (fun K ↦ λ_ K) (fun f ↦ leftUnitor_naturality f)

/-- **The associator of a derived tensor product is the associator of Tag 0FPT conjugated by the
comparison of the two bifunctors**, `CategoryTheory.MonoidalCategory.reseat_associator` at the
re-seating defining `Stacks.SheafOfModules.DerivedTensorProduct.monoidal`. -/
theorem associatorGeneral_hom (K L M : DerivedModules.{w, u, u, d} Y) :
    (T.associatorGeneral K L M).hom =
      ((reseatIso T.monoidalTensorIso ((T.tensor.obj K).obj L) M).inv ≫
          ((reseatIso T.monoidalTensorIso K L).inv ⊗ₘ 𝟙 M)) ≫
        (α_ K L M).hom ≫ (𝟙 K ⊗ₘ (reseatIso T.monoidalTensorIso L M).hom) ≫
          (reseatIso T.monoidalTensorIso K ((T.tensor.obj L).obj M)).hom :=
  reseat_associator T.monoidalTensorIso (DerivedMonoidalGeneral.canonicalUnitIso Y.O) K L M

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules.{w, u, u} Y)] in
private lemma iso_eq_symm_trans_of_eq {D : Type*} [Category D] {P R Z : D} {r : P ≅ R}
    {k : P ≅ Z} {c : R ≅ Z} (h : r = k ≪≫ c.symm) : c = r.symm ≪≫ k := by
  subst h
  ext
  simp

/-- **The K-flat comparison of a derived tensor product is the K-flat comparison of Tag 0FPT**,
read through the comparison `monoidalTensorIso` of the two bifunctors. -/
theorem comparison_eq (A B : CochainComplex (Modules.{w, u, u} Y) ℤ) (hA : IsKFlat Y.O A)
    (hB : IsKFlat Y.O B) :
    T.comparison A B hA hB =
      (reseatIso T.monoidalTensorIso (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B)).symm ≪≫ DerivedMonoidalGeneral.kFlatComparison Y.O hA hB :=
  iso_eq_symm_trans_of_eq (Iso.ext (T.monoidalTensorIso_hom_app_app A B hA hB))

/-- The associativity of the K-flat comparisons of Tag 0FPT, read through the comparison
`monoidalTensorIso` of the two bifunctors. -/
private theorem reseat_kFlatComparison_associator {K L M : CochainComplex (Modules.{w, u, u} Y) ℤ}
    (hK : DerivedMonoidalGeneral.KFlat Y.O K) (hL : DerivedMonoidalGeneral.KFlat Y.O L)
    (hM : DerivedMonoidalGeneral.KFlat Y.O M) :
    (T.tensor.map ((reseatIso T.monoidalTensorIso (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L)).symm ≪≫
          DerivedMonoidalGeneral.kFlatComparison Y.O hK hL).hom).app
          (DerivedCategory.Q.obj M) ≫
        ((reseatIso T.monoidalTensorIso (DerivedCategory.Q.obj (K ⊗ L))
          (DerivedCategory.Q.obj M)).symm ≪≫ DerivedMonoidalGeneral.kFlatComparison Y.O
            (CochainComplex.KFlatMonoidal.kFlat_tensor (Modules.{w, u, u} Y) hK hL) hM).hom ≫
          DerivedCategory.Q.map (α_ K L M).hom =
      (T.associatorGeneral (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
            (DerivedCategory.Q.obj M)).hom ≫
        (T.tensor.obj (DerivedCategory.Q.obj K)).map ((reseatIso T.monoidalTensorIso
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)).symm ≪≫
            DerivedMonoidalGeneral.kFlatComparison Y.O hL hM).hom ≫
          ((reseatIso T.monoidalTensorIso (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj (L ⊗ M))).symm ≪≫ DerivedMonoidalGeneral.kFlatComparison Y.O hK
              (CochainComplex.KFlatMonoidal.kFlat_tensor (Modules.{w, u, u} Y) hL hM)).hom :=
  reseat_associativity T.monoidalTensorIso (DerivedMonoidalGeneral.kFlatComparison Y.O hK hL)
    (DerivedMonoidalGeneral.kFlatComparison Y.O
      (CochainComplex.KFlatMonoidal.kFlat_tensor (Modules.{w, u, u} Y) hK hL) hM)
    (DerivedMonoidalGeneral.kFlatComparison Y.O hL hM)
    (DerivedMonoidalGeneral.kFlatComparison Y.O hK
      (CochainComplex.KFlatMonoidal.kFlat_tensor (Modules.{w, u, u} Y) hL hM))
    (T.associatorGeneral_hom _ _ _) (DerivedMonoidalGeneral.kFlatComparison_associator Y.O hK hL hM)

/-- **The associativity constraint of a derived tensor product is the associator of the total
tensor product of complexes**: on K-flat complexes `K`, `L`, `M` the K-flat comparisons carry
`Stacks.SheafOfModules.DerivedTensorProduct.associatorGeneral` to `Q(α_{K,L,M})`. -/
theorem comparison_associator {K L M : CochainComplex (Modules.{w, u, u} Y) ℤ}
    (hK : IsKFlat Y.O K) (hL : IsKFlat Y.O L) (hM : IsKFlat Y.O M) :
    (T.tensor.map (T.comparison K L hK hL).hom).app (DerivedCategory.Q.obj M) ≫
        (T.comparison (K ⊗ L) M (CochainComplex.KFlatMonoidal.kFlat_tensor
          (Modules.{w, u, u} Y) hK hL) hM).hom ≫
          DerivedCategory.Q.map (α_ K L M).hom =
      (T.associatorGeneral (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
            (DerivedCategory.Q.obj M)).hom ≫
        (T.tensor.obj (DerivedCategory.Q.obj K)).map (T.comparison L M hL hM).hom ≫
          (T.comparison K (L ⊗ M) hK (CochainComplex.KFlatMonoidal.kFlat_tensor
            (Modules.{w, u, u} Y) hL hM)).hom := by
  rw [T.comparison_eq K L hK hL, T.comparison_eq (K ⊗ L) M
    (CochainComplex.KFlatMonoidal.kFlat_tensor (Modules.{w, u, u} Y) hK hL) hM,
    T.comparison_eq L M hL hM, T.comparison_eq K (L ⊗ M) hK
    (CochainComplex.KFlatMonoidal.kFlat_tensor (Modules.{w, u, u} Y) hL hM)]
  exact T.reseat_kFlatComparison_associator hK hL hM

omit [HasDerivedCategory.{d} (Modules.{w, u, u} Y)] in
/-- **The associator of the total tensor product of complexes**,
`Tot(Tot(K ⊗ L) ⊗ M) ≅ Tot(K ⊗ Tot(L ⊗ M))`, in the spelling of
`Stacks.SheafOfModules.Tensor.tensorComplex`: the associator of the monoidal structure of
complexes over `⊗_O`. -/
def tensorComplexAssociator (K L M : CochainComplex (Modules.{w, u, u} Y) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K |>.obj L) |>.obj M) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K |>.obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj L |>.obj M)) :=
  α_ K L M

/-- `comparison_associator` in the spelling of `Stacks.SheafOfModules.Tensor.tensorComplex`. -/
theorem comparison_tensorComplexAssociator {K L M : CochainComplex (Modules.{w, u, u} Y) ℤ}
    (hK : IsKFlat Y.O K) (hL : IsKFlat Y.O L) (hM : IsKFlat Y.O M) :
    (T.tensor.map (T.comparison K L hK hL).hom).app (DerivedCategory.Q.obj M) ≫
        (T.comparison ((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K |>.obj L) M
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
          hM).hom ≫ DerivedCategory.Q.map (tensorComplexAssociator K L M).hom =
      (T.associatorGeneral (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
            (DerivedCategory.Q.obj M)).hom ≫
        (T.tensor.obj (DerivedCategory.Q.obj K)).map (T.comparison L M hL hM).hom ≫
          (T.comparison K ((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj L |>.obj M) hK
            (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hL hM)).hom :=
  T.comparison_associator hK hL hM

/-- **The associator is natural in the first variable.** -/
theorem associatorGeneral_naturality_left {K K' : DerivedModules.{w, u, u, d} Y} (f : K ⟶ K')
    (L M : DerivedModules.{w, u, u, d} Y) :
    (T.tensor.map ((T.tensor.map f).app L)).app M ≫ (T.associatorGeneral K' L M).hom =
      (T.associatorGeneral K L M).hom ≫ (T.tensor.map f).app ((T.tensor.obj L).obj M) :=
  @MonoidalCategory.associator_naturality_left (DerivedModules.{w, u, u, d} Y) _ T.monoidal _ _ f
    L M

/-- **The associator is natural in the second variable.** -/
theorem associatorGeneral_naturality_middle (K : DerivedModules.{w, u, u, d} Y)
    {L L' : DerivedModules.{w, u, u, d} Y} (g : L ⟶ L') (M : DerivedModules.{w, u, u, d} Y) :
    (T.tensor.map ((T.tensor.obj K).map g)).app M ≫ (T.associatorGeneral K L' M).hom =
      (T.associatorGeneral K L M).hom ≫ (T.tensor.obj K).map ((T.tensor.map g).app M) :=
  @MonoidalCategory.associator_naturality_middle (DerivedModules.{w, u, u, d} Y) _ T.monoidal K _ _
    g M

/-- **The associator is natural in the third variable.** -/
theorem associatorGeneral_naturality_right (K L : DerivedModules.{w, u, u, d} Y)
    {M M' : DerivedModules.{w, u, u, d} Y} (h : M ⟶ M') :
    (T.tensor.obj ((T.tensor.obj K).obj L)).map h ≫ (T.associatorGeneral K L M').hom =
      (T.associatorGeneral K L M).hom ≫ (T.tensor.obj K).map ((T.tensor.obj L).map h) :=
  @MonoidalCategory.associator_naturality_right (DerivedModules.{w, u, u, d} Y) _ T.monoidal K L _ _
    h

/-- **The associator is natural in the three variables at once.** -/
theorem associatorGeneral_naturality {K K' L L' M M' : DerivedModules.{w, u, u, d} Y} (a : K ⟶ K')
    (b : L ⟶ L') (c : M ⟶ M') :
    ((T.tensor.map ((T.tensor.map a).app L ≫ (T.tensor.obj K').map b)).app M ≫
        (T.tensor.obj ((T.tensor.obj K').obj L')).map c) ≫ (T.associatorGeneral K' L' M').hom =
      (T.associatorGeneral K L M).hom ≫ (T.tensor.map a).app ((T.tensor.obj L).obj M) ≫
        (T.tensor.obj K').map ((T.tensor.map b).app M ≫ (T.tensor.obj L').map c) :=
  @MonoidalCategory.associator_naturality (DerivedModules.{w, u, u, d} Y) _ T.monoidal _ _ _ _ _ _
    a b c

/-- **The triangle identity for the left unitor**: `λ_K ⊗^L L` is the associator followed by
`λ_{K ⊗^L L}`. -/
theorem leftUnitor_tensor (K L : DerivedModules.{w, u, u, d} Y) :
    (T.tensor.map (T.leftUnitor.hom.app K)).app L =
      (T.associatorGeneral _ K L).hom ≫ T.leftUnitor.hom.app ((T.tensor.obj K).obj L) :=
  @leftUnitor_whiskerRight (DerivedModules.{w, u, u, d} Y) _ T.monoidal K L

/-- **A map that dies on tensoring with `G` still dies after being tensored with an object on
the left**: if `ι ⊗^L 1_G = 0` then `(1_K ⊗^L ι) ⊗^L 1_G = 0`. This is naturality of the
associator in the second variable, together with additivity of tensoring with `K`. -/
theorem tensor_map_obj_map_app_eq_zero_general {I O : DerivedModules.{w, u, u, d} Y} (ι : I ⟶ O)
    (K G : DerivedModules.{w, u, u, d} Y) (h : (T.tensor.map ι).app G = 0) :
    (T.tensor.map ((T.tensor.obj K).map ι)).app G = 0 := by
  refine zero_of_comp_mono (T.associatorGeneral K O G).hom ?_
  rw [T.associatorGeneral_naturality_middle K ι G, h, T.tensor_obj_map_zero, comp_zero]

end Stacks.SheafOfModules.DerivedTensorProduct

end
