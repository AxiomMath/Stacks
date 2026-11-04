module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality

/-!
# The unit law of the derived tensor product of a ringed site, and its value on a complex

Let `(C, 𝒪)` be a ringed site and `T` a derived tensor product on it in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`. The structure sheaf in degree zero is a unit,
`E ⊗^𝐋_𝒪 𝒪[0] ≅ E` (`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`), and its value at the
image of a complex `K` is

`(T.unitIso (Q K)).hom = comparisonRight K 𝒪[0] ≫ Q(Tot(K ⊗_𝒪 𝒪[0]) ≅ K)`,

the right K-flat comparison of [Stacks, Tag 06YU] against the K-flat complex `𝒪[0]` followed by
`Q` of the unit law on complexes.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.unitComparisonNatIso`: the unit law on the images
  of complexes, `Q K ⊗^𝐋_𝒪 𝒪[0] ≅ Q K`, naturally in the complex `K`.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitNatIso`: the unit law as a natural
  isomorphism `- ⊗^𝐋_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`.

## Main results

* `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections_hom_naturality`: the unit law on
  complexes, `Tot(K ⊗_𝒪 𝒪[0]) ≅ K`, is natural in `K`.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitIso_hom_eq_unitNatIso_hom_app`: the pointwise
  unit law is the component of the natural one.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitIso_hom_q` and `unitIso_inv_comp_toTensor`:
  the value of the unit law at the image of a complex.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitIso_hom_naturality` and `unitIso_inv_naturality`:
  the unit law is natural in the tensor factor.

## Implementation notes

The natural unit law on `D(𝒪)` is `CategoryTheory.Localization.liftNatIso` at the localization
`DerivedCategory.Q`; since `𝒪[0]` is K-flat (`Stacks.SheafOfModules.isKFlat_single_unit`), no
K-flat resolution is chosen.

`Stacks.SheafOfModules.unitModule` and `Stacks.SheafOfModules.unitCochainComplex` are the
structure sheaf read as a module and placed in degree zero, with all three site universes free.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules

open AlgebraicGeometry.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The structure sheaf of a ringed site, read as the free rank-one sheaf of modules. -/
abbrev unitModule : Modules.{u, v, w} X :=
  _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)

/-- The structure sheaf of a ringed site placed in degree zero, as a complex. -/
abbrev unitCochainComplex : CochainComplex (Modules.{u, v, w} X) ℤ :=
  (HomologicalComplex.single (Modules.{u, v, w} X) (ComplexShape.up ℤ) 0).obj (unitModule X)

omit [∀ M : Modules.{u, v, w} X,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The termwise unit law `p ↦ K^p ⊗_𝒪 𝒪 ≅ K^p` is natural in the complex `K`. -/
theorem rowComplexUnitIsoFreeSections_hom_naturality
    {K K' : CochainComplex (Modules.{u, v, w} X) ℤ} (f : K ⟶ K') :
    CochainComplex.KFlatBifunctor.rowComplexMap
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) f (unitModule X) ≫
        (rowComplexUnitIsoFreeSections X.O K').hom =
      (rowComplexUnitIsoFreeSections X.O K).hom ≫ f := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  have h := sheafTensorUnitIsoFreeSections_naturality X.O (f.f p)
  rw [Functor.flip_obj_map] at h
  have hp : ∀ (L : CochainComplex (Modules.{u, v, w} X) ℤ) (q : ℤ),
      ((rowComplexUnitIsoFreeSections X.O L).hom).f q =
        (sheafTensorUnitIsoFreeSections X.O (L.X q)).hom ≫ 𝟙 _ := fun _ _ => rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hp, hp, Category.comp_id,
    Category.comp_id]
  exact h

/-- The unit law of the total tensor complex, `Tot(K ⊗_𝒪 𝒪[0]) ≅ K`, is natural in `K`. -/
theorem tensorComplexUnitIsoFreeSections_hom_naturality
    {K K' : CochainComplex (Modules.{u, v, w} X) ℤ} (f : K ⟶ K') :
    HomologicalComplex.mapBifunctorMap f (𝟙 (unitCochainComplex X))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫
        (tensorComplexUnitIsoFreeSections X.O K').hom =
      (tensorComplexUnitIsoFreeSections X.O K).hom ≫ f := by
  have key : HomologicalComplex.mapBifunctorMap f (𝟙 (unitCochainComplex X))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫
        ((CochainComplex.KFlatBifunctor.totalSingleIso
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) K' (unitModule X)).hom ≫
          (rowComplexUnitIsoFreeSections X.O K').hom) =
      ((CochainComplex.KFlatBifunctor.totalSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) K (unitModule X)).hom ≫
          (rowComplexUnitIsoFreeSections X.O K).hom) ≫ f := by
    rw [← Category.assoc, CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality,
      Category.assoc, rowComplexUnitIsoFreeSections_hom_naturality]
    exact (Category.assoc _ _ _).symm
  exact key

namespace DerivedTensorProduct

variable [HasDerivedCategory.{d} (Modules.{u, v, w} X)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-- The unit law on the images of complexes, `Q K ⊗^𝐋_𝒪 𝒪[0] ≅ Q K`, naturally in the
complex `K`: the right K-flat comparison against `𝒪[0]` followed by `Q` of the unit law on
complexes. -/
def unitComparisonNatIso :
    DerivedCategory.Q ⋙
        T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj (unitModule X)) ≅
      DerivedCategory.Q (C := Modules.{u, v, w} X) :=
  NatIso.ofComponents
    (fun K => T.comparisonRight K (unitCochainComplex X)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O) ≪≫
      DerivedCategory.Q.mapIso (tensorComplexUnitIsoFreeSections X.O K))
    (fun {K K'} f => by
      have hc := T.comparisonRight_naturality f (𝟙 (unitCochainComplex X))
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)
      rw [DerivedCategory.Q.map_id, (T.tensor.obj (DerivedCategory.Q.obj K')).map_id,
        Category.id_comp] at hc
      have hq : DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f (𝟙 (unitCochainComplex X))
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K').hom =
            DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K).hom ≫
              DerivedCategory.Q.map f :=
        (DerivedCategory.Q.map_comp _ _).symm.trans
          ((congrArg DerivedCategory.Q.map
            (tensorComplexUnitIsoFreeSections_hom_naturality X f)).trans
              (DerivedCategory.Q.map_comp _ _))
      have key : (T.tensor.map (DerivedCategory.Q.map f)).app
              (DerivedCategory.Q.obj (unitCochainComplex X)) ≫
            ((T.comparisonRight K' (unitCochainComplex X)
                (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
              DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K').hom) =
          ((T.comparisonRight K (unitCochainComplex X)
                (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
              DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K).hom) ≫
            DerivedCategory.Q.map f := by
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (fun z => z ≫ DerivedCategory.Q.map
          (tensorComplexUnitIsoFreeSections X.O K').hom) hc).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (fun z => (T.comparisonRight K (unitCochainComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫ z) hq).trans ?_
        exact (Category.assoc _ _ _).symm
      exact key)

/-- The unit law of the derived tensor product as a natural isomorphism
`- ⊗^𝐋_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`, the extension of `unitComparisonNatIso` along the localization
`DerivedCategory.Q`. -/
def unitNatIso :
    T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj (unitModule X)) ≅
      𝟭 (DerivedModules.{u, v, w, d} X) :=
  Localization.liftNatIso (DerivedCategory.Q (C := Modules.{u, v, w} X))
    (HomologicalComplex.quasiIso (Modules.{u, v, w} X) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙
      T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj (unitModule X)))
    (DerivedCategory.Q (C := Modules.{u, v, w} X))
    (T.tensor.flip.obj
      ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj (unitModule X)))
    (𝟭 _) (T.unitComparisonNatIso X)

/-- The value of the natural unit law at the image of a complex is the component of
`unitComparisonNatIso`. -/
theorem unitNatIso_hom_app_q (K : CochainComplex (Modules.{u, v, w} X) ℤ) :
    (T.unitNatIso X).hom.app (DerivedCategory.Q.obj K) =
      (T.comparisonRight K (unitCochainComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K).hom := by
  dsimp only [unitNatIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso, unitComparisonNatIso]

/-- The pointwise unit law `Stacks.SheafOfModules.DerivedTensorProduct.unitIso` is the component
of the natural one. -/
theorem unitIso_hom_eq_unitNatIso_hom_app (E : DerivedModules.{u, v, w, d} X) :
    (T.unitIso E).hom = (T.unitNatIso X).hom.app E := by
  have hnat := (T.unitNatIso X).hom.naturality
    ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objObjPreimageIso E).hom
  have hval :=
    T.unitNatIso_hom_app_q X ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objPreimage E)
  have hL : (T.unitIso E).hom =
      ((T.tensor.mapIso
            ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objObjPreimageIso E)).app
          (DerivedCategory.Q.obj (unitCochainComplex X))).inv ≫
        ((T.comparisonRight ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objPreimage E)
              (unitCochainComplex X) (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
          (DerivedCategory.Q.map
              (tensorComplexUnitIsoFreeSections X.O
                ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objPreimage E)).hom ≫
            ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objObjPreimageIso E).hom)) := rfl
  have hi : ((T.tensor.mapIso
          ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objObjPreimageIso E)).app
        (DerivedCategory.Q.obj (unitCochainComplex X))).hom =
      (T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj (unitModule X))).map
        ((DerivedCategory.Q (C := Modules.{u, v, w} X)).objObjPreimageIso E).hom := rfl
  rw [hL, Iso.inv_comp_eq, hi, hnat, hval, Functor.id_map]
  exact (Category.assoc _ _ _).symm

/-- The value of the unit law `E ⊗^𝐋_𝒪 𝒪[0] ≅ E` at the image of a complex: the right
K-flat comparison of [Stacks, Tag 06YU] against the K-flat complex `𝒪[0]`, followed by `Q` of
the unit law on complexes. -/
theorem unitIso_hom_q (K : CochainComplex (Modules.{u, v, w} X) ℤ) :
    (T.unitIso (DerivedCategory.Q.obj K)).hom =
      (T.comparisonRight K (unitCochainComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K).hom :=
  (T.unitIso_hom_eq_unitNatIso_hom_app X _).trans (T.unitNatIso_hom_app_q X K)

/-- The inverse of the unit law, followed by the canonical map `toTensor` to the ordinary total
tensor complex, is `Q` of the inverse of the unit law on complexes. -/
theorem unitIso_inv_comp_toTensor (K : CochainComplex (Modules.{u, v, w} X) ℤ) :
    (T.unitIso (DerivedCategory.Q.obj K)).inv ≫ T.toTensor K (unitCochainComplex X) =
      DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K).inv := by
  have hc : (T.comparisonRight K (unitCochainComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom =
      (T.unitIso (DerivedCategory.Q.obj K)).hom ≫
        DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections X.O K).inv := by
    rw [T.unitIso_hom_q X K, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [T.toTensor_eq_comparisonRight K (unitCochainComplex X)
      (Stacks.SheafOfModules.isKFlat_single_unit X.O), hc, Iso.inv_hom_id_assoc]

/-- The unit law is natural in the tensor factor: tensoring a morphism `a : E ⟶ E'` with the
identity of `𝒪[0]` and then cancelling the unit is cancelling the unit and then `a`. -/
theorem unitIso_hom_naturality {E E' : DerivedModules.{u, v, w, d} X} (a : E ⟶ E') :
    (T.tensor.map a).app
          ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj (unitModule X)) ≫
        (T.unitIso E').hom =
      (T.unitIso E).hom ≫ a := by
  rw [T.unitIso_hom_eq_unitNatIso_hom_app X E, T.unitIso_hom_eq_unitNatIso_hom_app X E']
  exact (T.unitNatIso X).hom.naturality a

/-- The inverse unit law is natural in the tensor factor. -/
theorem unitIso_inv_naturality {E E' : DerivedModules.{u, v, w, d} X} (a : E ⟶ E') :
    a ≫ (T.unitIso E').inv =
      (T.unitIso E).inv ≫ (T.tensor.map a).app
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj (unitModule X)) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← T.unitIso_hom_naturality X a, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end DerivedTensorProduct

end Stacks.SheafOfModules

end
