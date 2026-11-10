module

public import Mathlib.CategoryTheory.Localization.Predicate
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface

/-!
# The unit law of the derived tensor product of the interface is natural

Let `(C, 𝒪)` be a ringed site whose objects, morphisms and sections live in independent universes,
and let `T` be a derived tensor product on it in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`.  The unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`, `E ⊗^L_𝒪 𝒪[0] ≅ E`, is given there one
object at a time.  This file shows that it is the component of a natural isomorphism of functors

`- ⊗^L_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`.

On the image `Q K` of a complex the isomorphism is the right K-flat comparison at the K-flat
complex `𝒪[0]` followed by the unit law of the total tensor complex,
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`, which is natural in `K`; the natural
isomorphism on `D(𝒪)` is its lift along the localization `Q`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.unitComplexNatIso`: `- ⊗^L_𝒪 𝒪[0] ≅ 𝟭`.

## Main results

* `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections_naturality`: the unit law of the total
  tensor complex is natural in the complex, with the universe of the sections free.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitNatIso_hom_app_Q`: its value at `Q K`.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitNatIso_app`: its component at `E` is
  `Stacks.SheafOfModules.DerivedTensorProduct.unitIso E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace Stacks.SheafOfModules

open CochainComplex.KFlatBifunctor

section Complexes

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor S).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor S).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor S)
      (ComplexShape.up ℤ)]

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` is natural in `K`**, with the universe of the sections
free: both of its factors are, the single-row total comparison by
`CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality` and the termwise unit law as the
component of a natural isomorphism of functors. -/
lemma tensorComplexUnitIsoFreeSections_naturality
    {K K' : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ} (φ : K ⟶ K') :
    HomologicalComplex.mapBifunctorMap φ
        (𝟙 ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))))
        (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ) ≫
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections S K').hom =
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections S K).hom ≫ φ := by
  change _ ≫ (totalSingleIso _ K' _).hom ≫ (rowComplexUnitIsoFreeSections S K').hom =
    ((totalSingleIso _ K _).hom ≫ (rowComplexUnitIsoFreeSections S K).hom) ≫ φ
  rw [← Category.assoc, totalSingleIso_hom_naturality, Category.assoc, Category.assoc]
  congr 1
  exact (NatIso.mapHomologicalComplex (sheafTensorUnitNatIsoFreeSections S)
      (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.naturality φ

end Complexes

namespace DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct.{u, v, w, d} X)

/-- The structure sheaf placed in degree zero, as a complex. -/
abbrev unitComplex (X : AlgebraicGeometry.RingedSite.{u, v, w}) :
    CochainComplex (Modules.{u, v, w} X) ℤ :=
  (HomologicalComplex.single (Modules.{u, v, w} X) (ComplexShape.up ℤ) 0).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The unit law on the image of a complex, naturally in that complex**:
`Q K ⊗^L_𝒪 𝒪[0] ≅ Q K`, the right K-flat comparison at the K-flat complex `𝒪[0]` followed by
the unit law of the total tensor complex. -/
def unitComplexComparisonNatIso :
    DerivedCategory.Q ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj (unitComplex X)) ≅
      DerivedCategory.Q (C := Modules.{u, v, w} X) :=
  NatIso.ofComponents
    (fun K => T.comparisonRight K (unitComplex X)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O) ≪≫
      DerivedCategory.Q.mapIso (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O K))
    (fun {K K'} h => by
      have hc := T.comparisonRight_naturality h (𝟙 (unitComplex X))
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)
      rw [DerivedCategory.Q.map_id, (T.tensor.obj (DerivedCategory.Q.obj K')).map_id,
        Category.id_comp] at hc
      dsimp only [Functor.comp_map, Functor.flip_obj_map, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, hc]
      refine (Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ t) ?_).trans
        (Category.assoc _ _ _).symm)
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (tensorComplexUnitIsoFreeSections_naturality X.O h)).trans
          (DerivedCategory.Q.map_comp _ _)))

/-- **The unit law of the derived tensor product, as a natural isomorphism**:
`- ⊗^L_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`, the lift along the localization `Q` of `unitComplexComparisonNatIso`. -/
def unitComplexNatIso :
    T.tensor.flip.obj ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      𝟭 (DerivedModules.{u, v, w, d} X) :=
  Localization.liftNatIso (DerivedCategory.Q (C := Modules.{u, v, w} X))
    (HomologicalComplex.quasiIso (Modules.{u, v, w} X) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj (unitComplex X)))
    (DerivedCategory.Q (C := Modules.{u, v, w} X))
    (T.tensor.flip.obj (DerivedCategory.Q.obj (unitComplex X))) (𝟭 _)
    T.unitComplexComparisonNatIso

/-- **The unit law at the image of a complex** is the right K-flat comparison at `𝒪[0]`
followed by the unit law of the total tensor complex. -/
theorem unitNatIso_hom_app_Q (K : CochainComplex (Modules.{u, v, w} X) ℤ) :
    T.unitComplexNatIso.hom.app (DerivedCategory.Q.obj K) =
      (T.comparisonRight K (unitComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map
          (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O K).hom := by
  dsimp only [unitComplexNatIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso, unitComplexComparisonNatIso]

/-- **The natural unit law has the objectwise one as its components**:
`unitComplexNatIso T` at `E` is `Stacks.SheafOfModules.DerivedTensorProduct.unitIso T E`. -/
theorem unitNatIso_app (E : DerivedModules.{u, v, w, d} X) :
    T.unitComplexNatIso.app E = T.unitIso E := by
  ext
  have h := T.unitComplexNatIso.hom.naturality (DerivedCategory.Q.objObjPreimageIso E).hom
  dsimp only [Functor.flip_obj_map, Functor.id_map, Functor.id_obj] at h
  rw [← cancel_epi ((T.tensor.map (DerivedCategory.Q.objObjPreimageIso E).hom).app _),
    Iso.app_hom, h, unitNatIso_hom_app_Q]
  simp [unitIso]

end DerivedTensorProduct

end Stacks.SheafOfModules

end
