module

public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedUnitorCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# The constraints of the derived tensor product on a ringed site are natural

Let `(C, O)` be a ringed site and `T` a derived tensor product on it in the sense of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`.  Its unit constraints and its
commutativity constraint are built by replacing an object of `D(O)` by a chosen K-flat model,
which is not a functor, so each is supplied one object (resp. one pair of objects) at a time.
This file proves them natural.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitTrans`: the unit constraint on
  the right as a natural transformation `- ⊗^L_O O ⟶ id`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingTrans`: the commutativity
  constraint as a transformation `- ⊗^L_O - ⟶ (- ⊗^L_O -)ᶠˡⁱᵖ`.

## Main results

* `Stacks.SheafOfModules.tensorComplexFlipIso_hom_naturality`: the Koszul symmetry of the
  total tensor product of complexes is natural.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality` and
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso_hom_naturality`: the unit
  constraint on the right and the commutativity constraint of a derived tensor product are
  natural.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso_hom_naturality`: the unit
  constraint on the left of a derived tensor product is natural.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-! ### The constraints of the total tensor product of complexes are natural -/

namespace Stacks.SheafOfModules

section Complexes

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **The Koszul symmetry `Tot(K ⊗_O L) ≅ Tot(L ⊗_O K)` of the total tensor product of
complexes is natural in both complexes.** -/
lemma tensorComplexFlipIso_hom_naturality
    {K₁ L₁ K₂ L₂ : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) :
    HomologicalComplex.mapBifunctorMapReg φ₁ φ₂ (Tensor.sheafTensor R) (ComplexShape.up ℤ) ≫
        (Tensor.tensorComplexFlipIso R L₁ L₂).hom =
      (Tensor.tensorComplexFlipIso R K₁ K₂).hom ≫
        HomologicalComplex.mapBifunctorMapReg φ₂ φ₁ (Tensor.sheafTensor R)
          (ComplexShape.up ℤ) := by
  have hnat : HomologicalComplex.mapBifunctorMap φ₁ φ₂ (Tensor.sheafTensor R)
          (ComplexShape.up ℤ) ≫
        (HomologicalComplex.mapBifunctorNatIso L₁ L₂ (ComplexShape.up ℤ)
          (Tensor.sheafTensorBraiding R)).hom =
      (HomologicalComplex.mapBifunctorNatIso K₁ K₂ (ComplexShape.up ℤ)
          (Tensor.sheafTensorBraiding R)).hom ≫
        HomologicalComplex.mapBifunctorMap φ₁ φ₂ (Tensor.sheafTensor R).flip
          (ComplexShape.up ℤ) := by
    refine HomologicalComplex.hom_ext _ _ fun j ↦
      HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h ↦ ?_
    have ha := NatTrans.congr_app
      ((Tensor.sheafTensorBraiding R).hom.naturality (φ₁.f i₁)) (K₂.X i₂)
    simp only [NatTrans.comp_app] at ha
    simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.ι_mapBifunctorNatIso_hom_assoc,
      HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorNatIso_hom]
    rw [reassoc_of% (((Tensor.sheafTensorBraiding R).hom.app (L₁.X i₁)).naturality (φ₂.f i₂)),
      reassoc_of% ha]
  change HomologicalComplex.mapBifunctorMap φ₁ φ₂ (Tensor.sheafTensor R)
          (ComplexShape.up ℤ) ≫
        (HomologicalComplex.mapBifunctorNatIso L₁ L₂ (ComplexShape.up ℤ)
              (Tensor.sheafTensorBraiding R)).hom ≫
          (HomologicalComplex.mapBifunctorFlipIso L₂ L₁ (Tensor.sheafTensor R)
            (ComplexShape.up ℤ)).hom =
      ((HomologicalComplex.mapBifunctorNatIso K₁ K₂ (ComplexShape.up ℤ)
            (Tensor.sheafTensorBraiding R)).hom ≫
          (HomologicalComplex.mapBifunctorFlipIso K₂ K₁ (Tensor.sheafTensor R)
            (ComplexShape.up ℤ)).hom) ≫
        HomologicalComplex.mapBifunctorMap φ₂ φ₁ (Tensor.sheafTensor R)
          (ComplexShape.up ℤ)
  rw [← Category.assoc, hnat, Category.assoc,
    HomologicalComplex.mapBifunctorFlipIso_hom_naturality, Category.assoc]

end Complexes

end Stacks.SheafOfModules

/-! ### The constraints of the derived tensor product are natural -/

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor

namespace Stacks.DerivedTensor.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctorReg K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O)

/-! ### The unit constraint on the right -/

/-- Tensoring a complex of `O`-modules with the structure sheaf in degree zero and passing to
`D(O)`: the functor on complexes that `- ⊗^L_O O` descends. -/
abbrev unitTensorSource : CochainComplex (Modules X.O) ℤ ⥤ DerivedModules X.O :=
  (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj (unitComplex X) ⋙
    DerivedCategory.Q

/-- **`- ⊗^L_O O` descends `K ↦ Q(Tot(K ⊗_O O))`**, the lifting isomorphism being the K-flat
comparison on the right at the structure sheaf in degree zero. -/
@[instance_reducible]
def unitTensorLifting :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
      (unitTensorSource X) (T.tensor.flip.obj (unitObject X)) where
  iso := NatIso.ofComponents
    (fun K ↦ T.comparisonRight K (unitComplex X)
      (Stacks.SheafOfModules.isKFlat_single_unit X.O))
    (fun {_ _} f ↦ by
      have h := T.comparisonRight_naturality f (𝟙 (unitComplex X))
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)
      rwa [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h)

attribute [local instance] unitTensorLifting

/-- The unit constraint of the total tensor product of complexes, read in `D(O)`. -/
def unitTensorTrans : unitTensorSource X ⟶ DerivedCategory.Q where
  app K := DerivedCategory.Q.map (Stacks.SheafOfModules.tensorComplexUnitIso X.O K).hom
  naturality {_ _} f :=
    ((DerivedCategory.Q.map_comp _ _).symm.trans
        (congrArg DerivedCategory.Q.map
          (Stacks.SheafOfModules.tensorComplexUnitIso_naturality X.O f))).trans
      (DerivedCategory.Q.map_comp _ _)

/-- **The unit constraint on the right of a derived tensor product, as a natural
transformation** `- ⊗^L_O O ⟶ id` of endofunctors of `D(O)`: the lift along the
localization of the unit constraint of the total tensor product of complexes. -/
def rightUnitTrans : T.tensor.flip.obj (unitObject X) ⟶ 𝟭 (DerivedModules X.O) :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
    (unitTensorSource X) DerivedCategory.Q (T.tensor.flip.obj (unitObject X))
    (𝟭 _) (unitTensorTrans X)

/-- At the class of a complex the transformation is the K-flat comparison on the right followed
by the unit constraint of the total tensor product of complexes. -/
lemma rightUnitTrans_app_Q (K : CochainComplex (Modules X.O) ℤ) :
    (rightUnitTrans X T).app (DerivedCategory.Q.obj K) =
      (T.comparisonRight K (unitComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map (Stacks.SheafOfModules.tensorComplexUnitIso X.O K).hom := by
  have hiso : (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
        (unitTensorSource X) (T.tensor.flip.obj (unitObject X))).hom.app K =
      (T.comparisonRight K (unitComplex X)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom := rfl
  rw [rightUnitTrans, Localization.liftNatTrans_app, hiso]
  simp [unitTensorTrans]

/-- **The unit constraint on the right is the natural transformation
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitTrans` at that object.** -/
lemma rightUnitIso_hom_eq (A : DerivedModules X.O) :
    (T.rightUnitIso X A).hom = (rightUnitTrans X T).app A := by
  have hnat := (rightUnitTrans X T).naturality (RingedSite.kFlatModelIso X A).hom
  rw [rightUnitTrans_app_Q] at hnat
  have hR : (T.rightUnitIso X A).hom =
      ((T.tensor.mapIso (RingedSite.kFlatModelIso X A)).app (unitObject X)).inv ≫
        (T.comparisonRight (RingedSite.kFlatModel X A) (unitComplex X)
            (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
          DerivedCategory.Q.map (Stacks.SheafOfModules.tensorComplexUnitIso X.O
              (RingedSite.kFlatModel X A)).hom ≫
            (RingedSite.kFlatModelIso X A).hom := rfl
  refine (cancel_epi ((T.tensor.mapIso (RingedSite.kFlatModelIso X A)).app
    (unitObject X)).hom).1 ?_
  rw [hR, Iso.hom_inv_id_assoc, ← Category.assoc]
  exact hnat.symm

/-- **The unit constraint on the right of a derived tensor product is natural.** -/
theorem rightUnitIso_hom_naturality {A B : DerivedModules X.O} (f : A ⟶ B) :
    (T.tensor.map f).app (unitObject X) ≫ (T.rightUnitIso X B).hom =
      (T.rightUnitIso X A).hom ≫ f := by
  rw [rightUnitIso_hom_eq, rightUnitIso_hom_eq]
  exact (rightUnitTrans X T).naturality f

/-! ### The commutativity constraint -/

section Transport

variable {E : Type*} [Category E] (P : E ⥤ E ⥤ E) (θ : P ⟶ P.flip)

/-- **A transformation from a bifunctor to its flip is natural in the pair of variables.** -/
lemma flipTrans_naturality_pair {A A' B B' : E} (α : A ⟶ A') (β : B ⟶ B') :
    (P.obj A).map β ≫ (P.map α).app B' ≫ (θ.app A').app B' =
      (θ.app A).app B ≫ (P.obj B).map α ≫ (P.map β).app A' := by
  have hout := NatTrans.congr_app (θ.naturality α) B
  simp only [NatTrans.comp_app] at hout
  rw [reassoc_of% ((P.map α).naturality β), (θ.app A').naturality β, reassoc_of% hout]
  simp only [Functor.flip_obj_map, Functor.flip_map_app]

/-- **A transformation from a bifunctor to its flip is natural in the second variable alone.** -/
lemma flipTrans_naturality_right (A : E) {B B' : E} (β : B ⟶ B') :
    (P.obj A).map β ≫ (θ.app A).app B' = (θ.app A).app B ≫ (P.map β).app A :=
  (θ.app A).naturality β

end Transport

/-- The total tensor product of a pair of K-flat complexes of `O`-modules, pushed into `D(O)`:
the bifunctor on K-flat complexes that the derived tensor product descends. -/
abbrev kFlatTotSource :
    (Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O).FullSubcategory ⥤
      (Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O).FullSubcategory ⥤
        DerivedModules X.O :=
  (((Functor.whiskeringLeft₂ (DerivedModules X.O)).obj
        (Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O).ι).obj
      (Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O).ι).obj
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)

/-- **The derived tensor bifunctor descends the total tensor product of K-flat complexes**, the
lifting isomorphism being the K-flat comparison. -/
@[instance_reducible]
def kFlatTotLifting :
    Localization.Lifting₂ (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O)
      (kFlatTotSource X) T.tensor where
  iso := NatIso.ofComponents
    (fun K ↦ NatIso.ofComponents (fun L ↦ T.comparison K.1 L.1 K.2 L.2)
      (fun {L L'} g ↦ by
        have h := T.comparison_naturality (𝟙 K.1) g.hom K.2 K.2 L.2 L'.2
        rwa [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
          Category.id_comp] at h))
    (fun {K K'} f ↦ by
      ext L
      have h := T.comparison_naturality f.hom (𝟙 L.1) K.2 K'.2 L.2 L.2
      rwa [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h)

attribute [local instance] kFlatTotLifting

/-- The Koszul symmetry of the total tensor product of K-flat complexes of `O`-modules, read in
`D(O)`: a transformation from the bifunctor `(K, L) ↦ Q(Tot(K ⊗_O L))` to its flip. -/
def kFlatFlipTrans : kFlatTotSource X ⟶ (kFlatTotSource X).flip where
  app K :=
    { app := fun L ↦ DerivedCategory.Q.map
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O K.1 L.1).hom
      naturality := fun {_ _} g ↦
        ((DerivedCategory.Q.map_comp _ _).symm.trans
            (congrArg DerivedCategory.Q.map
              (Stacks.SheafOfModules.tensorComplexFlipIso_hom_naturality X.O
                (𝟙 K.1) g.hom))).trans
          (DerivedCategory.Q.map_comp _ _) }
  naturality {_ _} f := by
    ext L
    exact ((DerivedCategory.Q.map_comp _ _).symm.trans
        (congrArg DerivedCategory.Q.map
          (Stacks.SheafOfModules.tensorComplexFlipIso_hom_naturality X.O
            f.hom (𝟙 L.1)))).trans
      (DerivedCategory.Q.map_comp _ _)

/-- **The commutativity constraint of a derived tensor product, as a transformation**
`- ⊗^L_O - ⟶ (- ⊗^L_O -)ᶠˡⁱᵖ`: the lift along the localization of the K-flat complexes to
`D(O)` of the Koszul symmetry of the total tensor product of complexes. -/
def braidingTrans : T.tensor ⟶ T.tensor.flip :=
  Localization.lift₂NatTrans (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O)
    (kFlatTotSource X) ((kFlatTotSource X).flip)
    T.tensor T.tensor.flip (kFlatFlipTrans X)

/-- At a pair of K-flat complexes the transformation is the K-flat comparison, the Koszul
symmetry of complexes, and the inverse of the comparison of the exchanged pair. -/
lemma braidingTrans_app_app (K L : CochainComplex (Modules X.O) ℤ)
    (hK : Stacks.SheafOfModules.KFlat X.O K)
    (hL : Stacks.SheafOfModules.KFlat X.O L) :
    ((braidingTrans X T).app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
      (T.comparison K L hK hL).hom ≫
        DerivedCategory.Q.map
            (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O K L).hom ≫
          (T.comparison L K hL hK).inv :=
  Localization.lift₂NatTrans_app_app
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso X.O)
    (kFlatTotSource X) ((kFlatTotSource X).flip)
    T.tensor T.tensor.flip (kFlatFlipTrans X)
    (⟨K, hK⟩ : (Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O).FullSubcategory)
    (⟨L, hL⟩ : (Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O).FullSubcategory)

/-- **The commutativity constraint is the transformation
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingTrans` at that pair of
objects.** -/
lemma braidingIso_hom_eq (A B : DerivedModules X.O) :
    (T.braidingIso X A B).hom = ((braidingTrans X T).app A).app B := by
  have key := flipTrans_naturality_pair T.tensor (braidingTrans X T)
    (RingedSite.kFlatModelIso X A).hom (RingedSite.kFlatModelIso X B).hom
  rw [braidingTrans_app_app X T (RingedSite.kFlatModel X A) (RingedSite.kFlatModel X B)
    (RingedSite.isKFlat_kFlatModel X A) (RingedSite.isKFlat_kFlatModel X B)] at key
  have hB : (T.braidingIso X A B).hom =
      ((T.tensor.mapIso (RingedSite.kFlatModelIso X A)).app B).inv ≫
        ((T.tensor.obj (DerivedCategory.Q.obj (RingedSite.kFlatModel X A))).mapIso
            (RingedSite.kFlatModelIso X B)).inv ≫
          (T.comparison (RingedSite.kFlatModel X A) (RingedSite.kFlatModel X B)
              (RingedSite.isKFlat_kFlatModel X A)
              (RingedSite.isKFlat_kFlatModel X B)).hom ≫
            DerivedCategory.Q.map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
                (RingedSite.kFlatModel X A) (RingedSite.kFlatModel X B)).hom ≫
              (T.comparison (RingedSite.kFlatModel X B) (RingedSite.kFlatModel X A)
                  (RingedSite.isKFlat_kFlatModel X B)
                  (RingedSite.isKFlat_kFlatModel X A)).inv ≫
                (T.tensor.obj (DerivedCategory.Q.obj (RingedSite.kFlatModel X B))).map
                    (RingedSite.kFlatModelIso X A).hom ≫
                  (T.tensor.map (RingedSite.kFlatModelIso X B).hom).app A := rfl
  refine Eq.symm ?_
  rw [hB, Iso.eq_inv_comp, Iso.eq_inv_comp]
  simp only [Category.assoc] at key ⊢
  exact key

/-- **The commutativity constraint of a derived tensor product is natural in both objects.** -/
theorem braidingIso_hom_naturality {A A' B B' : DerivedModules X.O} (f : A ⟶ A') (g : B ⟶ B') :
    (T.tensor.map f).app B ≫ (T.tensor.obj A').map g ≫ (T.braidingIso X A' B').hom =
      (T.braidingIso X A B).hom ≫ (T.tensor.map g).app A ≫ (T.tensor.obj B').map f := by
  rw [braidingIso_hom_eq, braidingIso_hom_eq]
  rw [← reassoc_of% ((T.tensor.map f).naturality g), ← (T.tensor.map g).naturality f]
  exact flipTrans_naturality_pair T.tensor (braidingTrans X T) f g

/-- **The commutativity constraint of a derived tensor product is natural in its second
object**, the first being held fixed. -/
theorem braidingIso_hom_naturality_right (A : DerivedModules X.O) {B B' : DerivedModules X.O}
    (g : B ⟶ B') :
    (T.tensor.obj A).map g ≫ (T.braidingIso X A B').hom =
      (T.braidingIso X A B).hom ≫ (T.tensor.map g).app A := by
  rw [braidingIso_hom_eq, braidingIso_hom_eq]
  exact flipTrans_naturality_right T.tensor (braidingTrans X T) A g

/-! ### The unit constraint on the left -/

/-- **The unit constraint on the left of a derived tensor product is natural.** -/
theorem leftUnitIso_hom_naturality {A B : DerivedModules X.O} (f : A ⟶ B) :
    (T.tensor.obj (unitObject X)).map f ≫ (T.leftUnitIso X B).hom =
      (T.leftUnitIso X A).hom ≫ f := by
  rw [leftUnitIso_eq, leftUnitIso_eq, Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
    braidingIso_hom_naturality_right, Category.assoc, Category.assoc,
    rightUnitIso_hom_naturality]

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
