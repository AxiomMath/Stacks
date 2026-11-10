module

public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.Homology.KFlat.BifunctorComparisonOneVariable
public import StacksFrontier.Homology.RightUnitorShift

/-!
# The right unitor of the monoidal derived category commutes with the shift

Let `(C, O)` be a ringed site. The monoidal structure
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` on `D(Mod(O))` of
[Stacks, Tag 0FPT] has the derived tensor product of [Stacks, Tag 06YU] as its tensor product.
This file shows that its right unitor `K ⊗ᴸ O ≅ K` commutes with the shift in `K`, for the
commutation of `- ⊗ᴸ O` with the shift carried by the derived tensor product,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift_left`.

## The argument

Both are tested on the left K-flat complexes `K`, which reach every object of `D(Mod(O))`. There
the unitor is the K-flat comparison `Q(K) ⊗ᴸ Q(O) ≅ Q(K ⊗ O)` followed by `Q` of the right unitor
of complexes (`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_rightUnitor` for `K`
K-flat, and by naturality along a K-flat resolution for `K` left K-flat). The comparison commutes
with the shift in `K` (`CochainComplex.KFlatBifunctor.comparisonFirst_commShift`, read at the
canonical derived tensor product through `canonicalDerivedTensorProduct_eq`), and so does the
right unitor of complexes (`CochainComplex.mapBifunctorShift₁Iso_hom_comp_shift_rightUnitor_hom`).

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.commShift_canonicalRightUnitor` — the right unitor of
  `canonicalDerivedMonoidal`, as a morphism of functors `(- ⊗ᴸ O) ⟶ 𝟭`, commutes with the shift.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalRightUnitorHom_Q_obj` — on the image of a
  complex `K`, the right unitor is the one-sided K-flat comparison followed by `Q` of the right
  unitor of complexes.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

attribute [local instance 10000] CochainComplex.symmetricCategory
  SheafOfModules.monoidalCategorySheafTensor

attribute [local instance 100000] monoidalCategoryStructComplexes

/-! ### The right unitor of complexes as a morphism of functors -/

/-- The right unitor of complexes of `O`-modules, `Tot(K ⊗ O) ⟶ K`, as a morphism of functors
out of `K ↦ Tot(K ⊗ O)` formed with the tensor product of sheaves of modules, which is the
spelling of the K-flat comparison of [Stacks, Tag 06YU]. It is the right unitor of the monoidal
category of complexes, read through `SheafOfModules.curriedTensor_sheafTensor`. -/
def complexRightUnitorNatTrans :
    (totalBifunctor (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).flip.obj
        (𝟙_ (Complexes R)) ⟶
      𝟭 (Complexes R) :=
  eqToHom (CochainComplex.map₂CochainComplex_flip_obj_eq
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (curriedTensor (Mod R))
      (SheafOfModules.curriedTensor_sheafTensor R).symm (𝟙_ (Complexes R))) ≫
    CochainComplex.map₂CochainComplexFlipObjToTensorRight (𝟙_ (Complexes R)) ≫
      (rightUnitorNatIso (Complexes R)).hom

omit [HasDerivedCategory.{d} (Mod R)] in
/-- The components of `complexRightUnitorNatTrans` are the right unitor of complexes. -/
theorem complexRightUnitorNatTrans_app (K : Complexes R) :
    (complexRightUnitorNatTrans R).app K = (ρ_ K).hom :=
  rfl

/-- **The right unitor of complexes commutes with the shift.** -/
instance commShift_complexRightUnitorNatTrans :
    NatTrans.CommShift (complexRightUnitorNatTrans R) ℤ := by
  have := CochainComplex.commShift_eqToHom_map₂CochainComplex_flip_obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (curriedTensor (Mod R))
    (SheafOfModules.curriedTensor_sheafTensor R).symm (𝟙_ (Complexes R))
  unfold complexRightUnitorNatTrans
  infer_instance

/-! ### The one-sided K-flat comparison as a morphism of functors -/

variable {R} in
/-- The one-sided K-flat comparison `Q(K) ⊗ᴸ Q(L) ≅ Q(Tot(K ⊗ L))` of a derived tensor product
`T`, at a fixed K-flat complex `L`, as an isomorphism of functors of the left K-flat complex
`K`. -/
def comparisonRightFirst (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)
    {L : Complexes R} (hL : Stacks.SheafOfModules.KFlat R L) :
    kFlatComplexQLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) ⋙
        T.tensor.flip.obj (DerivedCategory.Q.obj L) ≅
      (kFlatComplexesLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).ι ⋙
        ((totalBifunctor (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).flip.obj L ⋙
          DerivedCategory.Q) :=
  NatIso.ofComponents (fun K => T.comparisonRight K.1 L hL) (fun {K K'} f => by
    have h := T.comparisonRight_naturality f.hom (𝟙 L) hL hL
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h)

variable {R} in
/-- The components of `comparisonRightFirst` are the one-sided K-flat comparison. -/
theorem comparisonRightFirst_hom_app (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)
    {L : Complexes R} (hL : Stacks.SheafOfModules.KFlat R L)
    (K : (kFlatComplexesLeft
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).FullSubcategory) :
    (comparisonRightFirst T hL).hom.app K = (T.comparisonRight K.1 L hL).hom :=
  rfl

/-- The one-sided comparison of the construction of the derived tensor product is the
comparison `CochainComplex.KFlatBifunctor.comparisonFirst`, and so commutes with the shift. -/
theorem commShift_comparisonRightFirst_of_eq
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)
    (hT : T = Stacks.DerivedTensor.RingedSite.derivedTensorProductConstruction R)
    {L : Complexes R} (hL : Stacks.SheafOfModules.KFlat R L) :
    NatTrans.CommShift (comparisonRightFirst T hL).hom ℤ := by
  subst hT
  have h : comparisonRightFirst
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductConstruction R) hL =
      comparisonFirst (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) L hL := by
    ext K
    exact (congrArg Iso.hom (comparisonRight_eq_comparison _ K.1 L K.2 hL)).trans
      (comparisonFirst_hom_app _ L hL K).symm
  rw [h]
  exact comparisonFirst_commShift
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) L hL

/-- **The one-sided comparison of the canonical derived tensor product commutes with the shift**
in the left variable. -/
theorem commShift_comparisonRightFirst {L : Complexes R}
    (hL : Stacks.SheafOfModules.KFlat R L) :
    NatTrans.CommShift
      (comparisonRightFirst (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R)
        hL).hom ℤ :=
  commShift_comparisonRightFirst_of_eq R _
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct_eq R) hL

/-! ### The right unitor of the derived category -/

/-- The left K-flat complexes reach every object of `D(Mod(O))`. -/
theorem kFlatComplexQLeft_essSurj :
    (kFlatComplexQLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).EssSurj where
  mem_essImage X := by
    obtain ⟨P, f, hP, hf⟩ :=
      Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso R (DerivedCategory.Q.objPreimage X)
    have : IsIso (DerivedCategory.Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
    exact ⟨⟨P, Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat R hP⟩,
      ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

/-- **The right unitor of `D(Mod(O))` on the image of a complex** `K` is the one-sided K-flat
comparison `Q(K) ⊗ᴸ Q(O) ≅ Q(K ⊗ O)` followed by `Q` of the right unitor of complexes. For `K`
K-flat this is `canonicalComparison_rightUnitor`; in general it follows by naturality along a
K-flat resolution of `K`. -/
theorem canonicalRightUnitorHom_Q_obj (K : Complexes R) :
    canonicalRightUnitorHom R (DerivedCategory.Q.obj K) =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparisonRight K
          (𝟙_ (Complexes R)) (kFlat_tensorUnit_complexes R)).hom ≫
        DerivedCategory.Q.map ((complexRightUnitorNatTrans R).app K) := by
  obtain ⟨P, p, hP, hp⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso R K
  have hP' : Stacks.SheafOfModules.KFlat R P := hP
  have hPcase : canonicalRightUnitorHom R (DerivedCategory.Q.obj P) =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparisonRight P
          (𝟙_ (Complexes R)) (kFlat_tensorUnit_complexes R)).hom ≫
        DerivedCategory.Q.map ((complexRightUnitorNatTrans R).app P) := by
    rw [canonicalComparison_rightUnitor R P hP', canonicalComparisonHom_eq,
      canonicalComparison_hom,
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        R).comparisonRight_eq_comparison P (𝟙_ (Complexes R)) hP' (kFlat_tensorUnit_complexes R),
      complexRightUnitorNatTrans_app]
    rfl
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have n1 : ((derivedTensorBifunctorOfSite R).map
        (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj (𝟙_ (Complexes R))) ≫
        canonicalRightUnitorHom R (DerivedCategory.Q.obj K) =
      canonicalRightUnitorHom R (DerivedCategory.Q.obj P) ≫ DerivedCategory.Q.map p :=
    let := canonicalDerivedMonoidal R
    rightUnitor_naturality (DerivedCategory.Q.map p)
  have n2 : ((derivedTensorBifunctorOfSite R).map
        (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj (𝟙_ (Complexes R))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparisonRight K
          (𝟙_ (Complexes R)) (kFlat_tensorUnit_complexes R)).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparisonRight P
          (𝟙_ (Complexes R)) (kFlat_tensorUnit_complexes R)).hom ≫
        DerivedCategory.Q.map
          (((totalBifunctor (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).flip.obj
            (𝟙_ (Complexes R))).map p) := by
    have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      R).comparisonRight_naturality p (𝟙 (𝟙_ (Complexes R))) (kFlat_tensorUnit_complexes R)
      (kFlat_tensorUnit_complexes R)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  have n3 := (complexRightUnitorNatTrans R).naturality p
  rw [Functor.id_map] at n3
  apply (cancel_epi (((derivedTensorBifunctorOfSite R).map
    (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj (𝟙_ (Complexes R))))).1
  rw [n1, hPcase]
  erw [Category.assoc, ← DerivedCategory.Q.map_comp, ← n3,
    DerivedCategory.Q.map_comp, ← Category.assoc, ← n2, Category.assoc]
  rfl

/-- **The right unitor of the monoidal derived category of Tag 0FPT commutes with the shift**,
for the commutation of `- ⊗ᴸ O` with the shift carried by the derived tensor product of
[Stacks, Tag 06YU]. -/
theorem commShift_canonicalRightUnitor :
    letI := canonicalDerivedMonoidal R
    letI : (tensorRight (𝟙_ (DerivedModules R))).CommShift ℤ :=
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).commShift_left _
    NatTrans.CommShift (rightUnitorNatIso (DerivedModules R)).hom ℤ := by
  let := canonicalDerivedMonoidal R
  let : (tensorRight (𝟙_ (DerivedModules R))).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).commShift_left _
  have := kFlatComplexQLeft_essSurj R
  have hc := commShift_comparisonRightFirst R (kFlat_tensorUnit_complexes R)
  apply NatTrans.commShift_of_whiskerLeft
    (kFlatComplexQLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R))
  have key : Functor.whiskerLeft
      (kFlatComplexQLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R))
      (rightUnitorNatIso (DerivedModules R)).hom =
      (comparisonRightFirst (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R)
          (kFlat_tensorUnit_complexes R)).hom ≫
        Functor.whiskerLeft
          (kFlatComplexesLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).ι
          (Functor.whiskerRight (complexRightUnitorNatTrans R) DerivedCategory.Q ≫
            (Functor.leftUnitor DerivedCategory.Q).hom) ≫
        (Functor.rightUnitor
          (kFlatComplexQLeft
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R))).inv := by
    ext K
    exact (canonicalRightUnitorHom_Q_obj R K.1).trans
      (by simp [comparisonRightFirst_hom_app]; rfl)
  rw [key]
  infer_instance

end Stacks.SheafOfModules.DerivedMonoidal

end
