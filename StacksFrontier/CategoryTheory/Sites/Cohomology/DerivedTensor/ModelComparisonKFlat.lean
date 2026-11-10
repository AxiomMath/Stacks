module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonQuotient
public import StacksFrontier.Homology.KFlat.BifunctorModelComparisonKFlat

/-!
# The derived tensor product at the two models, on K-flat complexes

`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso` compares the derived tensor
product of a ringed site at the standard model and at the locally small model of Tag 079Q through
the comparison equivalence `G`. On two K-flat complexes `K`, `L` its component is the canonical
composite through `Q(Tot(K ⊗ L))`: the K-flat comparison of [Stacks, Tag 06YU] at the locally small
model, followed by the image under `G` of the inverse of the K-flat comparison at the standard
model.

## Main results

* `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct_comparison_hom` — at any model,
  the K-flat comparison of `canonicalDerivedTensorProduct` is the identification of its bifunctor
  with the derived bifunctor, followed by the one-sided comparison of that derived bifunctor.
* `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso_hom_app_app_of_kFlat` —
  the component of `derivedTensorProductFunctorModelIso` at `(Q K, Q L)` for `K`, `L` K-flat,
  with the companions `derivedTensorProductFunctorModelIso_hom_app_app_comp_map_comparison_hom`
  and `derivedTensorProductFunctorModelIso_inv_app_app_comp_comparison_hom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedTensor.RingedSite

/-- Generic shape of the component of the comparison of two models of a derived bifunctor at
the classes of two complexes, from its component at their homotopy classes. -/
private lemma modelIso_app_app_aux {E₁ E₂ : Type*} [Category E₁] [Category E₂] (G : E₁ ⥤ E₂)
    (T₁ : E₁ ⥤ E₁ ⥤ E₁) (T₂ : E₂ ⥤ E₂ ⥤ E₂)
    (M : G ⋙ T₂ ⋙ (Functor.whiskeringLeft _ _ _).obj G ⟶
      T₁ ⋙ (Functor.whiskeringRight _ _ _).obj G)
    {k₁ kh₁ l₁ lh₁ h₁ t₁ : E₁} {kh₂ lh₂ h₂ : E₂}
    (a₁ : k₁ ≅ kh₁) (b₁ : l₁ ≅ lh₁) (a₂ : G.obj k₁ ⟶ kh₂) (b₂ : G.obj l₁ ⟶ lh₂)
    (sA : G.obj kh₁ ⟶ kh₂) (sB : G.obj lh₁ ⟶ lh₂)
    (hA : G.map a₁.hom ≫ sA = a₂) (hB : G.map b₁.hom ≫ sB = b₂)
    (ci₁ : (T₁.obj kh₁).obj lh₁ ≅ h₁) (ci₂ : (T₂.obj kh₂).obj lh₂ ⟶ h₂) (sD : h₂ ⟶ G.obj h₁)
    (hM : (M.app kh₁).app lh₁ =
      (T₂.map sA).app (G.obj lh₁) ≫ (T₂.obj kh₂).map sB ≫ ci₂ ≫ sD ≫ G.map ci₁.inv)
    (tq₁ : h₁ ≅ t₁) (tq₂ : h₂ ⟶ G.obj t₁) (htq : sD ≫ G.map tq₁.hom = tq₂)
    (cR₁ : (T₁.obj k₁).obj l₁ ≅ t₁)
    (hcR₁ : cR₁.hom = (T₁.obj k₁).map b₁.hom ≫ (T₁.map a₁.hom).app lh₁ ≫ ci₁.hom ≫ tq₁.hom)
    (cR₂ : (T₂.obj (G.obj k₁)).obj (G.obj l₁) ⟶ G.obj t₁)
    (hcR₂ : cR₂ = (T₂.obj (G.obj k₁)).map b₂ ≫ (T₂.map a₂).app lh₂ ≫ ci₂ ≫ tq₂) :
    (M.app k₁).app l₁ = cR₂ ≫ G.map cR₁.inv := by
  rw [← cancel_mono (G.map cR₁.hom), Category.assoc, ← G.map_comp, cR₁.inv_hom_id, G.map_id,
    Category.comp_id, hcR₁, hcR₂, ← hA, ← hB, ← htq]
  have n1 : (M.app k₁).app l₁ ≫ G.map ((T₁.obj k₁).map b₁.hom) =
      (T₂.obj (G.obj k₁)).map (G.map b₁.hom) ≫ (M.app k₁).app lh₁ :=
    ((M.app k₁).naturality b₁.hom).symm
  have n2 : (M.app k₁).app lh₁ ≫ G.map ((T₁.map a₁.hom).app lh₁) =
      (T₂.map (G.map a₁.hom)).app (G.obj lh₁) ≫ (M.app kh₁).app lh₁ :=
    (congr_app (M.naturality a₁.hom) lh₁).symm
  have n3 : (T₂.obj (G.obj k₁)).map sB ≫ (T₂.map (G.map a₁.hom ≫ sA)).app lh₂ =
      (T₂.map (G.map a₁.hom ≫ sA)).app (G.obj lh₁) ≫ (T₂.obj kh₂).map sB :=
    (T₂.map (G.map a₁.hom ≫ sA)).naturality sB
  simp only [G.map_comp]
  rw [reassoc_of% n1, reassoc_of% n2, hM]
  simp only [Category.assoc, ← G.map_comp, ci₁.inv_hom_id_assoc]
  rw [Functor.map_comp (T₂.obj (G.obj k₁)), Category.assoc, reassoc_of% n3]
  simp

/-- Generic shape of `derivedTensorProductFunctorModelIso_hom_app_app_of_kFlat` from the
component of the comparison of the two derived bifunctors. -/
private lemma conj_aux {E₁ E₂ : Type*} [Category E₁] [Category E₂] (G : E₁ ⥤ E₂)
    {p₁ q₁ t₁ : E₁} {p₂ q₂ : E₂} (x : p₂ ≅ q₂) (y : p₁ ≅ q₁) (M : q₂ ⟶ G.obj q₁)
    (cR₂ : q₂ ⟶ G.obj t₁) (cR₁ : q₁ ≅ t₁) (hM : M = cR₂ ≫ G.map cR₁.inv)
    (c₂ : p₂ ≅ G.obj t₁) (hc₂ : c₂.hom = x.hom ≫ cR₂) (c₁ : p₁ ≅ t₁)
    (hc₁ : c₁.hom = y.hom ≫ cR₁.hom) :
    x.hom ≫ M ≫ G.map y.inv = c₂.hom ≫ G.map c₁.inv := by
  have hc₁' : c₁.inv = cR₁.inv ≫ y.inv := by
    rw [← cancel_epi c₁.hom, Iso.hom_inv_id, hc₁]
    simp
  rw [hM, hc₂, hc₁', G.map_comp, Category.assoc, Category.assoc]

/-- Generic shape of the comparison of the two total-complex bridges. -/
private lemma totalComplexQhIso_aux {H E₁ E₂ : Type*} [Category H] [Category E₁] [Category E₂]
    (G : E₁ ⥤ E₂) (Qh₁ : H ⥤ E₁) (Qh₂ : H ⥤ E₂) (s : Qh₂ ≅ Qh₁ ⋙ G) {x y : H} (h : x ⟶ y)
    {t₁ : E₁} (b₁ : Qh₁.obj y ⟶ t₁) (b₂ : Qh₂.obj y ⟶ G.obj t₁)
    (hb : s.hom.app y ≫ G.map b₁ = b₂) :
    s.hom.app x ≫ G.map (Qh₁.map h ≫ b₁) = Qh₂.map h ≫ b₂ := by
  rw [G.map_comp, ← hb, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ G.map b₁) (s.hom.naturality h).symm

/-- Generic shape of `canonicalDerivedTensorProduct_comparison_hom`. -/
private lemma comparison_hom_aux {E : Type*} [Category E] {T T' : E ⥤ E ⥤ E} (e : T = T')
    {X Y Z : E} (c : (T.obj X).obj Y ≅ Z) (c' : (T'.obj X).obj Y ≅ Z)
    (h : HEq c c') : c.hom = ((eqToIso e).hom.app X).app Y ≫ c'.hom := by
  subst e
  cases eq_of_heq h
  simp

/-- Generic shape of `derivedTensorProductFunctorModelIso_hom_app_app_comp_map_comparison_hom`. -/
private lemma comp_map_hom_of_eq_aux {E₁ E₂ : Type*} [Category E₁] [Category E₂] (G : E₁ ⥤ E₂)
    {X Y : E₁} {P : E₂} (a : P ⟶ G.obj Y) (b : X ≅ Y) (e : P ⟶ G.obj X)
    (h : e = a ≫ G.map b.inv) : e ≫ G.map b.hom = a := by
  rw [h, Category.assoc, ← G.map_comp, b.inv_hom_id, G.map_id, Category.comp_id]

/-- Generic shape of `derivedTensorProductFunctorModelIso_inv_app_app_comp_comparison_hom`. -/
private lemma inv_comp_of_hom_comp_aux {E : Type*} [Category E] {P Q Z : E} (e : P ≅ Q)
    (a : P ⟶ Z) (c : Q ⟶ Z) (h : e.hom ≫ c = a) : e.inv ≫ a = c := by
  rw [← h, Iso.inv_hom_id_assoc]

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

section

variable [h : HasDerivedCategory (Modules R)]

/-- **The K-flat comparison of the canonical derived tensor product**, at any model: the
identification `derivedTensorProductFunctorIsoDerivedBifunctor` of its bifunctor with the derived
bifunctor of the total tensor complex, followed by the one-sided comparison of that derived
bifunctor. -/
theorem canonicalDerivedTensorProduct_comparison_hom (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) (hL : Stacks.SheafOfModules.KFlat R L) :
    ((canonicalDerivedTensorProduct R).comparison K L hK hL).hom =
      ((derivedTensorProductFunctorIsoDerivedBifunctor R).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        (@CochainComplex.KFlatBifunctor.comparisonRight _ _ _ _ _ _ _ _ _
          (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _ h h h
          _ _ K L hL).hom :=
  comparison_hom_aux _ _ _ (by rw [canonicalDerivedTensorProduct_eq]; rfl)

end

/-- The components of `derivedTensorProductFunctorModelIso`: the identification of the derived
tensor product with the derived bifunctor at the locally small model, the comparison
`CochainComplex.KFlatBifunctor.derivedBifunctorModelIso` of the two derived bifunctors, and the
image of the inverse identification at the standard model. -/
theorem derivedTensorProductFunctorModelIso_hom_app_app [IsGrothendieckAbelian.{u} (Modules R)]
    (X Y : @DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard (Modules R))) :
    ((derivedTensorProductFunctorModelIso R).hom.app X).app Y =
      ((derivedTensorProductFunctorIsoDerivedBifunctor R (h :=
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)))).hom.app
          ((Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.obj X)).app
          ((Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.obj Y) ≫
        (((CochainComplex.KFlatBifunctor.derivedBifunctorModelIso
            (Stacks.SheafOfModules.Tensor.sheafTensor R)
          (HasDerivedCategory.standard (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (HasDerivedCategory.standard (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (HasDerivedCategory.standard (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
          (exists_kFlatLeft_quasiIso R) (exists_kFlat_quasiIso R)
              (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
              (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
              (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
          (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
              (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
              (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm).hom.app X).app Y) ≫
        (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.map
            (((derivedTensorProductFunctorIsoDerivedBifunctor R (h := (HasDerivedCategory.standard
            (Modules R)))).inv.app X).app Y) := by
  simp [derivedTensorProductFunctorModelIso]
  rfl

/-- **The derived tensor product at the two models, on K-flat complexes.** For `K`, `L` K-flat,
the component of `derivedTensorProductFunctorModelIso` at `(Q K, Q L)` is the canonical composite
through `Q(Tot(K ⊗ L))`: the K-flat comparison of [Stacks, Tag 06YU] at the locally small model,
followed by the image under the comparison equivalence of the inverse of the K-flat comparison at
the standard model. -/
theorem derivedTensorProductFunctorModelIso_hom_app_app_of_kFlat
    [IsGrothendieckAbelian.{u} (Modules R)] (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) (hL : Stacks.SheafOfModules.KFlat R L) :
    ((derivedTensorProductFunctorModelIso R).hom.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj K)).app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj L) =
      (@DerivedTensorProduct.comparison _ _ _ R _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) _ _ _
          (@canonicalDerivedTensorProduct _ _ _ R _ _
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) _ _
              _) K L hK hL).hom ≫
        (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.map
          (@DerivedTensorProduct.comparison _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _
              _ _
            (@canonicalDerivedTensorProduct _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _
                _ _) K L hK hL).inv := by
  rw [derivedTensorProductFunctorModelIso_hom_app_app]
  refine conj_aux (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
    (((derivedTensorProductFunctorIsoDerivedBifunctor R (h :=
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)))).app
      ((Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.obj ((@DerivedCategory.Q
          _ _ _ (HasDerivedCategory.standard (Modules R))).obj K))).app
      ((Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.obj ((@DerivedCategory.Q
          _ _ _ (HasDerivedCategory.standard (Modules R))).obj L)))
    (((derivedTensorProductFunctorIsoDerivedBifunctor R (h := (HasDerivedCategory.standard (Modules
        R)))).app
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj K)).app
          ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj L))
    (((CochainComplex.KFlatBifunctor.derivedBifunctorModelIso
        (Stacks.SheafOfModules.Tensor.sheafTensor R)
          (HasDerivedCategory.standard (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (HasDerivedCategory.standard (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (HasDerivedCategory.standard (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
          (exists_kFlatLeft_quasiIso R) (exists_kFlat_quasiIso R)
              (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
              (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
              (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
          (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
              (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
              (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm).hom.app
              ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj K)).app
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj L))
    (@CochainComplex.KFlatBifunctor.comparisonRight _ _ _ _ _ _ _ _ _
        (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
          _ _ K L hL).hom (@CochainComplex.KFlatBifunctor.comparisonRight
                _ _ _ _ _ _ _ _ _ (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _
          (HasDerivedCategory.standard (Modules R)) (HasDerivedCategory.standard (Modules R))
              (HasDerivedCategory.standard (Modules R))
          _ _ K L hL) ?hM _ (canonicalDerivedTensorProduct_comparison_hom
                R (h := (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules
                R))) K L hK hL)
    _ (canonicalDerivedTensorProduct_comparison_hom R (h := (HasDerivedCategory.standard (Modules
        R))) K L hK hL)
  refine modelIso_app_app_aux (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor _
      _ _
      (kh₂ := (@DerivedCategory.Qh _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      (lh₂ := (@DerivedCategory.Qh _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))
      (h₂ := (@DerivedCategory.Qh _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))).obj
        (((CochainComplex.KFlatBifunctor.homotopyBifunctor
            (Stacks.SheafOfModules.Tensor.sheafTensor R)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)))
      ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard (Modules R))).app
          K).symm ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard (Modules
          R))).app L).symm
      ((@DerivedCategory.quotientCompQhIso _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))).inv.app
          K) ((@DerivedCategory.quotientCompQhIso _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))).inv.app
          L)
      ((StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      ((StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) ?hA ?hB
      (((@CochainComplex.KFlatBifunctor.derivedBifunctorComparisonIso _ _ _ _ _ _ _ _ _
          (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _
          (HasDerivedCategory.standard (Modules R)) (HasDerivedCategory.standard (Modules R))
              (HasDerivedCategory.standard (Modules R))
          _ _).app (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                K, kFlatLeft_of_kFlat R hK⟩ :
          (CochainComplex.KFlatBifunctor.kFlatObjectsLeft (Stacks.SheafOfModules.Tensor.sheafTensor
              R)).FullSubcategory)).app (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L,
              hL⟩ :
          (CochainComplex.KFlatBifunctor.kFlatObjects (Stacks.SheafOfModules.Tensor.sheafTensor
              R)).FullSubcategory)) (((@CochainComplex.KFlatBifunctor.derivedBifunctorComparisonIso
              _ _ _ _ _ _ _ _ _ (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))
          _ _).hom.app (⟨(HomotopyCategory.quotient _ (ComplexShape.up
                ℤ)).obj K, kFlatLeft_of_kFlat R hK⟩ :
          (CochainComplex.KFlatBifunctor.kFlatObjectsLeft (Stacks.SheafOfModules.Tensor.sheafTensor
              R)).FullSubcategory)).app (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L,
              hL⟩ :
          (CochainComplex.KFlatBifunctor.kFlatObjects (Stacks.SheafOfModules.Tensor.sheafTensor
              R)).FullSubcategory))
      ((StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).hom.app
          (((CochainComplex.KFlatBifunctor.homotopyBifunctor
          (Stacks.SheafOfModules.Tensor.sheafTensor R)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))) ?hM₂
      (@CochainComplex.KFlatBifunctor.totalComplexQhIso _ _ _ _ _ _ _ _ _
          (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _ (HasDerivedCategory.standard (Modules
          R)) K L)
      (@CochainComplex.KFlatBifunctor.totalComplexQhIso _ _ _ _ _ _ _ _ _
          (Stacks.SheafOfModules.Tensor.sheafTensor R) _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) K L).hom
      ?htq _ ?hcR₁ _ ?hcR₂
  case hA =>
    exact StacksDraft.DerivedModel.map_quotientCompQhIso_inv_app_comp_shrinkComparisonQhIso_inv_app
        _ K
  case hB =>
    exact StacksDraft.DerivedModel.map_quotientCompQhIso_inv_app_comp_shrinkComparisonQhIso_inv_app
        _ L
  case hM₂ =>
    refine Eq.trans (CochainComplex.KFlatBifunctor.derivedBifunctorModelIso_hom_app_app_quotient
      (K := K) (L := L) (hK := kFlatLeft_of_kFlat R hK) (hL := hL) ..) ?_
    congr 1
  case htq =>
    exact totalComplexQhIso_aux (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor
        (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard (Modules R)))
        (@DerivedCategory.Qh _ _ _
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)))
            (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R))
        (((CochainComplex.KFlatBifunctor.homotopyBifunctorIso
            (Stacks.SheafOfModules.Tensor.sheafTensor R)).hom.app K).app L)
        ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard (Modules
            R))).hom.app (CochainComplex.KFlatBifunctor.totalComplex
            (Stacks.SheafOfModules.Tensor.sheafTensor R) K L))
        ((@DerivedCategory.quotientCompQhIso _ _ _
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules
            R))).hom.app (CochainComplex.KFlatBifunctor.totalComplex
            (Stacks.SheafOfModules.Tensor.sheafTensor R) K L))
        (StacksDraft.DerivedModel.shrinkComparisonQhIso_hom_app_quotient_comp _ _)
  case hcR₁ =>
    let := HasDerivedCategory.standard (Modules R)
    refine Eq.trans (CochainComplex.KFlatBifunctor.comparisonRight_hom_eq_of_kFlatLeft
      (K := K) (L := L) (hK := kFlatLeft_of_kFlat R hK) (hL := hL) ..) ?_
    congr 1
  case hcR₂ =>
    let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)
    refine Eq.trans (CochainComplex.KFlatBifunctor.comparisonRight_hom_eq_of_kFlatLeft
      (K := K) (L := L) (hK := kFlatLeft_of_kFlat R hK) (hL := hL) ..) ?_
    congr 1


/-- `derivedTensorProductFunctorModelIso_hom_app_app_of_kFlat`, composed with the image of the
K-flat comparison at the standard model: for `K`, `L` K-flat, the component at `(Q K, Q L)`
followed by `G` of the standard comparison is the comparison at the locally small model. -/
theorem derivedTensorProductFunctorModelIso_hom_app_app_comp_map_comparison_hom
    [IsGrothendieckAbelian.{u} (Modules R)] (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) (hL : Stacks.SheafOfModules.KFlat R L) :
    ((derivedTensorProductFunctorModelIso R).hom.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj K)).app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj L) ≫
      (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.map
          (@DerivedTensorProduct.comparison _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _
          _ _
          (@canonicalDerivedTensorProduct _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _ _
              _) K L hK hL).hom =
      (@DerivedTensorProduct.comparison _ _ _ R _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) _ _ _
          (@canonicalDerivedTensorProduct _ _ _ R _ _
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) _ _
              _) K L hK hL).hom :=
  comp_map_hom_of_eq_aux (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor _
      (@DerivedTensorProduct.comparison _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _ _ _
          (@canonicalDerivedTensorProduct _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _ _
              _) K L hK hL) _
    (derivedTensorProductFunctorModelIso_hom_app_app_of_kFlat R K L hK hL)

/-- The inverse of `derivedTensorProductFunctorModelIso` at `(Q K, Q L)`, for `K`, `L` K-flat,
followed by the K-flat comparison at the locally small model, is the image under `G` of the
comparison at the standard model. -/
theorem derivedTensorProductFunctorModelIso_inv_app_app_comp_comparison_hom
    [IsGrothendieckAbelian.{u} (Modules R)] (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat R K) (hL : Stacks.SheafOfModules.KFlat R L) :
    ((derivedTensorProductFunctorModelIso R).inv.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj K)).app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj L) ≫
      (@DerivedTensorProduct.comparison _ _ _ R _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) _ _ _
          (@canonicalDerivedTensorProduct _ _ _ R _ _
              (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) _ _
              _) K L hK hL).hom =
      (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor.map
          (@DerivedTensorProduct.comparison _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _
          _ _
          (@canonicalDerivedTensorProduct _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _ _
              _) K L hK hL).hom :=
  inv_comp_of_hom_comp_aux
    (((derivedTensorProductFunctorModelIso R).app ((@DerivedCategory.Q _ _ _
        (HasDerivedCategory.standard (Modules R))).obj K)).app
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules R))).obj L)) _ _
    (derivedTensorProductFunctorModelIso_hom_app_app_comp_map_comparison_hom R K L hK hL)

end Stacks.DerivedTensor.RingedSite

end
