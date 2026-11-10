module

public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor

/-!
# The tensorator of a derived monoidal functor on K-flat complexes

Let `Φ : D(A) ⥤ D(B)` be computed on K-flat objects by an additive monoidal functor `F : A ⥤ B`
preserving K-flatness, through `e : kFlatQ ⋙ Φ ≅ kFlatLift F ⋙ kFlatQ`, and give it the monoidal
structure `CochainComplex.KFlatMonoidal.derivedFunctorMonoidal`. For K-flat complexes `K`, `L`
write `P K : Φ(QK) ≅ Q(FK)` for the comparison read off from `e`. Then the tensorator of `Φ` at
`(QK, QL)` corresponds, through `P` and the comparisons `QK ⊗ QL ≅ Q(K ⊗ L)` of the two
monoidal derived categories, to the image under `Q` of the tensorator of `F` on complexes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatBifunctor

universe w w' v₁ v₂ u₁ u₂

namespace CochainComplex.KFlatMonoidal

attribute [local instance] homotopyMonoidal

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ B, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : A ⥤ B) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) F]

attribute [local instance] homotopyMonoidal

variable (hF : ∀ K : CochainComplex A ℤ,
  _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K →
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) P ∧ QuasiIso f)
  (Φ : DerivedCategory A ⥤ DerivedCategory B)
  (e : kFlatQ (curriedTensor A) ⋙ Φ ≅ kFlatLift F hF ⋙ kFlatQ (curriedTensor B))

/-- The bookkeeping behind `derivedFunctorMonoidal_μ_kFlatQ`, in an arbitrary category. -/
private lemma comp_eq_of_μ {C : Type*} [Category C] {S T₁ U₁ U₂ U₃ U₄ T₃ T₄ T₅ V₁ V₂ W₁ : C}
    {μΦ : S ⟶ T₁} {t₁ : S ⟶ U₁} {μB : U₁ ⟶ U₂} {kμ : U₂ ⟶ U₃} {einv : U₃ ⟶ U₄}
    {mAinv : U₄ ⟶ T₁} {mAhom : T₁ ⟶ U₄} {u : U₄ ⟶ T₃} {eZ : T₃ ⟶ T₄} {fac : T₄ ⟶ T₅}
    {km : U₃ ⟶ T₄} {w : U₂ ⟶ T₅} {g₁ : U₂ ⟶ V₁} {g₂ : V₁ ⟶ V₂} {g₃ : V₂ ⟶ T₅}
    {t₂ : U₁ ⟶ W₁} {μB' : W₁ ⟶ V₁} {t₃ : S ⟶ W₁}
    (hμ : μΦ = t₁ ≫ μB ≫ kμ ≫ einv ≫ mAinv) (h₁ : mAinv ≫ mAhom = 𝟙 U₄)
    (hb : einv ≫ u ≫ eZ = km) (hc : kμ ≫ km ≫ fac = w) (hw : w = g₁ ≫ g₂ ≫ g₃)
    (hd : μB ≫ g₁ = t₂ ≫ μB') (htc : t₁ ≫ t₂ = t₃) :
    μΦ ≫ mAhom ≫ u ≫ eZ ≫ fac = t₃ ≫ μB' ≫ g₂ ≫ g₃ := by
  rw [hμ]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% hb, hc, hw, reassoc_of% hd,
    reassoc_of% htc]

omit [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] in
/-- On the classes of K-flat complexes `K`, `L`, the image under `kFlatQ` of the tensorator of
`kFlatLift F hF` followed by `homotopyMu A K L` is the image of the tensorator of `F` on
complexes, up to `Functor.mapHomotopyCategoryFactors`. -/
private lemma kFlatQ_map_kFlatLift_μ_comp_homotopyMu {K L : CochainComplex A ℤ}
    (hK : kFlatObjects (curriedTensor A) ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
    (hL : kFlatObjects (curriedTensor A) ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L))
    (hKL : kFlatObjects (curriedTensor A)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K ⊗ L))) :
    letI := kFlatLiftMonoidal F hF
    (kFlatQ (curriedTensor B)).map (Functor.LaxMonoidal.μ (kFlatLift F hF)
        ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
        ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩) ≫
      (kFlatQ (curriedTensor B)).map ((kFlatLift F hF).map
        (ObjectProperty.homMk (homotopyMu A K L).hom :
          (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ⊗
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ :
              (kFlatObjects (curriedTensor A)).FullSubcategory) ⟶
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K ⊗ L), hKL⟩)) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app (K ⊗ L)) =
      DerivedCategory.Qh.map (((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K ⊗ₘ
          (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L) ≫
        (homotopyMu B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L)) := by
  let := kFlatLiftMonoidal F hF
  change DerivedCategory.Qh.map (@Functor.LaxMonoidal.μ _ _ _ _ _ _
      (F.mapHomotopyCategory (ComplexShape.up ℤ)) (mapHomotopyCategoryMonoidal F).toLaxMonoidal
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (𝟙 _)) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
      (homotopyMu A K L).hom) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app (K ⊗ L)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id, mapHomotopyCategoryMonoidal_μ,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  exact congrArg (_ ≫ _ ≫ ·) (Category.comp_id _)

/-- The tensorator of `derivedFunctorMonoidal` at the images of the classes of two K-flat
complexes, in the `Qh`-spelling: through `e`, `Functor.mapHomotopyCategoryFactors` and the
tensorators of the two K-flat localizations it is the image of the tensorator of `F` on
complexes. -/
lemma derivedFunctorMonoidal_μ_kFlatQ {K L : CochainComplex A ℤ}
    (hK : kFlatObjects (curriedTensor A) ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
    (hL : kFlatObjects (curriedTensor A) ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L))
    (hKL : kFlatObjects (curriedTensor A)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K ⊗ L)))
    (hFK : kFlatObjects (curriedTensor B) ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    (hFL : kFlatObjects (curriedTensor B) ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))) :
    letI := kFlatQ_isLocalization (curriedTensor A) hresA
    letI := kFlatQ_isLocalization (curriedTensor B) hresB
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    letI := derivedFunctorMonoidal F hF hresA hresB Φ e
    Functor.LaxMonoidal.μ Φ
        ((kFlatQ (curriedTensor A)).obj
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩)
        ((kFlatQ (curriedTensor A)).obj
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩) ≫
      Φ.map (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩).hom ≫
      Φ.map (DerivedCategory.Qh.map (homotopyMu A K L).hom) ≫
      e.hom.app ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K ⊗ L), hKL⟩ ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app (K ⊗ L)) =
    ((e.hom.app ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ≫
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K)) ⊗ₘ
        (e.hom.app ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ ≫
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L))) ≫
      (Localization.Monoidal.μ (kFlatQ (curriedTensor B)) (kFlatQuasiIso (curriedTensor B))
          (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _)))
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K), hFK⟩
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L), hFL⟩).hom ≫
      DerivedCategory.Qh.map (homotopyMu B _ _).hom ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L)) := by
  let := kFlatQ_isLocalization (curriedTensor A) hresA
  let := kFlatQ_isLocalization (curriedTensor B) hresB
  let := derivedMonoidal A hresA
  let := derivedMonoidal B hresB
  let := derivedFunctorMonoidal F hF hresA hresB Φ e
  let := kFlatLiftMonoidal F hF
  let X : (kFlatObjects (curriedTensor A)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
  let Y : (kFlatObjects (curriedTensor A)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩
  let Z : (kFlatObjects (curriedTensor A)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K ⊗ L), hKL⟩
  let m : X ⊗ Y ⟶ Z := ObjectProperty.homMk (homotopyMu A K L).hom
  have hb : e.inv.app (X ⊗ Y) ≫ Φ.map (DerivedCategory.Qh.map (homotopyMu A K L).hom) ≫
      e.hom.app Z = (kFlatQ (curriedTensor B)).map ((kFlatLift F hF).map m) :=
    (congrArg (e.inv.app (X ⊗ Y) ≫ ·) (e.hom.naturality m)).trans
      (Iso.inv_hom_id_app_assoc e (X ⊗ Y) _)
  have hc := kFlatQ_map_kFlatLift_μ_comp_homotopyMu F hF hK hL hKL
  let X'' : (kFlatObjects (curriedTensor B)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K), hFK⟩
  let Y'' : (kFlatObjects (curriedTensor B)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L), hFL⟩
  let fK : (kFlatLift F hF).obj X ⟶ X'' :=
    ObjectProperty.homMk ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K)
  let fL : (kFlatLift F hF).obj Y ⟶ Y'' :=
    ObjectProperty.homMk ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L)
  have hd := Functor.LaxMonoidal.μ_natural (Localization.Monoidal.toMonoidalCategory
    (kFlatQ (curriedTensor B)) (kFlatQuasiIso (curriedTensor B))
    (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _)))) fK fL
  exact comp_eq_of_μ (derivedFunctorMonoidal_μ F hF hresA hresB Φ e X Y)
    (Φ.mapIso _).inv_hom_id hb hc
    ((Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _))) hd.symm
    (tensorHom_comp_tensorHom _ _ _ _)

/-- The bookkeeping behind `derivedFunctorMonoidal_μ_comp_derivedFunctorQComparison`, in an
arbitrary category. -/
private lemma comp_eq_of_μ_kFlatQ {C : Type*} [Category C]
    {S S' T T' R N₁ N₂ N₃ M₁ M₂ W W₂ W₃ W₄ V : C}
    {μQ : S ⟶ T} {d : T ⟶ T'} {p : T' ⟶ R} {n : T ⟶ N₁} {ma : N₁ ⟶ N₂} {mh : N₂ ⟶ N₃}
    {ak : N₃ ⟶ T'} {ak' : T' ⟶ N₃} {ez : N₃ ⟶ M₁} {fz : M₁ ⟶ M₂} {bz : M₂ ⟶ R}
    {m : S ⟶ S'} {μh : S' ⟶ N₁} {t : S' ⟶ W} {μB : W ⟶ W₂} {g : W₂ ⟶ W₃} {q : W₃ ⟶ M₂}
    {b' : W₃ ⟶ W₄} {qμ : W₄ ⟶ R} {pt : S ⟶ V} {dB : V ⟶ W₄} {binv : V ⟶ W}
    (hd : d = n ≫ ma ≫ mh ≫ ak) (hp : p = ak' ≫ ez ≫ fz ≫ bz) (hak : ak ≫ ak' = 𝟙 N₃)
    (hnat : μQ ≫ n = m ≫ μh) (h₁ : μh ≫ ma ≫ mh ≫ ez ≫ fz = t ≫ μB ≫ g ≫ q)
    (hq : q ≫ bz = b' ≫ qμ) (hdB : dB = binv ≫ μB ≫ g ≫ b') (htens : pt ≫ binv = m ≫ t) :
    μQ ≫ d ≫ p = pt ≫ dB ≫ qμ := by
  rw [hd, hp, hdB]
  simp only [Category.assoc]
  rw [reassoc_of% hak, reassoc_of% hnat, reassoc_of% h₁, hq, reassoc_of% htens]

/-- The comparison `Φ(QK) ⟶ Q(FK)` at a K-flat complex `K`, read off from `e` through the
`Q` versus `Qh ∘ quotient` bridges. -/
def derivedFunctorQComparison {K : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K) :
    Φ.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Φ.map (derivedQIso A K).inv ≫
    e.hom.app ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
    (derivedQIso B _).hom

/-- The comparison `Φ(QK) ⟶ Q(FK)` is an isomorphism. -/
instance isIso_derivedFunctorQComparison {K : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K) :
    IsIso (derivedFunctorQComparison F hF Φ e hK) :=
  IsIso.comp_isIso' (Iso.isIso_hom (Φ.mapIso (derivedQIso A K).symm))
    (IsIso.comp_isIso' (Iso.isIso_hom (e.app _))
      (IsIso.comp_isIso' (Iso.isIso_hom (DerivedCategory.Qh.mapIso
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K))) (Iso.isIso_hom _)))

/-- **The tensorator of `derivedFunctorMonoidal` on K-flat complexes**: through the comparisons
`derivedFunctorQComparison` and `derivedTensorIso`, it is the image under `Q` of the
tensorator of `F` on complexes. -/
theorem derivedFunctorMonoidal_μ_comp_derivedFunctorQComparison {K L : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K)
    (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    letI := derivedFunctorMonoidal F hF hresA hresB Φ e
    Functor.LaxMonoidal.μ Φ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        Φ.map (derivedTensorIso A hresA hK hL).hom ≫
        derivedFunctorQComparison F hF Φ e (kFlat_tensor A hK hL) =
      (derivedFunctorQComparison F hF Φ e hK ⊗ₘ derivedFunctorQComparison F hF Φ e hL) ≫
        (derivedTensorIso B hresB (hF K hK) (hF L hL)).hom ≫
        DerivedCategory.Q.map
          (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L) := by
  let := kFlatQ_isLocalization (curriedTensor A) hresA
  let := kFlatQ_isLocalization (curriedTensor B) hresB
  let := derivedMonoidal A hresA
  let := derivedMonoidal B hresB
  let := derivedFunctorMonoidal F hF hresA hresB Φ e
  have h₁ := derivedFunctorMonoidal_μ_kFlatQ F hF hresA hresB Φ e hK hL (kFlat_tensor A hK hL)
    (hF K hK) (hF L hL)
  have hnat := Functor.LaxMonoidal.μ_natural Φ (derivedQIso A K).inv (derivedQIso A L).inv
  have hq := (DerivedCategory.quotientCompQhIso B).hom.naturality
    (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L)
  refine comp_eq_of_μ_kFlatQ (binv := (derivedQIso B _).inv ⊗ₘ (derivedQIso B _).inv) ?_ rfl
    (congrArg Φ.map (derivedQIso A (K ⊗ L)).hom_inv_id |>.trans (Φ.map_id _) |>.symm |>.trans
      (Φ.map_comp _ _)).symm hnat.symm h₁ hq ?_ ?_
  · exact (Φ.map_comp _ _).trans (congrArg (_ ≫ ·) ((Φ.map_comp _ _).trans
      (congrArg (_ ≫ ·) (Φ.map_comp _ _))))
  · rfl
  · rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1 <;> simp [derivedFunctorQComparison]

/-- The bookkeeping behind `derivedFunctorMonoidal_ε_comp_derivedFunctorQComparison`. -/
private lemma comp_eq_of_ε {C : Type*} [Category C] {S T U V W : C} {x : S ⟶ U} {m : S ⟶ T}
    {mi : T ⟶ U} {ei : U ⟶ V} {eh : V ⟶ U} {mh : U ⟶ T} {d : T ⟶ W} {r : S ⟶ W}
    (hx : x = m ≫ mi) (he : ei ≫ eh = 𝟙 U) (hm : mi ≫ mh = 𝟙 T) (hd : m ≫ d = r) :
    (x ≫ ei) ≫ eh ≫ mh ≫ d = r := by
  rw [hx, Category.assoc, Category.assoc, reassoc_of% he, reassoc_of% hm, hd]

/-- **The unit of `derivedFunctorMonoidal` on the unit complex**: through the comparisons
`derivedUnitIso` and `derivedFunctorQComparison`, it is the image under `Q` of the unit of `F` on
complexes. -/
theorem derivedFunctorMonoidal_ε_comp_derivedFunctorQComparison :
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    letI := derivedFunctorMonoidal F hF hresA hresB Φ e
    Functor.LaxMonoidal.ε Φ ≫ Φ.map (derivedUnitIso A hresA).hom ≫
        derivedFunctorQComparison F hF Φ e (kFlat_tensorUnit A) =
      (derivedUnitIso B hresB).hom ≫
        DerivedCategory.Q.map
          (Functor.LaxMonoidal.ε (F.mapHomologicalComplex (ComplexShape.up ℤ))) := by
  let := derivedMonoidal A hresA
  let := derivedMonoidal B hresB
  let := derivedFunctorMonoidal F hF hresA hresB Φ e
  rw [derivedFunctorMonoidal_ε, mapHomotopyCategoryMonoidal_ε]
  have h₁ : (derivedUnitIso A hresA).hom ≫ (derivedQIso A (𝟙_ (CochainComplex A ℤ))).inv = 𝟙 _ :=
    Iso.hom_inv_id _
  have h₂ := Iso.inv_hom_id_app e (𝟙_ (kFlatObjects (curriedTensor A)).FullSubcategory)
  have h₃ := (DerivedCategory.quotientCompQhIso B).hom.naturality
    (Functor.LaxMonoidal.ε (F.mapHomologicalComplex (ComplexShape.up ℤ)))
  simp only [derivedFunctorQComparison, ← Φ.map_comp_assoc, h₁,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact comp_eq_of_ε (DerivedCategory.Qh.map_comp _ _) h₂
    ((DerivedCategory.Qh.map_comp _ _).symm.trans ((congrArg DerivedCategory.Qh.map
      (Iso.inv_hom_id_app _ _)).trans (DerivedCategory.Qh.map_id _))) h₃

/-- The bookkeeping behind `reseatFunctorMonoidal_δ_comp_derivedFunctorQComparison`, in an
arbitrary category. -/
private lemma comp_eq_of_δ {C : Type*} [Category C] {S S₁ S₂ T T₁ T₂ T₃ T₄ V W : C}
    {a₁ : S ⟶ S₁} {a₂ : S₁ ⟶ S₂} {a₃ : S₂ ⟶ S₁} {δ : S₂ ⟶ T} {μ : T ⟶ S₂} {r : T ⟶ T₁}
    {n₁ : T₁ ⟶ T₃} {n₂ : T₃ ⟶ T₂} {c : T₂ ⟶ W} {ci : W ⟶ T₂} {t : T ⟶ T₄} {d : T₄ ⟶ W}
    {p : S₁ ⟶ V} {q : W ⟶ V} {q' : V ⟶ W} {res : S ⟶ S₂}
    (hres : res = a₁ ≫ a₂) (h₂₃ : a₂ ≫ a₃ = 𝟙 S₁) (hδ : δ ≫ μ = 𝟙 S₂) (hc : ci ≫ c = 𝟙 W)
    (hq : q ≫ q' = 𝟙 W) (hr : r ≫ n₁ ≫ n₂ = t ≫ d ≫ ci) (h₁ : μ ≫ a₃ ≫ p = t ≫ d ≫ q) :
    res ≫ δ ≫ r ≫ n₁ ≫ n₂ ≫ c = a₁ ≫ p ≫ q' := by
  have h : δ ≫ t ≫ d = a₃ ≫ p ≫ q' := by
    calc δ ≫ t ≫ d = δ ≫ t ≫ d ≫ q ≫ q' := by rw [hq, Category.comp_id]
      _ = δ ≫ μ ≫ a₃ ≫ p ≫ q' := by rw [reassoc_of% h₁]
      _ = a₃ ≫ p ≫ q' := by rw [reassoc_of% hδ]
  rw [hres, Category.assoc, reassoc_of% hr, hc, Category.comp_id, h, reassoc_of% h₂₃]

/-- **The tensorator of a re-seated derived monoidal functor on K-flat complexes.** Re-seat the
monoidal structures of `D(A)` and `D(B)` along isomorphisms `eA : ⊗ ≅ T_A`, `eB : ⊗ ≅ T_B` which on
pairs of K-flat complexes are `derivedTensorIso` followed by the inverse of given comparisons
`cA K L : T_A(QK, QL) ≅ Q(K ⊗ L)`, `cB`. Then the oplax tensorator of `Φ` for the re-seated
structures, followed by the comparisons `derivedFunctorQComparison` and `cB`, is `cA` followed by
the comparison `Φ(Q(K ⊗ L)) ⟶ Q(F(K ⊗ L))` and the image of the oplax tensorator of `F` on
complexes. -/
theorem reseatFunctorMonoidal_δ_comp_derivedFunctorQComparison
    (TA : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (TB : DerivedCategory B ⥤ DerivedCategory B ⥤ DerivedCategory B)
    (UA : DerivedCategory A) (UB : DerivedCategory B)
    (eA : @curriedTensor (DerivedCategory A) _ (derivedMonoidal A hresA) ≅ TA)
    (εA : @MonoidalCategoryStruct.tensorUnit _ _
      (derivedMonoidal A hresA).toMonoidalCategoryStruct ≅ UA)
    (eB : @curriedTensor (DerivedCategory B) _ (derivedMonoidal B hresB) ≅ TB)
    (εB : @MonoidalCategoryStruct.tensorUnit _ _
      (derivedMonoidal B hresB).toMonoidalCategoryStruct ≅ UB)
    (cA : ∀ (K L : CochainComplex A ℤ),
      _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K →
      _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L →
      ((TA.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
        DerivedCategory.Q.obj (K ⊗ L)))
    (cB : ∀ (K L : CochainComplex B ℤ),
      _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) K →
      _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) L →
      ((TB.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
        DerivedCategory.Q.obj (K ⊗ L)))
    (heA : ∀ (K L : CochainComplex A ℤ)
      (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K)
      (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L),
      (eA.inv.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
        (cA K L hK hL).hom ≫ (derivedTensorIso A hresA hK hL).inv)
    (heB : ∀ (K L : CochainComplex B ℤ)
      (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) K)
      (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) L),
      (eB.hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
        (derivedTensorIso B hresB hK hL).hom ≫ (cB K L hK hL).inv)
    {K L : CochainComplex A ℤ}
    (hK : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K)
    (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L) :
    @Functor.OplaxMonoidal.δ _ _ (@reseat _ _ (derivedMonoidal A hresA) TA UA eA εA) _ _
        (@reseat _ _ (derivedMonoidal B hresB) TB UB eB εB) Φ
        (@reseatFunctorMonoidal _ _ (derivedMonoidal A hresA) TA UA _ _ (derivedMonoidal B hresB)
          TB UB Φ (derivedFunctorMonoidal F hF hresA hresB Φ e) eA εA eB εB).toOplaxMonoidal
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
      (TB.map (derivedFunctorQComparison F hF Φ e hK)).app _ ≫
      (TB.obj _).map (derivedFunctorQComparison F hF Φ e hL) ≫
      (cB _ _ (hF K hK) (hF L hL)).hom =
    Φ.map (cA K L hK hL).hom ≫ derivedFunctorQComparison F hF Φ e (kFlat_tensor A hK hL) ≫
      DerivedCategory.Q.map
        (Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L) := by
  let := derivedMonoidal A hresA
  let := derivedMonoidal B hresB
  let := derivedFunctorMonoidal F hF hresA hresB Φ e
  have hres := (congrArg Φ.map (heA K L hK hL)).trans (Φ.map_comp _ _)
  have hr := (MonoidalCategory.reseatIso_naturality_left_assoc eB
      (derivedFunctorQComparison F hF Φ e hK) _ _).symm.trans
    ((congrArg (_ ≫ ·) (MonoidalCategory.reseatIso_naturality_right eB _
      (derivedFunctorQComparison F hF Φ e hL)).symm).trans
      ((MonoidalCategory.tensorHom_def_assoc _ _ _).symm.trans
        (congrArg (_ ≫ ·) (heB _ _ (hF K hK) (hF L hL)))))
  have hq : DerivedCategory.Q.map
        (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L) ≫
      DerivedCategory.Q.map
        (Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L) = 𝟙 _ := by
    rw [← Functor.map_comp, Functor.Monoidal.μ_δ, CategoryTheory.Functor.map_id]
  refine (congrArg (· ≫ _) (@MonoidalCategory.reseatFunctorMonoidal_δ _ _ _ TA UA _ _ _ TB UB Φ _
    eA εA eB εB (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_))
  exact comp_eq_of_δ hres (Φ.mapIso _).inv_hom_id (Functor.Monoidal.δ_μ _ _ _) (Iso.inv_hom_id _)
    hq hr (derivedFunctorMonoidal_μ_comp_derivedFunctorQComparison F hF hresA hresB Φ e hK hL)

/-- **The unit of a re-seated derived monoidal functor on the unit complex**: if the units of
`D(A)` and `D(B)` are re-seated along `derivedUnitIso`, the lax unit of `Φ` followed by the
comparison `Φ(Q 𝟙) ⟶ Q(F 𝟙)` is the image under `Q` of the unit of `F` on complexes. -/
theorem reseatFunctorMonoidal_ε_comp_derivedFunctorQComparison
    (TA : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (TB : DerivedCategory B ⥤ DerivedCategory B ⥤ DerivedCategory B)
    (eA : @curriedTensor (DerivedCategory A) _ (derivedMonoidal A hresA) ≅ TA)
    (eB : @curriedTensor (DerivedCategory B) _ (derivedMonoidal B hresB) ≅ TB) :
    @Functor.LaxMonoidal.ε _ _
        (@reseat _ _ (derivedMonoidal A hresA) TA _ eA (derivedUnitIso A hresA)) _ _
        (@reseat _ _ (derivedMonoidal B hresB) TB _ eB (derivedUnitIso B hresB)) Φ
        (@reseatFunctorMonoidal _ _ (derivedMonoidal A hresA) TA _ _ _ (derivedMonoidal B hresB)
          TB _ Φ (derivedFunctorMonoidal F hF hresA hresB Φ e) eA (derivedUnitIso A hresA) eB
          (derivedUnitIso B hresB)).toLaxMonoidal ≫
      derivedFunctorQComparison F hF Φ e (kFlat_tensorUnit A) =
    DerivedCategory.Q.map
      (Functor.LaxMonoidal.ε (F.mapHomologicalComplex (ComplexShape.up ℤ))) := by
  let := derivedMonoidal A hresA
  let := derivedMonoidal B hresB
  let := derivedFunctorMonoidal F hF hresA hresB Φ e
  rw [@MonoidalCategory.reseatFunctorMonoidal_ε _ _ _ TA _ _ _ _ TB _ Φ _ eA _ eB _,
    Category.assoc, Category.assoc, derivedFunctorMonoidal_ε_comp_derivedFunctorQComparison,
    Iso.inv_hom_id_assoc]

end CochainComplex.KFlatMonoidal
