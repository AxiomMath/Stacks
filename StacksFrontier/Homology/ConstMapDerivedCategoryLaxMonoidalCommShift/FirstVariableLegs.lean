module

public import StacksFrontier.Homology.ConstMapDerivedCategoryTensoratorCommShift

/-!
# The tensorator of the derived constant diagram commutes with the shift

Let `J` be a category and `D` a monoidal abelian category over which both `CochainComplex D ℤ` and
`CochainComplex (J ⥤ D) ℤ` carry the total tensor product and admit K-flat resolutions, so that
`CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(D)` and `D(J ⥤ D)` with the derived
tensor product and `CategoryTheory.Functor.constMapDerivedCategoryMonoidal` makes

`π^{-1} := (Functor.const J).mapDerivedCategory : D(D) ⥤ D(J ⥤ D)`

a monoidal functor.  This file proves that its tensorator

`μ : π^{-1}K ⊗^L π^{-1}L ⟶ π^{-1}(K ⊗^L L)`

commutes with the shift in each variable, i.e. `CategoryTheory.Functor.LaxMonoidal.CommShift`.

That is a condition on the monoidal structure and not a consequence of it; it is the hypothesis
`hμ` of `Stacks.CategoryHomology.commShift_externalMateNatTransFst_derivedExternalTensor`, and
hence the shift-compatibility input a dévissage of the comparison of [Stacks, Tag 08QB] along the
compact generators consumes.

## Main results

* `CategoryTheory.commShift_muNatTransFst_constMapDerivedCategory_kFlat` and
  `commShift_muNatTransSnd_constMapDerivedCategory_kFlat`: **each one-variable reading of the
  tensorator, restricted along the K-flat complexes, commutes with the shift.**
* `CategoryTheory.constMapDerivedCategoryLaxMonoidalCommShift`: **the tensorator commutes with
  the shift**, by `CategoryTheory.Functor.LaxMonoidal.CommShift.of_essSurj` along
  `CochainComplex.KFlatBifunctor.kFlatComplexQ`, which is essentially surjective.

## Implementation notes

**Why the proof is a chain of reassociations.**  The value of the tensorator is computable only at
the image of a pair of K-flat complexes, where
`CategoryTheory.Functor.mu_constMapDerivedCategory_eq` expresses it as a six-fold composite: the
comparison `CategoryTheory.Functor.mapDerivedCategoryFactors` in each variable, the K-flat
comparison `CochainComplex.KFlatMonoidal.derivedTensorIso` over `J ⥤ D`, the image of the
tensorator of the degreewise functor, and the two previous ones again over `D`.  Each of those six
is shift-compatible for a reason of its own, but as *one-variable* transformations they live
between functors presented with different nestings of `CategoryTheory.Functor.comp` and, at the
K-flat comparison, over the full subcategory of (left) K-flat complexes rather than over the
complexes.  `CategoryTheory.NatTrans.CommShift` is a statement about a *chosen* pair of
`CategoryTheory.Functor.CommShift` data, so the chain has to be written with every reassociation
spelled out as a `CategoryTheory.Functor.associator` and every change of presentation as the
comparison `CategoryTheory.ObjectProperty.liftCompιIso` (resp.
`CategoryTheory.ObjectProperty.ιOfLECompιIso`), whose shift-compatibility is
`CategoryTheory.Functor.CommShift.ofComp_compatibility`.  The two data a junction of the chain
delivers and demands are then the same structure spelled two ways, and
`CategoryTheory.NatTrans.commShift_comp_of_eq_data` joins them.

A bridge is unavoidable rather than cosmetic: `Functor.constKFlatComplexLiftLeft ⋙ ι` and
`ι ⋙ (Functor.const J).mapHomologicalComplex _` are equal functors, by `rfl`, but their
commutation data are *not* definitionally equal -- the first is
`CategoryTheory.Functor.CommShift.ofComp`, which transports through a fully faithful functor,
and the second is `CategoryTheory.Functor.CommShift.comp`.

**Why the chain is cut into legs.**  The first variable's chain has twenty-six factors and the
second's twenty-one; a single declaration containing one of them, together with its factors'
compatibilities, exceeds Lean's default elaboration budget.  Each leg is therefore its own
private lemma, the identity blocks are their own, and the composite is assembled from them.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v u v₁ u₁ v₂ u₂

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]
  [SymmetricCategory (CochainComplex D ℤ)] [SymmetricCategory (CochainComplex (J ⥤ D) ℤ)]
  [HasDerivedCategory.{w} D] [HasDerivedCategory.{w'} (J ⥤ D)]
  (hresD : ∀ G : CochainComplex D ℤ, ∃ (P : CochainComplex D ℤ) (f : P ⟶ G),
    KFlat (curriedTensor D) P ∧ QuasiIso f)
  (hresJD : ∀ G : CochainComplex (J ⥤ D) ℤ, ∃ (P : CochainComplex (J ⥤ D) ℤ) (f : P ⟶ G),
    KFlat (curriedTensor (J ⥤ D)) P ∧ QuasiIso f)


/-- A twofold composite of identities. -/
lemma idComp2 {C : Type*} [Category* C] {X : C} {f g : X ⟶ X}
    (hf : f = 𝟙 X) (hg : g = 𝟙 X) : f ≫ g = 𝟙 X := by rw [hf, hg, Category.id_comp]

/-- A fourfold composite of identities. -/
lemma idComp4 {C : Type*} [Category* C] {X : C} {f g h k : X ⟶ X}
    (hf : f = 𝟙 X) (hg : g = 𝟙 X) (hh : h = 𝟙 X) (hk : k = 𝟙 X) :
    f ≫ g ≫ h ≫ k = 𝟙 X := by rw [hf, hg, hh, hk]; simp

/-- A fivefold composite of identities. -/
lemma idComp5 {C : Type*} [Category* C] {X : C} {f g h k l : X ⟶ X}
    (hf : f = 𝟙 X) (hg : g = 𝟙 X) (hh : h = 𝟙 X) (hk : k = 𝟙 X) (hl : l = 𝟙 X) :
    f ≫ g ≫ h ≫ k ≫ l = 𝟙 X := by rw [hf, hg, hh, hk, hl]; simp

/-- Replacing the identity reassociations of a twelve-fold composite. -/
lemma chainCongr {C : Type*} [Category* C] {Z₀ Z₁ Z₂ Z₃ Z₄ Z₅ Z₆ : C}
    {p : Z₀ ⟶ Z₀} {A : Z₀ ⟶ Z₁} {B : Z₁ ⟶ Z₂} {q : Z₂ ⟶ Z₂} {c c' : Z₂ ⟶ Z₃}
    {rr : Z₃ ⟶ Z₃} {d : Z₃ ⟶ Z₄} {ss : Z₄ ⟶ Z₄} {e : Z₄ ⟶ Z₅} {tt : Z₅ ⟶ Z₅}
    {f f' : Z₅ ⟶ Z₆} {uu : Z₆ ⟶ Z₆} {m : Z₀ ⟶ Z₆}
    (hp : p = 𝟙 Z₀) (hq : q = 𝟙 Z₂) (hr : rr = 𝟙 Z₃) (hs : ss = 𝟙 Z₄) (ht : tt = 𝟙 Z₅)
    (hu : uu = 𝟙 Z₆) (hc : c = c') (hf : f = f')
    (h : m = A ≫ B ≫ c' ≫ d ≫ e ≫ f') :
    m = p ≫ A ≫ B ≫ q ≫ c ≫ rr ≫ d ≫ ss ≫ e ≫ tt ≫ f ≫ uu := by
  rw [hp, hq, hr, hs, ht, hu, hc, hf]
  simpa using h

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst1
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      (((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L))))).hom) ≫
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L)))).inv)) ℤ := by
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst2
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L)))))) ℤ := by
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst3
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))
          ((curriedTensor (DerivedCategory (J ⥤ D))).flip.map
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom.app L.obj))))) ℤ := by
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst4
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (DerivedCategory.Q (C := J ⥤ D))
          (tensorRight ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj)))).hom) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj))))).inv) ≫
      (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).inv
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))) ≫
      ((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
          ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj))))).hom) ≫
      (Functor.whiskerLeft (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (Functor.associator (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
          (DerivedCategory.Q (C := J ⥤ D)) (tensorRight
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj)))).inv)) ℤ := by
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  exact NatTrans.commShift_comp_of_eq_data _ _ (inferInstance : NatTrans.CommShift _ ℤ)
    (NatTrans.commShift_comp_of_eq_data _ _ (inferInstance : NatTrans.CommShift _ ℤ)
    (NatTrans.commShift_comp_of_eq_data _ _ (inferInstance : NatTrans.CommShift _ ℤ)
    (NatTrans.commShift_comp_of_eq_data _ _
      (inferInstance : NatTrans.CommShift (Functor.associator _ _ _).hom ℤ)
      (inferInstance : NatTrans.CommShift _ ℤ))))

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst5
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (derivedTensorFirstIso (J ⥤ D) hresJD
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
          (kFlat_constMapHomologicalComplex L.obj L.property)).hom)) ℤ := by
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  have := derivedTensorFirstIso_commShift (J ⥤ D) hresJD
    (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
    (kFlat_constMapHomologicalComplex L.obj L.property)
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst6
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      (((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
          ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).inv) ≫
      (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom
              ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).hom) ≫
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv)) ℤ := by
  let := derivedMonoidal D hresD
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  exact NatTrans.commShift_comp_of_eq_data _ _
    (inferInstance : NatTrans.CommShift (Functor.associator _ _ _).inv ℤ)
    (NatTrans.commShift_comp_of_eq_data _ _
    (inferInstance : NatTrans.CommShift (Functor.whiskerRight _ _) ℤ)
    (NatTrans.commShift_comp_of_eq_data _ _
    (inferInstance : NatTrans.CommShift (Functor.associator _ _ _).hom ℤ)
      (inferInstance : NatTrans.CommShift _ ℤ)))

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst7
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight (Functor.LaxMonoidal.μNatTransFst
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)) L.obj)
          (DerivedCategory.Q (C := J ⥤ D))))) ℤ := by
  let := derivedMonoidal D hresD
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst8
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorRight L.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q (C := J ⥤ D))).hom)) ℤ := by
  let := derivedMonoidal D hresD
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst9
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (tensorRight L.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).inv))) ℤ := by
  let := derivedMonoidal D hresD
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst10
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorRight L.obj) (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
      (Functor.whiskerRight (Functor.whiskerRight (ObjectProperty.ιOfLECompιIso hle).inv
          ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D))))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
          (kFlatComplexesLeft (curriedTensor D)).ι ((tensorRight L.obj) ⋙
          (DerivedCategory.Q (C := D)))).hom ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)))
          ℤ := by
  let := derivedMonoidal D hresD
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  have : NatTrans.CommShift (ObjectProperty.ιOfLECompιIso hle).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst11
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerRight (Functor.whiskerLeft (ObjectProperty.ιOfLE hle)
          (derivedTensorFirstIso D hresD L.obj L.property).inv)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))) ℤ := by
  let := derivedMonoidal D hresD
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  have := derivedTensorFirstIso_commShift D hresD L.obj L.property
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
theorem legFst12
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
          ((kFlatComplexesLeft (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))).inv
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      (Functor.whiskerRight (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
          (kFlatComplexesLeft (curriedTensor D)).ι (DerivedCategory.Q (C := D))).inv
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerRight
          (ObjectProperty.ιOfLECompιIso hle).hom (DerivedCategory.Q (C := D)))
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      ((Functor.associator ((kFlatComplexes (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).hom)) ℤ := by
  let := derivedMonoidal D hresD
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  have : NatTrans.CommShift (ObjectProperty.ιOfLECompιIso hle).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  infer_instance

end CategoryTheory

end
