module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DualityUnitName
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoidDuality
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateCoherence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The name of a correspondence in the category of Chow motives

Let `X`, `Y` be smooth projective over `k`, equidimensional of dimensions `d` and `e`. Under the
self-duality `h(X)^∨ = h(X) ⊗ 𝟏(d)` of Stacks 0FGI, the name of a morphism `f : h(X) ⟶ h(Y)`
whose correspondence is `1 ⊗ α` for an integral class `α ∈ CH_e(X × Y)` is the morphism
`𝟏(-d) ⟶ h(X × Y)` of the class of `α` in `CH^d(X × Y)`, transported along
`h(X) ⊗ h(Y) ≅ h(X × Y)`. This is the motive-level form of
`Stacks.WeilCohomology.dualityUnit_comp_whiskerLeft_of_eq_pointCorrEquiv`, used in Stacks 0FHM.

## Main results

* `Stacks.WeilCohomology.coevaluationOfObjTensorTwist_comp_whiskerLeft`: the name of `f ▷ T(d)`
  under the duality of `(X, 𝟙, 0)` with `(X, 𝟙, 0) ⊗ T(d)`, in a general graded category.
* `Stacks.WeilCohomology.coevaluation_whiskerLeft_whiskerRight_eq`: the name of a
  correspondence in `M_k`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CategoryTheory.GradedCategory

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- The monoidal rearrangement behind the name of a correspondence: for `η' : 𝟙 ⟶ X ⊗ X` and
`c : X ⟶ Y` with `η' ≫ X ◁ c = P`,
`(η' ≫ X ◁ ρ⁻¹) ≫ (1 ⊗ (c ⊗ 1)) = ρ⁻¹ ≫ (P ⊗ 1) ≫ α`. -/
theorem MonoidalCategory.coevaluation_whiskerLeft_rightUnitor {C : Type*} [Category C]
    [MonoidalCategory C] {X Y : C} (η' : 𝟙_ C ⟶ X ⊗ X) (c : X ⟶ Y) (P : 𝟙_ C ⟶ X ⊗ Y)
    (h : η' ≫ X ◁ c = P) :
    (η' ≫ X ◁ (ρ_ X).inv) ≫ (𝟙 X ⊗ₘ (c ⊗ₘ 𝟙 (𝟙_ C))) =
      (ρ_ (𝟙_ C)).inv ≫ (P ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ X Y (𝟙_ C)).hom := by
  rw [id_tensorHom, tensorHom_id, tensorHom_id, ← h, ← rightUnitor_inv_naturality_assoc,
    rightUnitor_tensor_inv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← MonoidalCategory.whiskerLeft_comp, ← rightUnitor_inv_naturality,
    MonoidalCategory.whiskerLeft_comp]

/-- The underlying morphism of the inverse of `T(n) ⊗ T(m) ≅ T(p)` is `ρ⁻¹ : 𝟙 ⟶ 𝟙 ⊗ 𝟙`. -/
theorem TwistedKaroubi.unitTwistTensorIsoOfEq_inv_val {R : Type*} [Ring R] {C : Type*}
    [Category C] [Preadditive C] [GradedCategory R C] [MonoidalCategory C]
    [IsGradedMonoidal R C] (n m p : ℤ) (h : n + m = p) :
    (TwistedKaroubi.unitTwistTensorIsoOfEq (R := R) (C := C) n m p h).inv.val =
      (ρ_ (𝟙_ C)).inv := by
  have e : (TwistedKaroubi.unitTwistTensorIsoOfEq (R := R) (C := C) n m p h).hom.val ≫
      (TwistedKaroubi.unitTwistTensorIsoOfEq (R := R) (C := C) n m p h).inv.val =
        𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C) :=
    congrArg (fun f ↦ f.val)
      (TwistedKaroubi.unitTwistTensorIsoOfEq (R := R) (C := C) n m p h).hom_inv_id
  rw [TwistedKaroubi.unitTwistTensorIsoOfEq_hom_val, id_tensorHom_id] at e
  exact (cancel_epi (ρ_ (𝟙_ C)).hom).1 (e.trans (Iso.hom_inv_id _).symm)

section Generic

open TwistedKaroubi

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

attribute [-instance] TwistedKaroubi.monoidalCategoryStruct

variable (R C) in
/-- The morphism `𝟙 = T(0) ⟶ T(-d) ⊗ T(d)` with underlying morphism `ρ⁻¹ : 𝟙 ⟶ 𝟙 ⊗ 𝟙`. -/
def unitTwistNegTensorHom (d : ℤ) :
    𝟙_ (TwistedKaroubi R C) ⟶ tateTriple R C (-d) ⊗ tateTriple R C d :=
  ofComm (ρ_ (𝟙_ C)).inv
    (grade_cast (IsGradedMonoidal.rightUnitor_inv_mem (R := R) (𝟙_ C)) (by
      change (0 : ℤ) = -d + d - 0
      ring)) (by
      change 𝟙 (𝟙_ C) ≫ (ρ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C))
      rw [id_tensorHom_id, Category.id_comp, Category.comp_id])

/-- The underlying morphism of `unitTwistNegTensorHom R C d` is `𝟙 ≫ ρ⁻¹ : 𝟙 ⟶ 𝟙 ⊗ 𝟙`. -/
theorem unitTwistNegTensorHom_val (d : ℤ) :
    (unitTwistNegTensorHom R C d).val = 𝟙 (𝟙_ C) ≫ (ρ_ (𝟙_ C)).inv :=
  rfl

/-- `T(0) ⟶ T(-d) ⊗ T(d)` is the inverse of `T(-d) ⊗ T(d) ≅ T(0)`. -/
theorem unitTwistNegTensorHom_eq_inv (d : ℤ) :
    unitTwistNegTensorHom R C d =
      (unitTwistTensorIsoOfEq (R := R) (C := C) (-d) d 0 (neg_add_cancel d)).inv := by
  apply hom_ext
  rw [unitTwistNegTensorHom_val, TwistedKaroubi.unitTwistTensorIsoOfEq_inv_val, Category.id_comp]

/-- **The name of a morphism `f : (X, 𝟙, 0) ⟶ (Y, 𝟙, 0)` under the duality of `(X, 𝟙, 0)` with
`(X, 𝟙, 0) ⊗ T(d)`.** If the name `η ≫ (X ◁ f)` in `C` is the underlying morphism of
`Q : T(-d) ⟶ (X, 𝟙, 0) ⊗ (Y, 𝟙, 0)`, then
`η ≫ (X, 𝟙, 0) ◁ (f ▷ T(d)) = (T(-d) ⊗ T(d) ≅ T(0))⁻¹ ≫ (Q ▷ T(d)) ≫ α`. -/
theorem coevaluationOfObjTensorTwist_comp_whiskerLeft (X Y : C) [ExactPairing X X] {d : ℤ}
    (hη : η_ X X ∈ grade (R := R) _ _ d) (hε : ε_ X X ∈ grade (R := R) _ _ (-d))
    (f : ofObj (R := R) X ⟶ ofObj (R := R) Y)
    (Q : tateTriple R C (-d) ⟶ ofObj (R := R) X ⊗ ofObj (R := R) Y)
    (hQ : η_ X X ≫ X ◁ f.val = Q.val) :
    letI := exactPairingOfObjTensorTwist (R := R) X hη hε
    η_ (ofObj (R := R) X) (ofObj (R := R) X ⊗ tateTriple R C d) ≫
        ofObj (R := R) X ◁ (f ▷ tateTriple R C d) =
      unitTwistNegTensorHom R C d ≫ (Q ▷ tateTriple R C d) ≫
        (α_ (ofObj (R := R) X) (ofObj (R := R) Y) (tateTriple R C d)).hom := by
  apply hom_ext
  rw [comp_val, comp_val, comp_val, whiskerLeft_val, whiskerRight_val, whiskerRight_val,
    associator_hom_val, unitTwistNegTensorHom_val]
  change (η_ X X ≫ X ◁ (ρ_ X).inv) ≫ (𝟙 X ⊗ₘ ((@id (X ⟶ Y) f.val) ⊗ₘ 𝟙 (𝟙_ C))) =
    (𝟙 (𝟙_ C) ≫ (ρ_ (𝟙_ C)).inv) ≫ ((@id (𝟙_ C ⟶ X ⊗ Y) Q.val) ⊗ₘ 𝟙 (𝟙_ C)) ≫
      (((𝟙 X ⊗ₘ 𝟙 Y) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ X Y (𝟙_ C)).hom)
  rw [id_tensorHom_id, id_tensorHom_id, Category.id_comp, Category.id_comp]
  exact MonoidalCategory.coevaluation_whiskerLeft_rightUnitor _ _ _ hQ

/-- `η ≫ X ◁ f = P ≫ c` in `C` gives `η ≫ X ◁ f = (P ≫ κ⁻¹).val` for an isomorphism `κ` of
triples equal to `(a ⊗ b) ≫ μ` with `((a ⊗ b) ≫ μ) ≫ c = 1`. -/
theorem coevaluation_whiskerLeft_eq_comp_inv_val_of_hom_eq {X Y P : C} [ExactPairing X X]
    [MonObj P] (hη : (MonObj.one : 𝟙_ C ⟶ P) ∈ grade (R := R) (𝟙_ C) P 0)
    (hμ : (MonObj.mul : P ⊗ P ⟶ P) ∈ grade (R := R) (P ⊗ P) P 0)
    (a : X ⟶ P) (ha : a ∈ grade (R := R) X P 0) (b : Y ⟶ P) (hb : b ∈ grade (R := R) Y P 0)
    (c : P ⟶ X ⊗ Y) (hc : c ∈ grade (R := R) P (X ⊗ Y) 0)
    (e₁ : ((a ⊗ₘ b) ≫ (MonObj.mul : P ⊗ P ⟶ P)) ≫ c = 𝟙 (X ⊗ Y))
    (f : ofObj (R := R) X ⟶ ofObj (R := R) Y)
    (κ : ofObj (R := R) X ⊗ ofObj (R := R) Y ≅ ofObj (R := R) P)
    (hκ : letI := monObjOfObj P hη hμ
      κ.hom = (ofObjHom a ha ⊗ₘ ofObjHom b hb) ≫
        (MonObj.mul : ofObj (R := R) P ⊗ ofObj (R := R) P ⟶ ofObj (R := R) P))
    {n : ℤ} (Pv : tateTriple R C n ⟶ ofObj (R := R) P)
    (hcore : η_ X X ≫ X ◁ f.val = Pv.val ≫ c) :
    η_ X X ≫ X ◁ f.val = (Pv ≫ κ.inv).val := by
  let _ := monObjOfObj P hη hμ
  let i : ofObj (R := R) P ⟶ ofObj (R := R) X ⊗ ofObj (R := R) Y :=
    Hom.mk c ⟨grade_cast hc (by simp), Category.id_comp _,
      (congrArg (c ≫ ·) (id_tensorHom_id X Y)).trans (Category.comp_id c)⟩
  have hh : κ.hom ≫ i = 𝟙 _ := by
    rw [hκ]
    exact hom_ext (e₁.trans (id_tensorHom_id X Y).symm)
  rwa [(cancel_epi κ.hom).1 (κ.hom_inv_id.trans hh.symm)]

end Generic

/-- Transport of the correspondence of a class read in codimension `i` along `i = i'`. -/
theorem of_pointCorrEquiv_codimensionToCodimChow_congr
    (Z : (SmoothProjectiveScheme k).FullSubcategory)
    {l i i' : ℤ} (h : i = i') (β : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k)
      Z.obj.hom l) :
    haveI : CompactSpace Z.obj.left := QuasiCompact.compactSpace_of_compactSpace Z.obj.hom
    DirectSum.of
        (fun j ↦ SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) Z j) i
        (SmoothProjectiveScheme.pointCorrEquiv Z i
          (codimensionToCodimChow k Z.obj.hom i (chowGroupToCodimension Z.obj.hom l i β))) =
      DirectSum.of
        (fun j ↦ SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) Z j) i'
        (SmoothProjectiveScheme.pointCorrEquiv Z i'
          (codimensionToCodimChow k Z.obj.hom i' (chowGroupToCodimension Z.obj.hom l i' β))) := by
  subst h
  rfl

section Correspondences

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
  (hX : RelativeDimension X.obj.hom d)
  (hY : RelativeDimension Y.obj.hom e)

/-- **The name of the correspondence of an integral class is its point class**, in the category
of correspondences: for `α ∈ CH_e(X × Y)` and `c = 1 ⊗ α ∈ Corr⁰(X, Y)`,
`η ≫ (1 ⊗ c) = a_α`, the correspondence `Spec k ⟶ X × Y` of the class of `α` read in
codimension `d` (Stacks 0FG0 (3)). -/
theorem dualityUnit_comp_tensorHom_homOf
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    dualityUnit X hX ≫ CorrespondenceCategory.tensorHom
        (𝟙 (GradedCompositionData.Obj.mk X : CorrespondenceCategory k))
        (ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm
          ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α)))) =
      pointCorrHom (X ⊗ Y) d (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α) := by
  rw [← CorrespondenceCategory.whiskerLeft_eq, ChowMotiveCat.homOf, DirectSum.lof_eq_of,
    dualityUnit_comp_whiskerLeft_of_eq_pointCorrEquiv hX hY, corrToCodimChow_tmul, one_smul,
    pointCorrHom_apply, ChowMotiveCat.homOf, DirectSum.lof_eq_of]
  exact of_pointCorrEquiv_codimensionToCodimChow_congr (X ⊗ Y) (add_zero (d : ℤ)) α

end Correspondences

section

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
  (hX : RelativeDimension X.obj.hom d)
  (hY : RelativeDimension Y.obj.hom e)

variable (X Y) in
/-- The morphism of motives `a_α : 𝟏(-d) ⟶ h(X × Y)` of the class of `α ∈ CH_e(X × Y)` read
in codimension `d` (`Stacks.WeilCohomology.ChowMotiveCat.pointMotiveHom`). -/
def namePointHom (d : ℕ) {e : ℕ}
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj (-(d : ℤ)) ⟶
      TwistedKaroubi.ofObj (R := ℚ) (𝐎 (X ⊗ Y)) :=
  TwistedKaroubi.Hom.mk
    (pointCorrHom (X ⊗ Y) d (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α))
    ⟨TwistedKaroubi.grade_cast (pointCorrHom_mem_grade _ _ _) (by simp), Category.id_comp _,
      Category.comp_id _⟩

variable (X Y) in
/-- `h(X) ⊗ h(Y) ≅ h(X × Y)`, through `h(pr₁) ⊗ h(pr₂)` and the multiplication of `h(X × Y)`
(`Stacks.WeilCohomology.ChowMotiveCat.isIso_motMap_fst_snd_mul`). -/
def tensorMotiveIso : TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ≅
    TwistedKaroubi.ofObj (R := ℚ) (𝐎 (X ⊗ Y)) :=
  haveI := ChowMotiveCat.isIso_motMap_fst_snd_mul X Y
  asIso ((ChowMotiveCat.motMap (CorrespondenceCategory.tensorFst X Y) ⊗ₘ
    ChowMotiveCat.motMap (CorrespondenceCategory.tensorSnd X Y)) ≫ MonObj.mul)

/-- The correspondence `c = 1 ⊗ α ∈ Corr⁰(X, Y)` of an integral class `α ∈ CH_e(X × Y)`, as a
morphism of motives `h(X) ⟶ h(Y)`. -/
def nameCorrHom
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⟶ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) :=
  TwistedKaroubi.ofObjHom (ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm
    ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α))))
    (ChowMotiveCat.homOf_mem_grade _)

variable (X Y) in
/-- The isomorphism `h(X) ⊗ h(Y) ≅ h(X × Y)` is `(h(pr₁) ⊗ h(pr₂)) ≫ μ`. -/
theorem tensorMotiveIso_hom :
    (tensorMotiveIso X Y).hom = (ChowMotiveCat.motMap (CorrespondenceCategory.tensorFst X Y) ⊗ₘ
      ChowMotiveCat.motMap (CorrespondenceCategory.tensorSnd X Y)) ≫ MonObj.mul :=
  rfl

/-- The underlying correspondence of `nameCorrHom` is `1 ⊗ α`. -/
theorem nameCorrHom_val
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    (nameCorrHom hX hY α).val = ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm
      ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α))) :=
  rfl

variable (X Y) in
/-- The underlying correspondence of `namePointHom` is the class of `α` in codimension `d`. -/
theorem namePointHom_val (d : ℕ) {e : ℕ}
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    (namePointHom X Y d α).val =
      pointCorrHom (X ⊗ Y) d (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α) :=
  rfl

/-- **The name of `c` in the category of correspondences is its class** (from
`Stacks.WeilCohomology.dualityUnit_comp_whiskerLeft_of_eq_pointCorrEquiv`):
`η ≫ X ◁ c = a_α`. -/
theorem coevaluation_whiskerLeft_nameCorrHom
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    @ExactPairing.coevaluation _ _ _ _ _ (correspondenceExactPairing X hX) ≫
        𝐎 X ◁ (nameCorrHom hX hY α).val = (namePointHom X Y d α).val := by
  have hA : 𝟙_ (canonicalCorrespondenceCompositionData k).Obj =
      CorrespondenceCategory.tensorUnit := rfl
  have hB : 𝐎 X ⊗ 𝐎 X = CorrespondenceCategory.tensorObj (𝐎 X) (𝐎 X) := rfl
  have hC : 𝐎 X ⊗ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)).X =
      CorrespondenceCategory.tensorObj (𝐎 X) (𝐎 Y) := rfl
  have hx : @ExactPairing.coevaluation _ _ _ _ _ (correspondenceExactPairing X hX) ≍
      dualityUnit X hX := HEq.rfl
  have hy : 𝐎 X ◁ (nameCorrHom hX hY α).val ≍
      CorrespondenceCategory.tensorHom
        (𝟙 (GradedCompositionData.Obj.mk X : CorrespondenceCategory k))
        (ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm
          ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α)))) :=
    HEq.rfl
  have hz : (namePointHom X Y d α).val ≍
      pointCorrHom (X ⊗ Y) d (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α) :=
    HEq.rfl
  exact comp_eq_of_heq (dualityUnit_comp_tensorHom_homOf hX hY α) hA hB hC hx hy hz

/-- `a_α ≫ 𝟙 = a_α`, with the identity of `h(X) ⊗ h(Y)` spelled as the target of `a_α`. -/
theorem namePointHom_val_comp_id
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    (namePointHom X Y d α).val ≫ 𝟙 (𝐎 X ⊗ 𝐎 Y) = (namePointHom X Y d α).val :=
  Category.comp_id _

/-- `coevaluation_whiskerLeft_nameCorrHom` followed by the identity of `h(X) ⊗ h(Y)`. -/
theorem coevaluation_whiskerLeft_nameCorrHom_comp_id
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0)) :
    @ExactPairing.coevaluation _ _ _ _ _ (correspondenceExactPairing X hX) ≫
        𝐎 X ◁ (nameCorrHom hX hY α).val = (namePointHom X Y d α).val ≫ 𝟙 (𝐎 X ⊗ 𝐎 Y) :=
  (coevaluation_whiskerLeft_nameCorrHom hX hY α).trans (namePointHom_val_comp_id α).symm

/-- `coevaluation_whiskerLeft_nameCorrHom_comp_id` for any morphism `f : h(X) ⟶ h(Y)` with
underlying correspondence `1 ⊗ α`. -/
theorem coevaluation_whiskerLeft_comp_id_of_val
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0))
    (f : TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⟶ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
    (hf : f.val = (ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm
          ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α))))) :
    @ExactPairing.coevaluation _ _ _ _ _ (correspondenceExactPairing X hX) ≫ 𝐎 X ◁ f.val =
      (namePointHom X Y d α).val ≫ 𝟙 (𝐎 X ⊗ 𝐎 Y) := by
  rw [hf, ← nameCorrHom_val hX hY α]
  exact coevaluation_whiskerLeft_nameCorrHom_comp_id hX hY α

/-- **The name of a correspondence under the self-duality of `h(X)`, in `M_k`** (used in
Stacks 0FHM). Let `X`, `Y` be smooth projective over `k`, equidimensional of dimensions `d` and
`e`, let `h(X) ⊗ 𝟏(d)` be the dual of `h(X)` of Stacks 0FGI
(`Stacks.WeilCohomology.ChowMotiveCat.exactPairingMotive`), and let `f : h(X) ⟶ h(Y)` be a
morphism whose underlying correspondence is `c = 1 ⊗ α ∈ Corr⁰(X, Y)`, for an integral class
`α ∈ CH_e(X × Y)`. Then the name of `f ▷ 𝟏(d)` is
`η ≫ h(X) ◁ (f ▷ 𝟏(d)) = u ≫ (a_α ▷ 𝟏(d)) ≫ (κ⁻¹ ▷ 𝟏(d)) ≫ α`, where
`u : 𝟏 ⟶ 𝟏(-d) ⊗ 𝟏(d)` is the inverse of `𝟏(-d) ⊗ 𝟏(d) ≅ 𝟏`
(`Stacks.WeilCohomology.unitTwistNegTensorHom_eq_inv`), `a_α : 𝟏(-d) ⟶ h(X × Y)` is the
correspondence of the class of `α` in `CH^d(X × Y)` (Stacks 0FG0) and
`κ : h(X) ⊗ h(Y) ≅ h(X × Y)` is `(h(pr₁) ⊗ h(pr₂)) ≫ μ`. -/
theorem coevaluation_whiskerLeft_whiskerRight_eq
    (α : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom)
      ((e : ℤ) - 0))
    (f : TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⟶ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
    (hf : f.val = (ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm
          ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α))))) :
    letI := ChowMotiveCat.exactPairingMotive hX
    η_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
      TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ◁
        (f ▷ TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) =
      unitTwistNegTensorHom ℚ (canonicalCorrespondenceCompositionData k).Obj d ≫
        (namePointHom X Y d α ▷
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
        ((tensorMotiveIso X Y).inv ▷
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
        (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom := by
  let _ := correspondenceExactPairing X hX
  refine (coevaluationOfObjTensorTwist_comp_whiskerLeft (𝐎 X) (𝐎 Y)
    (correspondenceExactPairing_coevaluation_mem_grade X hX)
    (correspondenceExactPairing_evaluation_mem_grade X hX) f
    (namePointHom X Y d α ≫ (tensorMotiveIso X Y).inv)
    (coevaluation_whiskerLeft_eq_comp_inv_val_of_hom_eq (X := 𝐎 X) (Y := 𝐎 Y) (P := 𝐎 (X ⊗ Y))
      (CorrespondenceCategory.graphHom_mem_grade' _) (CorrespondenceCategory.graphHom_mem_grade' _)
      (graphHom (CorrespondenceCategory.tensorFst X Y))
      (CorrespondenceCategory.graphHom_mem_grade' _)
      (graphHom (CorrespondenceCategory.tensorSnd X Y))
      (CorrespondenceCategory.graphHom_mem_grade' _) (𝟙 (𝐎 X ⊗ 𝐎 Y)) (GradedCategory.id_mem _)
      ?_
      f (tensorMotiveIso X Y) rfl (namePointHom X Y d α)
      (coevaluation_whiskerLeft_comp_id_of_val hX hY α f hf))).trans ?_
  · rw [CorrespondenceCategory.tensorHom_graphHom_tensorFst_tensorSnd_mul X Y, Category.id_comp]
  · rw [MonoidalCategory.comp_whiskerRight, Category.assoc]

end

end Stacks.WeilCohomology

end
