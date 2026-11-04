module

public import StacksFrontier.Algebra.Homology.MapBifunctorShiftedPairing
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegrees
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Shifting pairings of single complexes

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor and `φ : F(M, N) ⟶ H`. The pairing
`Tot(M[-a] ⊗ N[-b]) ≅ F(M, N)[-a-b] ⟶ H[-a-b]` that `φ` induces between single complexes
(`CochainComplex.singleSinglePairing`) is carried to the pairing of the same kind in other degrees
by the two shifting operations used in the proof of [Stacks, Tag 0G8K]: the shift of a pairing by
`(s, -s)` (`CochainComplex.shiftedPairing_singleSinglePairing`) and the shift of its second
variable and target (`CochainComplex.rightShift_singleSinglePairing`), each up to a sign and the
identifications of shifted single complexes with single complexes.

## Main results

* `CochainComplex.mapBifunctor_single_single_hom_ext`
* `CochainComplex.shiftedPairing_singleSinglePairing`
* `CochainComplex.rightShift_singleSinglePairing`

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject

namespace CochainComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

omit [HasZeroObject D] in
/-- A map out of the total complex of two single complexes is determined by its restriction to
the summand of their degrees. -/
theorem mapBifunctor_single_single_hom_ext (M : C₁) (N : C₂) (a b : ℤ) {W : CochainComplex D ℤ}
    {u v : mapBifunctor ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)
      ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) F ⟶ W}
    (h : ιMapBifunctor _ _ F a b (a + b) rfl ≫ u.f (a + b) =
      ιMapBifunctor _ _ F a b (a + b) rfl ≫ v.f (a + b)) : u = v := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  by_cases hk : k = a + b
  · subst hk
    exact HomologicalComplex.mapBifunctor.hom_ext fun i j hij => by
      by_cases hij' : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hij'
        exact h
      · exact (HomologicalComplex.isZero_obj_obj_single_obj_X_X F M N a b i j
          (not_and_or.mp hij')).eq_of_src _ _
  · exact (HomologicalComplex.isZero_mapBifunctor_single_single_X F M N a b k hk).eq_of_src _ _

/-- The pairing `Tot(M[-a] ⊗ N[-b]) ≅ F(M, N)[-a-b] ⟶ H[-a-b]` induced by `φ : F(M, N) ⟶ H`. -/
def singleSinglePairing (M : C₁) (N : C₂) (a b : ℤ) {H : D} (φ : (F.obj M).obj N ⟶ H) :
    mapBifunctor ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)
      ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) F ⟶
      (HomologicalComplex.single D (ComplexShape.up ℤ) (a + b)).obj H :=
  (HomologicalComplex.mapBifunctorSingleSingleIso F M N a b).hom ≫
    (HomologicalComplex.single D (ComplexShape.up ℤ) (a + b)).map φ

/-- On its summand, `singleSinglePairing` is `φ` read through the identifications of terms. -/
@[reassoc]
theorem ι_singleSinglePairing_f (M : C₁) (N : C₂) (a b : ℤ) {H : D} (φ : (F.obj M).obj N ⟶ H) :
    ιMapBifunctor _ _ F a b (a + b) rfl ≫ (singleSinglePairing F M N a b φ).f (a + b) =
      (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom).app _ ≫
        (F.obj M).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b N).hom ≫ φ ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (a + b) H).inv := by
  simp only [singleSinglePairing, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f_assoc,
    HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]

/-- `ι_singleSinglePairing_f` at a degree `k` equal to `a + b`. -/
@[reassoc]
theorem ι_singleSinglePairing_f' (M : C₁) (N : C₂) (a b k : ℤ) (hk : a + b = k) {H : D}
    (φ : (F.obj M).obj N ⟶ H) :
    ιMapBifunctor _ _ F a b k hk ≫ (singleSinglePairing F M N a b φ).f k =
      (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom).app _ ≫
        (F.obj M).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b N).hom ≫ φ ≫
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) (a + b) H k hk.symm).inv := by
  subst hk
  exact ι_singleSinglePairing_f F M N a b φ

omit [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F] in
/-- The components of the commutation of single complexes with the shift are identities of
equal objects. -/
theorem singleFunctors_shiftIso_inv_app_f_eq_eqToHom (C : Type*) [Category* C] [Preadditive C]
    [HasZeroObject C] (n a a' : ℤ) (h : n + a = a') (X : C) (i : ℤ) :
    ∃ p, (((CochainComplex.singleFunctors C).shiftIso n a a' h).inv.app X).f i = eqToHom p := by
  dsimp only [CochainComplex.singleFunctors]
  simp only [NatIso.ofComponents_inv_app, HomologicalComplex.Hom.isoOfComponents_inv_f,
    eqToIso.inv]
  refine ⟨?_, trivial⟩
  show (if i = a then X else 0) = (if i + n = a' then X else 0)
  exact if_congr (show i = a ↔ i + n = a' by omega) rfl rfl

/-- **The shift of `singleSinglePairing` by `(s, -s)`** is, up to the sign `(-1)^{(a-s)(-s)}`, the
`singleSinglePairing` of `M[-(a-s)]` and `N[-(b+s)]`. -/
theorem shiftedPairing_singleSinglePairing (M : C₁) (N : C₂) (a b s : ℤ) {H : D}
    (φ : (F.obj M).obj N ⟶ H) :
    mapBifunctorMap (((CochainComplex.singleFunctors C₁).shiftIso s (a - s) a (by omega)).inv.app M)
        (((CochainComplex.singleFunctors C₂).shiftIso (-s) (b + s) b (by omega)).inv.app N) F
          (ComplexShape.up ℤ) ≫
      F.map₂CochainComplex.shiftedPairing (singleSinglePairing F M N a b φ) s (-s) (by omega) =
    ((a - s) * (-s)).negOnePow • (singleSinglePairing F M N (a - s) (b + s) φ ≫
      eqToHom (congrArg (fun k => (HomologicalComplex.single D (ComplexShape.up ℤ) k).obj H)
        (by omega))) := by
  refine mapBifunctor_single_single_hom_ext F M N (a - s) (b + s) ?_
  erw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc]
  have key := Functor.ι_shiftedPairing_map₂CochainComplex_f F (singleSinglePairing F M N a b φ)
    s (-s) (by omega) (a - s) (b + s) _ rfl a b (by omega) (by omega)
  refine (congrArg (_ ≫ _ ≫ ·) key).trans ?_
  rw [Linear.comp_units_smul, Linear.comp_units_smul, HomologicalComplex.units_smul_f_apply,
    Linear.comp_units_smul]
  congr 1
  rw [ι_singleSinglePairing_f' F M N a b _ (by omega), HomologicalComplex.comp_f,
    ι_singleSinglePairing_f_assoc]
  obtain ⟨p₁, hp₁⟩ := singleFunctors_shiftIso_inv_app_f_eq_eqToHom C₁ s (a - s) a (by omega) M
    (a - s)
  obtain ⟨p₂, hp₂⟩ := singleFunctors_shiftIso_inv_app_f_eq_eqToHom C₂ (-s) (b + s) b (by omega) N
    (b + s)
  rw [hp₁, hp₂]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom,
    eqToIso.inv, HomologicalComplex.eqToHom_f, eqToHom_map, eqToHom_app, eqToHom_trans_assoc,
    eqToHom_trans]

omit [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F] in
/-- The components of the commutation of single complexes with the shift are identities of
equal objects. -/
theorem singleFunctors_shiftIso_hom_app_f_eq_eqToHom (C : Type*) [Category* C] [Preadditive C]
    [HasZeroObject C] (n a a' : ℤ) (h : n + a = a') (X : C) (i : ℤ) :
    ∃ p, (((CochainComplex.singleFunctors C).shiftIso n a a' h).hom.app X).f i = eqToHom p := by
  dsimp only [CochainComplex.singleFunctors]
  simp only [NatIso.ofComponents_hom_app, HomologicalComplex.Hom.isoOfComponents_hom_f,
    eqToIso.hom]
  refine ⟨?_, trivial⟩
  show (if i + n = a' then X else 0) = (if i = a then X else 0)
  exact if_congr (show i + n = a' ↔ i = a by omega) rfl rfl

/-- **The right shift of `singleSinglePairing` by `m`** — the commutation of the total complex
with the shift in its second variable followed by the shift of the pairing — is, up to the sign
`(-1)^{am}`, the `singleSinglePairing` of `M[-a]` and `N[-(b-m)]`. -/
theorem rightShift_singleSinglePairing (M : C₁) (N : C₂) (a b m : ℤ) {H : D}
    (φ : (F.obj M).obj N ⟶ H) :
    mapBifunctorMap (𝟙 _)
        (((CochainComplex.singleFunctors C₂).shiftIso m (b - m) b (by omega)).inv.app N) F
          (ComplexShape.up ℤ) ≫
      ((F.map₂CochainComplex.obj
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)).commShiftIso m).hom.app
          ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) ≫
      (singleSinglePairing F M N a b φ)⟦m⟧' ≫
      (((CochainComplex.singleFunctors D).shiftIso m (a + b - m) (a + b) (by omega)).hom.app H) =
    (a * m).negOnePow • (singleSinglePairing F M N a (b - m) φ ≫
      eqToHom (congrArg (fun k => (HomologicalComplex.single D (ComplexShape.up ℤ) k).obj H)
        (by omega))) := by
  refine mapBifunctor_single_single_hom_ext F M N a (b - m) ?_
  erw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc]
  have key := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f
    ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)
    ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) F m a (b - m) (a + (b - m)) rfl b
    (a + (b - m) + m) (by omega) rfl
  refine (congrArg (_ ≫ _ ≫ ·) ((congrArg (_ ≫ ·) ((HomologicalComplex.comp_f _ _ _).trans
    (congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)))).trans ((reassoc_of% key) _))).trans ?_
  simp only [Linear.units_smul_comp, Linear.comp_units_smul,
    HomologicalComplex.units_smul_f_apply, Category.assoc]
  congr 1
  have nice : (F.map (𝟙 (((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M).X a))).app
        (((HomologicalComplex.single C₂ (ComplexShape.up ℤ) (b - m)).obj N).X (b - m)) ≫
      (F.obj (((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M).X a)).map
          ((((CochainComplex.singleFunctors C₂).shiftIso m (b - m) b (by omega)).inv.app N).f
            (b - m)) ≫
        (F.obj (((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M).X a)).map
            (CochainComplex.shiftFunctorObjXIso
              ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) m (b - m) b
              (by omega)).hom ≫
          ιMapBifunctor ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)
              ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) F a b
              (a + (b - m) + m) (by omega) ≫
            (CochainComplex.shiftFunctorObjXIso (mapBifunctor
              ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)
              ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) F) m (a + (b - m))
              (a + (b - m) + m) rfl).inv ≫
            (singleSinglePairing F M N a b φ).f (a + (b - m) + m) ≫
                (((CochainComplex.singleFunctors D).shiftIso m (a + b - m) (a + b)
                  (by omega)).hom.app H).f (a + (b - m)) =
      ιMapBifunctor ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)
          ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) (b - m)).obj N) F a (b - m)
          (a + (b - m)) rfl ≫
        (singleSinglePairing F M N a (b - m) φ).f (a + (b - m)) ≫
          (eqToHom (congrArg (fun k => (HomologicalComplex.single D (ComplexShape.up ℤ) k).obj H)
            (by omega))).f (a + (b - m)) := by
    have hx : (CochainComplex.shiftFunctorObjXIso (mapBifunctor
        ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) a).obj M)
        ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) b).obj N) F) m (a + (b - m))
        (a + (b - m) + m) rfl).inv = 𝟙 _ := by
      simp [CochainComplex.shiftFunctorObjXIso]
    rw [hx, Category.id_comp, ι_singleSinglePairing_f'_assoc F M N a b _ (by omega),
      ι_singleSinglePairing_f_assoc]
    obtain ⟨p₁, hp₁⟩ := singleFunctors_shiftIso_inv_app_f_eq_eqToHom C₂ m (b - m) b (by omega) N
      (b - m)
    obtain ⟨p₂, hp₂⟩ := singleFunctors_shiftIso_hom_app_f_eq_eqToHom D m (a + b - m) (a + b)
      (by omega) H (a + (b - m))
    rw [hp₁, hp₂]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom,
      eqToIso.inv, HomologicalComplex.eqToHom_f, eqToHom_map, eqToHom_app, eqToHom_trans_assoc,
      eqToHom_trans, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact (congrArg (_ ≫ _ ≫ ·) (by rfl)).trans
    (nice.trans (congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _).symm))

end CochainComplex
