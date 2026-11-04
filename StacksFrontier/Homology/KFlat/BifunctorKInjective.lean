module

public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
import all StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# Total complexes with a bounded factor and K-injectivity

Let `F : A ⥤ B ⥤ D` be a bifunctor additive in each variable and `K` a complex of objects of
`A`. Let `L` be a complex of objects of `B` which is strictly bounded on both sides. If for each
degree `q` the complex `p ↦ F(Kᵖ, L^q)` is K-injective, then the total complex `Tot(F(K, L))` is
K-injective.

## Main definitions

* `CochainComplex.KFlatBifunctor.TotIsKInjective`: the total complex `Tot(F(K, L))` is
  K-injective.

## Main results

* `CochainComplex.KFlatBifunctor.isKInjective_totalComplex_of_isStrictlyLE_of_isStrictlyGE`: if
  `L` is strictly bounded and each `Tot(F(K, L^q[-q]))` is K-injective, then `Tot(F(K, L))` is
  K-injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open ComplexShape HomologicalComplex

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (K : CochainComplex A ℤ)

/-- `Tot(F(K, L))` is K-injective. -/
def TotIsKInjective (L : CochainComplex B ℤ) : Prop :=
  CochainComplex.IsKInjective (totalComplex F K L)

omit [HasZeroObject B] [HasBinaryBiproducts B] in
/-- `Tot(F(K, L))` is K-injective if and only if the image of `L` under
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K` is right orthogonal to the acyclic
complexes in the homotopy category of `D`. -/
theorem totIsKInjective_iff (L : CochainComplex B ℤ) :
    TotIsKInjective F K L ↔ (HomotopyCategory.subcategoryAcyclic D).rightOrthogonal
      ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) := by
  unfold TotIsKInjective
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  exact (ObjectProperty.prop_iff_of_iso _
    ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors F K).app L)).symm

omit [HasZeroObject B] [HasBinaryBiproducts B] in
/-- If `L ≅ L'` and `Tot(F(K, L))` is K-injective, then so is `Tot(F(K, L'))`. -/
theorem TotIsKInjective.of_iso {L L' : CochainComplex B ℤ} (h : TotIsKInjective F K L)
    (e : L ≅ L') : TotIsKInjective F K L' := by
  rw [totIsKInjective_iff] at h ⊢
  exact ObjectProperty.prop_of_iso _
    ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K).mapIso
      ((HomotopyCategory.quotient B _).mapIso e)) h

/-- For a short complex `S` of cochain complexes which is split in each degree, if
`Tot(F(K, S.X₁))` and `Tot(F(K, S.X₃))` are K-injective, then so is `Tot(F(K, S.X₂))`. -/
theorem totIsKInjective_X₂_of_degreewiseSplit (S : ShortComplex (CochainComplex B ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval B _ n)).Splitting)
    (h₁ : TotIsKInjective F K S.X₁) (h₃ : TotIsKInjective F K S.X₃) :
    TotIsKInjective F K S.X₂ := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F K
  rw [totIsKInjective_iff] at h₁ h₃ ⊢
  exact ObjectProperty.ext_of_isTriangulatedClosed₂ _ _
    (bifunctorPhi_mapTriangle_distinguished F K _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ)) h₁ h₃

omit [HasBinaryBiproducts B] in
/-- If the row `p ↦ F(Kᵖ, M)` is K-injective, then `Tot(F(K, M[-q]))` is K-injective, where
`M[-q]` is the complex with `M` in degree `q` and zero elsewhere. -/
theorem totIsKInjective_single (M : B) (q : ℤ)
    (h : CochainComplex.IsKInjective (rowComplex F K M)) :
    TotIsKInjective F K ((single B (ComplexShape.up ℤ) q).obj M) := by
  have e := mapBifunctorSingleIso F K M q
  have : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) q).HasTotal
      (ComplexShape.up ℤ) := HomologicalComplex₂.hasTotal_of_iso e _
  have etot :
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
          ((single B (ComplexShape.up ℤ) q).obj M)).total (ComplexShape.up ℤ) ≅
        (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) q).total
          (ComplexShape.up ℤ) :=
    { hom := HomologicalComplex₂.total.map e.hom (ComplexShape.up ℤ)
      inv := HomologicalComplex₂.total.map e.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← HomologicalComplex₂.total.map_comp, e.hom_inv_id,
          HomologicalComplex₂.total.map_id]
      inv_hom_id := by
        rw [← HomologicalComplex₂.total.map_comp, e.inv_hom_id,
          HomologicalComplex₂.total.map_id] }
  have := StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit (rowComplex F K M) q
  have hsh : CochainComplex.IsKInjective
      ((CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-q)).obj (rowComplex F K M)) :=
    (CochainComplex.isKInjective_shift_iff _ (-q)).2 h
  exact CochainComplex.isKInjective_of_iso
    ((asIso (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) q)) ≪≫ etot.symm)

section Bounded

variable (L : CochainComplex B ℤ) (b : ℤ)

/-- The stupid truncation `σ_{≤ b - 1} L` is zero in degrees `> b - 1`. -/
private lemma isZero_stupidTrunc_X_of_lt {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (L : CochainComplex C ℤ) (b : ℤ) {q : ℤ} (hq : b - 1 < q) :
    IsZero ((L.stupidTrunc (embeddingUpIntLE (b - 1))).X q) :=
  L.isZero_stupidTrunc_X _ q (fun k => by change (b - 1 : ℤ) - (k : ℤ) ≠ q; omega)

/-- Let `L` be strictly concentrated in degrees `≤ b`. If `Tot(F(K, L^b[-b]))` and
`Tot(F(K, σ_{≤ b - 1} L))` are K-injective, where `σ_{≤ b - 1} L` is the stupid truncation, then
`Tot(F(K, L))` is K-injective. -/
theorem totIsKInjective_of_single_top [L.IsStrictlyLE b]
    (htop : TotIsKInjective F K ((single B (ComplexShape.up ℤ) b).obj (L.X b)))
    (hrest : TotIsKInjective F K (L.stupidTrunc (embeddingUpIntLE (b - 1)))) :
    TotIsKInjective F K L := by
  set e := embeddingUpIntLE (b - 1) with he
  set ι := mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b) with hιdef
  have hιb : IsIso (ι.f b) := by
    rw [hιdef, mkHomFromSingle_f, Category.comp_id]
    infer_instance
  have hlift : e.HasLift (𝟙 (L.restriction e)) :=
    fun _ hj _ _ => (hj.false_of_isTruncLE).elim
  set π := e.liftExtend (𝟙 (L.restriction e)) hlift with hπdef
  have hπiso : ∀ i : ℤ, i ≠ b → IsIso (π.f i) := by
    intro i hi
    by_cases hib : i ≤ b - 1
    · refine (e.isIso_liftExtend_f_iff _ hlift
        (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i hib)).2 ?_
      rw [HomologicalComplex.id_f]
      infer_instance
    · exact (L.isZero_of_isStrictlyLE b i (by omega)).isIso
        (isZero_stupidTrunc_X_of_lt L b (by omega)) _
  have hTb : IsZero ((L.stupidTrunc e).X b) := isZero_stupidTrunc_X_of_lt L b (by omega)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi; exact hTb.eq_of_tgt _ _
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi).eq_of_src _ _
  refine totIsKInjective_X₂_of_degreewiseSplit F K (ShortComplex.mk ι π hcomp) (fun n => ?_)
    htop hrest
  by_cases hn : n = b
  · subst hn
    have := hιb
    exact { r := inv (ι.f n)
            s := 0
            f_r := by simp
            s_g := hTb.eq_of_tgt _ _
            id := by simp }
  · have := hπiso n hn
    exact { r := 0
            s := inv (π.f n)
            f_r := (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) n hn).eq_of_src _ _
            s_g := by simp
            id := by simp }

private lemma totIsKInjective_of_bounds (n : ℕ) : ∀ (L : CochainComplex B ℤ) (a b : ℤ),
    L.IsStrictlyLE b → L.IsStrictlyGE a → a + n = b →
    (∀ q : ℤ, a ≤ q → q ≤ b →
      TotIsKInjective F K ((single B (ComplexShape.up ℤ) q).obj (L.X q))) →
    TotIsKInjective F K L := by
  induction n with
  | zero =>
      intro L a b hle hge hab hterm
      obtain rfl : a = b := by omega
      exact ((hterm a le_rfl le_rfl).of_iso F K (isoSingleOfConcentrated L a))
  | succ n IH =>
      intro L a b hle hge hab hterm
      set e := embeddingUpIntLE (b - 1) with he
      have hiso : ∀ q : ℤ, q ≤ b - 1 → ((L.stupidTrunc e).X q ≅ L.X q) := fun q hq =>
        L.stupidTruncXIso e (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) q hq)
      have hgeT : CochainComplex.IsStrictlyGE (L.stupidTrunc e) a := by
        refine IsStrictlySupported.mk (fun i hi => ?_)
        rw [notMem_range_embeddingUpIntGE_iff] at hi
        by_cases hib : i ≤ b - 1
        · exact IsZero.of_iso (L.isZero_of_isStrictlyGE a i hi) (hiso i hib)
        · exact isZero_stupidTrunc_X_of_lt L b (by omega)
      refine totIsKInjective_of_single_top F K L b (hterm b (by omega) le_rfl)
        (IH _ a (b - 1) inferInstance hgeT (by omega) (fun q hq hq' => ?_))
      exact (hterm q hq (by omega)).of_iso F K
        ((single B (ComplexShape.up ℤ) q).mapIso (hiso q hq').symm)

/-- If `L` is strictly concentrated in degrees `[a, b]` and `Tot(F(K, L^q[-q]))` is K-injective
for every `q`, then `Tot(F(K, L))` is K-injective. -/
theorem isKInjective_totalComplex_of_isStrictlyLE_of_isStrictlyGE (a : ℤ) [L.IsStrictlyLE b]
    [L.IsStrictlyGE a]
    (hterm : ∀ q : ℤ, TotIsKInjective F K ((single B (ComplexShape.up ℤ) q).obj (L.X q))) :
    TotIsKInjective F K L := by
  by_cases hab : a ≤ b
  · exact totIsKInjective_of_bounds F K (b - a).toNat L a b inferInstance inferInstance (by omega)
      fun q _ _ => hterm q
  · have : L.IsStrictlyGE b := ⟨fun i hi => L.isZero_of_isStrictlyGE a i (by
      simp only [notMem_range_embeddingUpIntGE_iff] at hi ⊢; omega)⟩
    exact totIsKInjective_of_bounds F K 0 L b b inferInstance this (by omega) fun q _ _ => hterm q

end Bounded

end CochainComplex.KFlatBifunctor
