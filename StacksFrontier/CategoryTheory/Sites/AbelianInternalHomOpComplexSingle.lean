module

public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpComplex

/-!
# The internal Hom complex out of a single sheaf

For a sheaf `A` of `Λ`-modules and a complex `M` of abelian sheaves, the internal Hom complex
`ℋom^•_ℤ(A[0], M)` of `Stacks.AbelianInternalHom.homOpComplex` is `ℋom_ℤ(A, -)` applied termwise
to `M`: in degree `n` the only nonzero factor of `∏_{p + n = q} ℋom_ℤ(A[0]^p, M^q)` is
`ℋom_ℤ(A, M^n)`, and the differential is postcomposition with that of `M`.

## Main definitions

* `Stacks.AbelianInternalHom.homOpComplexSingleIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {Λ : Type w} [Ring Λ]

/-- `ℋom_ℤ(G, F)` vanishes when `G` does. -/
lemma isZero_homOpSheaf_of_isZero {G : Sheaf K (ModuleCat.{max u v} Λ)} (hG : IsZero G)
    (F : Sheaf K AddCommGrpCat.{max u v}) : IsZero (homOpSheaf K G F) := by
  rw [IsZero.iff_id_eq_zero, ← homOpMapLeft_id K G F, hG.eq_of_src (𝟙 G) 0,
    homOpMapLeft_zero]

variable [HasZeroObject (Sheaf K (ModuleCat.{max u v} Λ))]
  (A : Sheaf K (ModuleCat.{max u v} Λ)) (M : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ)

/-- `ℋom_ℤ(A, -)` preserves zero morphisms. -/
local instance homOpFunctor_preservesZeroMorphisms_single :
    (homOpFunctor K A).PreservesZeroMorphisms :=
  ⟨fun F F' => homOpMap_zero K A F F'⟩

/-- The index `(0, n)` of the only nonzero factor of `ℋom^n_ℤ(A[0], M)`. -/
abbrev homOpSingleIndex (n : ℤ) : HomOpIndex n := ⟨(0, n), zero_add n⟩

/-- For an index `x` equal to `(0, n)`, the map `ℋom_ℤ(A, M^n) ⟶ ℋom_ℤ(A[0]^0, M^n)` induced by
`A[0]^0 ≅ A`. -/
def homOpSingleComponent (n : ℤ) (x : HomOpIndex n) (h : x = homOpSingleIndex n) :
    homOpSheaf K A (M.X n) ⟶
      homOpSheaf K (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A).X x.1.1)
        (M.X x.1.2) := by
  subst h
  exact homOpMapLeft K (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom (M.X n)

/-- At the index `(0, n)` itself, `homOpSingleComponent` is `ℋom_ℤ` of `A[0]^0 ≅ A`. -/
lemma homOpSingleComponent_self (n : ℤ) :
    homOpSingleComponent K A M n (homOpSingleIndex n) rfl =
      homOpMapLeft K (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom (M.X n) :=
  rfl

/-- **`ℋom^n_ℤ(A[0], M) ≅ ℋom_ℤ(A, M^n)`**. -/
def homOpComplexSingleXIso (n : ℤ) :
    homOpComplexX K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A) M n ≅
      homOpSheaf K A (M.X n) where
  hom := homOpComplexπ K _ M n (homOpSingleIndex n) ≫
    homOpMapLeft K (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv (M.X n)
  inv := homOpComplexLift K _ M n fun x =>
    if h : x = homOpSingleIndex n then homOpSingleComponent K A M n x h else 0
  hom_inv_id := by
    refine homOpComplexX_hom_ext K _ M n fun x => ?_
    simp only [Category.assoc, homOpComplexLift_π, Category.id_comp]
    by_cases h : x = homOpSingleIndex n
    · subst h
      simp only [dite_eq_left, homOpSingleComponent_self, homOpMapLeft_comp, Iso.hom_inv_id,
        homOpMapLeft_id, Category.comp_id]
    · rw [dite_eq_right h, comp_zero]
      refine (isZero_homOpSheaf_of_isZero K ?_ _).eq_of_tgt _ _
      refine HomologicalComplex.isZero_single_obj_X _ _ _ _ fun h' => h ?_
      exact Subtype.ext (Prod.ext h' (by have := x.2; change x.1.2 = n; omega))
  inv_hom_id := by
    have h₁ := homOpComplexLift_π K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A) M
      n (fun x => if h : x = homOpSingleIndex n then homOpSingleComponent K A M n x h else 0)
      (homOpSingleIndex n)
    rw [dite_eq_left rfl, homOpSingleComponent_self] at h₁
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ homOpMapLeft K
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv (M.X n)) h₁).trans ?_)
    rw [homOpMapLeft_comp, Iso.inv_hom_id, homOpMapLeft_id]

omit [HasZeroObject (Sheaf K (ModuleCat.{max u v} Λ))] in
/-- For `a = b`, the projection of `ℋom^n_ℤ(L, M)` to the factor `(p, a)` followed by
postcomposition with `d_M^{a, c}` equals the projection to `(p, b)` followed by postcomposition
with `d_M^{b, c}`. -/
lemma homOpComplexπ_homOpMap_congr (L : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ)
    {n : ℤ} (p a b : ℤ) (h : a = b) (ha : p + n = a) (hb : p + n = b) (c : ℤ) :
    homOpComplexπ K L M n ⟨(p, a), ha⟩ ≫ homOpMap K (L.X p) (M.d a c) =
      homOpComplexπ K L M n ⟨(p, b), hb⟩ ≫ homOpMap K (L.X p) (M.d b c) := by
  subst h; rfl

/-- The isomorphisms `homOpComplexSingleXIso` commute with the differentials of `ℋom^•_ℤ(A[0], M)`
and of `ℋom_ℤ(A, M^•)`. -/
lemma homOpComplexSingleXIso_hom_comm (n : ℤ) :
    (homOpComplexSingleXIso K A M n).hom ≫ homOpMap K A (M.d n (n + 1)) =
      (homOpComplex K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A) M).d n (n + 1) ≫
        (homOpComplexSingleXIso K A M (n + 1)).hom := by
  rw [homOpComplex_d]
  change _ = homOpComplexD K _ M n ≫ homOpComplexπ K _ M (n + 1) (homOpSingleIndex (n + 1)) ≫ _
  rw [homOpComplexD_π_assoc]
  unfold homOpComplexDComponent
  have hd : ∀ i j, ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A).d i j = 0 :=
    fun _ _ => rfl
  dsimp only [homOpSingleIndex]
  simp only [hd, homOpMapLeft_zero, comp_zero, smul_zero, add_zero]
  rw [homOpComplexπ_homOpMap_congr K M _ 0 (n + 1 - 1) n (by omega) _ (zero_add n) (n + 1)]
  simp only [homOpComplexSingleXIso, Category.assoc, homOpMapLeft_homOpMap]

/-- **`ℋom^•_ℤ(A[0], M) ≅ ℋom_ℤ(A, -)` applied termwise to `M`.** -/
def homOpComplexSingleIso :
    homOpComplex K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A) M ≅
      ((homOpFunctor K A).mapHomologicalComplex _).obj M :=
  HomologicalComplex.Hom.isoOfComponents (homOpComplexSingleXIso K A M) (by
    rintro n _ rfl
    exact homOpComplexSingleXIso_hom_comm K A M n)

end Stacks.AbelianInternalHom

end
