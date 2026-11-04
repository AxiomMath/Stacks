module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroResidueLinear
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroDifferentialGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedModuleCorrespondence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyForgetCommShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestriction

/-!
# The boundary of the residue sequence lifts to `D(Ω^•_{X/S}, d)`

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of its line bundle. The proof of Stacks Tag 0FUG begins:

> To be precise we consider the shift `0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0` of
> the short exact sequence of Lemma 0FUF. [...] Hence we may view
> `Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1]` as a map of right differential graded `Ω^•_{X/S}`-modules
> on `X`. The map `Res : Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S}` is a map of right differential graded
> `Ω^•_{X/S}`-modules [...]. Thus by the discussion in Differential Graded Sheaves, Section 0FU3
> we see that `δ` comes from a map `δ' : Ω^•_{X/S} → Ω^•_{X/S}[2]` in the derived category
> `D(Ω^•_{X/S}, d)` of right differential graded modules over the de Rham complex.

This file carries this out.

## Main definitions

* `Stacks.LineBundle.Situation.weightZeroDifferentialGradedModule`: `Ω^•_{L^⋆/S,0}` as a right
  differential graded `Ω^•_{X/S}`-module, through the homomorphism
  `Stacks.LineBundle.Situation.weightZeroDifferentialGradedAlgebraInclusion`.
* `Stacks.LineBundle.Situation.residueDifferentialGradedSequence`: the shifted residue sequence
  `0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0` as a short complex of right differential
  graded `Ω^•_{X/S}`-modules.

## Main results

* `Stacks.LineBundle.Situation.residueDifferentialGradedSequence_shortExact`: it is short exact.
* `Stacks.LineBundle.Situation.exists_deRhamForgetHom_eq_residueShiftedSequence_boundary`:
  **the boundary map `δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` of the shifted residue sequence comes from a
  morphism of `D(Ω^•_{X/S}, d)`**.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
-/

@[expose] public noncomputable section

open CategoryTheory ComplexShape Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### The weight-zero forms as a right differential graded module -/

/-- The pullback of forms `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` sends `1` to `1`. -/
theorem Situation.weightZeroDifferentialGradedAlgebraInclusion_preservesOne :
    D.weightZeroDifferentialGradedAlgebraInclusion.PreservesOne :=
  fun U => D.weightZeroDifferentialGradedAlgebraInclusion_one U

/-- **`Ω^•_{L^⋆/S,0}` as a right differential graded `Ω^•_{X/S}`-module**: the regular module of
the differential graded algebra `Ω^•_{L^⋆/S,0}`, read over `Ω^•_{X/S}` through the pullback of
forms, so that a form `α` of `X` acts by `x ↦ x ∧ π^*α`. -/
def Situation.weightZeroDifferentialGradedModule :
    _root_.SheafOfModules.DifferentialGradedModule.{u, u, u}
      (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))) :=
  restrictionObj D.weightZeroDifferentialGradedAlgebraInclusion
    D.weightZeroDifferentialGradedAlgebraInclusion_preservesOne
    (regularModule D.weightZeroDifferentialGradedAlgebra)

/-- The underlying complex of `Ω^•_{L^⋆/S,0}` as a right differential graded `Ω^•_{X/S}`-module is
the middle term of the residue sequence. -/
theorem Situation.weightZeroDifferentialGradedModule_complex :
    D.weightZeroDifferentialGradedModule.complex = D.residueBaseSequence.middle :=
  rfl

/-- **The pullback of forms `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` as a map of right differential graded
`Ω^•_{X/S}`-modules.** -/
def Situation.inclusionDifferentialGradedModuleHom :
    regularModule (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))) ⟶
      D.weightZeroDifferentialGradedModule where
  toHomologicalComplex := D.residueBaseSequence.incl
  map_mul n i U x y := D.weightZeroDifferentialGradedAlgebraInclusion.map_mul n i U x y

/-! ### The residue in each degree -/

/-- The residue `Ω^{k+1}_{L^⋆/S,0} ⟶ Ω^k_{X/S}` of the shifted residue sequence, in degree `k`:
the residue map of Tag 0FUF followed by the identification `Ω^•_{X/S}[-1][1] ≅ Ω^•_{X/S}`. -/
def Situation.residueShiftF (k : ℤ) :
    D.residueBaseSequence.middle.X (k + 1) ⟶
      (deRhamComplexInt.{u} (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).X k :=
  D.residueBaseSequence.res.f (k + 1) ≫
    ((Stacks.ShiftedBoundary.Sequence.unshiftIso (deRhamComplexInt.{u}
      (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))).hom).f k

/-- A morphism conjugated by transports along equalities of objects is heterogeneously the
morphism. -/
private theorem eqToHom_conj_heq {C : Type*} [Category* C] {P P₁ Q Q₁ Q₂ Q₃ : C}
    (h₁ : P = P₁) (φ : P₁ ⟶ Q) (h₂ : Q = Q₁) (h₃ : Q₁ = Q₂) (h₄ : Q₂ = Q₃) :
    HEq ((eqToHom h₁ ≫ φ ≫ eqToHom h₂) ≫ eqToHom h₃ ≫ eqToHom h₄) φ := by
  subst h₁ h₂ h₃ h₄
  simp

private theorem extendXIso_hom_eq {C : Type*} [Category* C] [Limits.HasZeroObject C]
    [Limits.HasZeroMorphisms C] (K : CochainComplex C ℕ) {i : ℕ} {i' : ℤ}
    (h : embeddingUpNat.f i = i') :
    (K.extendXIso embeddingUpNat h).hom = eqToHom (congrArg (HomologicalComplex.extend.X K)
      (embeddingUpNat.r_eq_some h)) :=
  rfl

private theorem extendXIso_inv_eq {C : Type*} [Category* C] [Limits.HasZeroObject C]
    [Limits.HasZeroMorphisms C] (K : CochainComplex C ℕ) {i : ℕ} {i' : ℤ}
    (h : embeddingUpNat.f i = i') :
    (K.extendXIso embeddingUpNat h).inv = eqToHom (congrArg (HomologicalComplex.extend.X K)
      (embeddingUpNat.r_eq_some h)).symm :=
  rfl

private theorem XIsoOfEq_hom_eq {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    (K : CochainComplex C ℤ) {p q : ℤ} (h : p = q) :
    (K.XIsoOfEq h).hom = eqToHom (congrArg K.X h) :=
  rfl

/-- In degree `p + 1` the residue map of the residue sequence is `Res : Ω^{p+1}_{L^⋆/S,0} ⟶
Ω^p_{X/S}`, conjugated by the identifications of the extended complexes in that degree. -/
theorem Situation.residueBaseSequence_res_f_natCast (p : ℕ) :
    D.residueBaseSequence.res.f ((p + 1 : ℕ) : ℤ) =
      (HomologicalComplex.extendXIso D.weightZeroBaseComplex embeddingUpNat
          (i := p + 1) rfl).hom ≫
        (Scheme.Hom.toBaseModules D.f).map (D.residueHom p) ≫
        (HomologicalComplex.extendXIso (Scheme.Hom.deRhamComplex D.f) embeddingUpNat (i := p)
          (show embeddingUpNat.f p = ((p + 1 : ℕ) : ℤ) + -1 by
            simp only [embeddingUpNat_f]; omega)).inv := by
  show (HomologicalComplex.extendMap D.residueBaseMap embeddingUpNat).f ((p + 1 : ℕ) : ℤ) ≫
      (CochainComplex.desuspendExtendIso (Scheme.Hom.deRhamComplex D.f)).hom.f
        ((p + 1 : ℕ) : ℤ) = _
  refine (congrArg (· ≫ _) (HomologicalComplex.extendMap_f D.residueBaseMap embeddingUpNat
    (i := p + 1) (i' := ((p + 1 : ℕ) : ℤ)) rfl)).trans ?_
  simp only [CochainComplex.desuspendExtendIso, HomologicalComplex.extendUpNatIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, HomologicalComplex.extendUpNatXIso_natCast,
    Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **In degree `p` the residue of the shifted residue sequence is `Res : Ω^{p+1}_{L^⋆/S,0} ⟶
Ω^p_{X/S}`.** -/
theorem Situation.residueShiftF_natCast_heq (p : ℕ) :
    HEq (D.residueShiftF (p : ℤ)) ((Scheme.Hom.toBaseModules D.f).map (D.residueHom p)) := by
  have h : D.residueShiftF (p : ℤ) = D.residueBaseSequence.res.f ((p + 1 : ℕ) : ℤ) ≫
      ((Stacks.ShiftedBoundary.Sequence.unshiftIso (deRhamComplexInt.{u}
        (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))).hom).f (p : ℤ) := rfl
  rw [h, D.residueBaseSequence_res_f_natCast]
  simp only [Stacks.ShiftedBoundary.Sequence.unshiftIso, Iso.app_hom, shiftFunctorCompIsoId,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorZero_hom_app_f]
  rw [extendXIso_hom_eq, extendXIso_inv_eq, XIsoOfEq_hom_eq, XIsoOfEq_hom_eq]
  exact eqToHom_conj_heq _ _ _ _ _

/-- The zero sections of equal sheaves of modules are heterogeneously equal. -/
private theorem zero_heq_of_eq {R : Sheaf (Opens.grothendieckTopology D.X.carrier) RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (h : M = N) (U : D.X.Opensᵒᵖ) :
    HEq (0 : M.val.obj U) (0 : N.val.obj U) := by
  subst h
  rfl

/-- **`Res(x ∧ π^*α) = Res(x) ∧ α` in the extended complexes**: the residue of the shifted residue
sequence commutes with the right action of `Ω^•_{X/S}`. -/
theorem Situation.residueShiftF_mul (m i : ℤ) (U : D.X.Opensᵒᵖ)
    (y : (D.weightZeroDifferentialGradedAlgebra.complex.X (m + 1)).val.obj U)
    (a : ((deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).complex.X i).val.obj U) :
    (D.residueShiftF (m + i)).val.app U
        (_root_.SheafOfModules.castHom D.weightZeroDifferentialGradedAlgebra.complex.X
          (add_right_comm m 1 i) U
          ((D.weightZeroDifferentialGradedAlgebra.mul (m + 1) i).app U y
            ((D.weightZeroDifferentialGradedAlgebraInclusion.toHomologicalComplex.f i).val.app U
              a))) =
      ((deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).mul m i).app U
          ((D.residueShiftF m).val.app U y) a := by
  by_cases hm : 0 ≤ m
  · by_cases hi : 0 ≤ i
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      obtain ⟨b, hb, y', hy⟩ := D.exists_heq_weightZero ((p : ℤ) + 1) (by omega) U y
      obtain rfl : b = p + 1 := by omega
      obtain ⟨a', ha⟩ := Scheme.Hom.exists_heq_deRhamPiece D.f (q : ℤ) hi U a
      have hφa := D.residueBaseSequence_incl_f_app_heq (q : ℤ) q rfl U a a' ha
      have hmul := D.weightZeroMul_app_heq ((p : ℤ) + 1) (q : ℤ) (p + 1) q hb rfl U y _ y' _ hy hφa
      have hcast := (_root_.SheafOfModules.heq_castHom _ (add_right_comm (p : ℤ) 1 q) U _).trans
        (hmul.trans (D.weightZeroCast_heq (Nat.add_right_comm p 1 q) _).symm)
      have hL := D.sheafHom_app_heq (D.weightZeroBaseComplexInt_X_natCast (p + q + 1))
        (Scheme.Hom.deRhamComplexInt_X_natCast D.f (p + q)) _ _
        (D.residueShiftF_natCast_heq (p + q)) U _ _ hcast
      have hρ := D.sheafHom_app_heq (D.weightZeroBaseComplexInt_X_natCast (p + 1))
        (Scheme.Hom.deRhamComplexInt_X_natCast D.f p) _ _
        (D.residueShiftF_natCast_heq p) U _ _ hy
      have hR := deRhamDifferentialGradedAlgebra_mul (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) p q U _ a _ a' hρ.symm ha
      refine eq_of_heq (hL.symm.trans ((heq_of_eq (D.residueHom_weightZeroWedge p q U.unop y'
        a')).trans hR.symm))
    · have ha0 := Scheme.Hom.deRhamComplexInt_section_eq_zero' D.f i (by omega) U a
      have h0 : (D.weightZeroDifferentialGradedAlgebraInclusion.toHomologicalComplex.f i).val.app U
          a = 0 := by rw [ha0]; exact map_zero _
      refine Eq.trans ?_ (D.bilinearMap_app_eq_zero_right _ U _ ha0).symm
      rw [D.bilinearMap_app_eq_zero_right _ U y h0]
      simp only [map_zero]
      exact map_zero _
  · by_cases hm1 : m = -1
    · subst hm1
      have hR : ((deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).mul (-1) i).app U
            ((D.residueShiftF (-1)).val.app U y) a = 0 :=
        D.bilinearMap_app_eq_zero_left _ U a
          (Scheme.Hom.deRhamComplexInt_section_eq_zero' D.f (-1) (by omega) U _)
      rw [hR]
      by_cases hi : 1 ≤ i
      · obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = ((q + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
        obtain ⟨b, hb, y', hy⟩ := D.exists_heq_weightZero ((-1 : ℤ) + 1) (by omega) U y
        obtain rfl : b = 0 := by omega
        obtain ⟨a', ha⟩ := Scheme.Hom.exists_heq_deRhamPiece D.f ((q + 1 : ℕ) : ℤ) (by omega) U a
        have hφa := D.residueBaseSequence_incl_f_app_heq _ (q + 1) rfl U a a' ha
        have hmul := D.weightZeroMul_app_heq ((-1 : ℤ) + 1) ((q + 1 : ℕ) : ℤ) 0 (q + 1) hb rfl U
          y _ y' _ hy hφa
        have hcast := (_root_.SheafOfModules.heq_castHom _
          (add_right_comm (-1 : ℤ) 1 ((q + 1 : ℕ) : ℤ)) U _).trans
            (hmul.trans (D.weightZeroCast_heq (Nat.zero_add (q + 1)) _).symm)
        have hk : (-1 : ℤ) + ((q + 1 : ℕ) : ℤ) = (q : ℤ) := by push_cast; ring
        have hρ : HEq (D.residueShiftF ((-1 : ℤ) + ((q + 1 : ℕ) : ℤ)))
            ((Scheme.Hom.toBaseModules D.f).map (D.residueHom q)) := by
          rw [hk]
          exact D.residueShiftF_natCast_heq q
        have hX₁ : D.residueBaseSequence.middle.X ((-1 : ℤ) + ((q + 1 : ℕ) : ℤ) + 1) =
            (Scheme.Hom.toBaseModules D.f).obj (D.weightZero (q + 1)) := by
          rw [hk]
          exact D.weightZeroBaseComplexInt_X_natCast (q + 1)
        have hX₂ : (deRhamComplexInt.{u} (Scheme.Hom.deRhamAlgebras D.f)
            (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).X
              ((-1 : ℤ) + ((q + 1 : ℕ) : ℤ)) =
            (Scheme.Hom.toBaseModules D.f).obj
              (Scheme.Hom.relativeDifferentialForms D.f (q : ℤ)) := by
          rw [hk]
          exact Scheme.Hom.deRhamComplexInt_X_natCast D.f q
        have hL := D.sheafHom_app_heq hX₁ hX₂ _ _ hρ U _ _ hcast
        exact eq_of_heq (hL.symm.trans ((heq_of_eq (D.residueHom_weightZeroWedge_zero q U.unop y'
          a')).trans (zero_heq_of_eq D hX₂.symm U)))
      · exact Scheme.Hom.deRhamComplexInt_section_eq_zero' D.f _ (by omega) U _
    · have hy0 := D.weightZeroBaseComplexInt_section_eq_zero (m + 1) (by omega) U y
      have h1 : (D.residueShiftF m).val.app U y = 0 := by rw [hy0]; exact map_zero _
      refine Eq.trans ?_ (D.bilinearMap_app_eq_zero_left _ U a h1).symm
      rw [D.bilinearMap_app_eq_zero_left _ U _ hy0]
      simp only [map_zero]
      exact map_zero _

/-- **The residue `Ω^•_{L^⋆/S,0}[1] ⟶ Ω^•_{X/S}` as a map of right differential graded
`Ω^•_{X/S}`-modules**: the second map of the shifted residue sequence. It commutes with the action
because `Res(x ∧ π^*α) = Res(x) ∧ α` (`Stacks.LineBundle.Situation.residueShiftF_mul`). -/
def Situation.residueDifferentialGradedModuleHom :
    shift D.weightZeroDifferentialGradedModule ⟶
      regularModule (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))) where
  toHomologicalComplex :=
    eqToHom (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex ≫
      D.residueBaseSequence.res⟦(1 : ℤ)⟧' ≫
      (Stacks.ShiftedBoundary.Sequence.unshiftIso (deRhamComplexInt.{u}
        (Scheme.Hom.deRhamAlgebras D.f) (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))).hom
  map_mul n i U x a := by
    change (D.residueShiftF (n + i)).val.app U
        (((shiftPackage D.weightZeroDifferentialGradedModule).xIso (n + i)).hom.val.app U
          (((shift D.weightZeroDifferentialGradedModule).mul n i).app U x a)) =
      ((deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).mul n i).app U
          ((D.residueShiftF n).val.app U
            (((shiftPackage D.weightZeroDifferentialGradedModule).xIso n).hom.val.app U x)) a
    rw [(shiftPackage D.weightZeroDifferentialGradedModule).xIso_mul n i U x a]
    exact D.residueShiftF_mul n i U _ a

/-! ### The shifted residue sequence of right differential graded modules -/

private theorem comp_eq_zero_of_conj {C : Type*} [Category* C] [Preadditive C]
    {P P' Q Q' R T : C} (h₁ : P' = P) (i : P ⟶ Q) (h₂ : Q = Q') (h₃ : Q' = Q) (r : Q ⟶ R)
    (t : R ⟶ T) (hir : i ≫ r = 0) :
    (eqToHom h₁ ≫ i ≫ eqToHom h₂) ≫ eqToHom h₃ ≫ r ≫ t = 0 := by
  subst h₁ h₂
  simp [reassoc_of% hir]

/-- The shift of the pullback of forms `Ω^•_{X/S}[1] ⟶ Ω^•_{L^⋆/S,0}[1]` is, on underlying
complexes, the shift of the first map of the residue sequence, up to the identifications of the
shifted complexes. -/
theorem Situation.coneShiftHom_inclusionDifferentialGradedModuleHom :
    (coneShiftHom D.inclusionDifferentialGradedModuleHom).toHomologicalComplex =
      eqToHom (shiftPackage (regularModule (deRhamDifferentialGradedAlgebra
          (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))).shifted_complex ≫
        D.residueBaseSequence.incl⟦(1 : ℤ)⟧' ≫
        eqToHom (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex.symm :=
  rfl

/-- The composite `Ω^•_{X/S}[1] ⟶ Ω^•_{L^⋆/S,0}[1] ⟶ Ω^•_{X/S}` of the pullback of forms and the
residue is zero. -/
theorem Situation.coneShiftHom_comp_residueDifferentialGradedModuleHom :
    coneShiftHom D.inclusionDifferentialGradedModuleHom ≫ D.residueDifferentialGradedModuleHom =
      0 := by
  refine Hom.ext fun n => ?_
  have h : (coneShiftHom D.inclusionDifferentialGradedModuleHom).toHomologicalComplex ≫
      D.residueDifferentialGradedModuleHom.toHomologicalComplex = 0 := by
    show (eqToHom (shiftPackage (regularModule (deRhamDifferentialGradedAlgebra
          (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))).shifted_complex ≫
        D.residueBaseSequence.incl⟦(1 : ℤ)⟧' ≫
        eqToHom (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex.symm) ≫
      (eqToHom (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex ≫
        D.residueBaseSequence.res⟦(1 : ℤ)⟧' ≫
        (Stacks.ShiftedBoundary.Sequence.unshiftIso (deRhamComplexInt.{u}
          (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))).hom) = 0
    exact comp_eq_zero_of_conj _ _ _ _ _ _ ((Functor.map_comp _ _ _).symm.trans
      ((congrArg _ D.residueBaseSequence.incl_comp_res).trans (Functor.map_zero _ _ _)))
  exact congrArg (fun φ => φ.f n) h

/-- **Stacks Tag 0FUF, shifted, as a short complex of right differential graded
`Ω^•_{X/S}`-modules**: `0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0`, the pullback of
forms and the residue. -/
def Situation.residueDifferentialGradedSequence :
    ShortComplex (_root_.SheafOfModules.DifferentialGradedModule.{u, u, u}
      (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))) :=
  ShortComplex.mk (coneShiftHom D.inclusionDifferentialGradedModuleHom)
    D.residueDifferentialGradedModuleHom D.coneShiftHom_comp_residueDifferentialGradedModuleHom

/-- A transport and its inverse cancel in front of a conjugated morphism. -/
theorem eqToHom_comp_eqToHom_comp {C : Type*} [Category* C] {P P' Q Q' : C}
    (h₁ : P = P') (h₁' : P' = P) (i : P ⟶ Q) (h₂ : Q = Q') :
    eqToHom h₁ ≫ eqToHom h₁' ≫ i ≫ eqToHom h₂ = i ≫ eqToHom h₂ := by
  subst h₁
  simp

/-- A transport and its inverse cancel. -/
theorem eqToHom_comp_eqToHom_comp' {C : Type*} [Category* C] {P P' Q : C}
    (h₁ : P = P') (h₁' : P' = P) (g : P ⟶ Q) :
    eqToHom h₁ ≫ eqToHom h₁' ≫ g = g ≫ 𝟙 Q := by
  subst h₁
  simp

/-- The shifted residue sequence of complexes of Tag 0FUF is the underlying sequence of complexes
of the shifted residue sequence of right differential graded modules. -/
def Situation.residueShiftedSequenceIso :
    D.residueShiftedSequence.shortComplex ≅
      D.residueDifferentialGradedSequence.map
        (_root_.SheafOfModules.toCochainComplex (deRhamDifferentialGradedAlgebra
          (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))) :=
  ShortComplex.isoMk
    (eqToIso (shiftPackage (regularModule (deRhamDifferentialGradedAlgebra
      (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))).shifted_complex.symm)
    (eqToIso (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex.symm)
    (Iso.refl _)
    (eqToHom_comp_eqToHom_comp (shiftPackage (regularModule (deRhamDifferentialGradedAlgebra
      (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))).shifted_complex.symm
      (shiftPackage (regularModule (deRhamDifferentialGradedAlgebra
      (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))).shifted_complex
      (D.residueBaseSequence.incl⟦(1 : ℤ)⟧')
      (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex.symm)
    (eqToHom_comp_eqToHom_comp'
      (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex.symm
      (shiftPackage D.weightZeroDifferentialGradedModule).shifted_complex
      (D.residueBaseSequence.res⟦(1 : ℤ)⟧' ≫
        (Stacks.ShiftedBoundary.Sequence.unshiftIso (deRhamComplexInt.{u}
          (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))).hom))

/-- **The shifted residue sequence of right differential graded modules is short exact**: its
underlying sequence of complexes is the shifted residue sequence of Tag 0FUF, and forgetting the
action is faithful and exact. -/
theorem Situation.residueDifferentialGradedSequence_shortExact :
    D.residueDifferentialGradedSequence.ShortExact :=
  CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (_root_.SheafOfModules.toCochainComplex (deRhamDifferentialGradedAlgebra
      (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
    (ShortComplex.shortExact_of_iso D.residueShiftedSequenceIso D.residueShiftedSequence.shortExact)

/-! ### The boundary map lifts -/

/-- **The boundary map `δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` of the shifted residue sequence of Tag 0FUF
comes from a morphism `δ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` of the derived category `D(Ω^•_{X/S}, d)` of
right differential graded modules over the de Rham complex**: this is the first half of the proof
of Stacks Tag 0FUG. The morphism is the connecting morphism of Tag 0FTB of the shifted residue
sequence of right differential graded `Ω^•_{X/S}`-modules, followed by the identification
`Ω^•_{X/S}[1][1] ≅ Ω^•_{X/S}[2]`; forgetting the action commutes with connecting morphisms. -/
theorem Situation.exists_deRhamForgetHom_eq_residueShiftedSequence_boundary :
    ∃ g : deRhamDerivedRegular (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) ⟶
        (deRhamDerivedRegular (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))⟦(2 : ℤ)⟧,
      deRhamForgetHom _ _ 2 g = D.residueShiftedSequence.boundary := by
  have hS := D.residueDifferentialGradedSequence_shortExact
  have hX := (HomotopyCategory.shiftFunctor_obj (X := baseSite _) _
    (regularModule (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))).symm
  refine ⟨shortExactδTwo (X := baseSite _) _ hS _ hX, ?_⟩
  have h7 := derivedForget_map_shortExactδTwo (X := baseSite _) _ hS
    (regularModule (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))) hX
    (shiftPackage (regularModule (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))).shifted_complex
  have hnat := DerivedCategory.triangleOfSESδ_naturality
    (toCochainComplex_shortExact _ _ hS) D.residueShiftedSequence.shortExact
    D.residueShiftedSequenceIso.inv
  have hτ : DerivedCategory.Q.map D.residueShiftedSequenceIso.inv.τ₃ = 𝟙 _ :=
    DerivedCategory.Q.map_id _
  rw [hτ] at hnat
  exact h7.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (hnat.trans (Category.id_comp _))))

end Stacks.LineBundle
