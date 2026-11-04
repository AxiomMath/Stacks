module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.Homology.HomComplex.Evaluation
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.TensorHom
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.Perfect.Defs

/-!
# K-flat Hom complexes out of perfect complexes of projectives

Let `P` be a bounded above cochain complex of projective `R`-modules which is perfect as an
object of the derived category `D(R)`, and let `K` be a K-flat complex of `R`-modules. Then the
Hom complex `Hom^•(P, K)` is K-flat, and it represents `RHom_R(P, K)`.

## Main results

* `Stacks.DerivedHom.KFlatHomComplex.homComplex_kFlat_and_represents_RHom`: for `P` bounded above
  with projective terms
  and perfect in `D(R)`, and `K` K-flat, the complex `Hom^•(P, K)` is K-flat and the canonical
  map from its degree-`n` cohomology classes to `Hom_{D(R)}(P, K⟦n⟧)` is bijective for every `n`.

## References

* [Stacks Project, Tag 0BYQ](https://stacks.math.columbia.edu/tag/0BYQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Stacks.DerivedHom.KFlatHomComplex

universe u w

/-! ### Transfer of K-flatness along homotopy equivalences -/

private noncomputable def tensorLeftHomotopyEquiv {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv P Q) :
    HomotopyEquiv ((tensorLeft K).obj P) ((tensorLeft K).obj Q) where
  hom := (tensorLeft K).map e.hom
  inv := (tensorLeft K).map e.inv
  homotopyHomInvId := by
    rw [← (tensorLeft K).map_comp, ← (tensorLeft K).map_id]
    exact HomologicalComplex.mapBifunctorMapHomotopy₂
      (K₁ := K) (L₁ := K) (K₂ := P) (L₂ := P) (f₁ := 𝟙 K) e.homotopyHomInvId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)
  homotopyInvHomId := by
    rw [← (tensorLeft K).map_comp, ← (tensorLeft K).map_id]
    exact HomologicalComplex.mapBifunctorMapHomotopy₂
      (K₁ := K) (L₁ := K) (K₂ := Q) (L₂ := Q) (f₁ := 𝟙 K) e.homotopyInvHomId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)

/-- A cochain complex homotopy equivalent to an acyclic complex is acyclic. -/
lemma acyclic_of_homotopyEquiv
    {C : Type*} [Category* C] [Abelian C] {K L : CochainComplex C ℤ} (e : HomotopyEquiv K L)
    (hK : K.Acyclic) : L.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (e.toHomologyIso n).isZero_iff.mp (hK n).isZero_homology

/-- A cochain complex of `R`-modules homotopy equivalent to a K-flat complex is K-flat. -/
lemma kFlat_of_homotopyEquiv {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv K L)
    (hK : K.KFlat) : L.KFlat := by
  intro M hM
  exact acyclic_of_homotopyEquiv (tensorLeftHomotopyEquiv M e) (hK M hM)

private lemma exists_homotopyEquiv_of_derived_iso
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P L : CochainComplex C ℤ) [P.IsKProjective] [L.IsKProjective]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj L) :
    Nonempty (HomotopyEquiv P L) := by
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ e.hom ≫
      (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective β
  have hf : DerivedCategory.Q.map f = e.hom := by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := C) f
    rw [hβ] at h
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
    exact ((cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P)).1 h).symm
  have : IsIso (DerivedCategory.Q.map f) := by
    rw [hf]
    infer_instance
  have : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso C f).mp inferInstance
  obtain ⟨h, _⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  exact ⟨h⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homComplexPrecompHomotopy
    {R : Type u} [CommRing R] {A B K : CochainComplex (ModuleCat.{u} R) ℤ}
    {f g : A ⟶ B} (ho : Homotopy f g) :
    Homotopy (Stacks.HomComplex.TensorHomComparison.HomCxMap B A K K f (𝟙 K))
      (Stacks.HomComplex.TensorHomComparison.HomCxMap B A K K g (𝟙 K)) := by
  let s := CochainComplex.HomComplex.Cochain.ofHomotopy ho
  refine
    { hom := fun i j ↦ if hij : j + 1 = i then ModuleCat.ofHom
        { toFun := fun z ↦ i.negOnePow • s.comp z (by omega)
          map_add' _ _ := by simp [CochainComplex.HomComplex.Cochain.comp_add]
          map_smul' := by
            intros
            rw [CochainComplex.HomComplex.Cochain.comp_smul]
            exact smul_comm i.negOnePow _ _ } else 0
      zero := fun i j hij ↦ by exact dite_eq_right hij
      comm := fun i ↦ ?_ }
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)]
  simp only [dite_true, dite_eq_left (show i - 1 + 1 = i by omega)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change Stacks.HomComplex.TensorHomComparison.HomCxMapDeg B A K K f (𝟙 K) i z =
    (i + 1).negOnePow • s.comp (CochainComplex.HomComplex.δ i (i + 1) z) (by omega) +
    CochainComplex.HomComplex.δ (i - 1) i (i.negOnePow • s.comp z (by omega)) +
    Stacks.HomComplex.TensorHomComparison.HomCxMapDeg B A K K g (𝟙 K) i z
  rw [CochainComplex.HomComplex.δ_units_smul,
    CochainComplex.HomComplex.δ_comp s z (by omega) 0 (i + 1) i
    (by omega) (by omega) (by omega), CochainComplex.HomComplex.δ_ofHomotopy ho]
  simp only [Int.negOnePow_succ, Units.neg_smul, smul_add, smul_smul,
    Int.units_mul_self, one_smul, neg_add_cancel_left,
    CochainComplex.HomComplex.Cochain.sub_comp]
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  simp only [Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v,
    CochainComplex.HomComplex.Cochain.add_v,
    CochainComplex.HomComplex.Cochain.sub_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.comp_id, sub_add_cancel]

private lemma homComplex_kFlat_of_homotopyEquiv
    {R : Type u} [CommRing R] {P Q K : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv P Q) (h : (CochainComplex.HomComplexR R Q K).KFlat) :
    (CochainComplex.HomComplexR R P K).KFlat := by
  let he : HomotopyEquiv (CochainComplex.HomComplexR R Q K)
      (CochainComplex.HomComplexR R P K) :=
    { hom := Stacks.HomComplex.TensorHomComparison.HomCxMap Q P K K e.hom (𝟙 K)
      inv := Stacks.HomComplex.TensorHomComparison.HomCxMap P Q K K e.inv (𝟙 K)
      homotopyHomInvId := by
        rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp]
        exact (homComplexPrecompHomotopy e.homotopyInvHomId).trans
          (Homotopy.ofEq (Stacks.HomComplex.TensorHomComparison.HomCxMap_id Q K))
      homotopyInvHomId := by
        rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp]
        exact (homComplexPrecompHomotopy e.homotopyHomInvId).trans
          (Homotopy.ofEq (Stacks.HomComplex.TensorHomComparison.HomCxMap_id P K)) }
  exact kFlat_of_homotopyEquiv he h

end Stacks.DerivedHom.KFlatHomComplex

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CochainComplex
  CochainComplex.HomComplex ChainEvaluation

namespace Stacks.DerivedHom.KFlatHomComplex

universe u w

variable {R : Type u} [CommRing R]

/-! ### Acyclicity of the Hom complex out of a K-projective complex

Mathlib's `CochainComplex.IsKProjective` is Spaltenstein's condition that every morphism to an
acyclic complex is homotopic to zero.  Applied to the shifts of an acyclic complex, it says that
every cocycle of the Hom complex is a coboundary, i.e. that the Hom complex is acyclic. -/

private lemma acyclic_shift {M : CochainComplex (ModuleCat.{u} R) ℤ} (hM : M.Acyclic) (n : ℤ) :
    (M⟦n⟧).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hM ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).commShiftIso n).symm.app M)
    ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).le_shift n _ hM)

private lemma homComplex_acyclic_of_isKProjective
    (Q M : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKProjective] (hM : M.Acyclic) :
    (HomComplexR R Q M).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hzero : CohomologyClass.toHom (CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz)) = 0 := by
    rw [CohomologyClass.toHom_mk, HomotopyCategory.eq_of_homotopy _ 0
      (CochainComplex.IsKProjective.homotopyZero _ (acyclic_shift hM n))]
    exact Functor.map_zero _ _ _
  rw [CohomologyClass.toHom_mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hzero
  exact hzero

/-! ### The Hom complex out of the unit complex

The monoidal unit of `CochainComplex (ModuleCat R) ℤ` is the complex `R[0]`, so a degree-`n`
cochain from it to `I` is just an element of `I^n`, compatibly with the differentials. -/

private lemma isZero_unit_X (i : ℤ) (hi : i ≠ 0) :
    Limits.IsZero ((𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).X i) :=
  HomologicalComplex.isZero_single_obj_X _ 0 _ i hi

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at `1 ∈ R` identifies morphisms out of the monoidal unit of `ModuleCat R`
with elements. -/
private noncomputable def unitHomEquiv (M : ModuleCat.{u} R) :
    (𝟙_ (ModuleCat.{u} R) ⟶ M) ≃ M where
  toFun f := f.hom (1 : R)
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • f.hom (1 : R) = f.hom r
    rw [← map_smul]
    simp
  right_inv x := one_smul R x

set_option backward.isDefEq.respectTransparency false in
/-- A degree-`n` cochain from the unit complex to `I`, evaluated at `1 ∈ R`. -/
private noncomputable def unitEvalLin (I : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) I n →ₗ[R] I.X n where
  toFun z := unitHomEquiv _ (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat.{u} R)) (zero_add n) z)
  map_add' z z' := by
    simp only [Cochain.fromSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, unitHomEquiv,
      Cochain.add_v, Preadditive.comp_add, ModuleCat.hom_add, LinearMap.add_apply]
  map_smul' r z := by
    simp only [Cochain.fromSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, unitHomEquiv,
      Cochain.smul_v, Linear.comp_smul, ModuleCat.hom_smul, LinearMap.smul_apply,
      RingHom.id_apply]

private lemma unitEvalLin_bijective (I : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Function.Bijective (unitEvalLin I n) :=
  (unitHomEquiv _).bijective.comp
    (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat.{u} R)) (zero_add n)).bijective

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism `Hom^•(R[0], I) ⟶ I`, evaluation at `1`. -/
private noncomputable def unitEval (I : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomComplexR R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) I ⟶ I :=
  HomologicalComplex.Hom.mk (fun n => ModuleCat.ofHom (unitEvalLin I n)) (by
    rintro i j rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hd : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).d 0 1 = 0 :=
      (isZero_unit_X (R := R) 1 (by omega)).eq_of_tgt _ _
    change (I.d i (i + 1)).hom (unitEvalLin I i z) = unitEvalLin I (i + 1) (δ i (i + 1) z)
    simp only [unitEvalLin, LinearMap.coe_mk, AddHom.coe_mk, Cochain.fromSingleEquiv,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, unitHomEquiv]
    rw [δ_v i (i + 1) rfl z 0 (i + 1) (by omega) i 1 (by omega) (by omega), hd]
    simp)

/-- `Hom^•(R[0], I) ≅ I`. -/
private noncomputable def unitHomIso (I : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomComplexR R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) I ≅ I :=
  have (n : ℤ) : IsIso ((unitEval I).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (unitEvalLin_bijective I n)
  have : IsIso (unitEval I) := HomologicalComplex.Hom.isIso_of_components _
  asIso (unitEval I)

/-! ### The dual complex

For `Q` a bounded complex of finite projective modules, the complex `Hom^•(Q, R[0])` is again
bounded with finite projective terms: its degree-`n` term is the linear dual of `Q^{-n}`. -/

set_option backward.isDefEq.respectTransparency false in
/-- Degree-`n` cochains from `Q` to the unit complex are the linear dual of `Q^{-n}`. -/
private noncomputable def dualCochainEquiv (Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) n ≃ₗ[R] Module.Dual R (Q.X (-n)) where
  toFun z := (Cochain.toSingleEquiv (X := 𝟙_ (ModuleCat.{u} R)) (p := -n) (by omega) z).hom
  invFun f := (Cochain.toSingleEquiv (X := 𝟙_ (ModuleCat.{u} R)) (p := -n)
    (show -n + n = 0 by omega)).symm (ModuleCat.ofHom f)
  left_inv z := by simp
  right_inv f := by simp
  map_add' z z' := by
    simp only [Cochain.toSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, Cochain.add_v,
      Preadditive.add_comp, ModuleCat.hom_add]
  map_smul' r z := by
    simp only [Cochain.toSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, Cochain.smul_v,
      Linear.smul_comp, ModuleCat.hom_smul, RingHom.id_apply]

private lemma dual_X_finite (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Finite R (Q.X i)] [∀ i, Module.Projective R (Q.X i)] (n : ℤ) :
    Module.Finite R ((HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).X n) :=
  Module.Finite.equiv (dualCochainEquiv Q n).symm

private lemma dual_X_projective (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Finite R (Q.X i)] [∀ i, Module.Projective R (Q.X i)] (n : ℤ) :
    Module.Projective R ((HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).X n) :=
  Module.Projective.of_equiv (dualCochainEquiv Q n).symm

private lemma dual_isZero_X (Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hQ : Limits.IsZero (Q.X (-n))) :
    Limits.IsZero ((HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).X n) := by
  have : Subsingleton (Q.X (-n)) := ModuleCat.isZero_iff_subsingleton.mp hQ
  have : Subsingleton (Module.Dual R (Q.X (-n))) :=
    ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (Function.Injective.subsingleton (dualCochainEquiv Q n).injective)

private lemma dual_isStrictlyGE (Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] :
    (HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).IsStrictlyGE (-b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => dual_isZero_X Q i (Q.isZero_of_isStrictlyLE b (-i) (by omega))

private lemma dual_isStrictlyLE (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    [Q.IsStrictlyGE a] :
    (HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).IsStrictlyLE (-a) := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => dual_isZero_X Q i (Q.isZero_of_isStrictlyGE a (-i) (by omega))

/-! ### The evaluation isomorphism `A ⊗ Q^∨ ≅ Hom^•(Q, A)` -/

/-- The Hom complex is contravariantly functorial in its first argument. -/
private noncomputable def homCxIsoOfIsoLeft {M M' : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : M' ≅ M) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomComplexR R M L ≅ HomComplexR R M' L where
  hom := Stacks.HomComplex.TensorHomComparison.HomCxMap M M' L L e.hom (𝟙 L)
  inv := Stacks.HomComplex.TensorHomComparison.HomCxMap M' M L L e.inv (𝟙 L)
  hom_inv_id := by
    rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, e.inv_hom_id, Category.comp_id,
      Stacks.HomComplex.TensorHomComparison.HomCxMap_id]
  inv_hom_id := by
    rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, e.hom_inv_id, Category.comp_id,
      Stacks.HomComplex.TensorHomComparison.HomCxMap_id]

/-- Reflexivity: a bounded complex of finite projective modules is its own double dual. -/
private noncomputable def reflIso (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [Q.IsStrictlyGE a] [Q.IsStrictlyLE b]
    [∀ i, Module.Finite R (Q.X i)] [∀ i, Module.Projective R (Q.X i)] :
    Q ≅ HomComplexR R (HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))
      (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) :=
  have : IsIso (chainEvaluation Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))
      (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) :=
    chainEvaluation_isIso_of_bounded Q _ _ a b
  (λ_ Q).symm ≪≫ whiskerRightIso
      (unitHomIso (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).symm Q ≪≫
    asIso (chainEvaluation Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))
      (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))

/-- For `Q` bounded with finite projective terms and any complex `A`, tensoring `A` with the
dual of `Q` computes the Hom complex out of `Q`. -/
private noncomputable def evalHomIso (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [Q.IsStrictlyGE a] [Q.IsStrictlyLE b]
    [∀ i, Module.Finite R (Q.X i)] [∀ i, Module.Projective R (Q.X i)]
    (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    A ⊗ HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ≅ HomComplexR R Q A :=
  have _hfin (i : ℤ) :
      Module.Finite R ((HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).X i) :=
    dual_X_finite Q i
  have _hproj (i : ℤ) :
      Module.Projective R ((HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))).X i) :=
    dual_X_projective Q i
  have _hGE := dual_isStrictlyGE Q b
  have _hLE := dual_isStrictlyLE Q a
  have : IsIso (chainEvaluation (HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))
      (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) A) :=
    chainEvaluation_isIso_of_bounded _ _ _ (-b) (-a)
  whiskerRightIso (unitHomIso A).symm _ ≪≫
    asIso (chainEvaluation (HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))
      (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) A) ≪≫
    homCxIsoOfIsoLeft (reflIso Q a b) A

/-- For `Q` a bounded complex of finite projective modules and `K` K-flat, `Hom^•(Q, K)` is
K-flat: it is isomorphic to `K ⊗ Q^∨`, and tensoring that with an acyclic complex gives
`Hom^•(Q, -)` of an acyclic complex, which is acyclic because `Q` is K-projective. -/
private lemma homComplex_kFlat_of_bounded (Q K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [Q.IsStrictlyGE a] [Q.IsStrictlyLE b]
    [∀ i, Module.Finite R (Q.X i)] [∀ i, Module.Projective R (Q.X i)]
    (hK : K.KFlat) : (HomComplexR R Q K).KFlat := by
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q b
  refine CochainComplex.KFlat.of_iso (evalHomIso Q a b K) ?_
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso
    ((evalHomIso Q a b (M ⊗ K)).symm ≪≫
      α_ M K (HomComplexR R Q (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))))
    (homComplex_acyclic_of_isKProjective Q (M ⊗ K) (hK M hM))

/-! ### The main result -/

/-- **Stacks 0BYQ.** Let `P` be a bounded above cochain complex of projective `R`-modules which
is perfect as an object of the derived category `D(R)`, and let `K` be a K-flat complex of
`R`-modules.  Then `Hom^•(P, K)` is K-flat, and it represents `RHom_R(P, K)`: for every `n`, the
map sending a degree-`n` cohomology class of `Hom^•(P, K)` to the corresponding morphism
`P ⟶ K⟦n⟧` in `D(R)` is bijective. -/
@[stacks 0BYQ]
theorem homComplex_kFlat_and_represents_RHom [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ i, Module.Projective R (P.X i)]
    (hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P)) (hK : K.KFlat) :
    (HomComplexR R P K).KFlat ∧
      ∀ n : ℤ, Function.Bijective
        (fun (c : CohomologyClass P K n) =>
          DerivedCategory.Qh.map (CohomologyClass.homAddEquiv c)) := by
  refine ⟨?_, fun n => homComplex_represents_RHom P K d n⟩
  obtain ⟨Q, a, b, hQa, hQb, hQfin, hQproj, ⟨eQ⟩⟩ := hP
  have := hQa
  have := hQb
  have (i : ℤ) := hQfin i
  have (i : ℤ) := hQproj i
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q b
  obtain ⟨e⟩ := exists_homotopyEquiv_of_derived_iso P Q eQ
  exact homComplex_kFlat_of_homotopyEquiv e (homComplex_kFlat_of_bounded Q K a b hK)

end Stacks.DerivedHom.KFlatHomComplex

end
