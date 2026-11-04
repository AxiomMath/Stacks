module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalDeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionCrisLeibniz

/-!
# [Stacks, Tag 07IZ] in degree two: exterior products and the de Rham differential

Fix a global crystalline situation of [Stacks, Tag 07MF] and an object `A = (U, T, δ)` of the small
crystalline site.  The comparison `Ω²_{X/S}(A|_W) ⟶ Γ(W, Ω²_{T/S,δ})` of
`...SmallSite.formsComparisonTwo` carries the exterior product `η ∧ ω` of two local sections of
`Ω_{X/S}` to the exterior product of their images in `Ω_{T/S,δ}`, and the de Rham differential of
`Ω^*_{X/S}` to the de Rham differential `d : Ω_{T/S,δ} ⟶ Ω²_{T/S,δ}`.

## Main definitions

* `formsWedge` — the exterior product `η ∧ ω ∈ Ω²_{X/S}(B)` of two sections of `Ω_{X/S}`.

## Main results

* `formsComparisonTwo_formsWedge` — the comparison carries `η ∧ ω` to `η ∧ ω`.

## References

* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- Two base changes of an exterior algebra on a product of two generators. -/
theorem _root_.ExteriorAlgebra.mapₛₗ_mapₛₗ_ι_mul_ι {R₁ R₂ R₃ : Type*} {_ : CommRing R₁}
    {_ : CommRing R₂} {_ : CommRing R₃} {M₁ M₂ M₃ : Type*} {_ : AddCommGroup M₁}
    {_ : AddCommGroup M₂} {_ : AddCommGroup M₃} {_ : Module R₁ M₁} {_ : Module R₂ M₂}
    {_ : Module R₃ M₃} (φ : R₁ →+* R₂) (ψ : R₂ →+* R₃)
    (u : M₁ →ₛₗ[φ] M₂) (w : M₂ →ₛₗ[ψ] M₃) (a b : M₁) :
    ExteriorAlgebra.mapₛₗ ψ w (ExteriorAlgebra.mapₛₗ φ u
        (ExteriorAlgebra.ι R₁ a * ExteriorAlgebra.ι R₁ b)) =
      ExteriorAlgebra.ι R₃ (w (u a)) * ExteriorAlgebra.ι R₃ (w (u b)) := by
  rw [map_mul, map_mul, ExteriorAlgebra.mapₛₗ_ι, ExteriorAlgebra.mapₛₗ_ι,
    ExteriorAlgebra.mapₛₗ_ι, ExteriorAlgebra.mapₛₗ_ι]

/-- **The exterior product `η ∧ ω` of two sections of `Ω_{X/S}`**, a section of `Ω²_{X/S}`. -/
def formsWedge {B : CrystallineThickening S} (η ω : (crysDifferentials S).obj (op B)) :
    (crysDifferentialForms S 2).obj (op B) :=
  (crysFormSections S 2 B).symm ⟨ExteriorAlgebra.ι _ η * ExteriorAlgebra.ι _ ω,
    ExteriorAlgebra.mul_mem_exteriorPower (ExteriorAlgebra.ι_mem_exteriorPower η)
      (ExteriorAlgebra.ι_mem_exteriorPower ω)⟩

/-- The value of `formsWedge η ω` in the exterior algebra is `ι η * ι ω`. -/
@[simp]
theorem crysFormVal_formsWedge {B : CrystallineThickening S}
    (η ω : (crysDifferentials S).obj (op B)) :
    crysFormVal S (formsWedge η ω) = ExteriorAlgebra.ι _ η * ExteriorAlgebra.ι _ ω := rfl

variable (A : CrystallineThickening S)

/-- **The comparison of degree-two forms carries `η ∧ ω` to `η ∧ ω`.** -/
theorem formsComparisonTwo_formsWedge (V : A.obj.thickening.target.scheme.Opens)
    (η ω : (crysDifferentials S).obj (op (A.restrictOpen V))) :
    (formsComparisonTwo A).toFun V (formsWedge η ω) =
      (dpWedge A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app (op V)
        (((restrictedToSheaf A.obj).app (op V)).hom η)
        (((restrictedToSheaf A.obj).app (op V)).hom ω) := by
  refine congrArg ((dpSecondExteriorToSheaf A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom).app (op V)).hom ?_
  apply dpFormVal_injective
  refine Eq.trans ?_ (dpFormVal_wedge _ _ _ (op V) _ _).symm
  exact ExteriorAlgebra.mapₛₗ_mapₛₗ_ι_mul_ι _ _ _ _ η ω


/-- The comparison of degree-one forms on a degree-one generator. -/
theorem formsCompOne_oneGen (V : A.obj.thickening.target.scheme.Opens)
    (y : (crysDifferentials S).obj (op (A.restrictOpen V))) :
    formsCompOne A V ((crysFormsOneGen S).app (op (A.restrictOpen V)) y) =
      ((restrictedToSheaf A.obj).app (op V)).hom y :=
  congrArg ((restrictedToSheaf A.obj).app (op V)).hom
    (crysFormsOneApp_oneGen S (A.restrictOpen V).obj y)

/-- The exterior product with an exact one-form, on a degree-one generator. -/
theorem leftWedge_oneGen {B : CrystallineThickening S} (η y : (crysDifferentials S).obj (op B)) :
    (show (crysDifferentialForms S 2).obj (op B) from
      leftWedge 1 η ((crysFormsOneGen S).app (op B) y)) = formsWedge η y :=
  crysFormVal_injective S rfl

/-- `0 ∧ ω = 0`. -/
theorem formsWedge_zero_left {B : CrystallineThickening S} (y : (crysDifferentials S).obj (op B)) :
    formsWedge 0 y = 0 := by
  apply crysFormVal_injective
  rw [crysFormVal_formsWedge, map_zero, zero_mul]
  rfl

/-- **The de Rham differential `d : Ω^1_{X/S}(B) ⟶ Ω²_{X/S}(B)` of [Stacks, Tag 07J4]**, on the
sections of the presheaves of forms. -/
def formsDeRham (B : CrystallineThickening S) :
    (crysDifferentialForms S 1).obj (op B) →+ (crysDifferentialForms S 2).obj (op B) :=
  crysDeRhamDifferential S 1 B

/-- `d (r d c) = d r ∧ d c`. -/
theorem formsDeRham_smul_d (B : CrystallineThickening S) (r c : crysFormRing S B) :
    formsDeRham B (r • (crysFormsOneGen S).app (op B) (crysD S B c)) =
      formsWedge (crysD S B r) (crysD S B c) := by
  have h := crysDeRhamDifferential_generator S 1 B ![r, c]
  refine Eq.trans ?_ (h.trans ?_)
  · congr 2
    exact (crysFormsOneApp_symm_eq_oneGen S B.obj (crysD S B c)).symm.trans
      (exteriorPower.oneEquiv_symm_apply _ _ _)
  · apply crysFormVal_injective
    rw [crysFormVal_formsWedge]
    show ((exteriorPower.ιMulti (crysFormRing S B) 2 (fun j ↦ crysD S B (![r, c] j)) :
      ⋀[crysFormRing S B]^2 ((crysDifferentials S).obj (op B))) :
        ExteriorAlgebra (crysFormRing S B) ((crysDifferentials S).obj (op B))) = _
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
    simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one]

/-- The inductive step of `formsComparisonTwo_formsDeRham`: the two Leibniz rules agree, so if the
comparison carries `d y` to `d` of the image of `y`, it does the same for `r • y`. -/
theorem formsComparisonTwo_formsDeRham_smul (V : A.obj.thickening.target.scheme.Opens)
    (r : crysFormRing S (A.restrictOpen V)) (y : (crysDifferentials S).obj (op (A.restrictOpen V)))
    (hy : (formsComparisonTwo A).toFun V
        (formsDeRham (A.restrictOpen V) ((crysFormsOneGen S).app (op (A.restrictOpen V)) y)) =
      dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op V)
        (formsCompOne A V ((crysFormsOneGen S).app (op (A.restrictOpen V)) y))) :
    (formsComparisonTwo A).toFun V
        (formsDeRham (A.restrictOpen V) ((crysFormsOneGen S).app (op (A.restrictOpen V)) (r • y))) =
      dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op V)
        (formsCompOne A V ((crysFormsOneGen S).app (op (A.restrictOpen V)) (r • y))) := by
  have e1 : (crysFormsOneGen S).app (op (A.restrictOpen V)) (r • y) =
      r • (crysFormsOneGen S).app (op (A.restrictOpen V)) y :=
    ((crysFormsOneGen S).app (op (A.restrictOpen V))).hom.map_smul r y
  have e2 : formsDeRham (A.restrictOpen V) (r • (crysFormsOneGen S).app (op (A.restrictOpen V)) y) =
      r • formsDeRham (A.restrictOpen V) ((crysFormsOneGen S).app (op (A.restrictOpen V)) y) +
        formsWedge (crysD S (A.restrictOpen V) r) y :=
    (crysDeRhamDifferential_smul S 1 (A.restrictOpen V) r _).trans
      (congrArg (fun z ↦ r • formsDeRham (A.restrictOpen V)
          ((crysFormsOneGen S).app (op (A.restrictOpen V)) y) + z)
        (leftWedge_oneGen (crysD S (A.restrictOpen V) r) y))
  refine (congrArg (fun z ↦ (formsComparisonTwo A).toFun V (formsDeRham (A.restrictOpen V) z))
    e1).trans ?_
  refine (congrArg ((formsComparisonTwo A).toFun V) e2).trans ?_
  refine (map_add _ _ _).trans ?_
  refine (congrArg₂ (· + ·) ((formsComparisonTwo A).map_smul V r _)
    (formsComparisonTwo_formsWedge A V (crysD S (A.restrictOpen V) r) y)).trans ?_
  refine Eq.trans ?_ (congrArg (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom
    (op V)) ((congrArg (formsCompOne A V) e1).trans (formsCompOne_smul A V r _))).symm
  refine Eq.trans ?_ (dpDeRham_smul _ _ _ (op V) (sectionRingEquiv A V r) _).symm
  refine congrArg₂ (· + ·) (congrArg (sectionRingEquiv A V r • ·) hy) ?_
  refine congrArg₂ (fun a b ↦ (dpWedge A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom).app (op V) a b) ?_ (formsCompOne_oneGen A V y).symm
  exact (formsCompOne_oneGen A V (crysD S (A.restrictOpen V) r)).symm.trans
    (formsCompOne_formsD A V r)


/-- **The comparison carries `d_{X/S}` on forms of degree one to `d_{T/S,δ}`.** -/
theorem formsComparisonTwo_formsDeRham (V : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen V))) :
    (formsComparisonTwo A).toFun V (formsDeRham (A.restrictOpen V) ω) =
      dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op V)
        (formsCompOne A V ω) := by
  obtain ⟨ω', rfl⟩ : ∃ ω', (crysFormsOneGen S).app (op (A.restrictOpen V)) ω' = ω :=
    ⟨formsOneEquiv (A.restrictOpen V) ω,
      (crysFormsOneApp_symm_eq_oneGen S (A.restrictOpen V).obj _).symm.trans
        ((formsOneEquiv (A.restrictOpen V)).symm_apply_apply ω)⟩
  have hspan := crysD_span S (A.restrictOpen V).obj
  refine Submodule.span_induction
    (p := fun (ω' : (GlobalCrystallineSituation.crysDifferentials S).obj
        (op (A.restrictOpen V).obj)) _ ↦ (formsComparisonTwo A).toFun V
        (formsDeRham (A.restrictOpen V)
          (((crysFormsOneGen S).app (op (A.restrictOpen V))).hom ω')) =
      dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op V)
        (formsCompOne A V (((crysFormsOneGen S).app (op (A.restrictOpen V))).hom ω')))
    ?_ ?_ ?_ ?_ (Submodule.eq_top_iff'.mp hspan ω')
  · rintro _ ⟨c, rfl⟩
    have h1 : formsDeRham (A.restrictOpen V)
        ((crysFormsOneGen S).app (op (A.restrictOpen V)) (crysD S (A.restrictOpen V) c)) = 0 := by
      have h := formsDeRham_smul_d (A.restrictOpen V) 1 c
      rw [one_smul] at h
      refine h.trans ?_
      have h0 : crysD S (A.restrictOpen V) 1 = 0 := by
        have h := (crysDifferentialsD S (A.restrictOpen V).obj).d_map 1
        rw [map_one] at h
        exact h
      rw [h0]
      exact formsWedge_zero_left _
    refine ((congrArg ((formsComparisonTwo A).toFun V) h1).trans (map_zero _)).trans ?_
    refine Eq.trans ?_ (congrArg (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom
      (op V)) (formsCompOne_formsD A V c)).symm
    exact (dpDeRham_d _ _ _ (op V) (sectionRingEquiv A V c)).symm
  · erw [map_zero ((crysFormsOneGen S).app (op (A.restrictOpen V))).hom]
    simp only [map_zero]
    exact (dpDeRham_zero _ _ _ _).symm
  · intro y y' _ _ hy hy'
    erw [map_add ((crysFormsOneGen S).app (op (A.restrictOpen V))).hom]
    simp only [map_add, hy, hy']
    exact (dpDeRham_add _ _ _ _ _ _).symm
  · intro r₀ y₀ _ hy
    exact formsComparisonTwo_formsDeRham_smul A V r₀ y₀ hy

end Crystalline.GlobalCrystallineSituation.SmallSite

end
