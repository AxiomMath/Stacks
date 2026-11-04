module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroWedge

/-!
# The residue is linear over the forms of the base

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of its line bundle. The proof of Stacks Tag 0FUG observes that the
residue `Res : Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}[-1]` of Tag 0FUF is a map of right differential graded
`Ω^•_{X/S}`-modules, "since it is locally defined by the rule
`Res(ω' + d log(s) ∧ ω) = ω`". This file proves the identity behind that:

`Res(x ∧ π^*α) = Res(x) ∧ α`

for a weight-zero form `x` of positive degree and a form `α` of `X`, and `Res(x ∧ π^*α) = 0` for
`x` of degree zero.

## Main results

* `Stacks.LineBundle.Situation.residueHom_weightZeroWedge`: `Res(x ∧ π^*α) = Res(x) ∧ α`.
* `Stacks.LineBundle.Situation.residueHom_weightZeroWedge_zero`: `Res(x ∧ π^*α) = 0` for `x` of
  degree zero.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules

attribute [local instance] gradedFormsGOne gradedFormsGMul gradedFormsGRing

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

attribute [local instance] Situation.AffineChart.algebraRA Situation.BaseChart.algebraRB
  Situation.BaseChart.algebraAB Situation.BaseChart.isScalarTower

/-! ### Moving a one-form past a form -/

/-- The wedge of a `p`-form with a one-form on the ambient complex agrees with the ambient wedge
in degrees `p` and `1`. -/
theorem Situation.gradedWedge_eq_ambientWedge (p : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (θ : Γ(D.gradedAmbient 1, U)) : D.gradedWedge p U η θ = D.ambientWedge p 1 U η θ :=
  rfl

/-- **A one-form moves past a `q`-form at the cost of the sign `(-1)^q`**:
`(η ∧ θ) ∧ ζ = (-1)^q (η ∧ ζ) ∧ θ`. -/
theorem Situation.ambientWedge_gradedWedge (p q : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (θ : Γ(D.gradedAmbient 1, U)) (ζ : Γ(D.gradedAmbient q, U)) :
    D.ambientCast (Nat.add_right_comm p 1 q)
        (D.ambientWedge (p + 1) q U (D.gradedWedge p U η θ) ζ) =
      (-1 : ℤ) ^ q • D.gradedWedge (p + q) U (D.ambientWedge p q U η ζ) θ := by
  refine D.ambientTot_injective _ U ?_
  rw [map_zsmul, D.ambientTot_ambientCast, D.ambientTot_ambientWedge,
    D.gradedWedge_eq_ambientWedge, D.gradedWedge_eq_ambientWedge, D.ambientTot_ambientWedge,
    D.ambientTot_ambientWedge, D.ambientTot_ambientWedge]
  have hc : D.ambientTot 1 U θ * D.ambientTot q U ζ =
      (-1 : ℤ) ^ (1 * q) • (D.ambientTot q U ζ * D.ambientTot 1 U θ) :=
    ofGradedForm_mul_comm (Scheme.Hom.deRhamAlgebras D.laurentToBase) 1 q _ θ ζ
  rw [one_mul] at hc
  rw [mul_assoc, hc, mul_smul_comm, mul_assoc]

/-! ### The residue over a base chart -/

/-- Transport of ambient forms along an equality of degrees is additive. -/
theorem Situation.ambientCast_add {m n : ℕ} (h : m = n) {U : D.X.Opens}
    (η η' : Γ(D.gradedAmbient m, U)) :
    D.ambientCast h (η + η') = D.ambientCast h η + D.ambientCast h η' := by
  subst h
  rfl

/-- Pullback of forms along `π` commutes with transport along an equality of degrees. -/
theorem Situation.pullbackG_formCast {m n : ℕ} (h : m = n) (U : D.X.Opens)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (m : ℤ), U)) :
    D.ambientCast h (D.pullbackG m U α) = D.pullbackG n U (Scheme.Hom.formCast h α) := by
  subst h
  rfl

/-- Pullback of forms along `π` commutes with multiplication by an integer. -/
theorem Situation.pullbackG_zsmul (p : ℕ) (U : D.X.Opens) (k : ℤ)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.pullbackG p U (k • α) = k • D.pullbackG p U α :=
  map_zsmul (AddMonoidHom.mk' (D.pullbackG p U) (fun a b => by
    rw [Situation.pullbackG, Situation.pullbackG, Situation.pullbackG, D.pullbackForms_add,
      map_add])) k α

/-- The wedge with a one-form commutes with integer multiplication in the left factor:
`(k • η) ∧ θ = k • (η ∧ θ)`. -/
theorem Situation.gradedWedge_zsmul_left (p : ℕ) (U : D.X.Opens) (k : ℤ)
    (η : Γ(D.gradedAmbient p, U)) (θ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge p U (k • η) θ = k • D.gradedWedge p U η θ :=
  DFunLike.congr_fun (map_zsmul ((D.laurentFormsAlgebra.mul (p : ℤ) 1).app
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) k η) θ

/-- The wedge of relative forms of `X` commutes with integer multiplication in the left factor:
`(k • ω) ∧ η = k • (ω ∧ η)`. -/
theorem Situation.formWedge_zsmul_left (p q : ℕ) (U : D.X.Opens) (k : ℤ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U))
    (η : Γ(Scheme.Hom.relativeDifferentialForms D.f (q : ℤ), U)) :
    Scheme.Hom.formWedge D.f p q U (k • ω) η = k • Scheme.Hom.formWedge D.f p q U ω η :=
  DFunLike.congr_fun (map_zsmul (((Scheme.Hom.deRhamAlgebras D.f).exterior.mul (p : ℤ)
    (q : ℤ)).app (op U)) k ω) η

/-- The ambient form of `x ∧ π^*α`, transported along `p + q = n`, is the ambient wedge of the
ambient form of `x` with `π^*α`. -/
private theorem weightZeroVal_cast_wedge_pullbackHom {D : Situation.{u}} {p q n : ℕ} (h : p + q = n)
    (U : D.X.Opens) (x : Γ(D.weightZero p, U))
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (q : ℤ), U)) :
    D.weightZeroVal n (D.weightZeroCast h
        ((D.weightZeroWedge p q).app (op U) x ((D.pullbackHom q).app U α))) =
      D.ambientCast h (D.ambientWedge p q U (D.weightZeroVal p x) (D.pullbackG q U α)) :=
  (D.weightZeroVal_weightZeroCast h _).trans
    (congrArg (D.ambientCast h) ((D.weightZeroVal_weightZeroWedge p q U x _).trans
      (congrArg (D.ambientWedge p q U (D.weightZeroVal p x)) (D.weightZeroVal_pullbackHom q U α))))

/-- **Over a base chart, `Res(x ∧ π^*α) = Res(x) ∧ α`.** Write `x = π^*a + π^*b ∧ d log s`
with `b` its residue against a right wedge; then
`x ∧ π^*α = π^*(a ∧ α) + (-1)^q π^*(b ∧ α) ∧ d log s`. -/
theorem Situation.BaseChart.residueHom_weightZeroWedge {D : Situation.{u}} (c : D.BaseChart)
    (p q : ℕ) (x : Γ(D.weightZero (p + 1), c.U.1))
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (q : ℤ), c.U.1)) :
    (D.residueHom (p + q)).app c.U.1 (D.weightZeroCast (Nat.add_right_comm p 1 q)
        ((D.weightZeroWedge (p + 1) q).app (op c.U.1) x ((D.pullbackHom q).app c.U.1 α))) =
      Scheme.Hom.formWedge D.f p q c.U.1 ((D.residueHom p).app c.U.1 x) α := by
  rw [D.residueHom_app, D.residueHom_app, weightZeroVal_cast_wedge_pullbackHom]
  set b := c.model.res p (D.weightZeroVal (p + 1) x) with hb
  obtain ⟨a, ha⟩ := c.model.exists_decomposition (D.weightZeroVal_mem (p + 1) x)
    (c.isDlog_laurentDlog c.unit) c.unit_mem
  have ha' : D.weightZeroVal (p + 1) x = D.pullbackG (p + 1) c.U.1 a +
      D.gradedWedge p c.U.1 (D.pullbackG p c.U.1 b) (D.laurentDlog c.U.1 c.unit) := ha
  have key : D.ambientCast (Nat.add_right_comm p 1 q) (D.ambientWedge (p + 1) q c.U.1
      (D.weightZeroVal (p + 1) x) (D.pullbackG q c.U.1 α)) =
      D.pullbackG (p + q + 1) c.U.1 (Scheme.Hom.formCast (Nat.add_right_comm p 1 q)
          (Scheme.Hom.formWedge D.f (p + 1) q c.U.1 a α)) +
        D.gradedWedge (p + q) c.U.1
          (D.pullbackG (p + q) c.U.1 ((-1 : ℤ) ^ q • Scheme.Hom.formWedge D.f p q c.U.1 b α))
          (D.laurentDlog c.U.1 c.unit) := by
    rw [ha', D.ambientWedge_add_left, D.ambientCast_add, ← D.pullbackG_formWedge,
      D.pullbackG_formCast, D.ambientWedge_gradedWedge, ← D.pullbackG_formWedge,
      D.pullbackG_zsmul, D.gradedWedge_zsmul_left]
  rw [key]
  have hres := c.model.res_decomposition (p + q) (Scheme.Hom.formCast (Nat.add_right_comm p 1 q)
    (Scheme.Hom.formWedge D.f (p + 1) q c.U.1 a α))
    ((-1 : ℤ) ^ q • Scheme.Hom.formWedge D.f p q c.U.1 b α) (c.isDlog_laurentDlog c.unit) c.unit_mem
  refine (congrArg (fun z => ((-1 : ℤ) ^ (p + q)) • z) hres).trans ?_
  rw [D.formWedge_zsmul_left, smul_smul, ← pow_add, show p + q + q = p + 2 * q by ring, pow_add,
    pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Over a base chart, `Res(x ∧ π^*α) = 0` for `x` of degree zero**: such an `x` is pulled back
from `X`. -/
theorem Situation.BaseChart.residueHom_weightZeroWedge_zero {D : Situation.{u}} (c : D.BaseChart)
    (q : ℕ) (x : Γ(D.weightZero 0, c.U.1))
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((q + 1 : ℕ) : ℤ), c.U.1)) :
    (D.residueHom q).app c.U.1 (D.weightZeroCast (Nat.zero_add (q + 1))
        ((D.weightZeroWedge 0 (q + 1)).app (op c.U.1) x ((D.pullbackHom (q + 1)).app c.U.1 α))) =
      0 := by
  obtain ⟨a, ha⟩ := c.model.exists_pull_zero (D.weightZeroVal_mem 0 x)
  have ha' : D.weightZeroVal 0 x = D.pullbackG 0 c.U.1 a := ha
  rw [D.residueHom_app, weightZeroVal_cast_wedge_pullbackHom, ha', ← D.pullbackG_formWedge,
    D.pullbackG_formCast]
  exact (congrArg (((-1 : ℤ) ^ q) • ·) (c.model.res_pull q _ (c.isDlog_laurentDlog c.unit)
    c.unit_mem)).trans (smul_zero _)

/-! ### Over an arbitrary open -/

/-- Transport of weight-zero forms along an equality of degrees commutes with restriction. -/
theorem Situation.weightZeroCast_map {m n : ℕ} (h : m = n) {U W : D.X.Opens} (hWU : W ≤ U)
    (x : Γ(D.weightZero m, U)) :
    (D.weightZero n).presheaf.map (homOfLE hWU).op (D.weightZeroCast h x) =
      D.weightZeroCast h ((D.weightZero m).presheaf.map (homOfLE hWU).op x) := by
  subst h
  rfl

/-- The wedge of weight-zero forms commutes with restriction. -/
theorem Situation.weightZeroWedge_map (p q : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (x : Γ(D.weightZero p, U)) (y : Γ(D.weightZero q, U)) :
    (D.weightZero (p + q)).presheaf.map (homOfLE hWU).op ((D.weightZeroWedge p q).app (op U) x y) =
      (D.weightZeroWedge p q).app (op W) ((D.weightZero p).presheaf.map (homOfLE hWU).op x)
        ((D.weightZero q).presheaf.map (homOfLE hWU).op y) :=
  (D.weightZeroWedge p q).naturality (homOfLE hWU).op x y

/-- The pullback `π^*` of relative forms of `X` to weight-zero forms commutes with restriction. -/
theorem Situation.pullbackHom_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    (D.weightZero p).presheaf.map (homOfLE hWU).op ((D.pullbackHom p).app U α) =
      (D.pullbackHom p).app W
        ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE hWU).op α) :=
  (PresheafOfModules.naturality_apply (D.pullbackHom p).val (homOfLE hWU).op α).symm

/-- The residue `Res` commutes with restriction. -/
theorem Situation.residueHom_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (x : Γ(D.weightZero (p + 1), U)) :
    (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE hWU).op
        ((D.residueHom p).app U x) =
      (D.residueHom p).app W ((D.weightZero (p + 1)).presheaf.map (homOfLE hWU).op x) :=
  (PresheafOfModules.naturality_apply (D.residueHom p).val (homOfLE hWU).op x).symm

/-- **`Res(x ∧ π^*α) = Res(x) ∧ α`**, for a section `x` of `Ω^{p+1}_{L^⋆/S,0}` and a relative
`q`-form `α` of `X` over an arbitrary open: the residue is linear over the forms of `X`, as in the
proof of Stacks Tag 0FUG. -/
theorem Situation.residueHom_weightZeroWedge (p q : ℕ) (U : D.X.Opens)
    (x : Γ(D.weightZero (p + 1), U))
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (q : ℤ), U)) :
    (D.residueHom (p + q)).app U (D.weightZeroCast (Nat.add_right_comm p 1 q)
        ((D.weightZeroWedge (p + 1) q).app (op U) x ((D.pullbackHom q).app U α))) =
      Scheme.Hom.formWedge D.f p q U ((D.residueHom p).app U x) α := by
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq
    (Scheme.Hom.relativeDifferentialForms D.f ((p + q : ℕ) : ℤ)) U _ _ fun z hz => ?_
  obtain ⟨c, hzc, hcU⟩ := D.exists_baseChart hz
  refine ⟨c.U.1, hcU, hzc, ?_⟩
  rw [D.residueHom_map _ hcU, D.weightZeroCast_map (Nat.add_right_comm p 1 q) hcU
      ((D.weightZeroWedge (p + 1) q).app (op U) x ((D.pullbackHom q).app U α)),
    D.weightZeroWedge_map _ _ hcU x ((D.pullbackHom q).app U α),
    D.pullbackHom_map _ hcU, c.residueHom_weightZeroWedge, Scheme.Hom.formWedge_res,
    D.residueHom_map _ hcU]

/-- **`Res(x ∧ π^*α) = 0` for a section `x` of `Ω^0_{L^⋆/S,0}`** over an arbitrary open. -/
theorem Situation.residueHom_weightZeroWedge_zero (q : ℕ) (U : D.X.Opens)
    (x : Γ(D.weightZero 0, U))
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((q + 1 : ℕ) : ℤ), U)) :
    (D.residueHom q).app U (D.weightZeroCast (Nat.zero_add (q + 1))
        ((D.weightZeroWedge 0 (q + 1)).app (op U) x ((D.pullbackHom (q + 1)).app U α))) = 0 := by
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq
    (Scheme.Hom.relativeDifferentialForms D.f (q : ℤ)) U _ _ fun z hz => ?_
  obtain ⟨c, hzc, hcU⟩ := D.exists_baseChart hz
  refine ⟨c.U.1, hcU, hzc, ?_⟩
  rw [D.residueHom_map _ hcU, D.weightZeroCast_map (Nat.zero_add (q + 1)) hcU
      ((D.weightZeroWedge 0 (q + 1)).app (op U) x ((D.pullbackHom (q + 1)).app U α)),
    D.weightZeroWedge_map _ _ hcU x ((D.pullbackHom (q + 1)).app U α),
    D.pullbackHom_map _ hcU, c.residueHom_weightZeroWedge_zero, map_zero]

end Stacks.LineBundle
