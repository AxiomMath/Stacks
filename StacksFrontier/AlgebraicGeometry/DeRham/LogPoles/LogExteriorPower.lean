module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DeRhamComplexLogPoles
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf

/-!
# The forms with logarithmic poles are the exterior powers of the `1`-forms

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined. Clause (3) of [Stacks, Tag 0FUP] states

`Ω^p_{X/S}(log Y) = ⋀^p(Ω^1_{X/S}(log Y))`,

that is, the unital homomorphism of sheaves of graded `𝒪_X`-algebras from the exterior algebra of
`Ω^1_{X/S}(log Y)` to the graded algebra of forms with logarithmic poles which is the identity in
degree one (`AlgebraicGeometry.Scheme.Hom.logExteriorDesc`) is an isomorphism in every degree.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.logExteriorDesc`: the wedge product
  `⋀^• Ω^1_{X/S}(log Y) ⟶ Ω^•_{X/S}(log Y)`.
* `AlgebraicGeometry.Scheme.Hom.logExteriorInclusion`: `⋀^• Ω_{X/S} ⟶ ⋀^• Ω^1_{X/S}(log Y)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_logExteriorDesc_app_eq`: local surjectivity.
* `AlgebraicGeometry.Scheme.Hom.logExteriorDesc_app_natCast_eq_zero`: injectivity on sections.
* `AlgebraicGeometry.Scheme.Hom.isIso_logExteriorDesc_app`: `logExteriorDesc` is an isomorphism
  in every degree.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace SheafOfModules.GradedAlgebra

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul AlgebraicGeometry.SheafOfModules.gradedFormsGRing

universe u

namespace Stacks.LogPoles

/-- In a ring with scalars, `(A + B E)(W + c • E) = A W + (c • A - B W) E` when `E W = -(W E)`,
`E E = 0` and multiplication commutes with the scalars. -/
theorem mul_gen_algebra {R S : Type*} [Ring R] [Monoid S] [DistribMulAction S R]
    (A B W E : R) (c : S) (hEW : E * W = -(W * E)) (hEE : E * E = 0)
    (hl : ∀ x y : R, (c • x) * y = c • (x * y)) (hr : ∀ x y : R, x * (c • y) = c • (x * y)) :
    (A + B * E) * (W + c • E) = A * W + (c • A - B * W) * E := by
  rw [add_mul, mul_add, mul_add, hr, hr, _root_.mul_assoc B E W, hEW, _root_.mul_assoc B E E, hEE,
    mul_zero, smul_zero, add_zero, sub_mul, hl, mul_neg, ← _root_.mul_assoc]
  abel

end Stacks.LogPoles

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- The identity of `Ω^1_{X/S}(log Y)`, read as a degree-one generator of the graded algebra of
forms with logarithmic poles. -/
def logGenerator : logPolesForms f I 1 ⟶ (logGradedAlgebra f I hI hlog).piece 1 :=
  𝟙 (logPolesForms f I 1)

/-- The wedge product of a `1`-form with logarithmic poles with itself vanishes. -/
theorem squareZero_logGenerator : SquareZero (logGenerator f I hI hlog) :=
  fun U φ ↦ logFormsWedge_self_eq_zero f I hI hlog (W := U.unop) φ

/-- **The wedge product `⋀^• Ω^1_{X/S}(log Y) ⟶ Ω^•_{X/S}(log Y)`**: the unique unital
homomorphism of sheaves of graded `𝒪_X`-algebras out of the exterior algebra of
`Ω^1_{X/S}(log Y)` which is the identity in degree one. In degree `p` it sends
`φ₁ ∧ ⋯ ∧ φ_p` to the wedge product of the `φᵢ` of Tag 0FUP (1). -/
def logExteriorDesc :
    UnitalHom (Scheme.Modules.exteriorAlgebra (logPolesForms f I 1))
        (logGradedAlgebra f I hI hlog) :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (logPolesForms f I 1)).desc _
    (logGenerator f I hI hlog) (squareZero_logGenerator f I hI hlog)

/-- In degree one, `logExteriorDesc` composed with the generator is the identity of
`Ω^1_{X/S}(log Y)`. -/
theorem logExteriorDesc_generator :
    Scheme.Modules.exteriorGenerator (logPolesForms f I 1) ≫ (logExteriorDesc f I hI hlog).app 1 =
      logGenerator f I hI hlog :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (logPolesForms f I 1)).desc_extends _ _ _

/-- The inclusion of `1`-forms `Ω_{X/S} ⟶ Ω^1_{X/S}(log Y)`. -/
def logOneFormsInclusion : relativeDifferentials f ⟶ logPolesForms f I 1 :=
  Scheme.Modules.exteriorGenerator (relativeDifferentials f) ≫ logPolesFormsInclusion f I 1

/-- The image of a `1`-form in the exterior algebra of `Ω^1_{X/S}(log Y)` squares to zero. -/
theorem squareZero_logOneFormsInclusion :
    SquareZero (logOneFormsInclusion f I ≫ Scheme.Modules.exteriorGenerator
        (logPolesForms f I 1)) :=
  ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (logPolesForms f I 1)).1).comp _

/-- The map `⋀^• Ω_{X/S} ⟶ ⋀^• Ω^1_{X/S}(log Y)` of exterior algebras induced by the inclusion of
`1`-forms. -/
def logExteriorInclusion :
    UnitalHom (relativeDifferentialFormsAlgebra f)
      (Scheme.Modules.exteriorAlgebra (logPolesForms f I 1)) :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials f)).desc _
    (logOneFormsInclusion f I ≫ Scheme.Modules.exteriorGenerator (logPolesForms f I 1))
    (squareZero_logOneFormsInclusion f I)

/-- In degree one, `logExteriorInclusion` composed with the generator is `logOneFormsInclusion`
followed by the generator. -/
private theorem exteriorGenerator_comp_logExteriorInclusion_app_one :
    Scheme.Modules.exteriorGenerator (relativeDifferentials f) ≫ (logExteriorInclusion f I).app 1 =
      logOneFormsInclusion f I ≫ Scheme.Modules.exteriorGenerator (logPolesForms f I 1) :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials f)).desc_extends _ _ _

/-- **`⋀^p Ω_{X/S} ⟶ ⋀^p Ω^1_{X/S}(log Y) ⟶ Ω^p_{X/S}(log Y)` is the inclusion of forms with no
pole.** -/
theorem logExteriorInclusion_comp_logExteriorDesc :
    (logExteriorInclusion f I).comp (logExteriorDesc f I hI hlog)
    = logGradedInclusion f I hI hlog := by
  have hE := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials f)
  have hsq : SquareZero (Scheme.Modules.exteriorGenerator (relativeDifferentials f) ≫
      (logGradedInclusion f I hI hlog).app 1) := by
    intro U ω
    have h := (logGradedInclusion f I hI hlog).map_mul 1 1 U
      ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U ω)
      ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U ω)
    have h0 : ((relativeDifferentialFormsAlgebra f).mul 1 1).app U
        ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U ω)
        ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U ω) = 0 := hE.1 U ω
    rw [h0, map_zero] at h
    exact h.symm
  refine IsUniversal.hom_ext hE hsq ?_ rfl
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (logExteriorDesc f I hI hlog).app 1)
    (exteriorGenerator_comp_logExteriorInclusion_app_one f I)).trans
    ((Category.assoc _ _ _).trans ((congrArg (logOneFormsInclusion f I ≫ ·)
      (logExteriorDesc_generator f I hI hlog)).trans ?_)))
  exact Category.comp_id _

/-- On sections, `logExteriorDesc` applied to the image of a `p`-form `ω` under
`logExteriorInclusion` is `ω` as a form with logarithmic poles. -/
theorem logExteriorDesc_app_logExteriorInclusion_app (p : ℕ) (U : X.Opensᵒᵖ)
    (ω : Γ(relativeDifferentialForms f (p : ℤ), U.unop)) :
    ((logExteriorDesc f I hI hlog).app (p : ℤ)).val.app U
        (((logExteriorInclusion f I).app (p : ℤ)).val.app U ω) =
      (logPolesFormsInclusion f I p).val.app U ω :=
  _root_.SheafOfModules.hom_congr_app_apply
    (congrArg (fun g : UnitalHom _ _ ↦ g.app (p : ℤ))
      (logExteriorInclusion_comp_logExteriorDesc f I hI hlog)) U ω

/-- On sections, `logExteriorDesc` sends a `1`-form with logarithmic poles, read in degree one
of the exterior algebra, to itself. -/
theorem logExteriorDesc_app_one (U : X.Opensᵒᵖ) (φ : (logPolesForms f I 1).val.obj U) :
    ((logExteriorDesc f I hI hlog).app 1).val.app U
        ((Scheme.Modules.exteriorGenerator (logPolesForms f I 1)).val.app U φ) = φ :=
  _root_.SheafOfModules.hom_congr_app_apply (logExteriorDesc_generator f I hI hlog) U φ

/-- A unital homomorphism of sheaves of graded algebras commutes with transport along an
equality of degrees. -/
theorem _root_.SheafOfModules.GradedAlgebra.UnitalHom.app_gradedCast
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {A B : _root_.SheafOfModules.GradedAlgebra.{u, u} R} (g : UnitalHom A B) {n m : ℤ}
    (h : n = m) (U : Cᵒᵖ) (x : (A.piece n).val.obj U) :
    (g.app m).val.app U (_root_.SheafOfModules.gradedCast (fun k => (A.piece k).val.obj U) h x) =
      _root_.SheafOfModules.gradedCast (fun k => (B.piece k).val.obj U) h
        ((g.app n).val.app U x) := by
  subst h
  rfl

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- **The form `dlog t`** over an open `W` inside a chart with local equation `t`. -/
abbrev dlogForm {W : X.Opens} (hW : W ≤ U) : (logPolesForms f I 1).val.obj (op W) :=
  e.logPolesChartForm (p := 0) hW 0 (formOne W)

/-- The local equation `t` times the chart form of `(ω, η)` is the form `t ω + dt ∧ η` with no
pole. -/
theorem equationAt_smul_logPolesChartForm {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    e.equationAtR hW • e.logPolesChartForm hW ω η =
      (logPolesFormsInclusion f I (p + 1)).val.app (op W)
        (e.equationAt hW • ω + exactWedge f p W (e.equationAt hW) η) := by
  rw [e.equationAt_smul_eq_logPolesFormsInclusion hW]
  exact congrArg _ (e.logEval_logOfCoord_basisLE hW _ (e.formRes_smul_add_exactWedge hW ω η))

/-- The wedge product of the `1`-form `c · 0 + dc ∧ 1` with a `q`-form `η` is `dc ∧ η`. -/
theorem formCast_formWedge_exactWedge {q : ℕ} {W : X.Opens} (c : Γ(X, W))
    (η : Γ(relativeDifferentialForms f (q : ℤ), W)) :
    formCast (Nat.add_comm 1 q) (formWedge f 1 q W (c • 0 + exactWedge f 0 W c (formOne W)) η) =
      exactWedge f q W c η := by
  refine totForm_injective (q + 1) W ?_
  refine (totForm_formCast _ _).trans ?_
  refine (totForm_formWedge 1 q W _ η).trans ?_
  rw [smul_zero, zero_add, totForm_exactWedge, totForm_exactWedge]
  exact congrArg (fun z ↦ totExact f W c * z * totForm f q W η)
    (AlgebraicGeometry.SheafOfModules.ofGradedForm_one (deRhamAlgebras f) (op W)) |>.trans
    (by rw [_root_.mul_one])

/-- The chart form of `(ω, η)` is `ω + dlog t ∧ η`: the sum of the form `ω` with no pole and the
wedge product of `dlog t` with the form `η` with no pole. -/
theorem logPolesChartForm_eq {q : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (q : ℤ), W)) :
    e.logPolesChartForm hW ω η =
      (logPolesFormsInclusion f I (q + 1)).val.app (op W) ω +
        logFormsCast (Nat.add_comm 1 q)
          (logFormsWedge hI hlog (e.dlogForm hW)
          ((logPolesFormsInclusion f I q).val.app (op W) η)) := by
  refine e.logForms_eq_of_equationAt_smul_eq hlog hW ?_
  rw [smul_add, ← logFormsCast_smul, ← logFormsWedge_smul_left, equationAt_smul_logPolesChartForm,
    equationAt_smul_logPolesChartForm, logFormsWedge_logPolesFormsInclusion,
    logFormsCast_logPolesFormsInclusion, formCast_formWedge_exactWedge]
  refine (map_add _ _ _).trans ?_
  exact congrArg (· + _) (((logPolesFormsInclusion f I (q + 1)).val.app (op W)).hom.map_smul _ _)

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul AlgebraicGeometry.SheafOfModules.gradedFormsGRing
  in
/-- If the `1`-form `κ` is `dc`, then `(dc ∧ β) ∧ κ = 0`. -/
theorem formWedge_exactWedge_exactWedge_eq_zero (q : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (q : ℤ), V))
    (κ : Γ(relativeDifferentialForms f ((1 : ℕ) : ℤ), V)) (hκ : totForm f 1 V κ = totExact f V c) :
    formWedge f (q + 1) 1 V (exactWedge f q V c β) κ = 0 := by
  refine totForm_injective (q + 1 + 1) V
    (((totForm_formWedge (q + 1) 1 V _ κ).trans ?_).trans (map_zero _).symm)
  rw [totForm_exactWedge, hκ, _root_.mul_assoc, totForm_mul_totExact, mul_smul_comm,
    ← _root_.mul_assoc, totExact_mul_self, zero_mul, smul_zero]

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul AlgebraicGeometry.SheafOfModules.gradedFormsGRing
  in
/-- If the `1`-form `κ` is `dc`, then for a `q`-form `β`, `β ∧ κ = (-1)^q dc ∧ β`. -/
theorem formWedge_eq_zsmul_exactWedge (q : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (q : ℤ), V))
    (κ : Γ(relativeDifferentialForms f ((1 : ℕ) : ℤ), V)) (hκ : totForm f 1 V κ = totExact f V c) :
    formWedge f q 1 V β κ = ((-1 : ℤ) ^ q) • exactWedge f q V c β := by
  refine totForm_injective (q + 1) V ((totForm_formWedge q 1 V β κ).trans ?_)
  rw [map_zsmul, totForm_exactWedge, hκ, totForm_mul_totExact]

/-! ### Computations in the exterior algebra of `Ω^1_{X/S}(log Y)` -/

/-- The exterior algebra of `Ω^1_{X/S}(log Y)`. -/
abbrev logExtAlg : _root_.SheafOfModules.GradedAlgebra.{u, u}
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) :=
  Scheme.Modules.exteriorAlgebra (logPolesForms f I 1)

variable {f I}

/-- A local section of `Ω^1_{X/S}(log Y)`, read in degree one of its exterior algebra. -/
abbrev logExtGen {V : X.Opens} (s : (logPolesForms f I 1).val.obj (op V)) :
    ((logExtAlg f I).piece 1).val.obj (op V) :=
  (Scheme.Modules.exteriorGenerator (logPolesForms f I 1)).val.app (op V) s

/-- The image of a local form under `⋀^• Ω_{X/S} ⟶ ⋀^• Ω^1_{X/S}(log Y)`. -/
abbrev logExtJ {V : X.Opens} (n : ℤ)
    (ω : ((relativeDifferentialFormsAlgebra f).piece n).val.obj (op V)) :
    ((logExtAlg f I).piece n).val.obj (op V) :=
  ((logExteriorInclusion f I).app n).val.app (op V) ω

/-- A homogeneous local section of the exterior algebra of `Ω^1_{X/S}(log Y)`, in the ring of all
local sections. -/
abbrev logExtIncl {V : X.Opens} (i : ℤ) (x : ((logExtAlg f I).piece i).val.obj (op V)) :
    (logExtAlg f I).toPresheafGradedAlgebra.Total (op V) :=
  (logExtAlg f I).toPresheafGradedAlgebra.incl i x

/-- In degree one, the image of a `1`-form `κ` in the exterior algebra of `Ω^1_{X/S}(log Y)` is
`κ`, as a form with logarithmic poles, read in degree one. -/
theorem logExtJ_one {V : X.Opens} (κ : Γ(relativeDifferentialForms f ((1 : ℕ) : ℤ), V)) :
    logExtJ (I := I) 1 κ = logExtGen ((logPolesFormsInclusion f I 1).val.app (op V) κ) := by
  let A := SheafOfModules.algebras _ (relativeDifferentials f)
  have := A.isIso_exteriorGenerator
  have hκ : A.exteriorGenerator.val.app (op V) ((inv A.exteriorGenerator).val.app (op V) κ) = κ :=
    _root_.SheafOfModules.iso_inv_hom_app_apply (asIso A.exteriorGenerator).symm (op V) κ
  exact (congrArg (logExtJ (I := I) 1) hκ.symm).trans
    ((_root_.SheafOfModules.hom_congr_app_apply
      (exteriorGenerator_comp_logExteriorInclusion_app_one f I) (op V)
      ((inv A.exteriorGenerator).val.app (op V) κ)).trans
    (congrArg (fun z ↦ logExtGen ((logPolesFormsInclusion f I 1).val.app (op V) z)) hκ))

/-- The map `⋀^• Ω_{X/S} ⟶ ⋀^• Ω^1_{X/S}(log Y)` sends `α ∧ β` to the product of the images of
`α` and `β`. -/
theorem logExtIncl_logExtJ_formWedge {V : X.Opens} (p q : ℕ)
    (α : Γ(relativeDifferentialForms f (p : ℤ), V))
    (β : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    logExtIncl (I := I) (((p + q : ℕ) : ℤ)) (logExtJ _ (formWedge f p q V α β)) =
      logExtIncl (I := I) (p : ℤ) (logExtJ _ α) * logExtIncl (I := I) (q : ℤ) (logExtJ _ β) :=
  (congrArg (logExtIncl (I := I) _) ((logExteriorInclusion f I).map_mul (p : ℤ) (q : ℤ)
      (op V) α β)).trans
    (Stacks.GradedAlgebra.incl_mul_incl _ _ _ _ _).symm

/-- The image of a form in the ring of all local sections does not depend on transport along an
equality of degrees. -/
theorem logExtIncl_logExtJ_formCast {V : X.Opens} {m n : ℕ} (h : m = n)
    (x : Γ(relativeDifferentialForms f (m : ℤ), V)) :
    logExtIncl (I := I) (n : ℤ) (logExtJ _ (formCast h x)) = logExtIncl (I := I) (m : ℤ)
        (logExtJ _ x) := by
  subst h
  rfl

/-- A local section of `Ω^1_{X/S}(log Y)` squares to zero in its exterior algebra. -/
theorem logExtIncl_logExtGen_mul_self {V : X.Opens} (s : (logPolesForms f I 1).val.obj (op V)) :
    logExtIncl 1 (logExtGen s) * logExtIncl 1 (logExtGen s) = 0 := by
  rw [Stacks.GradedAlgebra.incl_mul_incl]
  have h : ((logExtAlg f I).mul 1 1).app (op V) (logExtGen s) (logExtGen s) = 0 :=
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (logPolesForms f I 1)).1 (op V) s
  rw [show (logExtAlg f I).toPresheafGradedAlgebra.mul 1 1 = (logExtAlg f I).mul 1 1 from rfl, h]
  exact map_zero _

/-- Local sections of `Ω^1_{X/S}(log Y)` anticommute in its exterior algebra. -/
theorem logExtIncl_logExtGen_anticomm {V : X.Opens} (s s' : (logPolesForms f I 1).val.obj (op V)) :
    logExtIncl 1 (logExtGen s) * logExtIncl 1 (logExtGen s') =
      -(logExtIncl 1 (logExtGen s') * logExtIncl 1 (logExtGen s)) := by
  have h := logExtIncl_logExtGen_mul_self (s + s')
  have hadd : logExtIncl (I := I) (V := V) 1 (logExtGen (s + s')) =
      logExtIncl 1 (logExtGen s) + logExtIncl 1 (logExtGen s') :=
    (congrArg (logExtIncl (I := I) 1) (map_add _ s s')).trans
        (Stacks.GradedAlgebra.incl_add _ _ _ _)
  rw [hadd, add_mul, mul_add, mul_add,
    logExtIncl_logExtGen_mul_self, logExtIncl_logExtGen_mul_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A local function, in the spelling of the scalars of the exterior algebra. -/
abbrev toStructScalar {V : X.Opens} (c : Γ(X, V)) :
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj (op V) :=
  c

/-- The map `⋀^• Ω_{X/S} ⟶ ⋀^• Ω^1_{X/S}(log Y)` commutes with multiplication by a local
function. -/
theorem logExtIncl_logExtJ_smul {V : X.Opens} (n : ℕ) (c : Γ(X, V))
    (ω : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    logExtIncl (I := I) (n : ℤ) (logExtJ _ (c • ω)) =
      toStructScalar c • logExtIncl (I := I) (n : ℤ) (logExtJ _ ω) :=
  (congrArg (logExtIncl (I := I) _) (((logExteriorInclusion f I).app (n : ℤ)).val.app (op V)
    |>.hom.map_smul _ _)).trans (Stacks.GradedAlgebra.incl_smul _ _ _ _)

/-- The map `⋀^• Ω_{X/S} ⟶ ⋀^• Ω^1_{X/S}(log Y)` is additive. -/
theorem logExtIncl_logExtJ_add {V : X.Opens} (n : ℕ)
    (ω ω' : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    logExtIncl (I := I) (n : ℤ) (logExtJ _ (ω + ω')) =
      logExtIncl (I := I) (n : ℤ) (logExtJ _ ω) + logExtIncl (I := I) (n : ℤ) (logExtJ _ ω') :=
  (congrArg (logExtIncl (I := I) _) (map_add _ _ _)).trans (map_add (DirectSum.of _ _) _ _)

/-- The map `⋀^• Ω_{X/S} ⟶ ⋀^• Ω^1_{X/S}(log Y)` commutes with negation. -/
theorem logExtIncl_logExtJ_neg {V : X.Opens} (n : ℕ)
    (ω : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    logExtIncl (I := I) (n : ℤ) (logExtJ _ (-ω)) = -logExtIncl (I := I) (n : ℤ) (logExtJ _ ω) :=
  (congrArg (logExtIncl (I := I) _) (map_neg _ _)).trans (map_neg (DirectSum.of _ _) _)

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- The exact `1`-form `dt` of the local equation, as the form `t · 0 + dt ∧ 1`. -/
abbrev chartDt {V : X.Opens} (hV : V ≤ U) : Γ(relativeDifferentialForms f ((0 + 1 : ℕ) : ℤ), V) :=
  e.equationAt hV • 0 + exactWedge f 0 V (e.equationAt hV) (formOne V)

/-- The form `chartDt` is `dt ∧ 1`. -/
theorem chartDt_eq {V : X.Opens} (hV : V ≤ U) :
    e.chartDt hV = exactWedge f 0 V (e.equationAt hV) (formOne V) :=
  (congrArg (· + exactWedge f 0 V (e.equationAt hV) (formOne V)) (smul_zero _)).trans (zero_add _)

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul AlgebraicGeometry.SheafOfModules.gradedFormsGRing
  in
/-- In the total de Rham algebra, `chartDt` is the exact form `dt`. -/
theorem totForm_chartDt {V : X.Opens} (hV : V ≤ U) :
    totForm f 1 V (e.chartDt hV) = totExact f V (e.equationAt hV) := by
  refine (congrArg (totForm f 1 V) (e.chartDt_eq hV)).trans ((totForm_exactWedge 0 V _ _).trans ?_)
  exact (congrArg (totExact f V (e.equationAt hV) * ·)
    (AlgebraicGeometry.SheafOfModules.ofGradedForm_one (deRhamAlgebras f) (op V))).trans (mul_one _)

/-- As a form with logarithmic poles, `dt = t · dlog t`. -/
theorem logPolesFormsInclusion_chartDt {V : X.Opens} (hV : V ≤ U) :
    (logPolesFormsInclusion f I 1).val.app (op V) (e.chartDt hV) =
      e.equationAtR hV • e.dlogForm hV :=
  (e.equationAt_smul_logPolesChartForm (p := 0) hV 0 (formOne V)).symm

/-- The restriction of `chartDt` to a smaller open is `chartDt` there. -/
theorem chartDt_res {V V' : X.Opens} (hV : V ≤ U) (h : V' ≤ V) :
    (relativeDifferentialForms f ((0 + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op (e.chartDt hV) =
      e.chartDt (h.trans hV) := by
  rw [e.chartDt_eq, e.chartDt_eq, exactWedge_res, formOne_res, e.equationAt_res hV h]

/-- The restriction of `dlog t` to a smaller open is `dlog t` there. -/
theorem dlogForm_res (hlog : f.HasLogPolesDeRhamComplex I) {V V' : X.Opens} (hV : V ≤ U)
    (h : V' ≤ V) :
    (logPolesForms f I 1).val.map (homOfLE h).op (e.dlogForm hV) = e.dlogForm (h.trans hV) := by
  refine e.logForms_eq_of_equationAt_smul_eq hlog (h.trans hV) ?_
  rw [← e.logPolesFormsInclusion_chartDt (h.trans hV), ← e.chartDt_res hV h,
    ← logPolesFormsInclusion_map, e.logPolesFormsInclusion_chartDt hV]
  refine Eq.symm (((logPolesForms f I 1).val.map_smul (homOfLE h).op _ _).trans ?_)
  exact congrArg (· • _) (e.equationAt_res hV h)

/-- The local equation, in the spelling of the scalars of the exterior algebra. -/
abbrev equationAtS {V : X.Opens} (hV : V ≤ U) :
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj (op V) :=
  e.equationAt hV

/-- In the exterior algebra of `Ω^1_{X/S}(log Y)`, the image of `dt` is `t · dlog t`. -/
theorem logExtIncl_logExtJ_chartDt {V : X.Opens} (hV : V ≤ U) :
    logExtIncl (I := I) 1 (logExtJ _ (e.chartDt (f := f) hV)) =
      e.equationAtS hV • logExtIncl (I := I) 1 (logExtGen (e.dlogForm (f := f) hV)) := by
  refine (congrArg (logExtIncl (I := I) 1) ((logExtJ_one _).trans
    (congrArg logExtGen (e.logPolesFormsInclusion_chartDt hV)))).trans ?_
  refine (congrArg (logExtIncl (I := I) 1) (((Scheme.Modules.exteriorGenerator
    (logPolesForms f I 1)).val.app (op V)).hom.map_smul _ _)).trans ?_
  exact Stacks.GradedAlgebra.incl_smul _ _ _ _

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- Restricting a form with logarithmic poles twice is restricting it once. -/
theorem logPolesForms_map_map {p : ℕ} {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (χ : (logPolesForms f I p).val.obj (op W)) :
    (logPolesForms f I p).val.map (homOfLE h').op ((logPolesForms f I p).val.map (homOfLE h).op χ) =
      (logPolesForms f I p).val.map (homOfLE (h'.trans h)).op χ := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- **The wedge product `⋀^p Ω^1_{X/S}(log Y) ⟶ Ω^p_{X/S}(log Y)` is locally surjective.** -/
theorem exists_logExteriorDesc_app_eq (p : ℕ) {W : X.Opens} (χ : (logPolesForms f I p).val.obj
    (op W))
    (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧ ∃ z : ((logExtAlg f I).piece (p : ℤ)).val.obj (op V),
      ((logExteriorDesc f I hI hlog).app (p : ℤ)).val.app (op V) z =
        (logPolesForms f I p).val.map (homOfLE hV).op χ := by
  cases p with
  | zero =>
    obtain ⟨V, hVW, hxV, ω, hω⟩ := exists_map_eq_logPolesFormsInclusion_zero hI χ x hx
    exact ⟨V, hVW, hxV, logExtJ (I := I) _ ω,
      (logExteriorDesc_app_logExteriorInclusion_app f I hI hlog 0 (op V) ω).trans hω.symm⟩
  | succ q =>
    obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
    obtain ⟨V, hV, hxV, ω, η, hωη⟩ := e.exists_map_eq_logPolesChartForm
      (inf_le_right : W ⊓ Ux ≤ Ux) ((logPolesForms f I (q + 1)).val.map
        (homOfLE (inf_le_left : W ⊓ Ux ≤ W)).op χ) x ⟨hx, hxU⟩
    have hVU : V ≤ Ux := hV.trans inf_le_right
    have hVW : V ≤ W := hV.trans inf_le_left
    rw [logPolesForms_map_map, e.logPolesChartForm_eq hI hlog] at hωη
    refine ⟨V, hVW, hxV, logExtJ (I := I) _ ω +
      _root_.SheafOfModules.gradedCast (fun k ↦ ((logExtAlg f I).piece k).val.obj (op V))
        (show (1 : ℤ) + (q : ℤ) = ((q + 1 : ℕ) : ℤ) by push_cast; ring)
        (((logExtAlg f I).mul 1 (q : ℤ)).app (op V) (logExtGen (e.dlogForm hVU))
          (logExtJ (I := I) _ η)), ?_⟩
    rw [map_add, logExteriorDesc_app_logExteriorInclusion_app,
      UnitalHom.app_gradedCast, (logExteriorDesc f I hI hlog).map_mul,
      logExteriorDesc_app_one, logExteriorDesc_app_logExteriorInclusion_app, hωη]
    refine congrArg (fun z : (logPolesForms f I (q + 1)).val.obj (op V) ↦
      (logPolesFormsInclusion f I (q + 1)).val.app (op V) ω + z) (eq_of_heq ?_)
    exact (_root_.SheafOfModules.gradedCast_heq _ _ _).trans (logFormsCast_heq _ _).symm

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- `dc ∧ -` as an additive map. -/
def exactWedgeHom (q : ℕ) (V : X.Opens) (c : Γ(X, V)) :
    Γ(relativeDifferentialForms f (q : ℤ), V) →+ Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ),
        V) :=
  AddMonoidHom.mk' (exactWedge f q V c) (exactWedge_add_right q V c)

/-- Restriction of forms to `Y`, as an additive map. -/
def formResHom (n : ℤ) (V : X.Opens) :
    Γ(relativeDifferentialForms f n, V) →+
      Γ(relativeDifferentialForms (I.subschemeι ≫ f) n, I.subschemeι ⁻¹ᵁ V) :=
  AddMonoidHom.mk' (formRes I.subschemeι n V) (formRes_add I.subschemeι n V)

/-- In an additive group, `(-1)^q • (-1)^q • y = y`. -/
theorem neg_one_pow_smul_neg_one_pow_smul {M : Type*} [AddCommGroup M] (q : ℕ) (y : M) :
    ((-1 : ℤ) ^ q) • ((-1 : ℤ) ^ q) • y = y := by
  rw [smul_smul, ← mul_pow]
  simp

include e in
/-- **The local splitting of a form vanishing on `Y`.** A `q`-form `β` restricting to zero on `Y`
is near every point `t β' + γ`, where `γ ∧ dt = 0` and the image of `γ` in the exterior algebra of
`Ω^1_{X/S}(log Y)` is killed by `dlog t` on the right. -/
theorem exists_local_split {q : ℕ} {W : X.Opens} (hW : W ≤ U)
    (β : Γ(relativeDifferentialForms f (q : ℤ), W)) (hβ : formRes I.subschemeι (q : ℤ) W β = 0)
    (y : X) (hy : y ∈ W) :
    ∃ (V : X.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ β' γ : Γ(relativeDifferentialForms f (q : ℤ), V),
      (relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE hV).op β =
          e.equationAt (hV.trans hW) • β' + γ ∧
        formWedge f q 1 V γ (e.chartDt (hV.trans hW)) = 0 ∧
        logExtIncl (I := I) (q : ℤ) (logExtJ _ γ) *
          logExtIncl (I := I) 1 (logExtGen (e.dlogForm (hV.trans hW))) = 0 := by
  cases q with
  | zero =>
    obtain ⟨V, hV, hyV, β', hβ'⟩ := e.exists_local_eq_smul hW β hβ y hy
    refine ⟨V, hV, hyV, β', 0, by rw [add_zero]; exact hβ', formWedge_zero_left _ _ _ _, ?_⟩
    have h0 : logExtIncl (I := I) (V := V) ((0 : ℕ) : ℤ)
        (logExtJ _ (0 : Γ(relativeDifferentialForms f ((0 : ℕ) : ℤ), V))) = 0 :=
      (congrArg (logExtIncl (I := I) _) (map_zero _)).trans (map_zero (DirectSum.of _ _))
    rw [h0, zero_mul]
  | succ q' =>
    obtain ⟨V, hV, hyV, β', β'', hβ'⟩ := e.exists_local_eq_smul_add_exactWedge hW q' β hβ y hy
    have hκ := e.totForm_chartDt (f := f) (hV.trans hW)
    refine ⟨V, hV, hyV, β', exactWedge f q' V (e.equationAt (hV.trans hW)) β'', hβ',
      formWedge_exactWedge_exactWedge_eq_zero f q' V _ β'' _ hκ, ?_⟩
    have hγ : exactWedge f q' V (e.equationAt (hV.trans hW)) β'' =
        ((-1 : ℤ) ^ q') • formWedge f q' 1 V β'' (e.chartDt (hV.trans hW)) := by
      rw [formWedge_eq_zsmul_exactWedge f q' V _ β'' _ hκ, neg_one_pow_smul_neg_one_pow_smul]
    have hz : logExtIncl (I := I) (V := V) ((q' + 1 : ℕ) : ℤ)
        (logExtJ _ (((-1 : ℤ) ^ q') • formWedge f q' 1 V β'' (e.chartDt (hV.trans hW)))) =
        ((-1 : ℤ) ^ q') • logExtIncl (I := I) ((q' + 1 : ℕ) : ℤ)
          (logExtJ _ (formWedge f q' 1 V β'' (e.chartDt (hV.trans hW)))) :=
      (congrArg (logExtIncl (I := I) _) (map_zsmul _ _ _)).trans (map_zsmul (DirectSum.of _ _) _ _)
    have hdt : logExtIncl (f := f) (I := I) (V := V) ((1 : ℕ) : ℤ)
        (logExtJ _ (e.chartDt (hV.trans hW))) = e.equationAtS (hV.trans hW) •
          logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm (hV.trans hW))) :=
      e.logExtIncl_logExtJ_chartDt (hV.trans hW)
    rw [hγ, hz, logExtIncl_logExtJ_formWedge, hdt, smul_mul_assoc,
      Stacks.GradedAlgebra.mul_smul_eq, Stacks.GradedAlgebra.smul_mul_eq, _root_.mul_assoc,
      logExtIncl_logExtGen_mul_self, mul_zero, smul_zero, smul_zero]

include hI in
/-- **The relations of the local presentation hold in the exterior algebra.** If
`α + β ∧ dlog t = 0` as forms with logarithmic poles, then `α + β ∧ dlog t = 0` near every point
in the exterior algebra of `Ω^1_{X/S}(log Y)` as well. -/
theorem exists_local_logExt_eq_zero {q : ℕ} {V : X.Opens} (hV : V ≤ U)
    (α : Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), V))
    (β : Γ(relativeDifferentialForms f (q : ℤ), V))
    (hB : (logPolesFormsInclusion f I (q + 1)).val.app (op V) α +
      logFormsWedge hI hlog ((logPolesFormsInclusion f I q).val.app (op V) β) (e.dlogForm hV) = 0)
    (y : X) (hy : y ∈ V) :
    ∃ (V' : X.Opens) (h : V' ≤ V), y ∈ V' ∧
      logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ)
          (logExtJ _ ((relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
              (homOfLE h).op α)) +
        logExtIncl (f := f) (I := I) (q : ℤ)
            (logExtJ _ ((relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE h).op β)) *
          logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm (h.trans hV))) = 0 := by
  have h1 : (logPolesFormsInclusion f I (q + 1)).val.app (op V)
      (e.equationAt hV • α + formWedge f q 1 V β (e.chartDt hV)) = 0 := by
    refine (map_add _ _ _).trans ?_
    have h3 : (logPolesFormsInclusion f I (q + 1)).val.app (op V) (formWedge f q 1 V β
        (e.chartDt hV)) =
        e.equationAtR hV • logFormsWedge hI hlog ((logPolesFormsInclusion f I q).val.app (op V) β)
          (e.dlogForm hV) := by
      rw [← logFormsWedge_logPolesFormsInclusion hI hlog, e.logPolesFormsInclusion_chartDt hV,
        logFormsWedge_smul_right]
    rw [h3, show (logPolesFormsInclusion f I (q + 1)).val.app (op V) (e.equationAt hV • α) =
      e.equationAtR hV • (logPolesFormsInclusion f I (q + 1)).val.app (op V) α from
      ((logPolesFormsInclusion f I (q + 1)).val.app (op V)).hom.map_smul _ _, ← smul_add, hB]
    exact smul_zero _
  obtain ⟨V₁, h₁, hy₁, h2⟩ := exists_map_eq_zero_of_logPolesFormsInclusion_eq_zero hI hlog _ h1 y hy
  have hV₁ : V₁ ≤ U := h₁.trans hV
  set α₁ := (relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h₁).op α
  set β₁ := (relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE h₁).op β
  have h2' : e.equationAt hV₁ • α₁ + formWedge f q 1 V₁ β₁ (e.chartDt hV₁) = 0 := by
    have h := h2
    rw [map_add, forms_map_smul, formWedge_res, e.equationAt_res hV h₁] at h
    rw [← e.chartDt_res hV h₁]
    exact h
  have hκ₁ := e.totForm_chartDt (f := f) hV₁
  have h5 : e.equationAt hV₁ • α₁ +
      exactWedge f q V₁ (e.equationAt hV₁) (((-1 : ℤ) ^ q) • β₁) = 0 := by
    rw [show exactWedge f q V₁ (e.equationAt hV₁) (((-1 : ℤ) ^ q) • β₁) =
      ((-1 : ℤ) ^ q) • exactWedge f q V₁ (e.equationAt hV₁) β₁ from
        (exactWedgeHom q V₁ _).map_zsmul _ _, ← formWedge_eq_zsmul_exactWedge f q V₁ _ β₁ _ hκ₁]
    exact h2'
  have h6 := e.formRestriction_eq_zero_of_smul_add_exactWedge_eq_zero hlog hV₁ q α₁ _ h5
  have h7 : formRes I.subschemeι (q : ℤ) V₁ β₁ = 0 := by
    have h := congrArg (((-1 : ℤ) ^ q) • ·) ((formResHom (I := I) (q : ℤ) V₁).map_zsmul
      ((-1 : ℤ) ^ q) β₁ |>.symm.trans h6)
    exact (neg_one_pow_smul_neg_one_pow_smul q _).symm.trans (h.trans (zsmul_zero _))
  obtain ⟨V₂, h₂, hy₂, β', γ, hβ₂, hγ₁, hγ₂⟩ := e.exists_local_split hV₁ β₁ h7 y hy₁
  have hV₂ : V₂ ≤ U := h₂.trans hV₁
  have hαβ : (relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h₂).op α₁ =
      -formWedge f q 1 V₂ β' (e.chartDt hV₂) := by
    refine e.eq_of_equationAt_smul_eq hlog hV₂ ?_
    have h := congrArg ((relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE h₂).op) h2'
    rw [map_add, forms_map_smul, formWedge_res, e.chartDt_res hV₁ h₂, hβ₂, formWedge_add_left,
      formWedge_smul_left, hγ₁, add_zero, e.equationAt_res hV₁ h₂, map_zero] at h
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h
  refine ⟨V₂, h₂.trans h₁, hy₂, ?_⟩
  rw [← forms_map_map h₁ h₂, ← forms_map_map h₁ h₂]
  change logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) (logExtJ _
      ((relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h₂).op α₁)) +
    logExtIncl (f := f) (I := I) (q : ℤ) (logExtJ _
      ((relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE h₂).op β₁)) *
    logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm hV₂)) = 0
  have hdt : logExtIncl (f := f) (I := I) (V := V₂) ((1 : ℕ) : ℤ) (logExtJ _ (e.chartDt hV₂)) =
      e.equationAtS hV₂ • logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm hV₂)) :=
    e.logExtIncl_logExtJ_chartDt hV₂
  rw [hαβ, hβ₂, logExtIncl_logExtJ_neg, logExtIncl_logExtJ_formWedge, hdt, logExtIncl_logExtJ_add,
    logExtIncl_logExtJ_smul, add_mul, hγ₂, add_zero, Stacks.GradedAlgebra.mul_smul_eq,
    Stacks.GradedAlgebra.smul_mul_eq]
  exact neg_add_cancel _

/-- **The local presentation of a section of `⋀^{q+1} Ω^1_{X/S}(log Y)`**: over an open inside a
chart with local equation `t`, the section is `α + β ∧ dlog t` for forms `α`, `β` with no pole. -/
def LogExtRep {V : X.Opens} (hV : V ≤ U) (q : ℕ)
    (z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)) : Prop :=
  ∃ (α : Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), V))
    (β : Γ(relativeDifferentialForms f (q : ℤ), V)),
    logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) z =
      logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) (logExtJ _ α) +
        logExtIncl (f := f) (I := I) (q : ℤ) (logExtJ _ β) *
          logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm hV))

/-- A homogeneous local section of the exterior algebra of `Ω^1_{X/S}(log Y)` is determined by
its image in the ring of all local sections. -/
theorem logExtIncl_injective {V : X.Opens} (n : ℤ) :
    Function.Injective (logExtIncl (f := f) (I := I) (V := V) n) :=
  DirectSum.of_injective (β := fun i ↦ (((logExtAlg f I).piece i).val.obj (op V) : Type u)) n

/-- If the image of `z` in the ring of all local sections is `α + β ∧ dlog t`, then
`z = α + β ∧ dlog t` in degree `q + 1`. -/
theorem LogExtRep.eq {V : X.Opens} {hV : V ≤ U} {q : ℕ}
    {z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)}
    {α : Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), V)}
    {β : Γ(relativeDifferentialForms f (q : ℤ), V)}
    (h : logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) z =
      logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) (logExtJ _ α) +
        logExtIncl (f := f) (I := I) (q : ℤ) (logExtJ _ β) *
          logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm hV))) :
    z = logExtJ _ α + ((logExtAlg f I).mul (q : ℤ) 1).app (op V) (logExtJ _ β)
      (logExtGen (e.dlogForm hV)) := by
  refine logExtIncl_injective _ (h.trans ?_)
  rw [Stacks.GradedAlgebra.incl_mul_incl]
  exact (map_add (DirectSum.of _ _) _ _).symm

/-- Restricting a local presentation `z = α + β ∧ dlog t` to a smaller open gives the presentation
by the restrictions of `α` and `β`. -/
private theorem logExtIncl_res_eq (hlog : f.HasLogPolesDeRhamComplex I) {V : X.Opens}
    {hV : V ≤ U} {q : ℕ} {z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)}
    {α : Γ(relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), V)}
    {β : Γ(relativeDifferentialForms f (q : ℤ), V)}
    (hαβ : logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) z =
      logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) (logExtJ _ α) +
        logExtIncl (f := f) (I := I) (q : ℤ) (logExtJ _ β) *
          logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm hV)))
    {V' : X.Opens} (h : V' ≤ V) :
    logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ)
        (((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.map (homOfLE h).op z) =
      logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) (logExtJ _
          ((relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op α)) +
        logExtIncl (f := f) (I := I) (q : ℤ) (logExtJ _
            ((relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE h).op β)) *
          logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm (h.trans hV))) := by
  have hres := congrArg ((logExtAlg f I).toPresheafGradedAlgebra.totalRestrict (homOfLE h).op) hαβ
  rw [map_add, Stacks.GradedAlgebra.totalRestrict_mul, Stacks.GradedAlgebra.totalRestrict_incl,
    Stacks.GradedAlgebra.totalRestrict_incl, Stacks.GradedAlgebra.totalRestrict_incl,
    Stacks.GradedAlgebra.totalRestrict_incl] at hres
  refine hres.trans ?_
  refine congrArg₂ (· + ·) (congrArg (logExtIncl (f := f) (I := I) _) ?_)
    (congrArg₂ (· * ·) (congrArg (logExtIncl (f := f) (I := I) _) ?_)
      (congrArg (logExtIncl (f := f) (I := I) _) ?_))
  · exact (PresheafOfModules.naturality_apply ((logExteriorInclusion f I).app _).val _ α).symm
  · exact (PresheafOfModules.naturality_apply ((logExteriorInclusion f I).app _).val _ β).symm
  · exact (PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator (logPolesForms f I 1)).val _ _).symm.trans
      (congrArg logExtGen (e.dlogForm_res hlog hV h))

include hI in
/-- **Injectivity, locally**: a section of `⋀^{q+1} Ω^1_{X/S}(log Y)` with a local presentation
whose wedge product vanishes vanishes near every point. -/
theorem LogExtRep.exists_map_eq_zero {V : X.Opens} {hV : V ≤ U} {q : ℕ}
    {z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)} (hz : e.LogExtRep hV q z)
    (hg : ((logExteriorDesc f I hI hlog).app ((q + 1 : ℕ) : ℤ)).val.app (op V) z = 0)
    (y : X) (hy : y ∈ V) :
    ∃ (V' : X.Opens) (h : V' ≤ V), y ∈ V' ∧
      ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.map (homOfLE h).op z = 0 := by
  obtain ⟨α, β, hαβ⟩ := hz
  have hzeq := LogExtRep.eq e hαβ
  have hB : (logPolesFormsInclusion f I (q + 1)).val.app (op V) α +
      logFormsWedge hI hlog ((logPolesFormsInclusion f I q).val.app (op V) β)
          (e.dlogForm hV) = 0 := by
    have e1 : ((logExteriorDesc f I hI hlog).app ((q + 1 : ℕ) : ℤ)).val.app (op V) (logExtJ _ α) =
        (logPolesFormsInclusion f I (q + 1)).val.app (op V) α :=
      logExteriorDesc_app_logExteriorInclusion_app f I hI hlog (q + 1) (op V) α
    have e2 : ((logExteriorDesc f I hI hlog).app ((q + 1 : ℕ) : ℤ)).val.app (op V)
        (((logExtAlg f I).mul (q : ℤ) 1).app (op V) (logExtJ _ β) (logExtGen (e.dlogForm hV))) =
        logFormsWedge hI hlog ((logPolesFormsInclusion f I q).val.app (op V) β)
            (e.dlogForm hV) := by
      refine ((logExteriorDesc f I hI hlog).map_mul (q : ℤ) 1 (op V) _ _).trans ?_
      rw [logExteriorDesc_app_logExteriorInclusion_app, logExteriorDesc_app_one]
      rfl
    rw [← e1, ← e2]
    exact (map_add _ _ _).symm.trans ((congrArg _ hzeq.symm).trans hg)
  obtain ⟨V', h, hy', h0⟩ := e.exists_local_logExt_eq_zero hI hlog hV α β hB y hy
  refine ⟨V', h, hy', logExtIncl_injective _ ((?_ : _ = _).trans
    (Stacks.GradedAlgebra.incl_zero _ _).symm)⟩
  exact (logExtIncl_res_eq e hlog hαβ h).trans h0

/-- A section with the same image in the ring of all local sections as a section with a local
presentation has a local presentation. -/
theorem LogExtRep.of_logExtIncl_eq {V : X.Opens} {hV : V ≤ U} {q : ℕ}
    {z z' : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)}
    (h : logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) z =
      logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) z') (hz' : e.LogExtRep hV q z') :
    e.LogExtRep hV q z := by
  obtain ⟨α, β, hαβ⟩ := hz'
  exact ⟨α, β, h.trans hαβ⟩

/-- The sum of two sections with local presentations has a local presentation. -/
theorem LogExtRep.add {V : X.Opens} {hV : V ≤ U} {q : ℕ}
    {z z' : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)}
    (hz : e.LogExtRep hV q z) (hz' : e.LogExtRep hV q z') : e.LogExtRep hV q (z + z') := by
  obtain ⟨α, β, h⟩ := hz
  obtain ⟨α', β', h'⟩ := hz'
  refine ⟨α + α', β + β', ?_⟩
  refine ((Stacks.GradedAlgebra.incl_add (logExtAlg f I).toPresheafGradedAlgebra _ z z').trans
    (congrArg₂ (· + ·) h h')).trans ?_
  rw [logExtIncl_logExtJ_add, logExtIncl_logExtJ_add, add_mul]
  abel

/-- The zero section has a local presentation. -/
theorem LogExtRep.zero {V : X.Opens} (hV : V ≤ U) (q : ℕ) : e.LogExtRep (f := f) hV q 0 := by
  refine ⟨0, 0, ?_⟩
  have h0 : ∀ n : ℕ, logExtIncl (f := f) (I := I) (V := V) (n : ℤ)
      (logExtJ _ (0 : Γ(relativeDifferentialForms f (n : ℤ), V))) = 0 := fun n ↦
    (congrArg (logExtIncl (I := I) _) (map_zero _)).trans (map_zero (DirectSum.of _ _))
  rw [h0, h0, zero_mul, add_zero]
  exact map_zero (DirectSum.of _ _)

/-- A local function times a section with a local presentation has a local presentation. -/
theorem LogExtRep.smul {V : X.Opens} {hV : V ≤ U} {q : ℕ}
    {z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)}
    (hz : e.LogExtRep hV q z) (c : Γ(X, V)) : e.LogExtRep hV q (toStructScalar c • z) := by
  obtain ⟨α, β, h⟩ := hz
  refine ⟨c • α, c • β, ?_⟩
  refine ((Stacks.GradedAlgebra.incl_smul (logExtAlg f I).toPresheafGradedAlgebra _
    (toStructScalar c) z).trans (congrArg (toStructScalar c • ·) h)).trans ?_
  rw [logExtIncl_logExtJ_smul, logExtIncl_logExtJ_smul, Stacks.GradedAlgebra.smul_mul_eq, smul_add]

/-- The restriction of a section with a local presentation to a smaller open has a local
presentation. -/
theorem LogExtRep.res (hlog : f.HasLogPolesDeRhamComplex I) {V : X.Opens} {hV : V ≤ U} {q : ℕ}
    {z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)}
    (hz : e.LogExtRep hV q z) {V' : X.Opens} (h : V' ≤ V) :
    e.LogExtRep (h.trans hV) q
      (((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.map (homOfLE h).op z) := by
  obtain ⟨α, β, hαβ⟩ := hz
  exact ⟨_, _, logExtIncl_res_eq e hlog hαβ h⟩

/-- The image of the function `c`, as a `0`-form, in the exterior algebra of `Ω^1_{X/S}(log Y)`
is `c • 1`. -/
theorem logExtIncl_logExtJ_formOne {V : X.Opens} (c : Γ(X, V)) :
    logExtIncl (f := f) (I := I) ((0 : ℕ) : ℤ) (logExtJ _ (c • formOne (f := f) V)) =
      toStructScalar c • (1 : (logExtAlg f I).toPresheafGradedAlgebra.Total (op V)) := by
  rw [logExtIncl_logExtJ_smul]
  exact congrArg (toStructScalar c • ·) (congrArg (logExtIncl (I := I) _)
    ((logExteriorInclusion f I).map_one (op V)))

/-- If `s = ω + c dlog t`, then in the exterior algebra of `Ω^1_{X/S}(log Y)` the section `s`
is the image of `ω` plus `c` times `dlog t`. -/
theorem logExtIncl_logExtGen_eq {V : X.Opens} (hV : V ≤ U)
    (s : (logPolesForms f I 1).val.obj (op V))
    (ω : Γ(relativeDifferentialForms f ((0 + 1 : ℕ) : ℤ), V)) (c : Γ(X, V))
    (hs : s = (logPolesFormsInclusion f I 1).val.app (op V) ω +
      (show X.ringCatSheaf.obj.obj (op V) from c) • e.dlogForm hV) :
    logExtIncl (f := f) (I := I) 1 (logExtGen s) =
      logExtIncl (f := f) (I := I) 1 (logExtJ _ ω) +
        toStructScalar c • logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm hV)) := by
  rw [hs]
  refine ((congrArg (logExtIncl (f := f) (I := I) 1) (map_add _ _ _)).trans
    (map_add (DirectSum.of _ _) _ _)).trans (congrArg₂ (· + ·) ?_ ?_)
  · exact (congrArg (logExtIncl (f := f) (I := I) 1) (logExtJ_one ω)).symm
  · exact (congrArg (logExtIncl (f := f) (I := I) 1) (((Scheme.Modules.exteriorGenerator
      (logPolesForms f I 1)).val.app (op V)).hom.map_smul _ _)).trans
      (Stacks.GradedAlgebra.incl_smul _ _ _ _)

/-- A `1`-form with logarithmic poles of the shape `ω + c dlog t` has a local presentation. -/
theorem LogExtRep.gen {V : X.Opens} (hV : V ≤ U) (s : (logPolesForms f I 1).val.obj (op V))
    (ω : Γ(relativeDifferentialForms f ((0 + 1 : ℕ) : ℤ), V)) (c : Γ(X, V))
    (hs : s = (logPolesFormsInclusion f I 1).val.app (op V) ω +
      (show X.ringCatSheaf.obj.obj (op V) from c) • e.dlogForm hV) :
    e.LogExtRep hV 0 (logExtGen s) := by
  refine ⟨ω, c • formOne V, ?_⟩
  rw [logExtIncl_logExtJ_formOne, Stacks.GradedAlgebra.smul_mul_eq, _root_.one_mul]
  exact e.logExtIncl_logExtGen_eq hV s ω c hs

/-- **A local presentation is stable under multiplying by a `1`-form `ω + c dlog t` on the
right.** -/
theorem LogExtRep.mul_gen {V : X.Opens} {hV : V ≤ U} {q : ℕ}
    {z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)}
    (hz : e.LogExtRep hV q z) (s : (logPolesForms f I 1).val.obj (op V))
    (ω : Γ(relativeDifferentialForms f ((0 + 1 : ℕ) : ℤ), V)) (c : Γ(X, V))
    (hs : s = (logPolesFormsInclusion f I 1).val.app (op V) ω +
      (show X.ringCatSheaf.obj.obj (op V) from c) • e.dlogForm hV) :
    e.LogExtRep hV (q + 1)
        (((logExtAlg f I).mul ((q + 1 : ℕ) : ℤ) 1).app (op V) z (logExtGen s)) := by
  obtain ⟨α, β, h⟩ := hz
  have hgs := e.logExtIncl_logExtGen_eq hV s ω c hs
  refine ⟨formWedge f (q + 1) 1 V α ω, c • α - formWedge f q 1 V β ω, ?_⟩
  set A₀ := logExtIncl (f := f) (I := I) ((q + 1 : ℕ) : ℤ) (logExtJ _ α)
  set B₀ := logExtIncl (f := f) (I := I) (q : ℤ) (logExtJ _ β)
  set W₀ := logExtIncl (f := f) (I := I) ((1 : ℕ) : ℤ) (logExtJ _ ω)
  set E₀ := logExtIncl (f := f) (I := I) 1 (logExtGen (e.dlogForm hV))
  have hEW : E₀ * W₀ = -(W₀ * E₀) := by
    have hW : W₀ = logExtIncl (f := f) (I := I) 1
        (logExtGen ((logPolesFormsInclusion f I 1).val.app (op V) ω)) :=
      congrArg (logExtIncl (f := f) (I := I) 1) (logExtJ_one ω)
    rw [hW]
    exact logExtIncl_logExtGen_anticomm _ _
  have hEE : E₀ * E₀ = 0 := logExtIncl_logExtGen_mul_self _
  have hβ' : logExtIncl (f := f) (I := I) (((q + 1 : ℕ) : ℤ))
      (logExtJ _ (c • α - formWedge f q 1 V β ω)) = toStructScalar c • A₀ - B₀ * W₀ := by
    rw [sub_eq_add_neg, logExtIncl_logExtJ_add, logExtIncl_logExtJ_neg, logExtIncl_logExtJ_smul,
      logExtIncl_logExtJ_formWedge, ← sub_eq_add_neg]
  have hα' : logExtIncl (f := f) (I := I) (((q + 1 + 1 : ℕ) : ℤ))
      (logExtJ _ (formWedge f (q + 1) 1 V α ω)) = A₀ * W₀ :=
    logExtIncl_logExtJ_formWedge (q + 1) 1 α ω
  refine (Stacks.GradedAlgebra.incl_mul_incl (logExtAlg f I).toPresheafGradedAlgebra
    ((q + 1 : ℕ) : ℤ) 1 z (logExtGen s)).symm.trans ?_
  refine (congrArg₂ (· * ·) h hgs).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· + ·) hα'.symm (congrArg (· * E₀) hβ'.symm))
  exact Stacks.LogPoles.mul_gen_algebra A₀ B₀ W₀ E₀ (toStructScalar c) hEW hEE
    (fun x y ↦ Stacks.GradedAlgebra.smul_mul_eq _ _ x y)
    (fun x y ↦ Stacks.GradedAlgebra.mul_smul_eq _ _ x y)

include hI hlog in
/-- **A `1`-form with logarithmic poles is locally `ω + c dlog t`.** -/
theorem exists_local_logOneForm_eq {W : X.Opens} (hW : W ≤ U)
    (s : (logPolesForms f I 1).val.obj (op W))
    (y : X) (hy : y ∈ W) :
    ∃ (V : X.Opens) (hV : V ≤ W), y ∈ V ∧
      ∃ (ω : Γ(relativeDifferentialForms f ((0 + 1 : ℕ) : ℤ), V)) (c : Γ(X, V)),
        (logPolesForms f I 1).val.map (homOfLE hV).op s =
          (logPolesFormsInclusion f I 1).val.app (op V) ω +
            (show X.ringCatSheaf.obj.obj (op V) from c) • e.dlogForm (hV.trans hW) := by
  obtain ⟨V, hV, hyV, ω, η, hωη⟩ := e.exists_map_eq_logPolesChartForm (p := 0) hW s y hy
  obtain ⟨c, hc⟩ := AlgebraicGeometry.SheafOfModules.exists_eq_smul_one (deRhamAlgebras f) (op V) η
  refine ⟨V, hV, hyV, ω, c, hωη.trans ((e.logPolesChartForm_eq hI hlog (hV.trans hW) ω η).trans
    (congrArg ((logPolesFormsInclusion f I 1).val.app (op V) ω + ·) ?_))⟩
  refine (eq_of_heq (logFormsCast_heq _ _)).trans ?_
  have h1 : (logPolesFormsInclusion f I 0).val.app (op V) η =
      (show X.ringCatSheaf.obj.obj (op V) from c) • logFormsOne (f := f) (I := I) V :=
    (congrArg ((logPolesFormsInclusion f I 0).val.app (op V)) hc.symm).trans
      (((logPolesFormsInclusion f I 0).val.app (op V)).hom.map_smul _ _)
  refine (congrArg (logFormsWedge hI hlog (e.dlogForm (hV.trans hW))) h1).trans ?_
  exact (logFormsWedge_smul_right hI hlog _ _ _).trans
    (congrArg (_ • ·) (logFormsWedge_one_right hI hlog _))

include hI hlog in
/-- **Wedges of `1`-forms with logarithmic poles have local presentations.** -/
theorem exists_logExtRep_homogeneousProd (q : ℕ) {W : X.Opens} (hW : W ≤ U)
    (s : Fin (q + 1) → (logPolesForms f I 1).val.obj (op W)) (y : X) (hy : y ∈ W) :
    ∃ (V : X.Opens) (hV : V ≤ W), y ∈ V ∧ e.LogExtRep (hV.trans hW) q
      (((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.map (homOfLE hV).op
        ((logExtAlg f I).toPresheafGradedAlgebra.homogeneousProd (op W) (q + 1)
          fun i => logExtGen (s i))) := by
  induction q generalizing W with
  | zero =>
    obtain ⟨V, hV, hyV, ω, c, hωc⟩ := e.exists_local_logOneForm_eq hI hlog hW (s 0) y hy
    refine ⟨V, hV, hyV, LogExtRep.of_logExtIncl_eq e ?_ (LogExtRep.gen e (hV.trans hW) _ ω c hωc)⟩
    refine (congrArg (logExtIncl (f := f) (I := I) _)
      (Stacks.GradedAlgebra.homogeneousProd_naturality (O := X.sheaf.obj)
        (logExtAlg f I).toPresheafGradedAlgebra (homOfLE hV).op 1 _)).trans ?_
    refine (Stacks.GradedAlgebra.incl_mul_incl (logExtAlg f I).toPresheafGradedAlgebra 0 1
      ((logExtAlg f I).one.eval (op V)) _).symm.trans ?_
    refine ((congrArg (· * _) (Stacks.GradedAlgebra.one_eq_incl
      (logExtAlg f I).toPresheafGradedAlgebra (op V)).symm).trans (_root_.one_mul _)).trans ?_
    exact congrArg (logExtIncl (f := f) (I := I) 1)
      (PresheafOfModules.naturality_apply
        (Scheme.Modules.exteriorGenerator (logPolesForms f I 1)).val _ (s 0)).symm
  | succ q ih =>
    obtain ⟨V₁, hV₁, hyV₁, hrep⟩ := ih hW (fun i ↦ s i.castSucc) hy
    obtain ⟨V, hV, hyV, ω, c, hωc⟩ := e.exists_local_logOneForm_eq hI hlog (hV₁.trans hW)
      ((logPolesForms f I 1).val.map (homOfLE hV₁).op (s (Fin.last (q + 1)))) y hyV₁
    refine ⟨V, hV.trans hV₁, hyV, ?_⟩
    rw [logPolesForms_map_map] at hωc
    have key := LogExtRep.mul_gen e (LogExtRep.res e hlog hrep hV) _ ω c hωc
    refine LogExtRep.of_logExtIncl_eq e (congrArg (logExtIncl (f := f) (I := I) _) ?_) key
    refine ((logExtAlg f I).mul ((q + 1 : ℕ) : ℤ) 1).naturality (homOfLE
        (hV.trans hV₁)).op _ _ |>.trans ?_
    refine congrArg₂ (fun a b ↦ ((logExtAlg f I).mul ((q + 1 : ℕ) : ℤ) 1).app (op V) a b) ?_ ?_
    · rw [← PresheafOfModules.map_comp_apply]
      rfl
    · exact (PresheafOfModules.naturality_apply
        (Scheme.Modules.exteriorGenerator (logPolesForms f I 1)).val _ _).symm

/-- Restriction of sections of `⋀^n Ω^1_{X/S}(log Y)`. -/
abbrev logExtRes {n : ℤ} {V V' : X.Opens} (h : V' ≤ V)
    (z : ((logExtAlg f I).piece n).val.obj (op V)) : ((logExtAlg f I).piece n).val.obj (op V') :=
  ((logExtAlg f I).piece n).val.map (homOfLE h).op z

/-- A germ of a section of `⋀^{q+1} Ω^1_{X/S}(log Y)` at a point of the chart with a local
presentation. -/
def IsLogExtRepGerm (q : ℕ) (y : X)
    (a : ↑(TopCat.Presheaf.stalk
      ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf y)) : Prop :=
  ∃ (V : X.Opens) (hy : y ∈ V) (hVU : V ≤ U)
    (z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op V)),
    TopCat.Presheaf.germ ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf V y hy z = a ∧
      e.LogExtRep hVU q z

/-- The zero germ at a point of the chart has a local presentation. -/
theorem isLogExtRepGerm_zero (q : ℕ) (y : X) (hy : y ∈ U) :
    e.IsLogExtRepGerm (f := f) (I := I) q y 0 :=
  ⟨U, hy, le_rfl, 0, map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ
    ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf U y hy)), LogExtRep.zero e le_rfl q⟩

/-- The sum of two germs with local presentations has a local presentation. -/
theorem IsLogExtRepGerm.add (hlog : f.HasLogPolesDeRhamComplex I) {q : ℕ} {y : X}
    {a b : ↑(TopCat.Presheaf.stalk ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf y)}
    (ha : e.IsLogExtRepGerm q y a) (hb : e.IsLogExtRepGerm q y b) :
    e.IsLogExtRepGerm q y (a + b) := by
  obtain ⟨V₁, hy₁, hV₁, z₁, rfl, h₁⟩ := ha
  obtain ⟨V₂, hy₂, hV₂, z₂, rfl, h₂⟩ := hb
  refine ⟨V₁ ⊓ V₂, ⟨hy₁, hy₂⟩, inf_le_left.trans hV₁,
    logExtRes (inf_le_left : V₁ ⊓ V₂ ≤ V₁) z₁ + logExtRes (inf_le_right : V₁ ⊓ V₂ ≤ V₂) z₂, ?_,
    LogExtRep.add e (LogExtRep.res e hlog h₁ inf_le_left) (LogExtRep.res e hlog h₂ inf_le_right)⟩
  refine (map_add (ConcreteCategory.hom (TopCat.Presheaf.germ
    ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf _ y _)) _ _).trans ?_
  exact congrArg₂ (· + ·) (TopCat.Presheaf.germ_res_apply _ _ _ _ _)
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _)

/-- A germ of a function times a germ with a local presentation has a local presentation. -/
theorem IsLogExtRepGerm.smul (hlog : f.HasLogPolesDeRhamComplex I) {q : ℕ} {y : X}
    {a : ↑(TopCat.Presheaf.stalk ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf y)}
    (ha : e.IsLogExtRepGerm q y a) (r : ↑(TopCat.Presheaf.stalk X.sheaf.obj y)) :
    e.IsLogExtRepGerm q y (r • a) := by
  obtain ⟨V₀, hy₀, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r
  obtain ⟨V, hy, hVU, z, rfl, hz⟩ := ha
  refine ⟨V₀ ⊓ V, ⟨hy₀, hy⟩, inf_le_right.trans hVU,
    toStructScalar (X.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V ≤ V₀)).op c) •
      logExtRes (inf_le_right : V₀ ⊓ V ≤ V) z, ?_,
    LogExtRep.smul e (LogExtRep.res e hlog hz inf_le_right) _⟩
  refine (PresheafOfModules.germ_smul (R := X.sheaf.obj)
    ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val y (V₀ ⊓ V) ⟨hy₀, hy⟩ _ _).trans ?_
  exact congrArg₂ (· • ·) (TopCat.Presheaf.germ_res_apply _ _ _ _ _)
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _)

include hI in
/-- At a point of the chart, the germ of a wedge of `q + 1` local sections of `Ω^1_{X/S}(log Y)`
has a local presentation. -/
theorem isLogExtRepGerm_germ_homogeneousProd (hlog : f.HasLogPolesDeRhamComplex I) (q : ℕ)
    {y : X} (hyU : y ∈ U) {W : X.Opens} (hy : y ∈ W)
    (s : Fin (q + 1) → (logPolesForms f I 1).val.obj (op W)) :
    e.IsLogExtRepGerm q y (TopCat.Presheaf.germ
      ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf
      W y hy ((logExtAlg f I).toPresheafGradedAlgebra.homogeneousProd (op W) (q + 1)
        fun i => logExtGen (s i))) := by
  obtain ⟨V, hV, hyV, hrep⟩ := e.exists_logExtRep_homogeneousProd hI hlog q
    (inf_le_right : W ⊓ U ≤ U) (fun i ↦ (logPolesForms f I 1).val.map
      (homOfLE (inf_le_left : W ⊓ U ≤ W)).op (s i)) y ⟨hy, hyU⟩
  refine ⟨V, hyV, hV.trans inf_le_right, _, ?_, hrep⟩
  refine (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ?_
  have hnat : (logExtAlg f I).toPresheafGradedAlgebra.homogeneousProd (op (W ⊓ U)) (q + 1)
      (fun i ↦ logExtGen ((logPolesForms f I 1).val.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op
          (s i))) =
      ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op
        ((logExtAlg f I).toPresheafGradedAlgebra.homogeneousProd (op W) (q + 1)
          fun i ↦ logExtGen (s i)) := by
    refine Eq.trans ?_ (Stacks.GradedAlgebra.homogeneousProd_naturality (O := X.sheaf.obj)
      (logExtAlg f I).toPresheafGradedAlgebra (homOfLE (inf_le_left : W ⊓ U ≤ W)).op (q + 1) _).symm
    refine congrArg _ (funext fun i ↦ ?_)
    exact PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator (logPolesForms f I 1)).val _ (s i)
  rw [hnat]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

include hI in
/-- **Every germ of a section of `⋀^{q+1} Ω^1_{X/S}(log Y)` at a point of the chart has a local
presentation.** -/
theorem isLogExtRepGerm (hlog : f.HasLogPolesDeRhamComplex I) (q : ℕ) {y : X} (hyU : y ∈ U)
    (a : ↑(TopCat.Presheaf.stalk ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf y)) :
    e.IsLogExtRepGerm q y a := by
  have hspan := _root_.SheafOfModules.span_germWedgeSet_eq_top
    (SheafOfModules.algebras (Opens.grothendieckTopology X) (logPolesForms f I 1)) (q + 1) y
  have ha : a ∈ Submodule.span _ (_root_.SheafOfModules.germWedgeSet
      (SheafOfModules.algebras (Opens.grothendieckTopology X) (logPolesForms f I 1)) (q + 1) y) :=
    hspan ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨W, hy, s, rfl⟩ := hw
    exact e.isLogExtRepGerm_germ_homogeneousProd hI hlog q hyU hy s
  | zero => exact e.isLogExtRepGerm_zero q y hyU
  | add a b _ _ ha hb => exact IsLogExtRepGerm.add e hlog ha hb
  | smul r a _ ha => exact IsLogExtRepGerm.smul e hlog ha r

include hI in
/-- **Every section of `⋀^{q+1} Ω^1_{X/S}(log Y)` has local presentations** near every point of
the chart. -/
theorem exists_logExtRep_res (hlog : f.HasLogPolesDeRhamComplex I) (q : ℕ) {W : X.Opens}
    (z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op W)) {y : X} (hy : y ∈ W)
    (hyU : y ∈ U) :
    ∃ (V : X.Opens) (hV : V ≤ W) (hVU : V ≤ U), y ∈ V ∧ e.LogExtRep hVU q (logExtRes hV z) := by
  obtain ⟨V₁, hy₁, hV₁U, z₁, hgerm, hrep⟩ := e.isLogExtRepGerm hI hlog q hyU
    (TopCat.Presheaf.germ ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf W y hy z)
  obtain ⟨V, hyV, i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq
    ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.presheaf y hy₁ hy z₁ z hgerm
  refine ⟨V, leOfHom i₂, (leOfHom i₁).trans hV₁U, hyV, ?_⟩
  have h := LogExtRep.res e hlog hrep (leOfHom i₁)
  have heq' : logExtRes (f := f) (I := I) (leOfHom i₁) z₁ = logExtRes (leOfHom i₂) z := heq
  exact heq' ▸ h

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.Divisors.IdealTrivialization (logExtRes)

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- Restricting a section of `⋀^n Ω^1_{X/S}(log Y)` twice is restricting it once. -/
private theorem logExtRes_logExtRes {n : ℤ} {V V' V'' : X.Opens} (h : V' ≤ V) (h' : V'' ≤ V')
    (z : ((logExtAlg f I).piece n).val.obj (op V)) :
    logExtRes h' (logExtRes h z) = logExtRes (h'.trans h) z := by
  unfold logExtRes
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- On sections, `logExteriorDesc` commutes with restriction. -/
theorem logExteriorDesc_app_res {n : ℤ} {V V' : X.Opens} (h : V' ≤ V)
    (z : ((logExtAlg f I).piece n).val.obj (op V)) :
    ((logExteriorDesc f I hI hlog).app n).val.app (op V') (logExtRes h z) =
      ((logGradedAlgebra f I hI hlog).piece n).val.map (homOfLE h).op
        (((logExteriorDesc f I hI hlog).app n).val.app (op V) z) :=
  PresheafOfModules.naturality_apply ((logExteriorDesc f I hI hlog).app n).val _ z

/-- **The wedge product `⋀^{q+1} Ω^1_{X/S}(log Y) ⟶ Ω^{q+1}_{X/S}(log Y)` is injective on
sections.** -/
theorem logExteriorDesc_app_succ_eq_zero (q : ℕ) {W : X.Opens}
    (z : ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ)).val.obj (op W))
    (hz : ((logExteriorDesc f I hI hlog).app ((q + 1 : ℕ) : ℤ)).val.app (op W) z = 0) : z = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf
    ((logExtAlg f I).piece ((q + 1 : ℕ) : ℤ))) fun y hy ↦ ?_
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI y
  obtain ⟨V, hV, hVU, hyV, hrep⟩ := e.exists_logExtRep_res hI hlog q z hy hxU
  have hz' : ((logExteriorDesc f I hI hlog).app ((q + 1 : ℕ) : ℤ)).val.app (op V)
      (logExtRes hV z) = 0 := by
    rw [logExteriorDesc_app_res, hz]
    exact map_zero _
  obtain ⟨V', h', hyV', h0⟩ := Stacks.Divisors.IdealTrivialization.LogExtRep.exists_map_eq_zero e
    hI hlog hrep hz' y hyV
  refine ⟨V', h'.trans hV, hyV', ?_⟩
  change logExtRes (h'.trans hV) z = logExtRes (h'.trans hV) 0
  exact (logExtRes_logExtRes f I hV h' z).symm.trans (h0.trans (map_zero _).symm)

/-- The germ of the image of a restricted form in the exterior algebra of `Ω^1_{X/S}(log Y)` is
the germ of the image of the form. -/
theorem germ_logExtJ_res {n : ℕ} {V V' : X.Opens} (h : V' ≤ V) (y : X) (hy : y ∈ V')
    (α : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    TopCat.Presheaf.germ ((logExtAlg f I).piece (n : ℤ)).val.presheaf V' y hy
        (logExtJ (I := I) _ ((relativeDifferentialForms f (n : ℤ)).presheaf.map (homOfLE h).op α)) =
      TopCat.Presheaf.germ ((logExtAlg f I).piece (n : ℤ)).val.presheaf V y (h hy)
        (logExtJ (I := I) _ α) :=
  (congrArg (ConcreteCategory.hom (TopCat.Presheaf.germ ((logExtAlg f I).piece (n : ℤ)).val.presheaf
    V' y hy)) (PresheafOfModules.naturality_apply ((logExteriorInclusion f I).app _).val
      (homOfLE h).op α)).trans (TopCat.Presheaf.germ_res_apply _ (homOfLE h) _ _ _)

/-- A germ of a section of `⋀^0 Ω^1_{X/S}(log Y)` which is the image of a function. -/
def IsLogExtGermZero (y : X)
    (a : ↑(TopCat.Presheaf.stalk ((logExtAlg f I).piece ((0 : ℕ) : ℤ)).val.presheaf y)) : Prop :=
  ∃ (V : X.Opens) (hy : y ∈ V) (α : Γ(relativeDifferentialForms f ((0 : ℕ) : ℤ), V)),
    TopCat.Presheaf.germ ((logExtAlg f I).piece ((0 : ℕ) : ℤ)).val.presheaf V y hy
      (logExtJ (I := I) _ α) = a

/-- Every germ of a section of `⋀^0 Ω^1_{X/S}(log Y)` is the image of a germ of a function. -/
theorem isLogExtGermZero (y : X)
    (a : ↑(TopCat.Presheaf.stalk ((logExtAlg f I).piece ((0 : ℕ) : ℤ)).val.presheaf y)) :
    IsLogExtGermZero f I y a := by
  have hspan := _root_.SheafOfModules.span_germWedgeSet_eq_top
    (SheafOfModules.algebras (Opens.grothendieckTopology X) (logPolesForms f I 1)) 0 y
  have ha : a ∈ Submodule.span _ (_root_.SheafOfModules.germWedgeSet
      (SheafOfModules.algebras (Opens.grothendieckTopology X) (logPolesForms f I 1)) 0 y) :=
    hspan ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨W, hy, s, rfl⟩ := hw
    exact ⟨W, hy, formOne W, congrArg _ ((logExteriorInclusion f I).map_one (op W))⟩
  | zero =>
    refine ⟨⊤, show y ∈ (⊤ : X.Opens) from trivial, 0, ?_⟩
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  | add a b _ _ ha hb =>
    obtain ⟨V₁, hy₁, α₁, rfl⟩ := ha
    obtain ⟨V₂, hy₂, α₂, rfl⟩ := hb
    refine ⟨V₁ ⊓ V₂, show y ∈ V₁ ⊓ V₂ from ⟨hy₁, hy₂⟩,
      (relativeDifferentialForms f ((0 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op α₁ +
        (relativeDifferentialForms f ((0 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_right).op α₂, ?_⟩
    refine (congrArg _ (map_add _ _ _)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) ?_ ?_))
    · exact germ_logExtJ_res f I inf_le_left y _ α₁
    · exact germ_logExtJ_res f I inf_le_right y _ α₂
  | smul r a _ ha =>
    obtain ⟨V₀, hy₀, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj r
    obtain ⟨V, hy, α, rfl⟩ := ha
    refine ⟨V₀ ⊓ V, show y ∈ V₀ ⊓ V from ⟨hy₀, hy⟩,
      X.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V ≤ V₀)).op c •
        (relativeDifferentialForms f ((0 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_right).op α, ?_⟩
    refine (congrArg _ (((logExteriorInclusion f I).app _).val.app (op (V₀ ⊓ V)) |>.hom.map_smul
      (toStructScalar (X.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V ≤ V₀)).op c)) _)).trans ?_
    refine (PresheafOfModules.germ_smul (R := X.sheaf.obj)
      ((logExtAlg f I).piece ((0 : ℕ) : ℤ)).val y (V₀ ⊓ V) ⟨hy₀, hy⟩ _ _).trans ?_
    exact congrArg₂ (· • ·) (TopCat.Presheaf.germ_res_apply _ _ _ _ _)
      (germ_logExtJ_res f I inf_le_right y _ α)

/-- **The wedge product `⋀^0 Ω^1_{X/S}(log Y) ⟶ Ω^0_{X/S}(log Y)` is injective on sections.** -/
theorem logExteriorDesc_app_zero_eq_zero {W : X.Opens}
    (z : ((logExtAlg f I).piece ((0 : ℕ) : ℤ)).val.obj (op W))
    (hz : ((logExteriorDesc f I hI hlog).app ((0 : ℕ) : ℤ)).val.app (op W) z = 0) : z = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf
    ((logExtAlg f I).piece ((0 : ℕ) : ℤ))) fun y hy ↦ ?_
  obtain ⟨V₁, hy₁, α, hα⟩ := isLogExtGermZero f I y
    (TopCat.Presheaf.germ ((logExtAlg f I).piece ((0 : ℕ) : ℤ)).val.presheaf W y hy z)
  obtain ⟨V, hyV, i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq
    ((logExtAlg f I).piece ((0 : ℕ) : ℤ)).val.presheaf y hy₁ hy _ z hα
  have heq' : logExtRes (f := f) (I := I) (leOfHom i₁) (logExtJ (I := I) _ α) =
      logExtRes (leOfHom i₂) z := heq
  have hJ : ∀ {V₀ V₁' : X.Opens} (h : V₁' ≤ V₀)
      (β : Γ(relativeDifferentialForms f ((0 : ℕ) : ℤ), V₀)),
      logExtJ (I := I) _ ((relativeDifferentialForms f ((0 : ℕ) : ℤ)).presheaf.map
          (homOfLE h).op β) =
        logExtRes h (logExtJ (I := I) _ β) := fun h β ↦
    PresheafOfModules.naturality_apply ((logExteriorInclusion f I).app _).val (homOfLE h).op β
  have h1 : (logPolesFormsInclusion f I 0).val.app (op V)
      ((relativeDifferentialForms f ((0 : ℕ) : ℤ)).presheaf.map (homOfLE (leOfHom i₁)).op α)
      = 0 := by
    refine (logExteriorDesc_app_logExteriorInclusion_app f I hI hlog 0 (op V) _).symm.trans ?_
    refine (congrArg (((logExteriorDesc f I hI hlog).app ((0 : ℕ) : ℤ)).val.app (op V))
      ((hJ (leOfHom i₁) α).trans heq')).trans ?_
    rw [logExteriorDesc_app_res, hz]
    exact map_zero _
  obtain ⟨V', h', hyV', h0⟩
      := exists_map_eq_zero_of_logPolesFormsInclusion_eq_zero hI hlog _ h1 y hyV
  refine ⟨V', h'.trans (leOfHom i₂), hyV', ?_⟩
  change logExtRes (h'.trans (leOfHom i₂)) z = logExtRes (h'.trans (leOfHom i₂)) 0
  have h2 : logExtRes (f := f) (I := I) h' (logExtRes (leOfHom i₂) z) = 0 := by
    rw [← heq', ← hJ, ← hJ, h0]
    exact map_zero _
  exact (logExtRes_logExtRes f I (leOfHom i₂) h' z).symm.trans (h2.trans (map_zero _).symm)

/-- **The wedge product `⋀^p Ω^1_{X/S}(log Y) ⟶ Ω^p_{X/S}(log Y)` is injective on sections.** -/
theorem logExteriorDesc_app_natCast_eq_zero (p : ℕ) {W : X.Opens}
    (z : ((logExtAlg f I).piece (p : ℤ)).val.obj (op W))
    (hz : ((logExteriorDesc f I hI hlog).app (p : ℤ)).val.app (op W) z = 0) : z = 0 := by
  cases p with
  | zero => exact logExteriorDesc_app_zero_eq_zero f I hI hlog z hz
  | succ q => exact logExteriorDesc_app_succ_eq_zero f I hI hlog q z hz

/-- **`Ω^p_{X/S}(log Y) = ⋀^p Ω^1_{X/S}(log Y)`**: the morphism
`⋀^p Ω^1_{X/S}(log Y) ⟶ Ω^p_{X/S}(log Y)` sending `φ₁ ∧ ⋯ ∧ φ_p` to the wedge product of the `φᵢ`
is an isomorphism. -/
theorem isIso_logExteriorDesc_app (p : ℕ) : IsIso ((logExteriorDesc f I hI hlog).app (p : ℤ)) := by
  rw [AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap]
  refine fun y ↦ ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨W, hyW, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      ((logExtAlg f I).piece (p : ℤ)).val.presheaf (show ↑(TopCat.Presheaf.stalk
        ((logExtAlg f I).piece (p : ℤ)).val.presheaf y) from a)
    have ha' := (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ y
      ((logExteriorDesc f I hI hlog).app (p : ℤ)) W hyW z).symm.trans ha
    obtain ⟨V, hyV, i₁, i₂, h0⟩ := TopCat.Presheaf.germ_eq
      ((logGradedAlgebra f I hI hlog).piece (p : ℤ)).val.presheaf y hyW hyW _ 0
      (ha'.trans (map_zero _).symm)
    have h0' : ((logGradedAlgebra f I hI hlog).piece (p : ℤ)).val.map (homOfLE (leOfHom i₁)).op
        (((logExteriorDesc f I hI hlog).app (p : ℤ)).val.app (op W) z) = 0 := by
      refine Eq.trans ?_ (h0.trans (map_zero _))
      rfl
    have h1 : ((logExteriorDesc f I hI hlog).app (p : ℤ)).val.app (op V)
        (Stacks.Divisors.IdealTrivialization.logExtRes (leOfHom i₁) z) = 0 :=
      (logExteriorDesc_app_res f I hI hlog (leOfHom i₁) z).trans h0'
    exact (TopCat.Presheaf.germ_res_apply _ i₁ y hyV z).symm.trans
      ((congrArg _ (logExteriorDesc_app_natCast_eq_zero f I hI hlog p _ h1)).trans (map_zero _))
  · obtain ⟨W, hyW, χ, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      ((logGradedAlgebra f I hI hlog).piece (p : ℤ)).val.presheaf (show ↑(TopCat.Presheaf.stalk
        ((logGradedAlgebra f I hI hlog).piece (p : ℤ)).val.presheaf y) from a)
    obtain ⟨V, hVW, hyV, z, hz⟩ := exists_logExteriorDesc_app_eq f I hI hlog p χ y hyW
    refine ⟨(TopCat.Presheaf.germ ((logExtAlg f I).piece (p : ℤ)).val.presheaf V y hyV).hom z, ?_⟩
    refine (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ y
      ((logExteriorDesc f I hI hlog).app (p : ℤ)) V hyV z).trans ?_
    have hz' : ((logExteriorDesc f I hI hlog).app (p : ℤ)).val.app (op V) z =
        ((logGradedAlgebra f I hI hlog).piece (p : ℤ)).val.presheaf.map (homOfLE hVW).op χ := hz
    exact (congrArg (ConcreteCategory.hom (TopCat.Presheaf.germ
      ((logGradedAlgebra f I hI hlog).piece (p : ℤ)).val.presheaf V y hyV)) hz').trans
      (TopCat.Presheaf.germ_res_apply ((logGradedAlgebra f I hI hlog).piece (p : ℤ)).val.presheaf
        (homOfLE hVW) y hyV χ)

end AlgebraicGeometry.Scheme.Hom
