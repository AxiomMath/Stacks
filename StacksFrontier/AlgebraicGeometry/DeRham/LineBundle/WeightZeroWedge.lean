module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueSequenceBase
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.WedgeCalculus
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum

/-!
# The wedge product of the weight-zero forms of the complement of the zero section

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of its line bundle. The proof of Stacks Tag 0FUG uses that the
weight-zero part `Ω^•_{L^⋆/S,0}` of `π_*Ω^•_{L^⋆/S}` is a differential graded `𝒪_X`-algebra:
"as the degree zero part of a grading on `(L^⋆ → X)_*Ω^•_{L^⋆/S}`". This file constructs its
multiplication, the wedge product of forms on `L^⋆`, and proves the laws of a differential graded
algebra for it, in natural-number degrees.

## Main definitions

* `Stacks.LineBundle.Situation.ambientWedge`: the wedge product of sections of `π_*Ω^•_{L^⋆/S}`.
* `Stacks.LineBundle.Situation.weightZeroWedge`: the wedge product
  `Ω^p_{L^⋆/S,0} × Ω^q_{L^⋆/S,0} ⟶ Ω^{p+q}_{L^⋆/S,0}`, an `𝒪_X`-bilinear map of sheaves.
* `Stacks.LineBundle.Situation.weightZeroOne`: the unit `1 ∈ Ω^0_{L^⋆/S,0}`.

## Main results

* `Stacks.LineBundle.Situation.ambientWedge_mem`: the wedge product of two weight-zero forms has
  weight zero. Over a base chart this is the compatibility of the wedge product with the grading
  (Tag 0FU9); membership is local.
* `Stacks.LineBundle.Situation.ambientWedge_assoc`, `ambientWedge_one_left`,
  `ambientWedge_one_right`, `gradedDiff_ambientWedge`: associativity, unit and the graded Leibniz
  rule, read in the ring of all local forms on `L^⋆`.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules

attribute [local instance] gradedFormsGOne gradedFormsGMul gradedFormsGRing

universe u

namespace LaurentDeRham

open LaurentPolynomial

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- **The grading of `B` transported from the weight grading of `A[T;T⁻¹]` is multiplicative.** -/
instance transportGrading_gradedMonoid (e : A[T;T⁻¹] ≃ₐ[A] B) :
    SetLike.GradedMonoid (transportGrading (R := R) e) where
  one_mem := by simpa using algebraMap_mem_transportGrading (R := R) e (1 : A)
  mul_mem _ _ _ _ ha hb := mul_mem_transportGrading e ha hb

end LaurentDeRham

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### The wedge product of pushed-forward forms -/

/-- **The wedge product of sections of `π_*Ω^•_{L^⋆/S}`** over an open `U` of `X`: the wedge
product of forms of `L^⋆` over `π⁻¹U`. -/
def Situation.ambientWedge (p q : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (ξ : Γ(D.gradedAmbient q, U)) : Γ(D.gradedAmbient (p + q), U) :=
  Scheme.Hom.formWedge D.laurentToBase p q (D.laurentSpectrumToBase ⁻¹ᵁ U) η ξ

/-- A section of `π_*Ω^p_{L^⋆/S}`, read in the ring of all local forms of `L^⋆` over `π⁻¹U`. -/
abbrev Situation.ambientTot (p : ℕ) (U : D.X.Opens) :
    Γ(D.gradedAmbient p, U) →+
      totalForms (differentialAlgebras (inverseImageStructureMap D.laurentToBase))
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) :=
  Scheme.Hom.totForm D.laurentToBase p (D.laurentSpectrumToBase ⁻¹ᵁ U)

/-- Reading a section of `π_*Ω^p_{L^⋆/S}` in the ring of all local forms is injective. -/
theorem Situation.ambientTot_injective (p : ℕ) (U : D.X.Opens) :
    Function.Injective (D.ambientTot p U) :=
  Scheme.Hom.totForm_injective p _

/-- In the ring of all local forms, the wedge product `η ∧ ξ` is the product of `η` and `ξ`. -/
theorem Situation.ambientTot_ambientWedge (p q : ℕ) (U : D.X.Opens)
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient q, U)) :
    D.ambientTot (p + q) U (D.ambientWedge p q U η ξ) = D.ambientTot p U η * D.ambientTot q U ξ :=
  Scheme.Hom.totForm_formWedge p q _ η ξ

/-- A section of `π_*Ω^m_{L^⋆/S}` read in another, equal, degree. -/
abbrev Situation.ambientCast {m n : ℕ} (h : m = n) {U : D.X.Opens}
    (η : Γ(D.gradedAmbient m, U)) : Γ(D.gradedAmbient n, U) :=
  Scheme.Hom.formCast (f := D.laurentToBase) h η

/-- Reading a form in an equal degree does not change it in the ring of all local forms. -/
theorem Situation.ambientTot_ambientCast {m n : ℕ} (h : m = n) {U : D.X.Opens}
    (η : Γ(D.gradedAmbient m, U)) :
    D.ambientTot n U (D.ambientCast h η) = D.ambientTot m U η :=
  Scheme.Hom.totForm_formCast h η

/-- The constant form `1` is the unit of the ring of all local forms. -/
theorem Situation.ambientTot_gradedOne (U : D.X.Opens) :
    D.ambientTot 0 U (D.gradedOne U) = 1 :=
  rfl

/-! ### The laws of the wedge product -/

/-- **The wedge product of pushed-forward forms is associative.** -/
theorem Situation.ambientWedge_assoc (p q r : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (ξ : Γ(D.gradedAmbient q, U)) (ζ : Γ(D.gradedAmbient r, U)) :
    D.ambientWedge (p + q) r U (D.ambientWedge p q U η ξ) ζ =
      D.ambientCast (Nat.add_assoc p q r).symm
        (D.ambientWedge p (q + r) U η (D.ambientWedge q r U ξ ζ)) := by
  refine D.ambientTot_injective _ U ?_
  rw [D.ambientTot_ambientCast, D.ambientTot_ambientWedge, D.ambientTot_ambientWedge,
    D.ambientTot_ambientWedge, D.ambientTot_ambientWedge, mul_assoc]

/-- **The constant form `1` is a left unit for the wedge product.** -/
theorem Situation.ambientWedge_one_left (p : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U)) :
    D.ambientWedge 0 p U (D.gradedOne U) η = D.ambientCast (Nat.zero_add p).symm η := by
  refine D.ambientTot_injective _ U ?_
  rw [D.ambientTot_ambientCast, D.ambientTot_ambientWedge, D.ambientTot_gradedOne, one_mul]

/-- **The constant form `1` is a right unit for the wedge product.** -/
theorem Situation.ambientWedge_one_right (p : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U)) :
    D.ambientWedge p 0 U η (D.gradedOne U) = η := by
  refine D.ambientTot_injective _ U ?_
  rw [D.ambientTot_ambientWedge, D.ambientTot_gradedOne, mul_one]
  rfl

/-- **The graded Leibniz rule** `d(η ∧ ξ) = dη ∧ ξ + (-1)^p η ∧ dξ`. -/
theorem Situation.gradedDiff_ambientWedge (p q : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (ξ : Γ(D.gradedAmbient q, U)) :
    D.gradedDiff (p + q) U (D.ambientWedge p q U η ξ) =
      D.ambientCast (Nat.add_right_comm p 1 q) (D.ambientWedge (p + 1) q U (D.gradedDiff p U η) ξ) +
        (-1 : ℤ) ^ p • D.ambientWedge p (q + 1) U η (D.gradedDiff q U ξ) := by
  refine D.ambientTot_injective _ U ?_
  rw [map_add, map_zsmul, D.ambientTot_ambientCast, D.ambientTot_ambientWedge,
    show D.ambientTot (p + q + 1) U (D.ambientWedge p (q + 1) U η (D.gradedDiff q U ξ)) =
      D.ambientTot p U η * D.ambientTot (q + 1) U (D.gradedDiff q U ξ) from
      D.ambientTot_ambientWedge p (q + 1) U η _]
  exact Scheme.Hom.totForm_deRhamD_formWedge p q _ η ξ

/-- The wedge product is additive in its first argument. -/
theorem Situation.ambientWedge_add_left (p q : ℕ) (U : D.X.Opens)
    (η η' : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient q, U)) :
    D.ambientWedge p q U (η + η') ξ = D.ambientWedge p q U η ξ + D.ambientWedge p q U η' ξ :=
  Scheme.Hom.formWedge_add_left p q _ η η' ξ

/-- The wedge product is additive in its second argument. -/
theorem Situation.ambientWedge_add_right (p q : ℕ) (U : D.X.Opens)
    (η : Γ(D.gradedAmbient p, U)) (ξ ξ' : Γ(D.gradedAmbient q, U)) :
    D.ambientWedge p q U η (ξ + ξ') = D.ambientWedge p q U η ξ + D.ambientWedge p q U η ξ' :=
  Scheme.Hom.formWedge_add_right p q _ η ξ ξ'

/-- The wedge product is `𝒪_X`-linear in its first argument. -/
theorem Situation.ambientWedge_smul_left (p q : ℕ) (U : D.X.Opens) (r : Γ(D.X, U))
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient q, U)) :
    D.ambientWedge p q U (r • η) ξ = r • D.ambientWedge p q U η ξ :=
  ((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.mul (p : ℤ) (q : ℤ)).map_smul_left
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) (D.laurentPullbackFunction U r) η ξ

/-- The wedge product is `𝒪_X`-linear in its second argument. -/
theorem Situation.ambientWedge_smul_right (p q : ℕ) (U : D.X.Opens) (r : Γ(D.X, U))
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient q, U)) :
    D.ambientWedge p q U η (r • ξ) = r • D.ambientWedge p q U η ξ :=
  ((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.mul (p : ℤ) (q : ℤ)).map_smul_right
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) (D.laurentPullbackFunction U r) η ξ

/-- **The wedge product commutes with restriction** to a smaller open of `X`. -/
theorem Situation.ambientWedge_map (p q : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient q, U)) :
    (D.gradedAmbient (p + q)).presheaf.map (homOfLE hWU).op (D.ambientWedge p q U η ξ) =
      D.ambientWedge p q W ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op η)
        ((D.gradedAmbient q).presheaf.map (homOfLE hWU).op ξ) :=
  ((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.mul (p : ℤ) (q : ℤ)).naturality
    (D.laurentPreimageHom hWU).op η ξ


/-! ### Weight zero is closed under the wedge product -/

attribute [local instance] Situation.AffineChart.algebraRA Situation.BaseChart.algebraRB
  Situation.BaseChart.algebraAB Situation.BaseChart.isScalarTower

/-- **Over a base chart the identification of the forms of `L^⋆` with Kähler forms is
multiplicative.** -/
theorem Situation.BaseChart.formsL_mul {D : Situation.{u}} (c : D.BaseChart) (p q : ℕ)
    (x : Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f) (p : ℤ),
      D.laurentSpectrumToBase ⁻¹ᵁ c.U.1))
    (y : Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f) (q : ℤ),
      D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)) :
    (c.formsL (p + q)).hom
        (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials
          (D.laurentSpectrumToBase ≫ D.f))).mul (p : ℤ) q).app
          (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)) x y) =
      exteriorPower.wedgeMul p q ((c.formsL p).hom x) ((c.formsL q).hom y) := by
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_mul
    (D.laurentSpectrumToBase ≫ D.f) c.isAffineOpen_preimage c.V.2 c.preimage_le p q x y)
  congr 1

/-- **Over a base chart the wedge product is the wedge product of Kähler forms.** -/
theorem Situation.BaseChart.formsLF_ambientWedge {D : Situation.{u}} (c : D.BaseChart) (p q : ℕ)
    (η : Γ(D.gradedAmbient p, c.U.1)) (ξ : Γ(D.gradedAmbient q, c.U.1)) :
    c.formsLF (p + q) (D.ambientWedge p q c.U.1 η ξ) =
      exteriorPower.wedgeMul p q (c.formsLF p η) (c.formsLF q ξ) := by
  have h := c.formsL_mul p q (D.secG p c.U.1 η) (D.secG q c.U.1 ξ)
  have h3 : D.secG (p + q) c.U.1 (D.ambientWedge p q c.U.1 η ξ) =
      ((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials
          (D.laurentSpectrumToBase ≫ D.f))).mul (p : ℤ) q).app
          (op (D.laurentSpectrumToBase ⁻¹ᵁ c.U.1)) (D.secG p c.U.1 η) (D.secG q c.U.1 ξ) := rfl
  have h2 := congrArg (c.toΩB (p + q)) h
  rw [c.toΩB_wedgeMul p q, ← h3] at h2
  exact h2

/-- **The wedge product of two weight-zero forms has weight zero.** Over a base chart the wedge
product is compatible with the gradings (Tag 0FU9), and membership in the weight-zero part is
local. -/
theorem Situation.ambientWedge_mem (p q : ℕ) {U : D.X.Opens} (x : Γ(D.weightZero p, U))
    (y : Γ(D.weightZero q, U)) :
    D.ambientWedge p q U (D.weightZeroVal p x) (D.weightZeroVal q y) ∈
      (D.gradedLaurentForms (p + q) 0).obj (op U) := by
  refine D.mem_gradedLaurentForms_of_locally (p + q) 0 _ fun z hz => ?_
  obtain ⟨c, hzc, hcU⟩ := D.exists_baseChart hz
  refine ⟨c.U.1, hcU, hzc, ?_⟩
  have hx := D.weightZeroVal_mem p ((D.weightZero p).presheaf.map (homOfLE hcU).op x)
  have hy := D.weightZeroVal_mem q ((D.weightZero q).presheaf.map (homOfLE hcU).op y)
  rw [D.weightZeroVal_map] at hx hy
  refine D.mem_gradedLaurentForms_of_eq (p + q) 0 (D.ambientWedge_map p q hcU _ _) ?_
  have hx' := (c.mem_iff_ψE p _).1 hx
  have hy' := (c.mem_iff_ψE q _).1 hy
  have hw := KaehlerDifferential.gradedDifferentialFormComponent_wedgeMul_mem _ p q hx' hy'
  rw [c.ψE_apply, c.ψE_apply, ← c.formsLF_ambientWedge, ← c.ψE_apply] at hw
  exact (c.mem_iff_ψE (p + q) (D.ambientWedge p q c.U.1 _ _)).2 hw

/-- **The constant form `1` has weight zero.** -/
theorem Situation.gradedOne_mem (U : D.X.Opens) :
    D.gradedOne U ∈ (D.gradedLaurentForms 0 0).obj (op U) := by
  refine D.mem_gradedLaurentForms_of_locally 0 0 _ fun z hz => ?_
  obtain ⟨W, hW, hzW, hWU⟩ := Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens hz
  refine ⟨W, hWU, hzW, ?_⟩
  refine D.mem_gradedLaurentForms_of_eq 0 0 (D.gradedOne_map hWU) ?_
  exact D.mem_gradedLaurentForms ⟨W, hW⟩ (D.isHomogeneousLaurentForm_gradedOne ⟨W, hW⟩)

/-- **The wedge product `Ω^p_{L^⋆/S,0} × Ω^q_{L^⋆/S,0} ⟶ Ω^{p+q}_{L^⋆/S,0}`**, an
`𝒪_X`-bilinear map of sheaves: the wedge product of forms of `L^⋆`, which preserves weight
zero (`Stacks.LineBundle.Situation.ambientWedge_mem`). -/
def Situation.weightZeroWedge (p q : ℕ) :
    _root_.SheafOfModules.BilinearMap (D.weightZero p) (D.weightZero q) (D.weightZero (p + q)) where
  app U := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y =>
      D.weightZeroMk (p + q) (D.ambientWedge p q U.unop (D.weightZeroVal p x) (D.weightZeroVal q y))
        (D.ambientWedge_mem p q x y))
      fun _ _ => D.weightZeroVal_injective (p + q) (D.ambientWedge_add_right p q U.unop _ _ _))
    fun _ _ => AddMonoidHom.ext fun _ =>
      D.weightZeroVal_injective (p + q) (D.ambientWedge_add_left p q U.unop _ _ _)
  map_smul_left U r _ _ :=
    D.weightZeroVal_injective (p + q) (D.ambientWedge_smul_left p q U.unop r _ _)
  map_smul_right U r _ _ :=
    D.weightZeroVal_injective (p + q) (D.ambientWedge_smul_right p q U.unop r _ _)
  naturality f _ _ := D.weightZeroVal_injective (p + q)
    (((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.mul (p : ℤ) (q : ℤ)).naturality
      ((Opens.map D.laurentSpectrumToBase.base).map f.unop).op _ _)

/-- The underlying form of the weight-zero wedge product `x ∧ y` is the wedge product of the
underlying forms of `x` and `y`. -/
theorem Situation.weightZeroVal_weightZeroWedge (p q : ℕ) (U : D.X.Opens)
    (x : Γ(D.weightZero p, U)) (y : Γ(D.weightZero q, U)) :
    D.weightZeroVal (p + q) ((D.weightZeroWedge p q).app (op U) x y) =
      D.ambientWedge p q U (D.weightZeroVal p x) (D.weightZeroVal q y) :=
  rfl

/-- **The unit `1 ∈ Ω^0_{L^⋆/S,0}`**, the constant form `1`. -/
def Situation.weightZeroOne : (D.weightZero 0).sections :=
  PresheafOfModules.sectionsMk (fun U => D.weightZeroMk 0 (D.gradedOne U.unop)
      (D.gradedOne_mem U.unop))
    fun _ _ f => D.weightZeroVal_injective 0
      (PresheafOfModules.sections_property D.laurentFormsAlgebra.one
        ((Opens.map D.laurentSpectrumToBase.base).map f.unop).op)

/-- The underlying form of the unit `1 ∈ Ω^0_{L^⋆/S,0}` is the constant form `1`. -/
theorem Situation.weightZeroVal_weightZeroOne (U : D.X.Opens) :
    D.weightZeroVal 0 (D.weightZeroOne.eval (op U)) = D.gradedOne U :=
  rfl

/-! ### The laws of the weight-zero wedge product -/

/-- Taking the underlying form of a weight-zero form commutes with integer multiples. -/
theorem Situation.weightZeroVal_zsmul (p : ℕ) {U : D.X.Opens} (n : ℤ) (x : Γ(D.weightZero p, U)) :
    D.weightZeroVal p (n • x) = n • D.weightZeroVal p x :=
  map_zsmul (AddMonoidHom.mk' (D.weightZeroVal p (U := U)) (D.weightZeroVal_add p)) n x

/-- A section of `Ω^m_{L^⋆/S,0}` read in another, equal, degree. -/
def Situation.weightZeroCast {m n : ℕ} (h : m = n) {U : D.X.Opens} (x : Γ(D.weightZero m, U)) :
    Γ(D.weightZero n, U) :=
  _root_.SheafOfModules.gradedCast (fun k : ℕ => Γ(D.weightZero k, U)) h x

/-- A weight-zero form read in an equal degree is heterogeneously equal to itself. -/
theorem Situation.weightZeroCast_heq {m n : ℕ} (h : m = n) {U : D.X.Opens}
    (x : Γ(D.weightZero m, U)) : HEq (D.weightZeroCast h x) x := by
  subst h
  rfl

/-- The underlying form of a weight-zero form read in an equal degree is its underlying form
read in that degree. -/
theorem Situation.weightZeroVal_weightZeroCast {m n : ℕ} (h : m = n) {U : D.X.Opens}
    (x : Γ(D.weightZero m, U)) :
    D.weightZeroVal n (D.weightZeroCast h x) = D.ambientCast h (D.weightZeroVal m x) := by
  subst h
  rfl

/-- Two weight-zero forms of equal degrees are heterogeneously equal when their values agree
after transport. -/
theorem Situation.weightZero_heq_of_val {m n : ℕ} (h : m = n) {U : D.X.Opens}
    (x : Γ(D.weightZero m, U)) (y : Γ(D.weightZero n, U))
    (hv : D.ambientCast h (D.weightZeroVal m x) = D.weightZeroVal n y) : HEq x y := by
  subst h
  exact heq_of_eq (D.weightZeroVal_injective m hv)

/-- **The weight-zero wedge product is associative**, up to the identification of the degrees
`(p + q) + r = p + (q + r)`. -/
theorem Situation.weightZeroWedge_assoc (p q r : ℕ) (U : D.X.Opens) (x : Γ(D.weightZero p, U))
    (y : Γ(D.weightZero q, U)) (z : Γ(D.weightZero r, U)) :
    HEq ((D.weightZeroWedge (p + q) r).app (op U) ((D.weightZeroWedge p q).app (op U) x y) z)
      ((D.weightZeroWedge p (q + r)).app (op U) x ((D.weightZeroWedge q r).app (op U) y z)) :=
  (D.weightZero_heq_of_val (Nat.add_assoc p q r).symm _ _
    (D.ambientWedge_assoc p q r U _ _ _).symm).symm

/-- **The unit `1` is a left unit for the weight-zero wedge product**, up to the identification
of the degrees `0 + p = p`. -/
theorem Situation.weightZeroWedge_one_left (p : ℕ) (U : D.X.Opens) (x : Γ(D.weightZero p, U)) :
    HEq ((D.weightZeroWedge 0 p).app (op U) (D.weightZeroOne.eval (op U)) x) x :=
  (D.weightZero_heq_of_val (Nat.zero_add p).symm x _
    (D.ambientWedge_one_left p U _).symm).symm

/-- **The unit `1` is a right unit for the weight-zero wedge product.** -/
theorem Situation.weightZeroWedge_one_right (p : ℕ) (U : D.X.Opens) (x : Γ(D.weightZero p, U)) :
    (D.weightZeroWedge p 0).app (op U) x (D.weightZeroOne.eval (op U)) = x :=
  D.weightZeroVal_injective p (D.ambientWedge_one_right p U _)

/-- **The graded Leibniz rule for the weight-zero wedge product.** -/
theorem Situation.weightZeroD_weightZeroWedge (p q : ℕ) (U : D.X.Opens)
    (x : Γ(D.weightZero p, U)) (y : Γ(D.weightZero q, U)) :
    D.weightZeroD (p + q) U ((D.weightZeroWedge p q).app (op U) x y) =
      D.weightZeroCast (Nat.add_right_comm p 1 q)
          ((D.weightZeroWedge (p + 1) q).app (op U) (D.weightZeroD p U x) y) +
        (-1 : ℤ) ^ p • (show Γ(D.weightZero (p + q + 1), U) from
          (D.weightZeroWedge p (q + 1)).app (op U) x (D.weightZeroD q U y)) := by
  refine D.weightZeroVal_injective (p + q + 1) ?_
  refine (D.gradedDiff_ambientWedge p q U _ _).trans ?_
  refine Eq.trans ?_ (D.weightZeroVal_add (p + q + 1) _ _).symm
  refine congrArg₂ (· + ·) (D.weightZeroVal_weightZeroCast (Nat.add_right_comm p 1 q)
    ((D.weightZeroWedge (p + 1) q).app (op U) (D.weightZeroD p U x) y)).symm ?_
  exact (D.weightZeroVal_zsmul (p + q + 1) ((-1 : ℤ) ^ p)
    ((D.weightZeroWedge p (q + 1)).app (op U) x (D.weightZeroD q U y))).symm

/-! ### The pullback of forms is a homomorphism of algebras -/

/-- **The pullback of forms along `π` is multiplicative**: `π^*(α ∧ β) = π^*α ∧ π^*β`. This is the
multiplicativity of the canonical homomorphism of Tag 07HX. -/
theorem Situation.pullbackG_formWedge (p q : ℕ) (U : D.X.Opens)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U))
    (β : Γ(Scheme.Hom.relativeDifferentialForms D.f (q : ℤ), U)) :
    D.pullbackG (p + q) U (Scheme.Hom.formWedge D.f p q U α β) =
      D.ambientWedge p q U (D.pullbackG p U α) (D.pullbackG q U β) :=
  (Scheme.Hom.deRhamFormsPushforwardHom D.laurentSpectrumToBase D.f
    (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S) ((Category.comp_id _).symm)).map_mul
    (p : ℤ) (q : ℤ) (op U) α β

/-- **The pullback of forms along `π` is unital.** -/
theorem Situation.pullbackG_one (U : D.X.Opens) :
    D.pullbackG 0 U ((Scheme.Hom.deRhamAlgebras D.f).exterior.one.eval (op U)) = D.gradedOne U :=
  (Scheme.Hom.deRhamFormsPushforwardHom D.laurentSpectrumToBase D.f
    (D.laurentSpectrumToBase ≫ D.f) (𝟙 D.S) ((Category.comp_id _).symm)).map_one (op U)

/-- **The inclusion `Ω^p_{X/S} ⟶ Ω^p_{L^⋆/S,0}` is the pullback of forms along `π` over every
open of `X`**, not only over the base charts where it is glued from. -/
theorem Situation.weightZeroVal_pullbackHom (p : ℕ) (U : D.X.Opens)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.weightZeroVal p ((D.pullbackHom p).app U α) = D.pullbackG p U α := by
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq (D.gradedAmbient p) U _ _
    fun z hz => ?_
  obtain ⟨c, hzc, hcU⟩ := D.exists_baseChart hz
  refine ⟨c.U.1, hcU, hzc, ?_⟩
  have h1 : (D.pullbackHom p).app c.U.1
      ((Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)).presheaf.map (homOfLE hcU).op α) =
        (D.weightZero p).presheaf.map (homOfLE hcU).op ((D.pullbackHom p).app U α) :=
    PresheafOfModules.naturality_apply (D.pullbackHom p).val (homOfLE hcU).op α
  refine Eq.trans ?_ (D.pullbackG_map p hcU α).symm
  refine (D.weightZeroVal_map p hcU _).symm.trans ?_
  rw [← h1]
  exact D.pullbackHom_app p c _

/-- **The inclusion `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` is multiplicative.** -/
theorem Situation.pullbackHom_formWedge (p q : ℕ) (U : D.X.Opens)
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U))
    (β : Γ(Scheme.Hom.relativeDifferentialForms D.f (q : ℤ), U)) :
    (D.pullbackHom (p + q)).app U (Scheme.Hom.formWedge D.f p q U α β) =
      (D.weightZeroWedge p q).app (op U) ((D.pullbackHom p).app U α)
        ((D.pullbackHom q).app U β) := by
  refine D.weightZeroVal_injective (p + q) ?_
  refine (D.weightZeroVal_pullbackHom (p + q) U _).trans
    ((D.pullbackG_formWedge p q U α β).trans ?_)
  rw [← D.weightZeroVal_pullbackHom, ← D.weightZeroVal_pullbackHom]
  rfl

/-- **The inclusion `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` is unital.** -/
theorem Situation.pullbackHom_one (U : D.X.Opens) :
    (D.pullbackHom 0).app U ((Scheme.Hom.deRhamAlgebras D.f).exterior.one.eval (op U)) =
      D.weightZeroOne.eval (op U) :=
  D.weightZeroVal_injective 0 ((D.weightZeroVal_pullbackHom 0 U _).trans (D.pullbackG_one U))

end Stacks.LineBundle
