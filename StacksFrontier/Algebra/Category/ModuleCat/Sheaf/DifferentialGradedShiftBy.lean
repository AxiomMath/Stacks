module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone

/-!
# The shift of a right differential graded module by an integer

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `M` be a right differential graded `A`-module. For an integer `k` the shift `M[k]` has the
shifted complex, `M[k]^n = M^{n + k}` with differential `(-1)^k d`, and the right action of `M`
read in the shifted degree. The degree-one shift is the shift
`SheafOfModules.DifferentialGradedModule.shift` which the cones of `DifferentialGradedCone.lean`
are built from.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.shiftBy`: the shift `M[k]`.
* `SheafOfModules.DifferentialGradedModule.shiftByMap`: the shift of a morphism, with the same
  component maps.
* `SheafOfModules.DifferentialGradedModule.shiftByHomEquiv`: morphisms `T[k] ⟶ Q` are morphisms
  `T ⟶ Q[-k]`, naturally in `Q`.

## Main results

* `SheafOfModules.DifferentialGradedModule.shiftBy_zero`, `shiftBy_add` and `shiftBy_one`:
  `M[0] = M`, `M[n + m] = M[m][n]` and `M[1] = shift M`, as equalities of modules.
* `SheafOfModules.DifferentialGradedModule.shiftByHomEquiv_comp`: the bijection is natural in the
  target.

## Implementation notes

The construction of the action and its three laws is the one of the private shift of
`DifferentialGradedAxiomB.lean`, which is stated over a ringed site in a single universe; here the
base is an arbitrary sheaf of rings on an arbitrary site and the universes are independent, which
is what the two ringed topoi of a base change need. The equalities of modules are proved from an
equality of complexes together with a heterogeneous equality of the actions, and every identity
between morphisms below is checked degreewise, where the transports are `eqToHom`s.

## References

* [Stacks Project, Tag 0FRY](https://stacks.math.columbia.edu/tag/0FRY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### Transport lemmas -/

private lemma dependent_apply2_heq {ι κ : Type*} {B : ι → Type*} {D : κ → Type*}
    (f : ∀ i j, B i → D j) {i i' : ι} {j j' : κ} (hi : i = i') (hj : j = j')
    {x : B i} {y : B i'} (hxy : HEq x y) : HEq (f i j x) (f i' j' y) := by
  subst i' j'
  obtain rfl := eq_of_heq hxy
  rfl

private lemma gradedCast_neg_heq {ι : Type*} {B : ι → Type*} {i j : ι}
    [∀ i, AddGroup (B i)] (h : i = j) (x : B i) :
    HEq (-(SheafOfModules.gradedCast B h x)) (-x) := by subst j; rfl

private lemma sheafMap_neg_apply {P Q : SheafOfModules.{m} R} (f : P ⟶ Q) (U : Cᵒᵖ)
    (x : P.val.obj U) :
    (ConcreteCategory.hom ((-f).val.app U)) x =
      -(ConcreteCategory.hom (f.val.app U) x) := by
  change (ConcreteCategory.hom ((-f.val).app U)) x = _
  simp

private lemma sheafMap_scalarNeg_apply {P Q : SheafOfModules.{m} R} (f : P ⟶ Q) (U : Cᵒᵖ)
    (x : P.val.obj U) :
    (ConcreteCategory.hom (((-1 : ℤˣ) • f).val.app U)) x =
      -(ConcreteCategory.hom (f.val.app U) x) := by
  have h : (-1 : ℤˣ) • f = -f := by simp
  have h' := congrArg (fun g => ConcreteCategory.hom (g.val.app U)) h
  calc
    (ConcreteCategory.hom (((-1 : ℤ) • f).val.app U)) x =
        (ConcreteCategory.hom ((-f).val.app U)) x := congrArg (fun g => g x) h'
    _ = -(ConcreteCategory.hom (f.val.app U) x) := sheafMap_neg_apply f U x

private lemma dependent_add_heq {ι : Type*} {B : ι → Type*} [∀ i, Add (B i)]
    {i j : ι} (h : i = j) {x₁ y₁ : B i} {x₂ y₂ : B j}
    (hx : HEq x₁ x₂) (hy : HEq y₁ y₂) : HEq (x₁ + y₁) (x₂ + y₂) := by
  subst j
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

/-- A transported bilinear map, on local sections, is the original one followed by the transport
of its target. -/
theorem castBilinearMap_app_apply {M P P' N : SheafOfModules.{m} R} (h : P = P')
    (f : BilinearMap M N P) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (castBilinearMap h f).app U x y = (eqToHom h).val.app U (f.app U x y) := by
  subst h
  rfl

/-! ### The shift -/

/-- **The shift `M[s]` of a right differential graded module**: the complex is the `s`-th shift of
the complex of `M`, so `M[s]^n = M^{n + s}` with differential `(-1)^s d`, and a homogeneous
section `a` of `A` of degree `i` acts on `M[s]^n` as it acts on `M^{n + s}`. -/
noncomputable def shiftBy (M : DifferentialGradedModule.{t, a, m} A) (s : ℤ) :
    DifferentialGradedModule.{t, a, m} A := by
  let C := (CochainComplex.shiftFunctor (SheafOfModules.{m} R) s).obj M.complex
  let μ (p q : ℤ) : BilinearMap (C.X p) (A.complex.X q) (C.X (p + q)) :=
    castBilinearMap
      (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
      (M.mul (p + s) q)
  exact {
    complex := C
    mul := μ
    mul_assoc := by
      intro p q r U x a b
      let i := (p + q) + s
      let j := (p + s) + q
      have hij : i = j := by dsimp [i, j]; omega
      have hx : HEq ((μ p q).app U x a) ((M.mul (p + s) q).app U x a) :=
        castBilinearMap_eval_heq
          (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
          (M.mul (p + s) q) U x a
      have h₁ := castBilinearMap_eval_heq
        (congrArg M.complex.X (show ((p + q) + s) + r = ((p + q) + r) + s by omega))
        (M.mul ((p + q) + s) r) U ((μ p q).app U x a) b
      have h₂ := castBilinearMap_eval_heq
        (congrArg M.complex.X (show (p + s) + (q + r) = (p + (q + r)) + s by omega))
        (M.mul (p + s) (q + r)) U x ((A.mul q r).app U a b)
      have hm := heq_dependent_apply
        (fun d : ℤ => fun y : (M.complex.X d).val.obj U => ((M.mul d r).app U y) b)
        hij hx
      exact h₁.trans (hm.trans ((M.mul_assoc (p + s) q r U x a b).trans h₂.symm))
    mul_one := by
      intro p U x
      exact (castBilinearMap_eval_heq
        (congrArg M.complex.X (show (p + s) + 0 = (p + 0) + s by omega))
        (M.mul (p + s) 0) U x (A.one.eval U)).trans (M.mul_one (p + s) U x)
    leibniz := by
      intro p q U x a
      have hmul := castBilinearMap_eval_heq
        (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
        (M.mul (p + s) q) U x a
      have hAction2 : HEq
          (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))
          (((M.mul (p + s) (q + 1)).app U) x
            ((A.complex.d q (q + 1)).val.app U a)) :=
        castBilinearMap_eval_heq
          (congrArg M.complex.X (show (p + s) + (q + 1) = (p + (q + 1)) + s by omega))
          (M.mul (p + s) (q + 1)) U x ((A.complex.d q (q + 1)).val.app U a)
      let tgt₁ := SheafOfModules.gradedCast (fun d => (C.X d).val.obj U)
        (add_right_comm p 1 q) (((μ (p + 1) q).app U)
          ((C.d p (p + 1)).val.app U x) a)
      have hC : HEq
          (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a) tgt₁ := by
        dsimp [tgt₁]
        exact (gradedCast_heq (T := fun d => (C.X d).val.obj U)
          (add_right_comm p 1 q)
          (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a)).symm
      let src₂ := (p.negOnePow : ℤ) • SheafOfModules.gradedCast
        (fun d => (M.complex.X d).val.obj U) (add_assoc (p + s) q 1).symm
        (((M.mul (p + s) (q + 1)).app U x)
          ((A.complex.d q (q + 1)).val.app U a))
      let tgt₂ := (p.negOnePow : ℤ) • SheafOfModules.gradedCast
        (fun d => (C.X d).val.obj U) (add_assoc p q 1).symm
        (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))
      have hSecond : HEq src₂ tgt₂ := by
        have hRaw : HEq
            (SheafOfModules.gradedCast
              (fun d => (M.complex.X d).val.obj U) (add_assoc (p + s) q 1).symm
              (((M.mul (p + s) (q + 1)).app U x)
                ((A.complex.d q (q + 1)).val.app U a)))
            (SheafOfModules.gradedCast
              (fun d => (C.X d).val.obj U) (add_assoc p q 1).symm
              (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))) :=
          (gradedCast_heq (T := fun d => (M.complex.X d).val.obj U)
              (add_assoc (p + s) q 1).symm
              (((M.mul (p + s) (q + 1)).app U x)
                ((A.complex.d q (q + 1)).val.app U a))).trans
            (hAction2.symm.trans (gradedCast_heq (T := fun d => (C.X d).val.obj U)
              (add_assoc p q 1).symm
              (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))).symm)
        dsimp [C] at hRaw ⊢
        exact heq_dependent_apply
            (fun d : ℤ => fun y : (M.complex.X d).val.obj U =>
              (p.negOnePow : ℤ) • y)
          (show (p + s + q) + 1 = (p + q + 1) + s by omega) hRaw
      have hSum : ∀ src₁ : (M.complex.X (p + s + q + 1)).val.obj U,
          HEq src₁ tgt₁ → HEq (src₁ + src₂) (tgt₁ + tgt₂) := fun src₁ hFirst => by
        dsimp [C] at hFirst hSecond
        have hR := dependent_add_heq (B := fun d => (M.complex.X d).val.obj U)
          (show (p + s + q) + 1 = (p + q + 1) + s by omega) hFirst hSecond
        dsimp [src₂, tgt₁, tgt₂] at hR
        exact hR
      rcases Int.even_or_odd s with hEven | hOdd
      · have hsign : (p + s).negOnePow = p.negOnePow := by
          rw [Int.negOnePow_add, Int.negOnePow_even s hEven]
          simp
        have h := M.leibniz (p + s) q U x a
        rw [hsign] at h
        have hL : HEq
            (((C.d (p + q) (p + q + 1)).val.app U) ((μ p q).app U x a))
            (((M.complex.d (p + s + q) (p + s + q + 1)).val.app U)
              ((M.mul (p + s) q).app U x a)) := by
          dsimp [C, μ]
          simp only [Int.negOnePow_even s hEven, one_smul]
          exact dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (M.complex.d d e).val.app U y)
            (show p + q + s = p + s + q by omega)
            (show p + q + 1 + s = p + s + q + 1 by omega) hmul
        have hShiftD : HEq
            (((C.d p (p + 1)).val.app U) x)
            (((M.complex.d (p + s) (p + s + 1)).val.app U) x) := by
          have hEnd : p + 1 + s = p + s + 1 := by omega
          dsimp [C]
          simp only [Int.negOnePow_even s hEven, one_smul]
          exact dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (M.complex.d d e).val.app U y) rfl hEnd HEq.rfl
        have hAction1 : HEq
            (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a)
            (((M.mul (p + s + 1) q).app U)
              ((M.complex.d (p + s) (p + s + 1)).val.app U x) a) := by
          dsimp [μ]
          exact (castBilinearMap_eval_heq
            (congrArg M.complex.X (show (p + 1 + s) + q = (p + 1 + q) + s by omega))
            (M.mul (p + 1 + s) q) U ((C.d p (p + 1)).val.app U x) a).trans
            (heq_dependent_apply
              (fun d : ℤ => fun y : (M.complex.X d).val.obj U =>
                (M.mul d q).app U y a)
              (show p + 1 + s = p + s + 1 by omega) hShiftD)
        have hFirst := (gradedCast_heq (T := fun d => (M.complex.X d).val.obj U)
          (add_right_comm (p + s) 1 q)
          (((M.mul (p + s + 1) q).app U)
            ((M.complex.d (p + s) (p + s + 1)).val.app U x) a)).trans
          (hAction1.symm.trans hC)
        exact eq_of_heq (hL.trans ((heq_of_eq h).trans (hSum _ hFirst)))
      · have hsign : (p + s).negOnePow = -p.negOnePow := by
          rw [Int.negOnePow_add, Int.negOnePow_odd s hOdd]
          simp
        have h := M.leibniz (p + s) q U x a
        have h :
            -(((M.complex.d (p + s + q) (p + s + q + 1)).val.app U)
              (((M.mul (p + s) q).app U) x a)) =
            -SheafOfModules.gradedCast (fun d => (M.complex.X d).val.obj U)
                (add_right_comm (p + s) 1 q)
                (((M.mul (p + s + 1) q).app U)
                  ((M.complex.d (p + s) (p + s + 1)).val.app U x) a) +
              src₂ := by
          have h' := congrArg Neg.neg h
          rw [hsign] at h'
          simp only [neg_add, Units.val_neg, neg_smul, neg_neg] at h'
          exact h'
        have hL : HEq
            (((C.d (p + q) (p + q + 1)).val.app U) ((μ p q).app U x a))
            (-(((M.complex.d (p + s + q) (p + s + q + 1)).val.app U)
              ((M.mul (p + s) q).app U x a))) := by
          dsimp [C, μ]
          rw [Int.negOnePow_odd s hOdd]
          have hD := dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (ConcreteCategory.hom (((-1 : ℤˣ) • M.complex.d d e).val.app U)) y)
            (show p + q + s = p + s + q by omega)
            (show p + q + 1 + s = p + s + q + 1 by omega) hmul
          exact hD.trans (heq_of_eq (sheafMap_scalarNeg_apply
            (M.complex.d (p + s + q) (p + s + q + 1)) U
            (((M.mul (p + s) q).app U) x a)))
        have hShiftD : HEq
            (((C.d p (p + 1)).val.app U) x)
            (-((M.complex.d (p + s) (p + s + 1)).val.app U x)) := by
          have hEnd : p + 1 + s = p + s + 1 := by omega
          dsimp [C]
          rw [Int.negOnePow_odd s hOdd]
          let x' : (M.complex.X (p + s)).val.obj U := x
          have hD := dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (ConcreteCategory.hom (((-1 : ℤˣ) • M.complex.d d e).val.app U)) y)
            (i := p + s) (i' := p + s)
            (j := p + 1 + s) (j' := p + s + 1) (x := x') (y := x')
            rfl hEnd HEq.rfl
          exact hD.trans (heq_of_eq (sheafMap_scalarNeg_apply
            (M.complex.d (p + s) (p + s + 1)) U x))
        have hAction1 : HEq
            (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a)
            (-((((M.mul (p + s + 1) q).app U)
              ((M.complex.d (p + s) (p + s + 1)).val.app U x)) a)) := by
          dsimp [μ]
          have hCast := castBilinearMap_eval_heq
            (congrArg M.complex.X (show (p + 1 + s) + q = (p + 1 + q) + s by omega))
            (M.mul (p + 1 + s) q) U ((C.d p (p + 1)).val.app U x) a
          have hMap := heq_dependent_apply
            (fun d : ℤ => fun y : (M.complex.X d).val.obj U =>
              ((M.mul d q).app U y) a)
            (show p + 1 + s = p + s + 1 by omega) hShiftD
          have hNeg :
              ((((M.mul (p + s + 1) q).app U)
                (-((M.complex.d (p + s) (p + s + 1)).val.app U x))) a) =
              -((((M.mul (p + s + 1) q).app U)
                ((M.complex.d (p + s) (p + s + 1)).val.app U x)) a) := by
            simp
          exact hCast.trans (hMap.trans (heq_of_eq hNeg))
        have hFirst := (gradedCast_neg_heq (B := fun d => (M.complex.X d).val.obj U)
          (add_right_comm (p + s) 1 q)
          (((M.mul (p + s + 1) q).app U)
            ((M.complex.d (p + s) (p + s + 1)).val.app U x) a)).trans
          (hAction1.symm.trans hC)
        exact eq_of_heq (hL.trans ((heq_of_eq h).trans (hSum _ hFirst)))
  }

/-- The complex of `M[s]` is the `s`-th shift of the complex of `M`. -/
theorem shiftBy_complex (M : DifferentialGradedModule.{t, a, m} A) (s : ℤ) :
    (shiftBy M s).complex =
      (CochainComplex.shiftFunctor (SheafOfModules.{m} R) s).obj M.complex := rfl

/-- The differential of a shift is `(-1)^s` times the differential, in the shifted degrees. -/
theorem shiftBy_d (P : DifferentialGradedModule.{t, a, m} A) (s p q : ℤ) :
    (shiftBy P s).complex.d p q = s.negOnePow • P.complex.d (p + s) (q + s) := rfl

/-- The degree-`n` term of `P[1]` is `P^{n+1}`. -/
theorem shiftBy_one_X (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    P.complex.X (n + 1) = (shiftBy P 1).complex.X n := rfl

/-- The action of `A` on `M[s]^p` is that on `M^{p + s}`, transported along
`(p + s) + q = (p + q) + s`. -/
theorem shiftBy_mul (M : DifferentialGradedModule.{t, a, m} A) (s p q : ℤ) :
    (shiftBy M s).mul p q =
      castBilinearMap (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
        (M.mul (p + s) q) := rfl

/-- The action of `A` on `M[s]^p`, on local sections, is that on `M^{p + s}`. -/
theorem shiftBy_mul_app_heq (M : DifferentialGradedModule.{t, a, m} A) (s p q : ℤ) (U : Cᵒᵖ)
    (x : ((shiftBy M s).complex.X p).val.obj U) (y : (A.complex.X q).val.obj U) :
    HEq (((shiftBy M s).mul p q).app U x y) ((M.mul (p + s) q).app U x y) :=
  castBilinearMap_eval_heq
    (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega)) (M.mul (p + s) q) U x y

/-- The action of `A` on `M[s]^p` is the action on `M^{p + s}`. -/
theorem shiftBy_mul_heq (M : DifferentialGradedModule.{t, a, m} A) (s p q : ℤ) (U : Cᵒᵖ) :
    HEq (((shiftBy M s).mul p q).app U) ((M.mul (p + s) q).app U) :=
  castBilinearMap_app_heq
    (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega)) (M.mul (p + s) q) U

/-- **Two right differential graded modules with the same complex and heterogeneously equal
actions are equal.** -/
theorem ext_of_complex_eq {M N : DifferentialGradedModule.{t, a, m} A}
    (hc : M.complex = N.complex)
    (hm : ∀ p q U, HEq ((M.mul p q).app U) ((N.mul p q).app U)) : M = N := by
  rcases M with ⟨MC, μ, ma, mo, ml⟩
  rcases N with ⟨NC, ν, na, no, nl⟩
  dsimp only at hc hm
  subst NC
  have hμ : μ = ν := by
    funext p q
    have ha : (μ p q).app = (ν p q).app := funext (fun U => eq_of_heq (hm p q U))
    have hext : ∀ (f g : BilinearMap (MC.X p) (A.complex.X q)
        (MC.X (p + q))), f.app = g.app → f = g := by
      rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
      cases h
      rfl
    exact hext _ _ ha
  subst ν
  rfl

/-- **`M[0] = M`.** -/
theorem shiftBy_zero (M : DifferentialGradedModule.{t, a, m} A) : shiftBy M 0 = M := by
  apply ext_of_complex_eq
  · apply HomologicalComplex.ext_of_iso
      ((CochainComplex.shiftFunctorZero' (SheafOfModules.{m} R) 0 rfl).app M.complex)
    · intro p
      simp
  · intro p q U
    exact (shiftBy_mul_heq M 0 p q U).trans
      (congr_arg_heq (fun p => (M.mul p q).app U) (add_zero p))

/-- **`M[1]` is the chosen degree-one shift `shift M`.** -/
theorem shiftBy_one (M : DifferentialGradedModule.{t, a, m} A) : shiftBy M 1 = shift M := by
  apply ext_of_complex_eq
  · exact (shiftBy_complex M 1).trans (shiftPackage M).shifted_complex.symm
  · intro p q U
    exact (shiftBy_mul_heq M 1 p q U).trans ((shiftPackage M).shifted_action p q U).symm

/-- **`M[n + m] = M[m][n]`.** -/
theorem shiftBy_add (M : DifferentialGradedModule.{t, a, m} A) (n k : ℤ) :
    shiftBy M (n + k) = shiftBy (shiftBy M k) n := by
  apply ext_of_complex_eq
  · apply HomologicalComplex.ext_of_iso
      ((CochainComplex.shiftFunctorAdd' (SheafOfModules.{m} R) k n (n + k)
        (add_comm k n)).app M.complex)
    · intro p
      dsimp
      congr 1
      omega
  · intro p q U
    have h := (shiftBy_mul_heq (shiftBy M k) n p q U).trans
      (shiftBy_mul_heq M k (p + n) q U)
    exact (shiftBy_mul_heq M (n + k) p q U).trans
      ((h.trans (congr_arg_heq (fun p => (M.mul p q).app U) (add_assoc p n k))).symm)

/-- `M[k][-k] = M`. -/
theorem shiftBy_shiftBy_neg (M : DifferentialGradedModule.{t, a, m} A) (k : ℤ) :
    shiftBy (shiftBy M k) (-k) = M :=
  (shiftBy_add M (-k) k).symm.trans
    ((congrArg (shiftBy M) (neg_add_cancel k)).trans (shiftBy_zero M))

/-- `M[-k][k] = M`. -/
theorem shiftBy_neg_shiftBy (M : DifferentialGradedModule.{t, a, m} A) (k : ℤ) :
    shiftBy (shiftBy M (-k)) k = M :=
  (shiftBy_add M k (-k)).symm.trans
    ((congrArg (shiftBy M) (add_neg_cancel k)).trans (shiftBy_zero M))

/-! ### The shift of a morphism -/

/-- **The shift of a morphism of right differential graded modules**, with the same component
maps. -/
noncomputable def shiftByMap (s : ℤ) {M N : DifferentialGradedModule.{t, a, m} A} (φ : M ⟶ N) :
    shiftBy M s ⟶ shiftBy N s where
  toHomologicalComplex :=
    (CochainComplex.shiftFunctor (SheafOfModules.{m} R) s).map φ.toHomologicalComplex
  map_mul n i U x y := by
    refine eq_of_heq ?_
    have hL := heq_dependent_apply
      (fun d : ℤ => fun w : (M.complex.X d).val.obj U =>
        (φ.toHomologicalComplex.f d).val.app U w)
      (show (n + i) + s = (n + s) + i by omega) (shiftBy_mul_app_heq M s n i U x y)
    have hR := shiftBy_mul_app_heq N s n i U ((φ.toHomologicalComplex.f (n + s)).val.app U x) y
    exact hL.trans ((heq_of_eq (φ.map_mul (n + s) i U x y)).trans hR.symm)

/-- The components of the shift of a morphism are its components in the shifted degrees. -/
@[simp]
theorem shiftByMap_f (s : ℤ) {M N : DifferentialGradedModule.{t, a, m} A} (φ : M ⟶ N) (n : ℤ) :
    (shiftByMap s φ).toHomologicalComplex.f n = φ.toHomologicalComplex.f (n + s) := rfl

/-- The shift of the identity is the identity. -/
@[simp]
theorem shiftByMap_id (s : ℤ) (M : DifferentialGradedModule.{t, a, m} A) :
    shiftByMap s (𝟙 M) = 𝟙 (shiftBy M s) :=
  Hom.ext fun _ => rfl

/-- The shift of a composite is the composite of the shifts. -/
@[simp]
theorem shiftByMap_comp (s : ℤ) {M N P : DifferentialGradedModule.{t, a, m} A} (φ : M ⟶ N)
    (ψ : N ⟶ P) : shiftByMap s (φ ≫ ψ) = shiftByMap s φ ≫ shiftByMap s ψ :=
  Hom.ext fun _ => rfl

/-- A morphism of complexes, conjugated by the transports along an equality of degrees, is its
component in the other degree. -/
private theorem eqToHom_comp_f_comp_eqToHom {K L : CochainComplex (SheafOfModules.{m} R) ℤ}
    (φ : K ⟶ L) {p q : ℤ} (h : p = q) (h₁ : K.X p = K.X q) (h₂ : L.X q = L.X p) :
    (eqToHom h₁ ≫ φ.f q) ≫ eqToHom h₂ = φ.f p := by
  subst h
  simp

/-- The same, associated the other way. -/
private theorem eqToHom_comp_f_comp_eqToHom' {K L : CochainComplex (SheafOfModules.{m} R) ℤ}
    (φ : K ⟶ L) {p q : ℤ} (h : p = q) (h₁ : K.X p = K.X q) (h₂ : L.X q = L.X p) :
    eqToHom h₁ ≫ φ.f q ≫ eqToHom h₂ = φ.f p := by
  subst h
  simp

/-! ### Morphisms out of a shift -/

/-- **Morphisms `T[k] ⟶ Q` are morphisms `T ⟶ Q[-k]`.** -/
noncomputable def shiftByHomEquiv (k : ℤ) (T Q : DifferentialGradedModule.{t, a, m} A) :
    (shiftBy T k ⟶ Q) ≃ (T ⟶ shiftBy Q (-k)) where
  toFun φ := eqToHom (shiftBy_shiftBy_neg T k).symm ≫ shiftByMap (-k) φ
  invFun ψ := shiftByMap k ψ ≫ eqToHom (shiftBy_neg_shiftBy Q k)
  left_inv φ := by
    refine Hom.ext fun n => ?_
    have key : ∀ {P Q : DifferentialGradedModule.{t, a, m} A} (h : P = Q) (j : ℤ),
        (eqToHom h).toHomologicalComplex.f j =
          eqToHom (congrArg (fun T : DifferentialGradedModule.{t, a, m} A => T.complex.X j) h) := by
      intro P Q h j
      subst h
      rfl
    simp only [comp_f, shiftByMap_f, key]
    exact eqToHom_comp_f_comp_eqToHom φ.toHomologicalComplex (show n = n + k + -k by omega) _ _
  right_inv ψ := by
    refine Hom.ext fun n => ?_
    have key : ∀ {P Q : DifferentialGradedModule.{t, a, m} A} (h : P = Q) (j : ℤ),
        (eqToHom h).toHomologicalComplex.f j =
          eqToHom (congrArg (fun T : DifferentialGradedModule.{t, a, m} A => T.complex.X j) h) := by
      intro P Q h j
      subst h
      rfl
    simp only [comp_f, shiftByMap_f, key]
    exact eqToHom_comp_f_comp_eqToHom' ψ.toHomologicalComplex (show n = n + -k + k by omega) _ _

/-- The bijection `shiftByHomEquiv` sends `φ` to the transport of its shift by `-k`. -/
theorem shiftByHomEquiv_apply (k : ℤ) {T Q : DifferentialGradedModule.{t, a, m} A}
    (φ : shiftBy T k ⟶ Q) :
    shiftByHomEquiv k T Q φ = eqToHom (shiftBy_shiftBy_neg T k).symm ≫ shiftByMap (-k) φ := rfl

/-- **The bijection `shiftByHomEquiv` is natural in the target.** -/
theorem shiftByHomEquiv_comp (k : ℤ) {T Q Q' : DifferentialGradedModule.{t, a, m} A}
    (φ : shiftBy T k ⟶ Q) (g : Q ⟶ Q') :
    shiftByHomEquiv k T Q' (φ ≫ g) = shiftByHomEquiv k T Q φ ≫ shiftByMap (-k) g := by
  rw [shiftByHomEquiv_apply, shiftByHomEquiv_apply, shiftByMap_comp, Category.assoc]

end SheafOfModules.DifferentialGradedModule

end
