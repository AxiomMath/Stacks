module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.ModuleFunctorAtBase

/-!
# A linearly adequate functor that is not a projective object

Let `d : ℤ ⟶ ℤ` be multiplication by two on the rank-one finite free `ℤ`-module, a finite free
presentation of `ℤ/2`, and let `L = ker(d̲)` be the kernel of the induced morphism of
module-valued functors, so that `L(C) = {c ∈ C | 2c = 0}`.  **This file proves that `L` is not
a projective object** of `AdequateFunctor.ModuleValuedFunctor ℤ`, the module-valued functors
on *all* commutative `ℤ`-algebras.

## The counterexample

The epimorphism that does not split is the one out of the free module-valued functor on the
two-torsion set, `AdequateFunctor.twoTorsionFree : C ↦ C^{(C[2])}`, whose index set is
corepresented by `R = ℤ[x]/(2x)`: a two-torsion element of `C` is an algebra map `R → C`.

A section `s` of that epimorphism would send the universal two-torsion element `ξ ∈ L(R)` to a
section `y ∈ C^{(C[2])}` at `C = R`.  Since `ξ` scales along `x ↦ t x`, that is
`L(μ)(ξ) = t · L(ι)(ξ)` in `L(R[t])` for the two algebra maps `μ, ι : R → R[t]`, the section
`y` must satisfy the same identity — it is *weight one*.  But the weight-one part of a free
functor is degenerate: evaluating at `t = 0` and at `t = 1` shows that the scaled index
`μ ∘ u` can equal a constant index `ι ∘ u'` only when both are the index killing the variable
(`AdequateFunctor.twoTorsion_collide`), so every other coefficient of `y` vanishes and `y`
evaluates to `0` (`AdequateFunctor.evalTwoTorsionFree_eq_zero_of_weightOne`).  The universal
element is not zero, so no section exists.

## Main results

* `AdequateFunctor.not_projective_twoTorsionKernel`: `ker(d̲)` is not a projective object.
* `AdequateFunctor.not_forall_projective_of_isLinearlyAdequate`: linear adequacy does not
  imply projectivity in the ambient category.

## Implementation notes

Everything is stated at `AdequateFunctor.ModuleValuedFunctor.{0, 0} ℤ`, i.e.
`PresheafOfModules (AdequateFunctor.algebraRingDiagram.{0} ℤ)` over all of `CommAlgCat.{0} ℤ`,
the domain of `AdequateFunctor.adequate`, rather than over `AdequateFunctor.AlgebrasInSite`.

The `ℤ`-module structure that `AdequateFunctor.moduleExtension` puts on an algebra is the
algebra's own, and `AddCommGroup.toIntModule` is selected ahead of it, so a pure tensor would be
elaborated at a `ℤ`-action only propositionally equal to the one in the type. The instance is
therefore removed in the section in which pure tensors are written.
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Polynomial

namespace AdequateFunctor

/-! ### The universal two-torsion algebra -/

/-- `ℤ[x]/(2x)`, the algebra corepresenting two-torsion. -/
abbrev twoTorsionAlgebra : Type := Polynomial ℤ ⧸ Ideal.span {(2 : Polynomial ℤ) * X}

/-- The universal two-torsion element. -/
noncomputable def twoTorsionVar : twoTorsionAlgebra := Ideal.Quotient.mk _ X

/-- The universal two-torsion element is two-torsion: `2 x = 0` in `ℤ[x]/(2x)`. -/
lemma two_mul_twoTorsionVar : (2 : twoTorsionAlgebra) * twoTorsionVar = 0 := by
  have h : (2 : twoTorsionAlgebra) * twoTorsionVar =
      Ideal.Quotient.mk _ ((2 : Polynomial ℤ) * X) := rfl
  rw [h, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- The universal two-torsion element `x` is nonzero in `ℤ[x]/(2x)`. -/
lemma twoTorsionVar_ne_zero : twoTorsionVar ≠ 0 := by
  intro h
  rw [show twoTorsionVar = Ideal.Quotient.mk _ X from rfl, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) hc
  simp only [coeff_X_one, mul_assoc] at h1
  rw [show ((2 : Polynomial ℤ) * (X * c)) = C 2 * (X * c) by norm_num,
    coeff_C_mul, coeff_X_mul] at h1
  omega

/-- An algebra map out of `ℤ[x]/(2x)` is determined by the image of the variable. -/
lemma twoTorsion_algHom_ext {D : Type} [CommRing D] [Algebra ℤ D]
    (f g : twoTorsionAlgebra →ₐ[ℤ] D) (h : f twoTorsionVar = g twoTorsionVar) : f = g := by
  have key : f.comp (Ideal.Quotient.mkₐ ℤ (Ideal.span {(2 : Polynomial ℤ) * X})) =
      g.comp (Ideal.Quotient.mkₐ ℤ (Ideal.span {(2 : Polynomial ℤ) * X})) :=
    Polynomial.algHom_ext h
  refine AlgHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact AlgHom.congr_fun key p

/-- The algebra map classifying a two-torsion element. -/
noncomputable def twoTorsionClassify {D : Type} [CommRing D] [Algebra ℤ D] (c : D)
    (hc : (2 : D) * c = 0) : twoTorsionAlgebra →ₐ[ℤ] D :=
  Ideal.Quotient.liftₐ _ (Polynomial.aeval c) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
    have h2 : (Polynomial.aeval c) (2 : Polynomial ℤ) = 2 := map_ofNat _ 2
    simp only [map_mul, aeval_X, h2]
    rw [hc, zero_mul])

/-- The classifying map of a two-torsion element `c` sends the variable to `c`. -/
@[simp] lemma twoTorsionClassify_var {D : Type} [CommRing D] [Algebra ℤ D] (c : D)
    (hc : (2 : D) * c = 0) : twoTorsionClassify c hc twoTorsionVar = c := by
  have h : twoTorsionClassify c hc twoTorsionVar = (Polynomial.aeval c) X := rfl
  rw [h, aeval_X]

/-- Every two-torsion section is two-torsion. -/
lemma two_mul_apply_twoTorsionVar {D : Type} [CommRing D] [Algebra ℤ D]
    (u : twoTorsionAlgebra →ₐ[ℤ] D) : (2 : D) * u twoTorsionVar = 0 := by
  have h : (2 : D) * u twoTorsionVar = u ((2 : twoTorsionAlgebra) * twoTorsionVar) := by
    rw [map_mul, map_ofNat]
  rw [h, two_mul_twoTorsionVar, map_zero]

/-- The constant-term map of `ℤ[x]/(2x)`. -/
noncomputable def twoTorsionConstantTerm : twoTorsionAlgebra →ₐ[ℤ] ℤ :=
  twoTorsionClassify (0 : ℤ) (by simp)

/-- The endomorphism of `ℤ[x]/(2x)` killing the variable. -/
noncomputable def twoTorsionZero : twoTorsionAlgebra →ₐ[ℤ] twoTorsionAlgebra :=
  twoTorsionClassify (0 : twoTorsionAlgebra) (by simp)

/-- The constant term of a two-torsion element of `ℤ[x]/(2x)` is zero. -/
lemma twoTorsionConstantTerm_eq_zero {z : twoTorsionAlgebra}
    (hz : (2 : twoTorsionAlgebra) * z = 0) : twoTorsionConstantTerm z = 0 := by
  have h : (2 : ℤ) * twoTorsionConstantTerm z = 0 := by
    rw [show (2 : ℤ) * twoTorsionConstantTerm z = twoTorsionConstantTerm
      ((2 : twoTorsionAlgebra) * z) by rw [map_mul, map_ofNat], hz, map_zero]
  omega

/-- The endomorphism killing the variable is the constant term followed by the structure map. -/
lemma twoTorsionZero_eq (z : twoTorsionAlgebra) :
    twoTorsionZero z = algebraMap ℤ twoTorsionAlgebra (twoTorsionConstantTerm z) := by
  have h : twoTorsionZero = (Algebra.ofId ℤ twoTorsionAlgebra).comp twoTorsionConstantTerm := by
    refine twoTorsion_algHom_ext _ _ ?_
    simp [twoTorsionZero, twoTorsionConstantTerm, Algebra.ofId]
  rw [h]
  rfl

/-- Precomposing the endomorphism killing the variable with any endomorphism of `ℤ[x]/(2x)`
does not change it. -/
lemma twoTorsionZero_comp (u : twoTorsionAlgebra →ₐ[ℤ] twoTorsionAlgebra) :
    twoTorsionZero.comp u = twoTorsionZero := by
  refine twoTorsion_algHom_ext _ _ ?_
  have h : twoTorsionZero (u twoTorsionVar) = 0 := by
    rw [twoTorsionZero_eq, twoTorsionConstantTerm_eq_zero (two_mul_apply_twoTorsionVar u),
      map_zero]
  have h2 : twoTorsionZero twoTorsionVar = 0 := twoTorsionClassify_var _ _
  change twoTorsionZero (u twoTorsionVar) = twoTorsionZero twoTorsionVar
  rw [h, h2]

/-! ### The weight-one scaling, and the collision lemma -/

/-- The constant inclusion `ℤ[x]/(2x) → (ℤ[x]/(2x))[t]`. -/
noncomputable def twoTorsionConst : twoTorsionAlgebra →ₐ[ℤ] Polynomial twoTorsionAlgebra :=
  IsScalarTower.toAlgHom ℤ twoTorsionAlgebra (Polynomial twoTorsionAlgebra)

/-- The weight-one scaling `ℤ[x]/(2x) → (ℤ[x]/(2x))[t]`, `x ↦ t * x`. -/
noncomputable def twoTorsionScale : twoTorsionAlgebra →ₐ[ℤ] Polynomial twoTorsionAlgebra :=
  twoTorsionClassify (X * C twoTorsionVar) (by
    rw [show (2 : Polynomial twoTorsionAlgebra) * (X * C twoTorsionVar)
        = X * C ((2 : twoTorsionAlgebra) * twoTorsionVar) by rw [map_mul, map_ofNat]; ring]
    rw [two_mul_twoTorsionVar, map_zero, mul_zero])

/-- Evaluation of `t` at `1`. -/
noncomputable def twoTorsionEvalOne : Polynomial twoTorsionAlgebra →ₐ[ℤ] twoTorsionAlgebra :=
  (Polynomial.aeval (1 : twoTorsionAlgebra)).restrictScalars ℤ

/-- Evaluation of `t` at `0`. -/
noncomputable def twoTorsionEvalZero : Polynomial twoTorsionAlgebra →ₐ[ℤ] twoTorsionAlgebra :=
  (Polynomial.aeval (0 : twoTorsionAlgebra)).restrictScalars ℤ

/-- The constant inclusion sends `x` to the constant polynomial `x`. -/
@[simp] lemma twoTorsionConst_var : twoTorsionConst twoTorsionVar = C twoTorsionVar := rfl

/-- The weight-one scaling sends `x` to `t * x`. -/
@[simp] lemma twoTorsionScale_var :
    twoTorsionScale twoTorsionVar = X * C twoTorsionVar := twoTorsionClassify_var _ _

/-- Evaluating the weight-one scaling at `t = 1` gives the identity. -/
lemma twoTorsionEvalOne_comp_scale :
    twoTorsionEvalOne.comp twoTorsionScale = AlgHom.id ℤ twoTorsionAlgebra := by
  refine twoTorsion_algHom_ext _ _ ?_
  change twoTorsionEvalOne (twoTorsionScale twoTorsionVar) = twoTorsionVar
  rw [twoTorsionScale_var]
  simp [twoTorsionEvalOne]

/-- Evaluating the constant inclusion at `t = 1` gives the identity. -/
lemma twoTorsionEvalOne_comp_const :
    twoTorsionEvalOne.comp twoTorsionConst = AlgHom.id ℤ twoTorsionAlgebra := by
  refine twoTorsion_algHom_ext _ _ ?_
  change twoTorsionEvalOne (twoTorsionConst twoTorsionVar) = twoTorsionVar
  rw [twoTorsionConst_var]
  simp [twoTorsionEvalOne]

/-- Evaluating the weight-one scaling at `t = 0` gives the endomorphism killing the variable. -/
lemma twoTorsionEvalZero_comp_scale :
    twoTorsionEvalZero.comp twoTorsionScale = twoTorsionZero := by
  refine twoTorsion_algHom_ext _ _ ?_
  change twoTorsionEvalZero (twoTorsionScale twoTorsionVar) = twoTorsionZero twoTorsionVar
  rw [twoTorsionScale_var, show twoTorsionZero twoTorsionVar = 0 from twoTorsionClassify_var _ _]
  simp [twoTorsionEvalZero]

/-- Evaluating the constant inclusion at `t = 0` gives the identity. -/
lemma twoTorsionEvalZero_comp_const :
    twoTorsionEvalZero.comp twoTorsionConst = AlgHom.id ℤ twoTorsionAlgebra := by
  refine twoTorsion_algHom_ext _ _ ?_
  change twoTorsionEvalZero (twoTorsionConst twoTorsionVar) = twoTorsionVar
  rw [twoTorsionConst_var]
  simp [twoTorsionEvalZero]

/-- Postcomposing both sides of an equation of composites of algebra maps with one map. -/
private lemma comp_comp_congr {A B C D : Type} [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] [Algebra ℤ A] [Algebra ℤ B] [Algebra ℤ C] [Algebra ℤ D]
    (e : C →ₐ[ℤ] D) {f g : B →ₐ[ℤ] C} {u u' : A →ₐ[ℤ] B} (h : f.comp u = g.comp u') :
    (e.comp f).comp u = (e.comp g).comp u' := by
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, h]

/-- **The collision lemma.**  The weight-one scaling of a two-torsion section agrees with the
constant inclusion of one only at the section killing the variable. -/
lemma twoTorsion_collide {u u' : twoTorsionAlgebra →ₐ[ℤ] twoTorsionAlgebra}
    (h : twoTorsionScale.comp u = twoTorsionConst.comp u') :
    u = twoTorsionZero ∧ u' = twoTorsionZero := by
  have hp := comp_comp_congr twoTorsionEvalZero h
  rw [twoTorsionEvalZero_comp_scale, twoTorsionEvalZero_comp_const, AlgHom.id_comp] at hp
  have h' : u' = twoTorsionZero := by rw [← hp, twoTorsionZero_comp]
  have hs := comp_comp_congr twoTorsionEvalOne h
  rw [twoTorsionEvalOne_comp_scale, twoTorsionEvalOne_comp_const, AlgHom.id_comp,
    AlgHom.id_comp] at hs
  rw [hs, h']
  exact ⟨rfl, rfl⟩

/-- Postcomposition with the weight-one scaling is injective on endomorphisms of `ℤ[x]/(2x)`. -/
lemma twoTorsionScale_comp_injective :
    Function.Injective fun u : twoTorsionAlgebra →ₐ[ℤ] twoTorsionAlgebra =>
      twoTorsionScale.comp u := by
  intro u u' h
  have hc := comp_comp_congr twoTorsionEvalOne h
  rwa [twoTorsionEvalOne_comp_scale, AlgHom.id_comp, AlgHom.id_comp] at hc

/-- The weight-one scaling is injective. -/
lemma twoTorsionScale_injective : Function.Injective twoTorsionScale :=
  Function.LeftInverse.injective (g := twoTorsionEvalOne)
    (AlgHom.congr_fun twoTorsionEvalOne_comp_scale)

/-! ### The free module-valued functor on the two-torsion set -/

/-- The two-torsion sections over an algebra, as algebra maps out of the universal one. -/
abbrev twoTorsionIndex (B : CommAlgCat.{0} ℤ) : Type := twoTorsionAlgebra →ₐ[ℤ] (B : Type)

/-- The transition function of the free module on the two-torsion set. -/
noncomputable def twoTorsionFreeFun {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D)
    (y : twoTorsionIndex B →₀ (B : Type)) : twoTorsionIndex D →₀ (D : Type) :=
  Finsupp.mapDomain (fun u : twoTorsionIndex B => f.hom.comp u)
    (Finsupp.mapRange f.hom (map_zero f.hom) y)

/-- The transition function sends `a` at index `u` to `f a` at index `f ∘ u`. -/
@[simp] lemma twoTorsionFreeFun_single {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D)
    (u : twoTorsionIndex B) (a : B) :
    twoTorsionFreeFun f (Finsupp.single u a) = Finsupp.single (f.hom.comp u) (f.hom a) := by
  rw [twoTorsionFreeFun, Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- The transition function is additive. -/
lemma twoTorsionFreeFun_add {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D)
    (y z : twoTorsionIndex B →₀ (B : Type)) :
    twoTorsionFreeFun f (y + z) = twoTorsionFreeFun f y + twoTorsionFreeFun f z := by
  rw [twoTorsionFreeFun, twoTorsionFreeFun, twoTorsionFreeFun,
    Finsupp.mapRange_add (fun a b => map_add f.hom a b), Finsupp.mapDomain_add]

/-- The transition function sends zero to zero. -/
lemma twoTorsionFreeFun_zero {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D) :
    twoTorsionFreeFun f (0 : twoTorsionIndex B →₀ (B : Type)) = 0 := by
  rw [twoTorsionFreeFun, Finsupp.mapRange_zero, Finsupp.mapDomain_zero]

/-- The transition function is semilinear along `f`. -/
lemma twoTorsionFreeFun_smul {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D) (b : B)
    (y : twoTorsionIndex B →₀ (B : Type)) :
    twoTorsionFreeFun f (b • y) = f.hom b • twoTorsionFreeFun f y := by
  induction y using Finsupp.induction_linear with
  | zero =>
    rw [smul_zero, twoTorsionFreeFun_zero]
    exact (smul_zero _).symm
  | add y z hy hz =>
    rw [smul_add, twoTorsionFreeFun_add, hy, hz, twoTorsionFreeFun_add, smul_add]
  | single u a =>
    rw [Finsupp.smul_single, twoTorsionFreeFun_single, twoTorsionFreeFun_single,
      Finsupp.smul_single, smul_eq_mul, smul_eq_mul, map_mul]

/-- The transition function of a composite is the composite of the transition functions. -/
lemma twoTorsionFreeFun_comp {B D E : CommAlgCat.{0} ℤ} (f : B ⟶ D) (g : D ⟶ E)
    (y : twoTorsionIndex B →₀ (B : Type)) :
    twoTorsionFreeFun (f ≫ g) y = twoTorsionFreeFun g (twoTorsionFreeFun f y) := by
  induction y using Finsupp.induction_linear with
  | zero => rw [twoTorsionFreeFun_zero, twoTorsionFreeFun_zero, twoTorsionFreeFun_zero]
  | add y z hy hz =>
    rw [twoTorsionFreeFun_add, twoTorsionFreeFun_add, twoTorsionFreeFun_add, hy, hz]
  | single u a =>
    rw [twoTorsionFreeFun_single, twoTorsionFreeFun_single, twoTorsionFreeFun_single]
    rfl

/-- The transition map of the free module on the two-torsion set. -/
noncomputable def twoTorsionFreeMap {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D) :
    ModuleCat.of B (twoTorsionIndex B →₀ (B : Type)) ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj
        (ModuleCat.of D (twoTorsionIndex D →₀ (D : Type))) :=
  ModuleCat.ofHom
    (X := ModuleCat.of B (twoTorsionIndex B →₀ (B : Type)))
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj
      (ModuleCat.of D (twoTorsionIndex D →₀ (D : Type))))
    { toFun := twoTorsionFreeFun f
      map_add' := twoTorsionFreeFun_add f
      map_smul' := fun b y => twoTorsionFreeFun_smul f b y }

/-- The transition map acts by the transition function. -/
lemma twoTorsionFreeMap_apply {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D)
    (y : twoTorsionIndex B →₀ (B : Type)) :
    twoTorsionFreeMap f y = twoTorsionFreeFun f y := rfl

/-- **The free module-valued functor on the two-torsion set**: `C ↦ C^{(C[2])}`. It does not
commute with finite products of algebras, so it is not adequate. -/
noncomputable def twoTorsionFree : ModuleValuedFunctor.{0, 0} ℤ where
  obj X := ModuleCat.of X.unop.unop
    (twoTorsionIndex X.unop.unop →₀ (X.unop.unop : Type))
  map {X Y} f := twoTorsionFreeMap f.unop.unop
  map_id X := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    refine Eq.trans ?_ (ModuleCat.restrictScalarsId'App_inv_apply _ (by simp) _ y).symm
    rw [twoTorsionFreeMap_apply, twoTorsionFreeFun]
    change Finsupp.mapDomain id (Finsupp.mapRange id rfl y) = y
    rw [Finsupp.mapRange_id, Finsupp.mapDomain_id]
  map_comp {X Y Z} f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    induction y using Finsupp.induction_linear with
    | zero => rw [map_zero, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz]
    | single u a =>
      change twoTorsionFreeMap (f ≫ g).unop.unop (Finsupp.single u a)
        = twoTorsionFreeMap g.unop.unop (twoTorsionFreeMap f.unop.unop (Finsupp.single u a))
      exact twoTorsionFreeFun_comp f.unop.unop g.unop.unop (Finsupp.single u a)

/-! ### Evaluating a free section -/

/-- The evaluation of a free section: the two-torsion element it names. -/
noncomputable def evalTwoTorsionFree {B : CommAlgCat.{0} ℤ}
    (y : twoTorsionIndex B →₀ (B : Type)) : (B : Type) :=
  y.sum fun u a => a * u twoTorsionVar

/-- The evaluation of `a` at index `u` is `a * u x`. -/
@[simp] lemma evalTwoTorsionFree_single {B : CommAlgCat.{0} ℤ} (u : twoTorsionIndex B) (a : B) :
    evalTwoTorsionFree (Finsupp.single u a) = a * u twoTorsionVar := by
  rw [evalTwoTorsionFree, Finsupp.sum_single_index (by rw [zero_mul])]

/-- The evaluation of the zero section is zero. -/
lemma evalTwoTorsionFree_zero {B : CommAlgCat.{0} ℤ} :
    evalTwoTorsionFree (0 : twoTorsionIndex B →₀ (B : Type)) = 0 := by
  rw [evalTwoTorsionFree, Finsupp.sum_zero_index]

/-- Evaluation of free sections is additive. -/
lemma evalTwoTorsionFree_add {B : CommAlgCat.{0} ℤ} (y z : twoTorsionIndex B →₀ (B : Type)) :
    evalTwoTorsionFree (y + z) = evalTwoTorsionFree y + evalTwoTorsionFree z := by
  classical
  rw [evalTwoTorsionFree, evalTwoTorsionFree, evalTwoTorsionFree,
    Finsupp.sum_add_index (fun _ _ => by rw [zero_mul]) (fun _ _ b₁ b₂ => by rw [add_mul])]

/-- Evaluation of free sections is linear over the algebra. -/
lemma evalTwoTorsionFree_smul {B : CommAlgCat.{0} ℤ} (c : B)
    (y : twoTorsionIndex B →₀ (B : Type)) :
    evalTwoTorsionFree (c • y) = c * evalTwoTorsionFree y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [smul_zero, evalTwoTorsionFree_zero, mul_zero]
  | add y z hy hz => rw [smul_add, evalTwoTorsionFree_add, hy, hz, evalTwoTorsionFree_add,
      mul_add]
  | single u a => rw [Finsupp.smul_single, evalTwoTorsionFree_single,
      evalTwoTorsionFree_single, smul_eq_mul, mul_assoc]

/-- The evaluation of a free section is two-torsion. -/
lemma two_mul_evalTwoTorsionFree {B : CommAlgCat.{0} ℤ}
    (y : twoTorsionIndex B →₀ (B : Type)) : (2 : B) * evalTwoTorsionFree y = 0 := by
  induction y using Finsupp.induction_linear with
  | zero => rw [evalTwoTorsionFree_zero, mul_zero]
  | add y z hy hz => rw [evalTwoTorsionFree_add, mul_add, hy, hz, add_zero]
  | single u a =>
    rw [evalTwoTorsionFree_single, show (2 : B) * (a * u twoTorsionVar)
      = a * ((2 : B) * u twoTorsionVar) by ring, two_mul_apply_twoTorsionVar, mul_zero]

/-- Evaluation of free sections commutes with the transition functions. -/
lemma evalTwoTorsionFree_map {B D : CommAlgCat.{0} ℤ} (f : B ⟶ D)
    (y : twoTorsionIndex B →₀ (B : Type)) :
    evalTwoTorsionFree (twoTorsionFreeFun f y) = f.hom (evalTwoTorsionFree y) := by
  induction y using Finsupp.induction_linear with
  | zero => rw [twoTorsionFreeFun_zero, evalTwoTorsionFree_zero, evalTwoTorsionFree_zero,
      map_zero]
  | add y z hy hz => rw [twoTorsionFreeFun_add, evalTwoTorsionFree_add, hy, hz,
      evalTwoTorsionFree_add, map_add]
  | single u a =>
    rw [twoTorsionFreeFun_single, evalTwoTorsionFree_single, evalTwoTorsionFree_single, map_mul]
    rfl

/-! ### The rank-one module extension and its doubling -/

section RankOne

attribute [-instance] AddCommGroup.toIntModule

/-- The rank-one finite free `ℤ`-module, in the library's own presentation. -/
noncomputable abbrev rankOne : ModuleCat.{0} ℤ := finiteFreeModule.{0} ℤ 1

/-- The rank-one free module is `ℤ`. -/
noncomputable def rankOneEquiv : (rankOne : Type) ≃ₗ[ℤ] ℤ :=
  ULift.moduleEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

/-- The standard basis vector of the rank-one free module. -/
noncomputable def rankOneGen : (rankOne : Type) := rankOneEquiv.symm 1

/-- The standard basis vector corresponds to `1 : ℤ`. -/
@[simp] lemma rankOneEquiv_gen : rankOneEquiv rankOneGen = 1 :=
  rankOneEquiv.apply_symm_apply 1

/-- **Multiplication by two**: a finite free presentation `ℤ ⟶ ℤ` of `ℤ/2`. -/
noncomputable def doubling : rankOne ⟶ rankOne :=
  ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : (rankOne : Type) →ₗ[ℤ] (rankOne : Type)))

/-- The induced morphism of module-valued functors. -/
noncomputable abbrev doublingExt :
    moduleExtension.{0, 0} ℤ rankOne ⟶ moduleExtension.{0, 0} ℤ rankOne :=
  (moduleExtensionFunctor.{0, 0} ℤ).map doubling

/-- The section `1 ⊗ e` of the rank-one module extension. -/
noncomputable def unitAt (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ) :
    (moduleExtension.{0, 0} ℤ rankOne).obj X :=
  (1 : X.unop.unop) ⊗ₜ[ℤ] rankOneGen

/-- The coordinate of a section of the rank-one module extension. -/
noncomputable def coordAt (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ) :=
  (TensorProduct.congr (LinearEquiv.refl ℤ (X.unop.unop : Type)) rankOneEquiv).trans
    (TensorProduct.rid ℤ (X.unop.unop : Type))

/-- `c • (1 ⊗ e) = c ⊗ e`. -/
lemma smul_unitAt (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ) (c : X.unop.unop) :
    c • unitAt X = c ⊗ₜ[ℤ] rankOneGen := by
  rw [unitAt, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The coordinate of `c • (1 ⊗ e)` is `c`. -/
@[simp] lemma coordAt_smul_unitAt (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ) (c : X.unop.unop) :
    coordAt X (c • unitAt X) = c := by
  rw [smul_unitAt]
  change (TensorProduct.rid ℤ (X.unop.unop : Type))
    (TensorProduct.congr (LinearEquiv.refl ℤ (X.unop.unop : Type)) rankOneEquiv
      (c ⊗ₜ[ℤ] rankOneGen)) = c
  rw [TensorProduct.congr_tmul, rankOneEquiv_gen, TensorProduct.rid_tmul]
  rw [Algebra.smul_def, map_one, one_mul]
  rfl

/-- A section of the rank-one module extension is determined by its coordinate. -/
lemma eq_smul_unitAt (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ)
    (z : (moduleExtension.{0, 0} ℤ rankOne).obj X) : z = (coordAt X z) • unitAt X := by
  refine (coordAt X).injective ?_
  rw [coordAt_smul_unitAt]

/-- The section `1 ⊗ e` is preserved by the transition maps. -/
lemma map_unitAt {X Y : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
    (moduleExtension.{0, 0} ℤ rankOne).map f (unitAt X) = unitAt Y := by
  rw [unitAt, moduleExtension_map_tmul, map_one]
  rfl

/-- Doubling acts on sections by adding them to themselves. -/
lemma doublingExt_app (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ)
    (z : (moduleExtension.{0, 0} ℤ rankOne).obj X) : doublingExt.app X z = z + z := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    have h : doublingExt.app X (b ⊗ₜ[ℤ] m) = b ⊗ₜ[ℤ] (m + m) :=
      (moduleExtensionFunctor_map_app_tmul ℤ doubling X b m).trans
        (congrArg (fun m' : (rankOne : Type) => b ⊗ₜ[ℤ] m')
          (by change (2 : ℤ) • m = m + m; exact two_smul ℤ m))
    rw [h, TensorProduct.tmul_add]
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, h₁, h₂]
    abel

end RankOne

/-! ### The epimorphism onto the kernel, and its non-splitting -/

/-- `L = ker(d̲)`: the linearly adequate functor `C ↦ C[2]`. -/
noncomputable abbrev twoTorsionKernel : ModuleValuedFunctor.{0, 0} ℤ := kernel doublingExt

/-- The morphism out of the free module on the two-torsion set given by evaluation. -/
noncomputable def twoTorsionFreeToExtension :
    twoTorsionFree ⟶ moduleExtension.{0, 0} ℤ rankOne where
  app X := ModuleCat.ofHom
    { toFun := fun y => evalTwoTorsionFree y • unitAt X
      map_add' := fun y z => by rw [evalTwoTorsionFree_add, add_smul]
      map_smul' := fun c y => by
        rw [evalTwoTorsionFree_smul, mul_smul]
        rfl }
  naturality := by
    intro X Y f
    ext y
    change evalTwoTorsionFree (twoTorsionFreeFun f.unop.unop y) • unitAt Y =
      (moduleExtension.{0, 0} ℤ rankOne).map f (evalTwoTorsionFree y • unitAt X)
    refine Eq.trans (congrArg (fun c : (Y.unop.unop : Type) => c • unitAt Y)
      (evalTwoTorsionFree_map f.unop.unop y)) ?_
    rw [map_smul_algebra f (evalTwoTorsionFree y), map_unitAt]
    rfl

/-- The evaluation morphism sends a free section `y` to `eval y • (1 ⊗ e)`. -/
lemma twoTorsionFreeToExtension_app (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ)
    (y : twoTorsionFree.obj X) :
    twoTorsionFreeToExtension.app X y = evalTwoTorsionFree y • unitAt X := rfl

/-- The evaluation morphism composed with doubling is zero. -/
lemma twoTorsionFreeToExtension_comp_doublingExt :
    twoTorsionFreeToExtension ≫ doublingExt = 0 := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  change doublingExt.app X (twoTorsionFreeToExtension.app X y) = 0
  rw [twoTorsionFreeToExtension_app, doublingExt_app, ← add_smul,
    show evalTwoTorsionFree y + evalTwoTorsionFree y = 0 by
      have h := two_mul_evalTwoTorsionFree (B := X.unop.unop) y
      rw [two_mul] at h
      exact h,
    zero_smul]

/-- The canonical epimorphism from the free module on the two-torsion set onto `L`. -/
noncomputable def fromTwoTorsionFree : twoTorsionFree ⟶ twoTorsionKernel :=
  kernel.lift doublingExt twoTorsionFreeToExtension twoTorsionFreeToExtension_comp_doublingExt

/-- The morphism onto `L` followed by the kernel inclusion is the evaluation morphism. -/
lemma ι_comp_fromTwoTorsionFree :
    fromTwoTorsionFree ≫ kernel.ι doublingExt = twoTorsionFreeToExtension :=
  kernel.lift_ι _ _ _

/-- The kernel inclusion of the image of a free section `y` is `eval y • (1 ⊗ e)`. -/
lemma ι_app_fromTwoTorsionFree_app (X : ((CommAlgCat.{0} ℤ)ᵒᵖ)ᵒᵖ) (y : twoTorsionFree.obj X) :
    (kernel.ι doublingExt).app X (fromTwoTorsionFree.app X y) =
      evalTwoTorsionFree y • unitAt X := by
  have h := congrArg (fun φ : twoTorsionFree ⟶ moduleExtension.{0, 0} ℤ rankOne => φ.app X y)
    ι_comp_fromTwoTorsionFree
  exact h.trans (twoTorsionFreeToExtension_app X y)

/-- The universal two-torsion algebra as an object of `Alg_ℤ`. -/
noncomputable abbrev twoTorsionAlg : CommAlgCat.{0} ℤ := CommAlgCat.of ℤ twoTorsionAlgebra

/-- Its polynomial extension, where the weight-one condition lives. -/
noncomputable abbrev twoTorsionPolyAlg : CommAlgCat.{0} ℤ :=
  CommAlgCat.of ℤ (Polynomial twoTorsionAlgebra)

/-- The weight-one scaling, as a morphism of `Alg_ℤ`. -/
noncomputable def scaleHom : twoTorsionAlg ⟶ twoTorsionPolyAlg :=
  CommAlgCat.ofHom twoTorsionScale

/-- The constant inclusion, as a morphism of `Alg_ℤ`. -/
noncomputable def constHom : twoTorsionAlg ⟶ twoTorsionPolyAlg :=
  CommAlgCat.ofHom twoTorsionConst

/-- The morphism from the free module on the two-torsion set onto `L` is an epimorphism. -/
instance epi_fromTwoTorsionFree : Epi fromTwoTorsionFree := by
  refine PresheafOfModules.epi_of_surjective (f := fromTwoTorsionFree) ?_
  intro W lam
  have hzero : doublingExt.app W ((kernel.ι doublingExt).app W lam) = 0 := by
    have h := congrArg
      (fun φ : twoTorsionKernel ⟶ moduleExtension.{0, 0} ℤ rankOne => φ.app W lam)
      (kernel.condition doublingExt)
    rw [PresheafOfModules.comp_app] at h
    exact h
  have hzz : (kernel.ι doublingExt).app W lam + (kernel.ι doublingExt).app W lam = 0 := by
    rw [← doublingExt_app]
    exact hzero
  have hc : (2 : W.unop.unop) * coordAt W ((kernel.ι doublingExt).app W lam) = 0 := by
    have h := congrArg (coordAt W) hzz
    rw [map_add, map_zero] at h
    rw [two_mul]
    exact h
  refine ⟨Finsupp.single (twoTorsionClassify _ hc) 1, ?_⟩
  refine PresheafOfModules.injective_of_mono (kernel.ι doublingExt) W ?_
  refine Eq.trans (ι_app_fromTwoTorsionFree_app W _) ?_
  rw [evalTwoTorsionFree_single, twoTorsionClassify_var, one_mul]
  exact (eq_smul_unitAt W _).symm

/-- The universal two-torsion section, over `ℤ[x]/(2x)` itself. -/
noncomputable def universalTwoTorsion : twoTorsionKernel.obj (op (op twoTorsionAlg)) :=
  fromTwoTorsionFree.app (op (op twoTorsionAlg))
    (Finsupp.single (AlgHom.id ℤ twoTorsionAlgebra) 1)

/-- The universal two-torsion section is `x • (1 ⊗ e)` in the rank-one module extension. -/
lemma ι_universalTwoTorsion :
    (kernel.ι doublingExt).app (op (op twoTorsionAlg)) universalTwoTorsion =
      twoTorsionVar • unitAt (op (op twoTorsionAlg)) := by
  refine Eq.trans (ι_app_fromTwoTorsionFree_app (op (op twoTorsionAlg))
    (Finsupp.single (AlgHom.id ℤ twoTorsionAlgebra) 1)) ?_
  rw [evalTwoTorsionFree_single]
  exact congrArg (fun c : (twoTorsionAlg : Type) => c • unitAt (op (op twoTorsionAlg)))
    (one_mul _)

/-- **The universal section is weight one.**  Its scaling along `x ↦ t x` is `t` times its
constant inclusion. -/
lemma map_universalTwoTorsion :
    twoTorsionKernel.map scaleHom.op.op universalTwoTorsion =
      (Polynomial.X : Polynomial twoTorsionAlgebra) •
        twoTorsionKernel.map constHom.op.op universalTwoTorsion := by
  refine PresheafOfModules.injective_of_mono (kernel.ι doublingExt)
    (op (op twoTorsionPolyAlg)) ?_
  have e := fun f : twoTorsionAlg ⟶ twoTorsionPolyAlg =>
    PresheafOfModules.naturality_apply (kernel.ι doublingExt) f.op.op universalTwoTorsion
  have e3 : (moduleExtension.{0, 0} ℤ rankOne).map scaleHom.op.op
        ((kernel.ι doublingExt).app (op (op twoTorsionAlg)) universalTwoTorsion) =
      (Polynomial.X : Polynomial twoTorsionAlgebra) •
        (moduleExtension.{0, 0} ℤ rankOne).map constHom.op.op
          ((kernel.ι doublingExt).app (op (op twoTorsionAlg)) universalTwoTorsion) := by
    have a : ∀ f : twoTorsionAlg ⟶ twoTorsionPolyAlg,
        (moduleExtension.{0, 0} ℤ rankOne).map f.op.op
          (twoTorsionVar • unitAt (op (op twoTorsionAlg))) =
        f.hom twoTorsionVar • unitAt (op (op twoTorsionPolyAlg)) := fun f => by
      rw [map_smul_algebra f.op.op twoTorsionVar, map_unitAt]
      rfl
    rw [ι_universalTwoTorsion, a, a]
    refine Eq.trans (congrArg
      (fun c : (twoTorsionPolyAlg : Type) => c • unitAt (op (op twoTorsionPolyAlg)))
      (show twoTorsionScale twoTorsionVar = Polynomial.X * twoTorsionConst twoTorsionVar by
        rw [twoTorsionScale_var, twoTorsionConst_var])) ?_
    exact (smul_smul (Polynomial.X : Polynomial twoTorsionAlgebra)
      (twoTorsionConst twoTorsionVar) (unitAt (op (op twoTorsionPolyAlg)))).symm
  refine (e scaleHom).trans (e3.trans ?_)
  rw [← e constHom]
  exact (((kernel.ι doublingExt).app (op (op twoTorsionPolyAlg))).hom.map_smul
    (Polynomial.X : Polynomial twoTorsionAlgebra) _).symm

/-- The transition function along the weight-one scaling, unfolded. -/
lemma twoTorsionFreeFun_scaleHom (y : twoTorsionIndex twoTorsionAlg →₀ (twoTorsionAlg : Type)) :
    twoTorsionFreeFun scaleHom y =
      Finsupp.mapDomain (fun v : twoTorsionIndex twoTorsionAlg => twoTorsionScale.comp v)
        (Finsupp.mapRange twoTorsionScale (map_zero twoTorsionScale) y) := rfl

/-- The transition function along the constant inclusion, unfolded. -/
lemma twoTorsionFreeFun_constHom (y : twoTorsionIndex twoTorsionAlg →₀ (twoTorsionAlg : Type)) :
    twoTorsionFreeFun constHom y =
      Finsupp.mapDomain (fun v : twoTorsionIndex twoTorsionAlg => twoTorsionConst.comp v)
        (Finsupp.mapRange twoTorsionConst (map_zero twoTorsionConst) y) := rfl

/-! ### The weight-one part of the free functor is degenerate -/

/-- **The free module on the two-torsion set has a degenerate weight-one part.**  A section
whose weight-one scaling agrees with `t` times its constant inclusion is supported at the
two-torsion section killing the variable, hence evaluates to zero. -/
theorem evalTwoTorsionFree_eq_zero_of_weightOne
    (y : twoTorsionIndex twoTorsionAlg →₀ (twoTorsionAlg : Type))
    (hy : twoTorsionFreeFun scaleHom y =
      (Polynomial.X : Polynomial twoTorsionAlgebra) • twoTorsionFreeFun constHom y) :
    evalTwoTorsionFree y = 0 := by
  rw [twoTorsionFreeFun_scaleHom, twoTorsionFreeFun_constHom] at hy
  have key : ∀ u : twoTorsionIndex twoTorsionAlg, u ≠ twoTorsionZero → y u = 0 := by
    intro u hu
    have hcoe := congrArg
      (fun z : (twoTorsionAlgebra →ₐ[ℤ] Polynomial twoTorsionAlgebra) →₀
        Polynomial twoTorsionAlgebra => z (twoTorsionScale.comp u)) hy
    rw [Finsupp.mapDomain_apply_of_injective twoTorsionScale_comp_injective, Finsupp.mapRange_apply,
      Finsupp.smul_apply, Finsupp.mapDomain_of_notMem_range, smul_zero] at hcoe
    · exact twoTorsionScale_injective (by rw [hcoe, map_zero])
    · intro ⟨u', hu'⟩
      exact hu (twoTorsion_collide hu'.symm).1
  refine Finset.sum_eq_zero fun u _ => ?_
  dsimp only
  by_cases hu : u = twoTorsionZero
  · subst hu
    rw [show twoTorsionZero twoTorsionVar = 0 from twoTorsionClassify_var _ _, mul_zero]
  · rw [key u hu, zero_mul]

/-! ### The refutation -/

/-- **A linearly adequate module-valued functor need not be a projective object.**  The kernel
`L` of the finite free presentation `d : ℤ ⟶ ℤ` of `ℤ/2` by multiplication by two — the
functor `C ↦ {c ∈ C | 2c = 0}` — is not projective in the ambient category of module-valued
functors on all of `CommAlgCat ℤ`. -/
theorem not_projective_twoTorsionKernel : ¬ Projective twoTorsionKernel := by
  intro _
  have hs : Projective.factorThru (𝟙 twoTorsionKernel) fromTwoTorsionFree ≫
      fromTwoTorsionFree = 𝟙 twoTorsionKernel :=
    Projective.factorThru_comp _ _
  set s := Projective.factorThru (𝟙 twoTorsionKernel) fromTwoTorsionFree with hsdef
  set y := s.app (op (op twoTorsionAlg)) universalTwoTorsion with hydef
  have hy : twoTorsionFreeFun scaleHom y =
      (Polynomial.X : Polynomial twoTorsionAlgebra) • twoTorsionFreeFun constHom y := by
    have h := fun f : twoTorsionAlg ⟶ twoTorsionPolyAlg =>
      PresheafOfModules.naturality_apply s f.op.op universalTwoTorsion
    have h1 := h scaleHom
    have h2 := h constHom
    have h3 : s.app (op (op twoTorsionPolyAlg))
          ((Polynomial.X : Polynomial twoTorsionAlgebra) •
            twoTorsionKernel.map constHom.op.op universalTwoTorsion) =
        (Polynomial.X : Polynomial twoTorsionAlgebra) • s.app (op (op twoTorsionPolyAlg))
          (twoTorsionKernel.map constHom.op.op universalTwoTorsion) :=
      (s.app (op (op twoTorsionPolyAlg))).hom.map_smul _ _
    rw [map_universalTwoTorsion, h3, h2] at h1
    exact h1.symm
  have hzero : evalTwoTorsionFree y = 0 := evalTwoTorsionFree_eq_zero_of_weightOne y hy
  have hback : fromTwoTorsionFree.app (op (op twoTorsionAlg)) y = universalTwoTorsion := by
    have h := congrArg
      (fun φ : twoTorsionKernel ⟶ twoTorsionKernel => φ.app (op (op twoTorsionAlg))
        universalTwoTorsion) hs
    simpa using h
  have h1 : (kernel.ι doublingExt).app (op (op twoTorsionAlg))
      (fromTwoTorsionFree.app (op (op twoTorsionAlg)) y) =
        evalTwoTorsionFree y • unitAt (op (op twoTorsionAlg)) :=
    ι_app_fromTwoTorsionFree_app _ y
  rw [hback] at h1
  have hcontra : twoTorsionVar • unitAt (op (op twoTorsionAlg)) = 0 := by
    rw [← ι_universalTwoTorsion, h1, hzero, zero_smul]
  have := congrArg (coordAt (op (op twoTorsionAlg))) hcontra
  rw [coordAt_smul_unitAt, map_zero] at this
  exact twoTorsionVar_ne_zero this

/-- `L` is linearly adequate: it is by construction the kernel of a morphism between the
module-valued functors of two finite free modules. -/
lemma isLinearlyAdequate_twoTorsionKernel :
    IsLinearlyAdequate (𝟭 (CommAlgCat.{0} ℤ)) twoTorsionKernel :=
  (isLinearlyAdequate_iff twoTorsionKernel).2 ⟨1, 1, doublingExt, ⟨Iso.refl _⟩⟩

/-- **Linear adequacy does not imply projectivity in the ambient category.** -/
theorem not_forall_projective_of_isLinearlyAdequate :
    ¬ ∀ F : ModuleValuedFunctor.{0, 0} ℤ,
      IsLinearlyAdequate (𝟭 (CommAlgCat.{0} ℤ)) F → Projective F :=
  fun h => not_projective_twoTorsionKernel (h _ isLinearlyAdequate_twoTorsionKernel)

end AdequateFunctor

end
