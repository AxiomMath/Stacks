module

public import StacksFrontier.Algebra.DGA.CentralAction
public import StacksFrontier.Algebra.DifferentialGraded.Module.CohomologyActionTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction

/-!
# Derived tensor products carry central actions to central actions

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, and let `c`
and `e` be central closed elements of degree zero of `A` and of `B`. Right multiplication by `c`
is a natural endomorphism of every differential graded `A`-module, and it descends to an element
of the centre of the derived category `D(A, d)`
(`DifferentialGradedModule.derivedCentralSMul`); likewise for `e`.

Let `N` be a differential graded `(A, B)`-bimodule on which `c` acts on the left as `e` acts on
the right: `c y = y e` for every `y ∈ N`. Then on a pure tensor `x ⊗ y` of `M ⊗_A N` the two
endomorphisms `(x c) ⊗ y` and `x ⊗ (y e)` agree, because the tensor product is balanced, so
tensoring with `N` carries right multiplication by `c` to right multiplication by `e`. The same
then holds for the derived tensor product `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)`, by the universal
property of a left derived functor.

## Main definitions

* `DifferentialGradedModule.derivedCentralSMul`: right multiplication by a central closed element
  of degree zero, as an element of the centre of `D(A, d)`.
* `CategoryTheory.CatCenter.Carries`: a functor `F` carries a central element `z` of its source
  to a central element `w` of its target if `F.map (z.app X) = w.app (F.obj X)` for every `X`.

## Main results

* `DifferentialGraded.Bimodule.tensorCompFunctor_map_centralSMul`: the differential graded
  computation.
* `DifferentialGraded.Bimodule.carries_derivedTensorFunctor`: the derived form.
* `CategoryTheory.CatCenter.Carries.comp` and `CategoryTheory.CatCenter.Carries.inverse`: the
  relation is stable under composition and passes to the inverse of an equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.CatCenter

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- A functor `F` *carries* the central element `z` of its source to the central element `w` of
its target if `F.map (z.app X) = w.app (F.obj X)` for every object `X`. -/
def Carries (F : C ⥤ D) (z : CatCenter C) (w : CatCenter D) : Prop :=
  ∀ X : C, F.map (z.app X) = w.app (F.obj X)

/-- Carrying central elements is stable under composition of functors. -/
theorem Carries.comp {F : C ⥤ D} {G : D ⥤ E} {z : CatCenter C} {w : CatCenter D}
    {v : CatCenter E} (hF : Carries F z w) (hG : Carries G w v) : Carries (F ⋙ G) z v :=
  fun X => by
    change G.map (F.map (z.app X)) = v.app (G.obj (F.obj X))
    rw [hF X, hG]

/-- If the functor of an equivalence carries `z` to `w`, its inverse carries `w` to `z`. -/
theorem Carries.inverse (e : C ≌ D) {z : CatCenter C} {w : CatCenter D}
    (h : Carries e.functor z w) : Carries e.inverse w z := fun Y => by
  apply e.functor.map_injective
  have hc := w.naturality (e.counit.app Y)
  have hc' := e.counit.naturality (w.app Y)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hc hc'
  rw [h]
  have hiso : IsIso (e.counit.app Y) := inferInstance
  rw [← cancel_mono (e.counit.app Y), hc', hc]

end CategoryTheory.CatCenter

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- **Right multiplication by a central closed element of degree zero, in `D(A, d)`.** The
element of the centre of the derived category `D(A, d)` induced by right multiplication by `c` on
every differential graded `A`-module. -/
def derivedCentralSMul {c : A.A} (hc : IsCentralCocycle c) : CatCenter (derivedCategory' A) :=
  ((centralSMulCenter.{u, u, u} hc).quotient (homotopyRel A)).localization
    (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)

/-- The value of `derivedCentralSMul hc` at the class of a module is the class of right
multiplication by `c`. -/
theorem derivedCentralSMul_app {c : A.A} (hc : IsCentralCocycle c)
    (M : DifferentialGradedModule.{u, u, u} A) :
    (derivedCentralSMul hc).app ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj M) =
      (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (centralSMul hc M) :=
  CatCenter.localization_app _ _ _ _

/-- Right multiplication by a sum is the sum of the right multiplications. -/
theorem derivedCentralSMul_add {c c' : A.A} (hc : IsCentralCocycle c)
    (hc' : IsCentralCocycle c') (hcc : IsCentralCocycle (c + c')) :
    derivedCentralSMul hcc = derivedCentralSMul hc + derivedCentralSMul hc' := by
  have h : centralSMulCenter.{u, u, u} hcc =
      centralSMulCenter.{u, u, u} hc + centralSMulCenter.{u, u, u} hc' :=
    CatCenter.ext _ _ fun M => Hom.ext (LinearMap.ext fun x => by
      change MulOpposite.op (c + c') • x = MulOpposite.op c • x + MulOpposite.op c' • x
      rw [MulOpposite.op_add, add_smul])
  unfold derivedCentralSMul
  rw [h, ← CatCenter.quotientRingHom_apply, map_add, CatCenter.quotientRingHom_apply,
    CatCenter.quotientRingHom_apply]
  exact CatCenter.localization_add _ _ _ _

/-- Right multiplication by zero is zero. -/
theorem derivedCentralSMul_zero (hc : IsCentralCocycle (0 : A.A)) :
    derivedCentralSMul hc = 0 := by
  have h : centralSMulCenter.{u, u, u} hc = 0 :=
    CatCenter.ext _ _ fun M => Hom.ext (LinearMap.ext fun x => by
      change MulOpposite.op (0 : A.A) • x = 0
      rw [MulOpposite.op_zero, zero_smul])
  unfold derivedCentralSMul
  rw [h, ← CatCenter.quotientRingHom_apply, map_zero]
  exact CatCenter.localization_zero _ _

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- The relative tensor product is balanced over a central closed element `c` of degree zero:
`(x c) ⊗ y = x ⊗ (c y)`. -/
theorem pure_centralSMul_eq (N : Bimodule A B) {c : A.A} (hc : IsCentralCocycle c)
    (M : DifferentialGradedModule.{u, u, u} A) (x : M.M) (y : N.rightModule.M) :
    ((tensorDGFunctor N).pure M).toLinearMap (MulOpposite.op c • x) y =
      ((tensorDGFunctor N).pure M).toLinearMap x ((N.leftMultiplication 0 ⟨c, hc.mem⟩).1 y) := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp only [smul_zero, map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [smul_add, map_add, LinearMap.add_apply, hx, hx']
  | @homogeneous p x =>
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | @homogeneous q y =>
      rw [((tensorDGFunctor N).pure M).balance p q 0 x y ⟨c, hc.mem⟩,
        leftMultiplication_apply N 0 q ⟨c, hc.mem⟩ y]

/-- On the regular bimodule of a homomorphism `φ : A → B`, left multiplication by a degree-zero
element `a` is right multiplication by `φ a`, when `φ a` is central. -/
theorem regular_leftMultiplication_zero {φ : A.Hom B} (a : A.grading 0)
    (hφ : ∀ b : B.A, φ.toAlgebraHom (a : A.A) * b = b * φ.toAlgebraHom (a : A.A))
    (y : (Bimodule.regular φ).rightModule.M) :
    ((Bimodule.regular φ).leftMultiplication 0 a).1 y =
      DistribSMul.toLinearMap R (Bimodule.regular φ).rightModule.M
        (MulOpposite.op (φ.toAlgebraHom (a : A.A))) y := by
  induction y using DirectSum.Decomposition.inductionOn
    (Bimodule.regular φ).rightModule.grading with
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | @homogeneous p y =>
    rw [leftMultiplication_apply]
    exact (regularBimoduleStructure_action φ 0 p a y).trans (hφ _)

/-- **Tensoring carries right multiplication by `c` to right multiplication by `e`.** If the
central closed degree-zero element `c` of `A` acts on the left of the bimodule `N` as the central
closed degree-zero element `e` of `B` acts on the right, then tensoring with `N` carries right
multiplication by `c` on `M` to right multiplication by `e` on `M ⊗_A N`. On a pure tensor both
sides are `(x c) ⊗ y = x ⊗ (c y) = x ⊗ (y e)`. -/
theorem tensorCompFunctor_map_centralSMul (N : Bimodule A B) {c : A.A} {e : B.A}
    (hc : IsCentralCocycle c) (he : IsCentralCocycle e)
    (hN : ∀ y : N.rightModule.M,
      (N.leftMultiplication 0 ⟨c, hc.mem⟩).1 y = MulOpposite.op e • y)
    (M : DifferentialGradedModule.{u, u, u} A) :
    (tensorCompFunctor N).map (centralSMul hc M) =
      centralSMul he ((tensorCompFunctor N).obj M) := by
  refine tensorObj_hom_ext' N M _ _ fun x y => ?_
  have h : ((tensorCompFunctor N).map (centralSMul hc M)).toFun
        (((tensorDGFunctor N).pure M).toLinearMap x y) =
      (centralSMul he ((tensorCompFunctor N).obj M)).toFun
        (((tensorDGFunctor N).pure M).toLinearMap x y) := by
    rw [tensorCompFunctor_map_pure', centralSMul_toFun_apply]
    change _ = (MulOpposite.op e • (((tensorDGFunctor N).pure M).toLinearMap x y :
      ((tensorDGFunctor N).functor.obj M).M))
    rw [← ((tensorDGFunctor N).pure M).map_right, ← hN]
    exact pure_centralSMul_eq N hc M x y
  exact h

/-- **The derived tensor product carries right multiplication by `c` to right multiplication by
`e`**, under the hypothesis of `DifferentialGraded.Bimodule.tensorCompFunctor_map_centralSMul`
that `c` acts on the left of `N` as `e` acts on the right. -/
theorem carries_derivedTensorFunctor (N : Bimodule A B) {c : A.A} {e : B.A}
    (hc : IsCentralCocycle c) (he : IsCentralCocycle e)
    (hN : ∀ y : N.rightModule.M,
      (N.leftMultiplication 0 ⟨c, hc.mem⟩).1 y = MulOpposite.op e • y) :
    CatCenter.Carries (derivedTensorFunctor N) (derivedCentralSMul hc) (derivedCentralSMul he) := by
  intro Y
  refine CatCenter.map_localization_app_of_isLeftDerivedFunctor (derivedTensorFunctor N)
    (derivedTensorFunctorCounit N) (quasiIsomorphisms' A) _ (derivedCentralSMul he) ?_ Y
  rintro ⟨M⟩
  let ι := (tensorCompFunctor_quotient N).app M
  have hnat : (toHomotopyCategory B).map ((tensorCompFunctor N).map (centralSMul hc M)) ≫ ι.hom =
      ι.hom ≫ (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map (centralSMul hc M)) :=
    (tensorCompFunctor_quotient N).hom.naturality (centralSMul hc M)
  rw [tensorCompFunctor_map_centralSMul N hc he hN M] at hnat
  have hz : ι.hom ≫ ((centralSMulCenter.{u, u, u} he).quotient (homotopyRel B)).app
        ((tensorHomotopyFunctor N).obj ((toHomotopyCategory A).obj M)) =
      (toHomotopyCategory B).map (centralSMul he ((tensorCompFunctor N).obj M)) ≫ ι.hom :=
    ((centralSMulCenter.{u, u, u} he).quotient (homotopyRel B)).naturality ι.hom
  change (quasiIsomorphisms' B).Q.map ((tensorHomotopyFunctor N).map
      ((toHomotopyCategory A).map (centralSMul hc M))) =
    (derivedCentralSMul he).app ((quasiIsomorphisms' B).Q.obj
      ((tensorHomotopyFunctor N).obj ((toHomotopyCategory A).obj M)))
  have h1 : (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map (centralSMul hc M)) =
      ((centralSMulCenter.{u, u, u} he).quotient (homotopyRel B)).app
        ((tensorHomotopyFunctor N).obj ((toHomotopyCategory A).obj M)) := by
    rw [← cancel_epi ι.hom]
    exact hnat.symm.trans hz.symm
  rw [h1]
  exact (CatCenter.localization_app _ _ _ _).symm

end DifferentialGraded.Bimodule

end
