module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Cohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyClassOfClosedMap
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Triangulated

/-! # The cohomology of a differential graded algebra computes its derived endomorphisms

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, regarded as a right
differential graded module over itself. A degree-`k` homogeneous right `A`-linear endomorphism of
the regular module is left multiplication by its value at the unit, so such an endomorphism is
closed for the Hom differential exactly when that value is a cocycle, and is a boundary exactly
when it is a coboundary. By Tag 09LC this makes the degree-`k` cohomology of `A` the set of
homotopy classes of homomorphisms `A ⟶ A[k]`; and since every shift of the regular module is
orthogonal on the left to the acyclic modules (Tag 09K1), localizing at the quasi-isomorphisms
changes nothing. The upshot is the canonical bijection
$$H^k(A) \longrightarrow \Hom_{D(A, d)}(A, A[k]).$$

## Main definitions

* `DifferentialGradedModule.regularHomogeneousMul`: left multiplication by a homogeneous
  element, as a homogeneous endomorphism of the regular module.
* `DifferentialGradedModule.cohomologyToHomotopyCategory` and
  `DifferentialGradedModule.cohomologyToDerivedCategory`: the canonical maps from `H^k(A)` to the
  morphisms `A ⟶ A[k]` of the homotopy and of the derived category.

## Main results

* `DifferentialGradedModule.cohomologyToHomotopyCategory_bijective` and
  `DifferentialGradedModule.cohomologyToDerivedCategory_bijective`, packaged as the equivalence
  `DifferentialGradedModule.cohomologyEquivDerivedHom`.

## Implementation notes

*What the bijection is used for.* This is the identification `H^k(A) ≃ Hom_{D(A, d)}(A, A[k])`
through which hypothesis (2) of [Stacks, Tag 09R9] is read for the regular bimodule, and which
enters the graded endomorphism comparison of that lemma; it is stated here for the algebra alone,
with no bimodule in sight.

*Indices.* The Hom differential raises the degree, so the boundary condition in degree `k` is
about homogeneous maps of degree `k - 1`, whose differential has degree `k - 1 + 1`. Rather than
transporting along `k - 1 + 1 = k`, every statement below is proved pointwise on elements of the
algebra, where no index appears.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and the
modules all live in a single universe `u`, following Stacks Tag 09JJ.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC) for the dictionary
  between closed homogeneous maps and homomorphisms into a shift,
  [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the left orthogonality, and
  [Tag 09R9](https://stacks.math.columbia.edu/tag/09R9) for the use made of the result.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- Left multiplication by a homogeneous element of degree `k`, as a degree-`k` homogeneous right
`A`-linear endomorphism of the regular module. -/
def regularHomogeneousMul (k : ℤ) (a : A.grading k) :
    HomogeneousMap A (regularModule A) (regularModule A) k := by
  refine ⟨{ toFun := fun b => (a : A.A) * b
            map_add' := fun b c => mul_add _ b c
            map_smul' := fun r b => mul_smul_comm r (a : A.A) b }, ⟨?_, ?_⟩⟩
  · intro i b hb
    change (a : A.A) * b ∈ A.grading (i + k)
    simpa only [add_comm k i] using SetLike.mul_mem_graded a.property hb
  · intro c b
    change (a : A.A) * (MulOpposite.op c • b) = MulOpposite.op c • ((a : A.A) * b)
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_assoc]

/-- Left multiplication acts by multiplication. -/
@[simp] theorem regularHomogeneousMul_val_apply (k : ℤ) (a : A.grading k) (b : A.A) :
    (regularHomogeneousMul A k a).1 b = (a : A.A) * b :=
  rfl

/-- Left multiplication by `a` sends the unit to `a`. -/
@[simp] theorem regularHomogeneousMul_val_one (k : ℤ) (a : A.grading k) :
    (regularHomogeneousMul A k a).1 1 = a :=
  mul_one _

/-- The value at the unit of a degree-`k` homogeneous endomorphism of the regular module: a
homogeneous element of degree `k`. -/
def regularValueAtOne (k : ℤ) (f : HomogeneousMap A (regularModule A) (regularModule A) k) :
    A.grading k :=
  ⟨f.1 1, by simpa only [zero_add] using f.2.1 0 (1 : A.A) (SetLike.one_mem_graded A.grading)⟩

/-- The underlying element of the value at the unit is the value at the unit. -/
@[simp] theorem regularValueAtOne_val (k : ℤ)
    (f : HomogeneousMap A (regularModule A) (regularModule A) k) :
    (regularValueAtOne A k f : A.A) = f.1 1 :=
  rfl

/-- A homogeneous endomorphism of the regular module is left multiplication by its value at the
unit. -/
theorem regularHomogeneousMul_regularValueAtOne (k : ℤ)
    (f : HomogeneousMap A (regularModule A) (regularModule A) k) :
    regularHomogeneousMul A k (regularValueAtOne A k f) = f := by
  refine Subtype.ext (LinearMap.ext fun b => ?_)
  have h := f.2.2 b (1 : A.A)
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul] at h
  show (f.1 (1 : A.A)) * b = f.1 b
  exact h.symm

/-- The value at the unit of left multiplication by `a` is `a`. -/
theorem regularValueAtOne_regularHomogeneousMul (k : ℤ) (a : A.grading k) :
    regularValueAtOne A k (regularHomogeneousMul A k a) = a :=
  Subtype.ext (mul_one _)

/-- The Hom differential of a homogeneous endomorphism of the regular module, evaluated at the
unit, is the differential of its value at the unit. -/
theorem homogeneousMapDifferential_val_apply_one (k : ℤ)
    (f : HomogeneousMap A (regularModule A) (regularModule A) k) :
    (homogeneousMapDifferential A f).1 1 = A.d (f.1 1) := by
  have hd : (regularModule A).d (1 : A.A) = 0 := algebraDifferential_one A
  simp only [homogeneousMapDifferential_val, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, hd, map_zero, smul_zero, sub_zero]

/-- Left multiplication intertwines the differential of the algebra with the Hom differential. -/
theorem homogeneousMapDifferential_regularHomogeneousMul (k : ℤ) (a : A.grading k) (b : A.A) :
    (homogeneousMapDifferential A (regularHomogeneousMul A k a)).1 b = A.d (a : A.A) * b := by
  induction b using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | @homogeneous m b =>
    have hsmul : ((k.negOnePow : ℤ)) • ((a : A.A) * A.d b) =
        gradedSign R k • ((a : A.A) * A.d b) := by
      rw [← Int.cast_smul_eq_zsmul R, intCast_negOnePow]
    show A.d ((a : A.A) * (b : A.A)) - gradedSign R k • ((a : A.A) * A.d (b : A.A)) = _
    rw [A.leibniz k m (a : A.A) (b : A.A) a.property b.property, hsmul, add_sub_cancel_right]
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

/-- The action of a cocycle is closed for the Hom differential. -/
theorem homogeneousMapDifferential_regularHomogeneousMul_eq_zero (k : ℤ) (a : A.Cocycle k) :
    homogeneousMapDifferential A (regularHomogeneousMul A k a.1) = 0 := by
  refine Subtype.ext (LinearMap.ext fun b => ?_)
  refine (homogeneousMapDifferential_regularHomogeneousMul A k a.1 b).trans ?_
  show A.d (a.1 : A.A) * b = (0 : A.A)
  rw [a.2, zero_mul]

/-- The homomorphism `A ⟶ A[k]` of differential graded modules given by left multiplication by a
degree-`k` cocycle of the algebra. -/
def regularCocycleHom (k : ℤ) (a : A.Cocycle k) :
    regularModule A ⟶ (regularModule A).shift k :=
  ((homogeneousMapDifferential_eq_zero_iff_exists_hom_shift A _ _ k
    (regularHomogeneousMul A k a.1)).mp
      (homogeneousMapDifferential_regularHomogeneousMul_eq_zero A k a)).choose

/-- The homomorphism attached to a cocycle has left multiplication by it as its underlying
linear map. -/
theorem regularCocycleHom_toFun (k : ℤ) (a : A.Cocycle k) :
    (regularCocycleHom A k a).toFun = (regularHomogeneousMul A k a.1).1 :=
  ((homogeneousMapDifferential_eq_zero_iff_exists_hom_shift A _ _ k
    (regularHomogeneousMul A k a.1)).mp
      (homogeneousMapDifferential_regularHomogeneousMul_eq_zero A k a)).choose_spec

/-- Two cocycles act by the same morphism of the homotopy category exactly when they are
cohomologous. -/
theorem toHomotopyCategory_map_regularCocycleHom_eq_iff (k : ℤ) (a b : A.Cocycle k) :
    (toHomotopyCategory A).map (regularCocycleHom A k a) =
        (toHomotopyCategory A).map (regularCocycleHom A k b) ↔
      ∃ c : A.grading (k - 1), (a.1 : A.A) - b.1 = A.d c := by
  refine (toHomotopyCategory_map_eq_iff_exists_homogeneousMapDifferential A
    (f := regularHomogeneousMul A k a.1) (g := regularHomogeneousMul A k b.1)
    (regularCocycleHom_toFun A k a) (regularCocycleHom_toFun A k b)).trans ?_
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨regularValueAtOne A (k - 1) c, ?_⟩
    have h := LinearMap.congr_fun hc (1 : A.A)
    rw [homogeneousMapDifferential_val_apply_one] at h
    have h3 : ((regularHomogeneousMul A k a.1).1 - (regularHomogeneousMul A k b.1).1) (1 : A.A) =
        (a.1 : A.A) - b.1 := by
      show (a.1 : A.A) * 1 - (b.1 : A.A) * 1 = _
      rw [mul_one, mul_one]
    exact h3.symm.trans h.symm
  · rintro ⟨c, hc⟩
    refine ⟨regularHomogeneousMul A (k - 1) c, LinearMap.ext fun x => ?_⟩
    refine (homogeneousMapDifferential_regularHomogeneousMul A (k - 1) c x).trans ?_
    show A.d (c : A.A) * x = (a.1 : A.A) * x - (b.1 : A.A) * x
    rw [← sub_mul, ← hc]

/-- The canonical map from the degree-`k` cohomology of `A` to the morphisms of the homotopy
category from the regular module to its `k`-th shift. -/
def cohomologyToHomotopyCategory (k : ℤ) :
    A.Cohomology k → ((toHomotopyCategory A).obj (regularModule A) ⟶
      (toHomotopyCategory A).obj ((regularModule A).shift k)) :=
  Quotient.lift (fun a => (toHomotopyCategory A).map (regularCocycleHom A k a))
    (fun a b h => (toHomotopyCategory_map_regularCocycleHom_eq_iff A k a b).mpr h)

/-- On the class of a cocycle, the canonical map is the homotopy class of the action of that
cocycle. -/
theorem cohomologyToHomotopyCategory_mk (k : ℤ) (a : A.Cocycle k) :
    cohomologyToHomotopyCategory A k (Quotient.mk _ a) =
      (toHomotopyCategory A).map (regularCocycleHom A k a) :=
  rfl

/-- **The cohomology of `A` is the homotopy classes of maps from `A` to its shifts.** -/
theorem cohomologyToHomotopyCategory_bijective (k : ℤ) :
    Function.Bijective (cohomologyToHomotopyCategory A k) := by
  refine ⟨fun x y => Quotient.inductionOn₂ x y fun a b h =>
    (DifferentialGradedAlgebra.Cohomology.mk_eq_mk_iff A k a b).mpr
      ((toHomotopyCategory_map_regularCocycleHom_eq_iff A k a b).mp h), fun ψ => ?_⟩
  obtain ⟨F, hF⟩ := exists_hom_shift_toHomotopyCategory_map_eq A ψ
  have hcocycle : A.d (regularValueAtOne A k (homogeneousMapOfHomShift A F) : A.A) = 0 := by
    rw [regularValueAtOne_val, ← homogeneousMapDifferential_val_apply_one,
      homogeneousMapDifferential_homogeneousMapOfHomShift A F]
    rfl
  refine ⟨Quotient.mk _ ⟨regularValueAtOne A k (homogeneousMapOfHomShift A F), hcocycle⟩, ?_⟩
  rw [cohomologyToHomotopyCategory_mk, ← hF]
  refine congrArg (toHomotopyCategory A).map (Hom.ext ?_)
  rw [regularCocycleHom_toFun, regularHomogeneousMul_regularValueAtOne,
    homogeneousMapOfHomShift_val]

/-- The regular module is orthogonal on the left to the acyclic differential graded modules. This
is Tag 09K1, with the shift of the source taken to be trivial. -/
theorem leftOrthogonal_acyclic_toHomotopyCategory_regularModule :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (regularModule A)) :=
  ObjectProperty.prop_of_iso _
    ((toHomotopyCategory A).mapIso ((shiftZeroIso A).app (regularModule A)))
    (leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A 0)

/-- Localizing at the quasi-isomorphisms does not change the morphisms out of the regular
module. -/
theorem quasiIsomorphismsQ_map_bijective_regularModule (Y : HomotopyCategory A) :
    Function.Bijective ((quasiIsomorphisms' A).Q.map :
      ((toHomotopyCategory A).obj (regularModule A) ⟶ Y) →
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A)) ⟶
          (quasiIsomorphisms' A).Q.obj Y)) := by
  have hloc : (quasiIsomorphisms' A).Q.IsLocalization ((acyclic' A).trW) := by
    rw [acyclic_trW_eq_quasiIsomorphisms']
    infer_instance
  exact ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
    (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A) (quasiIsomorphisms' A).Q Y

/-- The canonical map from the degree-`k` cohomology of `A` to the morphisms of the derived
category from the regular module to its `k`-th shift. -/
def cohomologyToDerivedCategory (k : ℤ) :
    A.Cohomology k →
      (((toHomotopyCategory A) ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶
        ((toHomotopyCategory A) ⋙ (quasiIsomorphisms' A).Q).obj ((regularModule A).shift k)) :=
  fun x => (quasiIsomorphisms' A).Q.map (cohomologyToHomotopyCategory A k x)

/-- **The cohomology of `A` computes the derived endomorphisms of the regular module.** -/
theorem cohomologyToDerivedCategory_bijective (k : ℤ) :
    Function.Bijective (cohomologyToDerivedCategory A k) :=
  (quasiIsomorphismsQ_map_bijective_regularModule A _).comp
    (cohomologyToHomotopyCategory_bijective A k)

/-- The canonical bijection `H^k(A) ≃ Hom_{D(A, d)}(A, A[k])`. -/
def cohomologyEquivDerivedHom (k : ℤ) :
    A.Cohomology k ≃
      (((toHomotopyCategory A) ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶
        ((toHomotopyCategory A) ⋙ (quasiIsomorphisms' A).Q).obj ((regularModule A).shift k)) :=
  Equiv.ofBijective _ (cohomologyToDerivedCategory_bijective A k)

/-- The bijection `H^k(A) ≃ Hom_{D(A, d)}(A, A[k])` is the canonical map. -/
@[simp] theorem cohomologyEquivDerivedHom_apply (k : ℤ) (x : A.Cohomology k) :
    cohomologyEquivDerivedHom A k x = cohomologyToDerivedCategory A k x :=
  rfl

end DifferentialGradedModule

end
