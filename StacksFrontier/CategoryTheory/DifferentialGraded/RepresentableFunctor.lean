module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.Representable

/-!
# The representable differential graded functor of an object

Let `A` be a differential graded category over a commutative ring `R` and let `x` be an object of
`A`. Postcomposition makes `y ↦ Hom(x, y)` a functor of differential graded categories from `A` to
the differential graded category of right differential graded modules over the endomorphism
algebra `End(x)`: a degree-`m` morphism `f : y ⟶ z` goes to the degree-`m` homogeneous
`End(x)`-linear map `Hom(x, y) → Hom(x, z)` given by `g ↦ f ∘ g`.

## Main definitions

* `DGCategory.repPostcomp`: postcomposition with a homogeneous morphism, on `Hom(x, -)`.
* `DGCategory.repPostcompHomogeneousMap`: the same map, as a homogeneous morphism of the
  differential graded category of differential graded `End(x)`-modules.
* `DGCategory.representableDGFunctor`: the functor of differential graded categories `Hom(x, -)`.

## Main results

* `DGCategory.repPostcomp_of`: postcomposition is composition on each summand.
* `DGCategory.repPostcomp_repActionLinear`: postcomposition commutes with the right action of
  `End(x)`.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe w v u

variable {R : Type u} [CommRing R] (A : DGCategory.{w, v, u} R) (x : A.Obj)

/-! ### Postcomposition -/

/-- Postcomposition with a fixed homogeneous morphism `f : y ⟶ z`, on degree-`n` morphisms out of
`x`. -/
def repPostcompComponent {y z : A.Obj} {m : ℤ} (f : A.Hom y z m) (n : ℤ) :
    A.Hom x y n →ₗ[R] A.Hom x z (m + n) where
  toFun g := A.comp rfl f g
  map_add' g h := A.comp_add_right rfl f g h
  map_smul' r g := A.comp_smul_right rfl r f g

/-- Postcomposition with a fixed homogeneous morphism `f : y ⟶ z`, on all of `Hom(x, -)`. -/
def repPostcomp {y z : A.Obj} {m : ℤ} (f : A.Hom y z m) : repTotal A x y →ₗ[R] repTotal A x z :=
  DirectSum.toModule R ℤ (repTotal A x z) fun n =>
    (DirectSum.lof R ℤ (repFamily A x z) (m + n)).comp (repPostcompComponent A x f n)

/-- Postcomposition with `f` sends the summand of `g` to the summand of `f ∘ g`. -/
@[simp]
theorem repPostcomp_of {y z : A.Obj} {m n : ℤ} (f : A.Hom y z m) (g : A.Hom x y n) :
    repPostcomp A x f (DirectSum.of (repFamily A x y) n g) =
      DirectSum.of (repFamily A x z) (m + n) (A.comp rfl f g) := by
  rw [← DirectSum.lof_eq_of R ℤ (repFamily A x y) n g]
  simp only [repPostcomp, DirectSum.toModule_lof, LinearMap.comp_apply, repPostcompComponent]
  exact DirectSum.lof_eq_of R ℤ (repFamily A x z) (m + n) (A.comp rfl f g)

/-- Associativity of composition `f ∘ (g ∘ a) = (f ∘ g) ∘ a`, as an equality of elements of the
direct sum `Hom(x, z)`. -/
theorem repOf_comp_assoc {y z : A.Obj} {m n i : ℤ}
    (f : A.Hom y z m) (g : A.Hom x y n) (a : A.Hom x x i) :
    DirectSum.of (repFamily A x z) (m + (n + i)) (A.comp rfl f (A.comp rfl g a)) =
      DirectSum.of (repFamily A x z) ((m + n) + i) (A.comp rfl (A.comp rfl f g) a) := by
  have hdeg : m + (n + i) = (m + n) + i := by omega
  have hleft : A.comp rfl f (A.comp rfl g a) ≍ A.comp hdeg f (A.comp rfl g a) :=
    comp_heq hdeg f (A.comp rfl g a)
  have hassoc : A.comp hdeg f (A.comp rfl g a) =
      A.comp (show (m + n) + i = (m + n) + i from rfl) (A.comp rfl f g) a :=
    A.assoc rfl hdeg rfl rfl f g a
  exact DirectSum.of_eq_of_heq hdeg (hleft.trans (heq_of_eq hassoc))

/-- Postcomposition commutes with the right action of `End(x)`. -/
theorem repPostcomp_repActionLinear {y z : A.Obj} {m : ℤ} (f : A.Hom y z m)
    (a : endTotal A x) (b : repTotal A x y) :
    repPostcomp A x f (repActionLinear A x y a b) =
      repActionLinear A x z a (repPostcomp A x f b) := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp [repActionLinear]
  | add a₁ a₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | of i g =>
    induction b using DirectSum.induction_on with
    | zero => simp [repActionLinear]
    | add b₁ b₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]
    | of n h =>
      rw [repActionLinear_of, repPostcomp_of, repPostcomp_of, repActionLinear_of]
      exact repOf_comp_assoc A x f h g

/-! ### Postcomposition as a homogeneous morphism of differential graded modules -/

/-- Postcomposition with a degree-`m` morphism `f : y ⟶ z`, as a degree-`m` homogeneous morphism
`Hom(x, y) ⟶ Hom(x, z)` of differential graded `End(x)`-modules. -/
noncomputable def repPostcompHomogeneousMap {y z : A.Obj} {m : ℤ} (f : A.Hom y z m) :
    (DifferentialGradedModule.dgCategory (endAlgebra A x)).Hom
      (representableModule A x y) (representableModule A x z) m := by
  classical
  refine ⟨repPostcomp A x f, ?_, fun a b => repPostcomp_repActionLinear A x f a b⟩
  rintro n b ⟨b, rfl⟩
  rw [DirectSum.lof_eq_of R ℤ (repFamily A x y) n b, repPostcomp_of]
  refine ⟨(show m + n = n + m by omega) ▸ A.comp rfl f b, ?_⟩
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_of_heq (show n + m = m + n by omega)
    (eqRec_heq (show m + n = n + m by omega) (A.comp rfl f b))

/-! ### The representable functor of differential graded categories -/

/-- The representable functor of differential graded categories `Hom(x, -)`, from `A` to the
differential graded category of right differential graded modules over the endomorphism algebra
of `x`. -/
noncomputable def representableDGFunctor :
    DGCategory.DGFunctor A (DifferentialGradedModule.dgCategory (endAlgebra A x)) := by
  classical
  refine {
    obj := representableModule A x
    map := fun {y z n} f => repPostcompHomogeneousMap A x f
    map_add := ?_
    map_smul := ?_
    map_d := ?_
    map_comp := ?_
    map_id := ?_ }
  · intro y z n f g
    refine Subtype.ext (LinearMap.ext fun b => ?_)
    change repPostcomp A x (f + g) b = repPostcomp A x f b + repPostcomp A x g b
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, map_add]; abel_nf
    | of i b =>
      simp only [repPostcomp_of]
      rw [A.comp_add_left]
      simp only [← DirectSum.lof_eq_of, map_add]
  · intro y z n r f
    refine Subtype.ext (LinearMap.ext fun b => ?_)
    change repPostcomp A x (r • f) b = r • repPostcomp A x f b
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add]; simp only [smul_add]
    | of i b =>
      simp only [repPostcomp_of]
      rw [A.comp_smul_left, DirectSum.of_smul]
  · intro y z n f
    refine Subtype.ext (LinearMap.ext fun b => ?_)
    change repPostcomp A x (A.d f) b =
      repDifferential A x z (repPostcomp A x f b) -
        DifferentialGraded.gradedSign R n • repPostcomp A x f (repDifferential A x y b)
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => rw [map_add, h₁, h₂]; simp [smul_add]; abel
    | of i b =>
      simp only [repDifferential_of, repPostcomp_of]
      have h₁ : (n + 1) + i = (n + i) + 1 := by omega
      have h₂ : n + (i + 1) = (n + i) + 1 := by omega
      rw [repOf_comp_degree A x rfl h₂ h₂ f (A.d b),
        repOf_comp_degree A x rfl h₁ h₁ (A.d f) b, ← DirectSum.of_sub_smul,
        (DirectSum.of_injective (β := repFamily A x z) ((n + i) + 1)).eq_iff,
        DifferentialGraded.gradedSign, A.leibniz rfl f b]
      abel
  · intro y z t m n k h f g
    refine Subtype.ext (LinearMap.ext fun b => ?_)
    change repPostcomp A x (A.comp h f g) b = repPostcomp A x f (repPostcomp A x g b)
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | of i b =>
      simp only [repPostcomp_of]
      have hdeg : m + (n + i) = k + i := by omega
      have hcast : A.comp rfl f (A.comp rfl g b) ≍ A.comp hdeg f (A.comp rfl g b) :=
        comp_heq hdeg f (A.comp rfl g b)
      have hassoc := A.assoc (show n + i = n + i from rfl) hdeg h
        (show k + i = k + i from rfl) f g b
      exact (DirectSum.of_eq_of_heq (show k + i = m + (n + i) by omega)
        (hcast.trans (heq_of_eq hassoc)).symm)
  · intro y
    refine Subtype.ext (LinearMap.ext fun b => ?_)
    change repPostcomp A x (A.id y) b = b
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | of n b =>
      rw [repPostcomp_of]
      have hdeg : (0 : ℤ) + n = n := by omega
      exact DirectSum.of_eq_of_heq hdeg
        ((comp_heq hdeg (A.id y) b).trans (heq_of_eq (A.id_comp b)))

/-- The representable functor sends `y` to `Hom(x, y)`. -/
@[simp] theorem representableDGFunctor_obj (y : A.Obj) :
    (representableDGFunctor A x).obj y = representableModule A x y := rfl

/-- The representable functor sends a homogeneous morphism to postcomposition with it. -/
@[simp] theorem representableDGFunctor_map {y z : A.Obj} {m : ℤ} (f : A.Hom y z m) :
    (representableDGFunctor A x).map f = repPostcompHomogeneousMap A x f := rfl

/-- On underlying linear maps, the representable functor is postcomposition. -/
@[simp] theorem representableDGFunctor_map_val {y z : A.Obj} {m : ℤ} (f : A.Hom y z m) :
    ((representableDGFunctor A x).map f).1 = repPostcomp A x f := rfl

end DGCategory
