module

public import StacksFrontier.CategoryTheory.DifferentialGraded.EndomorphismAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The representable differential graded modules of an object

Let `A` be a differential graded category over a commutative ring `R` and let `x` be an object of
`A`. For every object `y`, the graded `R`-module `⨁ n, A.Hom x y n` is a right differential graded
module over the endomorphism differential graded algebra `DGCategory.endAlgebra A x`: the action
of a homogeneous endomorphism of `x` is precomposition with it, and the differential is the
differential of the Hom modules of `A`. Associativity of composition is the module axiom, and the
Leibniz rule of `A` is the Leibniz rule of the module.

These are the values of the representable functor `Hom(x, -)` of Tag 09LE.

## Main definitions

* `DGCategory.representableModule`: the differential graded `endAlgebra A x`-module `Hom(x, y)`.
* `DGCategory.repFamily`, `DGCategory.repTotal`: its homogeneous pieces and their direct sum.
* `DGCategory.repActionLinear`: the action of `endTotal A x` on `repTotal A x y`.
* `DGCategory.repDifferential`: the differential of `representableModule`.

## Main results

* `DGCategory.repActionLinear_of`: the action of a homogeneous endomorphism on a homogeneous
  morphism is their composite.
* `DGCategory.repDifferential_of`: the differential is `A.d` on each summand.

## Implementation notes

The right action is produced as a linear map `endTotal A x →ₗ[R] End (repTotal A x y)` and then
turned into a `Module (MulOpposite (endTotal A x))` structure, whose axioms are checked on the
generators of the two direct sums by `DirectSum.induction_on`. Everywhere that composition has to
be re-indexed, `DGCategory.comp_cast` and `DGCategory.comp_heq` from
`StacksFrontier.CategoryTheory.DifferentialGraded.EndomorphismAlgebra` do the transport.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe w v u

variable {R : Type u} [CommRing R] (A : DGCategory.{w, v, u} R) (x : A.Obj)

/-- The family of homogeneous morphism modules from `x` to `y`. -/
abbrev repFamily (y : A.Obj) : ℤ → Type w := fun n => A.Hom x y n

/-- The underlying module of the representable differential graded module `Hom(x, y)`: the direct
sum of the homogeneous morphism modules. -/
abbrev repTotal (y : A.Obj) : Type w := DirectSum ℤ (repFamily A x y)

/-- Composing two morphisms out of `x` and placing the result in two equal degrees gives the same
element of the direct sum. -/
theorem repOf_comp_degree {y z : A.Obj} {m n k k' : ℤ} (h : m + n = k) (h' : m + n = k')
    (e : k = k') (f : A.Hom y z m) (g : A.Hom x y n) :
    DirectSum.of (repFamily A x z) k (A.comp h f g) =
      DirectSum.of (repFamily A x z) k' (A.comp h' f g) :=
  DirectSum.of_eq_of_heq e (comp_heq e f g)

/-! ### The right action -/

/-- Precomposition with a fixed homogeneous endomorphism `a` of `x`, on degree-`n` morphisms out
of `x`. -/
def repRightMul {y : A.Obj} (i n : ℤ) (a : A.Hom x x i) :
    A.Hom x y n →ₗ[R] A.Hom x y (n + i) where
  toFun b := A.comp rfl b a
  map_add' b c := A.comp_add_left rfl b c a
  map_smul' r b := A.comp_smul_left rfl r b a

/-- The action of a fixed homogeneous endomorphism of `x` on all of `Hom(x, y)`. -/
def repActionComponent {y : A.Obj} (i : ℤ) (a : A.Hom x x i) :
    repTotal A x y →ₗ[R] repTotal A x y :=
  DirectSum.toModule R ℤ (repTotal A x y) fun n =>
    (DirectSum.lof R ℤ (repFamily A x y) (n + i)).comp (repRightMul A x (y := y) i n a)

/-- The right action of the endomorphisms of `x` on `Hom(x, y)`, as an `R`-linear map into the
endomorphisms of the direct sum. -/
noncomputable def repActionLinear (y : A.Obj) :
    endTotal A x →ₗ[R] (repTotal A x y →ₗ[R] repTotal A x y) :=
  DirectSum.toModule R ℤ _ fun i =>
    { toFun := repActionComponent A x (y := y) i
      map_add' := by
        intro a b
        apply DirectSum.linearMap_ext
        intro n
        apply LinearMap.ext
        intro f
        simp only [LinearMap.comp_apply, repActionComponent, DirectSum.toModule_lof,
          repRightMul, LinearMap.add_apply]
        exact (congrArg (DirectSum.lof R ℤ (repFamily A x y) (n + i))
            (A.comp_add_right rfl f a b)).trans
          (map_add (DirectSum.lof R ℤ (repFamily A x y) (n + i)) _ _)
      map_smul' := by
        intro r a
        apply DirectSum.linearMap_ext
        intro n
        apply LinearMap.ext
        intro f
        simp only [LinearMap.comp_apply, repActionComponent, DirectSum.toModule_lof,
          repRightMul, LinearMap.smul_apply]
        exact (congrArg (DirectSum.lof R ℤ (repFamily A x y) (n + i))
            (A.comp_smul_right rfl r f a)).trans
          (map_smul (DirectSum.lof R ℤ (repFamily A x y) (n + i)) r _) }

/-- The action of a homogeneous endomorphism `a` of `x` of degree `i` on a homogeneous morphism
`b` of degree `n` out of `x` is the composite `b ∘ a`, placed in degree `n + i`. -/
@[simp]
theorem repActionLinear_of {y : A.Obj} (i n : ℤ) (a : A.Hom x x i) (b : A.Hom x y n) :
    repActionLinear A x y (DirectSum.of (endFamily A x) i a)
        (DirectSum.of (repFamily A x y) n b) =
      DirectSum.of (repFamily A x y) (n + i) (A.comp rfl b a) := by
  classical
  rw [← DirectSum.lof_eq_of R ℤ (endFamily A x) i a,
    ← DirectSum.lof_eq_of R ℤ (repFamily A x y) n b]
  simp only [repActionLinear, DirectSum.toModule_lof]
  show DirectSum.toModule R ℤ (repTotal A x y) (fun j =>
      (DirectSum.lof R ℤ (repFamily A x y) (j + i)).comp (repRightMul A x (y := y) i j a))
      (DirectSum.lof R ℤ (repFamily A x y) n b) = _
  rw [DirectSum.toModule_lof]
  exact DirectSum.lof_eq_of R ℤ (repFamily A x y) (n + i) (A.comp rfl b a)

/-- `Hom(x, y)` is a right module over the endomorphism algebra of `x`, by precomposition. -/
@[instance_reducible]
noncomputable def repModule (y : A.Obj) :
    Module (MulOpposite (endTotal A x)) (repTotal A x y) := by
  classical
  letI : DirectSum.GRing (endFamily A x) := endGRing A x
  letI : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  letI : Ring (endTotal A x) := endTotalRing A x
  letI : Module R (endTotal A x) := endTotalModule A x
  letI : DirectSum.GAlgebra R (endFamily A x) := endGAlgebra A x
  letI : Algebra R (endTotal A x) := endTotalAlgebra A x
  refine {
    smul := fun a z => repActionLinear A x y (MulOpposite.unop a) z
    one_smul := ?one
    mul_smul := ?mul
    smul_zero := fun a => map_zero (repActionLinear A x y (MulOpposite.unop a))
    smul_add := fun a z₁ z₂ => map_add (repActionLinear A x y (MulOpposite.unop a)) z₁ z₂
    zero_smul := ?zero
    add_smul := ?add }
  case one =>
    intro z
    induction z using DirectSum.induction_on with
    | zero =>
      change repActionLinear A x y (1 : endTotal A x) 0 = 0
      exact map_zero _
    | add z₁ z₂ h₁ h₂ =>
      change repActionLinear A x y (1 : endTotal A x) (z₁ + z₂) = _
      rw [map_add]
      change repActionLinear A x y (1 : endTotal A x) z₁ = z₁ at h₁
      change repActionLinear A x y (1 : endTotal A x) z₂ = z₂ at h₂
      rw [h₁, h₂]
    | of n b =>
      change repActionLinear A x y (1 : endTotal A x)
        (DirectSum.of (repFamily A x y) n b) = _
      rw [DirectSum.one_def, show (GradedMonoid.GOne.one : endFamily A x 0) = A.id x by
        with_unfolding_all rfl]
      rw [repActionLinear_of A x (y := y) 0 n (A.id x) b]
      have hdeg : n + (0 : ℤ) = n := by omega
      have hcomp : A.comp rfl b (A.id x) ≍ A.comp hdeg b (A.id x) :=
        (eqRec_heq hdeg (A.comp rfl b (A.id x))).symm.trans
          (heq_of_eq (comp_cast hdeg b (A.id x)))
      exact DirectSum.of_eq_of_heq hdeg (hcomp.trans (heq_of_eq (A.comp_id b)))
  case mul =>
    rintro ⟨a⟩ ⟨b⟩ z
    change repActionLinear A x y (b * a) z =
      repActionLinear A x y a (repActionLinear A x y b z)
    induction a using DirectSum.induction_on with
    | zero => simp
    | add a₁ a₂ h₁ h₂ => simp [h₁, h₂, map_add, mul_add]
    | of i f =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | add b₁ b₂ h₁ h₂ => simp [h₁, h₂, map_add, add_mul]
      | of j g =>
        induction z using DirectSum.induction_on with
        | zero => simp
        | add z₁ z₂ h₁ h₂ => simp [h₁, h₂, map_add]
        | of n h =>
          rw [DirectSum.of_mul_of]
          rw [show (GradedMonoid.GMul.mul g f : endFamily A x (j + i)) = A.comp rfl g f by
            with_unfolding_all rfl]
          rw [repActionLinear_of, repActionLinear_of, repActionLinear_of]
          have hdeg : n + (j + i) = (n + j) + i := by omega
          have hcast : A.comp rfl h (A.comp rfl g f) ≍ A.comp hdeg h (A.comp rfl g f) :=
            (eqRec_heq hdeg (A.comp rfl h (A.comp rfl g f))).symm.trans
              (heq_of_eq (comp_cast hdeg h (A.comp rfl g f)))
          exact DirectSum.of_eq_of_heq hdeg
            (hcast.trans (heq_of_eq (A.assoc rfl hdeg rfl rfl h g f)))
  case zero =>
    intro z
    change (repActionLinear A x y (0 : endTotal A x)) z = 0
    rw [show repActionLinear A x y (0 : endTotal A x) = 0 from map_zero _]
    rfl
  case add =>
    rintro ⟨a⟩ ⟨b⟩ z
    change repActionLinear A x y (a + b) z =
      repActionLinear A x y a z + repActionLinear A x y b z
    simp only [map_add, LinearMap.add_apply]

/-! ### The differential -/

/-- The differential of `A` on the degree-`n` morphisms from `x` to `y`, as an `R`-linear map. -/
def repDifferentialComponent (y : A.Obj) (n : ℤ) : A.Hom x y n →ₗ[R] A.Hom x y (n + 1) where
  toFun := A.d
  map_add' := A.d_add
  map_smul' := A.d_smul

/-- The differential of the representable differential graded module `Hom(x, y)`. -/
def repDifferential (y : A.Obj) : repTotal A x y →ₗ[R] repTotal A x y :=
  DirectSum.toModule R ℤ (repTotal A x y) fun n =>
    (DirectSum.lof R ℤ (repFamily A x y) (n + 1)).comp (repDifferentialComponent A x y n)

/-- The differential of `Hom(x, y)` sends a homogeneous morphism `f` of degree `n` to `A.d f`,
placed in degree `n + 1`. -/
@[simp]
theorem repDifferential_of (y : A.Obj) (n : ℤ) (f : A.Hom x y n) :
    repDifferential A x y (DirectSum.of (repFamily A x y) n f) =
      DirectSum.of (repFamily A x y) (n + 1) (A.d f) := by
  show DirectSum.toModule R ℤ (repTotal A x y)
      (fun i => (DirectSum.lof R ℤ (repFamily A x y) (i + 1)).comp
        (repDifferentialComponent A x y i))
      (DirectSum.lof R ℤ (repFamily A x y) n f) = _
  rw [DirectSum.toModule_lof]
  exact DirectSum.lof_eq_of R ℤ (repFamily A x y) (n + 1) (A.d f)

/-! ### The representable differential graded module -/

/-- The representable right differential graded module `Hom(x, y)` over the endomorphism
differential graded algebra of `x`: the direct sum `⨁ n, A.Hom x y n`, with the right action of
`End(x)` by precomposition and the differential of `A` as differential. -/
@[implicit_reducible, ega "IV 2.5.6" "more general"]
noncomputable def representableModule (y : A.Obj) :
    DifferentialGradedModule (endAlgebra A x) := by
  classical
  letI : DirectSum.GRing (endFamily A x) := endGRing A x
  letI : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  letI : Ring (endTotal A x) := endTotalRing A x
  letI : Module R (endTotal A x) := endTotalModule A x
  letI : DirectSum.GAlgebra R (endFamily A x) := endGAlgebra A x
  letI : Algebra R (endTotal A x) := endTotalAlgebra A x
  letI : Module (MulOpposite (endTotal A x)) (repTotal A x y) := repModule A x y
  letI : Module (MulOpposite ((endAlgebra A x).A)) (repTotal A x y) := repModule A x y
  letI : IsScalarTower R (MulOpposite ((endAlgebra A x).A)) (repTotal A x y) :=
    IsScalarTower.of_algebraMap_smul fun r z => by
      change repActionLinear A x y (algebraMap R (endTotal A x) r) z = r • z
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
      change r • (repActionLinear A x y (1 : endTotal A x) z) = r • z
      congr 1
      change (1 : MulOpposite (endTotal A x)) • z = z
      exact one_smul _ _
  refine {
    M := repTotal A x y
    grading := DirectSum.rangeGrading R (repFamily A x y)
    decomposition := DirectSum.rangeGradingDecomposition R (repFamily A x y)
    smul_mem := ?_
    d := repDifferential A x y
    d_comp_d := ?_
    d_mem := ?_
    leibniz := ?_ }
  · intro n m b a hb ha
    obtain ⟨b, rfl⟩ := hb
    obtain ⟨a, rfl⟩ := ha
    change repActionLinear A x y (DirectSum.of (endFamily A x) m a)
      (DirectSum.of (repFamily A x y) n b) ∈ _
    rw [repActionLinear_of]
    exact ⟨A.comp rfl b a,
      DirectSum.lof_eq_of R ℤ (repFamily A x y) (n + m) (A.comp rfl b a)⟩
  · change repDifferential A x y ∘ₗ repDifferential A x y = 0
    apply LinearMap.ext
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z₁ z₂ hz₁ hz₂ =>
      simp only [LinearMap.comp_apply, LinearMap.map_add] at hz₁ hz₂ ⊢
      rw [hz₁, hz₂]
    | of n f => simp [LinearMap.comp_apply, A.d_d]
  · intro n b hb
    obtain ⟨f, rfl⟩ := hb
    change repDifferential A x y (DirectSum.of (repFamily A x y) n f) ∈ _
    rw [repDifferential_of]
    exact ⟨A.d f, (DirectSum.lof_eq_of R ℤ (repFamily A x y) (n + 1) (A.d f)).symm⟩
  · intro n m b a hb ha
    obtain ⟨b, rfl⟩ := hb
    obtain ⟨a, rfl⟩ := ha
    rw [DirectSum.lof_eq_of R ℤ (repFamily A x y) n b,
      DirectSum.lof_eq_of R ℤ (endFamily A x) m a]
    change repDifferential A x y
        (repActionLinear A x y (DirectSum.of (endFamily A x) m a)
          (DirectSum.of (repFamily A x y) n b)) =
      repActionLinear A x y (DirectSum.of (endFamily A x) m a)
          (repDifferential A x y (DirectSum.of (repFamily A x y) n b)) +
        (n.negOnePow : ℤ) • repActionLinear A x y
          (endDifferential A x (DirectSum.of (endFamily A x) m a))
          (DirectSum.of (repFamily A x y) n b)
    simp only [repDifferential_of, repActionLinear_of, endDifferential_of]
    have h₁ : (n + 1) + m = (n + m) + 1 := by omega
    have h₂ : n + (m + 1) = (n + m) + 1 := by omega
    rw [repOf_comp_degree A x rfl h₁ h₁ (A.d b) a,
      repOf_comp_degree A x rfl h₂ h₂ b (A.d a)]
    rw [← map_zsmul, ← map_add]
    refine congrArg (DirectSum.of (repFamily A x y) ((n + m) + 1)) ?_
    calc
      A.d (A.comp rfl b a) =
          A.comp h₁ (A.d b) a + (-1 : R) ^ n.natAbs • A.comp h₂ b (A.d a) :=
        A.leibniz rfl b a
      _ = A.comp h₁ (A.d b) a + (n.negOnePow : ℤ) • A.comp h₂ b (A.d a) := by
        congr 1
        rw [(Int.coe_negOnePow R n).symm]
        exact Int.cast_smul_eq_zsmul R n.negOnePow _

/-- The underlying module of `representableModule` is the direct sum of the homogeneous morphism
modules. -/
@[simp] theorem representableModule_M (y : A.Obj) :
    (representableModule A x y).M = repTotal A x y := rfl

/-- The grading of `representableModule` is the tautological grading of the direct sum. -/
@[simp] theorem representableModule_grading (y : A.Obj) (n : ℤ) :
    (representableModule A x y).grading n = DirectSum.rangeGrading R (repFamily A x y) n := rfl

/-- The differential of `representableModule` is `repDifferential`. -/
@[simp] theorem representableModule_d (y : A.Obj) :
    (representableModule A x y).d = repDifferential A x y := rfl

end DGCategory
