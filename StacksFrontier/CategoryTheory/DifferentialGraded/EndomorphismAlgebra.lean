module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.DirectSum.Ring
public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.Algebra.DGA.Abelian
public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# The endomorphism differential graded algebra of an object

Let `A` be a differential graded category over a commutative ring `R` and let `x` be an object of
`A`. The graded `R`-module `⨁ n, A.Hom x x n` of self-maps of `x` is a differential graded
`R`-algebra: its multiplication is the composition of `A`, its unit is the identity of `x`, and
its differential is the differential of the Hom modules of `A`. The Leibniz rule of `A` is
exactly the Leibniz rule of this algebra.

This is the algebra `End(x)` appearing in the construction of the representable differential
graded module functor `Hom(x, -)`.

## Main definitions

* `DGCategory.endAlgebra`: the endomorphism differential graded algebra of `x`.
* `DGCategory.endFamily`, `DGCategory.endTotal`: the family of homogeneous pieces and their direct
  sum, the underlying graded module of `endAlgebra`.
* `DGCategory.endDifferential`: the differential of `endAlgebra`, assembled degreewise.

## Main results

* `DGCategory.comp_cast` and `DGCategory.comp_heq`: composition in a differential graded category
  depends on the degree equality only up to transport.
* `DGCategory.endDifferential_of`: the differential of `endAlgebra` is `A.d` on each summand.

## Implementation notes

The ring structure is obtained from `DirectSum.GRing`, and the `R`-algebra structure from
`DirectSum.GAlgebra`, assembled in `DGCategory.endGRing` and `DGCategory.endGAlgebra`; the graded
monoid axioms are the unitality and associativity of `A`, transported across the degree
equalities, which is where `comp_cast` is used. The grading of the resulting algebra is the
tautological one of `StacksFrontier.Algebra.DirectSum.RangeGrading`.

Because `DifferentialGradedAlgebra R` has its underlying algebra in the same universe as `R`, the
differential graded category is taken with its homogeneous morphisms in that universe as well;
its objects may live anywhere.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe w v u

variable {R : Type u} [CommRing R] (A : DGCategory.{w, v, u} R) (x : A.Obj)

/-! ### Transporting composition across a degree equality -/

variable {A} in
/-- Composition in a differential graded category depends on the proof of the degree equality
only through the degree, so transporting the composition at degree `m + n` gives the composition
at any degree equal to it. -/
theorem comp_cast {x y z : A.Obj} {m n k : ℤ} (h : m + n = k)
    (f : A.Hom y z m) (g : A.Hom x y n) : h ▸ (A.comp rfl f g) = A.comp h f g := by
  subst k
  rfl

variable {A} in
/-- Two compositions of the same pair of morphisms, landing in degrees that are equal, are
heterogeneously equal. -/
theorem comp_heq {x y z : A.Obj} {m n k k' : ℤ} {h : m + n = k} {h' : m + n = k'} (e : k = k')
    (f : A.Hom y z m) (g : A.Hom x y n) : HEq (A.comp h f g) (A.comp h' f g) := by
  cases e
  exact heq_of_eq (congrArg (fun q => A.comp q f g) (Subsingleton.elim h h'))

/-! ### The graded ring and algebra structures -/

/-- The family of homogeneous endomorphism modules of `x`. -/
abbrev endFamily : ℤ → Type w := fun n => A.Hom x x n

/-- The underlying module of the endomorphism differential graded algebra of `x`: the direct sum
of the homogeneous endomorphism modules. -/
abbrev endTotal : Type w := DirectSum ℤ (endFamily A x)

/-- Composition of homogeneous endomorphisms of `x`, in the degree `m + n`. -/
def endMul {m n : ℤ} (f : A.Hom x x m) (g : A.Hom x x n) : A.Hom x x (m + n) :=
  A.comp rfl f g

/-- Composing with a scalar multiple of the identity on the left is that scalar multiple. -/
theorem endMul_smul_id_left {n : ℤ} (r : R) (a : A.Hom x x n) :
    A.comp rfl (r • A.id x) a ≍ r • a := by
  have h : (0 : ℤ) + n = n := by omega
  exact (comp_heq (h' := h) h (r • A.id x) a).trans
    (heq_of_eq (by rw [A.comp_smul_left, A.id_comp]))

/-- Composing with a scalar multiple of the identity on the right is that scalar multiple. -/
theorem endMul_smul_id_right {n : ℤ} (r : R) (a : A.Hom x x n) :
    A.comp rfl a (r • A.id x) ≍ r • a := by
  have h : n + (0 : ℤ) = n := by omega
  exact (comp_heq (h' := h) h a (r • A.id x)).trans
    (heq_of_eq (by rw [A.comp_smul_right, A.comp_id]))

/-- The graded ring structure on the homogeneous endomorphism modules of `x`, with composition as
multiplication and the identity of `x` as unit. -/
@[instance_reducible]
noncomputable def endGRing : DirectSum.GRing (endFamily A x) := by
  classical
  letI : GradedMonoid.GMul (endFamily A x) := ⟨fun f g => endMul A x f g⟩
  letI : GradedMonoid.GOne (endFamily A x) := ⟨A.id x⟩
  letI : Mul (GradedMonoid (endFamily A x)) := ⟨fun a b => ⟨a.1 + b.1, endMul A x a.2 b.2⟩⟩
  letI : One (GradedMonoid (endFamily A x)) := ⟨⟨0, A.id x⟩⟩
  letI : DirectSum.GNonUnitalNonAssocSemiring (endFamily A x) :=
    { mul_zero := fun {i j} f => A.comp_zero_right rfl f
      zero_mul := fun {i j} g => A.comp_zero_left rfl g
      mul_add := fun {i j} f g h => A.comp_add_right rfl f g h
      add_mul := fun {i j} f g h => A.comp_add_left rfl f g h }
  letI : GradedMonoid.GMonoid (endFamily A x) := {
    one_mul := by
      rintro ⟨n, f⟩
      change (⟨0 + n, A.comp rfl (A.id x) f⟩ : Sigma (endFamily A x)) = ⟨n, f⟩
      apply Sigma.ext (by simp)
      change A.comp rfl (A.id x) f ≍ f
      have hdeg : (0 : ℤ) + n = n := by omega
      have hcomp : A.comp rfl (A.id x) f ≍ A.comp hdeg (A.id x) f :=
        (eqRec_heq hdeg (A.comp rfl (A.id x) f)).symm.trans
          (heq_of_eq (comp_cast hdeg (A.id x) f))
      exact hcomp.trans (heq_of_eq (A.id_comp f))
    mul_one := by
      rintro ⟨n, f⟩
      change (⟨n + 0, A.comp rfl f (A.id x)⟩ : Sigma (endFamily A x)) = ⟨n, f⟩
      apply Sigma.ext (by simp)
      change A.comp rfl f (A.id x) ≍ f
      have hdeg : n + (0 : ℤ) = n := by omega
      have hcomp : A.comp rfl f (A.id x) ≍ A.comp hdeg f (A.id x) :=
        (eqRec_heq hdeg (A.comp rfl f (A.id x))).symm.trans
          (heq_of_eq (comp_cast hdeg f (A.id x)))
      exact hcomp.trans (heq_of_eq (A.comp_id f))
    mul_assoc := by
      rintro ⟨m, f⟩ ⟨n, g⟩ ⟨k, h⟩
      change (⟨(m + n) + k, A.comp rfl (A.comp rfl f g) h⟩ : Sigma (endFamily A x)) =
        ⟨m + (n + k), A.comp rfl f (A.comp rfl g h)⟩
      apply Sigma.ext (by simp [add_assoc])
      change A.comp rfl (A.comp rfl f g) h ≍ A.comp rfl f (A.comp rfl g h)
      have hdeg : m + (n + k) = (m + n) + k := (add_assoc m n k).symm
      have hcomp : A.comp rfl f (A.comp rfl g h) ≍ A.comp hdeg f (A.comp rfl g h) :=
        (eqRec_heq hdeg (A.comp rfl f (A.comp rfl g h))).symm.trans
          (heq_of_eq (comp_cast hdeg f (A.comp rfl g h)))
      have hassoc : A.comp hdeg f (A.comp rfl g h) = A.comp rfl (A.comp rfl f g) h :=
        A.assoc rfl hdeg rfl rfl f g h
      exact (heq_of_eq hassoc.symm).trans hcomp.symm }
  refine {
    toGSemiring := ?_
    intCast := fun z => z • A.id x
    intCast_ofNat := ?_
    intCast_negSucc_ofNat := ?_ }
  · exact {
      natCast := fun n => n • A.id x
      natCast_zero := by simp
      natCast_succ := by
        intro n
        simp [add_smul, show GradedMonoid.GOne.one = A.id x from rfl] }
  · intro n
    simp
  · intro n
    simp

/-- The graded `R`-algebra structure on the homogeneous endomorphism modules of `x`, with `r`
acting as `r • 𝟙 x`. -/
@[instance_reducible]
noncomputable def endGAlgebra :
    @DirectSum.GAlgebra ℤ R (endFamily A x) inferInstance inferInstance inferInstance inferInstance
      (endGRing A x).toGSemiring := by
  classical
  letI : DirectSum.GRing (endFamily A x) := endGRing A x
  letI : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  refine {
    toFun := {
      toFun := fun r => r • A.id x
      map_zero' := zero_smul R (A.id x)
      map_add' := fun r s => add_smul r s (A.id x) }
    map_one := one_smul R (A.id x)
    map_mul := ?_
    commutes := ?_
    smul_def := ?_ }
  · intro r s
    apply Sigma.ext (zero_add (0 : ℤ)).symm
    apply heq_of_cast_eq (congrArg (endFamily A x) (zero_add (0 : ℤ)).symm)
    have h : (0 : ℤ) = 0 + 0 := (zero_add 0).symm
    cases h
    dsimp
    change (r * s) • A.id x = A.comp rfl (r • A.id x) (s • A.id x)
    rw [A.comp_smul_left, A.comp_smul_right, A.comp_id, smul_smul]
  · rintro r ⟨n, a⟩
    exact Sigma.ext ((zero_add n).trans (add_zero n).symm)
      ((endMul_smul_id_left A x r a).trans (endMul_smul_id_right A x r a).symm)
  · rintro r ⟨n, a⟩
    exact Sigma.ext (zero_add n).symm (endMul_smul_id_left A x r a).symm

/-! ### The differential -/

/-- The differential of `A` on the degree-`n` endomorphisms of `x`, as an `R`-linear map. -/
def endDifferentialComponent (n : ℤ) : A.Hom x x n →ₗ[R] A.Hom x x (n + 1) where
  toFun f := A.d f
  map_add' := A.d_add
  map_smul' := A.d_smul

/-- The differential of the endomorphism differential graded algebra of `x`. -/
def endDifferential : endTotal A x →ₗ[R] endTotal A x :=
  DirectSum.toModule R ℤ (endTotal A x) fun n =>
    (DirectSum.lof R ℤ (endFamily A x) (n + 1)).comp (endDifferentialComponent A x n)

/-- The differential of `endAlgebra` sends a homogeneous endomorphism `f` of degree `n` to `A.d f`,
placed in degree `n + 1`. -/
@[simp]
theorem endDifferential_of (n : ℤ) (f : A.Hom x x n) :
    endDifferential A x (DirectSum.of (endFamily A x) n f) =
      DirectSum.of (endFamily A x) (n + 1) (A.d f) := by
  show DirectSum.toModule R ℤ (endTotal A x)
      (fun i => (DirectSum.lof R ℤ (endFamily A x) (i + 1)).comp (endDifferentialComponent A x i))
      (DirectSum.lof R ℤ (endFamily A x) n f) = _
  rw [DirectSum.toModule_lof]
  exact DirectSum.lof_eq_of R ℤ (endFamily A x) (n + 1) (A.d f)

/-- The ring structure on the direct sum of the homogeneous endomorphism modules. -/
noncomputable instance endTotalRing : Ring (endTotal A x) := by
  classical
  letI : DirectSum.GRing (endFamily A x) := endGRing A x
  exact DirectSum.ring (endFamily A x)

/-- The `R`-module structure on the direct sum of the homogeneous endomorphism modules. -/
noncomputable instance endTotalModule : Module R (endTotal A x) := by
  classical
  letI : DirectSum.GRing (endFamily A x) := endGRing A x
  letI : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  letI : Ring (endTotal A x) := endTotalRing A x
  letI : DirectSum.GAlgebra R (endFamily A x) := endGAlgebra A x
  exact inferInstance

/-- The `R`-algebra structure on the direct sum of the homogeneous endomorphism modules. -/
noncomputable instance endTotalAlgebra : Algebra R (endTotal A x) := by
  classical
  letI : DirectSum.GRing (endFamily A x) := endGRing A x
  letI : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  letI : Ring (endTotal A x) := endTotalRing A x
  letI : DirectSum.GAlgebra R (endFamily A x) := endGAlgebra A x
  exact inferInstance

/-- Composing two homogeneous endomorphisms and placing the result in two equal degrees gives the
same element of the direct sum. -/
theorem endOf_comp_degree {m n k k' : ℤ} (h : m + n = k) (h' : m + n = k') (e : k = k')
    (f : A.Hom x x m) (g : A.Hom x x n) :
    DirectSum.of (endFamily A x) k (A.comp h f g) =
      DirectSum.of (endFamily A x) k' (A.comp h' f g) :=
  DirectSum.of_eq_of_heq e (comp_heq e f g)

/-! ### The endomorphism differential graded algebra -/

/-- The endomorphism differential graded algebra of an object `x` of a differential graded
category: the direct sum `⨁ n, A.Hom x x n`, with composition as multiplication, the identity of
`x` as unit and the differential of `A` as differential. -/
@[implicit_reducible]
noncomputable def endAlgebra : DifferentialGradedAlgebra R := by
  classical
  letI : DirectSum.GRing (endFamily A x) := endGRing A x
  letI : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  letI : Ring (endTotal A x) := endTotalRing A x
  letI : Module R (endTotal A x) := endTotalModule A x
  letI : DirectSum.GAlgebra R (endFamily A x) := endGAlgebra A x
  letI : Algebra R (endTotal A x) := endTotalAlgebra A x
  let grade : ℤ → Submodule R (endTotal A x) := DirectSum.rangeGrading R (endFamily A x)
  letI : SetLike.GradedMonoid grade := {
    one_mem := by
      refine ⟨A.id x, ?_⟩
      rw [DirectSum.lof_eq_of, DirectSum.one_def]
      with_unfolding_all rfl
    mul_mem := by
      intro m n a b ha hb
      obtain ⟨f, rfl⟩ := ha
      obtain ⟨g, rfl⟩ := hb
      refine ⟨endMul A x f g, ?_⟩
      simp only [DirectSum.lof_eq_of, DirectSum.of_mul_of]
      rfl }
  letI : DirectSum.Decomposition grade := DirectSum.rangeGradingDecomposition R (endFamily A x)
  letI : GradedAlgebra grade :=
    DirectSum.IsInternal.gradedAlgebra (DirectSum.Decomposition.isInternal grade)
  exact {
    A := endTotal A x
    grading := grade
    d := endDifferential A x
    d_comp_d := by
      change endDifferential A x ∘ₗ endDifferential A x = 0
      apply LinearMap.ext
      intro z
      induction z using DirectSum.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ => simp only [LinearMap.map_add, hz₁, hz₂]
      | of n f => simp [LinearMap.comp_apply, A.d_d]
    d_mem := by
      intro n a ha
      obtain ⟨f, rfl⟩ := ha
      change endDifferential A x (DirectSum.of (endFamily A x) n f) ∈ _
      rw [endDifferential_of]
      exact ⟨A.d f, (DirectSum.lof_eq_of R ℤ (endFamily A x) (n + 1) (A.d f)).symm⟩
    leibniz := by
      intro m n a b ha hb
      obtain ⟨f, rfl⟩ := ha
      obtain ⟨g, rfl⟩ := hb
      simp only [DirectSum.lof_eq_of, DirectSum.of_mul_of, endDifferential_of]
      change DirectSum.of (endFamily A x) ((m + n) + 1) (A.d (A.comp rfl f g)) =
        DirectSum.of (endFamily A x) ((m + 1) + n) (A.comp rfl (A.d f) g) +
          (m.negOnePow : ℤ) •
            DirectSum.of (endFamily A x) (m + (n + 1)) (A.comp rfl f (A.d g))
      have hfirst : (m + 1) + n = (m + n) + 1 := by omega
      have hsecond : m + (n + 1) = (m + n) + 1 := by omega
      rw [endOf_comp_degree A x rfl hfirst hfirst (A.d f) g,
        endOf_comp_degree A x rfl hsecond hsecond f (A.d g)]
      calc
        _ = DirectSum.of (endFamily A x) ((m + n) + 1) (A.d (A.comp rfl f g)) := rfl
        _ = DirectSum.of (endFamily A x) ((m + n) + 1)
              (A.comp hfirst (A.d f) g + (-1 : R) ^ m.natAbs • A.comp hsecond f (A.d g)) :=
            congrArg (DirectSum.of (endFamily A x) ((m + n) + 1))
              (A.leibniz (f := g) (g := f) (h := rfl))
        _ = DirectSum.of (endFamily A x) ((m + n) + 1) (A.comp hfirst (A.d f) g) +
              (-1 : R) ^ m.natAbs •
                DirectSum.of (endFamily A x) ((m + n) + 1) (A.comp hsecond f (A.d g)) := by
            simp only [map_add]
            rw [DirectSum.of_smul]
        _ = DirectSum.of (endFamily A x) ((m + n) + 1) (A.comp hfirst (A.d f) g) +
              m.negOnePow •
                DirectSum.of (endFamily A x) ((m + n) + 1) (A.comp hsecond f (A.d g)) := by
            congr 1
            rw [(Int.coe_negOnePow R m).symm]
            exact Int.cast_smul_eq_zsmul R m.negOnePow _ }

/-- The underlying algebra of `endAlgebra` is the direct sum of the homogeneous endomorphism
modules. -/
@[simp] theorem endAlgebra_A : (endAlgebra A x).A = endTotal A x := rfl

/-- The grading of `endAlgebra` is the tautological grading of the direct sum. -/
@[simp] theorem endAlgebra_grading (n : ℤ) :
    (endAlgebra A x).grading n = DirectSum.rangeGrading R (endFamily A x) n := rfl

/-- The differential of `endAlgebra` is `endDifferential`. -/
@[simp] theorem endAlgebra_d : (endAlgebra A x).d = endDifferential A x := rfl

/-- Multiplication in `endAlgebra` is composition in `A`. -/
theorem endTotal_of_mul_of {m n : ℤ} (f : A.Hom x x m) (g : A.Hom x x n) :
    DirectSum.of (endFamily A x) m f * DirectSum.of (endFamily A x) n g =
      DirectSum.of (endFamily A x) (m + n) (A.comp rfl f g) := by
  classical
  let _ : DirectSum.GRing (endFamily A x) := endGRing A x
  let _ : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  have h := DirectSum.of_mul_of (A := endFamily A x) f g
  rwa [show (GradedMonoid.GMul.mul f g : endFamily A x (m + n)) = A.comp rfl f g by
    with_unfolding_all rfl] at h

/-- The unit of `endAlgebra` is the identity of `x`. -/
theorem endTotal_one_eq : (1 : endTotal A x) = DirectSum.of (endFamily A x) 0 (A.id x) := by
  classical
  let _ : DirectSum.GRing (endFamily A x) := endGRing A x
  let _ : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  have h := DirectSum.one_def (A := endFamily A x)
  rwa [show (GradedMonoid.GOne.one : endFamily A x 0) = A.id x by with_unfolding_all rfl] at h

end DGCategory
