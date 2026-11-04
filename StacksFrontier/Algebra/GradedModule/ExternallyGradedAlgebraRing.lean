module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.Algebra.GradedModule.ExternalShift

/-!
# The total algebra of an externally graded algebra

An externally `ℤ`-graded algebra `A` over a commutative ring `R` (a family of `R`-modules `Aⁿ`
with associative unital multiplications `Aⁱ × Aʲ → A^{i+j}`) is a graded `R`-algebra in Mathlib's
external sense, `DirectSum.GAlgebra R A.piece`, so that the direct sum `⨁ n, Aⁿ` is an
`R`-algebra. Its tautological grading `DirectSum.rangeGrading` by the images of the summands is
then a `GradedAlgebra` in Mathlib's internal sense. A family of linear maps `Aⁿ → Bⁿ` which is
multiplicative and unital assembles to an `R`-algebra homomorphism `⨁ Aⁿ → ⨁ Bⁿ` preserving the
gradings.

This is the passage from the cup product of a cohomology theory given degree by degree (for
instance by a monoid object of graded vector spaces) to the graded algebra `H^*(X)` of the data
(D1) of a Weil cohomology theory.

## Main definitions

* `ExternallyGradedAlgebra.instGRing`, `ExternallyGradedAlgebra.instGAlgebra`: the external graded
  ring and algebra structures on the pieces.
* `ExternallyGradedAlgebra.Total`: the total algebra `⨁ n, Aⁿ`.
* `ExternallyGradedAlgebra.grade`: its grading by the images of the summands.
* `ExternallyGradedAlgebra.totalMap`: the algebra homomorphism induced by a multiplicative unital
  family of linear maps.

## Main results

* `ExternallyGradedAlgebra.instGradedAlgebra`: the grading is a `GradedAlgebra`.
* `ExternallyGradedAlgebra.of_mul_of`: the product of homogeneous elements is the graded product.
* `ExternallyGradedAlgebra.totalMap_id`, `ExternallyGradedAlgebra.totalMap_comp`: functoriality.
-/

@[expose] public noncomputable section

open DirectSum

universe u v

namespace ExternallyGradedAlgebra

variable {R : Type u} [CommRing R] (A : ExternallyGradedAlgebra.{u, v} R)

/-- The graded multiplication `Aⁱ × Aʲ → A^{i+j}` of an externally graded algebra. -/
instance instGMul : GradedMonoid.GMul A.piece := ⟨fun {i j} a b ↦ A.mul i j a b⟩

/-- The unit of an externally graded algebra, an element of `A⁰`. -/
instance instGOne : GradedMonoid.GOne A.piece := ⟨A.one⟩

/-- The graded product of `a ∈ Aⁱ` and `b ∈ Aʲ` is `A.mul i j a b`. -/
theorem gMul_def {i j : ℤ} (a : A.piece i) (b : A.piece j) :
    GradedMonoid.GMul.mul a b = A.mul i j a b :=
  rfl

/-- The graded unit is `A.one`. -/
theorem gOne_def : (GradedMonoid.GOne.one : A.piece 0) = A.one :=
  rfl

/-- The pieces of an externally graded algebra form a graded ring in Mathlib's external sense. -/
instance instGRing : DirectSum.GRing A.piece where
  one_mul a := Sigma.ext (zero_add _) (A.one_mul _ a.2)
  mul_one a := Sigma.ext (add_zero _) (A.mul_one _ a.2)
  mul_assoc a b c := Sigma.ext (add_assoc _ _ _) (A.mul_assoc _ _ _ a.2 b.2 c.2)
  mul_zero a := (A.mul _ _ a).map_zero
  zero_mul b := LinearMap.map_zero₂ (A.mul _ _) b
  mul_add a b c := (A.mul _ _ a).map_add b c
  add_mul a b c := LinearMap.map_add₂ (A.mul _ _) a b c
  natCast n := n • A.one
  natCast_zero := zero_smul ℕ A.one
  natCast_succ n := succ_nsmul A.one n
  intCast n := n • A.one
  intCast_ofNat n := natCast_zsmul A.one n
  intCast_negSucc_ofNat n := by
    change Int.negSucc n • A.one = -((n + 1 : ℕ) • A.one)
    rw [negSucc_zsmul]

/-- The pieces of an externally graded algebra form a graded algebra in Mathlib's external
sense; the structure map is `r ↦ r • 1`. -/
instance instGAlgebra : DirectSum.GAlgebra R A.piece where
  toFun := (LinearMap.toSpanSingleton R _ A.one).toAddMonoidHom
  map_one := one_smul R A.one
  map_mul r s := by
    refine Sigma.ext (add_zero 0).symm ?_
    change (r * s) • A.one ≍ A.mul 0 0 (r • A.one) (s • A.one)
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul]
    exact ExternallyGraded.scalar_heq (zero_add 0).symm rfl (A.one_mul 0 A.one).symm
  commutes r x := by
    refine Sigma.ext (add_comm _ _) ?_
    change A.mul 0 x.1 (r • A.one) x.2 ≍ A.mul x.1 0 x.2 (r • A.one)
    rw [LinearMap.map_smul₂, LinearMap.map_smul]
    exact ExternallyGraded.scalar_heq (by simp) rfl ((A.one_mul _ x.2).trans (A.mul_one _ x.2).symm)
  smul_def r x := by
    refine Sigma.ext (zero_add _).symm ?_
    change r • x.2 ≍ A.mul 0 x.1 (r • A.one) x.2
    rw [LinearMap.map_smul₂]
    exact ExternallyGraded.scalar_heq (zero_add _).symm rfl (A.one_mul _ x.2).symm

/-- **The total algebra `⨁ n, Aⁿ`** of an externally graded algebra. -/
abbrev Total : Type v :=
  ⨁ n, A.piece n

/-- The product of homogeneous elements of the total algebra is their graded product. -/
theorem of_mul_of {i j : ℤ} (a : A.piece i) (b : A.piece j) :
    DirectSum.of A.piece i a * DirectSum.of A.piece j b =
      DirectSum.of A.piece (i + j) (A.mul i j a b) :=
  DirectSum.of_mul_of a b

/-- The unit of the total algebra is the unit of the degree-zero piece. -/
theorem one_eq_of : (1 : A.Total) = DirectSum.of A.piece 0 A.one :=
  rfl

/-- The scalars act on homogeneous elements degreewise. -/
theorem smul_of (r : R) {i : ℤ} (a : A.piece i) :
    r • DirectSum.of A.piece i a = DirectSum.of A.piece i (r • a) :=
  (DirectSum.lof_eq_of R ℤ A.piece i a ▸ DirectSum.lof_eq_of R ℤ A.piece i (r • a) ▸
    (map_smul (DirectSum.lof R ℤ A.piece i) r a).symm)

/-- **The grading of the total algebra** by the images of the summands. -/
abbrev grade (n : ℤ) : Submodule R A.Total :=
  DirectSum.rangeGrading R A.piece n

/-- The grading of the total algebra is multiplicative: `1 ∈ grade 0` and
`grade i * grade j ⊆ grade (i + j)`. -/
instance instGradedMonoid : SetLike.GradedMonoid A.grade where
  one_mem := ⟨A.one, by rw [DirectSum.lof_eq_of]; rfl⟩
  mul_mem := by
    rintro i j - - ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨A.mul i j a b, ?_⟩
    simp only [DirectSum.lof_eq_of, of_mul_of]

/-- **The grading of the total algebra is a `GradedAlgebra`.** -/
instance instGradedAlgebra : GradedAlgebra A.grade :=
  { instGradedMonoid A, DirectSum.rangeGradingDecomposition R A.piece with }

/-- An element of the total algebra has degree `n` iff it is the image of an element of `Aⁿ`. -/
theorem mem_grade_iff {n : ℤ} (x : A.Total) :
    x ∈ A.grade n ↔ ∃ a : A.piece n, x = DirectSum.of A.piece n a :=
  DirectSum.mem_rangeGrading R A.piece n x

/-- The image of an element of `Aⁿ` in the total algebra has degree `n`. -/
theorem of_mem_grade (n : ℤ) (a : A.piece n) : DirectSum.of A.piece n a ∈ A.grade n :=
  (A.mem_grade_iff _).2 ⟨a, rfl⟩

/-- The degree-`n` part of the total algebra is the piece `Aⁿ`. -/
def gradeEquiv (n : ℤ) : A.grade n ≃ₗ[R] A.piece n :=
  DirectSum.rangeGradingEquiv R A.piece n

/-- The inverse of `gradeEquiv` sends `a ∈ Aⁿ` to `DirectSum.of A.piece n a`. -/
theorem gradeEquiv_symm_apply_coe (n : ℤ) (a : A.piece n) :
    ((A.gradeEquiv n).symm a : A.Total) = DirectSum.of A.piece n a :=
  (DirectSum.lof_eq_of R ℤ A.piece n a)

/-- `gradeEquiv` sends a degree-`n` element equal to `DirectSum.of A.piece n a` to `a`. -/
theorem gradeEquiv_apply {n : ℤ} (x : A.grade n) (a : A.piece n)
    (hx : (x : A.Total) = DirectSum.of A.piece n a) : A.gradeEquiv n x = a :=
  DirectSum.rangeGradingEquiv_eq_of_coe_eq R A.piece x a hx

/-! ### Homomorphisms -/

variable {A} {B C : ExternallyGradedAlgebra.{u, v} R}

/-- If `f 0 1 = 1`, the family `f` sends the graded unit of `A` to the unit of `B.Total`. -/
theorem totalMap_one (f : ∀ n, A.piece n →ₗ[R] B.piece n) (hone : f 0 A.one = B.one) :
    (DirectSum.lof R ℤ B.piece 0 ∘ₗ f 0) (GradedMonoid.GOne.one : A.piece 0) = 1 := by
  simp [DirectSum.lof_eq_of, hone, one_eq_of, gOne_def]

/-- If the family `f` is multiplicative, it sends the graded product of `a ∈ Aⁱ` and `b ∈ Aʲ`
to the product of the images of `f i a` and `f j b` in `B.Total`. -/
theorem totalMap_mul (f : ∀ n, A.piece n →ₗ[R] B.piece n)
    (hmul : ∀ i j (a : A.piece i) (b : A.piece j), f (i + j) (A.mul i j a b) =
      B.mul i j (f i a) (f j b)) {i j : ℤ} (a : A.piece i) (b : A.piece j) :
    (DirectSum.lof R ℤ B.piece (i + j) ∘ₗ f (i + j)) (GradedMonoid.GMul.mul a b) =
      (DirectSum.lof R ℤ B.piece i ∘ₗ f i) a * (DirectSum.lof R ℤ B.piece j ∘ₗ f j) b := by
  simp [DirectSum.lof_eq_of, gMul_def, hmul, of_mul_of]

/-- **The algebra homomorphism `⨁ Aⁿ → ⨁ Bⁿ`** induced by a multiplicative unital family of
linear maps `f n : Aⁿ → Bⁿ`. -/
def totalMap (f : ∀ n, A.piece n →ₗ[R] B.piece n) (hone : f 0 A.one = B.one)
    (hmul : ∀ i j (a : A.piece i) (b : A.piece j), f (i + j) (A.mul i j a b) =
      B.mul i j (f i a) (f j b)) : A.Total →ₐ[R] B.Total :=
  DirectSum.toAlgebra R A.piece (fun n ↦ (DirectSum.lof R ℤ B.piece n).comp (f n))
    (totalMap_one f hone) (fun a b ↦ totalMap_mul f hmul a b)

/-- `totalMap f` sends the image of `a ∈ Aⁿ` to the image of `f n a ∈ Bⁿ`. -/
theorem totalMap_of (f : ∀ n, A.piece n →ₗ[R] B.piece n) (hone : f 0 A.one = B.one)
    (hmul : ∀ i j (a : A.piece i) (b : A.piece j), f (i + j) (A.mul i j a b) =
      B.mul i j (f i a) (f j b)) (n : ℤ) (a : A.piece n) :
    totalMap f hone hmul (DirectSum.of A.piece n a) = DirectSum.of B.piece n (f n a) :=
  (DirectSum.toSemiring_of (A := A.piece)
    (fun n ↦ ((DirectSum.lof R ℤ B.piece n).comp (f n)).toAddMonoidHom) (totalMap_one f hone)
    (fun a b ↦ totalMap_mul f hmul a b) n a).trans
    (DirectSum.lof_eq_of R ℤ B.piece n _)

/-- `totalMap f` sends elements of degree `n` to elements of degree `n`. -/
theorem totalMap_mem_grade (f : ∀ n, A.piece n →ₗ[R] B.piece n) (hone hmul) (n : ℤ)
    {x : A.Total} (hx : x ∈ A.grade n) : totalMap f hone hmul x ∈ B.grade n := by
  obtain ⟨a, rfl⟩ := (A.mem_grade_iff x).1 hx
  rw [totalMap_of]
  exact B.of_mem_grade n _

/-- The family of identity maps induces the identity of the total algebra. -/
theorem totalMap_id :
    totalMap (A := A) (fun _ ↦ LinearMap.id) rfl (fun _ _ _ _ ↦ rfl) = AlgHom.id R A.Total := by
  refine DirectSum.algHom_ext R A.piece fun n a ↦ ?_
  simp [totalMap_of]

/-- The degreewise composite `g ∘ f` induces the composite of the induced homomorphisms. -/
theorem totalMap_comp (f : ∀ n, A.piece n →ₗ[R] B.piece n) (hf₁ hf₂)
    (g : ∀ n, B.piece n →ₗ[R] C.piece n) (hg₁ hg₂) (hgf₁ hgf₂) :
    totalMap (fun n ↦ (g n).comp (f n)) hgf₁ hgf₂ =
      (totalMap g hg₁ hg₂).comp (totalMap f hf₁ hf₂) := by
  refine DirectSum.algHom_ext R A.piece fun n a ↦ ?_
  simp [totalMap_of]

end ExternallyGradedAlgebra

end
