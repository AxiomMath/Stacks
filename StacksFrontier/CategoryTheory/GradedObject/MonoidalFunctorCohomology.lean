module

public import StacksFrontier.Algebra.GradedModule.ExternallyGradedAlgebraRing
public import StacksFrontier.CategoryTheory.GradedObject.MonObjAlgebra
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorDuality

/-!
# The cohomology algebra of a realization

Let `G : D ⥤ GradedObject ℤ (ModuleCat F)` be a braided monoidal functor into `ℤ`-graded
`F`-vector spaces with the Koszul symmetry of Stacks, Homology, Example 0FFX. For a commutative
monoid object `M` of `D`, the graded vector space `G(M)` is a commutative monoid object, hence
(`CategoryTheory.GradedObject.Monoidal.toExternallyGradedAlgebra`) its total space
`⨁ₙ G(M)ⁿ` is a graded commutative `F`-algebra, and a morphism of monoid objects induces a graded
algebra homomorphism. For `M = h(X)` the motive of a smooth projective scheme this is the
cohomology `H^*(X) = G(h(X))` with its cup product and pullbacks.

## Main definitions

* `CategoryTheory.Functor.cohomologyAlgebra`: the externally graded algebra `G(M)`.
* `CategoryTheory.Functor.cohomologyMap`: the algebra homomorphism induced by `f : M ⟶ N`.

## Main results

* `CategoryTheory.Functor.cohomologyAlgebra_mul_comm`: graded commutativity of the total algebra.
* `CategoryTheory.Functor.cohomologyMap_id`, `CategoryTheory.Functor.cohomologyMap_comp`:
  functoriality.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open MonoidalCategory GradedObject GradedObject.Monoidal DirectSum

universe w

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type w} [Field F]
  (G : D ⥤ GradedObject ℤ (ModuleCat.{w} F))

section Lax

variable [G.LaxMonoidal]

/-- **The graded algebra `G(M)`** of a monoid object `M`: pieces `G(M)ⁿ`, product induced by the
multiplication of `M` and the tensorator of `G`. -/
abbrev cohomologyAlgebra (M : D) [MonObj M] : ExternallyGradedAlgebra.{w, w} F :=
  letI := monObjObj (F := G) M
  toExternallyGradedAlgebra (G.obj M)

/-- The product of `G(M)` is `gradedMonMul`, induced by the multiplication of `M` and the
tensorator of `G`. -/
theorem cohomologyAlgebra_mul (M : D) [MonObj M] (i j : ℤ) (a : G.obj M i) (b : G.obj M j) :
    (G.cohomologyAlgebra M).mul i j a b = gradedMonMul G M i j (i + j) rfl a b :=
  rfl

/-- **The graded algebra homomorphism `G(f)`** induced by a morphism of monoid objects. -/
def cohomologyMap {M N : D} [MonObj M] [MonObj N] (f : M ⟶ N) [IsMonHom f] :
    (G.cohomologyAlgebra M).Total →ₐ[F] (G.cohomologyAlgebra N).Total :=
  letI := monObjObj (F := G) M
  letI := monObjObj (F := G) N
  haveI : IsMonHom (G.map f) := inferInstance
  ExternallyGradedAlgebra.totalMap (A := G.cohomologyAlgebra M) (B := G.cohomologyAlgebra N)
    (fun n ↦ (G.map f n).hom) (map_toExternallyGradedAlgebra_one (G.map f))
    (map_toExternallyGradedAlgebra_mul (G.map f))

/-- `G(f)` acts on the summand of degree `n` as `G(f)ⁿ`. -/
theorem cohomologyMap_of {M N : D} [MonObj M] [MonObj N] (f : M ⟶ N) [IsMonHom f] (n : ℤ)
    (a : (G.cohomologyAlgebra M).piece n) :
    G.cohomologyMap f (DirectSum.of (G.cohomologyAlgebra M).piece n a) =
      DirectSum.of (G.cohomologyAlgebra N).piece n (G.map f n a) := by
  unfold cohomologyMap
  exact ExternallyGradedAlgebra.totalMap_of _ _ _ n a

/-- `G(f)` preserves the grading. -/
theorem cohomologyMap_mem_grade {M N : D} [MonObj M] [MonObj N] (f : M ⟶ N) [IsMonHom f]
    (n : ℤ) {x : (G.cohomologyAlgebra M).Total} (hx : x ∈ (G.cohomologyAlgebra M).grade n) :
    G.cohomologyMap f x ∈ (G.cohomologyAlgebra N).grade n := by
  unfold cohomologyMap
  exact ExternallyGradedAlgebra.totalMap_mem_grade _ _ _ n hx

/-- Algebra homomorphisms out of the total algebra agreeing on all homogeneous summands are
equal. -/
private theorem total_algHom_ext {A : ExternallyGradedAlgebra.{w, w} F} {B : Type*} [Semiring B]
    [Algebra F B] {φ ψ : A.Total →ₐ[F] B}
    (h : ∀ (n : ℤ) (a : A.piece n), φ (DirectSum.of A.piece n a) = ψ (DirectSum.of A.piece n a)) :
    φ = ψ :=
  DirectSum.algHom_ext' F A.piece fun n ↦ LinearMap.ext fun a ↦ h n a

/-- `G(𝟙 M)` is the identity. -/
theorem cohomologyMap_id (M : D) [MonObj M] :
    G.cohomologyMap (𝟙 M) = AlgHom.id F (G.cohomologyAlgebra M).Total := by
  refine total_algHom_ext fun n a ↦ ?_
  rw [AlgHom.id_apply]
  exact (G.cohomologyMap_of (𝟙 M) n a).trans (by rw [G.map_id]; rfl)

/-- `G(f ≫ g) = G(g) ∘ G(f)`. -/
theorem cohomologyMap_comp {M N P : D} [MonObj M] [MonObj N] [MonObj P] (f : M ⟶ N)
    (g : N ⟶ P) [IsMonHom f] [IsMonHom g] :
    G.cohomologyMap (f ≫ g) = (G.cohomologyMap g).comp (G.cohomologyMap f) := by
  refine total_algHom_ext fun n a ↦ ?_
  rw [AlgHom.comp_apply]
  calc G.cohomologyMap (f ≫ g) (DirectSum.of (G.cohomologyAlgebra M).piece n a)
      = DirectSum.of (G.cohomologyAlgebra P).piece n (G.map (f ≫ g) n a) :=
        G.cohomologyMap_of _ n a
    _ = DirectSum.of (G.cohomologyAlgebra P).piece n (G.map g n (G.map f n a)) := by
        rw [G.map_comp]; rfl
    _ = G.cohomologyMap g (DirectSum.of (G.cohomologyAlgebra N).piece n (G.map f n a)) :=
        (G.cohomologyMap_of g n _).symm
    _ = G.cohomologyMap g (G.cohomologyMap f (DirectSum.of (G.cohomologyAlgebra M).piece n a)) :=
        by rw [G.cohomologyMap_of f n a]

end Lax

section Braided

variable [BraidedCategory D]
  [@Functor.Braided D _ _ _ (GradedObject ℤ (ModuleCat.{w} F)) _ _ koszulBraidedCategory G]

/-- **Graded commutativity**: `a b = (-1)^{ij} b a` in the total algebra of `G(M)`, for `a` of
degree `i` and `b` of degree `j`. -/
theorem cohomologyAlgebra_mul_comm (M : D) [MonObj M] [IsCommMonObj M] (i j : ℤ)
    (a b : (G.cohomologyAlgebra M).Total) (ha : a ∈ (G.cohomologyAlgebra M).grade i)
    (hb : b ∈ (G.cohomologyAlgebra M).grade j) :
    a * b = ((i * j).negOnePow : ℤ) • (b * a) := by
  let := monObjObj (F := G) M
  have := @Functor.isCommMonObj_obj _ _ _ _ _ _ _ koszulBraidedCategory G _ M _ _
  obtain ⟨a, rfl⟩ := ((G.cohomologyAlgebra M).mem_grade_iff _).1 ha
  obtain ⟨b, rfl⟩ := ((G.cohomologyAlgebra M).mem_grade_iff _).1 hb
  have hc := (toExternallyGradedAlgebra_isGradedCommutative (G.obj M)).graded_comm i j a b
  rw [ExternallyGradedAlgebra.of_mul_of, ExternallyGradedAlgebra.of_mul_of,
    DirectSum.of_eq_of_heq (add_comm i j) (hc.trans (ExternallyGraded.scalar_heq rfl rfl
      HEq.rfl)), ← Int.cast_smul_eq_zsmul F, DifferentialGraded.intCast_negOnePow,
    ExternallyGradedAlgebra.smul_of]

end Braided

end CategoryTheory.Functor

end
