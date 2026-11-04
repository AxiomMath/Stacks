module

public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift

/-!
# Homomorphisms of differential graded algebras with a homotopy retraction

Let `ε : A → B` be a homomorphism of differential graded algebras over a commutative ring `R`. A
*homotopy retraction* of `ε` is an `R`-linear section `η : B → A` which preserves the grading and
commutes with the differentials, together with an `R`-linear operator `H` on `A` lowering the
degree by one, such that
$$\varepsilon \circ \eta = \mathrm{id}_B, \qquad
  \eta \circ \varepsilon - \mathrm{id}_A = \mathrm{d} \circ H + H \circ \mathrm{d}.$$
Such a homomorphism is a quasi-isomorphism of the underlying complexes of `R`-modules: a cocycle
of `B` lifts to a cocycle of `A` through the section, and a cocycle of `A` whose image is a
coboundary is itself one.

The section is only `R`-linear — it is not a homomorphism of algebras, and in the intended
application it is not `A`-linear either — so this is strictly weaker than an isomorphism in the
homotopy category of differential graded modules. It is, however, preserved by tensoring with a
differential graded algebra, which an isomorphism in the homotopy category of modules over the
coefficient algebra is not.

## Main definitions

* `DifferentialGradedAlgebra.HomotopyRetract`: the data of a homotopy retraction.

## Main results

* `DifferentialGradedAlgebra.HomotopyRetract.comp`: homotopy retractions compose.
* `DifferentialGradedAlgebra.HomotopyRetract.exists_cycle`: a cocycle of `B` of degree `n` is the
  image of a cocycle of `A` of degree `n`.
* `DifferentialGradedAlgebra.HomotopyRetract.exists_primitive`: a cocycle of `A` whose image in
  `B` is a coboundary is a coboundary.

## Implementation notes

The composite retraction has section `η ∘ η'` and homotopy `H + η ∘ H' ∘ ε`; the second summand is
a chain-homotopy conjugate, and the computation uses that the section commutes with the
differentials, which is why that is part of the data rather than derived.

## References

* [Stacks Project, Tag 061X](https://stacks.math.columbia.edu/tag/061X)
* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
-/

@[expose] public section

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra R}

/-- A homotopy retraction of a homomorphism `ε : A → B` of differential graded algebras: a
grading-preserving `R`-linear section commuting with the differentials, together with a homotopy
between the induced idempotent of `A` and the identity. -/
structure HomotopyRetract (ε : A.Hom B) where
  /-- The `R`-linear section of `ε`. -/
  sec : B.A →ₗ[R] A.A
  /-- The section preserves the grading. -/
  sec_mem : ∀ (n : ℤ) (b : B.A), b ∈ B.grading n → sec b ∈ A.grading n
  /-- The section commutes with the differentials. -/
  sec_d : ∀ b, sec (B.d b) = A.d (sec b)
  /-- The section is a right inverse of `ε`. -/
  hom_sec : ∀ b, ε.toAlgebraHom (sec b) = b
  /-- The homotopy operator of `A`. -/
  htp : A.A →ₗ[R] A.A
  /-- The homotopy operator lowers the degree by one. -/
  htp_mem : ∀ (n : ℤ) (a : A.A), a ∈ A.grading n → htp a ∈ A.grading (n - 1)
  /-- The homotopy identity. -/
  htp_eq : ∀ a, sec (ε.toAlgebraHom a) - a = A.d (htp a) + htp (A.d a)

namespace HomotopyRetract

variable {ε : A.Hom B} {φ : B.Hom C}

/-- Homotopy retractions compose. -/
def comp (σ : HomotopyRetract φ) (ρ : HomotopyRetract ε) :
    HomotopyRetract (φ.comp ε) where
  sec := ρ.sec ∘ₗ σ.sec
  sec_mem n c hc := ρ.sec_mem n _ (σ.sec_mem n c hc)
  sec_d c := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, σ.sec_d, ρ.sec_d]
  hom_sec c := by
    change φ.toAlgebraHom (ε.toAlgebraHom (ρ.sec (σ.sec c))) = c
    rw [ρ.hom_sec, σ.hom_sec]
  htp := ρ.htp + ρ.sec ∘ₗ σ.htp ∘ₗ ε.toAlgebraHom.toLinearMap
  htp_mem n a ha := by
    refine Submodule.add_mem _ (ρ.htp_mem n a ha) ?_
    exact ρ.sec_mem (n - 1) _ (σ.htp_mem n _ (ε.map_grading n a ha))
  htp_eq a := by
    have hb := σ.htp_eq (ε.toAlgebraHom a)
    have hεd : B.d (ε.toAlgebraHom a) = ε.toAlgebraHom (A.d a) := (ε.map_d a).symm
    rw [hεd] at hb
    have hsplit : σ.sec (φ.toAlgebraHom (ε.toAlgebraHom a)) =
        ε.toAlgebraHom a + (B.d (σ.htp (ε.toAlgebraHom a)) +
          σ.htp (ε.toAlgebraHom (A.d a))) := by
      rw [← hb]
      abel
    have hmain : ρ.sec (σ.sec (φ.toAlgebraHom (ε.toAlgebraHom a))) =
        ρ.sec (ε.toAlgebraHom a) + (A.d (ρ.sec (σ.htp (ε.toAlgebraHom a))) +
          ρ.sec (σ.htp (ε.toAlgebraHom (A.d a)))) := by
      rw [hsplit, map_add, map_add, ρ.sec_d]
    change ρ.sec (σ.sec (φ.toAlgebraHom (ε.toAlgebraHom a))) - a = _
    rw [hmain]
    have hρ := ρ.htp_eq a
    have hρ' : ρ.sec (ε.toAlgebraHom a) = a + (A.d (ρ.htp a) + ρ.htp (A.d a)) := by
      rw [← hρ]
      abel
    rw [hρ']
    change _ = A.d (ρ.htp a + ρ.sec (σ.htp (ε.toAlgebraHom a))) +
      (ρ.htp (A.d a) + ρ.sec (σ.htp (ε.toAlgebraHom (A.d a))))
    rw [map_add]
    abel

/-- The section of the composite homotopy retraction `σ.comp ρ` is the composite
`ρ.sec ∘ₗ σ.sec` of the sections. -/
@[simp] theorem comp_sec (σ : HomotopyRetract φ) (ρ : HomotopyRetract ε) :
    (σ.comp ρ).sec = ρ.sec ∘ₗ σ.sec := rfl

/-- An isomorphism of differential graded algebras is a homotopy retraction, with zero
homotopy. -/
def ofInverse (ε : A.Hom B) (ψ : B.Hom A)
    (hεψ : ∀ b, ε.toAlgebraHom (ψ.toAlgebraHom b) = b)
    (hψε : ∀ a, ψ.toAlgebraHom (ε.toAlgebraHom a) = a) :
    HomotopyRetract ε where
  sec := ψ.toAlgebraHom.toLinearMap
  sec_mem := ψ.map_grading
  sec_d b := ψ.map_d b
  hom_sec := hεψ
  htp := 0
  htp_mem _ _ _ := by
    rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _
  htp_eq a := by
    simp only [LinearMap.zero_apply, map_zero, add_zero]
    rw [show ψ.toAlgebraHom.toLinearMap (ε.toAlgebraHom a) =
      ψ.toAlgebraHom (ε.toAlgebraHom a) from rfl, hψε, sub_self]

/-- **A cocycle of `B` lifts to a cocycle of `A` of the same degree**, so `ε` is surjective on
cohomology. -/
theorem exists_cycle (ρ : HomotopyRetract ε) (n : ℤ) {b : B.A} (hb : b ∈ B.grading n)
    (hdb : B.d b = 0) :
    ∃ a : A.A, a ∈ A.grading n ∧ A.d a = 0 ∧ ε.toAlgebraHom a = b := by
  refine ⟨ρ.sec b, ρ.sec_mem n b hb, ?_, ρ.hom_sec b⟩
  rw [← ρ.sec_d, hdb, map_zero]

/-- **A cocycle of `A` whose image in `B` is a coboundary is a coboundary**, so `ε` is injective
on cohomology. -/
theorem exists_primitive (ρ : HomotopyRetract ε) (n : ℤ) {a : A.A} (ha : a ∈ A.grading n)
    (hda : A.d a = 0) {c : B.A} (hc : c ∈ B.grading (n - 1))
    (hdc : B.d c = ε.toAlgebraHom a) :
    ∃ w : A.A, w ∈ A.grading (n - 1) ∧ A.d w = a := by
  refine ⟨ρ.sec c - ρ.htp a, Submodule.sub_mem _ (ρ.sec_mem (n - 1) c hc)
    (ρ.htp_mem n a ha), ?_⟩
  have hkey := ρ.htp_eq a
  rw [hda, map_zero, add_zero] at hkey
  rw [map_sub, ← ρ.sec_d, hdc, ← hkey]
  abel

end HomotopyRetract

end DifferentialGradedAlgebra
