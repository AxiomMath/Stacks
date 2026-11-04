module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRealization
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.RingTheory.Koszul.CohomologicalDifferentialGradedAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# The two towers of Section 24.35 as sheaves of differential graded algebras

Let `f₁, …, f_r` be elements of a commutative ring `R` generating an ideal `I`. Section 24.35 of
the Stacks Project compares two sheaves of differential graded algebras on `ℕ` with the chaotic
topology and the constant sheaf of rings with value `R`: the sheaf `𝒜` of the inverse system of
quotients `R / (f₁ ^ n, …, f_r ^ n)`, and the sheaf `ℬ` of the inverse system of Koszul algebras
on `f₁ ^ n, …, f_r ^ n`. This file builds both, by realizing the two inverse systems with
`Stacks.ChaoticSite.systemAlgebra`.

## Main definitions

* `DifferentialGradedAlgebra.degreeZeroHom`: a homomorphism of `R`-algebras as a homomorphism of
  the differential graded algebras they define in degree zero.
* `Koszul.powAlgebraDiagram` and `Koszul.powQuotientAlgebraDiagram`: the Koszul tower and the
  quotient tower as inverse systems of differential graded algebras, indexed by `ℕᵒᵖ` with the
  stage `n` carrying the index `n + 1`.
* `Koszul.powSheafAlgebra` and `Koszul.powQuotientSheafAlgebra`: **the sheaves `ℬ` and `𝒜`.**
  Their base is the constant sheaf of rings, which by
  `Stacks.ChaoticSite.toRingCat_constCommRingSheaf` is on the nose the underlying sheaf of rings
  of the constant sheaf of commutative rings -- the form the quasi-coherence layer of Tag 0GZ9
  and the flat-resolution theory take their sheaf of rings in.

## References

* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- A homomorphism of `R`-algebras, read as a homomorphism of the differential graded algebras
they define in degree zero. -/
def degreeZeroHom {S S' : Type u} [Ring S] [Ring S'] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') : (degreeZero R S).Hom (degreeZero R S') where
  toAlgebraHom := φ
  map_grading n a ha := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [show (degreeZero R S').grading 0 = degreeZeroGrading R S' 0 from rfl,
        degreeZeroGrading_zero]
      exact Submodule.mem_top
    · rw [show (degreeZero R S).grading n = degreeZeroGrading R S n from rfl,
        degreeZeroGrading_eq_bot R S hn] at ha
      rw [show (degreeZero R S').grading n = degreeZeroGrading R S' n from rfl,
        degreeZeroGrading_eq_bot R S' hn]
      rw [Submodule.mem_bot] at ha ⊢
      rw [ha, map_zero]
  map_d a := map_zero φ

/-- The underlying algebra homomorphism of `degreeZeroHom φ` is `φ`. -/
@[simp]
theorem degreeZeroHom_toAlgebraHom {S S' : Type u} [Ring S] [Ring S'] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') : (degreeZeroHom φ).toAlgebraHom = φ := rfl

end DifferentialGradedAlgebra

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The Koszul differential graded algebras on the powers of `f`, as an inverse system indexed
by `ℕᵒᵖ` with the stage `n` carrying `K_{n + 1}`. -/
def powAlgebraDiagram (f : Fin r → R) : ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R where
  obj n := powAlgebra f (n.unop + 1)
  map {_ _} g := powTransition f (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_succ (leOfHom g.unop))
  map_id _ := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq
    (powTransition_self_toAlgebraHom f _)
  map_comp {_ _ _} _ _ := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq
    (powTransition_comp f _ _ _).symm

/-- **The Koszul tower on `f₁ ^ n, …, f_r ^ n` as a sheaf of differential graded algebras** over
the constant sheaf of rings with value `R` on `ℕ` with the chaotic topology. This is the sheaf
`ℬ` of Proposition 0GZK. -/
def powSheafAlgebra (f : Fin r → R) :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := ℕ) R) :=
  Stacks.ChaoticSite.systemAlgebra (powAlgebraDiagram f)

/-- The quotients `R / (f₁ ^ n, …, f_r ^ n)` in degree zero, as an inverse system of differential
graded algebras indexed by `ℕᵒᵖ` with the stage `n` carrying `R / (f₁ ^ (n+1), …, f_r ^ (n+1))`. -/
def powQuotientAlgebraDiagram (f : Fin r → R) : ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R where
  obj n := DifferentialGradedAlgebra.degreeZero R (R ⧸ powIdeal f (n.unop + 1))
  map {_ _} g := DifferentialGradedAlgebra.degreeZeroHom
    (Ideal.Quotient.factorₐ R (powIdeal_le f (Nat.succ_le_succ (leOfHom g.unop))))
  map_id _ := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq (by
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl)
  map_comp {_ _ _} _ _ := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq (by
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl)

/-- **The tower of quotients `R / (f₁ ^ n, …, f_r ^ n)` as a sheaf of differential graded
algebras** over the constant sheaf of rings with value `R` on `ℕ` with the chaotic topology.
This is the sheaf `𝒜` of Proposition 0GZK. -/
def powQuotientSheafAlgebra (f : Fin r → R) :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := ℕ) R) :=
  Stacks.ChaoticSite.systemAlgebra (powQuotientAlgebraDiagram f)

end Koszul

end
