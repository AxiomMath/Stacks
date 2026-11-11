module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricCharacterFiniteness.Curve
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.NumberTheory.TraceFormula.ConstantCharpoly.FiniteImage
public import StacksFrontier.NumberTheory.TraceFormula.FrobeniusCharpoly

/-!
# Gaitsgory's theorem: finite geometric monodromy for `ℓ > 2n`

Let `k` be a finite field of characteristic `p`, `X` a smooth, geometrically irreducible,
projective curve over `k`, `ℓ ≠ p` a prime and `ρ : π₁(X) → GL_n(F_ℓ[[t]])` continuous. The
Conjecture of the section on automorphic forms and sheaves asserts that `ρ(π₁(X_k̄))` is finite.
Tag 03W0 says that it holds for `ℓ > 2n`, modulo some unproven things, citing Gaitsgory.

## The unproven input

Gaitsgory ("On de Jong's conjecture", Israel J. Math. 157 (2007)) constructs, for `ℓ > 2n`, a
Hecke eigensheaf with `F_ℓ((t))`-coefficients attached to `ρ`, using a theory of constructible and
perverse sheaves with such coefficients, its sheaf–function dictionary and an extension of the
geometric Satake equivalence, none of which is worked out in the literature. Through the
dictionary the eigensheaf gives an `F_ℓ((t))`-valued cuspidal Hecke eigenform whose Hecke
eigenvalues at a closed point `v` are the coefficients of the characteristic polynomial of
`ρ(Frob_v)`. The space of such cusp forms is the base change of a finite-dimensional
`F_ℓ`-vector space stable under the Hecke operators, so these eigenvalues are algebraic over
`F_ℓ` (de Jong, "A conjecture on arithmetic fundamental groups", Israel J. Math. 121 (2001)).
That is the input the deduction uses, and it is what this file states as a hypothesis:
`Stacks.TraceFormula.HasAlgebraicFrobeniusCharpoly` — at every Frobenius element of `π₁(X)`, the
coefficients of the characteristic polynomial of `ρ` are algebraic over `F_ℓ`. It is not the
conclusion in another form: a representation with infinite unipotent image, such as
`g ↦ [[1, a(g)], [0, 1]]`, has all its characteristic polynomials equal to `(T - 1)²`.

## The deduction

1. The coefficients are constant power series, `F_ℓ` being algebraically closed in `F_ℓ[[t]]`,
   and by Chebotarev density and continuity this holds for every element of `π₁(X)`
   (`Stacks.TraceFormula.charpoly_coeff_mem_range_C_of_frobenius`).
2. A continuous representation of a compact group into `GL_n(F_ℓ[[t]])` whose characteristic
   polynomials have constant coefficients, and on each of whose open subgroups there are finitely
   many continuous `F_ℓ`-characters, has finite image
   (`Stacks.TraceFormula.finite_range_of_charpoly_coeff_mem_range_C`): on the open subgroup of
   elements reducing to `1` modulo `t` the characteristic polynomial is forced to be `(T - 1)ⁿ`;
   over a finite extension of `F_ℓ((t))` that subgroup is block upper triangular with absolutely
   irreducible diagonal blocks, which Burnside's theorem and the trace form force to be the
   identity; the remaining unipotent part is finite level by level by the finiteness of
   characters, and a homomorphism of a compact group trivial on an open subgroup has finite image.
3. Open subgroups of `π₁(X_k̄)` have finitely many continuous `F_ℓ`-characters, by finiteness of
   `H¹` of smooth proper curves over `k̄` with `𝐙/ℓ`-coefficients
   (`AlgebraicGeometry.finite_continuous_monoidHom_multiplicative_zmod_of_isOpen`).

## Main definitions

* `Stacks.TraceFormula.HasAlgebraicFrobeniusCharpoly` — the input.

## Main results

* `Stacks.TraceFormula.finite_geometricMonodromy_of_hasAlgebraicFrobeniusCharpoly` — finiteness
  from algebraic Frobenius characteristic polynomials. Tag 03W0, from the automorphic form
  attached to `ρ`, is in `StacksFrontier.NumberTheory.TraceFormula.GaitsgoryAutomorphic`.

## References

* [Stacks Project, Tag 03W0](https://stacks.math.columbia.edu/tag/03W0)
* [Gaitsgory]
* [dJ-conjecture]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped PowerSeries.WithPiTopology

universe u

namespace Stacks.TraceFormula

/-- An integral scheme is connected; pinned, since the general search for `ConnectedSpace X` runs
out of heartbeats with the imports of this file. -/
local instance (priority := 3000) connectedSpace_of_isIntegral_scheme {X : Scheme.{u}}
    [IsIntegral X] : ConnectedSpace X :=
  inferInstance

/-- The geometric curve of a geometrically irreducible scheme is connected; pinned, since the
general search runs out of heartbeats with the imports of this file. -/
local instance (priority := 3000) connectedSpace_geometricBaseChange_of_isCurve
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyIrreducible f] : ConnectedSpace (geometricBaseChange k K f) :=
  have := geometricallyConnected_of_geometricallyIrreducible f
  connectedSpace_fieldBaseChange f K

variable {X : Scheme.{u}} {n ℓ : ℕ}

/-- The coefficients of the characteristic polynomials of Frobenius of a representation
`ρ : π₁(X) → GL_n(F_ℓ[[t]])` are algebraic: at every Frobenius element of `π₁(X)`, every
coefficient of the characteristic polynomial of `ρ` is algebraic over `F_ℓ`. When `ρ` has an
attached automorphic form (`Stacks.TraceFormula.HasCuspidalHeckeEigenforms`) these coefficients
are, up to an unramified twist, Hecke eigenvalues of cuspidal eigenforms, which are algebraic by
Harder's finiteness theorem (`Stacks.Adeles.GeneralLinear.exists_isAlgebraic_mul_pow`). -/
def HasAlgebraicFrobeniusCharpoly {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (base : GeometricPoint X)
    (ρ : EtaleFundamentalGroup X base →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ))) : Prop :=
  ∀ F ∈ frobeniusElements base Set.univ, ∀ i,
    IsAlgebraic (ZMod ℓ) ((ρ F : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i)

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f]

/-- **Finite geometric monodromy from algebraic Frobenius characteristic polynomials.** Let `k` be
a finite field of characteristic `p`, `X` a smooth, geometrically irreducible, projective curve
over `k`, `ℓ ≠ p` a prime with `2n < ℓ`, and `ρ : π₁(X) → GL_n(F_ℓ[[t]])` continuous. If the
coefficients of the characteristic polynomials of Frobenius are algebraic over `F_ℓ`, then the
geometric monodromy group `ρ(π₁(X_k̄))` is finite. Tag 03W0 itself, from the automorphic form
attached to `ρ`, is
`Stacks.TraceFormula.geometricMonodromyConjecture_of_gaitsgoryInput`. -/
theorem finite_geometricMonodromy_of_hasAlgebraicFrobeniusCharpoly [Finite k] [IsAlgClosure k K]
    [Smooth f] (p : ℕ) [CharP k p] [Fact ℓ.Prime]
    (x : GeometricPoint (geometricBaseChange k K f))
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (hproj : IsProjective f) (hℓp : ℓ ≠ p) (hn : 2 * n < ℓ)
    (hρ : 2 * n < ℓ → HasAlgebraicFrobeniusCharpoly f (x.map (geometricProjection k K f)) ρ) :
    Finite (geometricMonodromy k K f x ρ) := by
  have : IsProper f := hproj.isProper
  have hp : p.Prime := CharP.char_is_prime k p
  have hℓ : (ℓ : k) ≠ 0 := fun h => hℓp <| by
    have hdvd := (CharP.cast_eq_zero_iff k p ℓ).mp h
    exact ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp hdvd).symm
  have := compactSpace_etaleFundamentalGroup (geometricBaseChange k K f) x
  have hchar := charpoly_coeff_mem_range_C_of_frobenius f (x.map (geometricProjection k K f)) ρ
    fun F hF i => (hρ hn F hF i).isIntegral
  have hfin := finite_range_of_charpoly_coeff_mem_range_C (geometricRestriction k K f x ρ)
    (fun g i => hchar _ i)
    (fun V hV => finite_continuous_monoidHom_multiplicative_zmod_of_isOpen k K f hℓ x V hV)
  exact hfin.to_subtype

end Stacks.TraceFormula

end
