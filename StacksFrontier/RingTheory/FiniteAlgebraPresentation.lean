module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# A finite algebra presented by generators, structure constants and monic equations

A module-finite algebra `S` over a commutative ring `R` carries, non-canonically, the following
finite amount of data: a finite family `gen` of elements spanning `S` as an `R`-module,
coefficients expressing each product `gen l * gen l'` in that family, and for each member a
monic equation over `R`. `Stacks.FiniteAlgebraPresentation.Presentation` packages it, and
`Stacks.FiniteAlgebraPresentation.exists_presentation` produces one.

## Main definitions

* `Stacks.FiniteAlgebraPresentation.Presentation` is the data.
* `Stacks.FiniteAlgebraPresentation.Presentation.coeffFamily` is the finite family of
  coefficients occurring in it.

## Main results

* `Stacks.FiniteAlgebraPresentation.exists_presentation`: a module-finite algebra has one.
-/

@[expose] public section

universe u

namespace Stacks.FiniteAlgebraPresentation

/-- **Generators, structure constants and monic equations for a finite algebra.** A spanning
family `gen` for `S` as an `R`-module, coefficients `cst` expressing the products of its members
in it, and a monic equation of degree `deg l` with coefficients `coeff l` for each member. -/
structure Presentation (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  /-- The index type of the generating family. -/
  L : Type u
  /-- The generating family is finite. -/
  [fintypeL : Fintype L]
  /-- The generating family. -/
  gen : L → S
  /-- The generating family spans `S` as an `R`-module. -/
  spans : ∀ x : S, ∃ t : L → R, x = ∑ l, t l • gen l
  /-- The structure constants. -/
  cst : L → L → L → R
  /-- The structure constants express the products of the generators. -/
  cst_spec : ∀ l l' : L, gen l * gen l' = ∑ j, cst l l' j • gen j
  /-- The degree of the monic equation chosen for each generator. -/
  deg : L → ℕ
  /-- The coefficients of the monic equation chosen for each generator. -/
  coeff : ∀ l : L, Fin (deg l) → R
  /-- Each generator satisfies its monic equation. -/
  monic : ∀ l : L, gen l ^ deg l + ∑ i : Fin (deg l), coeff l i • gen l ^ (i : ℕ) = 0

attribute [instance] Presentation.fintypeL

/-- **A module-finite algebra admits a presentation.** -/
theorem exists_presentation (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] : Nonempty (Presentation R S) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := S)
  set gen : ULift.{u} (Fin n) → S := fun l => g l.down
  have hrange : Set.range gen = Set.range g :=
    Set.ext fun _ => ⟨fun ⟨l, hl⟩ => ⟨l.down, hl⟩, fun ⟨i, hi⟩ => ⟨⟨i⟩, hi⟩⟩
  have spans : ∀ x : S, ∃ t : ULift.{u} (Fin n) → R, x = ∑ l, t l • gen l := fun x => by
    have hx : x ∈ Submodule.span R (Set.range gen) := by rw [hrange, hg]; exact Submodule.mem_top
    obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx
    exact ⟨t, ht.symm⟩
  have integral : ∀ x : S, ∃ (d : ℕ) (c : Fin d → R),
      x ^ d + ∑ i : Fin d, c i • x ^ (i : ℕ) = 0 := fun x => by
    obtain ⟨p, hp, hpx⟩ := IsIntegral.of_finite R x
    refine ⟨p.natDegree, fun i => p.coeff i, ?_⟩
    rw [Fin.sum_univ_eq_sum_range fun i => p.coeff i • x ^ i]
    simp only [Algebra.smul_def]
    rw [hp.as_sum] at hpx
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C] using hpx
  choose cst cst_spec using fun l l' => spans (gen l * gen l')
  choose deg coeff monic using fun l => integral (gen l)
  exact ⟨{ L := ULift.{u} (Fin n), gen := gen, spans := spans, cst := cst, cst_spec := cst_spec,
           deg := deg, coeff := coeff, monic := monic }⟩

namespace Presentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (P : Presentation R S)

/-- The index type of the family of coefficients occurring in a presentation: the structure
constants and the coefficients of the monic equations. -/
abbrev CoeffIndex : Type u := (P.L × P.L × P.L) ⊕ (Σ l : P.L, Fin (P.deg l))

/-- The coefficient index type of a presentation is finite. -/
instance : Finite P.CoeffIndex := by
  have : ∀ l : P.L, Finite (Fin (P.deg l)) := fun _ => inferInstance
  exact inferInstance

/-- The finite family of coefficients occurring in a presentation. -/
def coeffFamily : P.CoeffIndex → R
  | .inl (l, l', j) => P.cst l l' j
  | .inr ⟨l, i⟩ => P.coeff l i

/-- On a structure-constant index, `coeffFamily` is the structure constant `P.cst l l' j`. -/
@[simp] lemma coeffFamily_inl (l l' j : P.L) :
    P.coeffFamily (.inl (l, l', j)) = P.cst l l' j := rfl

/-- On an equation index, `coeffFamily` is the coefficient `P.coeff l i`. -/
@[simp] lemma coeffFamily_inr (l : P.L) (i : Fin (P.deg l)) :
    P.coeffFamily (.inr ⟨l, i⟩) = P.coeff l i := rfl

end Presentation

end Stacks.FiniteAlgebraPresentation

end
