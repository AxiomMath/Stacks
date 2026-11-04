module

public import StacksFrontier.RingTheory.Henselian.EtaleLifting

/-!
# Solutions of an étale system whose coefficients are read along a ring map

[Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX),
`bijOn_solutions_of_etale`, is stated for a system `P₁, …, P_n ∈ R[x₁, …, x_n]` whose
coefficients already live in the source ring `R` of the local homomorphism, and compares its
solutions in `R` with the solutions in `S` of the system obtained by applying `φ : R ⟶ S` to the
coefficients.

In the situation it is used in — step (4) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6) — the system is fixed once
and for all over a *third* ring `Γ` (the global functions of the base scheme), and the two
solution sets are the solutions of that one system read into `R` and into `S` by two ring
homomorphisms `ψ₁ : Γ ⟶ R` and `ψ₂ : Γ ⟶ S` with `ψ₂ = φ ∘ ψ₁`.  This file states 04GX in that
form, `bijOn_eval₂_solutions_of_etale`.

Two things make the reduction work.  The system over `R` is the coefficientwise image of the
system over `Γ`, so `MvPolynomial.eval_map` turns `MvPolynomial.eval₂Hom ψ₁` into
`MvPolynomial.eval` of the image system, and `MvPolynomial.map_map` with `ψ₂ = φ ∘ ψ₁` does the
same over `S`; the two solution sets are therefore the sets 04GX speaks of, not merely sets in
bijection with them.  And the étaleness hypothesis moves with the coefficients:
`etale_baseChange_presentation` carries étaleness of the presentation
`Γ[x]/(P)` over `Γ` to étaleness of `R[x]/(ψ₁P)` over `R`, which is what 04GX demands.

So the only hypotheses beyond those of 04GX are that the system is étale over `Γ` rather than
over `R`, which is where it is étale in the application.  No `@[stacks]` tag is registered: 04GX
is registered on `bijOn_solutions_of_etale`, and this is that statement with its coefficients
relabelled.

## Main results

* `bijOn_eval₂_solutions_of_etale`: **Stacks 04GX for a system whose coefficients are read along
  a ring map.**

## References

* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open MvPolynomial

/-- **Stacks 04GX for a system whose coefficients are read along a ring map.**

Let `φ : R → S` be a local homomorphism of strictly henselian local rings, let
`P₁, …, P_n ∈ Γ[x₁, …, x_n]` be a system of polynomials over a further commutative ring `Γ` such
that `Γ[x₁, …, x_n]/(P₁, …, P_n)` is étale over `Γ`, and let `ψ₁ : Γ → R` and `ψ₂ : Γ → S` read
the coefficients into `R` and into `S`, compatibly: `ψ₂ = φ ∘ ψ₁`.  Then the coordinatewise map
along `φ` is a bijection from the solutions of the system over `ψ₁` onto the solutions of the
same system over `ψ₂`.

This is `bijOn_solutions_of_etale` for the system `ψ₁(P)` over `R`: that system's solutions in
`R` are the solutions of `P` over `ψ₁` by `MvPolynomial.eval_map`, its coefficientwise image
along `φ` is `ψ₂(P)` by `MvPolynomial.map_map`, and its presentation over `R` is étale by
`etale_baseChange_presentation`. -/
theorem bijOn_eval₂_solutions_of_etale {Γ R S : Type*} [CommRing Γ] [CommRing R] [CommRing S]
    [HenselianLocalRing R] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField R)] [IsSepClosed (IsLocalRing.ResidueField S)]
    (ψ₁ : Γ →+* R) (φ : R →+* S) (hφ : IsLocalHom φ) (ψ₂ : Γ →+* S) (hψ : ψ₂ = φ.comp ψ₁)
    {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ)
    [Algebra.Etale Γ (MvPolynomial (Fin n) Γ ⧸ Ideal.span (Set.range P))] :
    Set.BijOn (fun a : Fin n → R => fun i => φ (a i))
      {a : Fin n → R | ∀ j, MvPolynomial.eval₂Hom ψ₁ a (P j) = 0}
      {b : Fin n → S | ∀ j, MvPolynomial.eval₂Hom ψ₂ b (P j) = 0} := by
  let : Algebra Γ R := ψ₁.toAlgebra
  have : Algebra.Etale R (MvPolynomial (Fin n) R ⧸
      Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap Γ R) (P i)))) :=
    etale_baseChange_presentation n P
  have h := bijOn_solutions_of_etale φ hφ n (fun i => MvPolynomial.map ψ₁ (P i))
  simpa only [MvPolynomial.map_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_map, ← hψ]
    using h

end
