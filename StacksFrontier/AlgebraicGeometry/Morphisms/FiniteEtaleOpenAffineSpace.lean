module

public import StacksFrontier.RingTheory.Etale.FiniteEtaleAffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# A variety minus a divisor is finite étale over an open of affine space

Let `A` be a domain of finite type and of Krull dimension `d` over a perfect field `k`. Then
there are nonzero `a ∈ A` and `f ∈ k[x₁, …, x_d]` and a finite étale morphism

`π : Spec A_a ⟶ Spec k[x₁, …, x_d]_f`

over `Spec k`, from the basic open `D(a)` of `Spec A` to the basic open `D(f)` of `𝔸^d_k`. This
is the scheme-theoretic form of `Stacks.GenericFiniteEtale.exists_finite_etale_away_mvPolynomial`
(separable Noether normalization followed by generic étaleness). For `d = 1` it is
`Stacks.GenericFiniteEtale.exists_finite_etale_specAway`.

## Main results

* `Stacks.GenericFiniteEtale.exists_finite_etale_specAway_mvPolynomial`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.GenericFiniteEtale

/-- **A variety minus a divisor is finite étale over an open of affine space.** For a domain `A`
of finite type and of Krull dimension `d` over a perfect field `k` there are nonzero `a ∈ A`,
`f ∈ k[x₁, …, x_d]` and a finite étale `π : Spec A_a ⟶ Spec k[x₁, …, x_d]_f` over `Spec k`. -/
theorem exists_finite_etale_specAway_mvPolynomial (k : Type u) [Field k] [PerfectField k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (d : ℕ)
    (hA : ringKrullDim A = d) :
    ∃ (a : A) (_ : a ≠ 0) (f : MvPolynomial (Fin d) k) (_ : f ≠ 0)
      (π : Spec (.of (Localization.Away a)) ⟶ Spec (.of (Localization.Away f))),
      IsFinite π ∧ Etale π ∧
      π ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away a))) := by
  obtain ⟨a, ha, f, hf, ψ, hfin, het, hk⟩ := exists_finite_etale_away_mvPolynomial k A d hA
  refine ⟨a, ha, f, hf, Spec.map (CommRingCat.ofHom ψ), ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).2 hfin
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).2 het
  · rw [← Spec.map_comp]
    congr 1
    ext x
    exact hk x

end Stacks.GenericFiniteEtale
