module

public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsExt
public import StacksFrontier.AlgebraicGeometry.Size.SiteAlgebraClosure

/-!
# The pairs argument over the algebras of a big site

`AdequateFunctor.PairsDomainClosed` records the closure conditions under which the adjunction
`ψ_N ⊣ φ_N` between `A`-algebras and pairs `(C, V)` restricts to a domain of algebras and a domain
of pairs. This file supplies them for the algebras of a big site with cutoff `κ`, that is the
algebras `B` with `Spec B` below `κ` (the domain of `AdequateFunctor.siteAlgebraInclusion`),
together with the pairs `(C, V)` with `C` such an algebra and `#V < κ`, for every finitely
generated `A`-module `N`.

## Main definitions

* `AdequateFunctor.sitePairs` — the pairs `(C, V)` with `Spec C` below `κ` and `#V < κ`.

## Main results

* `AdequateFunctor.mk_lt_of_finite` — a finitely generated module over a ring of cardinality
  below an infinite `κ` has cardinality below `κ`.
* `AdequateFunctor.pairsDomainClosed_site` — the closure conditions for the site algebras and
  `AdequateFunctor.sitePairs`.

## References

* [Stacks Project, Tag 06ZG](https://stacks.math.columbia.edu/tag/06ZG)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Cardinal
open scoped TensorProduct

universe u

namespace AdequateFunctor

variable {A : Type u} [CommRing A]

/-- The pairs `(C, V)` admitted over a big site with cutoff `κ`: `Spec C` is below the cutoff and
the module `V` has cardinality below it. -/
public def sitePairs (κ : Cardinal.{u}) : ObjectProperty (AlgebraModulePair.{u} A) :=
  fun X ↦ schemeSizeBelow κ (Spec (CommRingCat.of X.algebra)) ∧ #X.module < κ

/-- A finitely generated module over a ring of cardinality below an infinite `κ` has cardinality
below `κ`. -/
public theorem mk_lt_of_finite {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hA : #A < κ)
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N] : #N < κ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
  refine (mk_le_of_surjective hf).trans_lt ?_
  rw [show #(Fin n → A) = #A ^ n by simp]
  rcases lt_or_ge #A ℵ₀ with h | h
  · exact (power_lt_aleph0 h natCast_lt_aleph0).trans hκ
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using one_lt_aleph0.trans hκ
    · exact (power_nat_le h).trans_lt hA

/-- **The pairs argument restricts to the algebras of a big site.** For a cutoff `κ` above `ℵ₀`
with `Spec A` below it and a finitely generated `A`-module `N`, the site algebras and
`AdequateFunctor.sitePairs` satisfy `AdequateFunctor.PairsDomainClosed`. -/
public theorem pairsDomainClosed_site {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hA : schemeSizeBelow κ (Spec (CommRingCat.of A)))
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N] :
    PairsDomainClosed.{u, u} N (algebraInSite A (schemeSizeBelow κ)) (sitePairs κ) where
  linearPair_mem D hD :=
    ⟨hD, mk_linearMap_lt_of_fg hκ ((schemeSizeBelow_spec_iff hκ D).1 hD)⟩
  symPairObj_mem X hX := by
    let := symPairAlgebra (A := A) X.algebra (X.module ⊗[A] N)
    exact schemeSizeBelow_spec_symmetricAlgebra hκ X.algebra (X.module ⊗[A] N) hX.1
      (mk_tensorProduct_le.trans_lt (max_lt hκ
        (max_lt hX.2 (mk_lt_of_finite hκ ((schemeSizeBelow_spec_iff hκ A).1 hA) N))))
  dualNumberPair_mem X hX := by
    refine ⟨schemeSizeBelow_spec_trivSqZeroExt hκ X.algebra X.algebra hX.1
      ((schemeSizeBelow_spec_iff hκ X.algebra).1 hX.1), ?_⟩
    show #(X.module × X.module) < κ
    rw [mk_prod, lift_id]
    exact mul_lt_of_lt hκ.le hX.2 hX.2

end AdequateFunctor

end
