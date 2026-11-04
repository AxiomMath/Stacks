module

public import StacksFrontier.FieldTheory.KaehlerDifferential.CartierEquality
public import StacksFrontier.FieldTheory.PBasisRank

/-!
# The degree of a field over the compositum of its `p`-th powers, for a smooth extension

Let `K / k` be a finitely generated extension of fields of characteristic `p` which is formally
smooth. Then the degree of `K` over the compositum `kKᵖ` of the base field with the `p`-th
powers is `p` raised to the transcendence degree.

Formal smoothness enters only through the vanishing of the first homology of the naive cotangent
complex, which by Cartier's equality makes the dimension of the module of Kähler differentials
equal to the transcendence degree. A `p`-basis is the same thing as a family whose differentials
form a basis, so a `p`-basis has exactly that many elements, and the degree over `kKᵖ` is `p`
raised to the number of elements of a `p`-basis.

## Main results

* `finrank_compositumFrobenius_eq_pow_trdeg` — the degree of `K` over `kKᵖ` is `p` raised to the
  transcendence degree of `K / k`.

## References

* [Stacks Project, Tag 07E1](https://stacks.math.columbia.edu/tag/07E1)
* [Stacks Project, Tag 07P2](https://stacks.math.columbia.edu/tag/07P2)
-/

@[expose] public noncomputable section

/-- For a formally smooth, essentially finitely generated extension of fields of characteristic
`p`, the degree of `K` over the compositum `kKᵖ` is `p` raised to the transcendence degree: the
differentials of a `p`-basis form a basis of `Ω_{K/k}`, whose dimension is the transcendence
degree because the cotangent homology vanishes. -/
theorem finrank_compositumFrobenius_eq_pow_trdeg
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] [Algebra.FormallySmooth k K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Module.finrank (compositumFrobenius k K p) K =
      p ^ Cardinal.toNat (Algebra.trdeg k K) := by
  classical
  have hH1 : Subsingleton (Algebra.H1Cotangent k K) :=
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent k K).mp inferInstance
  have hH1rank : Module.finrank K (Algebra.H1Cotangent k K) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hdimZ : (Cardinal.toNat (Algebra.trdeg k K) : ℤ) = (Module.finrank K Ω[K⁄k] : ℤ) := by
    have h := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k K
    rw [hH1rank] at h
    simpa using h.2.2
  have hdim : Cardinal.toNat (Algebra.trdeg k K) = Module.finrank K Ω[K⁄k] :=
    mod_cast hdimZ
  obtain ⟨S, hPB⟩ := exists_pBasis (k := k) (K := K) p
  have hdiff := (pBasis_iff_basis_differentials (k := k) (K := K) (Subtype.val : S → K) p).mp hPB
  let bdiff : Module.Basis S K Ω[K⁄k] := Module.Basis.mk hdiff.1 hdiff.2
  have hSfinite : S.Finite :=
    bdiff.finite_index_of_rank_lt_aleph0 (Module.rank_lt_aleph0 K Ω[K⁄k])
  let _ : Fintype S := hSfinite.fintype
  rw [hPB.finrank_compositumFrobenius, Nat.card_eq_fintype_card,
    (Module.finrank_eq_card_basis bdiff).symm, hdim]

end
