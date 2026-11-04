module

public import StacksFrontier.AlgebraicGeometry.Variety.Projective.QuotientTwistPresentation

/-!
# The cohomology of `ℱ(m)` and `𝒦(m)` for a quotient of `𝒪^{⊕ r}` with Hilbert polynomial `P`

Let `n ≥ 0`, `r ≥ 1` and `P ∈ ℚ[t]`. There is an integer `m ≥ 0`, depending only on `n`, `r` and
`P`, such that for every field `k` and every surjection `q : 𝒪^{⊕ r} ⟶ ℱ` of coherent modules on
`ℙⁿ_k` where `ℱ` has Hilbert polynomial `P`, with kernel `𝒦`:

* `𝒦(m)` and `ℱ(m)` have no cohomology in positive degrees;
* `dim_k H⁰(ℙⁿ_k, ℱ(m)) = P(m)`;
* `H⁰(q(m)) : H⁰(𝒪(m)^{⊕ r}) ⟶ H⁰(ℱ(m))` is surjective;
* `𝒦(m)` is globally generated.

These are the facts about the fibres of a flat family of such quotients that the proof of Stacks
0DPA uses. The integer `m` is chosen so that `𝒦` is `m`-regular (Stacks 08AG); then `𝒦(m)` has no
higher cohomology (Stacks 08A6) and is globally generated (Stacks 08A8). The vanishing for `ℱ(m)`
and the surjectivity follow from the long exact cohomology sequence of
`0 ⟶ 𝒦(m) ⟶ 𝒪(m)^{⊕ r} ⟶ ℱ(m) ⟶ 0`, since `𝒪(m)` has no higher cohomology for `m ≥ 0`.

## Main results

* `AlgebraicGeometry.exists_twist_cohomology_of_hilbertPolynomial`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
* [Stacks Project, Tag 08A6](https://stacks.math.columbia.edu/tag/08A6)
* [Stacks Project, Tag 08A8](https://stacks.math.columbia.edu/tag/08A8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] isCoherent_projectiveTwist

/-- **The cohomology of the twists of a quotient of `𝒪^{⊕ r}` with Hilbert polynomial `P`.**
There is `m ≥ 0`, depending only on `n`, `r` and `P`, such that for every field `k` and every
surjection `q : 𝒪^{⊕ r} ⟶ ℱ` onto a coherent module on `ℙⁿ_k` with Hilbert polynomial `P`, with
kernel `𝒦`: the twists `𝒦(m)` and `ℱ(m)` have no higher cohomology, `dim_k H⁰(ℱ(m)) = P(m)`,
`H⁰(q(m))` is surjective, and `𝒦(m)` is globally generated. -/
theorem exists_twist_cohomology_of_hilbertPolynomial (n r : ℕ) (hr : 1 ≤ r)
    (P : Polynomial ℚ) :
    ∃ m : ℕ, ∀ (k : Type u) [Field k]
      (Q : (projectiveSpaceOverRing n (.of k)).Modules) [Q.IsCoherent]
      (q : freeModules k n r ⟶ Q) [Epi q],
      (∀ d : ℤ, (hilbertPolynomial k n Q d : ℚ) = P.eval (d : ℚ)) →
      (∀ i : ℕ, 0 < i → IsZero (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n (kernel q) m) i)) ∧
      (∀ i : ℕ, 0 < i → IsZero (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n Q m) i)) ∧
      (Module.finrank k (cohomologyOverField k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (projectiveTwist n Q m) 0) : ℚ) =
        P.eval (m : ℚ) ∧
      Function.Surjective (cohomologyOverFieldMap k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) ((twistFunctorModules k n m).map q) 0) ∧
      SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n (kernel q) m) := by
  obtain ⟨m₀, hm₀⟩ := exists_isMRegular_kernel_free_of_hilbertPolynomial n r hr P
  refine ⟨m₀.toNat, fun k _ Q _ q _ hP => ?_⟩
  have hm : m₀ ≤ ((m₀.toNat : ℕ) : ℤ) := Int.self_le_toNat m₀
  set m : ℤ := ((m₀.toNat : ℕ) : ℤ)
  have hm0 : 0 ≤ m := Int.natCast_nonneg _
  let f := projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)
  have : (kernel q).IsCoherent := CoherentAbelian.isCoherent_kernel q
  have hreg : ∀ d : ℤ, m₀ ≤ d → IsMRegular k n (kernel q) d := fun d hd =>
    isMRegular_of_le k n (kernel q) (hm₀ k Q q hP) hd
  have hvanK : ∀ i : ℕ, 0 < i →
      IsZero (cohomologyOverField k f (projectiveTwist n (kernel q) m) i) := by
    intro i hi
    rw [isZero_cohomologyOverField_iff_isZero_hgroup]
    by_cases hin : i ≤ n
    · simpa only [add_sub_cancel_right] using hreg (m + i) (by omega) i hi hin
    · have : (kernel q).IsQuasicoherent := isQuasicoherent_of_isCoherent _
      exact Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt n (.of k) _ i (by omega)
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel (kernelIsKernel q) }
  let T := S.map (twistFunctorModules k n m)
  have hT : T.ShortExact := hS.map_of_exact _
  obtain ⟨δ, -, -, hgδ, -⟩ := exists_cohomologyOverField_longExactSequence k f hT
  have hvanFree : ∀ i : ℕ, 0 < i → IsZero (cohomologyOverField k f T.X₂ i) := fun i hi =>
    (isZero_cohomologyOverField_iff_isZero_hgroup k f _ i).mpr
      (isZero_Hgroup_projectiveTwist_freeModules k n r m hm0 i hi)
  have hsurj : ∀ i : ℕ, Function.Surjective (cohomologyOverFieldMap k f T.g i) := by
    intro i b
    have : Subsingleton (cohomologyOverField k f T.X₁ (i + 1)) :=
      ModuleCat.subsingleton_of_isZero (hvanK (i + 1) (Nat.succ_pos i))
    exact (hgδ i b).mp (Subsingleton.elim _ _)
  have hvanQ : ∀ i : ℕ, 0 < i →
      IsZero (cohomologyOverField k f (projectiveTwist n Q m) i) := by
    intro i hi
    have := ModuleCat.subsingleton_of_isZero (hvanFree i hi)
    have : Subsingleton (cohomologyOverField k f T.X₃ i) := (hsurj i).subsingleton
    exact ModuleCat.isZero_of_subsingleton (cohomologyOverField k f T.X₃ i)
  refine ⟨hvanK, hvanQ, ?_, hsurj 0, ?_⟩
  · have hPm : (hilbertPolynomial k n Q m : ℚ) = P.eval ((m₀.toNat : ℕ) : ℚ) := by
      rw [hP m]
      exact congrArg (fun x : ℚ => P.eval x) (Int.cast_natCast m₀.toNat)
    rw [← hPm]
    exact_mod_cast (hilbertPolynomial_eq_finrank_cohomologyOverField_zero k n Q m hvanQ).symm
  · exact isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_field k n (kernel q) m
      (hreg m hm)

end AlgebraicGeometry

end
