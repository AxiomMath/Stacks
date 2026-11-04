module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Ring

/-!
# The algebra of the last step of the key formula, Stacks 0EQV

The proof of Stacks 0EQV computes the coefficient of both sides of the key formula at an
integral closed subspace `Y` of δ-dimension `n - 2` on an étale chart `(W, w)` of `X` at the
generic point of `Y`, with `A = 𝒪_{W, w}` a two-dimensional Noetherian local ring. The
contribution of the member `Z_i` of the family is a sum over the height-one primes `𝔮` of `A`
lying over the generic point of `Z_i`, and for each such `𝔮` the difference of the two
contributions is `-ord_{A/𝔮}(∂_{A_𝔮}(a, b))`, where `s = a e_ℒ` and `t = b e_𝒩` on the chart.
Summing over the family and using the Key Lemma (Stacks 0EAX) for `A` gives zero.

This file contains the two purely algebraic steps of that argument.

* `Stacks.Chow.keyFormula_perPrime_identity`: the identity at one height-one prime, from the
  comparison of the two tame symbols in a common extension
  (`Stacks.Chow.tameSymbol_hub_comparison`) and the readings of the three rational functions
  involved in the residue field.
* `Stacks.Chow.finsum_neg_finsum_subtype_eq_zero`: the regrouping of a finite sum over the
  height-one primes according to the (at most one) member of the family each prime lies over.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
-/

@[expose] public section

namespace Stacks.Chow

/-- **The identity of Stacks 0EQV at one height-one prime.** Let `ι : K → F` be a homomorphism
of fields and `ord` a homomorphism `Kˣ → ℤ` (written additively). Suppose that

* `x, y, z ∈ Kˣ` read in `F` as `l⁻¹`, `m⁻¹` and `d_B` respectively, and
* `d_B = ι(d_C) · m^{-o_a} · l^{o_b}` (the comparison of the two tame symbols).

Then `o_a · ord(y) - o_b · ord(x) - ord(z) = -ord(d_C)`.

In the application `K = κ(A_𝔮)`, `F` is the residue field of the étale local ring at a
geometric point over `𝔮`, `x` and `y` are the readings of the restricted generators
`(v s_ξ)|_Z` and `(w t_ξ)|_Z`, `z` the reading of `∂_B(f, g)`, `d_C = ∂_{A_𝔮}(a, b)` and
`o_a = ord_B(f)`, `o_b = ord_B(g)`. -/
theorem keyFormula_perPrime_identity {K F : Type*} [Field K] [Field F] (ι : K →+* F)
    (ord : Kˣ → ℤ) (hord : ∀ a b, ord (a * b) = ord a + ord b) (oa ob : ℤ) (x y z dC : Kˣ)
    (l m dB : Fˣ) (hx : Units.map ι.toMonoidHom x = l⁻¹) (hy : Units.map ι.toMonoidHom y = m⁻¹)
    (hz : Units.map ι.toMonoidHom z = dB)
    (hd : dB = Units.map ι.toMonoidHom dC * (m ^ oa)⁻¹ * l ^ ob) :
    oa * ord y - ob * ord x - ord z = -ord dC := by
  let φ : Kˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (ord a)) fun a b => by rw [hord, ofAdd_add]
  have hφ : ∀ a, ord a = Multiplicative.toAdd (φ a) := fun _ => rfl
  have hinj : Function.Injective (Units.map ι.toMonoidHom) := fun a b hab => by
    refine Units.ext (sub_eq_zero.mp ((map_eq_zero ι).mp ?_))
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Units.val hab)
  have hz' : z = dC * y ^ oa * (x ^ ob)⁻¹ := by
    refine hinj ?_
    rw [hz, hd, map_mul, map_mul, map_inv, map_zpow, map_zpow, hx, hy]
    simp only [inv_zpow, inv_inv]
  rw [hφ y, hφ x, hφ z, hφ dC, hz', φ.map_mul, φ.map_mul, φ.map_inv, φ.map_zpow, φ.map_zpow]
  simp only [toAdd_mul, toAdd_inv, toAdd_zpow, smul_eq_mul]
  ring

/-- **Regrouping a finite sum along an owner relation.** Let `T : Q → ℤ` have finite support and
total sum zero, and let `rel : I → Q → Prop` relate each `q` to at most one `i`, with `T q = 0`
whenever `q` is related to no `i`. If `c i = -∑_{rel i q} T q` for every `i`, then
`∑ᶠ i, c i = 0`.

In the application `Q` is the set of height-one primes of the local ring `A` of a chart at the
generic point of `Y`, `rel i 𝔮` says that `𝔮` lies over the generic point of `Z_i`, `T` is the
summand of the Key Lemma (Stacks 0EAX) and `c i` the difference of the coefficients at `Y` of the
`i`-th terms of the two sides of the key formula. -/
theorem finsum_neg_finsum_subtype_eq_zero {I Q : Type*} (rel : I → Q → Prop)
    (huniq : ∀ i j q, rel i q → rel j q → i = j) (T : Q → ℤ) (hT : (Function.support T).Finite)
    (hsum : ∑ᶠ q, T q = 0) (hT0 : ∀ q, (∀ i, ¬ rel i q) → T q = 0) (c : I → ℤ)
    (hc : ∀ i, c i = -∑ᶠ q : {q // rel i q}, T q) : ∑ᶠ i, c i = 0 := by
  classical
  let f : I × Q → ℤ := fun p => if rel p.1 p.2 then T p.2 else 0
  have hfin : (Function.support f).Finite := by
    rcases isEmpty_or_nonempty I with hI | hI
    · exact Set.toFinite _
    refine (hT.image fun q =>
      ((if h : ∃ i, rel i q then h.choose else Classical.arbitrary I), q)).subset ?_
    rintro ⟨i, q⟩ hiq
    simp only [Function.mem_support, f] at hiq
    by_cases hr : rel i q
    · rw [ite_eq_left hr] at hiq
      have hex : ∃ i, rel i q := ⟨i, hr⟩
      refine ⟨q, hiq, ?_⟩
      simp only [dite_eq_left hex, Prod.mk.injEq, and_true]
      exact huniq _ _ _ hex.choose_spec hr
    · simp [hr] at hiq
  have hfin' : (Function.support (f ∘ Prod.swap)).Finite := by
    rw [Function.support_comp_eq_preimage]
    exact hfin.preimage Prod.swap_injective.injOn
  have hrow : ∀ i, ∑ᶠ q, f (i, q) = ∑ᶠ q : {q // rel i q}, T q := by
    intro i
    rw [finsum_subtype_eq_finsum_cond]
    refine finsum_congr fun q => ?_
    simp only [f]
    rw [finsum_eq_if]
  have hcol : ∀ q, ∑ᶠ i, f (i, q) = T q := by
    intro q
    by_cases hex : ∃ i, rel i q
    · obtain ⟨i₀, hi₀⟩ := hex
      rw [finsum_eq_single _ i₀ fun j hj => ?_]
      · simp only [f, ite_eq_left hi₀]
      · simp only [f]
        rw [ite_eq_right fun hr => hj (huniq _ _ _ hr hi₀)]
    · have hex' : ∀ i, ¬ rel i q := fun i hi => hex ⟨i, hi⟩
      rw [hT0 q hex']
      exact finsum_eq_zero_of_forall_eq_zero fun i => by simp only [f, ite_eq_right (hex' i)]
  have h1 : ∑ᶠ i, ∑ᶠ q, f (i, q) = ∑ᶠ q, ∑ᶠ i, f (i, q) := by
    rw [← finsum_curry f hfin]
    exact (finsum_comp_equiv (Equiv.prodComm Q I)).symm.trans (finsum_curry _ hfin')
  calc ∑ᶠ i, c i = ∑ᶠ i, -∑ᶠ q, f (i, q) := finsum_congr fun i => by rw [hc, hrow]
    _ = -∑ᶠ i, ∑ᶠ q, f (i, q) := finsum_neg_distrib _
    _ = 0 := by rw [h1, finsum_congr hcol, hsum, neg_zero]

end Stacks.Chow

end
