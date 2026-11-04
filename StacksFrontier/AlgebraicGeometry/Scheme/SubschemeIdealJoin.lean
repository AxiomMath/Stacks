module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.KerCover
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Ideal sheaves of a closed subscheme, read in the ambient scheme

Let `K ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals and `V(K) = K.subscheme` the closed subscheme
it cuts out. An ideal sheaf `𝒦₀ ⊆ 𝒪_{V(K)}` has an **inverse image in `X`**: the ideal sheaf

  `𝒦₀.map K.subschemeι = (𝒦₀.subschemeι ≫ K.subschemeι).ker`,

Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.map`, which over an affine open `U` of `X` is
the preimage of `𝒦₀.ideal` under the surjection `Γ(X, U) ↠ Γ(X, U)/K.ideal U`. It therefore
*contains* `K`, and the family of these inverse images is exactly the family of ideal sheaves of
`X` above `K` — the **joins** `K ⊔ 𝒦₀`.

This file proves the order facts about that family which a Noetherian induction over the
quasi-coherent ideal sheaves of `X` needs when it replaces `X` by `V(K)`, as the dévissage of
[Stacks, Tag 088C] does before applying Chow's lemma. There are three.

* The inverse image lies **above `K`**, always: `Stacks.IdealSheafData.le_map_subschemeι`, so the
  inverse image *is* the join, `Stacks.IdealSheafData.sup_map_subschemeι`.
* It lies **strictly** above `K` exactly when `𝒦₀` does not vanish:
  `Stacks.IdealSheafData.lt_map_subschemeι_iff`. Both directions are elementary — `𝒦₀ = ⊥`
  pushes forward to `K` itself, and the pushforward is injective
  (`Stacks.IdealSheafData.eq_of_map_subschemeι_eq`) — and together they say that the strictness
  side condition of a Noetherian induction above `K` is, after the replacement, the
  **nonvanishing** of the ideal sheaf downstairs and nothing else.
* Nonvanishing of every power `𝒦₀ ᵉ⁺¹` is implied by the **support** of `𝒦₀` not being the whole
  of `V(K)`: `Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top`. This is where the
  geometric input of the dévissage enters, and it is the whole of what that input has to supply;
  see the discussion of density below.

## Main results

* `Stacks.IdealSheafData.le_map_subschemeι` — `K ≤ 𝒦₀.map K.subschemeι`.
* `Stacks.IdealSheafData.sup_map_subschemeι` — hence `K ⊔ 𝒦₀.map K.subschemeι = 𝒦₀.map
  K.subschemeι`: the inverse image is the join.
* `Stacks.IdealSheafData.map_subschemeι_eq_self_iff` — `𝒦₀.map K.subschemeι = K ↔ 𝒦₀ = ⊥`.
* `Stacks.IdealSheafData.lt_map_subschemeι_iff` — `K < 𝒦₀.map K.subschemeι ↔ 𝒦₀ ≠ ⊥`.
* `Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top` — an ideal sheaf whose support is not
  the whole scheme has no vanishing power.
* `Stacks.IdealSheafData.lt_map_subschemeι_pow_succ` — the two previous results combined: if the
  support of `𝒦₀` is not the whole of `V(K)` then every `K ⊔ 𝒦₀ ᵉ⁺¹` lies **strictly** above `K`.
* `Stacks.IdealSheafData.support_compl_ne_top_of_dense` — a dense open of a nonempty scheme has a
  complement which is not the whole space, and the vanishing ideal of that complement has that
  complement as its support.
* `Stacks.IdealSheafData.pow_map_le_map_pow` — the **power of an inverse image is below the
  inverse image of the power**, and not equal to it: the two families `(𝒦₀.map i) ᵉ⁺¹` and
  `(𝒦₀ ᵉ⁺¹).map i` are different, and it is the second that a Noetherian induction above `K`
  can consume.

## Implementation notes

**Where density and reducedness actually enter.** The source of [Stacks, Tag 088C] applies Chow's
lemma to `V(K)`, obtaining a modification which is an isomorphism over a dense open
`U ⊆ V(K)`, and takes for `𝒦₀` "the quasi-coherent sheaf of ideals cutting out the reduced
complement `V(K) \ U`", i.e. `𝒦₀ = vanishingIdeal (V(K) \ U)`. It then says only that "the powers
`𝒦₀ ᵉ` are all in `Ξ`", which by the preceding reduction means that they are all nonzero. That
step is elided, and unwinding it is what the three results above do. The outcome is narrower than
the source's language suggests:

* What is consumed is `𝒦₀.support ≠ ⊤`, nothing more. `Stacks.IdealSheafData.pow_succ_ne_bot_of_
  support_ne_top` holds for an **arbitrary** ideal sheaf, because `(𝒦₀ ᵉ⁺¹).support =
  𝒦₀.support` is `rfl` in Mathlib (`AlgebraicGeometry.Scheme.IdealSheafData.support_pow_succ`)
  and `(⊥).support = ⊤`.
* **Reducedness of the complement is a choice, not a hypothesis.** Any ideal sheaf whose support
  is `V(K) \ U` would do. Taking the *reduced* induced structure fixes which one: it is the
  largest, and it is the one whose support is `V(K) \ U` on the nose, which is
  `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support` read backwards —
  `((vanishingIdeal T).support : Set X) = T` by definition. Reducedness would be load-bearing if
  the nonvanishing had to be deduced from `𝒦₀ ≠ ⊥` instead, since
  `AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff` — the equivalence of `𝒦₀ ≠ ⊥` with
  `𝒦₀.support ≠ ⊤` — holds only on a reduced scheme, and `V(K)` is not reduced in the dévissage.
  It is not load-bearing, because the support statement is available directly.
* **Density of the Chow open is used only through its nonemptiness.** `𝒦₀.support = V(K) \ U` is
  the whole space exactly when `U` is empty, so what the dévissage needs of `U` is `U ≠ ∅`;
  density of `U` in a nonempty `V(K)` gives that and no more is used. Chow's lemma delivers
  density, so there is nothing to supply — but the implication is one-way, and
  `Stacks.IdealSheafData.support_compl_ne_top_of_dense` is stated at density only because that is
  the form the source and `AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification`
  provide.

**`𝒦₀.map i` versus `K ⊔ ‹a lift of 𝒦₀›`.** The two are the same thing: the inverse image is a
join by `sup_map_subschemeι`, and conversely every ideal sheaf above `K` is an inverse image,
since `(J.comap i).map i = J ⊔ i.ker` (`Stacks.IdealSheaf.map_comap_of_isClosedImmersion`) and
`i.ker = K`. The pushforward spelling is used throughout because it is the one Mathlib's Galois
connection `AlgebraicGeometry.Scheme.IdealSheafData.map_gc` is stated for, and because the
injectivity that gives strictness is stated for it.

`AlgebraicGeometry.Scheme.IdealSheafData` has no `pow_le_self`, so `𝒦₀ ᵉ⁺¹ ≤ 𝒦₀` goes through
`AlgebraicGeometry.Scheme.IdealSheafData.le_def` and `Ideal.pow_le_self` componentwise, which is
the repository's standing idiom for it.

**No Stacks tag attribute is attached to anything here.** These are order facts about Mathlib's
ideal-sheaf lattice, not statements of the source.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.IdealSheafData

variable {X : Scheme.{u}}

/-! ### The inverse image of an ideal sheaf of a closed subscheme -/

/-- Pushing the zero ideal sheaf of `V(K)` forward along `K.subschemeι` gives `K`. -/
private theorem map_bot_subschemeι (K : X.IdealSheafData) :
    (⊥ : K.subscheme.IdealSheafData).map K.subschemeι = K := by
  rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

/-- **The inverse image in `X` of an ideal sheaf of `V(K)` lies above `K`.** Pushing forward along
`K.subschemeι` is monotone and sends `⊥` to the kernel of `K.subschemeι`, which is `K`. -/
public theorem le_map_subschemeι (K : X.IdealSheafData) (L : K.subscheme.IdealSheafData) :
    K ≤ L.map K.subschemeι := by
  exact (map_bot_subschemeι K).symm.trans_le (Scheme.IdealSheafData.map_mono _ bot_le)

/-- **The inverse image is the join with `K`.** This is the sense in which the ideal sheaves at
which the dévissage of [Stacks, Tag 088C] consumes hypothesis (1) of [Stacks, Tag 088A] are the
joins `K ⊔ 𝒦₀`, as the source's replacement of `X` by `V(K)` produces them. -/
public theorem sup_map_subschemeι (K : X.IdealSheafData) (L : K.subscheme.IdealSheafData) :
    K ⊔ L.map K.subschemeι = L.map K.subschemeι :=
  sup_eq_right.mpr (le_map_subschemeι K L)

/-- **The inverse image is `K` itself exactly when the ideal sheaf downstairs vanishes.** The zero
ideal sheaf of `V(K)` pushes forward to `K`, and pushforward along `K.subschemeι` is injective
(`Stacks.IdealSheafData.eq_of_map_subschemeι_eq`). -/
public theorem map_subschemeι_eq_self_iff (K : X.IdealSheafData)
    (L : K.subscheme.IdealSheafData) :
    L.map K.subschemeι = K ↔ L = ⊥ := by
  exact ⟨fun h => eq_of_map_subschemeι_eq K (h.trans (map_bot_subschemeι K).symm),
    fun h => h ▸ map_bot_subschemeι K⟩

/-- **The inverse image lies strictly above `K` exactly when the ideal sheaf downstairs does not
vanish.**

This is the order fact the dévissage of [Stacks, Tag 088C] turns on. Its induction hypothesis is
available at ideal sheaves of `X` *strictly larger* than `K`, and after the source's replacement
of `X` by `V(K)` the ideal sheaves at which it is consumed are the inverse images of the powers
`𝒦₀ ᵉ⁺¹`. By this result the strictness obligation on them is exactly `𝒦₀ ᵉ⁺¹ ≠ ⊥` — a condition
on `V(K)`, which `Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top` then reduces to a
condition on the support of `𝒦₀`. Compare the obligation before the replacement, `K < 𝒦 ᵉ⁺¹` for
an ideal sheaf `𝒦` of `X`: powers descend, so that one forces `K < 𝒦` and places `K` strictly
below a descending chain, and at `K = ⊤` it cannot be met at all. -/
public theorem lt_map_subschemeι_iff (K : X.IdealSheafData) (L : K.subscheme.IdealSheafData) :
    K < L.map K.subschemeι ↔ L ≠ ⊥ := by
  rw [lt_iff_le_and_ne, ne_eq, ne_eq, eq_comm (a := K)]
  simp only [le_map_subschemeι K L, true_and]
  exact not_congr (map_subschemeι_eq_self_iff K L)

/-! ### Nonvanishing of the powers, from the support

That a positive power of an ideal sheaf is contained in it is **not** restated here: it is
`Stacks.IdealSheaf.pow_succ_le_self`
(`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/InfinitesimalNeighbourhood.lean`). -/

/-- **An ideal sheaf whose support is not the whole scheme has no vanishing power.** The support
of `I ᵉ⁺¹` is the support of `I`, and the support of the zero ideal sheaf is everything.

No reducedness is needed, and this is why reducedness of the complement is not load-bearing in
the dévissage of [Stacks, Tag 088C]: see the module docstring. On a reduced scheme the hypothesis
is equivalent to `I ≠ ⊥` by
`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff`, but `V(K)` is not reduced there. -/
public theorem pow_succ_ne_bot_of_support_ne_top {I : X.IdealSheafData}
    (hI : I.support ≠ ⊤) (e : ℕ) : I ^ (e + 1) ≠ ⊥ := fun h =>
  hI (by rw [← Scheme.IdealSheafData.support_pow_succ I e, h,
    Scheme.IdealSheafData.support_bot])

/-- **Every inverse image of a power lies strictly above `K`, from the support alone.** Combining
`Stacks.IdealSheafData.lt_map_subschemeι_iff` with
`Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top`: if the support of `𝒦₀` is not the whole
of `V(K)` then `K < K ⊔ 𝒦₀ ᵉ⁺¹` for every `e`.

**This is the replacement for the side condition `∀ e, K < 𝒦 ᵉ⁺¹` on an ideal sheaf `𝒦` of `X`,**
which is unsatisfiable. The replacement is satisfiable, and the dévissage satisfies it: Chow's
lemma applied to `V(K)` gives an open `U ⊆ V(K)` which is dense, hence nonempty when `V(K)` is,
and the vanishing ideal of its complement has that complement — a proper closed subset — as its
support. -/
public theorem lt_map_subschemeι_pow_succ (K : X.IdealSheafData)
    {L : K.subscheme.IdealSheafData} (hL : L.support ≠ ⊤) (e : ℕ) :
    K < (L ^ (e + 1)).map K.subschemeι :=
  (lt_map_subschemeι_iff K _).mpr (pow_succ_ne_bot_of_support_ne_top hL e)

/-- **The vanishing ideal of the complement of a dense open has a support which is not the whole
space.** The support of a vanishing ideal is the closed set it was formed from, by definition; and
the complement of a dense open of a nonempty space is not the whole space, since the complement is
everything only if the open is empty, whose closure is empty and not everything.

This is the geometric input of the dévissage's Chow step, in full: see the module docstring. -/
public theorem support_compl_ne_top_of_dense [Nonempty X] (U : X.Opens)
    (hU : Dense (U : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)).support ≠ ⊤ := by
  intro h
  obtain ⟨x, hx⟩ := hU.nonempty
  have hT : (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X) = ⊤ := h
  have hmem : x ∈ (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X) := by
    rw [hT]; trivial
  exact hmem hx

/-! ### The power of an inverse image is not the inverse image of the power -/

/-- **The power of an inverse image is below the inverse image of the power, and the two are
different ideal sheaves.** Over an affine open of `X` with `K.ideal = J` and `L.ideal = J'/J`, the
left side is `J' ᵉ` and the right side is `J' ᵉ + J`.

The two families are therefore genuinely distinct, which is the reason the side condition of the
dévissage cannot be repaired by taking powers of an ideal sheaf of `X`: the family a Noetherian
induction above `K` can consume is the right-hand one, the inverse images of the powers computed
in `V(K)`. -/
public theorem pow_map_le_map_pow (K : X.IdealSheafData) (L : K.subscheme.IdealSheafData)
    (n : ℕ) : (L.map K.subschemeι) ^ n ≤ (L ^ n).map K.subschemeι := by
  rw [Scheme.IdealSheafData.le_map_iff_comap_le, Stacks.IdealSheaf.comap_pow]
  exact pow_le_pow_left' (Scheme.IdealSheafData.comap_map_le L K.subschemeι) n

end Stacks.IdealSheafData

end
