module

public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.Locus
public import StacksCore.Tactic.StacksAttribute

/-!
# A criterion for a ring map to be unramified at a prime

Let `R → S` be of finite type and let `q` be a prime of `S` lying over the prime `p` of `R`. If
`p S_q` is the maximal ideal of `S_q` and `κ(q)/κ(p)` is finite separable, then `R → S` is
unramified at `q`: there is `g ∉ q` with `R → S_g` unramified. This is Lemma 02FM, the converse
of Lemma 00UW.

## Main results

* `Algebra.exists_unramified_away_of_map_eq_maximalIdeal`: Lemma 02FM.

## Implementation notes

*Unramified at a prime.* The source says that `R → S` is unramified at `q` if there is a `g ∉ q`
with `R → S_g` unramified (Definition 00UT (3)), and that is how the conclusion is written:
`∃ g ∉ q, Algebra.Unramified R (Localization.Away g)`. The proof passes through Mathlib's
`Algebra.IsUnramifiedAt R q`, the formal unramifiedness of `S_q` over `R`, which for an algebra of
finite type gives such a `g` (`Algebra.exists_unramified_of_isUnramifiedAt`).

*The map `κ(p) → κ(q)` is pinned.* The extension `κ(q)/κ(p)` of hypothesis (3) is the one
induced by `R_p → S_q`, whose algebra structure is a hypothesis together with
`Localization.AtPrime.IsLiesOverAlgebra p q`, which says that its algebra map is the localization
`Localization.localRingHom p q (algebraMap R S)` of the given map, as in Mathlib's
`Algebra.isUnramifiedAt_iff_map_eq`. Such a structure always exists
(`Localization.AtPrime.algebraOfLiesOver`), so this is no extra hypothesis on `R → S`.

*The proof.* The source reduces to the fibre over `p` through Lemma 00UV (8) and computes
`Ω_{S_q/κ(p)}` there. Here the two hypotheses are fed into the reverse direction of Mathlib's
`Algebra.isUnramifiedAt_iff_map_eq`, whose proof goes through the local criterion
`Algebra.FormallyUnramified.of_map_maximalIdeal` for `R_p → S_q` (the local-ring form of this
lemma, which Mathlib tags 02FM). The finiteness of `κ(q)/κ(p)` is a hypothesis of the source that
this route does not use: for an algebra essentially of finite type it follows from the other
hypotheses.

## References

* [Stacks 02FM](https://stacks.math.columbia.edu/tag/02FM), in the section
  "Unramified ring maps".
-/

@[expose] public section

namespace Algebra

/-- **Stacks 02FM.** Let `R → S` be of finite type and let `q` be a prime of `S` lying over the
prime `p` of `R`. If `p S_q` is the maximal ideal of `S_q` and `κ(q)/κ(p)` is finite separable,
then `R → S` is unramified at `q`: there is `g ∉ q` such that `R → S_g` is unramified. -/
@[stacks 02FM "Unramified at `q` is written as in Definition 00UT (3), as `R → S_g` unramified
for some `g ∉ q`, and `κ(q)/κ(p)` is the extension induced by `R_p → S_q`."]
theorem exists_unramified_away_of_map_eq_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (hmax : p.map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (_hfin : Module.Finite p.ResidueField q.ResidueField)
    (hsep : Algebra.IsSeparable p.ResidueField q.ResidueField) :
    ∃ g ∉ q, Algebra.Unramified R (Localization.Away g) := by
  have : IsUnramifiedAt R q := (isUnramifiedAt_iff_map_eq R p q).mpr ⟨hsep, hmax⟩
  exact exists_unramified_of_isUnramifiedAt q

end Algebra
