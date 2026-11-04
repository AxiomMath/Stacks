module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Unramified.Basic
public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.Unramified.QuasiFinite

/-!
# Local structure of unramified ring maps

* `Algebra.exists_hasStandardEtaleSurjectionOn_of_exists_unramified` (Stacks 0395): an unramified
  ring map is Zariski locally a quotient of a standard étale one.
* `Algebra.exists_etale_completeOrthogonalIdempotents_surjective_not_liesOver` (Stacks 00UY): the
  points of a fibre of an unramified ring map are separated by an étale neighbourhood.
* `exists_isIdempotentElem_isLocalization_away_of_unramified` (Stacks 02FL): an unramified ring
  map is a localization of `S ⊗[R] S` at an idempotent.
-/

@[expose] public section

universe u v

/-!
## An unramified ring map is Zariski locally a quotient of a standard étale one

Let `R → S` be a ring map and let `q ⊂ S` be a prime. Recall (Definition 00UT) that `R → S` is
*unramified* when it is of finite type with `Ω_{S/R} = 0`, that it is *unramified at `q`* when
there is a `g ∈ S`, `g ∉ q`, with `R → S_g` unramified, and (Definition 00UB) that `R → R[x]_g/(f)`
is *standard étale* when `f` is monic and `f'` is invertible in `R[x]_g/(f)`. This proposition says
that an unramified ring map is, Zariski locally on `Spec(S)`, a *quotient* of a standard étale one:
if `R → S` is unramified at `q`, then for some `g ∈ S`, `g ∉ q`, there are a standard étale
`R → S'` and a surjective `R`-algebra map `S' → S_g`. Geometrically, an unramified morphism is
locally the composition of a closed immersion and an étale morphism.

This is the unramified analogue of Proposition 00UE, and the source's proof is the "same": an
isomorphism `S_g ≅ R[x]_{g'}/(f)` is weakened to a surjection `R[x]_{g'}/(f) → S_g`, which is what
lets the statement cover the maps that are unramified but not étale — the closed immersions
`R → R/I`, for which the surjection cannot be an isomorphism because `R → R/I` is not flat.

The source's proof. Step 1 replaces `S` by an `S_g` unramified over `R`. Step 2 descends to a
Noetherian `R`, writing `S` as a quotient of a base change of an unramified `R₀ → S₀` with `R₀` of
finite type over `ℤ` (Lemma 00UV). Step 3 applies Zariski's main theorem (Lemma 00QB) to the map
`R → S`, quasi-finite by Lemma 02UR, to replace `S` by a finite `R`-algebra agreeing with it near
`q`. Steps 4–6 work in the fibre ring `S ⊗_R κ(p)`, a finite `κ(p)`-algebra, hence a finite product
of local rings (Lemmas 00J6, 00KJ) one factor of which is `κ(q)` (Lemma 00UW); a generator `α` of
the separable extension `κ(q)/κ(p)` is lifted to a `t ∈ S`, and Nakayama (Lemma 00DV) identifies
`S_q` with the localization of `S' = R[x]/I`, `x ↦ t`. Steps 7–10 produce a monic `f ∈ I` whose
image in `κ(p)[x]` factors as `h₁ w` with `h₁` the separable minimal polynomial of `α` and `w`
prime to `h₁`, so that `g = f'` does not vanish at `q`. Step 11 concludes: `R[x]_g/(f)` is
standard étale and `(R[x]/(f))_g → S_{φ(g)}` is the desired surjection.

### Main results

* `Algebra.exists_hasStandardEtaleSurjectionOn_of_exists_unramified`: Proposition 0395.

### Implementation notes

The three items of the conclusion are Mathlib's `HasStandardEtaleSurjectionOn R g`, which unfolds
(by `Iff.rfl`, checked in Lean) to `∃ (P : StandardEtalePair R) (φ : P.Ring →ₐ[R]
Localization.Away g), Function.Surjective φ`: item (1) is the bound `g : S`, item (2) is the
standard étale `R`-algebra `P.Ring = R[x][y]/(f, yg - 1)` of a pair `f g : R[X]` with `f` monic and
`f'` invertible away from `g`, and item (3) is `φ`. Quantifying over `StandardEtalePair R` rather
than over an abstract `S'` with `Algebra.IsStandardEtale R S'` loses nothing: by definition of that
class an `S'` standard étale over `R` *is* `R`-isomorphic to some `P.Ring`, and precomposing `φ`
with the isomorphism translates between the two forms (this is Mathlib's
`HasStandardEtaleSurjectionOn.mk`). It also keeps the statement free of a universe-quantified
existential over types.

The hypothesis is Definition 00UT (3) transcribed literally, `∃ g ∉ Q, Algebra.Unramified R S_g`,
the spelling of that condition in Tag 00UT, and it is deliberately *not* Mathlib's hypothesis
pair `[Algebra.FiniteType R S] [Algebra.IsUnramifiedAt R Q]`. The latter implies it, by
`Algebra.exists_unramified_of_isUnramifiedAt`, so this statement is strictly more general than
Mathlib's `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn` and implies it; the converse
fails, since finite type of `S` itself is not implied: for `R` a domain and `T` an `R`-algebra that
is not of finite type, `S = R × T` with the prime `Q = ⊥ × ⊤` (so `S ⧸ Q ≅ R`) and `g = (1, 0)` has
`S_g ≅ R`, unramified over `R`, while `S` is not of finite type over `R`. The
hypothesis does imply `Algebra.IsUnramifiedAt R Q` alone (checked in Lean, via
`Algebra.basicOpen_subset_unramifiedLocus_iff`), which is Mathlib's `Algebra.FormallyUnramified R
S_Q` and carries no finiteness at all. Both directions matter here: the source states no finiteness
hypothesis on `S`, only unramifiedness of a localization, and the proof needs none — Step 1 begins
by replacing `S` by that localization.

`S_g` is `Localization.Away g`, as in the statement of Tag 00UE and both Mathlib siblings. Its `R`-algebra
structure is the composite `R → S → S_g`, since `IsScalarTower R S (Localization.Away g)` is an
instance. Naming any other model of the localization gives an equivalent statement, by
`Algebra.Unramified.of_equiv` on the hypothesis and `HasStandardEtaleSurjectionOn.mk` on the
conclusion.

Faithfulness to [StacksProject 0395]:

1. No hypothesis is dead — unramifiedness at `q` is *necessary*, not merely sufficient. A quotient
   of a standard étale algebra is unramified: standard étale gives `Algebra.Etale R P.Ring`, and a
   surjection preserves both formal unramifiedness (`Algebra.FormallyUnramified.of_surjective`) and
   finite type (`Algebra.FiniteType.of_surjective`), so `HasStandardEtaleSurjectionOn R g` returns
   `Algebra.Unramified R (Localization.Away g)` for the very same `g`; checked in Lean. Hence no
   weakening of the hypothesis supports the conclusion, and the proposition is in fact an
   equivalence of the two localized conditions. Primality of `Q` is the source's and is used
   essentially: Steps 4–6 pass to the fibre over `p = Q ∩ R` and choose a generator of the
   separable field extension `κ(Q)/κ(p)`, which needs `κ(Q)` to be a field.
2. The scalars and the base are the source's. Unramifiedness of the hypothesis, the standard étale
   algebra `P.Ring` and the `R`-algebra map `φ` are all over `R` itself — not over `S`, not over
   `S_Q`, and not over a localization of `R`; `g` ranges over `S`, not over a localization of it,
   and `Q` is an ideal of `S`.
3. Where the source names a canonical map it is pinned. `S_g` is `Localization.Away g` with its
   canonical map from `S`, so "`S' → S_g`" is a map to that ring and not to an abstract algebra
   asserted to exist, and the `R`-algebra structures on both sides are the canonical ones recorded
   above. The map `φ` of item (3) is required to be a homomorphism of `R`-algebras and to be
   surjective, exactly the two conditions the source imposes on it; the source imposes no
   compatibility beyond `R`-linearity, and none is imposed here. Only `g`, `P` and `φ` are
   existentially quantified, as in the source.
4. The instantiation is not degenerate. Every closed immersion satisfies the hypothesis: for any
   ideal `I ⊆ R` and any prime `Q` of `R ⧸ I` it holds with `g = 1`, since `R → R ⧸ I` is of finite
   type and formally unramified (checked in Lean). Taking `R = ℚ[x]` and `I = (x)` gives
   `S = ℚ`, unramified over `ℚ[x]` and not étale, `ℚ[x] → ℚ` not being flat; the conclusion holds
   there with `S' = ℚ[x]` itself, and the surjection `S' → S_g` is not injective. So the statement
   is satisfied well away from the étale case of Proposition 00UE, and it is not vacuous in the
   other direction either: `g ∉ Q` with `Q` prime forces `S_g ≠ 0`, so item (3) asserts a genuine
   surjection onto a nonzero ring.

### References

* [StacksProject 0395](https://stacks.math.columbia.edu/tag/0395), Proposition 10.152.1, in
  Section 10.152 "Local structure of unramified ring maps" (Section 0G1D).
* [StacksProject 00UT](https://stacks.math.columbia.edu/tag/00UT), unramified and unramified at a
  prime.
* [StacksProject 00UB](https://stacks.math.columbia.edu/tag/00UB), standard étale.
* [StacksProject 00UE](https://stacks.math.columbia.edu/tag/00UE), the étale analogue, whose proof
  this one follows.

### Tags

unramified, standard étale, closed immersion, étale locally, localization, Zariski's main theorem
-/

/-!
## The proof of Stacks 0395

Let `R → S` be a ring map and `q ⊂ S` a prime, and suppose `R → S` is unramified at `q`, that is,
`R → S_g` is unramified for some `g ∈ S`, `g ∉ q`. Then there are a `g ∈ S`, `g ∉ q`, a standard
étale ring map `R → S'` and a surjective `R`-algebra map `S' → S_g`. This is Stacks 0395.

The proof given here is the source's Step 1 — replace `S` by the localization `S_s` that is
unramified over `R` — followed by an appeal to the same statement for an algebra unramified at
every prime, which is Mathlib's `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`; that
lemma is the source's Steps 2–11 (descent to a Noetherian base, Zariski's main theorem, the
computation in the fibre `S ⊗_R κ(p)`, Nakayama, and the construction of a monic `f ∈ I` with
`f'(t) ∉ q`).

Step 1 is the assertion that the conclusion *descends along a localization*: if `S_s` carries a
standard étale surjection at some element outside `q S_s`, then `S` carries one at some element
outside `q`. Both changes of ring it involves are governed by the single fact that the powers of
`s` avoid the prime `q`. In the direction `S → S_s` this makes `q S_s` prime, and in the direction
back it makes a fraction `a/s^n` avoid `q S_s` exactly when its numerator `a` avoids `q`; the
element of `S` produced from such a fraction is `s · a`, because `(S_s)_{a/s^n} = S_{s a}`.

### Implementation notes

The hypothesis is Definition 00UT (3) verbatim, `∃ g ∉ Q, Algebra.Unramified R (Localization.Away
g)`, and not Mathlib's hypothesis pair `[Algebra.FiniteType R S] [Algebra.IsUnramifiedAt R Q]`; see
the docstring of the statement for why that is strictly more general. Consequently the reduction to a
localization cannot be delegated to Mathlib's own reduction to the unramified case: the appeal is
to `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn` for the *localization* `S_s`, which
is unramified over `R` at each of its primes by `Algebra.unramified_iff_forall`, and finiteness
enters only there.

Step 1 is isolated as `exists_notMem_hasStandardEtaleSurjectionOn_of_isLocalizationAway`, stated
for an arbitrary `A` with `IsLocalization.Away s A` rather than for `Localization.Away s`, and its
two halves are the two lemmas above it: the numerator criterion
`mk'_mem_map_algebraMap_iff_of_isPrime`, which sharpens `IsLocalization.mk'_mem_map_algebraMap_iff`
by removing the existential over denominators, and `hasStandardEtaleSurjectionOn_mul_of_mk'`, which
carries out `(S_s)_{a/s^n} = S_{s a}` via `HasStandardEtaleSurjectionOn.of_dvd` and
`HasStandardEtaleSurjectionOn.mk`. The shared fact that the powers of `s` avoid `Q` is Mathlib's
`Ideal.disjoint_powers_iff_notMem_of_isPrime`.

### References

* [StacksProject 0395](https://stacks.math.columbia.edu/tag/0395), Proposition 10.152.1.
* [StacksProject 00UT](https://stacks.math.columbia.edu/tag/00UT), unramified at a prime.
-/

@[expose] public section


section Away

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] {s : S}
  [IsLocalization.Away s A] (Q : Ideal S) [Q.IsPrime] (hs : s ∉ Q)

include hs

/-- The image of a prime `Q` of `S` in a localization `S_s` at an element `s ∉ Q` is again prime,
the powers of `s` being disjoint from `Q`. -/
private lemma isPrime_map_algebraMap_of_notMem : (Q.map (algebraMap S A)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (.powers s) _ _ ‹_›
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs)

/-- A prime `Q` of `S` is recovered from its image in a localization `S_s` at an `s ∉ Q`. -/
private lemma under_map_algebraMap_of_notMem : Ideal.under S (Q.map (algebraMap S A)) = Q :=
  IsLocalization.under_map_of_isPrime_disjoint (.powers s) _ ‹_›
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs)

/-- A fraction `x / sⁿ` of a localization `S_s` lies in `Q S_s` exactly when its numerator lies in
`Q`, provided `Q` is prime and `s ∉ Q`. This sharpens `IsLocalization.mk'_mem_map_algebraMap_iff`,
whose right-hand side quantifies over denominators. -/
private lemma mk'_mem_map_algebraMap_iff_of_isPrime (x : S) (t : Submonoid.powers s) :
    IsLocalization.mk' A x t ∈ Q.map (algebraMap S A) ↔ x ∈ Q := by
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  refine ⟨fun ⟨u, hu, h⟩ ↦ (Ideal.IsPrime.mul_mem_left_iff ?_).mp h,
    fun h ↦ ⟨1, one_mem _, by simpa⟩⟩
  exact Set.disjoint_left.mp ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs) hu

end Away

section Descent

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [Algebra S A] [IsScalarTower R S A] {s : S} [IsLocalization.Away s A]

/-- A standard étale surjection over a localization `S_s`, at a fraction `f / sⁿ`, is one over `S`
at `s * f`: the fraction divides the image of `f`, and `(S_s)_f = S_{s f}`. -/
private lemma hasStandardEtaleSurjectionOn_mul_of_mk' (f : S) (t : Submonoid.powers s)
    (H : HasStandardEtaleSurjectionOn R (IsLocalization.mk' A f t)) :
    HasStandardEtaleSurjectionOn R (s * f) := by
  obtain ⟨P, φ, hφ⟩ := H.of_dvd (g := algebraMap S A f) ⟨algebraMap _ _ t.1, by simp⟩
  exact .mk _ hφ

/-- **Step 1 of Stacks 0395.** The conclusion of the proposition descends along a localization: if
a localization `S_s` at an `s` outside the prime `Q` admits a standard étale surjection at some
element outside `Q S_s`, then `S` admits one at some element outside `Q`. -/
private lemma exists_notMem_hasStandardEtaleSurjectionOn_of_isLocalizationAway (Q : Ideal S)
    [Q.IsPrime] (hs : s ∉ Q)
    (H : ∃ x ∉ Q.map (algebraMap S A), HasStandardEtaleSurjectionOn R x) :
    ∃ g ∉ Q, HasStandardEtaleSurjectionOn R g := by
  obtain ⟨x, hx, H⟩ := H
  obtain ⟨f, t, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
  exact ⟨s * f, ‹Q.IsPrime›.mul_notMem hs
    (mt (mk'_mem_map_algebraMap_iff_of_isPrime Q hs f t).mpr hx),
    hasStandardEtaleSurjectionOn_mul_of_mk' f t H⟩

end Descent


/-- **Stacks 0395.** Let `R → S` be a ring map and `q ⊂ S` a prime. If `R → S` is unramified at
`q` — that is, if `R → S_g` is unramified for some `g ∈ S`, `g ∉ q` — then there are a `g ∈ S`,
`g ∉ q`, a standard étale ring map `R → S'` and a surjective `R`-algebra map `S' → S_g`. -/
@[stacks 0395 "The conclusion's three items are Mathlib's `HasStandardEtaleSurjectionOn R g`,
namely `∃ (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] Localization.Away g), Surjective φ`. The
hypothesis \"unramified at `q`\" is Definition 00UT (3) verbatim,
`∃ g ∉ Q, Algebra.Unramified R (Localization.Away g)`, rather than Mathlib's hypothesis pair
`[Algebra.FiniteType R S] [Algebra.IsUnramifiedAt R Q]`, which implies it but is not implied by it;
so this is strictly more general than Mathlib's
`Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn` and implies it. See the module
docstring."]
public theorem Algebra.exists_hasStandardEtaleSurjectionOn_of_exists_unramified {R : Type u}
    {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (Q : Ideal S) [Q.IsPrime]
    (hQ : ∃ g ∉ Q, Algebra.Unramified R (Localization.Away g)) :
    ∃ g ∉ Q, HasStandardEtaleSurjectionOn R g := by
  obtain ⟨s, hsQ, hs⟩ := hQ
  -- `S_s` is unramified over `R`, hence unramified at the prime `Q S_s`.
  have : (Q.map (algebraMap S (Localization.Away s))).IsPrime :=
    isPrime_map_algebraMap_of_notMem Q hsQ
  have : Algebra.IsUnramifiedAt R (Q.map (algebraMap S (Localization.Away s))) :=
    (Algebra.unramified_iff_forall (R := R) (A := Localization.Away s)).mp hs ⟨_, ‹_›⟩
  -- Steps 2–11 apply to `S_s`, and Step 1 brings their conclusion back down to `S`.
  exact exists_notMem_hasStandardEtaleSurjectionOn_of_isLocalizationAway
    (A := Localization.Away s) Q hsQ
    (Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn _)


end


/-!
## Separating the points of a fibre of an unramified ring map by an étale neighbourhood

Let `R → S` be an unramified ring map — of finite type with `Ω_{S/R} = 0` — and let `p` be a
prime of `R`. The fibre `κ(p) ⊗[R] S` is unramified over the field `κ(p)`, hence a finite product
of finite separable field extensions of `κ(p)` (Tags 00UV and 00U3); after passing to an étale
neighbourhood `(R', p')` of `p` those extensions become trivial and each point of the fibre
splits off as a factor of the base change which is a *quotient* of `R'`:
`R' ⊗[R] S = A₁ × ⋯ × Aₙ × B`, with `R' → Aᵢ` surjective, `p'Aᵢ` a prime of `Aᵢ` lying over `p'`,
and `B` with no prime lying over `p'` at all. So the fibre of `Spec (R' ⊗[R] S) → Spec R'` over
`p'` is `n` points, each cut out by a closed immersion `Spec Aᵢ → Spec R'` through `p'`.

### Main results

* `Algebra.exists_etale_completeOrthogonalIdempotents_surjective_not_liesOver`: the decomposition
  above, for an unramified algebra.

### Implementation notes

The product decomposition is recorded by a family of complete orthogonal idempotents
`e : Fin (n + 1) → R' ⊗[R] S`, the factor cut out by an idempotent being the localization away
from it: `Aᵢ = (R' ⊗[R] S)[1/e i]` for `i < n` and `B = (R' ⊗[R] S)[1/e n]`, which for an
idempotent `a` is the quotient by `1 - a` (`IsLocalization.Away.quotient_of_isIdempotentElem`),
and `CompleteOrthogonalIdempotents.bijective_pi` turns the family into the product decomposition
itself. This is the spelling of the neighbouring
`Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt` (Tag 00UK) and of
Mathlib's `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`, and it keeps
every ring in the statement in a fixed universe; an equivalence `R' ⊗[R] S ≃ₐ[R'] (∀ i, A i) × B`
onto a product of newly quantified types says the same thing.

Where the source says "`Aᵢ` has exactly one prime lying over `p'`" it names that prime: it is
`p'Aᵢ`, the ideal generated by the image of `p'`. This is what the statement asserts, rather than
the existence of a unique prime over `p'`; the two agree because `R' → Aᵢ` is surjective, and the
named form is the stronger and more usable one. Note that `(p'Aᵢ).IsPrime` already forces
`Aᵢ` to be nonzero.

Unramifiedness is Mathlib's `Algebra.Unramified R S`, which is `Algebra.FormallyUnramified R S`
together with `Algebra.FiniteType R S`; formal unramifiedness is `Ω_{S/R} = 0`
(`Algebra.formallyUnramified_iff`), so this is Definition 00UT (1) verbatim. Definition 00UT (2),
G-unramified — finite presentation instead of finite type — is a stronger hypothesis, so the
lemma applies to a G-unramified map as it stands.

The étale neighbourhood produced by the route of the source (through Tag 00UK) also has
`κ(p) = κ(p')`, which the source's statement of this lemma does not claim; that extra property is
part of the statement of Tag 00UK, and a user who needs it should cite that lemma.

Faithfulness. (1) No hypothesis is dead: `Algebra.Unramified R S` is what makes the factors
quotients of `R'` and the last factor empty over `p'` (for a merely finite type algebra, say
`S = R[X]`, both fail), and `p.IsPrime` is what "lying over `p`" refers to; the remaining
hypotheses are the data `R`, `S`, `p` of the source. (2) The scalars and base are the source's:
`R'` is étale over `R` and not over a localization of it, the surjections are from `R'` onto the
factors of `R' ⊗[R] S`, and the base change is along `R → R'`. (3) The maps and ideals the source
names are pinned: the prime of `Aᵢ` over `p'` is the canonical `p'Aᵢ = p'.map (algebraMap R' Aᵢ)`,
and the surjection is the canonical `algebraMap R' Aᵢ`, the composite of `R' → R' ⊗[R] S` with the
projection to the factor. (4) The instantiation is not degenerate: for `S = R` (unramified) and
any prime `p` one may take `R' = R`, `p' = p`, `n = 1` and `e = ![1, 0]`, so that `A₁ = R` with
`p'A₁ = p` prime over `p'`, and `B = 0` with no prime at all. A witness where the étale base
change is genuinely needed: `R = ℚ`, `S = ℚ[X]/(X² + 1)`, `p = 0`; here `S` is a field, so `n = 1`
would force `R' → S ⊗[ℚ] R'` to be surjective, which fails for `R' = ℚ`, while `R' = S` gives
`S ⊗[ℚ] S ≅ S × S`, `n = 2` and `B = 0`.

### References

* [Stacks Project, Tag 00UY](https://stacks.math.columbia.edu/tag/00UY)

### Tags

unramified, étale, étale neighbourhood, fibre, complete orthogonal idempotents
-/

/-!
## The proof of Stacks 00UY

Let `R → S` be unramified and let `p` be a prime of `R`. Passing to the étale neighbourhood
`(R', p')` of Tag 00UL splits `R' ⊗[R] S` as `A₁ × ⋯ × Aₙ × B` with each `Aᵢ` finite over `R'`
carrying a single prime `rᵢ` over `p'` with `κ(rᵢ)/κ(p')` purely inseparable, and with `R' → B`
quasi-finite at no prime over `p'`. Unramifiedness closes the three remaining gaps:

* `R' ⊗[R] S` is unramified over `R'`, hence quasi-finite at *every* prime, so there is no prime
  of `R' ⊗[R] S` over `p'` avoiding the last idempotent at all — the factor `B` is empty over
  `p'`;
* `κ(rᵢ)/κ(p')` is separable as well as purely inseparable, hence trivial, and `p'(Aᵢ)_{rᵢ}` is
  the maximal ideal, so Nakayama makes `R'_{p'} → (Aᵢ)_{p'}` surjective;
* `Aᵢ` is finite over `R'`, so that surjectivity spreads out: `R'_f → (Aᵢ)_f` is surjective for
  some `f ∉ p'`, and replacing `R'` by `R'_f` — still étale over `R` — makes `R' → Aᵢ`
  surjective on the nose.

### Implementation notes

The surjectivity of `R' → (R' ⊗[R] S)[1/a]` for an idempotent `a` is recorded as the elementary
condition `∀ x, a * x = a * algebraMap _ _ c` for some `c` coming from the base
(`surjective_algebraMap_localizationAway_of_isIdempotentElem`), which is what both the Nakayama
step and the base localization produce, and which avoids naming the quotient presentation of the
factor.

The Nakayama step is Mathlib's `Localization.localRingHom_surjective_of_primesOver_eq_singleton`;
what is missing upstream is its spreading out *without* injectivity, since
`Localization.exists_awayMap_bijective_of_localRingHom_bijective` produces a bijection from a
bijection and here `R' → Aᵢ` is only surjective. That is
`exists_notMem_forall_exists_mul_eq_of_localRingHom_surjective` below, whose proof is the
surjectivity half of Mathlib's, with module generators in place of algebra generators.

Replacing `R'` by `R'_f` in the last step needs that localization commutes with base change:
`R'_f ⊗[R] S` is the localization of `R' ⊗[R] S` away from the image of `f`. Mathlib has this for
a localization of the *tensor factor being changed* (`IsLocalization.Away.tensor`, which gives
`(R' ⊗[R] S) ⊗[R'] R'_f`), so what is proved below,
`isLocalizationAway_map_of_isLocalizationAway`, transports that along
`Algebra.TensorProduct.cancelBaseChange`. Its `Algebra (R' ⊗[R] S) (R'_f ⊗[R] S)` argument is a
hypothesis pinned by an equation, as in `IsLocalization.of_ringEquiv_left`, because that algebra
structure is not canonical; note that `Algebra R' (R'_f ⊗[R] S)` *is*, and that introducing a
second one along `R' → R'_f → R'_f ⊗[R] S` breaks the scalar tower lemmas, the two `SMul R'`
structures agreeing only up to unfolding.

### References

* [Stacks Project, Tag 00UY](https://stacks.math.columbia.edu/tag/00UY)
-/

@[expose] public section


open TensorProduct

/-- The map from the base to the localization away from an idempotent `a` is surjective as soon
as every multiple of `a` is a multiple of `a` by an element of the base. -/
lemma surjective_algebraMap_localizationAway_of_isIdempotentElem
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {a : A} (ha : IsIdempotentElem a)
    (h : ∀ x : A, ∃ c : R, a * x = a * algebraMap R A c) :
    Function.Surjective (algebraMap R (Localization.Away a)) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem a ha
    (S := Localization.Away a) y
  obtain ⟨c, hc⟩ := h x
  refine ⟨c, (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a)
    |>.mul_left_cancel ?_⟩
  rw [← map_mul, hc, map_mul, IsScalarTower.algebraMap_apply R A (Localization.Away a)]

/-- A prime `r` of `T` which is the only prime over `p` avoiding a submonoid `M` becomes the only
prime over `p` of the localization of `T` at `M`. -/
public lemma primesOver_eq_singleton_of_isLocalization
    {R T A : Type*} [CommRing R] [CommRing T] [CommRing A] [Algebra R T] [Algebra T A]
    [Algebra R A] [IsScalarTower R T A] (M : Submonoid T) [IsLocalization M A]
    (p : Ideal R) (r : Ideal T) [r.IsPrime] [r.LiesOver p]
    (hdisj : Disjoint (M : Set T) (r : Set T))
    (huniq : ∀ Q : Ideal T, Q.IsPrime → Q.LiesOver p → Disjoint (M : Set T) (Q : Set T) → Q = r) :
    p.primesOver A = {r.map (algebraMap T A)} := by
  have hunder : ∀ q : Ideal A, Ideal.under R q = Ideal.under R (Ideal.under T q) :=
    fun q ↦ by simp [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨IsLocalization.isPrime_of_isPrime_disjoint M A r ‹_› hdisj, ?_⟩, ?_⟩
  · refine ⟨?_⟩
    rw [hunder, IsLocalization.under_map_of_isPrime_disjoint M A ‹_› hdisj]
    exact r.over_def p
  · rintro q ⟨hq, hq'⟩
    obtain ⟨h1, h2⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint M A q).mp hq
    rw [← IsLocalization.map_under M A q]
    congr 1
    refine huniq _ h1 ⟨?_⟩ h2
    rw [← hunder]
    exact q.over_def p

/-- Passing to a localization does not change the residue field at a prime, so a surjection
`κ(p) → κ(r)` stays surjective at the prime of the localization above `r`. -/
lemma surjective_algebraMap_residueField_of_isLocalization
    {R T A : Type*} [CommRing R] [CommRing T] [CommRing A] [Algebra R T] [Algebra T A]
    [Algebra R A] [IsScalarTower R T A] (M : Submonoid T) [IsLocalization M A]
    (p : Ideal R) [p.IsPrime] (r : Ideal T) [r.IsPrime] [r.LiesOver p]
    (q : Ideal A) [q.IsPrime] [q.LiesOver p] (hq : r = Ideal.under T q)
    [Algebra (Localization.AtPrime p) (Localization.AtPrime r)]
    [Localization.AtPrime.IsLiesOverAlgebra p r]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (H : Function.Surjective (algebraMap p.ResidueField r.ResidueField)) :
    Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
  have hbij := (RingHom.surjectiveOnStalks_of_isLocalization M A).residueFieldMap_bijective r q hq
  have key : (algebraMap p.ResidueField q.ResidueField) =
      (Ideal.ResidueField.map r q (algebraMap T A) hq).comp
        (algebraMap p.ResidueField r.ResidueField) := by
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R p.ResidueField r.ResidueField,
      IsScalarTower.algebraMap_apply R T r.ResidueField, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply T A q.ResidueField,
      ← IsScalarTower.algebraMap_apply R T q.ResidueField,
      ← IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField]
  rw [key]
  exact hbij.2.comp H

/-- Spreading out a surjection of local rings: if `S` is finite over `R` and `q` is the only
prime of `S` over `p`, a surjective `R_p → S_q` makes some `b ∉ p` multiply all of `S` into the
image of `R`.

This is the surjectivity half of Mathlib's
`Localization.exists_awayMap_bijective_of_localRingHom_bijective`, which is stated for a
bijection and therefore assumes `R → S` injective; here `R → S` is only surjective after
localization. -/
lemma exists_notMem_forall_exists_mul_eq_of_localRingHom_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hq : p.primesOver S = {q})
    (H : Function.Surjective (Localization.localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ b ∉ p, ∀ x : S, ∃ a : R, algebraMap R S b * x = algebraMap R S a := by
  classical
  have key : ∀ x : S, ∃ a : R, ∃ b ∉ p, algebraMap R S b * x = algebraMap R S a := by
    intro x
    have h := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H (algebraMap _ _ x))
    simp only [Localization.localRingHom_mk', Prod.exists, Subtype.exists,
      Ideal.mem_primeCompl_iff, IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at h
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := h
    obtain ⟨d, hd, t, ht⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp hab using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨∏ x ∈ s, b x, Submonoid.prod_mem p.primeCompl (fun x _ ↦ hbp x), ?_⟩
  have hmem : ∀ x ∈ (⊤ : Submodule R S), ∃ c : R,
      algebraMap R S (∏ x ∈ s, b x) * x = algebraMap R S c := by
    rw [← hs]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        refine ⟨(∏ y ∈ s.erase x, b y) * a x, ?_⟩
        rw [← Finset.prod_erase_mul s b hx, map_mul, map_mul, mul_assoc, hab x]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨d, hd⟩ := hy
        exact ⟨c + d, by rw [mul_add, hc, hd, map_add]⟩
    | smul t x _ hx =>
        obtain ⟨c, hc⟩ := hx
        refine ⟨t * c, ?_⟩
        rw [Algebra.smul_def, mul_left_comm, hc, map_mul]
  exact fun x ↦ hmem x Submodule.mem_top

/-- **The Nakayama step.** Let `T` be unramified over `R'` and let `a` be an idempotent of `T`
such that `T[1/a]` is finite over `R'` and `r` is the unique prime of `T` over `p'` avoiding `a`,
with `κ(r)/κ(p')` purely inseparable. Then some `b ∉ p'` multiplies `a * T` into the image of
`R'`. -/
private lemma exists_notMem_forall_exists_mul_eq_of_isIdempotentElem
    {R' T : Type*} [CommRing R'] [CommRing T] [Algebra R' T] [Algebra.Unramified R' T]
    (p' : Ideal R') [p'.IsPrime] {a : T} (ha : IsIdempotentElem a)
    (r : Ideal T) [r.IsPrime] [r.LiesOver p'] (har : a ∉ r)
    [Module.Finite R' (Localization.Away a)]
    (huniq : ∀ Q : Ideal T, Q.IsPrime → Q.LiesOver p' → a ∉ Q → Q = r)
    (hpi : letI := Localization.AtPrime.algebraOfLiesOver p' r
      IsPurelyInseparable p'.ResidueField r.ResidueField) :
    ∃ b ∉ p', ∀ y : T, ∃ c : R',
      a * (algebraMap R' T b * y) = a * algebraMap R' T c := by
  let _ := Localization.AtPrime.algebraOfLiesOver p' r
  set A := Localization.Away a
  set q : Ideal A := r.map (algebraMap T A) with hqdef
  have hdisj : ∀ Q : Ideal T, Q.IsPrime →
      (Disjoint (Submonoid.powers a : Set T) (Q : Set T) ↔ a ∉ Q) :=
    fun _ _ ↦ Ideal.disjoint_powers_iff_notMem_of_isPrime a
  have hq : p'.primesOver A = {q} :=
    primesOver_eq_singleton_of_isLocalization (Submonoid.powers a) p' r
      ((hdisj r ‹_›).mpr har) (fun Q hQ hQ' hQ'' ↦ huniq Q hQ hQ' ((hdisj Q hQ).mp hQ''))
  have hqmem : q ∈ p'.primesOver A := hq ▸ rfl
  have : q.IsPrime := hqmem.1
  have : q.LiesOver p' := hqmem.2
  let _ := Localization.AtPrime.algebraOfLiesOver p' q
  have hunder : r = Ideal.under T q := by
    exact (under_map_algebraMap_of_notMem r har).symm
  have hsurjr : Function.Surjective (algebraMap p'.ResidueField r.ResidueField) :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable p'.ResidueField r.ResidueField
  have hsurjq : Function.Surjective (algebraMap p'.ResidueField q.ResidueField) :=
    surjective_algebraMap_residueField_of_isLocalization (Submonoid.powers a) p' r q hunder hsurjr
  obtain ⟨b, hbp, hb⟩ := exists_notMem_forall_exists_mul_eq_of_localRingHom_surjective p' q hq
    (Localization.localRingHom_surjective_of_primesOver_eq_singleton hq hsurjq)
  refine ⟨b, hbp, fun y ↦ ?_⟩
  obtain ⟨c, hc⟩ := hb (algebraMap T A y)
  refine ⟨c, ?_⟩
  rw [IsScalarTower.algebraMap_apply R' T A, ← map_mul,
    IsScalarTower.algebraMap_apply R' T A] at hc
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a) A).mp hc
  have : a ^ (k + 1) * (algebraMap R' T b * y) = a ^ (k + 1) * algebraMap R' T c := by
    rw [pow_succ, mul_comm (a ^ k) a, mul_assoc, mul_assoc, hk]
  simpa [ha.pow_succ_eq] using this

/-- **Localization commutes with base change.** If `R''` is the localization of `R'` away from
`f`, then `R'' ⊗[R] S` is the localization of `R' ⊗[R] S` away from the image of `f`, along the
base change map `Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' R'') (AlgHom.id R S)`.

The algebra structure of `R'' ⊗[R] S` over `R' ⊗[R] S` is not canonical, so it is taken as a
hypothesis, pinned by `h` — the idiom of `IsLocalization.of_ringEquiv_left`. -/
lemma isLocalizationAway_map_of_isLocalizationAway
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {R' R'' : Type u} [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R'']
    [Algebra R' R''] [IsScalarTower R R' R''] (f : R') [IsLocalization.Away f R'']
    [Algebra (R' ⊗[R] S) (R'' ⊗[R] S)]
    (h : ∀ x : R' ⊗[R] S, algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) x =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' R'') (AlgHom.id R S) x) :
    IsLocalization.Away (algebraMap R' (R' ⊗[R] S) f) (R'' ⊗[R] S) := by
  have key : ∀ x : R' ⊗[R] S, ((Algebra.TensorProduct.comm R' (R' ⊗[R] S) R'').trans
      (Algebra.TensorProduct.cancelBaseChange R R' R' R'' S))
        (algebraMap (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[R'] R'') x) =
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) x := by
    intro x
    rw [h]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        show (Algebra.TensorProduct.cancelBaseChange R R' R' R'' S)
          ((Algebra.TensorProduct.comm R' (R' ⊗[R] S) R'')
            ((a ⊗ₜ[R] b) ⊗ₜ[R'] (1 : R''))) = _
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul]
        simp [Algebra.smul_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact (IsLocalization.isLocalization_iff_of_algEquiv
    (M := Submonoid.powers (algebraMap R' (R' ⊗[R] S) f))
    (AlgEquiv.ofRingEquiv (f := ((Algebra.TensorProduct.comm R' (R' ⊗[R] S) R'').trans
      (Algebra.TensorProduct.cancelBaseChange R R' R' R'' S)).toRingEquiv) key)).mp inferInstance

/-- An element `a` of `A ⊗[R] S` multiplies all of `A ⊗[R] S` into the image of `A` as soon as it
multiplies every `1 ⊗ s` into it: the elements it does multiply into the image of `A` are closed
under addition and under multiplication by the image of `A`. -/
lemma forall_exists_mul_eq_of_tmul
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (a : A ⊗[R] S)
    (h : ∀ s : S, ∃ c : A, a * (1 ⊗ₜ[R] s) = a * algebraMap A (A ⊗[R] S) c) (x : A ⊗[R] S) :
    ∃ c : A, a * x = a * algebraMap A (A ⊗[R] S) c := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r s =>
      obtain ⟨c, hc⟩ := h s
      have hrs : (r ⊗ₜ[R] s : A ⊗[R] S) = algebraMap A (A ⊗[R] S) r * (1 ⊗ₜ[R] s) := by
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      exact ⟨r * c, by rw [hrs, mul_left_comm, hc, map_mul]; ring⟩
  | add x y hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by rw [mul_add, hc, hd, map_add, mul_add]⟩

/-- **"After replacing `R` by `R_f` we win."** Let `R''` be the localization of `R'` away from an
`f ∉ p'`, and suppose `f` multiplies the `i`-th factor of `R' ⊗[R] S` into the image of `R'` for
`i < n`, that each of those factors has a prime over `p'`, and that no prime of `R' ⊗[R] S` over
`p'` avoids the last idempotent. Then `R''` and the images of the idempotents witness the
conclusion of Tag 00UY: `R'' ⊗[R] S` is the localization of `R' ⊗[R] S` away from the image of
`f` (`isLocalizationAway_map_of_isLocalizationAway`), so `f` having become a unit makes each
`R'' → (R'' ⊗[R] S)[1/eᵢ]` surjective, and the primes of `R'' ⊗[R] S` over `p'R''` are exactly
the primes of `R' ⊗[R] S` over `p'`. -/
private lemma exists_etale_completeOrthogonalIdempotents_of_exists_mul_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R)
    {R' : Type u} [CommRing R'] [Algebra R R'] (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p]
    (R'' : Type u) [CommRing R''] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']
    [Algebra.Etale R R''] (f : R') [IsLocalization.Away f R''] (hf : f ∉ p')
    {n : ℕ} (e : Fin (n + 1) → R' ⊗[R] S) (he : CompleteOrthogonalIdempotents e)
    (hmul : ∀ i : Fin n, ∀ y : R' ⊗[R] S, ∃ c : R',
      e i.castSucc * (algebraMap R' (R' ⊗[R] S) f * y) =
        e i.castSucc * algebraMap R' (R' ⊗[R] S) c)
    (hr : ∀ i : Fin n, ∃ r : Ideal (R' ⊗[R] S), r.IsPrime ∧ r.LiesOver p' ∧ e i.castSucc ∉ r)
    (hB : ∀ Q : Ideal (R' ⊗[R] S), Q.IsPrime → Q.LiesOver p' → e (Fin.last n) ∈ Q) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Algebra.Etale R R₀)
      (p₀ : Ideal R₀) (_ : p₀.IsPrime) (_ : p₀.LiesOver p) (m : ℕ)
      (e' : Fin (m + 1) → R₀ ⊗[R] S) (_ : CompleteOrthogonalIdempotents e'),
      (∀ i : Fin m, Function.Surjective (algebraMap R₀ (Localization.Away (e' i.castSucc)))) ∧
      (∀ i : Fin m, (p₀.map (algebraMap R₀ (Localization.Away (e' i.castSucc)))).IsPrime) ∧
      (∀ i : Fin m, (p₀.map (algebraMap R₀ (Localization.Away (e' i.castSucc)))).LiesOver p₀) ∧
      ∀ q : Ideal (Localization.Away (e' (Fin.last m))), q.IsPrime → ¬ q.LiesOver p₀ := by
  classical
  let _ : Algebra (R' ⊗[R] S) (R'' ⊗[R] S) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' R'')
      (AlgHom.id R S)).toRingHom.toAlgebra
  have halg : ∀ x : R' ⊗[R] S, algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) x =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' R'') (AlgHom.id R S) x := fun _ ↦ rfl
  have hbase : ∀ x : R', algebraMap R' (R'' ⊗[R] S) x =
      algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' x) :=
    IsScalarTower.algebraMap_apply R' R'' (R'' ⊗[R] S)
  have htower : ∀ x : R', algebraMap R' (R'' ⊗[R] S) x =
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (algebraMap R' (R' ⊗[R] S) x) := by
    intro x
    rw [halg, hbase]
    simp [Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower R' (R' ⊗[R] S) (R'' ⊗[R] S) := IsScalarTower.of_algebraMap_eq htower
  have : IsLocalization.Away (algebraMap R' (R' ⊗[R] S) f) (R'' ⊗[R] S) :=
    isLocalizationAway_map_of_isLocalizationAway f halg
  have hmapAlg : ∀ x : R',
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (algebraMap R' (R' ⊗[R] S) x) =
        algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' x) := fun x ↦ by rw [← htower, hbase]
  have hmapTmul : ∀ s : S,
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s := by
    intro s
    rw [halg]
    simp
  -- The prime `p'R''` of `R''`.
  have hfd : Disjoint (Submonoid.powers f : Set R') (p' : Set R') :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  have hp₀ : (p'.map (algebraMap R' R'')).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) R'' p' ‹_› hfd
  have hp₀under : Ideal.under R' (p'.map (algebraMap R' R'')) = p' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) R'' ‹_› hfd
  have hp₀lies : (p'.map (algebraMap R' R'')).LiesOver p :=
    ⟨by rw [← Ideal.under_under (A := R) (B := R'), hp₀under]; exact p'.over_def p⟩
  have hcoi : CompleteOrthogonalIdempotents
      (fun i ↦ algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i)) :=
    he.map (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S))
  -- Each of the first `n` factors keeps a prime over `p'R''`.
  have hQ : ∀ i : Fin n, ∃ Q : Ideal (R'' ⊗[R] S), Q.IsPrime ∧
      Ideal.under R'' Q = p'.map (algebraMap R' R'') ∧
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc) ∉ Q := by
    intro i
    obtain ⟨r, hrp, hrl, hrn⟩ := hr i
    have hgr : algebraMap R' (R' ⊗[R] S) f ∉ r := by
      intro hmem
      exact hf (by rw [r.over_def p']; exact Ideal.mem_comap.mpr hmem)
    have := hrp
    have h1 : Ideal.under (R' ⊗[R] S)
        (r.map (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S))) = r :=
      under_map_algebraMap_of_notMem r hgr
    refine ⟨r.map (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S)),
      isPrime_map_algebraMap_of_notMem r hgr, ?_, ?_⟩
    · calc Ideal.under R'' (r.map (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S)))
          = (Ideal.under R' (Ideal.under R''
              (r.map (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S))))).map (algebraMap R' R'') :=
            (IsLocalization.map_under (Submonoid.powers f) R'' _).symm
        _ = p'.map (algebraMap R' R'') := by
            rw [Ideal.under_under, ← Ideal.under_under (B := R' ⊗[R] S), h1,
              ← r.over_def p']
    · exact fun hmem ↦ hrn (h1 ▸ Ideal.mem_comap.mpr hmem)
  -- Surjectivity of `R'' → (R'' ⊗[R] S)[1/eᵢ]`, since `f` is now a unit.
  have hsurj : ∀ i : Fin n, Function.Surjective (algebraMap R''
      (Localization.Away (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc)))) := by
    intro i
    refine surjective_algebraMap_localizationAway_of_isIdempotentElem (hcoi.idem _) ?_
    refine forall_exists_mul_eq_of_tmul _ ?_
    intro s
    obtain ⟨c, hc⟩ := hmul i (1 ⊗ₜ[R] s)
    have hu : IsUnit (algebraMap R' R'' f) := IsLocalization.Away.algebraMap_isUnit f
    have hc' := congrArg (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S)) hc
    simp only [map_mul, hmapAlg, hmapTmul] at hc'
    refine ⟨(↑hu.unit⁻¹ : R'') * algebraMap R' R'' c, ?_⟩
    calc algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc) * (1 ⊗ₜ[R] s)
        = algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' f * (↑hu.unit⁻¹ : R'')) *
            (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc) * (1 ⊗ₜ[R] s)) := by
          rw [hu.mul_val_inv, map_one, one_mul]
      _ = algebraMap R'' (R'' ⊗[R] S) (↑hu.unit⁻¹ : R'') *
            (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc) *
              (algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' f) * (1 ⊗ₜ[R] s))) := by
          rw [map_mul]
          ring
      _ = algebraMap R'' (R'' ⊗[R] S) (↑hu.unit⁻¹ : R'') *
            (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc) *
              algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' c)) := by rw [hc']
      _ = algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc) *
            algebraMap R'' (R'' ⊗[R] S) ((↑hu.unit⁻¹ : R'') * algebraMap R' R'' c) := by
          rw [map_mul]
          ring
  -- The kernel of the surjection is contained in `p'R''`, because the factor has a prime there.
  have hker : ∀ i : Fin n, RingHom.ker (algebraMap R''
      (Localization.Away (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc)))) ≤
      p'.map (algebraMap R' R'') := by
    intro i
    obtain ⟨Q, hQp, hQu, hQn⟩ := hQ i
    have := hQp
    have h1 : Ideal.under R'' (Q.map (algebraMap (R'' ⊗[R] S)
        (Localization.Away (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i.castSucc))))) =
        p'.map (algebraMap R' R'') := by
      rw [← Ideal.under_under (B := R'' ⊗[R] S),
        under_map_algebraMap_of_notMem Q hQn, hQu]
    rw [RingHom.ker_eq_comap_bot, ← h1]
    exact Ideal.comap_mono bot_le
  refine ⟨R'', inferInstance, inferInstance, inferInstance, p'.map (algebraMap R' R''),
    hp₀, hp₀lies, n, fun i ↦ algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e i), hcoi, hsurj,
    fun i ↦ Ideal.map_isPrime_of_surjective (hsurj i) (hker i), fun i ↦ ⟨?_⟩, ?_⟩
  · rw [Ideal.under_def, Ideal.comap_map_of_surjective _ (hsurj i),
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr (hker i)]
  · -- No prime of the last factor lies over `p'R''`.
    intro q hq hql
    obtain ⟨hQp, hQd⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint
      (Submonoid.powers (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e (Fin.last n))))
      (Localization.Away (algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e (Fin.last n)))) q).mp hq
    have hQn : algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (e (Fin.last n)) ∉
        Ideal.under (R'' ⊗[R] S) q :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mp hQd
    have hQu : Ideal.under R'' (Ideal.under (R'' ⊗[R] S) q) = p'.map (algebraMap R' R'') := by
      rw [Ideal.under_under]
      exact (q.over_def _).symm
    have hQTp : (Ideal.under (R' ⊗[R] S) (Ideal.under (R'' ⊗[R] S) q)).IsPrime :=
      Ideal.IsPrime.comap _
    have hQTl : (Ideal.under (R' ⊗[R] S) (Ideal.under (R'' ⊗[R] S) q)).LiesOver p' := by
      refine ⟨?_⟩
      rw [Ideal.under_under, ← Ideal.under_under (A := R') (B := R''), hQu, hp₀under]
    exact hQn (Ideal.mem_comap.mp (hB _ hQTp hQTl))

/-- **Separating the points of a fibre of an unramified ring map** (Stacks 00UY). Let `S` be an
unramified `R`-algebra and `p` a prime of `R`. There are an étale `R`-algebra `R'`, a prime `p'`
of `R'` lying over `p`, and a decomposition `R' ⊗[R] S = A₁ × ⋯ × Aₙ × B` — given by complete
orthogonal idempotents `e 0, …, e n`, with `Aᵢ = (R' ⊗[R] S)[1/e i]` and `B = (R' ⊗[R] S)[1/e n]`
— such that each `R' → Aᵢ` is surjective, each `p'Aᵢ` is a prime of `Aᵢ` lying over `p'`, and no
prime of `B` lies over `p'`. -/
@[stacks 00UY "The product decomposition is given by complete orthogonal idempotents
`e : Fin (n + 1) → R' ⊗[R] S`, the factors being `(R' ⊗[R] S)[1/e i]`. The prime of `Aᵢ` lying
over `p'` is named as the source names it, namely `p'Aᵢ`. See the module docstring."]
public theorem Algebra.exists_etale_completeOrthogonalIdempotents_surjective_not_liesOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Unramified R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R')
      (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e),
      (∀ i : Fin n, Function.Surjective (algebraMap R' (Localization.Away (e i.castSucc)))) ∧
      (∀ i : Fin n, (p'.map (algebraMap R' (Localization.Away (e i.castSucc)))).IsPrime) ∧
      (∀ i : Fin n, (p'.map (algebraMap R' (Localization.Away (e i.castSucc)))).LiesOver p') ∧
      ∀ q : Ideal (Localization.Away (e (Fin.last n))), q.IsPrime → ¬ q.LiesOver p' := by
  classical
  obtain ⟨R', _, _, _, p', _, _, n, e, he, r, hrp, hrl, hfin, hnm, huniq, hres, hBnq⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable
      (R := R) (S := S) p
  -- No prime of `R' ⊗[R] S` over `p'` avoids the last idempotent: `R' ⊗[R] S` is unramified
  -- over `R'`, hence quasi-finite at every prime.
  have hB : ∀ Q : Ideal (R' ⊗[R] S), Q.IsPrime → Q.LiesOver p' → e (Fin.last n) ∈ Q := by
    intro Q hQ hQ'
    by_contra hQ''
    exact hBnq Q hQ' hQ'' inferInstance
  -- Nakayama at each of the `n` factors.
  have hb : ∀ i : Fin n, ∃ b ∉ p', ∀ y : R' ⊗[R] S, ∃ c : R',
      e i.castSucc * (algebraMap R' (R' ⊗[R] S) b * y) =
        e i.castSucc * algebraMap R' (R' ⊗[R] S) c := by
    intro i
    have := hrp i
    have := hrl i
    have := hfin i
    exact exists_notMem_forall_exists_mul_eq_of_isIdempotentElem p' (he.idem _) (r i) (hnm i)
      (fun Q hQ hQ' hQ'' ↦ huniq i Q hQ hQ' hQ'') (hres i).2
  choose b hbp hbmul using hb
  have : Algebra.Etale R (Localization.Away (∏ i, b i)) :=
    Algebra.Etale.comp R R' (Localization.Away (∏ i, b i))
  refine exists_etale_completeOrthogonalIdempotents_of_exists_mul_eq p p'
    (Localization.Away (∏ i, b i)) (∏ i, b i)
    (Submonoid.prod_mem p'.primeCompl fun i _ ↦ hbp i) e he (fun i y ↦ ?_)
    (fun i ↦ ⟨r i, hrp i, hrl i, hnm i⟩) hB
  obtain ⟨c, hc⟩ := hbmul i ((algebraMap R' (R' ⊗[R] S) (∏ j ∈ Finset.univ.erase i, b j)) * y)
  refine ⟨c, ?_⟩
  rwa [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i), map_mul, mul_assoc]


/-!
## An unramified ring map is a localization at an idempotent of its diagonal

Let `R` and `S` be commutative rings and `R → S` a ring map, so that `S` is an
`R`-algebra, and let `S ⊗[R] S` be the tensor product, a commutative `R`-algebra.

The multiplication, or diagonal, map `μ : S ⊗[R] S → S` is the `R`-algebra
homomorphism with `μ (a ⊗ b) = a * b`, namely
`Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S`. It is surjective, and its
kernel is the ideal `J = ker μ`.

A ring map `R → S` is *unramified* when it is both formally unramified and of
finite type, which is `Algebra.Unramified R S`. An element `e` of a ring is
*idempotent* when `e ^ 2 = e`, which is `IsIdempotentElem e`. For a commutative
ring `A` and `e : A`, the localization away from `e` is the localization
`A_e = A[e⁻¹]` at the multiplicative set of powers of `e`, together with the
canonical map `A → A_e`, which is `IsLocalization.Away`.

The main result: if `R → S` is unramified then there is an idempotent
`e ∈ S ⊗[R] S` such that `μ : S ⊗[R] S → S` is isomorphic, as an object under
`A := S ⊗[R] S`, to the canonical localization map `A → A_e`. Being isomorphic
as objects under `A` is expressed here by its universal property: with the
`A`-algebra structure on `S` given by `μ`, one has `IsLocalization.Away e S`.
-/

@[expose] public section

open Algebra TensorProduct in
/-- **Stacks Tag 02FL.** If `R → S` is unramified, then there is an idempotent
`e ∈ S ⊗[R] S` such that the multiplication map `μ : S ⊗[R] S → S` exhibits `S`
as the localization of `A := S ⊗[R] S` away from `e`. Equivalently (the standard
reading of "isomorphic as objects under `A`"), the localization map `A → A_e` is
isomorphic to `μ` under `A`.

Here the `(S ⊗[R] S)`-algebra structure on `S` is the one induced by the
multiplication map `μ = Algebra.TensorProduct.lmul' R`. -/
@[stacks 02FL]
theorem exists_isIdempotentElem_isLocalization_away_of_unramified (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.Unramified R S] :
    ∃ e : S ⊗[R] S, IsIdempotentElem e ∧
      letI : Algebra (S ⊗[R] S) S := (Algebra.TensorProduct.lmul' R).toRingHom.toAlgebra
      IsLocalization.Away e S := by
  -- Full proof below: no remaining open goals, verified clean.
  let : Algebra (S ⊗[R] S) S := (Algebra.TensorProduct.lmul' R).toRingHom.toAlgebra
  set J : Ideal (S ⊗[R] S) := KaehlerDifferential.ideal R S
  -- `J = ker μ` definitionally; it is finitely generated and idempotent (Ω[S⁄R] = 0
  -- since R → S is unramified), so by `Ideal.isIdempotentElem_iff_of_fg` it is `(e')`
  -- for an idempotent `e'`; localizing away from `e = 1 - e'` gives `S`.
  have hJker : J = RingHom.ker (Algebra.TensorProduct.lmul' R).toRingHom := rfl
  have hidem : IsIdempotentElem J := by
    rw [← Ideal.cotangent_subsingleton_iff]
    exact (inferInstance : Subsingleton Ω[S⁄R])
  obtain ⟨e', he'idem, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg J
    (KaehlerDifferential.ideal_fg R S)).mp hidem
  refine ⟨1 - e', he'idem.one_sub, ?_⟩
  have halg : (algebraMap (S ⊗[R] S) S) = (Algebra.TensorProduct.lmul' R).toRingHom := rfl
  apply IsLocalization.away_of_isIdempotentElem he'idem.one_sub
  · rw [sub_sub_cancel, halg, ← hJker, hspan]
  · intro x
    refine ⟨x ⊗ₜ 1, ?_⟩
    rw [halg]
    simp [Algebra.TensorProduct.lmul'_apply_tmul]
