module

public import Mathlib.RingTheory.Localization.Finiteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseTrivialize

/-!
# Primes of a shrunk base and of the algebras over it

The finite case of property (B) for the étale topology, [Stacks, Tag 04DQ], shrinks its base: the
étale local structure theorem [Stacks, Tag 00UL] produces an étale `A`-algebra `A'` with a prime
`p'`, and the decomposition it supplies is then trimmed by inverting an element `a ∉ p'`, so that
the base becomes `A'' = A'[1/a]` and the module-finite side becomes `P'' = P[1/a]` for
`P = A' ⊗[A] B`. The argument must then be *re-entered* over `A''`, because the per-index
trivialisation `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_algebraMap_of_etale_pair`
is applied to the trimmed decomposition and returns an element of the shrunk base.

Re-entering needs a prime of the shrunk base and primes of the shrunk algebras above it. Neither
can be obtained by pulling a prime back along the shrinking map: `Spec A'' → Spec A'` is an open
immersion and not surjective, and localising away from an element can empty an entire factor of a
decomposition. They are instead *pushed forward*: a prime avoiding the element inverted survives
in the localisation, as the ideal it generates there. This file records that production and the
facts about it that the re-entry consumes — the prime lies over the shrunk prime, it contracts
back to the prime it came from, uniqueness over the shrunk prime follows from uniqueness
downstairs, and the shrunk algebra is still module-finite over the shrunk base.

Everything here is stated for arbitrary localisations `IsLocalization.Away a A''` and
`IsLocalization.Away (algebraMap A' P a) P''` rather than for `Localization.Away`, so that the two
shrinkings the finite case performs — one of the base and one of a factor — can be composed
without rewriting along the comparison isomorphisms of the models.

The prime of the shrunk *base* itself needs nothing new: it is
`Stacks.EtaleCohomology.isPrime_map_algebraMap_of_notMem` together with
`Stacks.EtaleCohomology.under_map_algebraMap_of_notMem` and
`Stacks.EtaleCohomology.liesOver_map_algebraMap_of_notMem`, applied to the localisation
`A' → A'[1/a]`. What is new here is the comparison of the primes of an *algebra* over the shrunk
base with the primes of that algebra over `p'`.

## Main results

* `Stacks.EtaleCohomology.notMem_algebraMap_of_liesOver`: an element of the base outside a prime
  is outside every prime lying over it. This is what makes the element inverted automatically
  avoid every prime of the module-finite side over `p'`, so that no further hypothesis is needed
  to push those primes into the shrunk algebra.
* `Stacks.EtaleCohomology.liesOver_map_algebraMap_shrunk`: **the prime of the shrunk algebra lies
  over the prime of the shrunk base.** The prime of `P[1/a]` cut out by a prime `q` of `P` over
  `p'` lies over the prime of `A'[1/a]` cut out by `p'`.
* `Stacks.EtaleCohomology.exists_isPrime_liesOver_notMem_map_shrunk`: the same read as an
  existence statement, retaining an element avoided by `q`: the factor of a decomposition that `q`
  lives in still carries a prime after the shrinking.
* `Stacks.EtaleCohomology.liesOver_under_of_liesOver_shrunk`: conversely, a prime of the shrunk
  algebra over the shrunk prime contracts to a prime of the algebra over `p'`.
* `Stacks.EtaleCohomology.forall_eq_of_forall_eq_shrunk`: uniqueness of the prime over the shrunk
  prime, from uniqueness over `p'`.
* `Stacks.EtaleCohomology.isLocalization_algebraMapSubmonoid_powers_of_away` and
  `Stacks.EtaleCohomology.moduleFinite_shrunk`: **the shrunk algebra is module-finite over the
  shrunk base**; `Stacks.EtaleCohomology.isIntegral_shrunk` is the integrality that follows, which
  is the form the shrinking lemmas ask for.

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 00UL](https://stacks.math.columbia.edu/tag/00UL)
-/

@[expose] public section

namespace Stacks.EtaleCohomology

/-- **An element of the base outside a prime avoids every prime over it.** If `q` lies over `p`
and `x ∉ p`, then the image of `x` in the algebra is outside `q`, because `p` is by definition the
contraction of `q`.

In the finite case of property (B), [Stacks, Tag 04DQ], this is what makes the shrinking of the
base harmless for the primes that matter: the element inverted is chosen outside `p'`, so it
automatically avoids every prime of the module-finite side lying over `p'`, and each of those
primes therefore survives in the shrunk algebra. -/
theorem notMem_algebraMap_of_liesOver {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (p : Ideal A) (q : Ideal R) [q.LiesOver p] {x : A} (hx : x ∉ p) :
    algebraMap A R x ∉ q := fun hmem => hx (by
  rw [q.over_def p, Ideal.under_def]
  exact Ideal.mem_comap.mpr hmem)

section AwayBaseChange

variable {A' P P'' : Type*} [CommRing A'] [CommRing P] [CommRing P''] [Algebra A' P]
  [Algebra P P'']

/-- **A localisation away from the image of an element of the base is a localisation at the image
of its powers.** The submonoid of `P` generated by the images of the powers of `a : A'` is the
submonoid of powers of the image of `a`, so a localisation of `P` away from that image is a
localisation at the image of the powers of `a`.

This is the form `Module.Finite.of_isLocalization` asks for, and
`Stacks.EtaleCohomology.moduleFinite_shrunk` is its consequence. -/
theorem isLocalization_algebraMapSubmonoid_powers_of_away (a : A')
    [IsLocalization.Away (algebraMap A' P a) P''] :
    IsLocalization (Algebra.algebraMapSubmonoid P (Submonoid.powers a)) P'' := by
  rw [Algebra.algebraMapSubmonoid_powers]
  infer_instance

/-- The prime of `P[1/a]` cut out by a prime `q` of `P` over `p' ∌ a` contracts back to `q`. -/
private theorem under_map_algebraMap_shrunk (a : A') [IsLocalization.Away (algebraMap A' P a) P'']
    (p' : Ideal A') (ha : a ∉ p') (q : Ideal P) [q.IsPrime] [q.LiesOver p'] :
    (q.map (algebraMap P P'')).under P = q :=
  under_map_algebraMap_of_notMem _ q (notMem_algebraMap_of_liesOver p' q ha)

end AwayBaseChange

section ShrunkStage

variable {A' A'' P P'' : Type*} [CommRing A'] [CommRing A''] [CommRing P] [CommRing P'']
  [Algebra A' A''] [Algebra A' P] [Algebra A' P''] [Algebra A'' P''] [Algebra P P'']
  [IsScalarTower A' A'' P''] [IsScalarTower A' P P'']

/-- **The prime of the shrunk algebra cut out by a prime of the algebra lies over the prime of the
shrunk base.** Let `a ∉ p'`, let `A''` be `A'` localised away from `a` and `P''` be `P` localised
away from the image of `a`, and let `q` be a prime of `P` lying over `p'`. Then the prime of `P''`
cut out by `q` lies over the prime of `A''` cut out by `p'`.

This is the production of the prime that the re-entry of [Stacks, Tag 04DQ] over the shrunk base
needs, and it uses no surjectivity: the prime is pushed forward from `q`, not pulled back along
`Spec A'' → Spec A'`, which is not surjective. That `q` survives at all is
`Stacks.EtaleCohomology.notMem_algebraMap_of_liesOver`; that what it cuts out is prime and
contracts back to `q` is `Stacks.EtaleCohomology.isPrime_map_algebraMap_of_notMem` and
`Stacks.EtaleCohomology.under_map_algebraMap_of_notMem`. The content here is the identification of
its contraction to `A''`: that contraction is a prime of `A''` whose contraction to `A'` is `p'`,
and a prime of a localisation is recovered from its contraction by
`IsLocalization.map_under`. -/
theorem liesOver_map_algebraMap_shrunk (a : A') [IsLocalization.Away a A'']
    [IsLocalization.Away (algebraMap A' P a) P''] (p' : Ideal A') [p'.IsPrime] (ha : a ∉ p')
    {p'' : Ideal A''} (hp'' : p'' = p'.map (algebraMap A' A''))
    (q : Ideal P) [q.IsPrime] [q.LiesOver p'] :
    (q.map (algebraMap P P'')).LiesOver p'' := by
  subst hp''
  have hv : ((q.map (algebraMap P P'')).under A'').under A' = p' := by
    rw [Ideal.under_under, ← Ideal.under_under (A := A') (B := P),
      under_map_algebraMap_shrunk a p' ha q]
    exact (q.over_def p').symm
  refine ⟨?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers a) A''
    ((q.map (algebraMap P P'')).under A''), hv]

/-- **A prime of the shrunk algebra avoiding a given element, from one of the algebra.** If `q` is
a prime of `P` lying over `p'` and avoiding `b : P`, then the shrunk algebra `P'' = P[1/a]` has a
prime lying over the shrunk prime and avoiding the image of `b`.

This is the form the re-entry of [Stacks, Tag 04DQ] uses: the index set of the trimmed
decomposition is the set of indices `i` whose factor `P[1/b i]` carries a prime over `p'`, and
after the shrinking that factor must still carry one, over the shrunk prime. It does, and the
reason is not that anything is surjective but that the prime of `P''` cut out by `q` contracts
back to `q`, so an element outside `q` has image outside it. -/
theorem exists_isPrime_liesOver_notMem_map_shrunk (a : A') [IsLocalization.Away a A'']
    [IsLocalization.Away (algebraMap A' P a) P''] (p' : Ideal A') [p'.IsPrime] (ha : a ∉ p')
    {p'' : Ideal A''} (hp'' : p'' = p'.map (algebraMap A' A''))
    (q : Ideal P) [q.IsPrime] [q.LiesOver p'] {b : P} (hb : b ∉ q) :
    ∃ u : Ideal P'', ∃ _ : u.IsPrime, u.LiesOver p'' ∧ algebraMap P P'' b ∉ u := by
  refine ⟨q.map (algebraMap P P''),
    isPrime_map_algebraMap_of_notMem (algebraMap A' P a) q (notMem_algebraMap_of_liesOver p' q ha),
    liesOver_map_algebraMap_shrunk a p' ha hp'' q, fun hmem => hb ?_⟩
  rw [← under_map_algebraMap_shrunk a p' ha q (P'' := P''), Ideal.under_def, Ideal.mem_comap]
  exact hmem

/-- **A prime of the shrunk algebra over the shrunk prime contracts to a prime over `p'`.** This is
the converse direction of `Stacks.EtaleCohomology.liesOver_map_algebraMap_shrunk`, and it is what
transports a hypothesis about the primes of `P` over `p'` — uniqueness, or a residue field
condition — to the primes of `P''` over the shrunk prime: the contraction of the shrunk prime to
`A'` is `p'`, by `Stacks.EtaleCohomology.under_map_algebraMap_of_notMem`. -/
theorem liesOver_under_of_liesOver_shrunk (a : A') [IsLocalization.Away a A''] (p' : Ideal A')
    [p'.IsPrime] (ha : a ∉ p') {p'' : Ideal A''} (hp'' : p'' = p'.map (algebraMap A' A''))
    (u : Ideal P'') [u.LiesOver p''] : (u.under P).LiesOver p' := by
  subst hp''
  refine ⟨?_⟩
  rw [Ideal.under_under, ← Ideal.under_under (A := A') (B := A'') u,
    ← u.over_def (p'.map (algebraMap A' A''))]
  exact (under_map_algebraMap_of_notMem a p' ha).symm

/-- **Uniqueness of the prime over the shrunk prime.** If any two primes of `P` lying over `p'` are
equal, then any two primes of the shrunk algebra `P'' = P[1/a]` lying over the shrunk prime are
equal.

Each one contracts to a prime of `P` over `p'` by
`Stacks.EtaleCohomology.liesOver_under_of_liesOver_shrunk`, those contractions agree, and a prime
of a localisation is determined by its contraction. This is the uniqueness hypothesis of the
per-index trivialisation
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_algebraMap_of_etale_pair`, read over the
shrunk base rather than over `A'`. -/
theorem forall_eq_of_forall_eq_shrunk (a : A') [IsLocalization.Away a A'']
    [IsLocalization.Away (algebraMap A' P a) P''] (p' : Ideal A') [p'.IsPrime] (ha : a ∉ p')
    {p'' : Ideal A''} (hp'' : p'' = p'.map (algebraMap A' A''))
    (huniq : ∀ q₁ q₂ : Ideal P, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂) :
    ∀ u₁ u₂ : Ideal P'', u₁.IsPrime → u₂.IsPrime → u₁.LiesOver p'' → u₂.LiesOver p'' →
      u₁ = u₂ := by
  intro u₁ u₂ h₁ h₂ ho₁ ho₂
  have k₁ : (u₁.under P).LiesOver p' := liesOver_under_of_liesOver_shrunk a p' ha hp'' u₁
  have k₂ : (u₂.under P).LiesOver p' := liesOver_under_of_liesOver_shrunk a p' ha hp'' u₂
  have key : u₁.under P = u₂.under P := huniq _ _ (h₁.comap _) (h₂.comap _) k₁ k₂
  rw [← IsLocalization.map_under (Submonoid.powers (algebraMap A' P a)) P'' u₁,
    ← IsLocalization.map_under (Submonoid.powers (algebraMap A' P a)) P'' u₂, key]

/-- **The shrunk algebra is module-finite over the shrunk base.** If `P` is module-finite over `A'`
then `P[1/a]` is module-finite over `A'[1/a]`, for any `a : A'`.

This is `Module.Finite.of_isLocalization` for the submonoid of powers of `a`, the localisation of
`P` at the image of that submonoid being the localisation away from the image of `a` by
`Stacks.EtaleCohomology.isLocalization_algebraMapSubmonoid_powers_of_away`. It is what lets the
re-entry of [Stacks, Tag 04DQ] over the shrunk base use the hypotheses `[Module.Finite A' F]` of
the per-index trivialisation and `[Algebra.IsIntegral A' D]` of the shrinking lemmas: the
module-finiteness the étale local structure theorem [Stacks, Tag 00UL] supplies is over `A'`, and
the re-entry happens over `A'[1/a]`. -/
theorem moduleFinite_shrunk (a : A') [IsLocalization.Away a A'']
    [IsLocalization.Away (algebraMap A' P a) P''] [Module.Finite A' P] :
    Module.Finite A'' P'' :=
  have := isLocalization_algebraMapSubmonoid_powers_of_away (P := P) (P'' := P'') a
  Module.Finite.of_isLocalization A' P (Submonoid.powers a)

/-- **The shrunk algebra is integral over the shrunk base.** This is
`Stacks.EtaleCohomology.moduleFinite_shrunk` in the form the shrinking lemmas of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAlgebra` ask for: they require
`[Algebra.IsIntegral A' R]` in order to kill the factors of a decomposition that carry no prime
over the chosen prime of the base. -/
theorem isIntegral_shrunk (a : A') [IsLocalization.Away a A'']
    [IsLocalization.Away (algebraMap A' P a) P''] [Module.Finite A' P] :
    Algebra.IsIntegral A'' P'' :=
  have := moduleFinite_shrunk (A'' := A'') (P := P) (P'' := P'') a
  inferInstance

end ShrunkStage

end Stacks.EtaleCohomology

end
