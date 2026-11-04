module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings
public import StacksFrontier.RingTheory.WeaklyEtale.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField
public import StacksFrontier.RingTheory.WeaklyEtale.StrictlyHenselian
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# A faithfully flat ind-étale cover of a weakly étale ring map

Proposition 097Z says that a weakly étale ring map `A → B` admits a *cover* by an ind-étale
one: there is a faithfully flat, ind-étale `B → B'` for which the composite `A → B'` is
ind-étale. It is a cover and not a lift — nothing asserts that `A → B` itself factors through
an ind-étale map, and the faithful flatness of `B → B'` is what makes the statement useful.

The source proves it from Lemma 097X (the w-local square `B → D`, `A → C`, `C → D`) together
with Proposition 097G (a ring map which identifies local rings is covered by an ind-Zariski
one). Neither is in the library: 097G and everything its proof rests on — the whole of
Sections 61.5 and 61.6 of the source — is unformalized, and so is 097X, which lives in
Section 61.8 and rests on Section 61.5 as well. The main result here therefore carries each of
the two as an explicitly named hypothesis. Lemma 0982 carries 097Z as its hypothesis `h097Z`,
and this file's 097Z is stated so as to fit that binder. What this file *does* prove outright
is the step of 097Z's proof that is not one of those two citations: that the right-hand edge
`C → D` of the square identifies local rings. That is
`identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian`, which assumes no upstream lemma.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.ProEtale.identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian`: a
  weakly étale `C → D` identifies local rings as soon as every maximal ideal of `D` contracts
  to a maximal ideal of `C` and `C` is strictly henselian at each of its maximal ideals. This
  is the middle of the proof of Proposition 097Z; it carries no upstream lemma as a hypothesis.
* `AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indEtale_of_weaklyEtale`: **Proposition
  097Z**, from Lemma 097X and Proposition 097G carried as named hypotheses.

## Implementation notes

The source argument for 097Z runs: `A → B` induces algebraic residue field extensions
(Lemma 092R, `isSeparable_and_isAlgebraic_residueField_of_weaklyEtale`), so Lemma 097X supplies
a square with `A → C` and `B → D` faithfully flat ind-étale, with `Spec C` and `Spec D` w-local
and `C` strictly henselian at its maximal ideals. Then `C → D` is weakly étale (Lemma 092L,
`weaklyEtale_of_comp`), it identifies local rings, and Proposition 097G produces a faithfully
flat ind-Zariski `D → D'` with `C → D'` ind-Zariski; `D'` is the required cover of `B`.

Two economies are taken in the hypothesis `h097X`. The first makes the statement *stronger*:
only four of 097X's nine conclusions are assumed — parts (1) and (2), the half of part (6)
saying that a maximal ideal of `D` contracts to a maximal ideal of `C`, and part (9). Parts
(3), (4), (5), (7) and (8) are dropped. In particular the w-locality of `Spec C` and of
`Spec D` is not needed: the specialization fact the source uses is replaced by
`Ideal.exists_le_maximal`, that every prime of a commutative ring is contained in a maximal
ideal, and the source's "every point of `Spec C` specializes to a closed point" is applied here
in the form "every prime of `D` is contained in a maximal ideal" — the same Zorn argument, one
ring over. The second economy changes nothing either way: the hypotheses are phrased with
maximal ideals rather than with closed points of the prime spectrum, which is the same
condition, and keeps the statement algebraic.

The proof of `identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian` follows the source. At a
maximal ideal `m` of `D` lying over a maximal `m' ⊆ C`, the map `C_{m'} → D_m` is weakly étale
— `C → C_{m'}` and `D → D_m` are ind-étale hence weakly étale (Lemma 097N and
`StacksDraft.indEtale_atPrime`), so `C → D_m` is weakly étale by Lemma 092J and `C_{m'} → D_m`
by Lemma 092L — and it is a local homomorphism, so Theorem 092Z
(`bijective_algebraMap_of_weaklyEtale_of_isLocalHom`) makes it bijective. An arbitrary prime
`q` of `D` is contained in some maximal `m`, and `C_p → D_q` is then obtained from `C_{m'} →
D_m` by localizing both sides: `Localization.AtPrime p` is a localization of `C_{m'}` at the
prime `p · C_{m'}` (`IsLocalization.isLocalization_atPrime_localization_atPrime`), and the
square of `Localization.localRingHom`s commutes by `Localization.localRingHom_unique`, so three
of its four sides being bijective forces the fourth.

Ind-étaleness and ind-Zariskiness are taken in the universe-pinned forms
`StacksDraft.IndEtale` and `Algebra.IsIndZariski`, each of which fixes the index universe of
the filtered colimit in terms of the universes of the two rings; writing
`CategoryTheory.ObjectProperty.ind` directly in a statement would bind a fresh universe
parameter at every occurrence. Every ring named in the two main statements lives in the single
universe `u`; the three purely localization-theoretic helpers are universe-polymorphic.

No declaration here carries a `@[stacks]` attribute. Proposition 097Z is a single assertion, so
a tag on it would have to be the bare tag; but the form proved here assumes two upstream
lemmas, and tagging a hypothesis-carrying statement would claim coverage the library does not
have.

## References

* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
* [Stacks Project, Tag 097X](https://stacks.math.columbia.edu/tag/097X)
* [Stacks Project, Tag 097G](https://stacks.math.columbia.edu/tag/097G)
* [Stacks Project, Tag 092R](https://stacks.math.columbia.edu/tag/092R)
* [Stacks Project, Tag 092J](https://stacks.math.columbia.edu/tag/092J)
* [Stacks Project, Tag 092L](https://stacks.math.columbia.edu/tag/092L)
* [Stacks Project, Tag 092Z](https://stacks.math.columbia.edu/tag/092Z)
* [Stacks Project, Tag 097N](https://stacks.math.columbia.edu/tag/097N)
* [Stacks Project, Tag 0982](https://stacks.math.columbia.edu/tag/0982)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-! ## Transferring bijectivity of a map of local rings down a specialization -/

/-- In a commuting square of maps `γ ∘ φ = β ∘ α`, if `α`, `β` and `γ` are bijective then so is
`φ`: it is injective because `γ ∘ φ` is, and surjective because `γ ∘ φ` is and `γ` is
injective. -/
private theorem bij_of_comp_eq {X Y Z W : Type*} {φ : X → Y} {γ : Y → W} {α : X → Z}
    {β : Z → W} (h : γ ∘ φ = β ∘ α) (hα : Function.Bijective α) (hβ : Function.Bijective β)
    (hγ : Function.Bijective γ) : Function.Bijective φ := by
  have hcomp : Function.Bijective (γ ∘ φ) := h ▸ hβ.comp hα
  refine ⟨Function.Injective.of_comp hcomp.1, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hcomp.2 (γ y)
  exact ⟨x, hγ.1 hx⟩

/-- A bijective ring map induces a bijective map of localizations at corresponding primes: the
induced map is the underlying map of `Localization.localRingEquiv`. -/
private theorem bijective_localRingHom_of_bijective {R P : Type*} [CommRing R] [CommRing P]
    (I : Ideal R) [I.IsPrime] (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f)
    (hf : Function.Bijective f) :
    Function.Bijective (Localization.localRingHom I J f hIJ) :=
  (Localization.localRingEquiv I J (RingEquiv.ofBijective f hf) hIJ).bijective

/-- For a prime `P` of a localization `Localization M` of `R` lying over a prime `p` of `R`, the
map `R_p → (Localization M)_P` induced by the localization map `R → Localization M` is
bijective. Indeed `(Localization M)_P` is itself a localization of `R` at `p`
(`IsLocalization.isLocalization_atPrime_localization_atPrime`), and the induced map is the
unique `R`-algebra map between two localizations of `R` at `p`. -/
private theorem bijective_localRingHom_toLocalization {R : Type*} [CommRing R] (M : Submonoid R)
    (P : Ideal (Localization M)) [P.IsPrime] (p : Ideal R) [p.IsPrime]
    (hp : p = P.comap (algebraMap R (Localization M))) :
    Function.Bijective (Localization.localRingHom p P (algebraMap R (Localization M)) hp) := by
  have hpc : p.primeCompl = (P.comap (algebraMap R (Localization M))).primeCompl := by
    ext x
    show x ∉ p ↔ x ∉ P.comap (algebraMap R (Localization M))
    rw [hp]
  have : IsLocalization p.primeCompl (Localization.AtPrime P) := by
    rw [hpc]
    exact IsLocalization.isLocalization_atPrime_localization_atPrime M P
  let e : Localization.AtPrime p ≃ₐ[R] Localization.AtPrime P :=
    IsLocalization.algEquiv p.primeCompl _ _
  have he : (Localization.localRingHom p P (algebraMap R (Localization M)) hp :
      Localization.AtPrime p →+* Localization.AtPrime P) = e.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext p.primeCompl ?_
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, Localization.localRingHom_to_map]
    rw [← IsScalarTower.algebraMap_apply R (Localization M) (Localization.AtPrime P) x]
    exact (e.commutes x).symm
  rw [he]
  exact e.bijective

/-- Bijectivity of the induced map of local rings descends along a specialization: if `q ≤ m`
are primes of `D` and `C_{m ∩ C} → D_m` is bijective, then so is `C_{q ∩ C} → D_q`.

Write `P` and `Q` for the primes of `C_{m ∩ C}` and of `D_m` lying over `q ∩ C` and `q`. The
square of induced maps `C_{q ∩ C} → D_q → (D_m)_Q` and `C_{q ∩ C} → (C_{m ∩ C})_P → (D_m)_Q`
commutes, because both composites are maps out of a localization of `C` restricting to the same
map on `C` (`Localization.localRingHom_unique`). Its other three sides are bijective, two by
`bijective_localRingHom_toLocalization` and one by `bijective_localRingHom_of_bijective`. -/
private theorem bijective_localRingHom_of_le {C D : Type*} [CommRing C] [CommRing D]
    [Algebra C D] (m q : Ideal D) [m.IsPrime] [q.IsPrime] (hqm : q ≤ m)
    (hg : Function.Bijective
      (Localization.localRingHom (m.comap (algebraMap C D)) m (algebraMap C D) rfl)) :
    Function.Bijective
      (Localization.localRingHom (q.comap (algebraMap C D)) q (algebraMap C D) rfl) := by
  set f := algebraMap C D
  set m' := m.comap f
  set p := q.comap f
  have hle : p ≤ m' := Ideal.comap_mono hqm
  set cm := algebraMap C (Localization.AtPrime m') with hcmdef
  set dm := algebraMap D (Localization.AtPrime m) with hdmdef
  set g := Localization.localRingHom m' m f rfl with hgdef
  set P := p.map cm with hPdef
  set Q := q.map dm
  have hPp : P.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m' hle
  have hQp : Q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m hqm
  have hPc : p = P.comap cm := (Ideal.under_map_of_isLocalizationAtPrime m' hle).symm
  have hQc : q = Q.comap dm := (Ideal.under_map_of_isLocalizationAtPrime m hqm).symm
  have hsq : g.comp cm = dm.comp f := by
    ext x
    simp [hgdef, hcmdef, hdmdef]
  have hPQ : P = Q.comap g := by
    have h1 : (Q.comap g).comap cm = p := by
      rw [Ideal.comap_comap, hsq, ← Ideal.comap_comap, ← hQc]
    rw [hPdef, ← h1, IsLocalization.map_under m'.primeCompl]
  refine bij_of_comp_eq (γ := Localization.localRingHom q Q dm hQc)
    (α := Localization.localRingHom p P cm hPc) (β := Localization.localRingHom P Q g hPQ)
    ?_ (bijective_localRingHom_toLocalization _ _ _ hPc)
    (bijective_localRingHom_of_bijective _ _ _ hPQ hg)
    (bijective_localRingHom_toLocalization _ _ _ hQc)
  have h1 := Localization.localRingHom_comp p q Q f rfl dm hQc
  have h2 := Localization.localRingHom_unique p Q (dm.comp f)
    (by rw [← Ideal.comap_comap, ← hQc])
    (j := (Localization.localRingHom P Q g hPQ).comp (Localization.localRingHom p P cm hPc))
    (fun x => by simp [hsq.symm])
  exact congrArg (fun h : Localization.AtPrime p →+* Localization.AtPrime Q => (h : _ → _))
    (h1.symm.trans h2)

/-- **Theorem 092Z at a maximal ideal.** If `C → D` is weakly étale and `C` is strictly
henselian at the contraction `m ∩ C` of a prime `m` of `D`, then `C_{m ∩ C} → D_m` is
bijective.

The map `C → C_{m ∩ C}` is ind-étale, hence weakly étale by Lemma 097N, and so is `D → D_m`;
therefore `C → D_m` is weakly étale by Lemma 092J and `C_{m ∩ C} → D_m` by Lemma 092L. It is a
local homomorphism by `Localization.isLocalHom_localRingHom`, so Theorem 092Z applies. -/
private theorem bijective_localRingHom_atMaximal {C D : Type u} [CommRing C] [CommRing D]
    [Algebra C D] (hCD : Algebra.WeaklyEtale C D) (m : Ideal D) [m.IsPrime]
    (hsh : StrictlyHenselianLocalRing (Localization.AtPrime (m.comap (algebraMap C D)))) :
    Function.Bijective
      (Localization.localRingHom (m.comap (algebraMap C D)) m (algebraMap C D) rfl) := by
  let _ : Algebra (Localization.AtPrime (m.comap (algebraMap C D))) (Localization.AtPrime m) :=
    (Localization.localRingHom (m.comap (algebraMap C D)) m (algebraMap C D) rfl).toAlgebra
  have _ : IsScalarTower C (Localization.AtPrime (m.comap (algebraMap C D)))
      (Localization.AtPrime m) :=
    IsScalarTower.of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ m _ rfl x).symm
  have hC : Algebra.WeaklyEtale C (Localization.AtPrime (m.comap (algebraMap C D))) :=
    Algebra.weaklyEtale_of_ind_etale
      (StacksDraft.indEtale_atPrime (m.comap (algebraMap C D)))
  have hCDm : Algebra.WeaklyEtale C (Localization.AtPrime m) :=
    weaklyEtale_comp C D (Localization.AtPrime m) hCD
      (Algebra.weaklyEtale_of_ind_etale (StacksDraft.indEtale_atPrime m))
  exact bijective_algebraMap_of_weaklyEtale_of_isLocalHom _ (Localization.AtPrime m)
    (weaklyEtale_of_comp C _ _ hC hCDm)

/-! ## The middle step of Proposition 097Z -/

/-- **The step of Proposition 097Z's proof that is not one of its citations.** A weakly étale
ring map `C → D` identifies local rings as soon as every maximal ideal of `D` contracts to a
maximal ideal of `C` and `C` is strictly henselian at each of its maximal ideals. In the
source's situation these two hypotheses are parts (6) and (9) of Lemma 097X.

Every prime `q` of `D` is contained in a maximal ideal `m` (`Ideal.exists_le_maximal`, the Zorn
argument that replaces the source's appeal to specialization onto closed points), the map
`C_{m ∩ C} → D_m` is bijective by Theorem 092Z, and bijectivity descends from `m` to `q`. -/
theorem identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian (C D : Type u) [CommRing C]
    [CommRing D] [Algebra C D] (hCD : Algebra.WeaklyEtale C D)
    (hmax : ∀ (m : Ideal D) [m.IsMaximal], (m.comap (algebraMap C D)).IsMaximal)
    (hsh : ∀ (n : Ideal C) [n.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime n)) :
    Algebra.IdentifiesLocalRings C D := by
  intro q _
  obtain ⟨m, _, hqm⟩ := Ideal.exists_le_maximal q (Ideal.IsPrime.ne_top ‹q.IsPrime›)
  have _ : (m.comap (algebraMap C D)).IsMaximal := hmax m
  exact bijective_localRingHom_of_le m q hqm
    (bijective_localRingHom_atMaximal hCD m (hsh (m.comap (algebraMap C D))))

/-! ## Proposition 097Z -/

/-- **Proposition 097Z, from Lemma 097X and Proposition 097G.** A weakly étale ring map `A → B`
admits a faithfully flat, ind-étale `B → B'` with `A → B'` ind-étale. This is a cover of
`A → B`, not a factorization of it.

`h097X` is Lemma 097X restricted to what this proof consumes: for a ring map inducing algebraic
residue field extensions, a commutative square `B → D`, `A → C`, `C → D` with `A → C` and
`B → D` faithfully flat and ind-étale — parts (1) and (2) — in which a maximal ideal of `D`
contracts to a maximal ideal of `C` — part of (5) and (6) — and `C` is strictly henselian at
each of its maximal ideals — part (9). `h097G` is Proposition 097G verbatim: a ring map which
identifies local rings is covered by a faithfully flat ind-Zariski map through which the source
becomes ind-Zariski.

Given those, the hypothesis of `h097X` holds for `A → B` by Lemma 092R, the resulting
`C → D` is weakly étale by Lemmas 092J and 092L and identifies local rings by
`identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian`, and `h097G` applied to it produces
`D → D'`. Then `B → D'` is faithfully flat as a composite of faithfully flat maps and ind-étale
as a composite of ind-étale maps, and `A → D'` is ind-étale through `C`, the square `A → C → D'`
agreeing with `A → B → D'` because `C → D'` factors through `D`. -/
theorem exists_faithfullyFlat_indEtale_of_weaklyEtale (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (hAB : Algebra.WeaklyEtale A B)
    (h097X : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
      (∀ q : Ideal S, ∀ [q.IsPrime],
        letI := (Ideal.ResidueField.map (q.comap (algebraMap R S)) q
          (algebraMap R S) rfl).toAlgebra
        Algebra.IsAlgebraic (q.comap (algebraMap R S)).ResidueField q.ResidueField) →
      ∃ (C E : Type u) (_ : CommRing C) (_ : CommRing E) (_ : Algebra R C) (_ : Algebra S E)
          (_ : Algebra C E) (_ : Algebra R E) (_ : IsScalarTower R C E)
          (_ : IsScalarTower R S E),
        Module.FaithfullyFlat R C ∧ StacksDraft.IndEtale R C ∧
          Module.FaithfullyFlat S E ∧ StacksDraft.IndEtale S E ∧
          (∀ (m : Ideal E) [m.IsMaximal], (m.comap (algebraMap C E)).IsMaximal) ∧
          (∀ (n : Ideal C) [n.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime n)))
    (h097G : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
      Algebra.IdentifiesLocalRings R S →
      ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S') (_ : Algebra R S')
          (_ : IsScalarTower R S S'),
        Module.FaithfullyFlat S S' ∧ Algebra.IsIndZariski S S' ∧ Algebra.IsIndZariski R S') :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra A B'),
      ∃ _ : IsScalarTower A B B', Module.FaithfullyFlat B B' ∧
        StacksDraft.IndEtale B B' ∧ StacksDraft.IndEtale A B' := by
  obtain ⟨C, E, _, _, _, _, _, _, _, _, hffC, hindC, hffE, hindE, hmax, hsh⟩ :=
    h097X A B fun q _ => (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B hAB
      (q.comap (algebraMap A B)) q rfl).2
  obtain ⟨D, _, _, _, _, hffD, hzED, hzCD⟩ := h097G C E
    (identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian C E
      (weaklyEtale_of_comp A C E (Algebra.weaklyEtale_of_ind_etale hindC)
        (weaklyEtale_comp A B E hAB (Algebra.weaklyEtale_of_ind_etale hindE))) hmax hsh)
  let _ : Algebra B D := ((algebraMap E D).comp (algebraMap B E)).toAlgebra
  have _ : IsScalarTower B E D := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra A D := ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A B D, IsScalarTower.algebraMap_apply B E D,
      ← IsScalarTower.algebraMap_apply A B E, IsScalarTower.algebraMap_apply C E D,
      ← IsScalarTower.algebraMap_apply A C E]
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.FaithfullyFlat.trans B E D,
    StacksDraft.indEtale_comp hindE (indEtale_of_isIndZariski _ _ hzED),
    StacksDraft.indEtale_comp hindC (indEtale_of_isIndZariski _ _ hzCD)⟩

end AlgebraicGeometry.ProEtale
