module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.Tactic.TFAE
public import StacksCore.Topology.Connected.ComponentSpace
public import StacksCore.Topology.ExtremallyDisconnected.Defs
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.FaithfullyFlatCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCharacterization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WContractibleCharacterization
public import StacksFrontier.RingTheory.IndZariski.Defs
public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The w-contractibility criterion: the arrows into and out of condition (2)

Lemma 0982 asserts that for a ring `A` the following three conditions are equivalent:

1. `A` is w-contractible, i.e. every faithfully flat weakly étale `A → B` has a retraction
   (Definition 0981);
2. every faithfully flat *ind-étale* `A → B` has a retraction;
3. `Spec A` is w-local, `π₀(Spec A)` is extremally disconnected, and `A_𝔪` is strictly
   henselian for every maximal ideal `𝔪 ⊆ A`.

`StacksFrontier.AlgebraicGeometry.ProEtale.WContractibleCharacterization` proves (1) ⇒ (2), and
the part of (2) ⇒ (3) that concerns condition (3)(c). This file adds the arrows that the source
derives from Proposition 097Z, from Lemma 09AZ and from Lemma 097A, each of those three taken as
an explicitly named hypothesis: `h097Z` for (2) ⇒ (1), `h09AZ` for (2) ⇒ (3)(a) and (3)(b), and
`h097A` together with `h09AZ` for (3) ⇒ (2). Composing them assembles the whole equivalence
relative to those three hypotheses, which is `wContractible_tfae_of_upstream`; the unconditional
form of Lemma 0982 is not proved here.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.ProEtale.isWContractible_of_ind_etale_retraction`: the implication
  (2) ⇒ (1) of Lemma 0982, from Proposition 097Z carried as a hypothesis.
* `AlgebraicGeometry.ProEtale.isWContractible_iff_ind_etale_retraction`: the equivalence
  (1) ⇔ (2) of Lemma 0982, from the same hypothesis.
* `AlgebraicGeometry.ProEtale.wLocalSpace_and_extremallyDisconnected_of_ind_etale_retraction`:
  the (3)(a) and (3)(b) components of (2) ⇒ (3), from Lemma 09AZ carried as a hypothesis.
* `AlgebraicGeometry.ProEtale.wLocalProperties_of_ind_etale_retraction` and
  `AlgebraicGeometry.ProEtale.wLocalProperties_of_isWContractible`: the implications
  (2) ⇒ (3) and (1) ⇒ (3) in full, from the same hypothesis.
* `AlgebraicGeometry.ProEtale.faithfullyFlat_of_forall_isMaximal_exists_comap_eq`: a flat
  algebra whose spectrum hits every maximal ideal of the base is faithfully flat. This is the
  source's standing remark that for a flat map faithful flatness is tested on closed points,
  and it assumes nothing about Lemma 0982.
* `AlgebraicGeometry.ProEtale.ind_etale_retraction_of_wLocalProperties`: the implication
  (3) ⇒ (2) of Lemma 0982, from Lemma 097A and Lemma 09AZ carried as hypotheses.
* `AlgebraicGeometry.ProEtale.wContractible_tfae_of_upstream`: the full `List.TFAE` of
  Lemma 0982, relative to Proposition 097Z, Lemma 09AZ and Lemma 097A.

## Implementation notes

Ind-étaleness is taken throughout in the single-universe categorical form
`ObjectProperty.ind.{u} (CommAlgCat.etale A) (CommAlgCat.of A B)`, with the index universe of
the filtered colimit pinned to the universe of the rings. That is the form in which
`StacksDraft.indEtale_iff` and `Algebra.isIndZariski_iff` state their universe-independent
counterparts, and leaving the index universe free would make the predicate depend on a second
universe parameter with no lemma relating two instantiations of it.

`h097Z` is Proposition 097Z: a weakly étale `A → B` admits a faithfully flat ind-étale
`B → B'` with `A → B'` ind-étale. `h09AZ` is Lemma 09AZ in full, as a three-element
`List.TFAE`; its implications (2) ⇒ (3) and (3) ⇒ (1) are used, through `List.TFAE.out`, whose
indices are one-based. In each case the extracted implication is bound to a `have` whose type
is written out, so that the compiler — and not the reader's count — decides which direction
`List.TFAE.out` delivered.

`h097A` is **part (2) of Lemma 097A, weakened to the three consequences the proof consumes**,
which makes the statement that carries it stronger rather than weaker. The source produces,
for a ring map `A → B` inducing algebraic residue field extensions and the radical ideal `I`
cutting out the closed points of the w-local `Spec A`, an ind-Zariski `B → C` with (a)
`B/IB → C/IC` an isomorphism, (b) `Spec C` w-local, (c) `Spec C → Spec A` w-local, and (d)
the closed points of `Spec C` the preimage of those of `Spec A`. Assumed here are: the
ind-Zariskiness, the *surjectivity* of `Spec (C/IC) → Spec (B/IB)` — the only part of (a) the
argument uses, phrased as a lifting statement for primes of `B` containing `IB` so that no
quotient map has to be named — and (c). Parts (b) and (d) are dropped: the sole use of the
w-locality of `Spec C` in the source is to see that every point specializes to a closed one,
and that is replaced by `Ideal.exists_le_maximal`, exactly as in
`StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.FaithfullyFlatCover`.

The proof of (3) ⇒ (2) then runs as in the source. Given faithfully flat ind-étale `A → B`,
Lemma 092R (`isSeparable_and_isAlgebraic_residueField_of_weaklyEtale`) supplies the residue
field hypothesis of 097A for `A → B`, and `I` is taken to be the vanishing ideal of the set of
closed points, whose zero locus is that set again because (3)(a) makes it closed. With `C` as
above, `A → C` is ind-étale (`StacksDraft.indEtale_comp`, an ind-Zariski algebra being
ind-étale) hence weakly étale, every maximal ideal of `C` contracts to a maximal ideal of `A`
because (c) carries closed points to closed points, and so `A → C` identifies local rings by
`identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian` together with (3)(c) — this is the
step that consumes Theorem 092Z. It is faithfully flat by
`faithfullyFlat_of_forall_isMaximal_exists_comap_eq`: a maximal ideal of `A` is in the image of
`Spec B` because `A → B` is faithfully flat, that prime contains `IB`, and the surjectivity
part of `h097A` lifts it to `C`. Finally implication (3) ⇒ (1) of `h09AZ` retracts `A → C`, and
the retraction restricts along `B → C`.

No statement here carries a `@[stacks]` attribute: `wContractible_tfae_of_upstream` is the
reduction of Lemma 0982 to Proposition 097Z, Lemma 09AZ and Lemma 097A, not Lemma 0982 itself.

## References

* [Stacks Project, Tag 0982](https://stacks.math.columbia.edu/tag/0982)
* [Stacks Project, Tag 0981](https://stacks.math.columbia.edu/tag/0981)
* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
* [Stacks Project, Tag 09AZ](https://stacks.math.columbia.edu/tag/09AZ)
* [Stacks Project, Tag 097A](https://stacks.math.columbia.edu/tag/097A)
* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 092R](https://stacks.math.columbia.edu/tag/092R)
* [Stacks Project, Tag 092Z](https://stacks.math.columbia.edu/tag/092Z)
* [Stacks Project, Tag 0975](https://stacks.math.columbia.edu/tag/0975)
-/

open CategoryTheory

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtale

/-- **Lemma 0982, (2) ⇒ (1), assuming Proposition 097Z.** If every faithfully flat ind-étale
algebra over `A` has a retraction, then `A` is w-contractible.

Given a faithfully flat weakly étale `A → B`, the hypothesis `h097Z` — which is
Proposition 097Z — produces a faithfully flat ind-étale `B → B'` with `A → B'` ind-étale.
Then `A → B'` is faithfully flat as a composite of faithfully flat maps, so it has a
retraction `σ : B' →ₐ[A] A`, and `σ` precomposed with `B → B'` retracts `A → B`. -/
theorem isWContractible_of_ind_etale_retraction (A : Type u) [CommRing A]
    (h097Z : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.WeaklyEtale A B →
      ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra A B'),
        ∃ _ : IsScalarTower A B B', Module.FaithfullyFlat B B' ∧
          StacksDraft.IndEtale B B' ∧ StacksDraft.IndEtale A B')
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C) (CommAlgCat.of A B) →
      Nonempty (B →ₐ[A] A)) :
    ProetaleWContractible.IsWContractible.{u, u} A := by
  intro B _ _ hwe hff
  obtain ⟨B', _, _, _, _, hffB, -, hindA⟩ := h097Z B ⟨hwe.1, hwe.2⟩
  have : Module.FaithfullyFlat A B' := Module.FaithfullyFlat.trans A B B'
  obtain ⟨σ⟩ := h B' inferInstance (StacksDraft.indEtale_iff.mp hindA)
  exact ⟨σ.comp (IsScalarTower.toAlgHom A B B')⟩

/-- **Lemma 0982, (1) ⇔ (2), assuming Proposition 097Z.** A ring is w-contractible if and only
if every faithfully flat ind-étale algebra over it has a retraction. The forward implication is
`nonempty_algHom_of_ind_etale_of_isWContractible` and needs no hypothesis; the converse is
`isWContractible_of_ind_etale_retraction`. -/
theorem isWContractible_iff_ind_etale_retraction (A : Type u) [CommRing A]
    (h097Z : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.WeaklyEtale A B →
      ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra A B'),
        ∃ _ : IsScalarTower A B B', Module.FaithfullyFlat B B' ∧
          StacksDraft.IndEtale B B' ∧ StacksDraft.IndEtale A B') :
    ProetaleWContractible.IsWContractible.{u, u} A ↔
      ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
        ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C) (CommAlgCat.of A B) →
        Nonempty (B →ₐ[A] A) :=
  ⟨fun hA B _ _ hff hind ↦ nonempty_algHom_of_ind_etale_of_isWContractible A hA B hff hind,
    isWContractible_of_ind_etale_retraction A h097Z⟩

/-- **Lemma 0982, the (3)(a) and (3)(b) components of (2) ⇒ (3), assuming Lemma 09AZ.** If
every faithfully flat ind-étale algebra over `A` has a retraction, then `Spec A` is w-local and
`π₀(Spec A)` is extremally disconnected.

An ind-Zariski algebra is ind-étale (`indEtale_of_isIndZariski`), so the hypothesis
specializes to condition (2) of Lemma 09AZ, whose condition (3) is exactly the conjunction
asserted here. -/
theorem wLocalSpace_and_extremallyDisconnected_of_ind_etale_retraction (A : Type u) [CommRing A]
    (h09AZ : List.TFAE
      [∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IdentifiesLocalRings A B → Nonempty (B →ₐ[A] A),
        ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IsIndZariski A B → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))])
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C) (CommAlgCat.of A B) →
      Nonempty (B →ₐ[A] A)) :
    WLocalSpace (PrimeSpectrum A) ∧
      ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) := by
  refine (h09AZ.out 2 3).mp ?_
  intro B _ _ hff hindZariski
  exact h B hff (StacksDraft.indEtale_iff.mp (indEtale_of_isIndZariski _ _ hindZariski))

/-- **Lemma 0982, (2) ⇒ (3), assuming Lemma 09AZ.** If every faithfully flat ind-étale algebra
over `A` has a retraction, then `Spec A` is w-local, `π₀(Spec A)` is extremally disconnected,
and `A` localized at any maximal ideal is strictly henselian. The first two components come
from Lemma 09AZ and the third from Lemma 097V. -/
theorem wLocalProperties_of_ind_etale_retraction (A : Type u) [CommRing A]
    (h09AZ : List.TFAE
      [∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IdentifiesLocalRings A B → Nonempty (B →ₐ[A] A),
        ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IsIndZariski A B → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))])
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C) (CommAlgCat.of A B) →
      Nonempty (B →ₐ[A] A)) :
    WLocalSpace (PrimeSpectrum A) ∧
      ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
      ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m) :=
  (wLocalSpace_and_extremallyDisconnected_of_ind_etale_retraction A h09AZ h).imp_right
    fun hed ↦ ⟨hed, fun m _ ↦ strictlyHenselian_atPrime_of_ind_etale_retraction A h m⟩

/-- **Lemma 0982, (1) ⇒ (3), assuming Lemma 09AZ.** A w-contractible ring has w-local spectrum,
extremally disconnected space of connected components, and strictly henselian local rings at
its maximal ideals. This composes the unconditional (1) ⇒ (2) with (2) ⇒ (3). -/
theorem wLocalProperties_of_isWContractible (A : Type u) [CommRing A]
    (h09AZ : List.TFAE
      [∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IdentifiesLocalRings A B → Nonempty (B →ₐ[A] A),
        ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IsIndZariski A B → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))])
    (hA : ProetaleWContractible.IsWContractible.{u, u} A) :
    WLocalSpace (PrimeSpectrum A) ∧
      ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
      ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m) :=
  wLocalProperties_of_ind_etale_retraction A h09AZ
    fun B _ _ hff hind ↦ nonempty_algHom_of_ind_etale_of_isWContractible A hA B hff hind

/-- **A flat algebra whose spectrum hits every maximal ideal of the base is faithfully flat.**
This is the fact the source uses "without further mention" in the proofs of Lemmas 09AZ and
0982: for a flat ring map, faithful flatness is equivalent to every closed point of the base
being in the image.

A prime `p` of `A` is contained in some maximal ideal `m` (`Ideal.exists_le_maximal`), the
hypothesis provides a prime of `C` over `m`, and going down for a flat algebra
(`Algebra.HasGoingDown.of_flat`) produces a prime of `C` over `p`. So the map on spectra is
surjective, and `Module.FaithfullyFlat.of_comap_surjective` applies. -/
@[ega "0 6.6.1" "(e) ⇒ (a)", sga "1 IV 2.6" "(ii bis)⇒(i)"]
theorem faithfullyFlat_of_forall_isMaximal_exists_comap_eq (A C : Type u) [CommRing A]
    [CommRing C] [Algebra A C] [Module.Flat A C]
    (h : ∀ m : Ideal A, m.IsMaximal →
      ∃ Q : Ideal C, ∃ _ : Q.IsPrime, Q.comap (algebraMap A C) = m) :
    Module.FaithfullyFlat A C := by
  refine Module.FaithfullyFlat.of_comap_surjective fun p ↦ ?_
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  obtain ⟨Q, hQ, hQm⟩ := h m hm
  have := hQ
  have : Q.LiesOver m := ⟨hQm.symm⟩
  have := hm
  have := p.isPrime
  obtain ⟨P, -, hPp, hPo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p.asIdeal) (q := m) Q hpm
  exact ⟨⟨P, hPp⟩, PrimeSpectrum.ext hPo.over.symm⟩

/-- **Lemma 0982, (3) ⇒ (2), assuming Lemma 097A and Lemma 09AZ.** If `Spec A` is w-local,
`π₀(Spec A)` is extremally disconnected and `A` is strictly henselian at each of its maximal
ideals, then every faithfully flat ind-étale algebra over `A` has a retraction.

`h097A` is part (2) of Lemma 097A restricted to the three consequences used here: for a ring
map `A → B` inducing algebraic residue field extensions and a radical ideal `I` cutting out the
closed points of `Spec A`, an ind-Zariski `B → C` for which every prime of `B` containing `IB`
is the contraction of a prime of `C` — the surjectivity half of the source's isomorphism
`B/IB ≅ C/IC` — and for which `Spec C → Spec A` is w-local. `h09AZ` is Lemma 09AZ in full; its
implication (3) ⇒ (1) is the one consumed.

The argument is the source's: `I` is the vanishing ideal of the closed points, `C` comes from
`h097A`, `A → C` is ind-étale hence weakly étale, it identifies local rings by
`identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian` and it is faithfully flat by
`faithfullyFlat_of_forall_isMaximal_exists_comap_eq`, so 09AZ retracts it; restricting the
retraction along `B → C` retracts `A → B`. -/
theorem ind_etale_retraction_of_wLocalProperties (A : Type u) [CommRing A]
    (h097A : ∀ (B : Type u) [CommRing B] [Algebra A B],
      WLocalSpace (PrimeSpectrum A) →
      (∀ q : Ideal B, ∀ [q.IsPrime],
        letI := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q
          (algebraMap A B) rfl).toAlgebra
        Algebra.IsAlgebraic (q.comap (algebraMap A B)).ResidueField q.ResidueField) →
      ∀ I : Ideal A, I.IsRadical →
        PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A) →
        ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Algebra A C)
            (_ : IsScalarTower A B C),
          Algebra.IsIndZariski B C ∧
            (∀ q : Ideal B, ∀ _ : q.IsPrime, I.map (algebraMap A B) ≤ q →
              ∃ Q : Ideal C, ∃ _ : Q.IsPrime, Q.comap (algebraMap B C) = q) ∧
            IsWLocalMap (PrimeSpectrum.comap (algebraMap A C)))
    (h09AZ : List.TFAE
      [∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IdentifiesLocalRings A B → Nonempty (B →ₐ[A] A),
        ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IsIndZariski A B → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))])
    (hwl : WLocalSpace (PrimeSpectrum A))
    (hed : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)))
    (hsh : ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m))
    (B : Type u) [CommRing B] [Algebra A B] (hffB : Module.FaithfullyFlat A B)
    (hindB : ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C)
      (CommAlgCat.of A B)) :
    Nonempty (B →ₐ[A] A) := by
  have _ : WLocalSpace (PrimeSpectrum A) := hwl
  have hindB' : StacksDraft.IndEtale A B := StacksDraft.indEtale_iff.mpr hindB
  have hwB : Algebra.WeaklyEtale A B := Algebra.weaklyEtale_of_ind_etale hindB'
  set I : Ideal A := PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum A)) with hIdef
  have hIrad : I.IsRadical := PrimeSpectrum.isRadical_vanishingIdeal _
  have hIz : PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A) := by
    rw [hIdef, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact WLocalSpace.isClosed_closedPoints.closure_eq
  obtain ⟨C, _, _, _, _, hzBC, hsurjq, hwlmap⟩ := h097A B hwl
    (fun q _ => (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B hwB
      (q.comap (algebraMap A B)) q rfl).2) I hIrad hIz
  have hwAC : Algebra.WeaklyEtale A C := Algebra.weaklyEtale_of_ind_etale
    (StacksDraft.indEtale_comp hindB' (indEtale_of_isIndZariski _ _ hzBC))
  have _ : Module.Flat A C := hwAC.flat
  have hmax : ∀ (m : Ideal C), ∀ [m.IsMaximal], (m.comap (algebraMap A C)).IsMaximal := by
    intro m _
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (hwlmap.isClosed_singleton
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal
          (⟨m, inferInstance⟩ : PrimeSpectrum C)).mpr inferInstance))
  have hid : Algebra.IdentifiesLocalRings A C :=
    identifiesLocalRings_of_weaklyEtale_of_strictlyHenselian A C hwAC hmax hsh
  have hffC : Module.FaithfullyFlat A C := by
    refine faithfullyFlat_of_forall_isMaximal_exists_comap_eq A C fun m hm ↦ ?_
    have hmp : m.IsPrime := hm.isPrime
    have hmem : (⟨m, hmp⟩ : PrimeSpectrum A) ∈ closedPoints (PrimeSpectrum A) :=
      mem_closedPoints_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm)
    have hIm : (I : Set A) ⊆ m := by
      rw [← hIz] at hmem
      exact (PrimeSpectrum.mem_zeroLocus _ _).mp hmem
    obtain ⟨qb, hqb⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) ⟨m, hmp⟩
    have hqbc : qb.asIdeal.comap (algebraMap A B) = m := by
      rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) qb, hqb]
    have hmaple : I.map (algebraMap A B) ≤ qb.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hqbc]
      exact hIm
    obtain ⟨Q, hQ, hQq⟩ := hsurjq qb.asIdeal qb.isPrime hmaple
    refine ⟨Q, hQ, ?_⟩
    rw [IsScalarTower.algebraMap_eq A B C, ← Ideal.comap_comap, hQq, hqbc]
  have h09AZ1 : ∀ (D : Type u) [CommRing D] [Algebra A D], Module.FaithfullyFlat A D →
      Algebra.IdentifiesLocalRings A D → Nonempty (D →ₐ[A] A) :=
    (h09AZ.out 3 1).mp (And.intro hwl hed)
  obtain ⟨σ⟩ := h09AZ1 C hffC hid
  exact ⟨σ.comp (IsScalarTower.toAlgHom A B C)⟩

/-- **Lemma 0982 relative to Propositions 097Z and 097A and Lemma 09AZ.** The three conditions
of Lemma 0982 are equivalent once those three upstream results are granted. This is a reduction
of Lemma 0982 to them, not the tag itself.

The cycle is closed by four arrows: (1) ⇒ (2) and (2) ⇒ (3) are
`nonempty_algHom_of_ind_etale_of_isWContractible` and
`wLocalProperties_of_ind_etale_retraction`, (2) ⇒ (1) is
`isWContractible_of_ind_etale_retraction`, and (3) ⇒ (2) is
`ind_etale_retraction_of_wLocalProperties`. -/
theorem wContractible_tfae_of_upstream (A : Type u) [CommRing A]
    (h097Z : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.WeaklyEtale A B →
      ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra A B'),
        ∃ _ : IsScalarTower A B B', Module.FaithfullyFlat B B' ∧
          StacksDraft.IndEtale B B' ∧ StacksDraft.IndEtale A B')
    (h097A : ∀ (B : Type u) [CommRing B] [Algebra A B],
      WLocalSpace (PrimeSpectrum A) →
      (∀ q : Ideal B, ∀ [q.IsPrime],
        letI := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q
          (algebraMap A B) rfl).toAlgebra
        Algebra.IsAlgebraic (q.comap (algebraMap A B)).ResidueField q.ResidueField) →
      ∀ I : Ideal A, I.IsRadical →
        PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A) →
        ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Algebra A C)
            (_ : IsScalarTower A B C),
          Algebra.IsIndZariski B C ∧
            (∀ q : Ideal B, ∀ _ : q.IsPrime, I.map (algebraMap A B) ≤ q →
              ∃ Q : Ideal C, ∃ _ : Q.IsPrime, Q.comap (algebraMap B C) = q) ∧
            IsWLocalMap (PrimeSpectrum.comap (algebraMap A C)))
    (h09AZ : List.TFAE
      [∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IdentifiesLocalRings A B → Nonempty (B →ₐ[A] A),
        ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          Algebra.IsIndZariski A B → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))]) :
    List.TFAE
      [ProetaleWContractible.IsWContractible.{u, u} A,
        ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
          ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C)
            (CommAlgCat.of A B) → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
          ∀ (m : Ideal A) [m.IsMaximal],
            StrictlyHenselianLocalRing (Localization.AtPrime m)] := by
  tfae_have 1 → 2 := fun hA B _ _ hff hind ↦
    nonempty_algHom_of_ind_etale_of_isWContractible A hA B hff hind
  tfae_have 2 → 1 := fun h ↦ isWContractible_of_ind_etale_retraction A h097Z h
  tfae_have 2 → 3 := fun h ↦ wLocalProperties_of_ind_etale_retraction A h09AZ h
  tfae_have 3 → 2 := fun h ↦
    ind_etale_retraction_of_wLocalProperties A h097A h09AZ h.1 h.2.1 h.2.2
  tfae_finish

end AlgebraicGeometry.ProEtale

end
