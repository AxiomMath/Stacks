module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamHorizontal
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.EndomorphismFactorizationQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalBridge
public import StacksFrontier.AlgebraicGeometry.Crystalline.StrongLiftingEnvelope
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# Smooth presentations, their completed divided power envelopes, and the statement of 07LH

[Stacks, Lemma 60.21.4, Tag 07LH] is the independence of the de Rham computation of crystalline
cohomology from the chosen presentation.  With its references resolved, it reads in full:

> Assumptions as in Proposition [Stacks, Tag 07LG].  Let `A → P' → C` be ring maps with
> `A → P'` smooth and `P' → C` surjective with kernel `J'`.  Let `D'` be the `p`-adic completion
> of `D_{P', γ}(J')`.  Let `(M', ∇')` be the pair over `D'` corresponding to `ℱ`, see
> Lemma [Stacks, Tag 07L5].  Then the complex `M' ⊗^∧_{D'} Ω^*_{D'}` computes
> `RΓ(Cris(X/S), ℱ)`.

[Stacks, Tag 07LG] itself is stated in this library as
`Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionDeRham.lean`, over the ring `D` of
[Stacks, Tag 07J8] — the `p`-adic completion of the divided power envelope of the kernel of a
*polynomial* presentation.  This module builds the ring `D'` of the lemma for a *smooth*
presentation and writes the lemma down.

## Main definitions

* `Crystalline.pAdicCompletionDPRing` — the `p`-adic completion of a divided power ring, as a
  divided power ring: the completion of the ring, the completed divided power ideal of
  [Stacks, Tag 07KD] part (2), and the extension of the divided powers to it of part (3).
* `Crystalline.SmoothPresentation` — **the datum `A → P' → C` of [Stacks, Tag 07LH]** in the
  standing affine situation of [Stacks, Tag 07MD]: a smooth `A`-algebra `P'`, a surjection
  `P' → C`, and the commutation of the triangle.
* `Crystalline.SmoothPresentation.envelope` — the divided power envelope `D_{P', γ}(J')` of
  `J' = ker(P' → C)`.
* `Crystalline.SmoothPresentation.completedEnvelope` — **the divided power ring `D'`**, the
  `p`-adic completion of that envelope.
* `Crystalline.SmoothPresentation.baseHom` — the structure map `A → D'`.
* `Crystalline.SmoothPresentation.ofFinitePolynomialPresentation` — a smooth presentation built
  from a surjection `A[x_1, …, x_n] → C`, which is what inhabits the datum.
* `Crystalline.GlobalCrystallineSituation.SmallSite.pairOverEnvelope` — the pair `(M, ∇)` over
  `D` that [Stacks, Tag 07JG] attaches to a quasi-coherent `ℱ`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.basePairOverSmooth` — **the pair `(M', ∇')`
  over `D'` corresponding to `ℱ`**, as `Crystalline.Pair.baseChange` along the map `a : D → D'`
  of [Stacks, Lemma 60.17.5, Tag 07L5].
* `Crystalline.GlobalCrystallineSituation.SmallSite.smoothDeRhamComplex` — the complex
  `M' ⊗^∧_{D'} Ω^*_{D'}`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LH` — **the statement of
  [Stacks, Tag 07LH]**.
* `Crystalline.GlobalCrystallineSituation.SmallSite.comparisonAlpha` — **the map `α` of the
  proof of [Stacks, Tag 07LH]**, the base change map of completed de Rham complexes along
  `a : D → D'` for a graded comparison of forms.  It is `Crystalline.CompletedDeRham.
  baseChangeComplexHom` and nothing else: it is constructed, not quantified over.
* `Crystalline.GlobalCrystallineSituation.SmallSite.backChangedConnection` — the base change of
  `∇'` along `b : D' → D`, the connection of the pair that the second assertion of
  [Stacks, Lemma 60.17.5, Tag 07L5] identifies with `(M, ∇)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.gammaOfHorizontalEquiv` — that
  identification **read on the complexes**, from the horizontal `D`-linear bijection of pairs
  that the second assertion of [Stacks, Lemma 60.17.5, Tag 07L5] produces.  The bijection is a
  hypothesis; nothing here proves that assertion.
* `Crystalline.GlobalCrystallineSituation.SmallSite.comparisonBeta` — **the map `β` of the proof
  of [Stacks, Tag 07LH]**: the base change map along `b` followed by that identification, the
  identification being the only thing about `β` that is not determined by `b` and the graded
  comparison along it.

## Main results

* `Crystalline.SmoothPresentation.ideal_map_le` — the divided power ideal `I` of `A` maps into
  `J'`, so that the envelope of `J'` relative to `(A, I, γ)` is defined.
* `Crystalline.SmoothPresentation.quotientEquiv` — the quotient of `D_{P', γ}(J')` by its
  divided power ideal is `C`.  This is [Stacks, Tag 07HA] for this presentation.
* `Crystalline.SmoothPresentation.isNilpotent_quotient` — consequently `p` is nilpotent in that
  quotient, which is what lets the divided powers extend to the `p`-adic completion and so makes
  `D'` exist.
* `Crystalline.GlobalCrystallineSituation.SmallSite.isIso_of_comp_id_of_isIso_comp` — a map with
  a left inverse whose other composite is invertible is invertible.  This is the retract step of
  the proof of [Stacks, Tag 07LH].
* `Crystalline.GlobalCrystallineSituation.SmallSite.computes07LH_of_computes07LG` — the proof of
  [Stacks, Tag 07LH] from [Stacks, Tag 07LG].  The two de Rham base change maps are
  **constructed**, as `...SmallSite.comparisonAlpha` and `...SmallSite.comparisonBeta`; what is
  carried as a hypothesis is the graded comparison of forms in each direction, the
  identification of `(M, ∇)` with the base change of `(M', ∇')` along `b` — the second
  assertion of [Stacks, Tag 07L5] — and the two assertions `hab`, `hba` of the source's proof,
  now stated about those constructed maps.  The retract between the rings is available, as
  `Crystalline.exists_completedEnvelopeRetract`; what is missing is the functoriality that
  would carry it to the complexes.
* `Crystalline.GlobalCrystallineSituation.SmallSite.isIso_homologyMap_comparison_of_transport`
  — **`hba` from the factorization of `ρ = b ∘ a`.**  The source proves `hba` by factoring `ρ`
  through the `p`-adic completion of a divided power polynomial algebra; this is that argument
  instantiated at the constructed `α` and `β`, through
  `Crystalline.CompletedDeRham.isIso_homologyMap_of_transport`.  So `hba` is not a
  hypothesis standing in for the whole of [Stacks, Lemma 60.20.2, Tag 07LD]: it follows from the
  factorization data, that lemma's completed clause for the single map `ν : D → D⟨ξ_i⟩^∧`, and
  the invertibility on homology of the base change along `τ` out of the `σ` copy.
* `Crystalline.GlobalCrystallineSituation.SmallSite.computes07LH_of_computes07LG_of_transport`
  — `...SmallSite.computes07LH_of_computes07LG` with `hba` replaced by that factorization data.
* `Crystalline.GlobalCrystallineSituation.SmallSite.isIso_homologyMap_comparison_of_factorization`,
  `...SmallSite.computes07LH_of_computes07LG_of_factorization` — variants of those two in
  which `s` and `incl` are required to land in the *same* complex and `α` to be an endomorphism
  of it.  **No base change data can satisfy that shape**, for the reason set out at the two
  results above, and they are superseded by those two.

## What is and is not proved

**No tag attribute is placed anywhere in this module.** [Stacks, Tag 07LH] is proved, by a
different route (the retract of [Stacks, Tag 07L5] together with the stratification of the crystal
and the universal property of `D(1)`), as
`Crystalline.GlobalCrystallineSituation.SmallSite.smoothPresentationPair_computesCohomology` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SmoothPresentationCohomology07LH.lean`.
`Computes07LH` is a definition of a proposition, and this module does not establish it. What *is*
proved here is everything about the ring `D'`: that the envelope of a smooth presentation has `C`
for its quotient by its divided power ideal, hence that `p` is nilpotent there, hence that the
completed divided power ring `D'` of the lemma exists for every smooth presentation; the *pair*
`(M', ∇')` the lemma speaks of, as the base change of the pair over `D` of [Stacks, Tag 07JG]; the
**retract step** of the lemma's proof, as `...SmallSite.computes07LH_of_computes07LG`; and the
**factorization step**, as `...SmallSite.isIso_homologyMap_comparison_of_transport`, which removes
`hba` from the hypotheses in favour of the factorization of `ρ = b ∘ a` that the source's proof of
that step uses.

What the route of this module would still need, beyond [Stacks, Tag 07LG] and the second
assertion of [Stacks, Tag 07L5], is: the construction of the ring `D⟨ξ_i⟩^∧` and of the divided
power maps `σ`, `τ`, `ν` and the automorphism `α` of the source's proof, read on the completed de
Rham complexes; the invertibility on homology of the base change along `τ` out of the complex base
changed along `σ`, for which this library has nothing —
`Crystalline.isIso_homologyMap_tauComplexHom` is the corresponding statement for `ν`, a different
map, since `τ ∘ ν = id_D` whereas `τ ∘ σ = ρ`; and the completed clause of
[Stacks, Lemma 60.20.2, Tag 07LD] for `ν`.  The last is
the theorem `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamPerturbation.lean`, whose output is
read as a quasi-isomorphism by
`Crystalline.CompletedDeRham.isIso_homologyMap_of_degreewiseHomotopyRetract`; what stands between
the two is that `exists_twistedHomotopyEquiv` produces its differential `d_L` on the base-level
complex and its map `ι'` existentially, so they must still be identified with the de Rham
differential of `M ⊗^∧_D Ω^*_D` and with the base change map along `ν`, and that identification
also carries the standard comparison of `M ⊗^∧_D Ω^*_{D⟨ξ_i⟩^∧}`, the form in which the source
states [Stacks, Tag 07LD], with `(M ⊗^∧_{D, ν} D⟨ξ_i⟩^∧) ⊗^∧ Ω^*_{D⟨ξ_i⟩^∧}`, the form a base
change produces.

### How the correspondence `ℱ ↦ (M', ∇')` is handled

The source defines "the pair over `D'` corresponding to `ℱ`" through the equivalence of
[Stacks, Lemma 60.17.5, Tag 07L5]: that lemma produces a polynomial presentation `A → P → C` and
divided power maps `a : D → D'`, `b : D' → D` over `A` and over `C` with `a ∘ b = id_{D'}`, and
the corresponding pair over `D'` is the base change along `a` of the pair over `D` which
[Stacks, Tag 07JG] attaches to `ℱ`.

That base change **is** available: it is `Crystalline.Pair.baseChange` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChange.lean`, built on
`Crystalline.CompletedConnection.baseChange`, the completed analogue of Remark
[Stacks, Tag 07KJ].  So `Computes07LH` **names** its pair, as
`...SmallSite.basePairOverSmooth`, rather than binding it existentially: it is the base change
along `a` of `...SmallSite.pairOverEnvelope`, which is `Crystalline.functor07JG` applied to `ℱ`.
Naming it is strictly stronger than binding it existentially, and so
strictly closer to the lemma.

The map `a` enters as the `Algebra ↑Dr ↑T.completedEnvelope` instance together with the
comparison of one-forms `psi` and its compatibility `hpsi`; of the four conditions of a pair,
[Stacks, Tag 07JB] and [Stacks, Tag 07JC] are discharged by the base change and the remaining
three are the hypotheses `hcoord`, `hint`, `hqn`, which [Stacks, Tag 07L5] asserts of
`(M', ∇')`.

The maps `a` and `b` themselves do exist in this library.  The first assertion of
[Stacks, Tag 07L5] — for a surjection `q : P ↠ P'` of presentations, the canonical map
`ρ : D_{P, γ}(J) → D_{P', γ}(J')` of [Stacks, Tag 07HB] together with divided power morphisms
`a : D̂ → D̂'` and `b : D̂' → D̂` between the `p`-adic completions satisfying `a ∘ b = id`, `a`
being the completion of `ρ` — is `Crystalline.exists_completedEnvelopeRetract` of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean`.

Two things keep that from discharging anything here.  It produces `a` and `b` existentially for
a presentation `P` of its own choosing, and nothing identifies that `a` with the
`Algebra ↑Dr ↑T.completedEnvelope` instance this module carries, nor `Dr` with the envelope of
any particular `P`.  The *second* assertion of [Stacks, Tag 07L5], the equivalence between
the categories of pairs over `D` and over `D'`, is stated with both directions in
`Crystalline.exists_presentation_retract_pairEquivalence` of `EnvelopeRetractEquivalence.lean`
(the direction `F ∘ G = id` on complexes is also
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract`); the direction
`G ∘ F ≅ id`, the one this module needs, uses the Taylor comparison, whose horizontality the
source omits.  This module does not connect its `Algebra` instances to that equivalence, so
`Computes07LH` is a proposition *about* given `07L5` data, exactly as the source's lemma is.

The complex is not loose either.  Its terms are `M' ⊗̂_{D'} Ω^i_{D'}` and its differential is
`Crystalline.CompletedDeRham.differential`, the de Rham differential
`∇'(m ⊗ ω) = ∇'(m) ∧ ω + m ⊗ d ω` of the pair's own connection, which
`Crystalline.CompletedDeRham.differential_eq_of_val` shows is determined and not a choice.

### What the reduction to [Stacks, Tag 07LG] does and does not establish

`...SmallSite.computes07LH_of_computes07LG` carries out the proof of the lemma from
[Stacks, Tag 07LG].  The two base change maps `α`, `β` of de Rham complexes along `a` and `b`
are **constructed**: `α` is `...SmallSite.comparisonAlpha`, which is
`Crystalline.CompletedDeRham.baseChangeComplexHom` for a graded comparison of forms along `a`,
and `β` is `...SmallSite.comparisonBeta`, the same construction along `b` followed by the
identification of `(M, ∇)` with the base change of `(M', ∇')` along `b`.  They used to be
hypotheses, and that was a defect and not an economy: with `α` and `β` arbitrary and
`β ≫ α = 𝟙` their only constraint, `H(α) ≫ H(β)` is an idempotent, a split idempotent need not
be invertible, and the hypothesis `hba` that it *is* invertible was consequently
undischargeable for every input — [Stacks, Tag 07LD] speaks about base change maps, and
arbitrary maps of complexes carry no information identifying them as such.

What remains carried as hypotheses is: the graded comparisons of forms along `a` and `b`, which
are data and are unremovable for abstract graded families; the identification just named, which
is the direction `G ∘ F ≅ id` of the **second assertion of [Stacks, Lemma 60.17.5, Tag 07L5]**
and rests on [Stacks, Proposition 60.17.4, Tag 07JH]; `hab`, that `β ≫ α` is the identity,
which is the
retract `a ∘ b = id_{D'}` of [Stacks, Tag 07L5] read on complexes; and `hba`, that `α ≫ β` is a
quasi-isomorphism, which the source deduces from the **completed** clause of
[Stacks, Lemma 60.21.2, Tag 07LD].  Both clauses of [Stacks, Tag 07LD] are proved, as
`Crystalline.DividedPowerPolynomial.stacks07LD` of
`Differentials/RelativePoincareModuleQuasiIso.lean` (the completed clause is
`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`); this module does not
derive `hba` from it.  The comparison of divided power forms along `B → B⟨x_w⟩` in every degree
is `Crystalline.mapDifferentialFormsOfDPMorphism` and, completed,
`Crystalline.completedMapDifferentialForms`.  The `M = D` case of the completed clause is also
`Crystalline.completedRelativeFormsHomotopy_identity`, but that homotopy does not tensor up: the
differential of `M ⊗̂_D Ω^*` is the connection-twisted `∇m ∧ ω + m ⊗ dω`, so a homotopy against
`1_M ⊗ d` is not a homotopy against it.

For `hab` the functoriality of `Crystalline.CompletedDeRham.baseChangeComplexHom` is now
available in both halves: the identity case as
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_id`, and the composition case on the
complexes as `Crystalline.CompletedDeRham.baseChangeComplexHom_comp` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeComposite.lean`, which
rests on the horizontality
`Crystalline.CompletedConnection.baseChange_baseChangeComposite` of the comparison
`Crystalline.CompletedConnection.baseChangeComposite` along which the composition law is stated.
What still blocks `hab` is the identification of the `Algebra` instances carried here with the
maps `a`, `b` that `Crystalline.exists_completedEnvelopeRetract` produces existentially, and the
compatibility of `gamma` with the two base changes.

What the theorem itself proves is the retract step,
`...SmallSite.isIso_of_comp_id_of_isIso_comp`, and the transport of the comparison with
crystalline cohomology from the polynomial presentation to the smooth one.

### The hypotheses `Computes07LH` carries, exhaustively

Besides the global crystalline situation `S` and the smooth presentation `T`:

* `[IsAffine S.X]`, `[IsAffine S.S.scheme]` and `hp : IsNilpotent (S.p : Γ(X, 𝒪_X))`.  These are
  **not optional**: [Stacks, Tag 07LH] opens "assumptions as in Proposition [Stacks, Tag 07LG]",
  which opens "assumptions as in Proposition [Stacks, Tag 07JN]", which is the affine case with
  `p` nilpotent; `Computes07LG` carries exactly these three.  They are also what makes the
  affine situation of [Stacks, Tag 07MD] available at all, through
  `Crystalline.GlobalCrystallineSituation.affineSituation`, and `T` is a presentation in that
  situation.
* the polynomial presentation side of [Stacks, Tag 07LG]: the divided power ring `Dr = D` with
  its structure map `g : A → D`, its graded forms `Om` with the divided power derivation `der`
  of [Stacks, Tag 07HR] and the coordinate differentials `dx`, and the reduction datum `R` of
  [Stacks, Tag 07JG].  Without these the pair over `D` — and so the pair over `D'` — cannot be
  named.
* the graded family of forms `Om' : ℕ → Type u` of `D'` with its wedge product `wedge'`, its de
  Rham differential `deRham'`, the divided power derivation `der' : D' → Ω_{D'}` of
  [Stacks, Tag 07HR], the coordinate differentials `dx'`, and the Leibniz rule `hleib'`.  These
  are carried exactly as `Computes07LG` carries them: the library does not identify the completed
  divided power forms of `D'`, so the family is a parameter and the proposition asserts nothing
  for a family that is not the genuine one.

The hypothesis on the coefficients is the source's own and is stated **once**:
`SheafOfModules.IsQuasicoherentOnSite`, condition (1) of [Stacks, Tag 07IT].  The crystal
condition `Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal`, condition (2), is
*not* also assumed — asking for both would be strictly stronger than the source asks and would
make the proposition weaker than its tag.  What is carried instead, exactly as `Computes07LG`
carries it, is the implication (1) ⟹ (2) of [Stacks, Tag 07IT]: with it, quasi-coherence of `ℱ`
is the source's "crystal in quasi-coherent modules", and the proposition quantifies over neither
more nor fewer coefficients than the lemma does.

The prime is `S.p` throughout, not a free parameter: `D'` is the `S.p`-adic completion of the
envelope, so the complex and the situation must use the same prime.

### Inhabitation

`Crystalline.SmoothPresentation` is inhabited exactly when `C` is a quotient of a smooth
`A`-algebra, and `Crystalline.SmoothPresentation.ofFinitePolynomialPresentation` is the witness
in the case the source has in mind: a surjection `A[x_1, …, x_n] → C` from a polynomial algebra
on *finitely many* variables, which is a smooth `A`-algebra.  Finiteness matters: `Algebra.Smooth`
is formal smoothness together with finite presentation, so the tautological presentation
`A[x_c : c ∈ C] → C` — the one `Crystalline.canonicalPresentation` uses, and the one
[Stacks, Tag 07JN] works over — is formally smooth but is *not* a smooth presentation unless `C`
is finite.  For a `C` that is not of finite type over `A` the datum may be empty, and then the
proposition says nothing about that situation; that is a property of the tag, which assumes a
smooth presentation to be given.

Nothing here claims that the *conclusion* is non-vacuous in another sense: as with
`Computes07LG`, stated over a reduction datum `Crystalline.Reduction07JG` which the library
assembles only from levelwise inputs (`...SmallSite.reduction07JGWholeSpaceOfLevelwise`), a proof
is what would settle that.  [Stacks, Tag 07LH] itself is
`...SmallSite.smoothPresentationPair_computesCohomology`.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07HA](https://stacks.math.columbia.edu/tag/07HA)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u v uI uI'

namespace Crystalline

/-! ### The `p`-adic completion of a divided power ring -/

/-- **The `p`-adic completion of a divided power ring `(E, K, δ)`, as a divided power ring.**
The underlying ring is `AdicCompletion (p) E`, the ideal is the completed divided power ideal of
[Stacks, Tag 07KD] part (2), and the divided powers are their extension to it of part (3).  The
hypothesis is that `p` is nilpotent in `E ⧸ K`, which is what [Stacks, Tag 07KD] needs. -/
public noncomputable abbrev pAdicCompletionDPRing (E : DividedPowerRing.{v}) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk E.ideal (p : E))) :
    DividedPowerRing.{v} :=
  ⟨AdicCompletion (DividedPowers.pAdicIdeal (A := (E : Type v)) p) (E : Type v),
    DividedPowers.completionIdeal E.ideal p hp,
    (DividedPowers.completedDividedPowers E.ideal E.dividedPowers p hp).1⟩

/-! ### Smooth presentations and their completed envelopes -/

/-- **The datum `A → P' → C` of [Stacks, Tag 07LH]** in the standing affine situation
[Stacks, Tag 07MD]: a smooth `A`-algebra `P'` together with a surjection `P' → C` whose
composition with `A → P'` is the structure map `A → C` of the situation.

Smoothness is Mathlib's `Algebra.Smooth`, formal smoothness together with finite presentation;
it is the hypothesis the source makes, and it is used by a *proof* of [Stacks, Tag 07LH] only
through the strong lifting property of [Stacks, Tag 07K4], as
`Crystalline.exists_dpMorphism_envelope_of_smooth` records.  It is a field here because without
it the datum would be more general than the lemma's. -/
public structure SmoothPresentation (s : AffineCrystallineSituation.{u, v}) where
  /-- The smooth `A`-algebra `P'`. -/
  ring : Type u
  /-- Its commutative ring structure. -/
  [commRing : CommRing ring]
  /-- Its `A`-algebra structure, which is the ring map `A → P'`. -/
  [algebra : Algebra (s.A : Type u) ring]
  /-- `A → P'` is smooth. -/
  [smooth : Algebra.Smooth (s.A : Type u) ring]
  /-- The map `P' → C`. -/
  toTarget : ring →+* s.C
  /-- It is surjective, so that its kernel is the ideal `J'` of the lemma. -/
  surjective_toTarget : Function.Surjective toTarget
  /-- The triangle commutes: `A → P' → C` is the structure map `A → C`. -/
  toTarget_comp_algebraMap :
    toTarget.comp (algebraMap (s.A : Type u) ring) = algebraMap (s.A : Type u) s.C

attribute [instance] SmoothPresentation.commRing SmoothPresentation.algebra
  SmoothPresentation.smooth

namespace SmoothPresentation

variable {s : AffineCrystallineSituation.{u, v}} (T : SmoothPresentation s)

/-- **The ideal `J' = ker(P' → C)`** of [Stacks, Tag 07LH]. -/
public abbrev kernel : Ideal T.ring := RingHom.ker T.toTarget

/-- **The divided power ideal `I` of `A` maps into `J'`**, because `I` dies in `C` and the
triangle `A → P' → C` commutes.  This is what makes the divided power envelope of `J'` relative
to `(A, I, γ)` defined. -/
public theorem ideal_map_le :
    (s.A).ideal.map (algebraMap (s.A : Type u) T.ring) ≤ T.kernel := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  show T.toTarget (algebraMap (s.A : Type u) T.ring a) = 0
  have h : T.toTarget (algebraMap (s.A : Type u) T.ring a) =
      algebraMap (s.A : Type u) s.C a :=
    RingHom.congr_fun T.toTarget_comp_algebraMap a
  rw [h]
  have ha' : algebraMap (s.A : Type u) s.C a ∈
      (s.A).ideal.map (algebraMap (s.A : Type u) s.C) :=
    Ideal.mem_map_of_mem _ ha
  rw [s.ideal_map_eq_bot] at ha'
  exact ha'

/-- **The divided power envelope `D_{P', γ}(J')`** of [Stacks, Tag 07LH], for the ideal
`J' = ker(P' → C)` of the smooth presentation relative to the divided power base `(A, I, γ)`. -/
public noncomputable def envelope :
    DividedPowerEnvelope s.A (algebraMap (s.A : Type u) T.ring) T.kernel T.ideal_map_le :=
  dividedPowerEnvelope s.A (algebraMap (s.A : Type u) T.ring) T.kernel T.ideal_map_le

/-- **The quotient of `D_{P', γ}(J')` by its divided power ideal is isomorphic to `C`.**  This is
[Stacks, Tag 07HA] — `Crystalline.dividedPowerEnvelope_factorization` — for this presentation:
the envelope factors `P' → P' ⧸ J'` and its divided power ideal is exactly the kernel of the
second map, and `P' ⧸ J'` is `C` because `P' → C` is surjective with kernel `J'`.  The
isomorphism is asserted rather than named because [Stacks, Tag 07HA] produces the factoring map
existentially. -/
public theorem nonempty_ringEquiv_quotient :
    Nonempty ((T.envelope.object ⧸ T.envelope.object.ideal) ≃+* s.C) := by
  obtain ⟨-, q, -, -, hsurj, hker, -⟩ :=
    dividedPowerEnvelope_factorization s.A (algebraMap (s.A : Type u) T.ring) T.kernel
      T.ideal_map_le T.envelope
  exact ⟨((Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)).trans
      (RingHom.quotientKerEquivOfSurjective T.surjective_toTarget)⟩

/-- **`p` is nilpotent in `D_{P', γ}(J')` modulo its divided power ideal**, that quotient being
`C`, where `p` is nilpotent by the standing assumption of [Stacks, Tag 07MD].  This is the
hypothesis [Stacks, Tag 07KD] needs in order to extend the divided powers to the `p`-adic
completion, so it is what makes `D'` exist. -/
public theorem isNilpotent_quotient :
    IsNilpotent (Ideal.Quotient.mk T.envelope.object.ideal ((s.p : T.envelope.object))) := by
  obtain ⟨e⟩ := T.nonempty_ringEquiv_quotient
  simpa only [map_natCast] using s.prime_nilpotent.map e.symm.toRingHom

/-- **The divided power ring `D'` of [Stacks, Tag 07LH]**: the `p`-adic completion of the divided
power envelope `D_{P', γ}(J')` of the smooth presentation, with its completed divided power ideal
and the extension of the divided powers to it. -/
public noncomputable abbrev completedEnvelope : DividedPowerRing.{u} :=
  pAdicCompletionDPRing T.envelope.object s.p T.isNilpotent_quotient

/-- **The structure map `A → D'`**: the map to the envelope followed by the map to its `p`-adic
completion. -/
public noncomputable def baseHom : (s.A : Type u) →+* (T.completedEnvelope : Type u) :=
  (algebraMap (T.envelope.object : Type u) (T.completedEnvelope : Type u)).comp
    T.envelope.structureMap.toRingHom

/-- **A surjection `A[x_1, …, x_n] → C` from a polynomial algebra on finitely many variables is a
smooth presentation.**  This is what inhabits `Crystalline.SmoothPresentation`: a polynomial
algebra on a finite set of variables is formally smooth and of finite presentation, hence smooth.
Finiteness is needed for the second half, so the tautological presentation on the variables `C`
is not an instance of this unless `C` is finite. -/
public noncomputable def ofFinitePolynomialPresentation (s : AffineCrystallineSituation.{u, v})
    {n : ℕ} (f : MvPolynomial (Fin n) (s.A : Type u) →ₐ[(s.A : Type u)] s.C)
    (hf : Function.Surjective f) :
    SmoothPresentation s where
  ring := MvPolynomial (Fin n) (s.A : Type u)
  smooth := ⟨inferInstance, inferInstance⟩
  toTarget := f.toRingHom
  surjective_toTarget := hf
  toTarget_comp_algebraMap := f.comp_algebraMap

end SmoothPresentation

/-! ### The statement of [Stacks, Tag 07LH] -/

namespace GlobalCrystallineSituation.SmallSite

/-- **Reading a quasi-coherent `ℱ` as a crystal in quasi-coherent modules changes nothing about
`ℱ`.**  The object of the source category of [Stacks, Proposition 60.17.4, Tag 07JH] produced by
`...SmallSite.toQuasiCoherentCrystal` has `ℱ` for its underlying sheaf, so the cohomology the
statement of [Stacks, Tag 07LH] below compares against is the cohomology of `ℱ` itself. -/
public theorem toQuasiCoherentCrystal_obj (S : GlobalCrystallineSituation.{u})
    (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
      F.IsQuasicoherentOnSite → IsSheafCrystal F)
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) :
    (toQuasiCoherentCrystal S h07IT F hF).obj = F :=
  rfl

/-- **A map with a left inverse whose other composite is invertible is itself invertible.**  If
`g ≫ f = 𝟙` and `f ≫ g` is an isomorphism, then `f` is an isomorphism and `g` is its inverse.

This is the retract step of the proof of [Stacks, Lemma 60.21.4, Tag 07LH], where `f` and `g` are
the base change maps of de Rham complexes induced by the maps `a : D → D'` and `b : D' → D` of
[Stacks, Lemma 60.17.5, Tag 07L5]: the composite induced by `a ∘ b = id_{D'}` is the identity,
and the composite induced by `b ∘ a` is a quasi-isomorphism. -/
public theorem isIso_of_comp_id_of_isIso_comp {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) (hgf : g ≫ f = 𝟙 Y) (hfg : IsIso (f ≫ g)) : IsIso f := by
  have h : f ≫ g = 𝟙 X := by
    rw [← cancel_mono (f ≫ g), Category.id_comp, Category.assoc, reassoc_of% hgf]
  exact ⟨g, h, hgf⟩

section Statement

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (Dr : DividedPowerRing.{u}) (g : ((affineSituation S hp).A : Type u) →+* Dr)
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module (Dr : Type u) (Om i)]
  [Module (Dr : Type u)ᵐᵒᵖ (Om 1)] [IsCentralScalar (Dr : Type u) (Om 1)]
  (der : DividedPowerDerivation ((affineSituation S hp).A : Type u) Dr g (Om 1))
  {ι : Type uI} (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun ((affineSituation S hp).A : Type u) Dr g (Om 1) der))
  (R : Reduction07JG S ((affineSituation S hp).A : Type u) Dr g (Om 1) der S.p dx hp)
  (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
    F.IsQuasicoherentOnSite → IsSheafCrystal F)
  (T : SmoothPresentation (affineSituation S hp))
  [Algebra (Dr : Type u) (T.completedEnvelope : Type u)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)]
  [∀ i, Module (T.completedEnvelope : Type u) (Om' i)]
  [Module (T.completedEnvelope : Type u)ᵐᵒᵖ (Om' 1)]
  [IsCentralScalar (T.completedEnvelope : Type u) (Om' 1)]
  (der' : DividedPowerDerivation ((affineSituation S hp).A : Type u) T.completedEnvelope
    T.baseHom (Om' 1))
  {ι' : Type uI'} (dx' : ι' → Om' 1)
  (wedge' : ∀ i, Om' i →ₗ[(T.completedEnvelope : Type u)]
    Om' 1 →ₗ[(T.completedEnvelope : Type u)] Om' (i + 1))
  (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  (hleib' : CompletedDeRham.IsGradedLeibniz T.completedEnvelope Om' wedge' deRham'
    (derivationFun ((affineSituation S hp).A : Type u) T.completedEnvelope T.baseHom
      (Om' 1) der'))
  (psi : Om 1 →ₛₗ[algebraMap (Dr : Type u) (T.completedEnvelope : Type u)] Om' 1)
  (hpsi : ∀ x : (Dr : Type u),
    psi (der x) = der' (algebraMap (Dr : Type u) (T.completedEnvelope : Type u) x))

/-- **The pair `(M, ∇)` over `D` that [Stacks, Tag 07JG] attaches to a quasi-coherent `ℱ`**,
through the reduction datum `R`.  This is the pair [Stacks, Proposition 60.21.3, Tag 07LG] speaks
of, and the one [Stacks, Lemma 60.17.5, Tag 07L5] base changes along `a : D → D'`. -/
public noncomputable abbrev pairOverEnvelope (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) :
    Pair.{u, u, uI, u} S.p Dr (Om 1) dx
      (derivationFun ((affineSituation S hp).A : Type u) Dr g (Om 1) der) :=
  (functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)

/-- **The connection `∇'` over `D'`**: the base change of `∇` along the map `a : D → D'` of
[Stacks, Lemma 60.17.5, Tag 07L5], carried by the `Algebra` instance, through
`Crystalline.CompletedConnection.baseChange` of [Stacks, Tag 07JC].  Its Leibniz rule is
`∇'(b' • x) = b' • ∇' x + x ⊗ d' b'`; the two product-rule hypotheses the base change needs of
`d'` are supplied by `der'`, which extends a `Derivation ℤ`. -/
public noncomputable abbrev baseChangedConnection (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) :
    CompletedConnection S.p (T.completedEnvelope : Type u) (Om' 1)
      (derivationFun ((affineSituation S hp).A : Type u) T.completedEnvelope T.baseHom
        (Om' 1) der')
      (CompletedConnection.baseChangeCarrier S.p (Dr : Type u) (T.completedEnvelope : Type u)
        (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier) :=
  CompletedConnection.baseChange S.p (Dr : Type u) (T.completedEnvelope : Type u)
    (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier (Om 1) (Om' 1)
    (derivationFun ((affineSituation S hp).A : Type u) T.completedEnvelope T.baseHom
      (Om' 1) der')
    psi (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).nabla
    (fun x y ↦ der'.map_add x y) (fun x y ↦ der'.leibniz x y) hpsi

variable (hcoord : ∀ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite),
    ∃ theta : ι' → (CompletedConnection.baseChangeCarrier S.p (Dr : Type u)
          (T.completedEnvelope : Type u)
          (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier →
        CompletedConnection.baseChangeCarrier S.p (Dr : Type u) (T.completedEnvelope : Type u)
          (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier),
      IsCoordinateExpansion S.p (T.completedEnvelope : Type u) (Om' 1) dx'
        (baseChangedConnection S hp Dr g Om der dx R h07IT T Om' der' psi hpsi F hF) theta)
  (hint : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    IsIntegrable S.p (T.completedEnvelope : Type u) (Om' 1) dx'
      (baseChangedConnection S hp Dr g Om der dx R h07IT T Om' der' psi hpsi F hF))
  (hqn : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    IsTopologicallyQuasiNilpotent S.p (T.completedEnvelope : Type u) (Om' 1) dx'
      (baseChangedConnection S hp Dr g Om der dx R h07IT T Om' der' psi hpsi F hF))

/-- **The pair `(M', ∇')` over `D'` corresponding to `ℱ`**, named rather than bound
existentially: it is `Crystalline.Pair.baseChange`, the base change along `a : D → D'` of the
pair [Stacks, Tag 07JG] attaches to `ℱ`, which is exactly what the proof of
[Stacks, Lemma 60.17.5, Tag 07L5] means by "the pair over `D'` corresponding to `ℱ`".

Of the four conditions of a pair, [Stacks, Tag 07JB] and [Stacks, Tag 07JC] are discharged by the
base change itself; `hcoord`, `hint` and `hqn` are the remaining three, carried as hypotheses.
They are not an assumption beyond the source's: [Stacks, Tag 07L5] asserts that `(M', ∇')` *is* a
pair, so in the situation of the lemma they hold. -/
public noncomputable abbrev basePairOverSmooth (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) :
    Pair.{u, u, uI', u} S.p (T.completedEnvelope : Type u) (Om' 1) dx'
      (derivationFun ((affineSituation S hp).A : Type u) T.completedEnvelope T.baseHom
        (Om' 1) der') :=
  Pair.baseChange S.p (Dr : Type u) (T.completedEnvelope : Type u) (Om 1) (Om' 1) dx dx'
    (derivationFun ((affineSituation S hp).A : Type u) T.completedEnvelope T.baseHom
      (Om' 1) der')
    psi (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF)
    (fun x y ↦ der'.map_add x y) (fun x y ↦ der'.leibniz x y) hpsi
    (hcoord F hF) (hint F hF) (hqn F hF)

variable (hsq' : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
  CompletedDeRham.IsSquareZero S.p (T.completedEnvelope : Type u) Om' wedge' deRham'
    (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' psi hpsi hcoord hint hqn
      F hF).carrier
    (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' psi hpsi hcoord hint hqn
      F hF).nabla hleib')

/-- **The complex `M' ⊗^∧_{D'} Ω^*_{D'}` of [Stacks, Lemma 60.21.4, Tag 07LH]**: in degree `i`
the completed tensor product `M' ⊗̂_{D'} Ω^i_{D'}`, with the de Rham differential
`∇'(m ⊗ ω) = ∇'(m) ∧ ω + m ⊗ d ω` of the base-changed connection. -/
public noncomputable abbrev smoothDeRhamComplex (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) : CochainComplex AddCommGrpCat.{u} ℕ :=
  CompletedDeRham.complex S.p (T.completedEnvelope : Type u) Om' wedge' deRham'
    (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' psi hpsi hcoord hint hqn
      F hF).carrier
    (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' psi hpsi hcoord hint hqn
      F hF).nabla hleib' (hsq' F hF)

/-- **The statement of [Stacks, Lemma 60.21.4, Tag 07LH]**: with the assumptions of
[Stacks, Tag 07LG] and `A → P' → C` a smooth presentation of the affine situation, with
`D'` the `p`-adic completion of `D_{P', γ}(J')`, the complex `M' ⊗^∧_{D'} Ω^*_{D'}` of the pair
over `D'` corresponding to a crystal `ℱ` in quasi-coherent `𝒪_{X/S}`-modules computes
`RΓ(Cris(X/S), ℱ)` — in the graded form in which crystalline cohomology is available here,
namely that the complex's cohomology in degree `j` is `H^j(Cris(X/S), ℱ)` for every `j`, after
lifting the complex to the universe `u + 1` in which that cohomology exists.

This is a proposition, not a theorem: nothing in this module proves it, and no attribute claims
it.

The pair `(M', ∇')` is **named, not bound existentially**: it is
`...SmallSite.basePairOverSmooth`, that is `Crystalline.Pair.baseChange` applied to the pair
[Stacks, Tag 07JG] attaches to `ℱ` and to the map `a : D → D'` of
[Stacks, Lemma 60.17.5, Tag 07L5].  That is what the source means by "the pair over `D'`
corresponding to `ℱ`", so the proposition is the lemma and not a weakening of it.  The complex is
`Crystalline.CompletedDeRham.complex`, whose differential is the de Rham differential
`∇'(m ⊗ ω) = ∇'(m) ∧ ω + m ⊗ d ω` of that pair's own connection.

The hypotheses are, exhaustively:

* `[IsAffine S.X]`, `[IsAffine S.S.scheme]`, `hp` — the standing hypotheses of
  [Stacks, Tag 07JN] inherited through [Stacks, Tag 07LG], which also supply the affine situation
  of [Stacks, Tag 07MD] that `T` is a presentation in;
* the polynomial-presentation side of [Stacks, Tag 07LG]: the divided power ring `D` with its
  structure map `g : A → D`, its forms `Om` with the divided power derivation `der` and the
  coordinate differentials `dx`, and the reduction datum `R` of [Stacks, Tag 07JG], which is
  what "the pair corresponding to `ℱ`" rests on;
* `T`, the smooth presentation `A → P' → C`, which determines `D'`;
* `Om'`, `wedge'`, `deRham'`, `der'`, `dx'`, `hleib'` — the graded forms `Ω^i_{D'}` with their
  wedge product, de Rham differential, divided power derivation and Leibniz rule, carried as
  parameters exactly as `...SmallSite.Computes07LG` carries them for `D`;
* `[Algebra (Dr) (D')]`, `psi` and `hpsi` — the map `a : D → D'` of
  [Stacks, Lemma 60.17.5, Tag 07L5] together with the comparison `ψ : Ω^1_D → Ω^1_{D'}` of
  Remark [Stacks, Tag 07KJ] and its compatibility `ψ (d x) = d' (a x)`;
* `hcoord`, `hint`, `hqn` — the three clauses of a pair, [Stacks, Tag 07JD] and
  [Stacks, Tag 07JE] among them, that the base change does not itself discharge;
  [Stacks, Tag 07L5] asserts them of `(M', ∇')`, so they are not an assumption beyond the
  source's;
* `hsq'`, that the completed de Rham differentials compose to zero, without which there is no
  complex;
* on the coefficients, `SheafOfModules.IsQuasicoherentOnSite` and nothing more, together with
  `h07IT`, the implication (1) ⟹ (2) of [Stacks, Tag 07IT].  The coefficient hypothesis is
  therefore stated **once**: condition (1) of that tag, which by the tag *is* the source's
  "crystal in quasi-coherent modules".  Assuming the conjunction of (1) and
  `...SmallSite.IsSheafCrystal` instead would be strictly stronger than the source asks, and
  would make this proposition weaker than its tag; omitting `h07IT` altogether would quantify
  over a strictly wider class of coefficients than the source does.  `h07IT` is read off here by
  `...SmallSite.toQuasiCoherentCrystal`, which is the point at which `ℱ` becomes an object of
  the category the source's hypothesis names; its underlying sheaf is `ℱ` itself.

The prime is `S.p` throughout, not a free parameter: `D'` is the `S.p`-adic completion of the
envelope, so the complex and the situation use the same prime. -/
public def Computes07LH : Prop :=
  ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
    Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((smoothDeRhamComplex S hp Dr g Om der dx R h07IT T Om' der' dx' wedge' deRham' hleib'
          psi hpsi hcoord hint hqn hsq' F hF).homology j) ≅
      (cohomologyFunctor S j).obj
        (abelianSheaf (toQuasiCoherentCrystal S h07IT F hF).obj))

/-! ### The canonical comparison maps `α` and `β`

The proof of [Stacks, Lemma 60.21.4, Tag 07LH] uses two maps of completed de Rham complexes:
`α` induced by `a : D → D'` and `β` induced by `b : D' → D`.  They are **constructed** below,
from the data they are made of, rather than quantified over.

Quantifying over them is not a matter of taste; it is wrong, and this module carried the wrong
statement.  If `α` and `β` are arbitrary maps of complexes whose only constraint is
`β ≫ α = 𝟙`, then on homology `H(β) ≫ H(α) = 𝟙`, so `H(α) ≫ H(β)` is an **idempotent** — and a
split idempotent need not be the identity, nor invertible.  A hypothesis asserting that it *is*
invertible is then not a consequence of anything such a theorem supplies, and no caller can
supply it either: the source obtains it from the completed clause of
[Stacks, Lemma 60.21.2, Tag 07LD], a statement about the base change map induced by a divided
power endomorphism of `D`, and an arbitrary pair of maps of complexes carries no information
identifying it as such a base change.  The hypothesis was therefore undischargeable for every
input, and the theorem could never be applied to anything.

With both maps constructed, `hab` and `hba` become statements about honest base change maps:
`hab` is the retract of [Stacks, Lemma 60.17.5, Tag 07L5] read on complexes, and `hba` is the
completed clause of [Stacks, Tag 07LD] for the endomorphism `b ∘ a` of `D`.  Neither is proved
here; what each still owes is recorded on `...SmallSite.computes07LH_of_computes07LG`.
-/

variable (hsqD : ∀ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite),
    CompletedDeRham.IsSquareZero S.p Dr Om wedge deRham
      (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier
      (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).nabla hleib)

/-! The graded comparison of forms along `a : D → D'`.  `psiG 1` is the degree-one comparison
`ψ` of Remark [Stacks, Tag 07KJ] that the base-changed pair is built from, so the pair, the
complex and the statement below are the same ones as above with `psi := psiG 1`; the higher
components are what `α` is made of.  The family is **unremovable**: `α` is a map of complexes in
every degree, its degree-`i` component is the completion of `m ⊗ ω ↦ (1 ⊗ m) ⊗ ψ_i ω`, and for
the abstract graded families `Om`, `Om'` carried here — which are not assumed to be exterior
powers of `Om 1`, `Om' 1` — a degree-one comparison induces nothing in higher degrees.
`hpsiG_wedge` and `hpsiG_deRham` are likewise properties of `ψ_*` and not consequences of the
rest of the data: `Crystalline.CompletedDeRham.baseChangeComplexHom` carries exactly these two.

The three are not vacuous.  For the genuine completed divided power forms they are exactly
`Crystalline.completedMapDifferentialForms` — the `p`-adic completion of
`Crystalline.mapDifferentialFormsOfDPMorphism`, a graded comparison in every degree for any
divided power morphism over `A` — together with
`Crystalline.completedMapDifferentialForms_wedge` and
`Crystalline.completedMapDifferentialForms_deRham`.  What keeps that from being the definition
here rather than a hypothesis is that `Om`, `Om'` are carried families and nothing identifies
them with `Crystalline.completedDividedPowerForms` of `D`, `D'`; this is the same reason
`Computes07LH` carries them at all.
-/
variable (psiG : ∀ i, Om i →ₛₗ[algebraMap (Dr : Type u) (T.completedEnvelope : Type u)] Om' i)
  (hpsiG : ∀ x : (Dr : Type u),
    psiG 1 (der x) = der' (algebraMap (Dr : Type u) (T.completedEnvelope : Type u) x))
  (hpsiG_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psiG (i + 1) (wedge i omega eta) = wedge' i (psiG i omega) (psiG 1 eta))
  (hpsiG_deRham : ∀ (i : ℕ) (omega : Om i),
    psiG (i + 1) (deRham i omega) = deRham' i (psiG i omega))
  (hcoordG : ∀ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite),
    ∃ theta : ι' → (CompletedConnection.baseChangeCarrier S.p (Dr : Type u)
          (T.completedEnvelope : Type u)
          (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier →
        CompletedConnection.baseChangeCarrier S.p (Dr : Type u) (T.completedEnvelope : Type u)
          (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier),
      IsCoordinateExpansion S.p (T.completedEnvelope : Type u) (Om' 1) dx'
        (baseChangedConnection S hp Dr g Om der dx R h07IT T Om' der' (psiG 1) hpsiG F hF)
        theta)
  (hintG : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    IsIntegrable S.p (T.completedEnvelope : Type u) (Om' 1) dx'
      (baseChangedConnection S hp Dr g Om der dx R h07IT T Om' der' (psiG 1) hpsiG F hF))
  (hqnG : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    IsTopologicallyQuasiNilpotent S.p (T.completedEnvelope : Type u) (Om' 1) dx'
      (baseChangedConnection S hp Dr g Om der dx R h07IT T Om' der' (psiG 1) hpsiG F hF))
  (hsqG : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    CompletedDeRham.IsSquareZero S.p (T.completedEnvelope : Type u) Om' wedge' deRham'
      (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
        hintG hqnG F hF).carrier
      (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
        hintG hqnG F hF).nabla hleib')

/-- **The comparison map `α` of [Stacks, Lemma 60.21.4, Tag 07LH]**: the base change map of
completed de Rham complexes `M ⊗^∧_D Ω^*_D ⟶ M' ⊗^∧_{D'} Ω^*_{D'}` induced by the map
`a : D → D'` of [Stacks, Lemma 60.17.5, Tag 07L5] and the graded comparison of forms `ψ_*`.

This is `Crystalline.CompletedDeRham.baseChangeComplexHom`, nothing else: its target is the
complex of the base-changed pair, whose module is
`Crystalline.CompletedConnection.baseChangeCarrier` and whose connection is
`Crystalline.CompletedConnection.baseChange`, and those are exactly the module and the
connection of `...SmallSite.basePairOverSmooth`, so the target *is*
`...SmallSite.smoothDeRhamComplex`.  Nothing is quantified over here and nothing is assumed
about the map; it is determined by `a` and `ψ_*`. -/
public noncomputable def comparisonAlpha (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) :
    crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
        deRham hleib R h07IT F hF (hsqD F hF) ⟶
      smoothDeRhamComplex S hp Dr g Om der dx R h07IT T Om' der' dx' wedge' deRham' hleib'
        (psiG 1) hpsiG hcoordG hintG hqnG hsqG F hF :=
  CompletedDeRham.baseChangeComplexHom S.p (Dr : Type u) (T.completedEnvelope : Type u)
    (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier Om Om' psiG wedge wedge'
    deRham deRham'
    (derivationFun ((affineSituation S hp).A : Type u) T.completedEnvelope T.baseHom
      (Om' 1) der')
    (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).nabla
    (fun x y ↦ der'.map_add x y) (fun x y ↦ der'.leibniz x y) hpsiG hleib hleib'
    hpsiG_wedge hpsiG_deRham (hsqD F hF) (hsqG F hF)

/-! The data of `β`.  `b : D' → D` is the second map of [Stacks, Lemma 60.17.5, Tag 07L5],
carried as `[Algebra ↑T.completedEnvelope ↑Dr]`; `chi` is the graded comparison of forms along
it, with the same three compatibilities `α` needs of `ψ_*`, and unremovable for the same reason.
`gamma` is the one thing `β` needs beyond a base change: the target of a base change along `b`
is the complex of the base change of `(M', ∇')` along `b`, whereas `β` has to land in the
complex of `(M, ∇)` itself, so `β` is a base change followed by the identification of `(M, ∇)`
with that base change.  That identification is the **second assertion of
[Stacks, Lemma 60.17.5, Tag 07L5]** — the equivalence of the categories of pairs over `D` and
over `D'`, stated as `Crystalline.exists_presentation_retract_pairEquivalence`, whose maps this
module does not identify with its own; `Crystalline.exists_completedEnvelopeRetract` is the
first assertion only.  It is taken here as an **isomorphism** of complexes, which is what an
equivalence of categories of pairs gives, and not as a bare morphism: `hba` below is
dischargeable from [Stacks, Tag 07LD] only because `gamma` is invertible.
-/
variable [Algebra (T.completedEnvelope : Type u) (Dr : Type u)]
  (chi : ∀ i, Om' i →ₛₗ[algebraMap (T.completedEnvelope : Type u) (Dr : Type u)] Om i)
  (hchi : ∀ x : (T.completedEnvelope : Type u),
    chi 1 (der' x) = der (algebraMap (T.completedEnvelope : Type u) (Dr : Type u) x))
  (hchi_wedge : ∀ (i : ℕ) (omega : Om' i) (eta : Om' 1),
    chi (i + 1) (wedge' i omega eta) = wedge i (chi i omega) (chi 1 eta))
  (hchi_deRham : ∀ (i : ℕ) (omega : Om' i),
    chi (i + 1) (deRham' i omega) = deRham i (chi i omega))

/-- **The connection on `M' ⊗̂_{D'} D` obtained by base change along `b : D' → D`**, through
`Crystalline.CompletedConnection.baseChange` of [Stacks, Tag 07JC], exactly as
`...SmallSite.baseChangedConnection` is the base change along `a` in the other direction.  This
is the connection of the pair that the second assertion of [Stacks, Lemma 60.17.5, Tag 07L5]
identifies with `(M, ∇)`. -/
public noncomputable abbrev backChangedConnection (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) :
    CompletedConnection S.p (Dr : Type u) (Om 1)
      (derivationFun ((affineSituation S hp).A : Type u) Dr g (Om 1) der)
      (CompletedConnection.baseChangeCarrier S.p (T.completedEnvelope : Type u) (Dr : Type u)
        (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
          hintG hqnG F hF).carrier) :=
  CompletedConnection.baseChange S.p (T.completedEnvelope : Type u) (Dr : Type u)
    (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
      hintG hqnG F hF).carrier (Om' 1) (Om 1)
    (derivationFun ((affineSituation S hp).A : Type u) Dr g (Om 1) der) (chi 1)
    (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
      hintG hqnG F hF).nabla
    (fun x y ↦ der.map_add x y) (fun x y ↦ der.leibniz x y) hchi

variable (hsqBack : ∀ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite),
    CompletedDeRham.IsSquareZero S.p (Dr : Type u) Om wedge deRham
      (CompletedConnection.baseChangeCarrier S.p (T.completedEnvelope : Type u) (Dr : Type u)
        (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
          hintG hqnG F hF).carrier)
      (backChangedConnection S hp Dr g Om der dx R h07IT T Om' der' dx' psiG hpsiG hcoordG
        hintG hqnG chi hchi F hF) hleib)
  (gamma : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    CompletedDeRham.complex S.p (Dr : Type u) Om wedge deRham
        (CompletedConnection.baseChangeCarrier S.p (T.completedEnvelope : Type u) (Dr : Type u)
          (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG
            hcoordG hintG hqnG F hF).carrier)
        (backChangedConnection S hp Dr g Om der dx R h07IT T Om' der' dx' psiG hpsiG hcoordG
          hintG hqnG chi hchi F hF) hleib (hsqBack F hF) ≅
      crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
        deRham hleib R h07IT F hF (hsqD F hF))

/-- **`gamma` from an isomorphism of pairs.**  The second assertion of
[Stacks, Lemma 60.17.5, Tag 07L5] is an equivalence between the categories of pairs over `D` and
over `D'`; what it produces at `ℱ` is an isomorphism of *pairs* — a horizontal `D`-linear
bijection `e` between the base change of `(M', ∇')` along `b` and `(M, ∇)` — and not directly an
isomorphism of complexes.  This turns the one into the other, so that nothing beyond that
assertion is owed at the point where `gamma` is used: given `e` and its horizontality `he`, the
isomorphism of complexes follows with no further hypothesis.

It is `Crystalline.CompletedDeRham.horizontalComplexIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamHorizontal.lean`, where `he` is the
shape of `Crystalline.PairHom.horizontal`, so an isomorphism in the category
`Crystalline.Pair` supplies it directly; see
`Crystalline.CompletedDeRham.pairComplexIso`.

This does **not** prove the direction `G ∘ F ≅ id` of that second assertion, and no attribute
for [Stacks, Tag 07L5] is placed on it: `e` and `he` are hypotheses, and nothing in this library
produces them.  The lemma's first assertion is
`Crystalline.exists_completedEnvelopeRetract`, and the other direction of its second,
`F ∘ G = id`, is
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract`; both carry the tag. -/
public noncomputable def gammaOfHorizontalEquiv (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite)
    (e : CompletedConnection.baseChangeCarrier S.p (T.completedEnvelope : Type u)
          (Dr : Type u)
          (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG
            hcoordG hintG hqnG F hF).carrier ≃ₗ[(Dr : Type u)]
        (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).carrier)
    (he : ∀ m, (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).nabla (e m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (Dr : Type u)) S.p)
        (TensorProduct.map (e : _ →ₗ[(Dr : Type u)] _)
          (LinearMap.id (R := (Dr : Type u)) (M := Om 1)))
        (backChangedConnection S hp Dr g Om der dx R h07IT T Om' der' dx' psiG hpsiG hcoordG
          hintG hqnG chi hchi F hF m)) :
    CompletedDeRham.complex S.p (Dr : Type u) Om wedge deRham
        (CompletedConnection.baseChangeCarrier S.p (T.completedEnvelope : Type u) (Dr : Type u)
          (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG
            hcoordG hintG hqnG F hF).carrier)
        (backChangedConnection S hp Dr g Om der dx R h07IT T Om' der' dx' psiG hpsiG hcoordG
          hintG hqnG chi hchi F hF) hleib (hsqBack F hF) ≅
      crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
        deRham hleib R h07IT F hF (hsqD F hF) :=
  CompletedDeRham.horizontalComplexIso S.p (Dr : Type u) _ _ Om e wedge deRham
    (backChangedConnection S hp Dr g Om der dx R h07IT T Om' der' dx' psiG hpsiG hcoordG
      hintG hqnG chi hchi F hF)
    (pairOverEnvelope S hp Dr g Om der dx R h07IT F hF).nabla hleib he (hsqBack F hF)
    (hsqD F hF)

/-- **The comparison map `β` of [Stacks, Lemma 60.21.4, Tag 07LH]**: the base change map of
completed de Rham complexes along `b : D' → D` for the graded comparison `chi`, followed by the
identification `gamma` of `(M, ∇)` with the base change of `(M', ∇')` along `b`.

This is the source's `β`.  It is a construction and not a quantified morphism: the only thing
about it that is not determined by `b` and `chi` is `gamma`, which is the direction
`G ∘ F ≅ id` of the second assertion of [Stacks, Lemma 60.17.5, Tag 07L5] — the direction whose
last step, the horizontality of the comparison, the source's proof omits. -/
public noncomputable def comparisonBeta (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) :
    smoothDeRhamComplex S hp Dr g Om der dx R h07IT T Om' der' dx' wedge' deRham' hleib'
        (psiG 1) hpsiG hcoordG hintG hqnG hsqG F hF ⟶
      crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
        deRham hleib R h07IT F hF (hsqD F hF) :=
  CompletedDeRham.baseChangeComplexHom S.p (T.completedEnvelope : Type u) (Dr : Type u)
      (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
        hintG hqnG F hF).carrier Om' Om chi wedge' wedge deRham' deRham
      (derivationFun ((affineSituation S hp).A : Type u) Dr g (Om 1) der)
      (basePairOverSmooth S hp Dr g Om der dx R h07IT T Om' der' dx' (psiG 1) hpsiG hcoordG
        hintG hqnG F hF).nabla
      (fun x y ↦ der.map_add x y) (fun x y ↦ der.leibniz x y) hchi hleib' hleib
      hchi_wedge hchi_deRham (hsqG F hF) (hsqBack F hF) ≫
    (gamma F hF).hom

/-- From a left inverse on complexes whose other composite is a quasi-isomorphism in degree `j`,
the map itself is a quasi-isomorphism in degree `j`.  This is
`...SmallSite.isIso_of_comp_id_of_isIso_comp` read through `homologyMap`, which is additive on
composites and sends the identity to the identity. -/
private theorem isIso_homologyMap_of_retract {X Y : CochainComplex AddCommGrpCat.{u} ℕ}
    (f : X ⟶ Y) (g : Y ⟶ X) (hgf : g ≫ f = 𝟙 Y) (j : ℕ)
    (hfg : IsIso (HomologicalComplex.homologyMap (f ≫ g) j)) :
    IsIso (HomologicalComplex.homologyMap f j) := by
  have h1 : HomologicalComplex.homologyMap g j ≫ HomologicalComplex.homologyMap f j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hgf, HomologicalComplex.homologyMap_id]
  have h2 : IsIso (HomologicalComplex.homologyMap f j ≫
      HomologicalComplex.homologyMap g j) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact hfg
  exact isIso_of_comp_id_of_isIso_comp _ _ h1 h2

omit [Module (T.completedEnvelope : Type u)ᵐᵒᵖ (Om' 1)]
  [IsCentralScalar (T.completedEnvelope : Type u) (Om' 1)] in
/-- **The reduction of [Stacks, Lemma 60.21.4, Tag 07LH] to
[Stacks, Proposition 60.21.3, Tag 07LG], carried out.**  The proof of the lemma runs: the pair
over `D` corresponding to `ℱ` is the base change of `(M', ∇')` along `b`, so
[Stacks, Tag 07LG] computes the crystalline cohomology of `ℱ` by `M ⊗^∧_D Ω^*_D`; the two base
change maps of de Rham complexes induced by `a` and `b` compose, one way round, to the identity
of `M' ⊗^∧_{D'} Ω^*_{D'}` because `a ∘ b = id_{D'}`; and the other composite, induced by
`b ∘ a : D → D`, is a quasi-isomorphism.  Hence both maps are quasi-isomorphisms and the two
complexes have the same cohomology.

The two maps are **not** hypotheses: `α` is `...SmallSite.comparisonAlpha` and `β` is
`...SmallSite.comparisonBeta`, both constructed from the data of
[Stacks, Lemma 60.17.5, Tag 07L5].  What is carried as a hypothesis is, exhaustively:

* the graded comparisons of forms `psiG` along `a` and `chi` along `b` with their
  compatibilities.  These are data, not stand-ins for missing proofs, and they are unremovable:
  `α` and `β` are maps of complexes in all degrees, and the abstract graded families `Om`, `Om'`
  carried here are not assumed to be exterior powers, so a degree-one comparison induces nothing
  in higher degrees.  The degree-one component of `psiG` plays the role the single comparison
  `psi` plays above: the conclusion is `...SmallSite.Computes07LH` at `psi := psiG 1`, that
  proposition being untouched by this theorem.  For the genuine completed divided power forms
  such a family exists and satisfies both compatibilities, as
  `Crystalline.completedMapDifferentialForms` with
  `Crystalline.completedMapDifferentialForms_wedge` and
  `Crystalline.completedMapDifferentialForms_deRham`, so these hypotheses are instantiable and
  not a way of assuming the conclusion.
* `gamma`, the identification of `(M, ∇)` with the base change of `(M', ∇')` along `b`.  This is
  the direction `G ∘ F ≅ id` of the **second assertion of
  [Stacks, Lemma 60.17.5, Tag 07L5]**, stated as
  `Crystalline.exists_presentation_retract_pairEquivalence` for the maps that theorem produces,
  which this module does not identify with its `Algebra` instances.  The step of it the source's
  proof leaves to the reader — "It remains to prove that this map is horizontal, i.e.,
  compatible with connections, which we omit." — is `Crystalline.nabla_taylorSum_eq` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/TaylorHorizontal.lean`.  The first assertion is
  proved, as
  `Crystalline.exists_completedEnvelopeRetract`, and so is the other direction of the second,
  `F ∘ G = id`, as
  `Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract`.  It is carried as an
  isomorphism because that is what the equivalence of categories of pairs gives, and because
  `hba` is dischargeable only for an invertible `gamma`.  What the second assertion produces at
  `ℱ` is an isomorphism of *pairs*, and the passage from that to this isomorphism of complexes
  is proved: `...SmallSite.gammaOfHorizontalEquiv` above, through
  `Crystalline.CompletedDeRham.horizontalComplexIso`.  So nothing beyond the second assertion
  itself is owed here.
* `hab`, that `β ≫ α` is the identity.  This is the retract half of
  [Stacks, Lemma 60.17.5, Tag 07L5], `a ∘ b = id_{D'}`, read on complexes.  Between the *rings*
  that identity is proved, as `Crystalline.exists_completedEnvelopeRetract`.  Reading it on
  complexes needs the functoriality of `Crystalline.CompletedDeRham.baseChangeComplexHom` under
  composition and under the identity.  Both halves are available: the identity half as
  `Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_id`, and the composition half on the
  complexes as `Crystalline.CompletedDeRham.baseChangeComplexHom_comp` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeComposite.lean`, whose
  input is that the comparison `Crystalline.CompletedConnection.baseChangeComposite` along which
  the composition law is stated is **horizontal** for the two base-changed connections, hence a
  morphism of complexes — `Crystalline.CompletedConnection.baseChange_baseChangeComposite`.
  What `hab` still owes is the identification of the carried `Algebra` instances with the maps
  `a`, `b` that `Crystalline.exists_completedEnvelopeRetract` produces existentially, and the
  compatibility of `gamma` with the two base changes.
* `hba`, that `α ≫ β` is a quasi-isomorphism in every degree.  In the source this is the claim
  that a divided power `A`-algebra endomorphism `ρ : D → D` compatible with the augmentation to
  `C` induces a quasi-isomorphism, which is proved from the **completed** clause of
  [Stacks, Lemma 60.21.2, Tag 07LD].  That clause is proved, as clause 2 of
  `Crystalline.DividedPowerPolynomial.stacks07LD`; this module does not derive `hba` from it.
  The homotopy of its `M = D` case, `Crystalline.completedRelativeFormsHomotopy_identity`, does
  not tensor up by itself, because the differential of `M ⊗̂_D Ω^*` is the connection-twisted
  `∇m ∧ ω + m ⊗ dω` and not `1_M ⊗ d`, so it is a homotopy only against the untwisted
  differential.  `hba` is a statement about a composite of
  genuine base change maps, so it is the statement [Stacks, Tag 07LD] would discharge; with `α`
  and `β` quantified over it would be a statement about arbitrary maps, dischargeable from
  nothing.

No tag attribute is placed on this theorem: it is the retract step of a superseded route, with
`hab`, `hba` and `gamma` as arguments.  [Stacks, Tag 07LH] is
`Crystalline.GlobalCrystallineSituation.SmallSite.smoothPresentationPair_computesCohomology`. -/
public theorem computes07LH_of_computes07LG
    (h07LG : Computes07LG S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
      deRham hleib hp R h07IT hsqD)
    (hab : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
          hchi_deRham hsqBack gamma F hF ≫
        comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
          F hF = 𝟙 _)
    (hba : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (j : ℕ), IsIso (HomologicalComplex.homologyMap
        (comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
            deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
            F hF ≫
          comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
            deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
            hchi_deRham hsqBack gamma F hF) j)) :
    Computes07LH S hp Dr g Om der dx R h07IT T Om' der' dx' wedge' deRham' hleib' (psiG 1)
      hpsiG hcoordG hintG hqnG hsqG := by
  intro F hF j
  obtain ⟨e⟩ := h07LG F hF j
  have := isIso_homologyMap_of_retract _ _ (hab F hF) j (hba F hF j)
  exact ⟨(AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
    (@asIso _ _ _ _ _ this).symm).trans e⟩

/-! ### `hba` from the factorization of `ρ = b ∘ a`

The last step of the proof of [Stacks, Lemma 60.21.4, Tag 07LH] is the claim that the
endomorphism `ρ = b ∘ a` of `D` induces a quasi-isomorphism of `M ⊗^∧_D Ω^*_D`, which is the
hypothesis `hba` above.  The source proves it by factoring `ρ` through the `p`-adic completion
of a divided power polynomial algebra,

`D --σ--> D⟨ξ_i⟩^∧ --τ--> D`,  `σ(x_i) = x_i + ξ_i`,  `τ(ξ_i) = z_i`,

where `ρ(x_i) = x_i + z_i` with the `z_i` in the divided power ideal, and then using: the
automorphism `α` of `D⟨ξ_i⟩^∧` with `α(x_i) = x_i - ξ_i`, `α(ξ_i) = ξ_i`, which makes `α ∘ σ` the
structure map `ν : D → D⟨ξ_i⟩^∧`; the identity `τ ∘ ν = id_D`; and the completed clause of
[Stacks, Lemma 60.20.2, Tag 07LD] for `ν`.

That argument is `Crystalline.CompletedDeRham.isIso_homologyMap_of_factorization`, read on
complexes of abelian groups.  The two results below are it instantiated at the constructed maps
`α` and `β` of this module, so that `hba` is no longer a hypothesis standing for all of
[Stacks, Tag 07LD] but a *consequence* of the factorization data — the four hypotheses `hfac`,
`hse`, `hit`, `hincl`, each of which is one sentence of the source's proof.
-/

omit [Module (T.completedEnvelope : Type u)ᵐᵒᵖ (Om' 1)]
  [IsCentralScalar (T.completedEnvelope : Type u) (Om' 1)] in
/-- **`hba` of `...SmallSite.computes07LH_of_computes07LG` from the factorization of `ρ = b ∘ a`
through the completed divided power polynomial algebra.**

Given a complex `Y` — in the application the completed de Rham complex over `D⟨ξ_i⟩^∧` — maps
`s`, `t` into and out of it — in the application the base change maps along `σ` and `τ` — a
second map `incl` into it — the base change map along the structure map `ν : D → D⟨ξ_i⟩^∧` — and
an isomorphism `e` of `Y` — the automorphism `α` of `D⟨ξ_i⟩^∧` read on the complexes — such that

* `hfac`: `s ≫ t` is the composite `α ≫ β`, which is the map induced by `ρ = b ∘ a`;
* `hse`: `s ≫ e.hom = incl`, which is `α ∘ σ = ν`;
* `hit`: `incl ≫ t = 𝟙`, which is `τ ∘ ν = id_D`;
* `hincl`: `incl` is invertible on homology, which is the **completed clause of
  [Stacks, Lemma 60.20.2, Tag 07LD]** for `ν`,

the composite `α ≫ β` is invertible on homology in every degree.  That is exactly `hba`.

Nothing here constructs `Y`, `s`, `t`, `incl`, `e`, and nothing here proves `hincl`; this is the
reduction of `hba` to those five pieces of data and that one quasi-isomorphism, which is what
the source's proof of this step consists of.  In particular no tag attribute is placed. -/
theorem isIso_homologyMap_comparison_of_factorization
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
    (Y : CochainComplex AddCommGrpCat.{u} ℕ)
    (s : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
      deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y)
    (t : Y ⟶ crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
      wedge deRham hleib R h07IT F hF (hsqD F hF))
    (incl : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
      deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y)
    (e : Y ≅ Y)
    (hfac : s ≫ t =
      comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
          F hF ≫
        comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
          hchi_deRham hsqBack gamma F hF)
    (hse : s ≫ e.hom = incl) (hit : incl ≫ t = 𝟙 _)
    (hincl : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap incl j)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
          F hF ≫
        comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
          hchi_deRham hsqBack gamma F hF) j) :=
  CompletedDeRham.isIso_homologyMap_of_factorization _ s t incl e hfac hse hit hincl j

omit [Module (T.completedEnvelope : Type u)ᵐᵒᵖ (Om' 1)]
  [IsCentralScalar (T.completedEnvelope : Type u) (Om' 1)] in
/-- **[Stacks, Lemma 60.21.4, Tag 07LH] from [Stacks, Proposition 60.21.3, Tag 07LG] and the
factorization of `ρ = b ∘ a`.**

This is `...SmallSite.computes07LH_of_computes07LG` with its hypothesis `hba` replaced by the
factorization data of the source's own proof of that step: for each `ℱ` a complex `Y` over the
completed divided power polynomial algebra `D⟨ξ_i⟩^∧`, the base change maps `s`, `t` along `σ`
and `τ`, the base change map `incl` along the structure map `ν`, the automorphism `α` read as an
isomorphism `e` of `Y`, and the four assertions `τ ∘ σ = ρ`, `α ∘ σ = ν`, `τ ∘ ν = id_D` and the
completed clause of [Stacks, Lemma 60.20.2, Tag 07LD] for `ν`.

So what [Stacks, Tag 07LH] still owes, beyond [Stacks, Tag 07LG], `hab`, and the second
assertion of [Stacks, Lemma 60.17.5, Tag 07L5] carried in `gamma`, is exhaustively: the
**construction** of the factorization — the ring `D⟨ξ_i⟩^∧`, the three divided power maps `σ`,
`τ`, `ν`, the automorphism `α`, and these read on the completed de Rham complexes through
`Crystalline.CompletedDeRham.baseChangeComplexHom` and its composition law
`Crystalline.CompletedDeRham.baseChangeComplexHom_comp` — and the completed clause of
[Stacks, Tag 07LD] at `ν`.  The latter is what
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamPerturbation.lean` supplies, through
`Crystalline.CompletedDeRham.isIso_homologyMap_of_homotopyRetract`, once its `ι'` and its
existentially produced differential `d_L` are identified with the base change map along `ν` and
with the de Rham differential of `M ⊗^∧_D Ω^*_D`.

`hba` is therefore not a hypothesis of this theorem, and no hypothesis of this theorem is a
statement about arbitrary maps of complexes: each of the four is a sentence of the source's
proof.  No tag attribute is placed, for the same reason as on
`...SmallSite.computes07LH_of_computes07LG`: `gamma` still carries the direction `G ∘ F ≅ id` of
the second assertion of [Stacks, Tag 07L5], whose last step the source omits. -/
theorem computes07LH_of_computes07LG_of_factorization
    (h07LG : Computes07LG S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
      deRham hleib hp R h07IT hsqD)
    (hab : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
          hchi_deRham hsqBack gamma F hF ≫
        comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
          F hF = 𝟙 _)
    (hfactor : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      ∃ (Y : CochainComplex AddCommGrpCat.{u} ℕ)
        (s : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
          wedge deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y)
        (t : Y ⟶ crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
          wedge deRham hleib R h07IT F hF (hsqD F hF))
        (incl : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
          wedge deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y) (e : Y ≅ Y),
        s ≫ t =
            comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx'
                wedge' deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG
                hqnG hsqG F hF ≫
              comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx'
                wedge' deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi
                hchi_wedge hchi_deRham hsqBack gamma F hF ∧
          s ≫ e.hom = incl ∧ incl ≫ t = 𝟙 _ ∧
            ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap incl j)) :
    Computes07LH S hp Dr g Om der dx R h07IT T Om' der' dx' wedge' deRham' hleib' (psiG 1)
      hpsiG hcoordG hintG hqnG hsqG :=
  computes07LH_of_computes07LG S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx'
    wedge' deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG chi
    hchi hchi_wedge hchi_deRham hsqBack gamma h07LG hab
    (fun F hF j ↦ by
      obtain ⟨Y, s, t, incl, e, hfac, hse, hit, hincl⟩ := hfactor F hF
      exact isIso_homologyMap_comparison_of_factorization S hp Dr g Om der dx wedge deRham
        hleib R h07IT T Om' der' dx' wedge' deRham' hleib' hsqD psiG hpsiG hpsiG_wedge
        hpsiG_deRham hcoordG hintG hqnG hsqG chi hchi hchi_wedge hchi_deRham hsqBack gamma
        F hF Y s t incl e hfac hse hit hincl j)

/-! ### `hba` from the factorization of `ρ = b ∘ a`, in the shape the factorization has

The two results above read the source's factorization with `s` and `incl` landing in one complex
`Y` and the automorphism `α` as an *endomorphism* `e : Y ≅ Y` of it.  That shape cannot be filled
by the source's data.  The three maps live in three complexes: `s` is the base change along `σ`,
into the complex of `M ⊗̂_{D, σ} D⟨ξ_i⟩^∧`; `incl` is the base change along `ν`, into the complex
of `M ⊗̂_{D, ν} D⟨ξ_i⟩^∧`; and those two modules are different objects, because
`Crystalline.CompletedConnection.baseChangeCarrier` is `(D' ⊗[D] M)^∧` and so depends on the
`Algebra D D'` instance, of which `σ` and `ν` are two.  `α` relates them and is not an
automorphism of either — on the coefficient ring `α ∘ ν = σ⁻`, by
`Crystalline.envelopeCompletionAlpha_comp_nu`.  Worse, the shape is jointly contradictory for
base change maps: forcing `s` and `incl` into one target forces them to be base changes along one
map `w`, so `hit` says `τ ∘ w = id_D` and `hfac` says `τ ∘ w = ρ`, and `ρ ≠ id_D`.

The two results below are the repair.  `α` becomes a **transport** `Tr : Y₁ ⟶ Y₂`, invertible on
homology, and the retraction out of the first complex is replaced by its consequence `H(t)`,
which is what the source's `τ ∘ ν = id_D` does *not* give for the `σ` copy; see
`Crystalline.CompletedDeRham.isIso_homologyMap_of_transport`.
-/

omit [Module (T.completedEnvelope : Type u)ᵐᵒᵖ (Om' 1)]
  [IsCentralScalar (T.completedEnvelope : Type u) (Om' 1)] in
/-- **`hba` of `...SmallSite.computes07LH_of_computes07LG` from the factorization of `ρ = b ∘ a`,
in the shape the factorization has.**

Given two complexes `Y₁`, `Y₂` — in the application the completed de Rham complexes of
`M ⊗̂_{D, σ} D⟨ξ_i⟩^∧` and of `M ⊗̂_{D, ν} D⟨ξ_i⟩^∧` — the base change maps `s : X ⟶ Y₁` along `σ`
and `t : Y₁ ⟶ X` along `τ`, the base change map `incl : X ⟶ Y₂` along `ν`, and a transport
`Tr : Y₁ ⟶ Y₂` — the automorphism `α` read on the complexes, composed with the comparison of the
twice base-changed module with the once base-changed one — such that

* `hfac`: `s ≫ t` is the composite `α ≫ β`, which is the map induced by `ρ = b ∘ a`;
* `hsT`: `s ≫ Tr = incl`, which is `α ∘ σ = ν`;
* `hT`: `Tr` is invertible on homology, which is "`α` is an isomorphism";
* `hincl`: `incl` is invertible on homology, the **completed clause of
  [Stacks, Lemma 60.20.2, Tag 07LD]** for `ν`;
* `ht`: `t` is invertible on homology,

the composite `α ≫ β` is invertible on homology in every degree.  That is exactly `hba`.

`ht` is a hypothesis and not a consequence of the others.  The source's sentence about the left
inverse of `τ` is a statement about the base change along `τ` out of the `ν` copy, which is
proved in this library as `Crystalline.isIso_homologyMap_tauComplexHom`; `t` here is the base
change along `τ` out of the `σ` copy, a different map, for which `τ ∘ σ = ρ` and there is no
section coming from a ring map.  Deriving it from `hfac` would need `H(ρ)`, the conclusion.

Nothing here constructs `Y₁`, `Y₂`, `s`, `t`, `incl`, `Tr`, and nothing here proves `hincl`, `hT`
or `ht`.  In particular no tag attribute is placed. -/
theorem isIso_homologyMap_comparison_of_transport
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
    (Y₁ Y₂ : CochainComplex AddCommGrpCat.{u} ℕ)
    (s : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
      deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y₁)
    (t : Y₁ ⟶ crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
      wedge deRham hleib R h07IT F hF (hsqD F hF))
    (incl : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
      deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y₂)
    (Tr : Y₁ ⟶ Y₂)
    (hfac : s ≫ t =
      comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
          F hF ≫
        comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
          hchi_deRham hsqBack gamma F hF)
    (hsT : s ≫ Tr = incl)
    (hT : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap Tr j))
    (hincl : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap incl j))
    (ht : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap t j)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
          F hF ≫
        comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
          hchi_deRham hsqBack gamma F hF) j) :=
  CompletedDeRham.isIso_homologyMap_of_transport _ s Tr incl t hfac hsT hT hincl ht j

omit [Module (T.completedEnvelope : Type u)ᵐᵒᵖ (Om' 1)]
  [IsCentralScalar (T.completedEnvelope : Type u) (Om' 1)] in
/-- **[Stacks, Lemma 60.21.4, Tag 07LH] from [Stacks, Proposition 60.21.3, Tag 07LG] and the
factorization of `ρ = b ∘ a`, in the shape the factorization has.**

This is `...SmallSite.computes07LH_of_computes07LG_of_factorization` with its hypothesis
`hfactor` — which, as explained above, no base change data can satisfy — replaced by
`htransport`, the same factorization read between two complexes: for each `ℱ` the complexes `Y₁`
of `M ⊗̂_{D, σ} D⟨ξ_i⟩^∧` and `Y₂` of `M ⊗̂_{D, ν} D⟨ξ_i⟩^∧`, the base change maps `s`, `t` along
`σ` and `τ`, the base change map `incl` along `ν`, the transport `Tr`, and the five assertions
`τ ∘ σ = ρ`, `α ∘ σ = ν`, the invertibility on homology of `Tr`, of `incl` and of `t`.

What [Stacks, Tag 07LH] still owes, beyond [Stacks, Tag 07LG], `hab`, and the second assertion
of [Stacks, Lemma 60.17.5, Tag 07L5] carried in `gamma`, is therefore: the **construction** of
the factorization, which exists in this library as
`Crystalline.envelopeCompletionSigmaComplexHom`,
`Crystalline.envelopeCompletionNuComplexHom`,
`Crystalline.envelopeCompletionAlphaComplexHom` and
`Crystalline.envelopeCompletionSigmaAlphaCorrection`, together with the identification of the
carried graded data of this statement with the concrete completed divided power forms of `D`
those are stated at; the completed clause of [Stacks, Lemma 60.20.2, Tag 07LD] at `ν`, which is
`hincl` and which `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` supplies once its
`ι'` and its existentially produced differential are identified with the base change along `ν`
and with the de Rham differential; the invertibility of `α` on homology, which is `hT` and which
is **proved**, as `Crystalline.isIso_homologyMap_envelopeCompletionAlphaComplexHom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedEnvelopeAlphaQuasiIso.lean`, by the
composition law of base changes run in both directions along `α` and `α⁻¹`; and `ht`,
the invertibility on homology of the base change along `τ` out of the `σ` copy, for which this
library has nothing — `Crystalline.isIso_homologyMap_tauComplexHom` is the
corresponding statement for the `ν` copy and does not apply.

No tag attribute is placed, for three independent reasons.  `gamma` still carries the direction
`G ∘ F ≅ id` of the second assertion of [Stacks, Tag 07L5], whose last step the source omits.
`Computes07LG` is carried as a *hypothesis*, whereas the source's hypotheses for 07LH are
"assumptions as in [Stacks, Tag 07LG]" and not that proposition's conclusion.  And it carries the
three `CompletedDeRham.IsSquareZero` families `hsqD`, `hsqG` and `hsqBack` — four more at the
envelope level, in `Crystalline.isIso_homologyMap_of_sigmaFactorization` — which are not source
hypotheses at all: the source derives `d² = 0` from integrability of the connection,
[Stacks, Tag 07JD]. -/
theorem computes07LH_of_computes07LG_of_transport
    (h07LG : Computes07LG S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx wedge
      deRham hleib hp R h07IT hsqD)
    (hab : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi hchi_wedge
          hchi_deRham hsqBack gamma F hF ≫
        comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx' wedge'
          deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG
          F hF = 𝟙 _)
    (htransport : ∀ (F : SheafOfModules.{u} (structureSheaf S))
      (hF : F.IsQuasicoherentOnSite),
      ∃ (Y₁ Y₂ : CochainComplex AddCommGrpCat.{u} ℕ)
        (s : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
          wedge deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y₁)
        (t : Y₁ ⟶ crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
          wedge deRham hleib R h07IT F hF (hsqD F hF))
        (incl : crystalDeRhamComplex S ((affineSituation S hp).A : Type u) Dr g Om der S.p dx
          wedge deRham hleib R h07IT F hF (hsqD F hF) ⟶ Y₂) (Tr : Y₁ ⟶ Y₂),
        s ≫ t =
            comparisonAlpha S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx'
                wedge' deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG
                hqnG hsqG F hF ≫
              comparisonBeta S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx'
                wedge' deRham' hleib' hsqD psiG hpsiG hcoordG hintG hqnG hsqG chi hchi
                hchi_wedge hchi_deRham hsqBack gamma F hF ∧
          s ≫ Tr = incl ∧
            (∀ j : ℕ, IsIso (HomologicalComplex.homologyMap Tr j)) ∧
              (∀ j : ℕ, IsIso (HomologicalComplex.homologyMap incl j)) ∧
                ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap t j)) :
    Computes07LH S hp Dr g Om der dx R h07IT T Om' der' dx' wedge' deRham' hleib' (psiG 1)
      hpsiG hcoordG hintG hqnG hsqG :=
  computes07LH_of_computes07LG S hp Dr g Om der dx wedge deRham hleib R h07IT T Om' der' dx'
    wedge' deRham' hleib' hsqD psiG hpsiG hpsiG_wedge hpsiG_deRham hcoordG hintG hqnG hsqG chi
    hchi hchi_wedge hchi_deRham hsqBack gamma h07LG hab
    (fun F hF j ↦ by
      obtain ⟨Y₁, Y₂, s, t, incl, Tr, hfac, hsT, hT, hincl, ht⟩ := htransport F hF
      exact isIso_homologyMap_comparison_of_transport S hp Dr g Om der dx wedge deRham
        hleib R h07IT T Om' der' dx' wedge' deRham' hleib' hsqD psiG hpsiG hpsiG_wedge
        hpsiG_deRham hcoordG hintG hqnG hsqG chi hchi hchi_wedge hchi_deRham hsqBack gamma
        F hF Y₁ Y₂ s t incl Tr hfac hsT hT hincl ht j)

end Statement

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
