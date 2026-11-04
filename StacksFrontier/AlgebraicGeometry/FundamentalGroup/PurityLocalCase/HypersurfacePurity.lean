module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedComplement
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumSchemeStalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Purity for a hypersurface in the local Lefschetz situation

Work in the local Lefschetz situation of Tag 0BLF: `(A, 𝔪)` is a Noetherian local ring,
`f ∈ 𝔪`, `X = Spec A` and `X₀ = Spec (A / fA)`, and `U = X ∖ {𝔪}`, `U₀ = X₀ ∖ {𝔪}` are the
punctured spectra. Purity for a local ring `R` is `AlgebraicGeometry.HasPurity R`: every finite
étale cover of the punctured spectrum of `R` is the restriction of a finite étale cover of
`Spec R`.

Tag 0DXZ deduces purity for `A / fA` from purity for `A` by a two-step argument: a finite étale
`V₀ → U₀` is first realised as the restriction of a finite étale `V → U`, and then `V` is extended
over the whole of `X` by purity for `A`; the restriction of that extension to `X₀` is the extension
of `V₀` that is wanted. This file contains that argument, and the part of the first step that
follows from Tag 0EY7.

## Main results

* `AlgebraicGeometry.essImage_finiteEtaleBaseChange_of_commSq` and
  `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_commSq` — the categorical step: for a
  commuting square `r ≫ j = j₀ ≫ g` of schemes, a cover in the essential image of base change
  along `r` is in the essential image of base change along `j₀`, as soon as base change along
  `j` is essentially surjective.
* `AlgebraicGeometry.LocalLefschetzSituation.hasPurity_quotientRing_of_essSurj_U₀ToU` — **the
  whole of the proof of Tag 0DXZ after its appeal to Tag 0EK9**: purity for `A` together with
  essential surjectivity of the restriction functor `FÉt_U ⥤ FÉt_{U₀}` gives purity for `A / fA`.
* `AlgebraicGeometry.LocalLefschetzSituation.essImage_finiteEtaleBaseChange_U₀ToU_of_hasPurity`
  and `…essSurj_finiteEtaleBaseChange_U₀ToU_of_hasPurity` — the last step of the proof of Tag
  0EK9: if a cover of `U₀` is already the restriction of a cover of an open `W ⊆ U` containing
  `U₀`, and purity holds at every point of `U` outside `W`, then it is the restriction of a cover
  of `U` itself.
* `AlgebraicGeometry.LocalLefschetzSituation.hasPurity_quotientRing_of_forall_exists_open` — the
  two combined: purity for `A / fA`, from purity for `A` and the existence, for each finite étale
  cover of `U₀`, of an open `W` with `U₀ ⊆ W ⊆ U` over which the cover is defined and outside
  which purity holds.
* `AlgebraicGeometry.hasPurity_of_ringEquiv` — purity depends only on the isomorphism class of
  the local ring; and `AlgebraicGeometry.puncturedSpectrum_eq_preimage_of_ringEquiv`, the
  identification of punctured spectra that proves it.
* `AlgebraicGeometry.hasPurity_stalk_puncturedSpectrum`,
  `AlgebraicGeometry.hasPurity_atPrime_comap_of_hasPurity_atPrime` and
  `AlgebraicGeometry.hasPurity_atPrime_of_eq_comap` — purity at a point of the punctured spectrum
  of `A` is purity of `A_𝔮`, and purity of `(A_g)_𝔭` is purity of `A_{𝔭 ∩ A}`. These are what
  turn the geometric hypothesis "purity at the points of `U ∖ W`" into the ring-theoretic
  hypothesis (3) of Tag 0DXZ.
* `…LocalLefschetzSituation.hasPurity_quotientRing_of_forall_exists_open_of_hasPurity_away`
  — all of the above combined: purity for `A / fA` from hypotheses (3) and (4) of Tag 0DXZ,
  together with the open `W` and the side condition on `U ∖ W` that the proof of Tag 0EK9
  produces.

## What is and is not proved

Nothing here is a Stacks tag and nothing is tagged. Every statement below is an unconditional
theorem; none of them carries a Stacks lemma as a hypothesis under a name like `h0EK9`, and the
hypotheses that do appear — essential surjectivity of `FÉt_U ⥤ FÉt_{U₀}`, pointwise purity on
the complement of an open `W ⊆ U`, and purity for the local rings of `A_f` at its maximal ideals
— are statements in this development's own vocabulary, quantified in the statement that uses
them.

Tag 0DXZ itself is **not** proved, and its missing input is exactly one lemma:

> **Tag 0EK9.** In Situation 0BLF assume (1) `A` has a dualizing complex and is `f`-adically
> complete, (2) either `A_f` is `(S₂)` and every irreducible component of `X` not contained in
> `X₀` has dimension `≥ 4`, or else `depth(A_𝔭) + dim(A/𝔭) > 3` whenever `𝔭 ∉ V(f)` and
> `V(𝔭) ∩ V(f) ≠ {𝔪}`, and (3) purity holds for `(A_f)_𝔭` for every maximal ideal `𝔭 ⊂ A_f`.
> Then the restriction functor `FÉt_U ⥤ FÉt_{U₀}` is essentially surjective.

No declaration in this repository carries tag 0EK9, and the source proves it from Tag 0DXY (the
restriction functor from the colimit of `FÉt_{U'}` over the opens `U₀ ⊆ U' ⊆ U` is an
equivalence), which it in turn proves from Tag 0EK1 and Tag 0EKY; neither 0DXY nor 0EKY is
formalized here either. What this file supplies is the rest: the step of the proof of 0EK9 that
goes from such a `U'` to `U` — which the source performs by `n` applications of Tag 0BPA and
which is available here in one step from Tag 0EY7 — and the whole of the proof of
0DXZ downstream of 0EK9. Beyond Tag 0DXY, one assertion of the source's proof of Tag 0EK9 is
also left as a hypothesis: that the points of `U ∖ U'` are primes as in hypothesis (3), i.e.
contractions of maximal ideals of `A_f`.

Because the source's proof of Tag 0BPC is, verbatim, "the proof of 0DXZ with Tag 0EKA in place
of Tag 0EK9", `hasPurity_quotientRing_of_essSurj_U₀ToU` is the complete proof of 0BPC after its
appeal to 0EKA as well: it names neither tag and only asks for the common conclusion.

## Implementation notes

The local Lefschetz situation used is `AlgebraicGeometry.LocalLefschetzSituation`, the structure
carrying tag 0BLF, so that the Noetherianness of `U` and the closed immersion `U₀ ⟶ U` recorded
in `StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityLocalCase/PuncturedComplement.lean` are
available. The duplicate `Stacks.FundamentalGroup.LocalLefschetzSituation` is not used and no
third copy is introduced.

Purity for `A / fA` is a statement about `Stacks.puncturedSpectrum (A / fA)`, while the
restriction functor of the situation is base change along `U₀Open.ι` for
`U₀Open = X₀ToX ⁻¹ᵁ UOpen`; the two opens of `X₀` are *equal*, by
`AlgebraicGeometry.LocalLefschetzSituation.U₀Open_eq_puncturedSpectrumOpen`, so no transport
along an isomorphism of schemes is needed and the goal is reached by a rewrite.

## References

* [Stacks Project, Tag 0DXZ](https://stacks.math.columbia.edu/tag/0DXZ)
* [Stacks Project, Tag 0EK9](https://stacks.math.columbia.edu/tag/0EK9)
* [Stacks Project, Tag 0BPC](https://stacks.math.columbia.edu/tag/0BPC)
* [Stacks Project, Tag 0EY7](https://stacks.math.columbia.edu/tag/0EY7)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### Two general facts about essential images of composites -/

/-- **An object in the essential image of `G` lies in the essential image of `F ⋙ G` as soon as
`F` is essentially surjective.**  A preimage of the witness `V` is `F.objPreimage V`, and `G`
carries the isomorphism `F.obj (F.objPreimage V) ≅ V` along. -/
lemma essImage_comp_of_essSurj_left {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] {Z : E} (h : G.essImage Z) :
    (F ⋙ G).essImage Z := by
  obtain ⟨V, ⟨e⟩⟩ := h
  exact ⟨F.objPreimage V, ⟨G.mapIso (F.objObjPreimageIso V) ≪≫ e⟩⟩

private lemma essImage_of_essImage_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {Z : E} (h : (F ⋙ G).essImage Z) : G.essImage Z := by
  obtain ⟨V, ⟨e⟩⟩ := h
  exact ⟨F.obj V, ⟨e⟩⟩

/-- A cover in the essential image of base change along `r` lies in the essential image of base
change along `r ≫ j` when base change along `j` is essentially surjective. -/
private lemma essImage_finiteEtaleBaseChange_comp_of_essSurj {X U U₀ : Scheme.{u}} {j : U ⟶ X}
    {r : U₀ ⟶ U} (hj : (finiteEtaleBaseChange j).EssSurj) {W₀ : FiniteEtaleOver U₀}
    (hr : (finiteEtaleBaseChange r).essImage W₀) :
    (finiteEtaleBaseChange (r ≫ j)).essImage W₀ :=
  Functor.essImage.ofNatIso (finiteEtaleBaseChangeComp r j).symm
    (essImage_comp_of_essSurj_left _ _ hr)

/-! ### Transporting essential surjectivity across a commuting square -/

/-- **A finite étale cover descends across a commuting square.** Let `r ≫ j = j₀ ≫ g` be a
commuting square of schemes, and suppose base change along `j` is essentially surjective on
finite étale covers. Then a finite étale cover of the source that is the base change of a cover
along `r` is also the base change of a cover along `j₀`.

In the application `j` and `j₀` are the inclusions of the punctured spectra of `A` and of
`A / fA`, `g` is the closed immersion `X₀ ⟶ X` and `r` is the restriction `U₀ ⟶ U`: a cover of
`U₀` coming from `U` comes from `X₀`, because by purity it comes from `X`. -/
theorem essImage_finiteEtaleBaseChange_of_commSq {X X₀ U U₀ : Scheme.{u}} {g : X₀ ⟶ X}
    {j : U ⟶ X} {j₀ : U₀ ⟶ X₀} {r : U₀ ⟶ U} (hsq : r ≫ j = j₀ ≫ g)
    (hj : (finiteEtaleBaseChange j).EssSurj) {W₀ : FiniteEtaleOver U₀}
    (hr : (finiteEtaleBaseChange r).essImage W₀) :
    (finiteEtaleBaseChange j₀).essImage W₀ := by
  have h₂ := essImage_finiteEtaleBaseChange_comp_of_essSurj hj hr
  rw [hsq] at h₂
  exact essImage_of_essImage_comp (finiteEtaleBaseChange g) (finiteEtaleBaseChange j₀)
    (Functor.essImage.ofNatIso (finiteEtaleBaseChangeComp j₀ g) h₂)

/-- **Essential surjectivity descends across a commuting square.** The functor form of
`AlgebraicGeometry.essImage_finiteEtaleBaseChange_of_commSq`: for a commuting square
`r ≫ j = j₀ ≫ g`, essential surjectivity of base change along `j` and along `r` gives essential
surjectivity of base change along `j₀`. -/
theorem essSurj_finiteEtaleBaseChange_of_commSq {X X₀ U U₀ : Scheme.{u}} {g : X₀ ⟶ X}
    {j : U ⟶ X} {j₀ : U₀ ⟶ X₀} {r : U₀ ⟶ U} (hsq : r ≫ j = j₀ ≫ g)
    (hj : (finiteEtaleBaseChange j).EssSurj) (hr : (finiteEtaleBaseChange r).EssSurj) :
    (finiteEtaleBaseChange j₀).EssSurj :=
  ⟨fun W₀ => essImage_finiteEtaleBaseChange_of_commSq hsq hj (hr.mem_essImage W₀)⟩

/-! ### Purity depends only on the isomorphism class of the local ring -/

/-- **An isomorphism of local rings pulls the punctured spectrum back to the punctured
spectrum.** The map of spectra it induces carries the closed point to the closed point, because
the comap of the maximal ideal along a ring isomorphism of local rings is the maximal ideal. -/
theorem puncturedSpectrum_eq_preimage_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Stacks.puncturedSpectrum S =
      Spec.map e.toCommRingCatIso.hom ⁻¹ᵁ Stacks.puncturedSpectrum R := by
  ext x
  show (x ∉ ({IsLocalRing.closedPoint S} : Set (PrimeSpectrum S))) ↔
    (Spec.map e.toCommRingCatIso.hom x ∉
      ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)))
  apply not_congr
  constructor
  · rintro rfl
    exact PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap (e : R →+* S))
  · intro hx
    refine PrimeSpectrum.ext ?_
    have he : x.asIdeal.comap (e : R →+* S) = IsLocalRing.maximalIdeal R :=
      congrArg PrimeSpectrum.asIdeal hx
    rw [← IsLocalRing.maximalIdeal_comap (e : R →+* S)] at he
    exact Ideal.comap_injective_of_surjective (e : R →+* S) e.surjective he

/-- **Purity only depends on the isomorphism class of the local ring.** An isomorphism
`R ≃+* S` identifies the punctured spectra of `R` and of `S` compatibly with their inclusions
into the two spectra, so each of the two essential surjectivity statements implies the other. -/
theorem hasPurity_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (h : HasPurity R) : HasPurity S := by
  have heq := puncturedSpectrum_eq_preimage_of_ringEquiv e
  let ε : (Stacks.puncturedSpectrum S).toScheme ≅ (Stacks.puncturedSpectrum R).toScheme :=
    (Spec (.of S)).isoOfEq heq ≪≫
      (Spec.map e.toCommRingCatIso.hom).preimageIso (Stacks.puncturedSpectrum R)
  have hsq : ε.hom ≫ (Stacks.puncturedSpectrum R).ι
      = (Stacks.puncturedSpectrum S).ι ≫ Spec.map e.toCommRingCatIso.hom := by
    rw [Iso.trans_hom, Category.assoc, Scheme.Hom.preimageIso_hom_ι, ← Category.assoc,
      Scheme.isoOfEq_hom_ι]
  exact essSurj_finiteEtaleBaseChange_of_commSq hsq h
    (essSurj_finiteEtaleBaseChange_of_isIso ε.hom)

/-- **Purity at a point of the punctured spectrum of `A` is purity of the localization of `A`
at the corresponding prime.** The local ring of the punctured spectrum at a point `𝔮 ≠ 𝔪` is
`A_𝔮`, so purity for `A_𝔮` is purity for that local ring. -/
theorem hasPurity_stalk_puncturedSpectrum {A : Type u} [CommRing A] [IsLocalRing A]
    (q : PrimeSpectrum A) (hq : q ≠ IsLocalRing.closedPoint A)
    (h : HasPurity (Localization.AtPrime q.asIdeal)) :
    HasPurity ((Stacks.puncturedSpectrum A).toScheme.presheaf.stalk
      (Stacks.LocalCohomology.puncturedSpectrumPoint q hq)) :=
  hasPurity_of_ringEquiv
    (Stacks.LocalCohomology.puncturedSpectrumStalkIso q hq).symm.commRingCatIsoToRingEquiv h

/-- **Purity for a local ring of `A_g` is purity for the corresponding local ring of `A`.**
A prime `𝔭` of `A_g` is the image of the prime `𝔮 = 𝔭 ∩ A` of `A`, and `(A_g)_𝔭 ≅ A_𝔮`. -/
theorem hasPurity_atPrime_comap_of_hasPurity_atPrime {A : Type u} [CommRing A] (g : A)
    (p : Ideal (Localization.Away g)) [p.IsPrime]
    (h : HasPurity (Localization.AtPrime p)) :
    HasPurity (Localization.AtPrime
      (p.comap (algebraMap A (Localization.Away g)))) :=
  hasPurity_of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers g) p).symm.toRingEquiv h

/-- The form of `AlgebraicGeometry.hasPurity_atPrime_comap_of_hasPurity_atPrime` in which the
prime of `A` is given and only *recognised* as the contraction of a prime of `A_g`. -/
theorem hasPurity_atPrime_of_eq_comap {A : Type u} [CommRing A] (g : A)
    (p : Ideal (Localization.Away g)) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hq : q = p.comap (algebraMap A (Localization.Away g)))
    (h : HasPurity (Localization.AtPrime p)) :
    HasPurity (Localization.AtPrime q) := by
  subst hq
  exact hasPurity_atPrime_comap_of_hasPurity_atPrime g p h

namespace LocalLefschetzSituation

variable (S : LocalLefschetzSituation.{u})

/-! ### Purity for the hypersurface, given essential surjectivity of restriction -/

/-- **The proof of Tag 0DXZ after its appeal to Tag 0EK9, and of Tag 0BPC after its appeal to
Tag 0EKA.** In the local Lefschetz situation, if the restriction functor `FÉt_U ⥤ FÉt_{U₀}` is
essentially surjective and purity holds for `A`, then purity holds for `A / fA`.

A finite étale cover of `U₀` is by hypothesis the restriction of one of `U`; purity for `A`
extends the latter over `X`; and the restriction of that extension to `X₀` is the extension of
the original cover. -/
@[sga "2 X 3.9" "(ii)"]
theorem hasPurity_quotientRing_of_essSurj_U₀ToU
    (hess : (finiteEtaleBaseChange S.U₀ToU).EssSurj) (hpurity : HasPurity S.A) :
    HasPurity S.quotientRing := by
  show (finiteEtaleBaseChange (Stacks.puncturedSpectrum S.quotientRing).ι).EssSurj
  rw [← S.U₀Open_eq_puncturedSpectrumOpen]
  exact essSurj_finiteEtaleBaseChange_of_commSq S.U₀ToU_comp_immersion hpurity hess

/-! ### Enlarging an open of `U` that contains `U₀` -/

/-- **The last step of the proof of Tag 0EK9.** Let `W` be an open of the punctured spectrum `U`
containing the image of `U₀`, and suppose purity holds for the local ring of `U` at every point
outside `W`. Then a finite étale cover of `U₀` that is the restriction of a cover of `W` is the
restriction of a cover of `U`.

The source extends the cover from `W` to `U` by applying Tag 0BPA once at each of the finitely
many points of `U ∖ W`; here the extension is Tag 0EY7, which does the Noetherian
induction in one step. -/
theorem essImage_finiteEtaleBaseChange_U₀ToU_of_hasPurity (W : S.U.Opens)
    (hW : Set.range S.U₀ToU.base ⊆ Set.range W.ι.base)
    (hpur : ∀ x : S.U, x ∉ W → HasPurity (S.U.presheaf.stalk x))
    {W₀ : FiniteEtaleOver S.U₀}
    (hW₀ : (finiteEtaleBaseChange (IsOpenImmersion.lift W.ι S.U₀ToU hW)).essImage W₀) :
    (finiteEtaleBaseChange S.U₀ToU).essImage W₀ := by
  have hWess : (finiteEtaleBaseChange W.ι).EssSurj :=
    essSurj_finiteEtaleBaseChange_of_hasPurity W.ι fun x hx =>
      hpur x (by rwa [Scheme.Opens.opensRange_ι] at hx)
  have h₂ := essImage_finiteEtaleBaseChange_comp_of_essSurj hWess hW₀
  rwa [IsOpenImmersion.lift_fac] at h₂

/-- The functor form of
`AlgebraicGeometry.LocalLefschetzSituation.essImage_finiteEtaleBaseChange_U₀ToU_of_hasPurity`:
if every finite étale cover of `U₀` already comes from the open `W`, and purity holds at every
point of `U` outside `W`, then restriction `FÉt_U ⥤ FÉt_{U₀}` is essentially surjective. -/
@[sga "2 X 3.9" "(ii)"]
theorem essSurj_finiteEtaleBaseChange_U₀ToU_of_hasPurity (W : S.U.Opens)
    (hW : Set.range S.U₀ToU.base ⊆ Set.range W.ι.base)
    (hpur : ∀ x : S.U, x ∉ W → HasPurity (S.U.presheaf.stalk x))
    (hess : (finiteEtaleBaseChange (IsOpenImmersion.lift W.ι S.U₀ToU hW)).EssSurj) :
    (finiteEtaleBaseChange S.U₀ToU).EssSurj :=
  ⟨fun W₀ => S.essImage_finiteEtaleBaseChange_U₀ToU_of_hasPurity W hW hpur
    (hess.mem_essImage W₀)⟩

/-! ### Purity for the hypersurface from a neighbourhood of `U₀` in `U` -/

/-- **Tag 0DXZ with its appeal to Tag 0EK9 replaced by the data that lemma produces.** Purity
holds for `A / fA` as soon as purity holds for `A` and, for every finite étale cover of `U₀`,
there is an open `W` of `U` containing `U₀` such that the cover is the restriction of a cover of
`W` and purity holds at every point of `U` outside `W`.

The hypothesis is what the source's proof of Tag 0EK9 produces: Tag 0DXY supplies the open `W`
and the cover of `W`, and hypothesis (3) of 0EK9 — purity for `(A_f)_𝔭` at each maximal ideal
`𝔭` of `A_f` — is what makes purity available at the points of `U ∖ W`. -/
theorem hasPurity_quotientRing_of_forall_exists_open
    (h : ∀ W₀ : FiniteEtaleOver S.U₀, ∃ (W : S.U.Opens)
      (hW : Set.range S.U₀ToU.base ⊆ Set.range W.ι.base),
      (∀ x : S.U, x ∉ W → HasPurity (S.U.presheaf.stalk x)) ∧
        (finiteEtaleBaseChange (IsOpenImmersion.lift W.ι S.U₀ToU hW)).essImage W₀)
    (hpurity : HasPurity S.A) :
    HasPurity S.quotientRing := by
  have hess : (finiteEtaleBaseChange S.U₀ToU).EssSurj := ⟨fun W₀ => by
    obtain ⟨W, hW, hpur, hW₀⟩ := h W₀
    exact S.essImage_finiteEtaleBaseChange_U₀ToU_of_hasPurity W hW hpur hW₀⟩
  exact S.hasPurity_quotientRing_of_essSurj_U₀ToU hess hpurity

/-- **Tag 0DXZ with its appeal to Tag 0EK9 replaced by the data and the side condition that
lemma's proof supplies.** Purity holds for `A / fA` as soon as

* purity holds for `(A_f)_𝔭` for every maximal ideal `𝔭 ⊂ A_f` — hypothesis (3) of Tag 0DXZ,
* purity holds for `A` — hypothesis (4) of Tag 0DXZ, and
* for every finite étale cover of `U₀` there is an open `W` of `U` containing `U₀` over which
  the cover is already defined, and every point of `U` outside `W` is the contraction of a
  maximal ideal of `A_f`.

The last item is what the source's proof of Tag 0EK9 produces and asserts: Tag 0DXY supplies the
open `W` and the cover of `W`, and the proof then says that, `W` containing `U₀`, the points of
`U ∖ W` are primes as in hypothesis (3). Hypotheses (1) and (2) of Tag 0DXZ are used by the
source only to reach Tag 0DXY, which is not formalized here, so they do not appear. -/
theorem hasPurity_quotientRing_of_forall_exists_open_of_hasPurity_away
    (haway : ∀ (p : Ideal (Localization.Away S.f)) [p.IsMaximal],
      HasPurity (Localization.AtPrime p))
    (h : ∀ W₀ : FiniteEtaleOver S.U₀, ∃ (W : S.U.Opens)
      (hW : Set.range S.U₀ToU.base ⊆ Set.range W.ι.base),
      (∀ x : S.U, x ∉ W → ∃ (p : Ideal (Localization.Away S.f)) (_ : p.IsMaximal),
          x.1.asIdeal = p.comap (algebraMap S.A (Localization.Away S.f))) ∧
        (finiteEtaleBaseChange (IsOpenImmersion.lift W.ι S.U₀ToU hW)).essImage W₀)
    (hpurity : HasPurity S.A) :
    HasPurity S.quotientRing := by
  refine S.hasPurity_quotientRing_of_forall_exists_open (fun W₀ => ?_) hpurity
  obtain ⟨W, hW, hpts, hW₀⟩ := h W₀
  refine ⟨W, hW, fun x hx => ?_, hW₀⟩
  obtain ⟨p, hpmax, hpc⟩ := hpts x hx
  have : (x.1 : PrimeSpectrum S.A).asIdeal.IsPrime := x.1.isPrime
  exact hasPurity_stalk_puncturedSpectrum x.1 x.2
    (hasPurity_atPrime_of_eq_comap S.f p x.1.asIdeal hpc (haway p))

end LocalLefschetzSituation

end AlgebraicGeometry

end
