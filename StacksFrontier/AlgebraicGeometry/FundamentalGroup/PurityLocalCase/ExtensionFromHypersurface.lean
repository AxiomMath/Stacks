module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumSectionsDepthTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FullyFaithfulPunctured
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.SerreBranch
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# Extending a finite étale cover from the hypersurface section

Work in the local Lefschetz situation of Tag 0BLF: `A` is a Noetherian local ring with maximal
ideal `𝔪`, `f ∈ 𝔪`, `X = Spec A`, `X₀ = Spec (A / fA)`, and `U`, `U₀` are the punctured spectra
of `A` and of `A / fA`. Let `V` be finite étale over `U` and suppose `V₀ = V ×_U U₀` already
comes from `X₀`, i.e. `V₀ = Y₀ ×_{X₀} U₀` for some `Y₀ → X₀` finite étale. The three lemmas here
give conditions under which `V` itself comes from `X`: `V = Y ×_X U` for some `Y → X` finite
étale.

All three are the two-step argument of the source. Base change along the closed immersion
`X₀ ⟶ X` is an *equivalence* on finite étale covers when `(A, fA)` is a henselian pair — Stacks
09ZS, the scheme form of the lifting lemma Stacks 09ZL that the source quotes — so `Y₀` lifts to
a finite étale `Y → X`. Restriction `FÉt_U ⟶ FÉt_{U₀}` is *fully faithful* under the hypotheses
of the lemma, by Stacks 0BM6 for Tag 0BLS and by Stacks 0EK5 for Tag 0EK6, so the isomorphism
`V ×_U U₀ ≅ (Y ×_X U) ×_U U₀` descends to `V ≅ Y ×_X U`. Both proofs run inside the reduction
to the `f`-adically complete case, Stacks 0BLL, available as
`…LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicCompleteCase`: it turns the
problem over `A` into the same problem over the `𝔪`-adic completion `Â`, where `(Â, fÂ)` is a
henselian pair by Stacks 0ALJ and where the side conditions of the lemmas hold by Stacks 0ALZ
and Stacks 0EHW. Tag 0BLM is Tag 0BLS once depth at least `3` has killed `H¹_𝔪(A)` and
`H²_𝔪(A)` (Stacks 0AVZ). For Tag 0EK6, branch (c)(i) of the hypotheses is reduced to branch
(c)(ii) by `…LocalLefschetzSituation.two_lt_depth_add_ringKrullDim_of_propertySkRing_away`, and
hypothesis (b) is not used: the reduction supplies its own henselian pair `(Â, fÂ)`.

## Main results

* `AlgebraicGeometry.exists_isPullback_finiteEtale_of_isEquivalence_of_fullyFaithful` — the
  descent step, for any commutative square of schemes.
* `AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_dualizingComplex`
  — **Stacks 0EK6**, with its disjunctive hypothesis (c).
* `AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_depth_add_dim`
  — the same under branch (c)(ii) alone.
* `…LocalLefschetzSituation.exists_finiteEtale_extension_of_localCohomology_annihilated`
  — **Stacks 0BLS**.
* `…LocalLefschetzSituation.exists_finiteEtale_extension_of_three_le_depth_self` — **Stacks
  0BLM**.

## Implementation notes

The situation is `AlgebraicGeometry.LocalLefschetzSituation`, Situation [Stacks, Tag 0BLF].
`FÉt_X` is `AlgebraicGeometry.FiniteEtaleOver X` and restriction is
`AlgebraicGeometry.finiteEtaleBaseChange`. "`V = Y ×_X U`" is recorded as a
`CategoryTheory.IsPullback` square rather than an equality of schemes, and likewise the
hypothesis on `V₀`; `V ×_U U₀` is the chosen pullback `pullback pi S.U₀ToU`.

Local cohomology `Hⁱ_𝔪(A)` is `Stacks.LocalCohomology.localCohomologyModule` and depth is
`Module.depth A 𝔪 A`.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
* [Stacks Project, Tag 0BLM](https://stacks.math.columbia.edu/tag/0BLM)
* [Stacks Project, Tag 0EK6](https://stacks.math.columbia.edu/tag/0EK6)
* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
* [Stacks Project, Tag 0BLL](https://stacks.math.columbia.edu/tag/0BLL)
* [Stacks Project, Tag 0ALJ](https://stacks.math.columbia.edu/tag/0ALJ)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.FundamentalGroup Stacks.RelativeSpec
open Stacks.LocalCohomology (localCohomologyModule)
open Stacks.Algebraization (enatToEInt krullDimToEInt)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **The descent step.** Let `i : X₀ ⟶ X`, `j : U ⟶ X`, `i' : U₀ ⟶ U` and `j₀ : U₀ ⟶ X₀` form a
commutative square `i' ≫ j = j₀ ≫ i`. Suppose base change along `i` is an equivalence on finite
étale covers and base change along `i'` is fully faithful on finite étale covers. Then a finite
étale `V ⟶ U` whose base change to `U₀` is `Y₀ ×_{X₀} U₀` for a finite étale `Y₀ ⟶ X₀` is
`Y ×_X U` for a finite étale `Y ⟶ X`.

The equivalence produces a finite étale `Y ⟶ X` with `Y ×_X X₀ ≅ Y₀`. Restricting `Y ×_X U` to
`U₀` gives `Y₀ ×_{X₀} U₀` because the square commutes, and the hypothesis identifies that with
`V ×_U U₀`; full faithfulness of restriction turns this isomorphism over `U₀` into one over
`U`. -/
public theorem exists_isPullback_finiteEtale_of_isEquivalence_of_fullyFaithful
    {X X₀ U U₀ : Scheme.{u}} (i : X₀ ⟶ X) (j : U ⟶ X) (i' : U₀ ⟶ U) (j₀ : U₀ ⟶ X₀)
    (w : i' ≫ j = j₀ ≫ i)
    (hequiv : (finiteEtaleBaseChange i).IsEquivalence)
    (hfull : Nonempty (finiteEtaleBaseChange i').FullyFaithful)
    (V : Scheme.{u}) (pi : V ⟶ U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi i' ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi i') g₀ j₀ f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g j p := by
  let : (finiteEtaleBaseChange i).IsEquivalence := hequiv
  let E := finiteEtaleBaseChange i
  let F := finiteEtaleBaseChange i'
  let G := finiteEtaleBaseChange j
  let J := finiteEtaleBaseChange j₀
  let y₀ : FiniteEtaleOver X₀ :=
    MorphismProperty.Over.mk ⊤ f₀ ⟨inferInstance, inferInstance⟩
  let v : FiniteEtaleOver U :=
    MorphismProperty.Over.mk ⊤ pi ⟨inferInstance, inferInstance⟩
  obtain ⟨y, ⟨e₀⟩⟩ := Functor.EssSurj.mem_essImage (F := E) y₀
  let : F.Full := (Classical.choice hfull).full
  let : F.Faithful := (Classical.choice hfull).faithful
  let ecomp : G ⋙ F ≅ E ⋙ J :=
    (MorphismProperty.Over.pullbackComp
        (P := (finiteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
        i' j).symm ≪≫
      MorphismProperty.Over.pullbackCongr
          (P := (finiteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
          w ≪≫
        MorphismProperty.Over.pullbackComp
          (P := (finiteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
          j₀ i
  let eV₀ : F.obj v ≅ J.obj y₀ := MorphismProperty.Over.isoMk
    (h₀.isoPullback ≪≫ pullbackSymmetry j₀ f₀) (by
      show (h₀.isoPullback ≪≫ pullbackSymmetry j₀ f₀).hom ≫
        pullback.snd f₀ j₀ = pullback.snd pi i'
      simpa only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd] using
        h₀.isoPullback_hom_fst)
  let eVY : v ≅ G.obj y := F.preimageIso (eV₀ ≪≫ J.mapIso e₀.symm ≪≫ (ecomp.app y).symm)
  let eVYOver : Over.mk pi ≅ Over.mk (pullback.fst j y.hom) :=
    (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤ U).mapIso
        eVY ≪≫
      Over.isoMk (pullbackSymmetry y.hom j) (by
        show (pullbackSymmetry y.hom j).hom ≫ pullback.fst j y.hom =
          pullback.snd y.hom j
        exact pullbackSymmetry_hom_comp_fst y.hom j)
  exact ⟨y.left, y.hom, eVYOver.hom.left ≫ pullback.snd j y.hom,
    y.prop.1, y.prop.2, IsPullback.of_over_iso eVYOver⟩


namespace LocalLefschetzSituation

/-- The complete case of the extension: over an `f`-adically complete base `(A, fA)` is a henselian
pair, so the descent step applies once restriction to `U₀` is fully faithful. -/
private theorem exists_finiteEtale_extension_of_isAdicComplete_of_fullyFaithful
    (T : LocalLefschetzSituation.{u}) (hTcomplete : IsAdicComplete (Ideal.span {T.f}) T.A)
    (hfull : HenselianPair T.A T.principalIdeal →
      Nonempty (finiteEtaleBaseChange T.U₀ToU).FullyFaithful)
    (W : Scheme.{u}) (p : W ⟶ T.U) (hpfin : IsFinite p) (hpet : Etale p)
    (Z₀ : Scheme.{u}) (q₀ : Z₀ ⟶ T.X₀) (hqfin : IsFinite q₀) (hqet : Etale q₀)
    (e₀ : pullback p T.U₀ToU ⟶ Z₀)
    (he₀ : IsPullback (pullback.snd p T.U₀ToU) e₀ T.U₀Open.ι q₀) :
    ∃ (Y : Scheme.{u}) (r : Y ⟶ T.X) (g : W ⟶ Y),
      IsFinite r ∧ Etale r ∧ IsPullback p g T.UOpen.ι r := by
  let : IsFinite p := hpfin
  let : Etale p := hpet
  let : IsFinite q₀ := hqfin
  let : Etale q₀ := hqet
  have hT' : HenselianPair T.A T.principalIdeal :=
    let : HenselianRing T.A (Ideal.span {T.f}) := IsAdicComplete.henselianRing T.A _
    henselianPair_of_henselianRing T.A (Ideal.span {T.f})
  exact exists_isPullback_finiteEtale_of_isEquivalence_of_fullyFaithful T.X₀ToX T.UOpen.ι
    T.U₀ToU T.U₀Open.ι T.U₀ToU_comp_immersion
    (finiteEtaleBaseChange_isEquivalence_of_henselianPair T.A T.principalIdeal hT')
    (hfull hT') W p Z₀ q₀ e₀ he₀

/-- Hypothesis (c)(ii) form of [Stacks, Tag 0EK6]. In the local Lefschetz situation let `V` be
finite étale over `U` and assume (a) `A` has a dualizing complex, (b) the pair `(A, (f))` is
henselian, (c)(ii) `depth(A_𝔭) + dim(A/𝔭) > 2` for every prime `𝔭 ⊂ A` with `f ∉ 𝔭`, and
(d) `V ×_U U₀` is `Y₀ ×_{X₀} U₀` for some `Y₀ → X₀` finite étale. Then `V = Y ×_X U` for some
`Y → X` finite étale. The tag itself, with its disjunctive hypothesis (c), is
`exists_finiteEtale_extension_of_dualizingComplex` below.

The proof is the source's. Stacks 0BLL reduces the existence of the extension to the case of an
`f`-adically complete base, which is
`…LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicCompleteCase`, and hypotheses (a)
and (c)(ii) are inherited by the `𝔪`-adic completion through Stacks 0BFR and Stacks 0EHW, which is
`…LocalLefschetzSituation.depthDim_completion`. In the complete case `(A, fA)` is a henselian pair
by Stacks 0ALJ (`IsAdicComplete.henselianRing` and `henselianPair_of_henselianRing`), which is what
Stacks 09ZS (`finiteEtaleBaseChange_isEquivalence_of_henselianPair`) consumes to lift `Y₀` to a
finite étale `Y → X`, and is also hypothesis (b) of Stacks 0EK5 there; the full faithfulness of
restriction is Stacks 0EK5, `fullyFaithful_finiteEtaleRestriction_of_depth_add_dim`. Hypothesis
(b) is not used: the reduction supplies its own henselian pair. -/
public theorem exists_finiteEtale_extension_of_depth_add_dim
    (S : LocalLefschetzSituation.{u})
    (hS : HenselianPair S.A S.principalIdeal)
    (hdual : ∃ omega : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex omega)
    (hdepth : ∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl S.A)) +
        krullDimToEInt (ringKrullDim (S.A ⧸ p.asIdeal)) > ((2 : ℤ) : EInt))
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  have : HenselianPair S.A S.principalIdeal := hS
  refine exists_finiteEtale_extension_of_isAdicCompleteCase S DepthDim ⟨hdual, hdepth⟩
    S.depthDim_completion ?_ V pi Y₀ f₀ g₀ h₀
  intro T hTcomplete hT
  exact exists_finiteEtale_extension_of_isAdicComplete_of_fullyFaithful T hTcomplete
    fun hT' => T.fullyFaithful_finiteEtaleRestriction_of_depth_add_dim hT' hT.1 hT.2

/-- **[Stacks, Tag 0EK6].** In the local Lefschetz situation (Tag 0BLF) let `V` be finite étale
over `U`. Assume

* (a) `A` has a dualizing complex,
* (b) the pair `(A, (f))` is henselian,
* (c) one of the following is true:
  (i) `A_f` is `(S₂)` and every irreducible component of `X` not contained in `X₀` has dimension
  `≥ 3`, or (ii) `depth(A_𝔭) + dim(A/𝔭) > 2` for every prime `𝔭 ⊂ A` with `f ∉ 𝔭`,
* (d) `V₀ = V ×_U U₀` is equal to `Y₀ ×_{X₀} U₀` for some `Y₀ → X₀` finite étale.

Then `V = Y ×_X U` for some `Y → X` finite étale.

Spelling. Hypothesis (a) is `hdual`, (b) is `hS` and (c) is the disjunction `hc`. "`A` has a
dualizing complex" is `∃ ω, Dualizing.IsDualizingComplex ω`, the predicate of [Stacks, Tag 0A7B]
on the derived category of `A`-modules. `(S₂)` for `A_f` is
`PropertySkRing (Localization.Away S.f) 2`, Serre's condition of [Stacks, Tag 031P]. The
irreducible components of `X = Spec A` are the `V(𝔮)` for `𝔮` a minimal prime of `A`; `V(𝔮)` is
contained in `X₀ = V(f)` exactly when `f ∈ 𝔮`, and its dimension is `dim(A/𝔮)`; so the second
half of (c)(i) is the quantification over minimal primes `𝔮` with `f ∉ 𝔮`. In (c)(ii)
`depth(A_𝔭)` is the depth of the `A_𝔭`-module `A_𝔭` along its maximal ideal and the sum is formed
in `ℤ ∪ {±∞}`. Hypothesis (d) and the conclusion record "`V₀ = Y₀ ×_{X₀} U₀`" and
"`V = Y ×_X U`" as cartesian squares (`CategoryTheory.IsPullback`), `V ×_U U₀` being the chosen
pullback.

The proof is the source's. Branch (c)(i) implies branch (c)(ii) for a ring with a dualizing
complex (`two_lt_depth_add_ringKrullDim_of_propertySkRing_away`, through the universal
catenarity of Stacks 0A80), and under (c)(ii) the statement is
`exists_finiteEtale_extension_of_depth_add_dim`: Stacks 0BLL reduces to the complete case,
where Stacks 09ZL/09ZS lifts `Y₀` (the pair being henselian by Stacks 0ALJ) and Stacks 0EK5
descends the isomorphism over `U₀` to one over `U`. -/
@[stacks 0EK6]
public theorem exists_finiteEtale_extension_of_dualizingComplex
    (S : LocalLefschetzSituation.{u})
    (hdual : ∃ omega : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex omega)
    (hS : HenselianPair S.A S.principalIdeal)
    (hc : (PropertySkRing (Localization.Away S.f) 2 ∧
        ∀ q : Ideal S.A, q ∈ minimalPrimes S.A → S.f ∉ q →
          (3 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ q)) ∨
      ∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
        enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl S.A)) +
          krullDimToEInt (ringKrullDim (S.A ⧸ p.asIdeal)) > ((2 : ℤ) : EInt))
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  have hdepth : ∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl S.A)) +
        krullDimToEInt (ringKrullDim (S.A ⧸ p.asIdeal)) > ((2 : ℤ) : EInt) := by
    rcases hc with ⟨hS₂, hcomponents⟩ | hdepth
    · obtain ⟨omega, homega⟩ := hdual
      exact S.two_lt_depth_add_ringKrullDim_of_propertySkRing_away omega homega hS₂ hcomponents
    · exact hdepth
  exact S.exists_finiteEtale_extension_of_depth_add_dim hS hdual hdepth V pi Y₀ f₀ g₀ h₀

/-- **[Stacks, Tag 0BLS].** In the local Lefschetz situation let `V` be finite étale over `U` and
assume (1) `H¹_𝔪(A)` and `H²_𝔪(A)` are annihilated by a power of `f`, and (2) `V ×_U U₀` is
`Y₀ ×_{X₀} U₀` for some `Y₀ → X₀` finite étale. Then `V = Y ×_X U` for some `Y → X` finite étale.

The proof is the source's. Stacks 0BLL reduces the existence of the extension to the case of an
`f`-adically complete base, which is
`…LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicCompleteCase`, and the annihilation
hypothesis is inherited by the `𝔪`-adic completion through Stacks 0ALZ, which is
`…LocalLefschetzSituation.annihilated_completion`. In the complete case `(A, fA)` is a henselian
pair by Stacks 0ALJ (`IsAdicComplete.henselianRing` and `henselianPair_of_henselianRing`); that
henselian pair feeds Stacks 09ZS, lifting `Y₀` to a finite étale `Y → X`, and is also hypothesis
(2) of Stacks 0BM6, which supplies the full faithfulness of restriction that the descent step
needs, as `fullyFaithful_finiteEtaleRestriction_of_annihilated_of_henselian`. -/
@[stacks 0BLS]
public theorem exists_finiteEtale_extension_of_localCohomology_annihilated
    (S : LocalLefschetzSituation.{u})
    (h1 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 1,
      S.f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 2,
      S.f ^ n • x = 0)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  refine exists_finiteEtale_extension_of_isAdicCompleteCase S Annihilated ⟨h1, h2⟩
    S.annihilated_completion ?_ V pi Y₀ f₀ g₀ h₀
  intro T hTcomplete hT
  exact exists_finiteEtale_extension_of_isAdicComplete_of_fullyFaithful T hTcomplete fun hT' =>
    T.fullyFaithful_finiteEtaleRestriction_of_annihilated_of_henselian (Or.inr hT') hT.1 hT.2

/-- **[Stacks, Tag 0BLM].** In the local Lefschetz situation let `V` be finite étale over `U` and
assume (1) `A` has depth at least `3`, and (2) `V ×_U U₀` is `Y₀ ×_{X₀} U₀` for some `Y₀ → X₀`
finite étale. Then `V = Y ×_X U` for some `Y → X` finite étale.

This is the source's proof. Depth at least `3` forces `H¹_𝔪(A) = H²_𝔪(A) = 0` by
[Stacks, Tag 0AVZ] (`Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth`), so
both are annihilated by `f ^ 0`, and the conclusion is [Stacks, Tag 0BLS] at `S`, which is
`exists_finiteEtale_extension_of_localCohomology_annihilated`. -/
@[stacks 0BLM]
public theorem exists_finiteEtale_extension_of_three_le_depth_self
    (S : LocalLefschetzSituation.{u})
    (hdepth : 3 ≤ Module.depth S.A (maximalIdeal S.A) S.A)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  have hvan : ∀ i : ℕ, i < 3 → ∃ n : ℕ, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) (i : ℤ),
      S.f ^ n • x = 0 := fun i hi =>
    ⟨0, fun _ =>
      (Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth S.A
        (maximalIdeal S.A) (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A))
        (ModuleCat.of S.A S.A) (by simpa using (maximalIdeal.isMaximal S.A).ne_top) i
        (lt_of_lt_of_le (by exact_mod_cast hi) hdepth)).elim _ _⟩
  exact S.exists_finiteEtale_extension_of_localCohomology_annihilated (hvan 1 (by norm_num))
    (hvan 2 (by norm_num)) V pi Y₀ f₀ g₀ h₀

end LocalLefschetzSituation

end AlgebraicGeometry

end
