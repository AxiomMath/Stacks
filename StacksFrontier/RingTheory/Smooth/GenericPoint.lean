module

public import StacksFrontier.RingTheory.Smooth.Field
public import StacksFrontier.RingTheory.Smooth.SmoothAt
import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.GenericFinitePresentation.AwayMapMul
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness at the generic point and separability

Stacks 07ND. Let `R → S` be an injective finite type ring map of domains, and let `K` and `L` be
the fraction fields of `R` and `S`. Then `R → S` is smooth at `𝔮 = (0)` — some nonzero `g ∈ S`
has `S_g` smooth over `R` (Definition 00TB) — if and only if `L/K` is separable.

## Main results

* `Algebra.smoothAt_bot_iff_isSeparableExtension`: Stacks 07ND.

## Implementation notes

Smoothness at `(0)` is `Algebra.SmoothAt R S ⊥`, Definition 00TB, which asks for some `S_g`,
`g ≠ 0`, smooth — in particular of finite presentation — over `R`. The formal-smoothness form, in
which smoothness at `(0)` is Mathlib's `Algebra.IsSmoothAt R ⊥`, that is formal smoothness of
`S_{(0)} = L` over `R`, is `Algebra.isSmoothAt_bot_iff_isSeparableExtension`; this file transports
it to Definition 00TB.

* `⇒`: Definition 00TB implies formal smoothness of the local ring
  (`Algebra.isSmoothAt_of_smoothAt`).
* `⇐`: generic finite presentation (Lemma 00FG,
  `GenericFinitePresentation.generic_finite_presentation`) gives nonzero `f ∈ R` and `g ∈ S` with
  `R_f → S_{fg}` of finite presentation, so `R → S_h` is of finite presentation for the nonzero
  `h = fg`; this is where `Algebra.FiniteType R S` and the injectivity of `R → S` are used, as in
  the source's proof. The local ring `S_{(0)}` is also the local ring of `S_h` at `(0) S_h`, so it
  is formally smooth over `R` there too, and Lemma 00TA (`Algebra.IsSmoothAt.exists_notMem_smooth`)
  for the finitely presented `S_h` produces `a / h^n ∉ (0) S_h` with `(S_h)_{a / h^n} = S_{ha}`
  smooth over `R`.

The source's proof of `⇐` instead reduces to `K → S ⊗_R K` and uses Lemmas 00TG and 00TV; the
argument through formal smoothness of `L` is described in `StacksFrontier.RingTheory.Smooth.Field`.

The hypotheses are those of `Algebra.isSmoothAt_bot_iff_isSeparableExtension`: the fraction fields
are abstract, pinned by `IsFractionRing`, and the injectivity of `R → S` is implied by the
compatible `K`-algebra structure on `L` (`IsScalarTower R S L`, `IsScalarTower R K L`) rather than
assumed.

## References

* [Stacks 07ND](https://stacks.math.columbia.edu/tag/07ND)
  (`algebra-lemma-smooth-at-generic-point`).
* [Stacks 00TB](https://stacks.math.columbia.edu/tag/00TB), smoothness at a prime.
* [Stacks 00TA](https://stacks.math.columbia.edu/tag/00TA), the smooth locus is open.
* [Stacks 00FG](https://stacks.math.columbia.edu/tag/00FG), generic finite presentation.

## Tags

smooth ring map, generic point, fraction field, separable field extension
-/

@[expose] public section

namespace Stacks.Smooth.GenericPointSmoothAt

/-- Definition 00TB from `Algebra.IsSmoothAt`: if `S_q` is formally smooth over `R` and `S_h` is
of finite presentation over `R` for some `h ∉ q`, then `R → S` is smooth at `q`. The local ring
`S_q` is also the local ring of `S_h` at `q S_h`, so Lemma 00TA applies to `S_h`, and an element
`a / h^n` of `S_h` it produces gives the element `h a` of `S`. -/
private theorem smoothAt_of_isSmoothAt_of_finitePresentation_away {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] (hq : Algebra.IsSmoothAt R q) {h : S}
    (hh : h ∉ q) [Algebra.FinitePresentation R (Localization.Away h)] :
    Algebra.SmoothAt R S q := by
  have : (q.map (algebraMap S (Localization.Away h))).IsPrime :=
    Stacks.Smooth.FlatFibreCriterion.isPrime_map_algebraMap_of_notMem q hh
  let : Algebra (Localization.Away h) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers h) q.primeCompl
      (Submonoid.powers_le.mpr hh)
  have : IsScalarTower S (Localization.Away h) (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsScalarTower R (Localization.Away h) (Localization.AtPrime q) := .to₁₃₄ _ S _ _
  have : IsLocalization.AtPrime (Localization.AtPrime q)
      (q.map (algebraMap S (Localization.Away h))) :=
    Stacks.Smooth.FlatFibreCriterion.isLocalization_atPrime_map_of_notMem
      (B := Localization.Away h) (C := Localization.AtPrime q) hh
  have : Algebra.IsSmoothAt R (q.map (algebraMap S (Localization.Away h))) :=
    .of_equiv ((IsLocalization.algEquiv (q.map (algebraMap S (Localization.Away h))).primeCompl
      (Localization.AtPrime q)
      (Localization.AtPrime (q.map (algebraMap S (Localization.Away h))))).restrictScalars R)
  obtain ⟨f, hf, hfsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R
    (q.map (algebraMap S (Localization.Away h)))
  have hassoc := IsLocalization.Away.associated_sec_fst (S := Localization.Away h) h f
  have : IsLocalization.Away (h * (IsLocalization.Away.sec h f).1) (Localization.Away f) :=
    .mul_of_associated _ _ f hassoc
  exact ⟨h * (IsLocalization.Away.sec h f).1, ‹q.IsPrime›.mul_notMem hh fun hmem ↦
    hf ((Ideal.mem_iff_of_associated hassoc).mp (Ideal.mem_map_of_mem _ hmem)),
    .of_equiv ((Localization.algEquiv (Submonoid.powers (h * (IsLocalization.Away.sec h f).1))
      (Localization.Away f)).restrictScalars R).symm⟩

end Stacks.Smooth.GenericPointSmoothAt

/-- **Smoothness at the generic point is separability of the fraction field extension**
(Stacks 07ND). Let `R → S` be a finite type map of domains, let `K` and `L` be the fraction fields
of `R` and `S`, and let `L` be a `K`-algebra compatibly with both towers — which forces `R → S` to
be injective. Then `R → S` is smooth at `𝔮 = (0)` in the sense of Definition 00TB — some nonzero
`g ∈ S` has `S_g` smooth over `R` — if and only if `L/K` is separable. -/
@[stacks 07ND "Smoothness at `(0)` is Definition 00TB, `Algebra.SmoothAt R S (⊥ : Ideal S)`: some
`g ∉ (0)` with `Localization.Away g` smooth (so of finite presentation) over `R`, not Mathlib's
`Algebra.IsSmoothAt`, which is only formal smoothness of `S_{(0)}`; the formal-smoothness form is
`Algebra.isSmoothAt_bot_iff_isSeparableExtension`, and the passage to 00TB uses generic finite
presentation (00FG). Separability of the possibly transcendental extension `L/K` is
`Algebra.IsSeparableExtension`, Definition 030O (2), not `Algebra.IsSeparable`. The fraction fields
are abstract, pinned by `IsFractionRing`, and the source's injectivity of `R → S` is implied by
the compatible `K`-algebra structure on `L` rather than assumed. See the module docstring."]
public theorem Algebra.smoothAt_bot_iff_isSeparableExtension (R S K L : Type*)
    [CommRing R] [CommRing S] [Field K] [Field L] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R S L] [IsScalarTower R K L] :
    Algebra.SmoothAt R S (⊥ : Ideal S) ↔ Algebra.IsSeparableExtension K L := by
  refine ⟨fun h ↦ (Algebra.isSmoothAt_bot_iff_isSeparableExtension R S K L).1
    (Algebra.isSmoothAt_of_smoothAt R S h), fun hsep ↦ ?_⟩
  have hinj : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L,
      RingHom.coe_comp]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  obtain ⟨f, g, hf, hg, hfp⟩ := GenericFinitePresentation.generic_finite_presentation hinj
  have : Algebra.FinitePresentation R (Localization.Away (algebraMap R S f * g)) := by
    rw [← RingHom.finitePresentation_algebraMap, ← Localization.awayMapMul_comp_algebraMap f g]
    exact hfp.comp
      (RingHom.finitePresentation_algebraMap.2 (IsLocalization.Away.finitePresentation f))
  exact Stacks.Smooth.GenericPointSmoothAt.smoothAt_of_isSmoothAt_of_finitePresentation_away ⊥
    ((Algebra.isSmoothAt_bot_iff_isSeparableExtension R S K L).2 hsep)
    (h := algebraMap R S f * g)
    (by simpa using mul_ne_zero ((map_ne_zero_iff _ hinj).2 hf) hg)

end
