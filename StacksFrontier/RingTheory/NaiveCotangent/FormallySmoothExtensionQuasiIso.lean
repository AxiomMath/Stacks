module

public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.Cotangent.SurjectivePresentationSequence
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget

/-!
# A morphism between two formally smooth presentations is a quasi-isomorphism

Let `S` be an `R`-algebra and let `P`, `P'` be two extensions of `S` over `R`, that is two
surjections of `R`-algebras onto `S`.  A morphism of extensions `f : P ⟶ P'` induces a chain map
`NL(P) ⟶ NL(P')` of the two-term complexes `I/I² ⟶ Ω[P.Ring⁄R] ⊗ S`
(`NaiveCotangent.nlExtensionMap`).  If **both** presenting rings are formally smooth over `R`,
that chain map is a quasi-isomorphism.

`NaiveCotangent.nlExtensionMap_isQuasiIso` already gives this when a morphism `P' ⟶ P` exists in
the other direction, which makes the two chain maps mutually inverse up to homotopy.  That
hypothesis is unavailable in the situation this file is written for: `P` is a polynomial
presentation of `S` and `P'` is a formally smooth `R`-algebra surjecting onto `S`, and a morphism
`P' ⟶ P` would be a lift of `P'.Ring ⟶ S` along `P.Ring ⟶ S`, whose kernel is not nilpotent.

## Main results

* `NaiveCotangent.bijective_onH₁_nlExtensionMap_of_formallySmooth`: the induced map on
  `H₁ = ker d` is bijective.  This is Mathlib's
  `Algebra.Extension.H1Cotangent.equivOfFormallySmooth` read on the two-term complex.
* `NaiveCotangent.bijective_onH₀_nlExtensionMap`: the induced map on `H₀ = coker d` is bijective
  for **every** morphism of extensions, no smoothness needed: both cokernels are `Ω[S⁄R]`,
  compatibly.
* `NaiveCotangent.nlExtensionMap_isQuasiIso_of_formallySmooth`: the chain map is a
  quasi-isomorphism.
* `NaiveCotangent.isHomotopyEquiv_toKaehlerChainMap_of_formallySmooth`: for a formally smooth
  `R`-algebra `S`, the augmentation `NL_{S/R} → (0 → Ω_{S/R})` is a homotopy equivalence.
* `NaiveCotangent.isHomotopyEquiv_toKaehlerChainMap_of_algEquiv_mvPolynomial` and
  `NaiveCotangent.isQuasiIso_toKaehlerChainMap_of_algEquiv_mvPolynomial`: the same for a
  polynomial algebra (Stacks 08Q1), and the resulting quasi-isomorphism.

## Route

`H₁` is `Algebra.Extension.H1Cotangent` on the nose — both are `LinearMap.ker` of
`Algebra.Extension.cotangentComplex` — and `NaiveCotangent.ChainMap.onH₁` of the chain map is
`Algebra.Extension.H1Cotangent.map` on the nose, both being the restriction of
`Algebra.Extension.Cotangent.map`.  Mathlib's
`Algebra.Extension.H1Cotangent.equivOfFormallySmooth` says that map is bijective when the two
presenting rings are formally smooth; it is proved there by passing to the infinitesimal
thickenings, where the lift that is unavailable for `P'` itself does exist.

For `H₀` the criterion is `NaiveCotangent.bijective_onH₀_of_surjective_square` applied with both
outer modules `Ω[S⁄R]`, the two projections `Algebra.Extension.toKaehler` and the identity: each
projection is surjective with kernel the image of the differential
(`Algebra.Extension.toKaehler_surjective`,
`Algebra.Extension.exact_cotangentComplex_toKaehler`), and the square commutes by the second
clause of `Stacks.Cotangent.outerTerms_constant`.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
* [Stacks Project, Tag 08Q1](https://stacks.math.columbia.edu/tag/08Q1)
-/

@[expose] public section

namespace NaiveCotangent

open Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {P P' : Extension.{w} R S}

/-- **The map induced on `H₁` by a morphism of two formally smooth presentations is bijective.**

`H₁ (nlOfExtension P)` is `Algebra.Extension.H1Cotangent P` and the induced map is
`Algebra.Extension.H1Cotangent.map`, both on the nose; Mathlib's
`Algebra.Extension.H1Cotangent.equivOfFormallySmooth` says that map is an isomorphism. -/
theorem bijective_onH₁_nlExtensionMap_of_formallySmooth (f : P.Hom P')
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R P'.Ring] :
    Function.Bijective (nlExtensionMap f).onH₁ := by
  have hb : Function.Bijective (Extension.H1Cotangent.map f) := by
    rw [← Extension.H1Cotangent.equivOfFormallySmooth_toLinearMap f]
    exact (Extension.H1Cotangent.equivOfFormallySmooth P P').bijective
  have hmk : ∀ (x : P.Cotangent) (hx : x ∈ LinearMap.ker P.cotangentComplex),
      (Extension.H1Cotangent.map f (show P.H1Cotangent from ⟨x, hx⟩)).1 =
        Extension.Cotangent.map f x := fun _ _ ↦ rfl
  refine bijective_onH₁_of_bijOn _ ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
  · exact (hmk x hx) ▸ (Extension.H1Cotangent.map f (show P.H1Cotangent from ⟨x, hx⟩)).2
  · have h := hb.1 (a₁ := show P.H1Cotangent from ⟨x, hx⟩)
      (a₂ := show P.H1Cotangent from ⟨y, hy⟩)
      (Subtype.ext (((hmk x hx).trans hxy).trans (hmk y hy).symm))
    exact congrArg (fun t : P.H1Cotangent ↦ t.1) h
  · obtain ⟨x, hx⟩ := hb.2 (show P'.H1Cotangent from ⟨y, hy⟩)
    exact ⟨x.1, x.2, (hmk x.1 x.2).symm.trans (congrArg (fun t : P'.H1Cotangent ↦ t.1) hx)⟩

/-- **The map induced on `H₀` by a morphism of extensions is bijective.**  No hypothesis is
needed: the cokernel of the differential of `NL(P)` is `Ω[S⁄R]` for every extension `P`, and the
chain map is compatible with the two projections onto it. -/
theorem bijective_onH₀_nlExtensionMap (f : P.Hom P') :
    Function.Bijective (nlExtensionMap f).onH₀ := by
  have hsq : P'.toKaehler ∘ₗ Extension.CotangentSpace.map f =
      (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) ∘ₗ P.toKaehler :=
    ((Stacks.Cotangent.outerTerms_constant f).2).trans (LinearMap.id_comp _).symm
  exact bijective_onH₀_of_surjective_square (A := nlOfExtension P) (B := nlOfExtension P')
    (Ω[S⁄R]) (Ω[S⁄R]) (nlExtensionMap f) P.toKaehler P'.toKaehler LinearMap.id
    P.toKaehler_surjective
    (LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler)
    (LinearMap.exact_iff.mp P'.exact_cotangentComplex_toKaehler) hsq Function.bijective_id

/-- **A morphism between two formally smooth presentations of `S` over `R` induces a
quasi-isomorphism of naive cotangent complexes.**  For extensions `P`, `P'` of `S` over `R` whose
presenting rings are both formally smooth over `R`, and any morphism of extensions
`f : P ⟶ P'`, the chain map `NL(P) ⟶ NL(P')` is bijective on `H₁` and on `H₀`.

Unlike `NaiveCotangent.nlExtensionMap_isQuasiIso` this does not ask for a morphism in the other
direction. -/
theorem nlExtensionMap_isQuasiIso_of_formallySmooth (f : P.Hom P')
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R P'.Ring] :
    IsQuasiIso (nlExtensionMap f) :=
  ⟨bijective_onH₁_nlExtensionMap_of_formallySmooth f, bijective_onH₀_nlExtensionMap f⟩

/-!
## The naive cotangent complex of a formally smooth algebra

For a formally smooth `R`-algebra `S` the canonical `NL_{S/R}` is homotopy equivalent to the
complex `(0 → Ω_{S/R})`, with `Ω_{S/R}` in degree `0`, through the augmentation
`Algebra.Extension.toKaehler`. In particular this holds for a polynomial algebra (Stacks 08Q1).
-/

section Kaehler

/-- **The naive cotangent complex of an extension with injective differential and projective
differentials.** Let `P` be an extension of the `R`-algebra `S` whose differential
`d : I/I² → Ω_{P/R} ⊗_P S` is injective and such that `Ω_{S/R}` is a projective `S`-module.
Then the augmentation `P.toKaehler` has a section `ψ₀`, and there is `s : Ω_{P/R} ⊗_P S → I/I²`
with `-1 = s ∘ d` and `ψ₀ ∘ toKaehler - 1 = d ∘ s`: these are the data of a homotopy
equivalence between `NL(P)` and `(0 → Ω_{S/R})`. -/
theorem exists_homotopy_toKaehler_of_injective_cotangentComplex (P : Extension.{w} R S)
    [Module.Projective S Ω[S⁄R]] (hd : Function.Injective P.cotangentComplex) :
    ∃ (ψ₀ : Ω[S⁄R] →ₗ[S] P.CotangentSpace) (s : P.CotangentSpace →ₗ[S] P.Cotangent),
      P.toKaehler ∘ₗ ψ₀ = LinearMap.id ∧
      0 - LinearMap.id = s ∘ₗ P.cotangentComplex ∧
      ψ₀ ∘ₗ P.toKaehler - LinearMap.id = P.cotangentComplex ∘ₗ s := by
  have hex := P.exact_cotangentComplex_toKaehler
  obtain ⟨ψ₀, hψ₀⟩ := P.toKaehler.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr Extension.toKaehler_surjective)
  have hψ (y : Ω[S⁄R]) : P.toKaehler (ψ₀ y) = y := LinearMap.congr_fun hψ₀ y
  let p : P.CotangentSpace →ₗ[S] P.CotangentSpace := LinearMap.id - ψ₀ ∘ₗ P.toKaehler
  have hp (x : P.CotangentSpace) : p x ∈ LinearMap.range P.cotangentComplex := by
    rw [← LinearMap.exact_iff.mp hex, LinearMap.mem_ker]
    simp [p, hψ]
  let e₁ := LinearEquiv.ofInjective P.cotangentComplex hd
  let s : P.CotangentSpace →ₗ[S] P.Cotangent :=
    -((e₁.symm : _ →ₗ[S] P.Cotangent) ∘ₗ p.codRestrict _ hp)
  have hds (x : P.CotangentSpace) : P.cotangentComplex (s x) = -p x := by
    have h : ((e₁ (e₁.symm ⟨p x, hp x⟩) : LinearMap.range P.cotangentComplex) :
        P.CotangentSpace) = P.cotangentComplex (e₁.symm ⟨p x, hp x⟩) :=
      LinearEquiv.ofInjective_apply _ _
    rw [LinearEquiv.apply_symm_apply] at h
    change P.cotangentComplex (-(e₁.symm ⟨p x, hp x⟩)) = -p x
    rw [map_neg, ← h]
  refine ⟨ψ₀, s, hψ₀, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    apply hd
    rw [LinearMap.comp_apply, hds]
    simp [p, hex.apply_apply_eq_zero x]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hds]
    simp [p]

/-- For a formally smooth `R`-algebra `S` the differential of the canonical `NL_{S/R}` is
injective: its kernel is `H₁(L_{S/R}) = Algebra.H1Cotangent R S`, which vanishes. -/
theorem cotangentComplex_self_injective_of_formallySmooth [Algebra.FormallySmooth R S] :
    Function.Injective (Generators.self R S).toExtension.cotangentComplex := by
  have : Subsingleton (LinearMap.ker (Generators.self R S).toExtension.cotangentComplex) :=
    (Algebra.FormallySmooth.subsingleton_h1Cotangent : Subsingleton (Algebra.H1Cotangent R S))
  exact LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton

variable (R S) in
/-- The two-term complex `(0 → Ω_{S/R})` of `S`-modules, with `Ω_{S/R}` in degree `0` and the
zero module in degree `1`. -/
noncomputable def kaehlerTwoTerm : TwoTerm S where
  X₁ := PUnit.{v + 1}
  X₀ := Ω[S⁄R]
  d := 0

variable (R S) in
/-- The augmentation `NL_{S/R} → (0 → Ω_{S/R})` of the canonical naive cotangent complex: zero in
degree `1` and `Algebra.Extension.toKaehler : Ω_{R[S]/R} ⊗_{R[S]} S → Ω_{S/R}` in degree `0`. It
is a chain map because `toKaehler ∘ d = 0`. -/
noncomputable def toKaehlerChainMap :
    ChainMap (NL (canonicalGenerators R S)) (kaehlerTwoTerm R S) where
  f₁ := 0
  f₀ := (Generators.self R S).toExtension.toKaehler
  comm := LinearMap.ext fun x =>
    (Extension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero x).symm

/-- **The naive cotangent complex of a formally smooth algebra.** For a formally smooth
`R`-algebra `S`, the augmentation `NL_{S/R} → (0 → Ω_{S/R})` is a homotopy equivalence of
two-term complexes of `S`-modules. -/
theorem isHomotopyEquiv_toKaehlerChainMap_of_formallySmooth [Algebra.FormallySmooth R S] :
    IsHomotopyEquiv (toKaehlerChainMap R S) := by
  have : Module.Projective S Ω[S⁄R] := Algebra.FormallySmooth.projective_kaehlerDifferential
  obtain ⟨ψ₀, s, hψ₀, hs₁, hs₀⟩ := exists_homotopy_toKaehler_of_injective_cotangentComplex _
    (cotangentComplex_self_injective_of_formallySmooth (R := R) (S := S))
  let g : ChainMap (kaehlerTwoTerm R S) (NL (canonicalGenerators R S)) :=
    { f₁ := 0
      f₀ := ψ₀
      comm := (LinearMap.comp_zero _).trans (LinearMap.comp_zero ψ₀).symm }
  refine ⟨g, ⟨s, ?_, hs₀⟩, ⟨0, LinearMap.ext fun _ => rfl, ?_⟩⟩
  · rw [show (g.comp (toKaehlerChainMap R S)).f₁ = 0 from LinearMap.zero_comp _]
    exact hs₁
  · rw [LinearMap.comp_zero]
    exact sub_eq_zero.mpr hψ₀

/-- **The naive cotangent complex of a polynomial algebra** (Stacks 08Q1). Let `R → S` be a
polynomial algebra, that is `S ≅ R[x_i : i ∈ ι]` as `R`-algebras for some set of variables `ι`.
Then the canonical naive cotangent complex `NL_{S/R}` is homotopy equivalent to the complex
`(0 → Ω_{S/R})` with `Ω_{S/R}` in degree `0`, the homotopy equivalence being the augmentation
`toKaehlerChainMap R S`. -/
@[stacks 08Q1 "the homotopy equivalence `NL_{S/R} → (0 → Ω_{S/R})`, for the canonical naive
cotangent complex of any `R`-algebra `S` isomorphic to a polynomial algebra `R[x_i : i ∈ ι]`"]
theorem isHomotopyEquiv_toKaehlerChainMap_of_algEquiv_mvPolynomial {ι : Type*}
    (e : MvPolynomial ι R ≃ₐ[R] S) : IsHomotopyEquiv (toKaehlerChainMap R S) :=
  have : Algebra.FormallySmooth R S := Algebra.FormallySmooth.of_equiv e
  isHomotopyEquiv_toKaehlerChainMap_of_formallySmooth

/-- **Homology of the naive cotangent complex of a polynomial algebra** (Stacks 08Q1). For an
`R`-algebra `S` isomorphic to a polynomial algebra `R[x_i : i ∈ ι]`, the augmentation
`NL_{S/R} → (0 → Ω_{S/R})` is a quasi-isomorphism: `H₁(NL_{S/R}) = 0` and `H₀(NL_{S/R}) = Ω_{S/R}`
through it. -/
@[stacks 08Q1 "the quasi-isomorphism `NL_{S/R} → (0 → Ω_{S/R})` deduced from the homotopy
equivalence, for any `R`-algebra `S` isomorphic to a polynomial algebra `R[x_i : i ∈ ι]`"]
theorem isQuasiIso_toKaehlerChainMap_of_algEquiv_mvPolynomial {ι : Type*}
    (e : MvPolynomial ι R ≃ₐ[R] S) : IsQuasiIso (toKaehlerChainMap R S) :=
  isQuasiIso_of_isHomotopyEquiv (isHomotopyEquiv_toKaehlerChainMap_of_algEquiv_mvPolynomial e)

end Kaehler

end NaiveCotangent

end
