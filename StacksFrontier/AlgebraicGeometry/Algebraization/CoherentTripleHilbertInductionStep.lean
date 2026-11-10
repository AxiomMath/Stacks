module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelNonvanishing
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInduction
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSequence
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroDimensionalVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecInjective

/-!
# The Hilbert polynomial of a coherent triple

Let `A` be a Noetherian local ring, `f ∈ 𝔪` a nonzerodivisor and `L` an invertible coherent
triple. For every coherent triple `T = (F, F₀, α)`, the Euler characteristics of the twists
`T ⊗ L^{⊗ n}` are the values at `n ∈ ℤ` of a rational polynomial whose degree is at most
`dim(Supp F)`, the dimension being truncated at `0`.

## Main results

* `Stacks.Algebraization.CoherentTriple.exists_shortExact_twistZ_cokernelTriple_of_mono`: a
  morphism `T ⊗ L^{⊗ 0} ⟶ T ⊗ L^{⊗ 1}` that is a monomorphism on both members, with
  `f`-torsion-free cokernel, gives short exact sequences
  `0 → T ⊗ L^{⊗ n} → T ⊗ L^{⊗ (n + 1)} → G ⊗ L^{⊗ n} → 0` with `G` its cokernel triple.
* `Stacks.Algebraization.hasHilbertInductionStep`: every invertible triple `L` satisfies
  `Stacks.Algebraization.HasHilbertInductionStep`.
* `Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp`: the Euler characteristics of
  the integer twists of a coherent triple are the values of a rational polynomial whose degree is
  at most the dimension of the support of the punctured-spectrum member, truncated at `0`.
* `Stacks.Algebraization.exists_polynomial_eulerCharacteristic_twistZ`: the same, with the degree
  bounded by any natural number bounding the dimension of the support.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open Stacks.RelativeVeryAmple (tensorModules)

universe u

namespace Stacks.Algebraization

/-! ### Quasi-coherence -/

/-- The tensor product `Stacks.RelativeVeryAmple.tensorModules X M N` of quasi-coherent modules
`M` and `N` is quasi-coherent. -/
public theorem isQuasicoherent_tensorModules (X : Scheme.{u}) (M N : X.Modules)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (tensorModules X M N).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace M N hM hN

/-- The punctured-spectrum member of a coherent triple is quasi-coherent. -/
public theorem CoherentTriple.isQuasicoherent_F {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T : CoherentTriple A f) : T.F.IsQuasicoherent :=
  have := T.coherent_F
  _root_.isQuasicoherent_of_isCoherent _

/-- The closed-fibre member of a coherent triple is quasi-coherent. -/
public theorem CoherentTriple.isQuasicoherent_F₀ {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T : CoherentTriple A f) : T.F₀.IsQuasicoherent :=
  have := T.coherent_F₀
  _root_.isQuasicoherent_of_isCoherent _

/-! ### Short exact sequences of twists -/

/-- For a morphism `φ : T ⊗ L^{⊗ 0} ⟶ T ⊗ L^{⊗ 1}` that is a monomorphism on both members and has
`f`-torsion-free cokernel on the punctured spectrum, there are short exact sequences
`0 → T ⊗ L^{⊗ n} → T ⊗ L^{⊗ (n + 1)} → G ⊗ L^{⊗ n} → 0` for every `n ∈ ℤ`, with `G` the cokernel
triple of `φ`. -/
public theorem CoherentTriple.exists_shortExact_twistZ_cokernelTriple_of_mono {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (φ : (T.twistZ L hL 0).Hom (T.twistZ L hL (0 + 1)))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) (hmono : Mono φ.onPunctured)
    (hmono₀ : Mono φ.onClosedFibre) :
    ∃ (u : ∀ n : ℤ, (T.twistZ L hL n).Hom (T.twistZ L hL (n + 1)))
      (v : ∀ n : ℤ, (T.twistZ L hL (n + 1)).Hom
        ((CoherentTriple.cokernelTriple φ htf).twistZ L hL n)),
      ∀ n : ℤ, CoherentTriple.ShortExact (u n) (v n) := by
  let := (T.isIso_twistZZeroHom hL).1
  let := (T.isIso_twistZZeroHom hL).2
  let := (T.isIso_twistZOneHom hL).1
  let := (T.isIso_twistZOneHom hL).2
  let := CoherentTriple.isIso_inverse_onPunctured (T.twistZZeroHom hL)
  let := CoherentTriple.isIso_inverse_onClosedFibre (T.twistZZeroHom hL)
  have hse := ((CoherentTriple.shortExact_cokernelHom φ htf hmono hmono₀).isoComp
    (T.twistZZeroHom hL).inverse).midIso (T.twistZOneHom hL)
  have key : ∀ n : ℤ, ∃ (u : (T.twistZ L hL n).Hom (T.twistZ L hL (n + 1)))
      (v : (T.twistZ L hL (n + 1)).Hom ((CoherentTriple.cokernelTriple φ htf).twistZ L hL n)),
      CoherentTriple.ShortExact u v := by
    intro n
    let := (T.isIso_tensorInvertibleTwistZSuccDegreeOneHom hL n).1
    let := (T.isIso_tensorInvertibleTwistZSuccDegreeOneHom hL n).2
    exact ⟨_, _, (hse.twistZ L hL n).midIso (T.tensorInvertibleTwistZSuccDegreeOneHom hL n)⟩
  choose u v huv using key
  exact ⟨u, v, huv⟩

/-! ### The induction step -/

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}

/-- For a Noetherian local ring `A`, a nonzerodivisor `f` in the maximal ideal and an invertible
triple `L`, the geometric input `Stacks.Algebraization.HasHilbertInductionStep` of the induction
step holds. -/
public theorem hasHilbertInductionStep (hf : f ∈ maximalIdeal A)
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L) :
    HasHilbertInductionStep L hL := by
  let := isLocalRing_quotient_span hf
  let := hL.invertible_F
  let := hL.invertible_F₀
  let := isInvertibleModule_tensorPowScheme
    (Stacks.Divisors.puncturedSpectrum A).toScheme L.F 0
  rintro T -
  refine
    Exists.elim (Stacks.SectionProduct.exists_tensorSheaf_iso_unit L.F) fun N hN =>
    Exists.elim (Stacks.SectionProduct.exists_tensorSheaf_iso_unit L.F₀) fun N₀ hN₀ =>
    Exists.elim (exists_sectionPair_nonvanishing_on_associatedPoints_depthFree hf hL T)
      fun x h₁ => Exists.elim h₁ fun x₀ h₂ => ?_
  obtain ⟨hx, hsupp⟩ := h₂
  obtain ⟨hsupp₁, hsupp₂⟩ := Set.union_subset_iff.mp hsupp
  have hmono := (T.quotientTriple hf).mono_onPunctured_mulSectionTwistZOfGlobalSections L hL
    x x₀ hx 0 (CoherentTriple.isQuasicoherent_F _)
    (isQuasicoherent_tensorModules _ _ _ (CoherentTriple.isQuasicoherent_F _)
      (CoherentTriple.isQuasicoherent_F L))
    hN.some hsupp₁
  have hcok : (cokernel (Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom
      (T.quotientTriple hf).F (scalarGlobal A f) 1)).IsQuasicoherent :=
    have := CoherentTriple.isQuasicoherent_F (T.quotientTriple hf)
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _
  have hinv := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule
    (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F 0)
  have htf :=
    (T.quotientTriple hf).isFTorsionFree_cokernel_onPunctured_mulSectionTwistZOfGlobalSections
      L hL x x₀ hx 0 hmono
      (isQuasicoherent_tensorModules _ _ _ hcok hinv)
      (isQuasicoherent_tensorModules _ _ _ (isQuasicoherent_tensorModules _ _ _ hcok hinv)
        (CoherentTriple.isQuasicoherent_F L))
      hN.some hsupp₂
  have hmono₀ := T.mono_onClosedFibre_quotientTriple_of_nonvanishing hf L hL x x₀ hx 0
    (CoherentTriple.isQuasicoherent_F₀ _)
    (isQuasicoherent_tensorModules _ _ _ (CoherentTriple.isQuasicoherent_F₀ _)
      (CoherentTriple.isQuasicoherent_F₀ L))
    hN₀.some hsupp
  have hdrop := (T.quotientTriple hf).dimension_drop_cokernelTriple_mulSectionTwistZ L hL
    (Scheme.Modules.unitHomEquivTop L.F x) (Scheme.Modules.unitHomEquivTop L.F₀ x₀)
    (hcompat_of_eq_globalSectionsMap x x₀ hx) 0 htf hN.some
    (Stacks.NonvanishingSpelling.forall_exists_opens_mem_stalkNonvanishingLocus_unitHomEquivTop
      (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x hsupp₁)
  refine Exists.elim ((T.quotientTriple hf).exists_shortExact_twistZ_cokernelTriple_of_mono hL
    ((T.quotientTriple hf).mulSectionTwistZOfGlobalSections L hL x x₀ hx 0) htf hmono hmono₀)
    fun u h₃ => Exists.elim h₃ fun v hseq => ?_
  exact ⟨T.closedPointTriple hf, T.quotientTriple hf, _, T.closedPointHom hf, T.quotientHom hf,
    u, v, isZero_cokernel_of_epi (𝟙 T.F), T.shortExact_closedPointReduction hf, hseq,
    hdrop.1, hdrop.2,
    fun hdim hG => CoherentTriple.eulerCharacteristic_eq_zero_of_shortExact_twistZ_quotientTriple
      hf T hL (hseq 0) hdim hG⟩

/-! ### The Hilbert polynomial -/

/-- Let `A` be a Noetherian local ring, `f ∈ 𝔪` a nonzerodivisor, and `(L, L₀, λ)` an invertible
coherent triple. For every coherent triple `T = (F, F₀, α)` there is a polynomial `P ∈ ℚ[t]` with

`χ(T ⊗ (L, L₀, λ)^{⊗ n}) = P(n)` for every `n ∈ ℤ`,

and `deg P ≤ dim(Supp F)`, the dimension being truncated at `0`. -/
@[stacks 0F27]
public theorem exists_polynomial_natDegree_le_dim_supp (hf : f ∈ maximalIdeal A)
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L) (T : CoherentTriple A f) :
    ∃ P : Polynomial ℚ,
      (P.natDegree : WithBot ℕ∞) ≤ max 0 (topologicalKrullDim ↥(SheafOfModules.supp T.F)) ∧
        ∀ n : ℤ, (((T.twistZ L hL n).eulerCharacteristic : ℤ) : ℚ) = P.eval (n : ℚ) :=
  exists_polynomial_natDegree_le_dim_supp_of_hasInductionStep hf L hL
    (hasHilbertInductionStep hf L hL) T

/-- Let `A` be a Noetherian local ring, `f ∈ 𝔪` a nonzerodivisor, and `L` an invertible coherent
triple. For every coherent triple `T = (F, F₀, α)` with `dim(Supp F) ≤ d` for a natural number `d`,
there is a polynomial `P ∈ ℚ[t]` of degree at most `d` with `χ(T ⊗ L^{⊗ n}) = P(n)` for every
`n ∈ ℤ`. -/
public theorem exists_polynomial_eulerCharacteristic_twistZ (hf : f ∈ maximalIdeal A)
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L) (d : ℕ)
    (T : CoherentTriple A f)
    (hT : topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((d : ℕ) : WithBot ℕ∞)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ d ∧
      ∀ n : ℤ, (((T.twistZ L hL n).eulerCharacteristic : ℤ) : ℚ) = P.eval (n : ℚ) :=
  exists_polynomial_eulerCharacteristic_twistZ_of_hasInductionStep hf L hL
    (hasHilbertInductionStep hf L hL) d T hT

end Stacks.Algebraization

end
