module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Support.DepthAdicCompletion
public import StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibre
public import StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibreUniverse
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.RingTheory.Catenary.Universes
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth plus dimension is unchanged by adic completion

Let `A` be a Noetherian ring admitting a dualizing complex, let `I` be an ideal, let `M` be a
finite `A`-module and write `A'`, `M'` for the `I`-adic completions. If `𝔭' ⊆ 𝔮'` are primes of
`A'` with `𝔮' ∈ V(I A')`, lying over `𝔭 ⊆ 𝔮` in `A`, then

`depth(M'_{𝔭'}) + dim((A'/𝔭')_{𝔮'}) = depth(M_𝔭) + dim((A/𝔭)_𝔮)`.

## Main results

* `Module.depth_add_ringKrullDim_quotient_localization_adicCompletion`: the displayed equality.
* `Module.depth_add_ringKrullDim_quotient_adicCompletion`: its special case for `A` local,
  `I ≤ 𝔪_A` and `𝔮'` the maximal ideal of `A'`, where the two localizations are `A'/𝔭'` and
  `A/𝔭` themselves.
* `Module.depth_add_ringKrullDim_quotient_localization_adicCompletion_of_isUniversallyCatenary`
  and `Module.depth_add_ringKrullDim_quotient_adicCompletion_of_isUniversallyCatenary`: the same
  two statements for `A` universally catenary whose local rings have Cohen--Macaulay formal
  fibres, which is all the proof takes from the dualizing complex.

## Proof outline

Depth is additive along the flat local map `A_𝔭 → A'_{𝔭'}`
(`AlgebraicGeometry.depth_localized_adicCompletion`, from Stacks 0338): the depth of `M'_{𝔭'}` is
the depth of `M_𝔭` plus the depth of the fibre `A'_{𝔭'}/𝔭A'_{𝔭'}`. The fibre is Cohen--Macaulay,
because the fibres of `A → A'` are, so its depth is its dimension, which is the height of the
image `𝔭'` in `A'/𝔭A'`
(`Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height`, from Stacks 0AWY through the
formal-fibre formalism of Stacks 0BJ9 and 0BK9). Finally the dimension of `(A/𝔭)_𝔮` splits as
that height plus the dimension of `(A'/𝔭')_{𝔮'}`
(`Stacks.AdicCompletionDimension.height_add_height_quotient_eq_height_quotient_adicCompletion`,
from Ratliff's theorem Stacks 0AW6 and Stacks 0AW4), `A` being universally catenary by
Stacks 0A80. Adding up gives the display.

## Implementation notes

The hypothesis `𝔮' ∈ V(I A')` is spelled `I·A' ≤ 𝔮'`, and `𝔭' ⊆ 𝔮'` is a hypothesis rather than
notation. The two local rings of the display are spelled as quotients of localizations: `(A/𝔭)_𝔮`
is `A_𝔮 ⧸ 𝔭 A_𝔮`, which needs no primality instance for the image of `𝔮` in `A/𝔭`, and is
identified with the localization of `A/𝔭` at that image inside the proof
(`Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime`).

The module universe of the dualizing complex is arbitrary, as the source's hypothesis "`A` has a
dualizing complex" is. Stacks 0AWY and Stacks 0A80 are available in the library only for a
complex whose modules live in the universe of the ring, so both are applied to `ULift A`, which
is a localization of `A` and therefore inherits the dualizing complex at its own module
universe; `A` is a quotient of `ULift A`, and the statement transports back along that
isomorphism.

The first display, the inequality `depth(M_𝔭) ≤ depth(M'_{𝔭'})`, is
`Module.depth_localized_adicCompletion_le`.

## References

* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338), additivity of depth.
* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY), the formal fibres.
* [Stacks Project, Tag 0AW6](https://stacks.math.columbia.edu/tag/0AW6), Ratliff's theorem.
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80), universal catenarity.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Module

/-- **A Noetherian ring with a dualizing complex is universally catenary** (Stacks 0A80), with the
dualizing complex read at an arbitrary module universe. -/
public theorem _root_.Dualizing.isUniversallyCatenary_of_isDualizingComplex_univ {B : Type u}
    [CommRing B] [IsNoetherianRing B] {K : DerivedCategory (ModuleCat.{w} B)}
    (hK : Dualizing.IsDualizingComplex K) : Ring.IsUniversallyCatenary B := by
  let e : B ≃+* ULift.{w} B := ULift.ringEquiv.symm
  let _ : Algebra B (ULift.{w} B) := e.toRingHom.toAlgebra
  let M₀ : Submonoid (ULift.{w} B) := IsUnit.submonoid (ULift.{w} B)
  let M : Submonoid B := M₀.map e.symm.toRingHom
  have hloc : IsLocalization M (ULift.{w} B) :=
    IsLocalization.isLocalization_of_base_ringEquiv M₀ (ULift.{w} B) e.symm
  have hN : IsNoetherianRing (ULift.{w} B) :=
    IsLocalization.isNoetherianRing M (ULift.{w} B) inferInstance
  have hL := Dualizing.isDualizingComplex_localization (B := ULift.{w} B) M K hK
  exact Ring.IsUniversallyCatenary.of_surjective' (f := e.symm.toRingHom) e.symm.surjective
    (Dualizing.isUniversallyCatenary_of_isDualizingComplex hL)

/-- **A Noetherian ring with a dualizing complex is universally catenary**, with the dualizing
complex read at an arbitrary module universe: this is
`Dualizing.isUniversallyCatenary_of_isDualizingComplex_univ`. -/
private alias isUniversallyCatenary_of_isDualizingComplex_univ := Dualizing.isUniversallyCatenary_of_isDualizingComplex_univ

/-- Bookkeeping for the depth-plus-dimension equality: if `a = b + c` and `c + d = e`, then
`a + d = b + e`, after coercion to `WithBot ℕ∞`. -/
private theorem coe_add_eq_of_add_eq {a b c : ℕ∞} {d e : WithBot ℕ∞} (h : a = b + c)
    (h' : (c : WithBot ℕ∞) + d = e) : (a : WithBot ℕ∞) + d = b + e := by
  rw [h, ← h', WithBot.coe_add, add_assoc]

/-- **Stacks Project, Tag 0EHW, second display.** Let `B` be a Noetherian local ring admitting a
dualizing complex, let `J` be an ideal contained in the maximal ideal, let `N` be a finite
`B`-module, and write `B'` and `N'` for the `J`-adic completions. For a prime `P'` of `B'` lying
over a prime `P` of `B`,

`depth(N'_{P'}) + dim(B'/P') = depth(N_P) + dim(B/P)`.

This is the special case `J ≤ 𝔪_B`, `Q' = 𝔪_{B'}` of
`Module.depth_add_ringKrullDim_quotient_localization_adicCompletion`, in which the two
localizations of the source's display are the rings `B'/P'` and `B/P` themselves. -/
@[ega "0 16.4.6" "(iv), special case"]
public theorem depth_add_ringKrullDim_quotient_adicCompletion
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{w} B), Dualizing.IsDualizingComplex K)
    (J : Ideal B) (hJ : J ≤ maximalIdeal B)
    (N : Type v) [AddCommGroup N] [Module B N] [Module.Finite B N]
    (P : Ideal B) [P.IsPrime]
    (P' : Ideal (AdicCompletion J B)) [P'.IsPrime] [P'.LiesOver P] :
    ((Module.depth (Localization.AtPrime P') (maximalIdeal (Localization.AtPrime P'))
            (LocalizedModule P'.primeCompl (AdicCompletion J N)) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (AdicCompletion J B ⧸ P') =
      ((Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
            (LocalizedModule P.primeCompl N) : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
  obtain ⟨K, hK⟩ := hdual
  have hfibre :=
    Stacks.AdicCompletionFibreUniverse.depth_fibre_localization_eq_height_univ hK J P P'
  have hsplit :=
    Stacks.AdicCompletionDimension.height_add_ringKrullDim_quotient_eq_ringKrullDim_quotient
      (isUniversallyCatenary_of_isDualizingComplex_univ hK) hJ P P'
  have hadd := AlgebraicGeometry.depth_localized_adicCompletion J P P' (M := N)
  rw [hfibre] at hadd
  exact coe_add_eq_of_add_eq hadd hsplit

/-- **Stacks Project, Tag 0EHW, second display.** Let `A` be a Noetherian ring admitting a
dualizing complex, let `I` be an ideal, let `M` be a finite `A`-module and write `A'` and `M'` for
the `I`-adic completions. Let `𝔭' ⊆ 𝔮'` be primes of `A'` with `𝔮' ∈ V(I A')`, lying over primes
`𝔭 ⊆ 𝔮` of `A`. Then

`depth(M'_{𝔭'}) + dim((A'/𝔭')_{𝔮'}) = depth(M_𝔭) + dim((A/𝔭)_𝔮)`. -/
@[stacks 0EHW "second display"]
public theorem depth_add_ringKrullDim_quotient_localization_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{w} A), Dualizing.IsDualizingComplex K)
    (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : Ideal A) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (p' : Ideal (AdicCompletion I A)) [p'.IsPrime] [p'.LiesOver p]
    (q' : Ideal (AdicCompletion I A)) [q'.IsPrime] [q'.LiesOver q]
    (hIq' : I.map (algebraMap A (AdicCompletion I A)) ≤ q') (hpq' : p' ≤ q') :
    ((Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
            (LocalizedModule p'.primeCompl (AdicCompletion I M)) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (Localization.AtPrime q' ⧸
          p'.map (algebraMap (AdicCompletion I A) (Localization.AtPrime q'))) =
      ((Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
            (LocalizedModule p.primeCompl M) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) := by
  obtain ⟨K, hK⟩ := hdual
  have hpq : p ≤ q := by
    rw [Ideal.over_def p' p, Ideal.over_def q' q]
    exact Ideal.comap_mono hpq'
  have hfibre :=
    Stacks.AdicCompletionFibreUniverse.depth_fibre_localization_eq_height_univ hK I p p'
  have hadd := AlgebraicGeometry.depth_localized_adicCompletion I p p' (M := M)
  rw [hfibre] at hadd
  have hsplit :=
    Stacks.AdicCompletionDimension.height_add_height_quotient_eq_height_quotient_adicCompletion
      (isUniversallyCatenary_of_isDualizingComplex_univ hK) p q p' q' hIq' hpq'
  rw [Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime p' q' hpq',
    Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime p q hpq]
  exact coe_add_eq_of_add_eq hadd (mod_cast hsplit)

/-- **Stacks Project, Tag 0EHW, second display, under the hypotheses its proof uses.** Let `B`
be a Noetherian local ring which is universally catenary and whose local rings have
Cohen--Macaulay formal fibres, let `J` be an ideal contained in the maximal ideal, let `N` be a
finite `B`-module, and write `B'` and `N'` for the `J`-adic completions. For a prime `P'` of
`B'` lying over a prime `P` of `B`,

`depth(N'_{P'}) + dim(B'/P') = depth(N_P) + dim(B/P)`.

The source states this for `B` with a dualizing complex (that is
`Module.depth_add_ringKrullDim_quotient_adicCompletion`) and derives both hypotheses carried
here inside its proof; those are the only two things the proof uses, and they are the hypotheses
the source itself takes for this same translation in Stacks 0EHI and Stacks 0BJV. A dualizing
complex, in any module universe, supplies them through
`Dualizing.isUniversallyCatenary_of_isDualizingComplex_univ` and
`Stacks.AdicCompletionFibre.isPRing_cohenMacaulayRingMapProperty_univ`. -/
@[ega "0 16.4.6" "(iv), special case"]
public theorem depth_add_ringKrullDim_quotient_adicCompletion_of_isUniversallyCatenary
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (hcat : Ring.IsUniversallyCatenary B)
    (hCM : IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u} B)
    (J : Ideal B) (hJ : J ≤ maximalIdeal B)
    (N : Type v) [AddCommGroup N] [Module B N] [Module.Finite B N]
    (P : Ideal B) [P.IsPrime]
    (P' : Ideal (AdicCompletion J B)) [P'.IsPrime] [P'.LiesOver P] :
    ((Module.depth (Localization.AtPrime P') (maximalIdeal (Localization.AtPrime P'))
            (LocalizedModule P'.primeCompl (AdicCompletion J N)) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (AdicCompletion J B ⧸ P') =
      ((Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
            (LocalizedModule P.primeCompl N) : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
  have hfibre :=
    Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height_of_isPRing hCM J P P'
  have hsplit :=
    Stacks.AdicCompletionDimension.height_add_ringKrullDim_quotient_eq_ringKrullDim_quotient
      hcat hJ P P'
  have hadd := AlgebraicGeometry.depth_localized_adicCompletion J P P' (M := N)
  rw [hfibre] at hadd
  exact coe_add_eq_of_add_eq hadd hsplit

/-- **Stacks Project, Tag 0EHW, second display, under the hypotheses its proof uses.** Let `A`
be a Noetherian ring which is universally catenary and whose local rings have Cohen--Macaulay
formal fibres, let `I` be an ideal, let `M` be a finite `A`-module and write `A'` and `M'` for
the `I`-adic completions. Let `𝔭' ⊆ 𝔮'` be primes of `A'` with `𝔮' ∈ V(I A')`, lying over
primes `𝔭 ⊆ 𝔮` of `A`. Then

`depth(M'_{𝔭'}) + dim((A'/𝔭')_{𝔮'}) = depth(M_𝔭) + dim((A/𝔭)_𝔮)`.

The source states this for `A` with a dualizing complex, which is
`Module.depth_add_ringKrullDim_quotient_localization_adicCompletion`; its proof uses the
dualizing complex only through the two hypotheses carried here. -/
public theorem depth_add_ringKrullDim_quotient_localization_adicCompletion_of_isUniversallyCatenary
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hcat : Ring.IsUniversallyCatenary A)
    (hCM : IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u} A)
    (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : Ideal A) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (p' : Ideal (AdicCompletion I A)) [p'.IsPrime] [p'.LiesOver p]
    (q' : Ideal (AdicCompletion I A)) [q'.IsPrime] [q'.LiesOver q]
    (hIq' : I.map (algebraMap A (AdicCompletion I A)) ≤ q') (hpq' : p' ≤ q') :
    ((Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
            (LocalizedModule p'.primeCompl (AdicCompletion I M)) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (Localization.AtPrime q' ⧸
          p'.map (algebraMap (AdicCompletion I A) (Localization.AtPrime q'))) =
      ((Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
            (LocalizedModule p.primeCompl M) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) := by
  have hpq : p ≤ q := by
    rw [Ideal.over_def p' p, Ideal.over_def q' q]
    exact Ideal.comap_mono hpq'
  have hfibre :=
    Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height_of_isPRing hCM I p p'
  have hadd := AlgebraicGeometry.depth_localized_adicCompletion I p p' (M := M)
  rw [hfibre] at hadd
  have hsplit :=
    Stacks.AdicCompletionDimension.height_add_height_quotient_eq_height_quotient_adicCompletion
      hcat p q p' q' hIq' hpq'
  rw [Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime p' q' hpq',
    Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime p q hpq]
  exact coe_add_eq_of_add_eq hadd (mod_cast hsplit)

end Module

end
