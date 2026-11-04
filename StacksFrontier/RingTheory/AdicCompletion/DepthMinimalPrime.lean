module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Support.DepthAdicCompletion
public import StacksFrontier.RingTheory.Depth.Dimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth at a minimal prime of the fibre of an adic completion

Let `R` be a Noetherian ring, `I` an ideal, `M` a finite `R`-module and `q` a prime of `R`.
The additivity formula for depth under completion and localization expresses the depth of
`M ⊗ R^` at a prime `P` of the `I`-adic completion lying over `q` as the depth of `M` at `q`
plus the depth of the local fibre `R^_P / q R^_P`. When `P` is in addition a *minimal* prime
over `q R^`, that fibre term vanishes: minimality makes the fibre ring Artinian, and an
Artinian quotient of a Noetherian local ring has depth zero. Hence depth is simply preserved.

Such a minimal prime always exists above a given prime of `R` when the extension is faithfully
flat, which is the case for the completion of a Noetherian ring along an ideal contained in the
Jacobson radical; the existence statement is recorded here in general form.

## Main results

* `Ideal.exists_mem_minimalPrimes_map_liesOver_of_faithfullyFlat`: over a faithfully flat
  algebra every prime is the contraction of a minimal prime over its extension.
* `Ideal.isArtinianRing_localizationAtPrime_quotient_of_mem_minimalPrimes`: localizing at a
  minimal prime of an ideal makes the quotient by that ideal Artinian.
* `Module.depth_eq_zero_of_isArtinianRing_quotient`: a proper ideal with Artinian quotient has
  depth zero in a Noetherian local ring.
* `Module.depth_localized_adicCompletion_eq_of_mem_minimalPrimes`: depth is preserved by adic
  completion at a minimal prime of the fibre.
-/

@[expose] public section

universe u v

namespace Ideal

/-- Over a faithfully flat algebra `R → S`, every prime `q` of `R` is the contraction of some
prime of `S` that is *minimal* over the extension `q S`. Faithful flatness provides some prime
lying over `q`; shrinking it to a minimal prime of `q S` below it keeps the contraction equal to
`q`, since the contraction is squeezed between `q` and the contraction of the original prime. -/
public theorem exists_mem_minimalPrimes_map_liesOver_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (q : Ideal R) [q.IsPrime] :
    ∃ P : Ideal S, P ∈ (q.map (algebraMap R S)).minimalPrimes ∧ P.LiesOver q := by
  obtain ⟨Q, _, _⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) q
  obtain ⟨P, hminimal, hle⟩ := Ideal.exists_minimalPrimes_le
    (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.ge : q.map (algebraMap R S) ≤ Q)
  exact ⟨P, hminimal, ⟨le_antisymm (Ideal.map_le_iff_le_comap.mp hminimal.1.2)
    ((Ideal.comap_mono hle).trans_eq Ideal.LiesOver.over.symm)⟩⟩

/-- If `P` is a minimal prime over an ideal `J` of a Noetherian ring `R`, then the extension of
`J` to the localization `R_P` is `P`-primary in the strong sense that the quotient is an
Artinian ring. Indeed localization identifies the minimal primes over `J R_P` with those
minimal primes over `J` contained in `P`, so the maximal ideal of `R_P` is minimal over
`J R_P`, and Krull's height theorem gives Artinian-ness of the quotient. -/
public theorem isArtinianRing_localizationAtPrime_quotient_of_mem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] (J P : Ideal R) [P.IsPrime]
    (hP : P ∈ J.minimalPrimes) :
    IsArtinianRing ((Localization.AtPrime P) ⧸
      J.map (algebraMap R (Localization.AtPrime P))) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rw [IsLocalization.minimalPrimes_map P.primeCompl]
  show (IsLocalRing.maximalIdeal (Localization.AtPrime P)).under R ∈ J.minimalPrimes
  rwa [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P]

end Ideal

namespace Module

/-- In a Noetherian local ring `R`, a proper ideal `J` whose quotient `R ⧸ J` is Artinian has
depth zero along the maximal ideal. The quotient is a nonzero finite module, so Nakayama's
lemma shows that the maximal ideal does not act by the whole of it and the bound
`depth ≤ dim Supp` applies; the support of `R ⧸ J` is `Spec (R ⧸ J)`, which is zero-dimensional
because `R ⧸ J` is Artinian. -/
@[ega "0 16.4.6" "(iii), special case"]
public theorem depth_eq_zero_of_isArtinianRing_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (J : Ideal R) (hJ : J ≠ ⊤) [IsArtinianRing (R ⧸ J)] :
    Module.depth R (IsLocalRing.maximalIdeal R) (R ⧸ J) = 0 := by
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have hnotTop : IsLocalRing.maximalIdeal R • (⊤ : Submodule R (R ⧸ J)) ≠ ⊤ := fun heq =>
    (top_ne_bot : (⊤ : Submodule R (R ⧸ J)) ≠ ⊥)
      (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
        Module.Finite.fg_top (by rw [heq])
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]))
  have hdimension : ringKrullDim (R ⧸ J) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hdepth := Module.depth_le_supportDim R (IsLocalRing.maximalIdeal R) (R ⧸ J) hnotTop
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient,
    hdimension] at hdepth
  exact le_zero_iff.mp (WithBot.coe_le_coe.mp hdepth)

/-- **Depth is preserved by adic completion at a minimal prime of the fibre.** Let `R` be
Noetherian, `I` an ideal, `M` a finite `R`-module, `q` a prime of `R` and `P` a prime of the
`I`-adic completion `R^` lying over `q` and minimal over the extension `q R^`. Then the depth of
the localization of `AdicCompletion I M` at `P` agrees with the depth of the localization of `M`
at `q`. The additivity formula contributes the depth of the local fibre `R^_P / q R^_P`, and
minimality of `P` makes that fibre Artinian, hence of depth zero. -/
public theorem depth_localized_adicCompletion_eq_of_mem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : Ideal R) [q.IsPrime] (P : Ideal (AdicCompletion I R)) [P.IsPrime] [P.LiesOver q]
    (hP : P ∈ (q.map (algebraMap R (AdicCompletion I R))).minimalPrimes) :
    Module.depth (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl (AdicCompletion I M)) =
      Module.depth (Localization.AtPrime q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl M) := by
  let fibreIdeal := (q.map (algebraMap R (AdicCompletion I R))).map
    (algebraMap (AdicCompletion I R) (Localization.AtPrime P))
  have hfibre : fibreIdeal = q.map (algebraMap R (Localization.AtPrime P)) := by
    dsimp only [fibreIdeal]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have := Ideal.isArtinianRing_localizationAtPrime_quotient_of_mem_minimalPrimes
    (q.map (algebraMap R (AdicCompletion I R))) P hP
  have hproper : fibreIdeal ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top
      ((Ideal.map_mono hP.le).trans_eq Localization.AtPrime.map_eq_maximalIdeal)
  have hzero := Module.depth_eq_zero_of_isArtinianRing_quotient fibreIdeal hproper
  rw [hfibre] at hzero
  rw [AlgebraicGeometry.depth_localized_adicCompletion I q P, hzero, add_zero]

end Module

end
