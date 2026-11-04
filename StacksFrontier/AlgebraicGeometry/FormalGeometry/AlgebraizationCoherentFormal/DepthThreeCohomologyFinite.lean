module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceLocalDimension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentComplementAffine
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.TildeStalkPrime
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.RingTheory.DimensionFormulaMinimalPrimes
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCriterion
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessDepthDimension
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite cohomology on `U` from a depth bound against the distance to `Z`

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and let `δ^Y_Z` be the distance of a point of `Y` from
`Z`. Assume `A` has a dualizing complex. Let `𝒢` be a coherent `𝒪_U`-module supported on
`U ∩ Y` (its stalks off `U ∩ Y` have infinite depth) with `depth(𝒢_y) + δ^Y_Z(y) ≥ 3` at every
`y ∈ U ∩ Y`. Then `H⁰(U, 𝒢)` and `H¹(U, 𝒢)` are finite `A`-modules.

This is the finiteness step of the proof of [Stacks, Tag 0EJG], which the source draws from
[Stacks, Tag 0BJY] and the elementary properties of `δ^Y_Z` of [Stacks, Tag 0EIY].

## Main results

* `Stacks.Algebraization.distanceToZ_le_height_map_quotientMk`: for primes `𝔭 ⊆ 𝔮` of `A` with
  `𝔭 ∈ Y` and `𝔮 ∈ Z`, the distance `δ^Y_Z(𝔭)` is at most `dim((A/𝔭)_𝔮)`.
* `Stacks.Algebraization.finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ`:
  the finiteness of `H⁰(U, 𝒢)` and `H¹(U, 𝒢)`.

## Implementation notes

The source invokes [Stacks, Tag 0BJY], whose hypotheses on `X` (universal catenarity and Serre's
condition on the formal fibres) a dualizing complex supplies. Here the same finiteness is
obtained more directly over the affine base: by [Stacks, Tag 0BK0] the coherent module `𝒢` is
`M̃|_U` for a finite `A`-module `M`, and `H^p(U, 𝒢)` is finite exactly when `H^{p+1}_Z(M)` is;
Faltings' criterion [Stacks, Tag 0EFD], which is stated for a ring with a dualizing complex,
turns the finiteness of `H^i_Z(M)` for `i ≤ 2` into the inequalities
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > 2` for `𝔭 ∉ Z`, `𝔮 ∈ Z`, `𝔭 ⊆ 𝔮`, which are the inequalities of
[Stacks, Tag 0BJY] (a) at `n = 2`.

These are checked pointwise at `𝔭 ∈ U`, where the depth of `M_𝔭` is that of the stalk `𝒢_𝔭`.
If `𝔭 ∉ Y` that depth is `∞`. Otherwise
`δ^Y_Z(𝔭) ≤ dim((A/𝔭)_𝔮)` by [Stacks, Tag 0EIY]
(`Stacks.Algebraization.distanceFunction_le_closureLocalDimension`), applied in `Y` at the point
`𝔮 ∈ Z ∩ closure{𝔭}`; so the depth bound gives `> 2`.

`H^p(U, -)` is `Stacks.LocalCohomology.complementSheafCohomology`, the right derived functor of
global sections on the open subscheme `U` read as an `A`-module; the open `U` of the situation
is, by definition, the open `Stacks.LocalCohomology.complementZeroLocus A 𝔞` on which that
functor is defined.

A point of `U ∩ Y` is a point `y` of `U` together with a point `z` of `Y` with the same image in
`X`, as in `Stacks.Algebraization.SatisfiesDepthInequalities`.

## References

* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace IsLocalRing
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### The distance to `Z` against the dimension of a localized quotient -/

/-- In a prime spectrum, specialization is inclusion of primes. -/
private theorem specializes_iff_asIdeal_le {R : Type u} [CommRing R] (x y : PrimeSpectrum R) :
    x ⤳ y ↔ x.asIdeal ≤ y.asIdeal :=
  (PrimeSpectrum.le_iff_specializes x y).symm

/-- Contracting along `A ⟶ A ⧸ I` reflects the inclusion of primes. -/
private theorem comap_quotientMk_asIdeal_le_iff {A : Type u} [CommRing A] (I : Ideal A)
    (x y : PrimeSpectrum (A ⧸ I)) :
    (PrimeSpectrum.comap (Ideal.Quotient.mk I) x).asIdeal ≤
        (PrimeSpectrum.comap (Ideal.Quotient.mk I) y).asIdeal ↔ x.asIdeal ≤ y.asIdeal := by
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
  refine ⟨fun h => ?_, fun h => Ideal.comap_mono h⟩
  have h' := Ideal.map_mono (f := Ideal.Quotient.mk I) h
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h'

/-- In `Spec(A ⧸ I)`, the scheme order on the closure of a point `a` is the reverse of the
inclusion order of primes, so contracting to `A` and reading the result in the zero locus of the
contraction of `a` is strictly antitone. The coheight of a point `b` of the closure of `a` is
therefore at most the height of the image of the contraction of `b` in `A ⧸ a`. -/
private theorem coheight_closure_le_height_map_quotientMk {A : Type u} [CommRing A] (I : Ideal A)
    (a b : Spec (.of (A ⧸ I))) (hb : b ∈ closure ({a} : Set (Spec (.of (A ⧸ I))))) :
    Order.coheight (⟨b, hb⟩ : (closure ({a} : Set (Spec (.of (A ⧸ I)))) :
        Set (Spec (.of (A ⧸ I))))) ≤
      ((PrimeSpectrum.comap (Ideal.Quotient.mk I) b).asIdeal.map
        (Ideal.Quotient.mk (PrimeSpectrum.comap (Ideal.Quotient.mk I) a).asIdeal)).height := by
  set C : Set (Spec (.of (A ⧸ I))) := closure {a}
  set pa := PrimeSpectrum.comap (Ideal.Quotient.mk I) a
  have hmem : ∀ c : C, pa.asIdeal ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk I) c.1).asIdeal :=
    fun c => (comap_quotientMk_asIdeal_le_iff I a c.1).mpr
      ((specializes_iff_asIdeal_le a c.1).mp (specializes_iff_mem_closure.mpr c.2))
  let f : Cᵒᵈ → (PrimeSpectrum.zeroLocus (pa.asIdeal : Set A)) := fun c =>
    ⟨PrimeSpectrum.comap (Ideal.Quotient.mk I) (OrderDual.ofDual c).1, by
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
      exact hmem (OrderDual.ofDual c)⟩
  have hf : StrictMono f := by
    intro c d hcd
    have hlt : (OrderDual.ofDual d).1 < (OrderDual.ofDual c).1 := hcd
    rw [lt_iff_le_not_ge] at hlt
    have h2 : ¬ (OrderDual.ofDual d).1 ⤳ (OrderDual.ofDual c).1 := fun h =>
      hlt.2 (AlgebraicGeometry.Scheme.le_iff_specializes.mpr h)
    have hle := (comap_quotientMk_asIdeal_le_iff I _ _).mpr
      ((specializes_iff_asIdeal_le _ _).mp (Scheme.le_iff_specializes.mp hlt.1))
    have hnle : ¬ (PrimeSpectrum.comap (Ideal.Quotient.mk I) (OrderDual.ofDual d).1).asIdeal ≤
        (PrimeSpectrum.comap (Ideal.Quotient.mk I) (OrderDual.ofDual c).1).asIdeal := fun h =>
      h2 ((specializes_iff_asIdeal_le _ _).mpr ((comap_quotientMk_asIdeal_le_iff I _ _).mp h))
    exact lt_iff_le_not_ge.mpr ⟨hle, hnle⟩
  rw [Ideal.height_map_quotientMk_eq_orderHeight _ _ (hmem ⟨b, hb⟩), ← Order.height_toDual]
  exact Order.height_le_height_apply_of_strictMono f hf (OrderDual.toDual ⟨b, hb⟩)

/-- **The distance to `Z` is at most a local dimension of `Y`.** For a point `z` of `Y` with
image the prime `𝔭` of `A`, and a prime `𝔮 ⊇ 𝔭` of `A` lying in `Z = V(𝔞)`, one has
`δ^Y_Z(z) ≤ dim((A/𝔭)_𝔮)`, the latter written as the height of the image of `𝔮` in `A ⧸ 𝔭`.
This is [Stacks, Tag 0EIY] at the point of `Y` defined by `𝔮`. -/
public theorem distanceToZ_le_height_map_quotientMk (S : AlgebraizationSituation.{u}) (z : S.Y)
    (p q : PrimeSpectrum S.A) (hzp : PrimeSpectrum.comap (Ideal.Quotient.mk S.I) z = p)
    (hpq : p.asIdeal ≤ q.asIdeal) (hq : S.a ≤ q.asIdeal) :
    S.distanceToZ z ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  have hIq : S.I ≤ q.asIdeal := S.I_le_a.trans hq
  have hqbar : (q.asIdeal.map (Ideal.Quotient.mk S.I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hIq
  let z' : PrimeSpectrum (S.A ⧸ S.I) := ⟨q.asIdeal.map (Ideal.Quotient.mk S.I), hqbar⟩
  have hz' : PrimeSpectrum.comap (Ideal.Quotient.mk S.I) z' = q :=
    PrimeSpectrum.ext (Ideal.comap_map_mk hIq)
  have hzz' : z.asIdeal ≤ z'.asIdeal :=
    (comap_quotientMk_asIdeal_le_iff S.I z z').mp (by rwa [hzp, hz'])
  have hclos : (z' : S.Y) ∈ closure ({z} : Set S.Y) :=
    specializes_iff_mem_closure.mp ((specializes_iff_asIdeal_le z z').mpr hzz')
  have hZ : (z' : S.Y) ∈ (S.closedSubsetZ : Set S.Y) := by
    show ((S.a.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) : Set (S.A ⧸ S.I)) ⊆
      (z'.asIdeal : Set (S.A ⧸ S.I))
    exact Ideal.map_mono hq
  have hbound := distanceFunction_le_closureLocalDimension S.Y S.closedSubsetZ z z' hclos hZ
  have hcoh := coheight_closure_le_height_map_quotientMk S.I z z' hclos
  rw [hzp, hz'] at hcoh
  exact WithBot.coe_le_coe.mp (hbound.trans (WithBot.coe_le_coe.mpr hcoh))

/-! ### Finiteness of `H⁰(U, 𝒢)` and `H¹(U, 𝒢)` -/

/-- Under the hypotheses of
`Stacks.Algebraization.finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ`, for
every finite `A`-module `M` with `𝒢 ≅ M̃|_U` the local cohomology `H^i_Z(M)` is finite for
`i ≤ 2`, by Faltings' criterion. -/
@[sga "2 VIII 2.3" "(i) ⇒ (iii)"]
private theorem finite_localCohomologyModule_of_three_le_depth_add_distanceToZ
    (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (G : S.U.toScheme.Modules) [G.IsCoherent]
    (htop : ∀ y : S.U.toScheme, (∀ z : S.Y, S.U.ι.base y ≠ S.Yι.base z) →
      Module.depth (S.U.toScheme.presheaf.stalk y)
        (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) = ⊤)
    (hdepth : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      (3 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk y)
          (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) +
        S.distanceToZ z)
    (M : ModuleCat.{u} S.A) [Module.Finite S.A M]
    (e : (show (complementZeroLocus S.A S.a : Scheme).Modules from G) ≅
      complementTilde S.A S.a M)
    (i : ℕ) (hi : i ≤ 2) :
    Module.Finite S.A (localCohomologyModule S.A S.a (Ideal.fg_of_isNoetherianRing S.a) M i) := by
  obtain ⟨K, hK⟩ := hdual
  have hI : S.a.FG := Ideal.fg_of_isNoetherianRing S.a
  let M' : ModuleCat.{u} (CommRingCat.of S.A) := M
  -- the depth-dimension inequalities of Faltings' criterion at `s = 2`
  have hcond : ∀ p q : PrimeSpectrum S.A, p ∉ PrimeSpectrum.zeroLocus (S.a : Set S.A) →
      q ∈ PrimeSpectrum.zeroLocus (S.a : Set S.A) → p.asIdeal ≤ q.asIdeal →
      enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))) >
        (((2 : ℕ) : ℤ) : EInt) := by
    intro p q hp hq hpq
    rw [ringKrullDim_localization_quotient_eq_height p q hpq]
    refine (natCast_lt_add_iff_eint 2 _ _).mp ?_
    rw [mem_zeroLocus_iff] at hp hq
    let y : S.U.toScheme := ⟨(p : S.X), hp⟩
    have hdeq : Module.depth (S.U.toScheme.presheaf.stalk y)
        (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) =
        Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) := by
      let e'' : G ≅ (tilde M').restrict S.U.ι := e
      rw [Scheme.Modules.depth_stalk_congr e'' y]
      exact (Scheme.Modules.depth_stalk_restrict S.U.ι (tilde M') y).trans
        (depth_stalk_tilde_eq_depth_localizedModule (R := CommRingCat.of S.A) M'
          (p : S.X) p rfl)
    by_cases hY : ∃ z : S.Y, S.U.ι.base y = S.Yι.base z
    · obtain ⟨z, hyz⟩ := hY
      have hzp : PrimeSpectrum.comap (Ideal.Quotient.mk S.I) z = p := hyz.symm
      have hdist := distanceToZ_le_height_map_quotientMk S z p q hzp hpq hq
      have hd := hdepth y z hyz
      rw [hdeq] at hd
      exact lt_of_lt_of_le (by norm_num) (hd.trans (add_le_add le_rfl hdist))
    · have htop' := htop y fun z hz => hY ⟨z, hz⟩
      rw [hdeq] at htop'
      rw [htop', top_add]
      exact ENat.coe_lt_top 2
  have hfin := (finite_localCohomologyWithSupportIn_iff_depth_add_dim S.A
    (PrimeSpectrum.zeroLocus (S.a : Set S.A))
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization 2 M K hK).mpr hcond
  have := hfin (i : ℤ) (by omega)
  exact Module.Finite.equiv
    (localCohomologyWithSupportInIsoLocalCohomologyModule S.A S.a hI M (i : ℤ)).toLinearEquiv

/-- Under the depth hypotheses, `H^p(U, 𝒢)` for `p ≤ 1` and `Γ(U, 𝒢)` are finite `A`-modules. -/
private theorem finite_cohomology_and_sections_of_three_le_depth_add_distanceToZ
    (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (G : S.U.toScheme.Modules) [G.IsCoherent]
    (htop : ∀ y : S.U.toScheme, (∀ z : S.Y, S.U.ι.base y ≠ S.Yι.base z) →
      Module.depth (S.U.toScheme.presheaf.stalk y)
        (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) = ⊤)
    (hdepth : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      (3 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk y)
          (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) +
        S.distanceToZ z) :
    (∀ p : ℕ, p ≤ 1 → Module.Finite S.A ((complementSheafCohomology S.A S.a p).obj G)) ∧
      Module.Finite S.A (complementGlobalSections S.A S.a
        (show (complementZeroLocus S.A S.a : Scheme).Modules from G)) := by
  have hI : S.a.FG := Ideal.fg_of_isNoetherianRing S.a
  let G' : (complementZeroLocus S.A S.a : Scheme).Modules := G
  have : G'.IsCoherent := ‹G.IsCoherent›
  obtain ⟨⟨M, hM, ⟨e⟩⟩, hrest⟩ := coherent_complement_affine S.A S.a hI G'
  have := hM
  have hlc := finite_localCohomologyModule_of_three_le_depth_add_distanceToZ S hdual G htop
    hdepth M e
  exact ⟨fun p hp => ((hrest M hM e).2.1 p).out 2 3 |>.mpr (hlc (p + 1) (by omega)),
    ((hrest M hM e).2.2 (hlc 1 (by omega))).1⟩

/-- **Finite cohomology on `U` from the depth bound.** Let `A` have a dualizing complex and let
`𝒢` be a coherent `𝒪_U`-module whose stalks have infinite depth (that is, vanish) off `U ∩ Y`
and with
`depth(𝒢_y) + δ^Y_Z(y) ≥ 3` at every point `y` of `U ∩ Y`. Then `H^p(U, 𝒢)` is a finite
`A`-module for `p = 0, 1`. -/
public theorem finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ
    (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (G : S.U.toScheme.Modules) [G.IsCoherent]
    (htop : ∀ y : S.U.toScheme, (∀ z : S.Y, S.U.ι.base y ≠ S.Yι.base z) →
      Module.depth (S.U.toScheme.presheaf.stalk y)
        (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) = ⊤)
    (hdepth : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      (3 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk y)
          (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) +
        S.distanceToZ z)
    (p : ℕ) (hp : p ≤ 1) :
    Module.Finite S.A ((complementSheafCohomology S.A S.a p).obj G) :=
  (finite_cohomology_and_sections_of_three_le_depth_add_distanceToZ S hdual G htop hdepth).1 p hp

/-- **Finite sections on `U` from the depth bound.** Under the hypotheses of
`Stacks.Algebraization.finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ`, the
module `Γ(U, 𝒢)` of sections over `U`, read over `A`, is finite. -/
public theorem finite_complementGlobalSections_of_three_le_depth_add_distanceToZ
    (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (G : S.U.toScheme.Modules) [G.IsCoherent]
    (htop : ∀ y : S.U.toScheme, (∀ z : S.Y, S.U.ι.base y ≠ S.Yι.base z) →
      Module.depth (S.U.toScheme.presheaf.stalk y)
        (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) = ⊤)
    (hdepth : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      (3 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk y)
          (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) +
        S.distanceToZ z) :
    Module.Finite S.A (complementGlobalSections S.A S.a
      (show (complementZeroLocus S.A S.a : Scheme).Modules from G)) :=
  (finite_cohomology_and_sections_of_three_le_depth_add_distanceToZ S hdual G htop hdepth).2

end Stacks.Algebraization

end
