module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonalRigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveRigEtaleDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFormalSpectrumRepresentable
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientAdic

/-!
# Rig-surjective closed immersions: the chart conditions discharged

Let `f : X ⟶ Y` be a closed immersion of locally Noetherian formal algebraic spaces over `S`.
**Stacks 0GD5** says that `f` is rig-surjective exactly when on every affine chart `V ⟶ Y`
which is representable by algebraic spaces and étale, the base change `X ×_Y V ⟶ V` is given by
a surjection `B → A` of `WAdm^{Noeth}` whose kernel `J` has `I J ^ n = 0` for an ideal of
definition `I` of `B` and some `n ≥ 1`. The conditions themselves are defined in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersion`; this file proves
everything the source's proof uses about them.

## Main results

* `Rig.exists_mul_pow_eq_bot_of_leKerAtDvrPointsBelow` and
  `Rig.leKerAtDvrPoints_iff_leKerAtDvrPointsBelow`: the algebraic criterion of Stacks 0GD5,
  tested only at the discrete valuation points no larger than the ring, which is what a big
  fppf site can see.
* `AlgebraicGeometry.FormalSpace.leKerAtDvrPoints_ker_of_isRigSurjective` and
  `AlgebraicGeometry.FormalSpace.isRigSurjective_formalSpectrumMap_of_leKerAtDvrPoints`:
  **Stacks 0AR0** for `Spf` of a closed immersion of adic rings, read through Stacks 0AN0.
* `AlgebraicGeometry.FormalSpace.hasRigSurjectiveOnPullbackCharts_of_isRigSurjective`:
  **Stacks 0AQS** in chart form.
* `AlgebraicGeometry.FormalSpace.hasSurjectiveOnPullbackCharts_of_isClosedImmersion`: the
  surjectivity clause of **Stacks 0AQI** on the charts of a closed immersion.
* `AlgebraicGeometry.FormalSpace.hasAnnihilatedKerPow_iff_hasRigSurjective_of_isClosedImmersion`:
  for a closed immersion, condition (2) of Stacks 0GD5 holds exactly when every chart map is
  rig-surjective.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isClosedImmersion`: a closed immersion
  is locally of finite type.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_pullback_snd_of_hasRigSurjectiveOnPullbackCharts`:
  every Noetherian representable étale chart of the target carries a presentation of the kind
  the chart conditions quantify over, so those conditions reach it.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0AQT](https://stacks.math.columbia.edu/tag/0AQT)
* [Stacks Project, Tag 0AQV](https://stacks.math.columbia.edu/tag/0AQV)
* [Stacks Project, Tag 0AR0](https://stacks.math.columbia.edu/tag/0AR0)
* [Stacks Project, Tag 0GD5](https://stacks.math.columbia.edu/tag/0GD5)
* [Stacks Project, Tag 0GHX](https://stacks.math.columbia.edu/tag/0GHX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Cardinal

universe u

namespace Rig

/-- The condition of `Rig.LeKerAtDvrPoints` asked only of the discrete valuation rings smaller
than a cardinal `kappa`.

This is the form the condition takes over a big fppf site: a discrete valuation point of `A`
is visible to the site only once the site holds the quotient spectra of the point's ring, which
bounds that ring by the size cutoff. For a Noetherian ring `A` whose topology is adic and which
is itself smaller than `kappa` the restriction costs nothing — the two conditions are then
equivalent, by `Rig.leKerAtDvrPoints_iff_leKerAtDvrPointsBelow` — because the discrete valuation
ring that the proof of `Rig.exists_mul_pow_eq_bot_of_leKerAtDvrPointsBelow` builds out of a
prime of `A` is a subring of a fraction field of a localization of a quotient of `A`, hence no
larger than `A`. -/
def LeKerAtDvrPointsBelow {A : Type u} [CommRing A] [TopologicalSpace A]
    (kappa : Cardinal.{u}) (J : Ideal A) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (φ : A →+* R),
    #R < kappa →
    (∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
        Ideal.map φ I ≠ ⊥ ∧ Ideal.map φ I ≤ IsLocalRing.maximalIdeal R) →
      J ≤ RingHom.ker φ

/-- Being killed at every discrete valuation point is being killed at the small ones. -/
theorem leKerAtDvrPointsBelow_of_leKerAtDvrPoints {A : Type u} [CommRing A] [TopologicalSpace A]
    {kappa : Cardinal.{u}} {J : Ideal A} (h : LeKerAtDvrPoints J) :
    LeKerAtDvrPointsBelow kappa J :=
  fun R _ _ _ φ _ hadic => h R φ hadic

/-- A Noetherian local domain which is not a field is dominated by a discrete valuation ring
inside its fraction field. This is **Stacks 00PH** for the identity extension of the fraction
field, with domination recorded as sending the maximal ideal into the maximal ideal.

The dominating ring is a subring of the fraction field of `T`, which is a localization of `T`,
so it is no larger than `T`. That bound is what lets the criterion of
`Rig.exists_mul_pow_eq_bot_of_leKerAtDvrPointsBelow` be applied at this point. -/
private theorem exists_dvr_of_isLocalDomain' (T : Type u) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsLocalRing T] (hT : ¬ IsField T) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (ψ : T →+* R), Function.Injective ψ ∧
        (∀ y ∈ IsLocalRing.maximalIdeal T, ψ y ∈ IsLocalRing.maximalIdeal R) ∧
        #R ≤ #T := by
  obtain ⟨R, hRdvr, -, hRloc⟩ :=
    Stacks.DiscreteValuationRing.Existence.solution (R := T) (FractionRing T)
      (L := FractionRing T) hT
  have hinj : Function.Injective (algebraMap T R) := fun a b hab => by
    apply FaithfulSMul.algebraMap_injective T (FractionRing T)
    rw [IsScalarTower.algebraMap_apply T R (FractionRing T),
      IsScalarTower.algebraMap_apply T R (FractionRing T), hab]
  have hcard : #(↥R) ≤ #T :=
    (Cardinal.mk_le_of_injective (f := fun x : ↥R => (x : FractionRing T))
      Subtype.val_injective).trans
      (IsLocalization.cardinalMk_le (R := T) (L := FractionRing T) (nonZeroDivisors T))
  refine ⟨R, inferInstance, inferInstance, hRdvr, algebraMap T R, hinj, fun y hy => ?_, hcard⟩
  rw [IsLocalRing.mem_maximalIdeal] at hy ⊢
  exact fun hu => hy (hRloc.map_nonunit _ hu)

/-- A Noetherian domain with a nonzero prime `q` admits an injective homomorphism into a
discrete valuation ring taking `q` into the maximal ideal: localize at `q`, which is a
Noetherian local domain and not a field, and dominate it by Stacks 00PH. Both steps are
localizations and a passage to a subring, so the discrete valuation ring is no larger than
`D`. -/
private theorem exists_dvr_of_isPrime_ne_bot' (D : Type u) [CommRing D] [IsDomain D]
    [IsNoetherianRing D] (q : Ideal D) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (ψ : D →+* R), Function.Injective ψ ∧
        (∀ y ∈ q, ψ y ∈ IsLocalRing.maximalIdeal R) ∧ #R ≤ #D := by
  have hinj : Function.Injective (algebraMap D (Localization.AtPrime q)) :=
    IsLocalization.injective (Localization.AtPrime q)
      (Ideal.primeCompl_le_nonZeroDivisors q)
  have _ : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := q.primeCompl)
      (S := Localization.AtPrime q) (Ideal.primeCompl_le_nonZeroDivisors q)
  have hmem : ∀ y ∈ q, algebraMap D (Localization.AtPrime q) y ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := fun y hy =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q y).mpr hy
  have hnotField : ¬ IsField (Localization.AtPrime q) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro hbot
    obtain ⟨y, hyq, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
    refine hy0 (hinj ?_)
    have hy := hmem y hyq
    rw [hbot, Ideal.mem_bot] at hy
    simpa using hy
  obtain ⟨R, _, _, hRdvr, ψ, hψinj, hψloc, hψcard⟩ :=
    exists_dvr_of_isLocalDomain' (Localization.AtPrime q) hnotField
  exact ⟨R, inferInstance, inferInstance, hRdvr,
    ψ.comp (algebraMap D (Localization.AtPrime q)), hψinj.comp hinj,
    fun y hy => hψloc _ (hmem y hy),
    hψcard.trans (IsLocalization.cardinalMk_le (R := D) (L := Localization.AtPrime q)
      q.primeCompl)⟩

/-- A prime `p` of a Noetherian adic ring not containing an ideal of definition `I₀` is
dominated by an adic discrete valuation point: there is a discrete valuation ring `R` and a
homomorphism `A → R` whose kernel is inside `p` and which carries every ideal of definition
into the maximal ideal of `R`. The ring `R` is obtained from a quotient of `A` by a
localization and a passage to a subring of a fraction field, so it is no larger than `A`. -/
private theorem exists_dvr_ker_le_of_isPrime' {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsNoetherianRing A] {I₀ : Ideal A}
    (hI₀ : TopologicalRing.IsIdealOfDefinition I₀) [IsAdicComplete I₀ A]
    {p : Ideal A} (hp : p.IsPrime) (hpI : ¬ I₀ ≤ p) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : A →+* R), RingHom.ker φ ≤ p ∧
        (∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
          Ideal.map φ I ≤ IsLocalRing.maximalIdeal R) ∧ #R ≤ #A := by
  classical
  have hjac : I₀ ≤ Ideal.jacobson (⊥ : Ideal A) := IsAdicComplete.le_jacobson_bot I₀
  have hne : p ⊔ I₀ ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ p ⊔ I₀ := htop ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨x, hx, a, ha, hxa⟩ := h1
    have hu : IsUnit x := by
      have h2 := Ideal.mem_jacobson_bot.mp (hjac ha) (-1)
      rwa [show a * (-1) + 1 = x by linear_combination -hxa] at h2
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx hu)
  obtain ⟨m, hm, hmle⟩ := Ideal.exists_le_maximal _ hne
  have hIm : I₀ ≤ m := le_sup_right.trans hmle
  have _ : p.IsPrime := hp
  have _ : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  have _ : (m.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by simpa [Ideal.mk_ker] using le_sup_left.trans hmle)
  obtain ⟨x₀, hx₀I, hx₀p⟩ := SetLike.not_le_iff_exists.mp hpI
  have hqne : m.map (Ideal.Quotient.mk p) ≠ ⊥ := by
    intro hbot
    refine hx₀p (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    have hx₀ := Ideal.mem_map_of_mem (Ideal.Quotient.mk p) (hIm hx₀I)
    rwa [hbot, Ideal.mem_bot] at hx₀
  obtain ⟨R, _, _, hRdvr, ψ, hψinj, hψq, hψcard⟩ :=
    exists_dvr_of_isPrime_ne_bot' (A ⧸ p) (m.map (Ideal.Quotient.mk p)) hqne
  refine ⟨R, inferInstance, inferInstance, hRdvr, ψ.comp (Ideal.Quotient.mk p), ?_, ?_,
    hψcard.trans Cardinal.mk_quotient_le⟩
  · intro z hz
    rw [RingHom.mem_ker] at hz
    simp only [RingHom.coe_comp, Function.comp_apply] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hψinj (by simpa using hz))
  · -- a power of an ideal of definition `I` lies in `I₀ ≤ m`, and `m` is prime
    intro I hI
    obtain ⟨n, hn⟩ := hI.2 (I₀ : Set A) (hI₀.1.mem_nhds I₀.zero_mem)
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    exact Ideal.mem_comap.mpr (hψq _ (Ideal.mem_map_of_mem _ (hm.isPrime.mem_of_pow_mem (n + 1)
      (hIm (hn (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hz (n + 1))))))))

/-- An ideal `J` of a Noetherian adic ring which is killed at every discrete valuation point
*smaller than a cardinal above `#A`* has a positive power annihilated by an ideal of definition:
otherwise `I₀ * J` is a finitely generated non-nilpotent ideal for an ideal of definition `I₀`
defining the topology, so some prime `p` contains neither `I₀` nor `J`, and the discrete
valuation point dominating `p` kills `I₀` on no ideal of definition yet fails to kill `J`.

Only small discrete valuation rings are needed because the one the argument produces is built
from `A` by a quotient, a localization and a passage to a subring of a fraction field, none of
which increases cardinality, so it satisfies `#R ≤ #A`. -/
theorem exists_mul_pow_eq_bot_of_leKerAtDvrPointsBelow {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) {kappa : Cardinal.{u}} (hAcard : #A < kappa)
    {J : Ideal A} (h : LeKerAtDvrPointsBelow kappa J) :
    ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
      ∃ n : ℕ, n ≠ 0 ∧ I * J ^ n = ⊥ := by
  obtain ⟨I₀, hI₀def, hI₀adic, hI₀complete⟩ :=
    AlgebraicGeometry.FormalSpace.exists_idealOfDefinition_isAdicComplete hA
  have _ : IsAdicComplete I₀ A := hI₀complete
  have hnil : IsNilpotent (I₀ * J) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (Ideal.fg_of_isNoetherianRing _),
      nilradical_eq_sInf]
    refine le_sInf fun P hP => ?_
    have hPp : P.IsPrime := hP
    rw [Ideal.IsPrime.mul_le hPp]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hI₀P, hJP⟩ := hcon
    obtain ⟨R, _, _, _, φ, hker, hmax, hRcard⟩ :=
      exists_dvr_ker_le_of_isPrime' hI₀def hPp hI₀P
    refine hJP ((h R φ (hRcard.trans_lt hAcard) fun I hI => ⟨?_, hmax I hI⟩).trans hker)
    rw [Ne, Ideal.map_eq_bot_iff_le_ker]
    intro hIker
    obtain ⟨j, hj⟩ := hI₀def.2 (I : Set A) (hI.1.mem_nhds I.zero_mem)
    refine hI₀P ((Ideal.IsPrime.pow_le_iff (I := I₀) (P := P) (Nat.succ_ne_zero j)).mp ?_)
    exact (Ideal.pow_le_pow_right (Nat.le_succ j)).trans (le_trans hj (hIker.trans hker))
  obtain ⟨k, hk⟩ := hnil
  have hk1 : (I₀ * J) ^ (k + 1) = ⊥ := by
    have hle := Ideal.pow_le_pow_right (I := I₀ * J) (Nat.le_succ k)
    rw [hk] at hle
    simpa using le_bot_iff.mp hle
  rw [mul_pow] at hk1
  exact ⟨I₀ ^ (k + 1), AlgebraicGeometry.FormalSpace.isIdealOfDefinition_pow_succ hI₀adic k,
    k + 1, Nat.succ_ne_zero k, hk1⟩

/-- **For a Noetherian adic ring the cardinality restriction costs nothing.** If `A` is
Noetherian with an adic topology and smaller than `kappa`, then an ideal killed at every
discrete valuation point of `A` below `kappa` is killed at every discrete valuation point
whatsoever: the small points already force an ideal of definition to annihilate a power of `J`,
and that in turn kills `J` at every point. -/
theorem leKerAtDvrPoints_of_leKerAtDvrPointsBelow {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) {kappa : Cardinal.{u}} (hAcard : #A < kappa)
    {J : Ideal A} (h : LeKerAtDvrPointsBelow kappa J) : LeKerAtDvrPoints J := by
  obtain ⟨I, hI, n, hn, hmul⟩ := exists_mul_pow_eq_bot_of_leKerAtDvrPointsBelow hA hAcard h
  exact leKerAtDvrPoints_of_mul_pow_eq_bot hI hn hmul

/-- For a Noetherian adic ring smaller than `kappa`, being killed at every discrete valuation
point and being killed at the ones below `kappa` are the same condition. Over a big fppf site
this is what makes the right-hand side of Stacks 0AR0 insensitive to the size cutoff: only the
discrete valuation points the site can carry need be tested. -/
theorem leKerAtDvrPoints_iff_leKerAtDvrPointsBelow {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) {kappa : Cardinal.{u}} (hAcard : #A < kappa)
    {J : Ideal A} : LeKerAtDvrPoints J ↔ LeKerAtDvrPointsBelow kappa J :=
  ⟨leKerAtDvrPointsBelow_of_leKerAtDvrPoints,
    leKerAtDvrPoints_of_leKerAtDvrPointsBelow hA hAcard⟩

end Rig

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A ring with an adic topology carrying a quotient system over `S` is smaller than the size
cutoff of the site.** An adic ring is complete for one of its ideals of definition
(`AlgebraicGeometry.FormalSpace.exists_idealOfDefinition_isAdicComplete`), and for such a ring
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem` reads the bound off the quotient
spectra that the quotient system places in the site.

This is what makes the cardinality side condition of
`AlgebraicGeometry.FormalSpace.exists_quotientSystem_continuousHom` free on the presenting rings
of the chart conditions below, all of which are quantified with
`TopologicalRing.IsAdic` and a quotient system. -/
theorem mk_lt_cutoff_of_quotientSystem_of_isAdic {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (hA : TopologicalRing.IsAdic A) (D : QuotientSystem B S hS A) :
    #A < B.cutoff := by
  obtain ⟨I, -, hIadic, hIcomplete⟩ := exists_idealOfDefinition_isAdicComplete hA
  exact mk_lt_cutoff_of_quotientSystem hIadic hIcomplete D

/-- An adic topological ring with a linear topology is weakly admissible. -/
private theorem isWeaklyAdmissible_of_topologicalRing_isAdic {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsAdic A) : TopologicalRing.IsWeaklyAdmissible A := by
  obtain ⟨I, -, hIadic, hIcomplete⟩ := exists_idealOfDefinition_isAdicComplete hA
  exact TopologicalRing.isWeaklyAdmissible_of_isAdic hIadic hIcomplete

/-- The neighbourhood filter of zero in an adic topological ring is countably generated. -/
private theorem isCountablyGenerated_nhds_zero_of_topologicalRing_isAdic {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (hA : TopologicalRing.IsAdic A) :
    (nhds (0 : A)).IsCountablyGenerated := by
  obtain ⟨I, -, hIadic, -⟩ := exists_idealOfDefinition_isAdicComplete hA
  exact hIadic.hasBasis_nhds_zero.isCountablyGenerated

/-- **Rig-surjectivity of a map of McQuillan affine formal algebraic spaces kills the kernel at
every discrete valuation point.** Let `A` be a Noetherian ring with an adic topology carrying a
quotient system `D` over `S`, let `C` be weakly admissible carrying a quotient system `E`, and
let `g : A → C` be continuous over `S`. If `Spf g : Spf C ⟶ Spf A` is rig-surjective then
`ker g` is killed at every discrete valuation point of `A`, in the sense of
`Rig.LeKerAtDvrPoints`.

This is the substantial half of Stacks 0AR0 for the chart maps, read through the full
faithfulness of `Spf` of Stacks 0AN0. Nothing is assumed beyond what the chart conditions below
already quantify with, and no largeness condition on the site is needed.

Three steps join the geometry to the algebra.

The discrete valuation rings of `Rig.LeKerAtDvrPoints` are not assumed adically complete, while
`AlgebraicGeometry.FormalSpace.IsRigSurjective` quantifies only over complete ones, so each is
replaced by its maximal-adic completion `W = R^`. That is again a discrete valuation ring by
Stacks 0AP1 (`isDiscreteValuationRing_iff_adicCompletion_maximalIdeal`), is complete and
small enough to carry a quotient system (`mk_adicCompletion_lt_cutoff`), and `R → W` is
injective (`AdicCompletion.of_injective`), which is what lets the conclusion be read back on
`R`. The restriction to the discrete valuation points below the cutoff costs nothing, by
`Rig.leKerAtDvrPoints_of_leKerAtDvrPointsBelow`: the bound on `A` it needs is free, supplied by
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem_of_isAdic`.

The representability hypothesis of `IsRigSurjective` is Stacks 0AN5,
`isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut`, whose `RingHom.IsTaut`
input is `RingHom.isTaut_of_isAdic` applied to `RingHom.IsAdic (A → W)`. That adicness is
exactly what the two conjuncts of `Rig.LeKerAtDvrPoints` provide: the image of an ideal of
definition of `A` is a nonzero proper ideal of the discrete valuation ring `W`, hence a positive
power of its maximal ideal, hence defines its topology.

The lift that rig-surjectivity returns is a morphism `Spf W' ⟶ Spf C` of formal spectra, and
Stacks 0AN0, `existsUnique_continuousHom_formalSpectrumMap_eq`, turns it back into a ring map
`C → W'` whose composite with `g` is `A → W → W'`; the latter is injective because `W ⊆ W'` is
an extension of discrete valuation rings, which is `FaithfulSMul` by definition. -/
theorem leKerAtDvrPoints_ker_of_isRigSurjective
    {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hAadic : TopologicalRing.IsAdic A) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (g : ContinuousHom D E)
    (hrig : IsRigSurjective B S hS (formalSpectrumMap hA g)) :
    Rig.LeKerAtDvrPoints (RingHom.ker g.toRingHom) := by
  classical
  refine Rig.leKerAtDvrPoints_of_leKerAtDvrPointsBelow hAadic
    (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hAadic D) ?_
  intro R _ _ _ φ hRcard hφ
  obtain ⟨I₀, hI₀def, hI₀adic, -⟩ := exists_idealOfDefinition_isAdicComplete hAadic
  obtain ⟨hI₀ne, hI₀le⟩ := hφ I₀ hI₀def
  -- the maximal-adic completion `W` of `R` is a complete discrete valuation ring
  set W : Type u := AdicCompletion (IsLocalRing.maximalIdeal R) R with hWdef
  obtain ⟨hWdom, hWdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := R)).mp
      ⟨inferInstance, inferInstance⟩
  have : IsDomain W := hWdom
  have : IsDiscreteValuationRing W := hWdvr
  let : TopologicalSpace W := (IsLocalRing.maximalIdeal W).adicTopology
  have hWtopring : IsTopologicalRing W :=
    (IsLocalRing.maximalIdeal W).ringFilterBasis.isTopologicalRing
  have hWlin : IsLinearTopology W W := (IsLocalRing.maximalIdeal W).isLinearTopology
  have hWtop : _root_.IsAdic (IsLocalRing.maximalIdeal W) := rfl
  have hWcomplete : IsAdicComplete (IsLocalRing.maximalIdeal W) W := inferInstance
  have hWweak : TopologicalRing.IsWeaklyAdmissible W :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hWtop hWcomplete
  have hWcard : #W < B.cutoff := mk_adicCompletion_lt_cutoff _ hRcard
  -- the composite `ψ : A → R → W` is adic, hence continuous and taut
  have hinj : Function.Injective (algebraMap R W) :=
    AdicCompletion.of_injective (IsLocalRing.maximalIdeal R) R
  set ψ : A →+* W := (algebraMap R W).comp φ with hψdef
  have hψmap : Ideal.map ψ I₀ = Ideal.map (algebraMap R W) (Ideal.map φ I₀) := by
    rw [hψdef, Ideal.map_map]
  have hψne : Ideal.map ψ I₀ ≠ ⊥ := by
    rw [hψmap, Ne, Ideal.map_eq_bot_iff_le_ker]
    intro hle
    refine hI₀ne (le_bot_iff.mp fun x hx => Ideal.mem_bot.mpr (hinj ?_))
    rw [map_zero]
    exact RingHom.mem_ker.mp (hle hx)
  have hψle : Ideal.map ψ I₀ ≤ IsLocalRing.maximalIdeal W := by
    rw [hψmap]
    refine (Ideal.map_mono hI₀le).trans
      (Ideal.map_le_iff_le_comap.mpr (le_of_eq ?_))
    rw [IsLocalRing.maximalIdeal_comap]
  have hψproper : Ideal.map ψ I₀ ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal W).ne_top hψle
  -- `Ideal.map ψ I₀` is a nonzero proper ideal of the discrete valuation ring `W`, which
  -- carries its maximal-adic topology, so it is a positive power of the maximal ideal and
  -- defines that same topology.
  have hψmapadic : _root_.IsAdic (Ideal.map ψ I₀) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hψne hπ
    have heq : Ideal.map ψ I₀ = IsLocalRing.maximalIdeal W ^ n := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
        Ideal.span_singleton_pow]
      exact hn
    have hnpos : 0 < n := by
      by_contra! h
      exact hψproper (by simpa [Nat.eq_zero_of_le_zero h] using heq)
    rw [heq]
    exact is_ideal_adic_pow hWtop hnpos
  have hψadic : RingHom.IsAdic ψ := ⟨I₀, hI₀adic, hψmapadic⟩
  have hψcont : Continuous ψ := continuous_of_isAdic_of_map_le hI₀adic hWtop ψ hψle
  -- the adic point `Spf W ⟶ Spf A`, and the lift that rig-surjectivity returns
  obtain ⟨DW, p, hp⟩ := exists_quotientSystem_continuousHom hA D ψ hψcont hWcard
  obtain ⟨W', hW'ring, hW'dom, hW'dvr, hW'alg, hW'ext, hW'top, hW'topring, hW'lin,
    hW'adic, hW'complete, DW', e, y, he, hy⟩ :=
    hrig W hWtop hWcomplete hWweak DW (formalSpectrumMap hA p)
      (isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hA hWweak
        D DW (hasLargeSite_of_mk_lt_cutoff DW hWcard) p
        (RingHom.isTaut_of_isAdic p.toRingHom p.continuous (by rw [hp]; exact hψadic)))
  let : CommRing W' := hW'ring
  have : IsDomain W' := hW'dom
  have : IsDiscreteValuationRing W' := hW'dvr
  let : Algebra W W' := hW'alg
  let : TopologicalSpace W' := hW'top
  have : IsTopologicalRing W' := hW'topring
  have : IsLinearTopology W' W' := hW'lin
  have : IsDiscreteValuationRing.IsExtension W W' := hW'ext
  have hW'weak : TopologicalRing.IsWeaklyAdmissible W' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hW'adic hW'complete
  -- the lift is `Spf` of a ring map `C → W'`, by Stacks 0AN0
  obtain ⟨χ, hχ, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hC hW'weak y
  obtain ⟨gχ, hgχ⟩ := exists_continuousHom_comp hA g χ hC
  obtain ⟨pe, hpe⟩ := exists_continuousHom_comp hA p e hWweak
  have hhom : gχ = pe := by
    obtain ⟨k, hk, huniq⟩ :=
      existsUnique_continuousHom_formalSpectrumMap_eq hA hW'weak (formalSpectrumMap hA pe)
    clear hk
    refine (huniq gχ ?_).trans (huniq pe rfl).symm
    show formalSpectrumMap hA gχ = formalSpectrumMap hA pe
    rw [← formalSpectrumMap_comp hA hC g χ gχ hgχ,
      ← formalSpectrumMap_comp hA hWweak p e pe hpe, hχ]
    exact hy
  have hring : χ.toRingHom.comp g.toRingHom = (algebraMap W W').comp ψ := by
    have hh := congrArg ContinuousHom.toRingHom hhom
    rw [hgχ, hpe, he, hp] at hh
    exact hh
  -- an element killed by `g` is killed by `A → W'`, hence by `φ`
  intro b hb
  have hb0 : (algebraMap W W') (ψ b) = 0 := by
    rw [← RingHom.comp_apply, ← hring, RingHom.comp_apply,
      RingHom.mem_ker.mp hb, map_zero]
  have hψb : ψ b = 0 := FaithfulSMul.algebraMap_injective W W' (by rw [hb0, map_zero])
  refine RingHom.mem_ker.mpr (hinj ?_)
  rw [map_zero]
  exact hψb

/-- **An `Spf` of a closed immersion whose kernel dies at every discrete valuation point is
rig-surjective**, which is the converse of
`AlgebraicGeometry.FormalSpace.leKerAtDvrPoints_ker_of_isRigSurjective`. Let `A` have an adic
topology and carry a quotient system `D` over `S`, let `C` be weakly admissible and carry a
quotient system `E`, and let `g : A → C` be continuous over `S` with `Spf g` a closed immersion
and `g` taut. If `ker g` is killed at every discrete valuation point of `A`, in the sense of
`Rig.LeKerAtDvrPoints`, then `Spf g` is rig-surjective.

This is the half of Stacks 0AR0 that the source calls trivial, read through Stacks 0AN0. Nothing
beyond the closed immersion is assumed: tautness of `g` and the countable fundamental system of
neighbourhoods of zero are both free on the chart rings, exactly as they are for the
surjectivity clause of Stacks 0AQI.

The factorisation asked for by
`AlgebraicGeometry.FormalSpace.FactorsAdicCompleteDvrPoints` — which by
`AlgebraicGeometry.FormalSpace.isRigSurjective_of_factorsAdicCompleteDvrPoints` is enough, that
implication of Stacks 0AR0 carrying nothing at all — is built in three steps.

Stacks 0AN0, `existsUnique_continuousHom_formalSpectrumMap_eq`, turns the adic point
`p : Spf R ⟶ Spf A` into a continuous ring map `φ : A → R`, and the implication (1) ⟹ (3) of
**Stacks 0AN5**,
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
makes `φ` taut. That implication carries the two conditions
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite`, and both are free here: `A` is adic
and carries `D`, while `R` carries its maximal-adic topology, is complete for it and carries
`D_R`, so `AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem_of_isAdic` and
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem` bound both rings by the cutoff of
the site and `AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff` supplies the
conditions.

Tautness of `φ` then yields the two conjuncts of `Rig.LeKerAtDvrPoints` for an ideal of
definition `I` of `A`. Were `I R` zero, the closure of the extension of `I` would be the zero
ideal — closed because `R` is separated — and tautness would make it open, so a power of the
maximal ideal of `R` would vanish and `R` would be a field, which a discrete valuation ring is
not (`IsDiscreteValuationRing.not_isField`). And `I R` lies in the maximal ideal because each
element of `I` is topologically nilpotent
(`Rig.isTopologicallyNilpotent_of_mem_isIdealOfDefinition`), hence so is its image, hence some
power of that image lies in the maximal ideal, which a unit cannot do.

So `ker g ≤ ker φ` and `φ` descends through `A ⧸ ker g`. The quotient part of **Stacks 0AQI**,
`AlgebraicGeometry.FormalSpace.isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion`,
identifies `A ⧸ ker g` with `C` *topologically*, and that is what makes the descended map
`C → R` continuous: `Ideal.Quotient.mk` is an open quotient map, so the descent of `φ` is
continuous, and the identification is a homeomorphism.
`AlgebraicGeometry.FormalSpace.exists_continuousHom_of_comp` makes the result a morphism over
`S` and `formalSpectrumMap_comp` identifies its composite with `Spf g` as `p`. -/
theorem isRigSurjective_formalSpectrumMap_of_leKerAtDvrPoints
    {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hAadic : TopologicalRing.IsAdic A) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    (hcount : (nhds (0 : A)).IsCountablyGenerated)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (g : ContinuousHom D E)
    (hgci : IsClosedImmersion B S hS (formalSpectrumMap hA g))
    (htaut : RingHom.IsTaut g.toRingHom)
    (hdvr : Rig.LeKerAtDvrPoints (RingHom.ker g.toRingHom)) :
    IsRigSurjective B S hS (formalSpectrumMap hA g) := by
  classical
  -- Stacks 0AQI presents `C` as `A ⧸ ker g` topologically
  obtain ⟨-, e, he, hehom⟩ :=
    isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion hA hC hcount g hgci htaut
  have hesymm : Continuous (e.symm : C → A ⧸ RingHom.ker g.toRingHom) :=
    e.toEquiv.continuous_symm_iff.2 hehom.isOpenMap
  refine isRigSurjective_of_factorsAdicCompleteDvrPoints B S hS _ ?_
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak DR p hp
  -- Stacks 0AN0 reads the adic point as a continuous ring map `φ : A → R`
  obtain ⟨φ, hφ, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hRweak p
  -- Stacks 0AN5, (1) implies (3): `φ` is taut, both largeness conditions being free
  have htautφ : RingHom.IsTaut φ.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap B S hS hA hRweak D DR
      (hasLargeSite_of_mk_lt_cutoff D
        (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hAadic D))
      (hasLargeSite_of_mk_lt_cutoff DR (mk_lt_cutoff_of_quotientSystem hRadic hRcomplete DR))
      φ (by rwa [hφ])
  have hT2 : T2Space R := hRweak.2.2
  have hmopen : IsOpen ((IsLocalRing.maximalIdeal R) : Set R) := by
    simpa using (isAdic_iff.mp hRadic).1 1
  have hmmem : (0 : R) ∈ ((IsLocalRing.maximalIdeal R) : Set R) :=
    (IsLocalRing.maximalIdeal R).zero_mem
  have hbotcoe : ((⊥ : Ideal R) : Set R) = {0} := Submodule.bot_coe
  have hbotclosed : IsClosed ((⊥ : Ideal R) : Set R) := hbotcoe ▸ isClosed_singleton
  have hbotmem : (0 : R) ∈ ((⊥ : Ideal R) : Set R) := (⊥ : Ideal R).zero_mem
  -- tautness supplies the two conjuncts of `Rig.LeKerAtDvrPoints` at `φ`
  have hpoint : ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
      Ideal.map φ.toRingHom I ≠ ⊥ ∧
        Ideal.map φ.toRingHom I ≤ IsLocalRing.maximalIdeal R := by
    intro I hI
    refine ⟨fun hbot => ?_, ?_⟩
    · -- a zero extension would make `⊥` open, hence kill a power of the maximal ideal
      have hopen : IsOpen (Ideal.closure (Ideal.map φ.toRingHom I) : Set R) := htautφ.1 I hI.1
      rw [hbot, Ideal.closure_eq_of_isClosed _ hbotclosed] at hopen
      obtain ⟨n, hn⟩ := (isAdic_iff.mp hRadic).2 _ (hopen.mem_nhds hbotmem)
      refine IsDiscreteValuationRing.not_isField R
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr
          ((Ideal.pow_eq_bot (Nat.succ_ne_zero n)).mp (le_bot_iff.mp ?_)))
      exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans fun x hx => hn hx
    · -- the image of a topologically nilpotent element cannot be a unit
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      obtain ⟨n, hn⟩ :=
        ((Rig.isTopologicallyNilpotent_of_mem_isIdealOfDefinition hI hx).map
          φ.continuous).exists_pow_mem_of_mem_nhds (hmopen.mem_nhds hmmem)
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        ((IsLocalRing.maximalIdeal R).eq_top_of_isUnit_mem hn (hunit.pow n))
  -- `φ` kills `ker g`, so it descends through the identification of `A ⧸ ker g` with `C`
  have hzero : ∀ a ∈ RingHom.ker g.toRingHom, φ.toRingHom a = 0 := fun a ha =>
    RingHom.mem_ker.mp (hdvr R φ.toRingHom hpoint ha)
  have hliftcont : Continuous (Ideal.Quotient.lift _ φ.toRingHom hzero) :=
    (QuotientRing.isOpenQuotientMap_mk
      (RingHom.ker g.toRingHom)).isQuotientMap.continuous_iff.mpr φ.continuous
  have hψcomp : ((Ideal.Quotient.lift _ φ.toRingHom hzero).comp
      (e.symm : C →+* A ⧸ RingHom.ker g.toRingHom)).comp g.toRingHom = φ.toRingHom := by
    refine RingHom.ext fun x => ?_
    show (Ideal.Quotient.lift _ φ.toRingHom hzero) (e.symm (g.toRingHom x)) = φ.toRingHom x
    rw [← he x, RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  obtain ⟨χ, hχ⟩ := exists_continuousHom_of_comp hA g φ
    ((Ideal.Quotient.lift _ φ.toRingHom hzero).comp
      (e.symm : C →+* A ⧸ RingHom.ker g.toRingHom)) (hliftcont.comp hesymm) hψcomp
  refine ⟨formalSpectrumMap hC χ, ?_⟩
  rw [formalSpectrumMap_comp hA hC g χ φ (by rw [hχ, hψcomp]), hφ]

/-! ### The forward half of the chart comparison, which is Stacks 0AQS -/

/-- **Stacks 0AQS** in the chart shape in which the proof of Stacks 0GD5 uses it: a
rig-surjective morphism has rig-surjective chart base changes, presented as formal spectra of
the chart homomorphisms. Nothing is carried.

A chart `b : V ⟶ Y` which is representable by algebraic spaces and étale is in particular
representable by algebraic spaces, so
`AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback_of_representable` makes the chart
base change `t` rig-surjective; local finite typeness of `f`, which Stacks 0AQS assumes, enters
that lemma only through the conclusion that the base change is locally of finite type, which is
not asserted here. The presenting isomorphisms of the chart are then stripped off by
Stacks 0AQT and its postcomposition companion, which is the step the module documentation used
to record as missing. -/
@[stacks 0AQS "the chart shape in which the proof of Stacks 0GD5 uses it, carrying nothing \
beyond rig-surjectivity of f: a chart which is representable by algebraic spaces and etale is \
in particular representable, so the base change of f along it is rig-surjective, and the \
presenting isomorphisms of the chart are stripped off by Stacks 0AQT and its postcomposition \
companion. Local finite typeness of f and of the chart, which the source assumes, is used by \
the source only for the conclusion that the base change is locally of finite type, which is \
not asserted here"]
theorem hasRigSurjectiveOnPullbackCharts_of_isRigSurjective {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsRigSurjective B S hS f) :
    HasRigSurjectiveOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  obtain ⟨hbrep, -⟩ := hb
  have ht : IsRigSurjective B S hS t :=
    IsRigSurjective.of_isPullback_of_representable B S hS sq.flip hbrep hf
  have hstrip : (eU.inv ≫ t) ≫ eV.hom = formalSpectrumMap hA g := by simp [hg]
  have hcomp : IsRigSurjective B S hS ((eU.inv ≫ t) ≫ eV.hom) :=
    IsRigSurjective.comp_isIso (eU.inv ≫ t) eV.hom
      (IsRigSurjective.isIso_comp eU.inv t ht)
  rwa [hstrip] at hcomp

/-- **Stacks 0AR0 on the charts, the substantial half.** On the charts over `f`,
rig-surjectivity of the chart map forces the kernel of the chart homomorphism to be killed at
every discrete valuation point of its source. This is
`AlgebraicGeometry.FormalSpace.leKerAtDvrPoints_ker_of_isRigSurjective` applied chart by chart,
weak admissibility of the chart ring `C` being read off its adic topology. -/
theorem hasDvrFactorization_of_hasRigSurjective
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : HasRigSurjectiveOnPullbackCharts B S hS f) :
    HasDvrFactorizationOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  exact leKerAtDvrPoints_ker_of_isRigSurjective B S hS hAdicA hA
    (isWeaklyAdmissible_of_topologicalRing_isAdic hAdicC) D E g
    (h V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg)

/-- **The chart homomorphisms of a closed immersion are surjective**, carrying nothing beyond
the closed immersion itself. This is the surjectivity clause of **Stacks 0AQI** on the pullback
charts of `f`.

The chart map `t : U ⟶ V` is a closed immersion because closed immersions are stable under base
change (**Stacks 0GHX**, `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_isPullback`), and
conjugating it by the presenting isomorphisms of the two charts leaves a closed immersion, an
isomorphism square being cartesian; so `Spf g` is a closed immersion. Its representability is
the first component of the closed-immersion predicate of Stacks 0ANP, so the implication
(1) ⟹ (3) of **Stacks 0AN5**,
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
makes `g` taut. That implication carries the two set-theoretic conditions
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite`, and both are free here: the chart
rings are Noetherian with adic topologies carrying quotient systems, so
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem_of_isAdic` bounds each by the
cutoff of the site and
`AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff` supplies the condition. This is why
the surjectivity clause of Stacks 0AQI is not a missing input: it is blocked on nothing.

The passage from tautness to the presentation of the chart ring as a quotient is then the
quotient part of Stacks 0AQI,
`AlgebraicGeometry.FormalSpace.isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion`, whose
remaining inputs are free as well: the source is adic, so the powers of an ideal of definition
are a countable fundamental system of neighbourhoods of zero, and the target is weakly
admissible by `TopologicalRing.isWeaklyAdmissible_of_isAdic` applied to the ideal of definition
for which it is adically complete. Surjectivity is read off the resulting ring equivalence
`A ⧸ ker g ≃+* C`, which agrees with `g` on representatives. -/
@[stacks 0AQI "the surjectivity clause alone, on the pullback charts of a closed immersion, \
carrying nothing: the chart map is a closed immersion by Stacks 0GHX, conjugation by the \
presenting isomorphisms of the two charts preserves that, the implication (1) implies (3) of \
Stacks 0AN5 makes the chart homomorphism taut -- its two HasLargeSite conditions being free on \
chart rings, which are adic and carry quotient systems, by \
mk_lt_cutoff_of_quotientSystem_of_isAdic and hasLargeSite_of_mk_lt_cutoff -- and the quotient \
part of Stacks 0AQI, isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion, turns the \
tautness into the presentation of the chart ring as a quotient. The adic and topologically \
finite type clauses of Stacks 0AQI are not asserted"]
theorem hasSurjectiveOnPullbackCharts_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    HasSurjectiveOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  have hC := isWeaklyAdmissible_of_topologicalRing_isAdic hAdicC
  have hcount := isCountablyGenerated_nhds_zero_of_topologicalRing_isAdic hAdicA
  obtain ⟨hconj, htaut⟩ :=
    isClosedImmersion_formalSpectrumMap_and_isTaut B S hS hf sq hAdicA hAdicC hA eU eV g hg
  obtain ⟨-, e, he, -⟩ :=
    isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion hA hC hcount g hconj htaut
  intro c
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm c)
  exact ⟨x, by rw [← he x, hx, e.apply_symm_apply]⟩

/-- **The chart maps of a closed immersion are rig-surjective as soon as their kernels die at
the discrete valuation points**, carrying nothing beyond the closed immersion itself. This is
the half of **Stacks 0AR0** that the source calls trivial, in chart form.

The chart homomorphism is taut with `Spf` of it a closed immersion, which is the same first step
as for the surjectivity clause above, and
`AlgebraicGeometry.FormalSpace.isRigSurjective_formalSpectrumMap_of_leKerAtDvrPoints` then turns
the annihilation into rig-surjectivity. The remaining inputs are free on the chart rings for the
reasons recorded there: the source is adic, so the powers of an ideal of definition are a
countable fundamental system of neighbourhoods of zero, and the target is weakly admissible by
`TopologicalRing.isWeaklyAdmissible_of_isAdic` applied to the ideal of definition for which it
is adically complete. -/
theorem hasRigSurjectiveOnPullbackCharts_of_hasDvrFactorization_of_isClosedImmersion
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f)
    (h : HasDvrFactorizationOnPullbackCharts B S hS f) :
    HasRigSurjectiveOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  have hC := isWeaklyAdmissible_of_topologicalRing_isAdic hAdicC
  have hcount := isCountablyGenerated_nhds_zero_of_topologicalRing_isAdic hAdicA
  obtain ⟨hconj, htaut⟩ :=
    isClosedImmersion_formalSpectrumMap_and_isTaut B S hS hf sq hAdicA hAdicC hA eU eV g hg
  exact isRigSurjective_formalSpectrumMap_of_leKerAtDvrPoints B S hS hAdicA hA hC hcount D E g
    hconj htaut (h V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg)

/-- **The two chart conditions of Stacks 0GD5 agree for a closed immersion.** For a closed
immersion `f`, condition (2) of Stacks 0GD5 on the pullback charts — the chart homomorphism is
surjective and an ideal of definition of its source annihilates a positive power of its
kernel — holds exactly when every chart map `Spf C ⟶ Spf A` is rig-surjective.

This is the whole of the source's proof except for the passage between `f` and its charts.
Surjectivity of the chart homomorphisms is `hasSurjectiveOnPullbackCharts_of_isClosedImmersion`;
Stacks 0AR0 on the charts, in both directions, is `hasDvrFactorization_of_hasRigSurjective` and
`hasRigSurjectiveOnPullbackCharts_of_hasDvrFactorization_of_isClosedImmersion`; and the algebra,
which uses Stacks 00PH, is `hasAnnihilatedKerPow_iff_hasDvrFactorization_of_hasSurjective`. -/
theorem hasAnnihilatedKerPow_iff_hasRigSurjective_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    HasAnnihilatedKerPowOnPullbackCharts B S hS f ↔
      HasRigSurjectiveOnPullbackCharts B S hS f :=
  (hasAnnihilatedKerPow_iff_hasDvrFactorization_of_hasSurjective B S hS f
      (hasSurjectiveOnPullbackCharts_of_isClosedImmersion B S hS f hf)).trans
    ⟨hasRigSurjectiveOnPullbackCharts_of_hasDvrFactorization_of_isClosedImmersion B S hS f hf,
      hasDvrFactorization_of_hasRigSurjective B S hS f⟩

/-- Stacks 0GD5 for a closed immersion `f` reduced to the passage from the charts to `f`: given
that rig-surjectivity of all chart maps gives rig-surjectivity of `f`, the two conditions of
Stacks 0GD5 are equivalent. The converse passage is
`AlgebraicGeometry.FormalSpace.hasRigSurjectiveOnPullbackCharts_of_isRigSurjective`. -/
theorem isRigSurjective_iff_hasAnnihilatedKerPow {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (hf : IsClosedImmersion B S hS f)
    (hcharts : HasRigSurjectiveOnPullbackCharts B S hS f → IsRigSurjective B S hS f) :
    IsRigSurjective B S hS f ↔ HasAnnihilatedKerPowOnPullbackCharts B S hS f :=
  (⟨hasRigSurjectiveOnPullbackCharts_of_isRigSurjective B S hS f, hcharts⟩ :
      IsRigSurjective B S hS f ↔ HasRigSurjectiveOnPullbackCharts B S hS f).trans
    (hasAnnihilatedKerPow_iff_hasRigSurjective_of_isClosedImmersion B S hS f hf).symm

/-! ### From the charts to the morphism -/

/-- **A closed immersion of formal algebraic spaces is locally of finite type.** Each base change
of a closed immersion `f` along a scheme-valued point `h_U ⟶ Y` of its target is, up to
isomorphism, the image `h_W ⟶ h_U` of a closed immersion `W ⟶ U` of the site: the base change
of it along the identity of `h_U` is representable because `f` is a closed immersion. A closed
immersion of schemes is locally of finite type, and that passes to every étale chart. -/
theorem IsLocallyOfFiniteType.of_isClosedImmersion {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) : IsLocallyOfFiniteType B S hS f := by
  obtain ⟨hrep, hci⟩ := hf
  refine ⟨hrep, fun U ξ => ?_⟩
  show Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ f.hom)
  have hrel := hci U ξ
  obtain ⟨W, k, e, hpb⟩ := hrel.1 (𝟙 ((uliftYoneda.{u + 1}).obj U))
  have hk : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) :=
    hrel.2 (𝟙 _) e k hpb
  have : IsIso e := hpb.isIso_fst_of_isIso
  have hfac : pullback.fst ξ f.hom = inv e ≫ (uliftYoneda.{u + 1}).map k := by
    rw [IsIso.eq_inv_comp, ← Category.comp_id ((uliftYoneda.{u + 1}).map k), ← hpb.w]
    rfl
  rw [hfac]
  exact Space.holdsOnEveryEtaleChartULift_precomp B S hS _ (inv e) _
    (Space.isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS k inferInstance)

/-- **The fibre product of a closed immersion with a Noetherian chart is a chart of
`HasRigSurjectiveOnPullbackCharts`.** Let `f : X ⟶ Y` be a closed immersion and let
`b : V ⟶ Y` be representable étale with `V` a Noetherian affine formal algebraic space. If the
chart condition `AlgebraicGeometry.FormalSpace.HasRigSurjectiveOnPullbackCharts` holds for `f`,
then the base change `X ×_Y V ⟶ V` of `f` is rig-surjective.

The chart condition is quantified over presentations of `V` and of `X ×_Y V` by Noetherian
rings with adic topologies, so the work is to produce such presentations. `V` is presented by
its Noetherian adic ring `A`. The base change is a closed immersion (**Stacks 0GHX**), so
`X ×_Y V` is a countably indexed affine formal algebraic space (**Stacks 0AQI**) and is the
formal spectrum of a weakly admissible ring `C` with a countable fundamental system of
neighbourhoods of zero (**Stacks 0AN1**); the closed immersion is `Spf` of a continuous
homomorphism `g : A ⟶ C` (**Stacks 0AN0**). That homomorphism is taut by the implication
(1) ⟹ (3) of **Stacks 0AN5**, the two formal spectra being affine because they are isomorphic
to `V` and to `X ×_Y V`, so the quotient part of Stacks 0AQI identifies `C` with `A ⧸ ker g`
as topological rings. Hence `C` is Noetherian, and its topology is the adic topology of the
image of an ideal of definition of `A`; being weakly admissible it is complete, so it is
adic. The chart condition then makes `Spf g` rig-surjective, and Stacks 0AQT strips the
presenting isomorphisms. -/
theorem isRigSurjective_pullback_snd_of_hasRigSurjectiveOnPullbackCharts
    {X Y V : FppfSheaf B S hS} (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) (b : V ⟶ Y)
    (hb : IsRepresentableEtale B S hS b) (hV : IsNoetherian B S hS V)
    (h : HasRigSurjectiveOnPullbackCharts B S hS f) :
    IsRigSurjective B S hS (pullback.snd f b) := by
  obtain ⟨⟨hVaff, -⟩, A, _, _, _, _, hpres, _, hAadic⟩ := hV
  have hA : TopologicalRing.IsWeaklyAdmissible A := hpres.1
  set D : QuotientSystem B S hS A := hpres.2.some.quotientSystem
  set eV : V ≅ formalSpectrum D := hpres.2.some.formalSpectrumIso
  obtain ⟨I, -, hIadic, -⟩ := exists_idealOfDefinition_isAdicComplete hAadic
  have hcountA := isCountablyGenerated_nhds_zero_of_topologicalRing_isAdic hAadic
  have hVci : IsCountablyIndexedAffine B S hS V :=
    ⟨hVaff, isCountablyIndexed_of_isPresentingRing B S hS V A hpres hcountA⟩
  have sq : IsPullback (pullback.fst f b) (pullback.snd f b) f b := IsPullback.of_hasPullback f b
  have ht : IsClosedImmersion B S hS (pullback.snd f b) :=
    isClosedImmersion_of_isPullback B S hS sq hf
  have hUci : IsCountablyIndexedAffine B S hS (pullback f b) :=
    isCountablyIndexedAffine_of_isClosedImmersion B S hS hVci (pullback.snd f b) ht
  obtain ⟨Q, hC, -⟩ := hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS _ hUci
  obtain ⟨eU⟩ := Q.iso
  obtain ⟨g, hg, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hA hC (eU.inv ≫ pullback.snd f b ≫ eV.hom)
  have ht' : pullback.snd f b = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv := by
    rw [hg]; simp
  -- `Spf g` is a closed immersion and `g` is taut
  have hconj : IsClosedImmersion B S hS (formalSpectrumMap hA g) := by
    rw [hg]
    exact isClosedImmersion_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (fst := eU.inv) (snd := eU.inv ≫ pullback.snd f b ≫ eV.hom)
        (f := pullback.snd f b) (g := eV.inv) ⟨by simp⟩) ht
  have htaut : RingHom.IsTaut g.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS hA hC
      D Q.system (isAffineFormalAlgebraicSpace_of_iso B S hS eV hVaff)
      (isAffineFormalAlgebraicSpace_of_iso B S hS eU hUci.1) g hconj.1
  obtain ⟨-, e, -, hehom⟩ :=
    isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion hA hC hcountA g hconj htaut
  have hesymm : Continuous (e.symm : Q.ring → A ⧸ RingHom.ker g.toRingHom) :=
    e.toEquiv.continuous_symm_iff.2 hehom.isOpenMap
  -- `C` is Noetherian with an adic topology
  have : IsNoetherianRing Q.ring := isNoetherianRing_of_ringEquiv _ e
  have hpre : TopologicalRing.IsPreAdic (A ⧸ RingHom.ker g.toRingHom) :=
    ⟨I.map (Ideal.Quotient.mk _),
      TopologicalRing.isIdealOfDefinition_of_isAdic (isAdic_map_quotient_mk I _ hIadic),
      isAdic_map_quotient_mk I _ hIadic⟩
  have hCadic : TopologicalRing.IsAdic Q.ring :=
    ⟨TopologicalRing.isPreAdic_of_ringEquiv e hehom.continuous hesymm hpre, hC.2.2, hC.2.1⟩
  have hrig : IsRigSurjective B S hS (formalSpectrumMap hA g) :=
    h V hVaff b hb _ (pullback.fst f b) (pullback.snd f b) sq A Q.ring hAadic hCadic hA D
      Q.system eU eV g ht'
  rw [ht', ← Category.assoc]
  exact IsRigSurjective.comp_isIso _ _ (IsRigSurjective.isIso_comp _ _ hrig)

end AlgebraicGeometry.FormalSpace

end
