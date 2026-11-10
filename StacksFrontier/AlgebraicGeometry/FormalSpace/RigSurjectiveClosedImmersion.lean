module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# Rig-surjective closed immersions

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a closed immersion
of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GD5** says that `f` is
rig-surjective if and only if for every affine formal algebraic space `V` and every morphism
`V ⟶ Y` representable by algebraic spaces and étale the base change `X ×_Y V ⟶ V` corresponds
to a surjective morphism `B → A` of `WAdm^{Noeth}` whose kernel `J` satisfies `I * J ^ n = 0`
for some ideal of definition `I` of `B` and some `n ≥ 1`.

## Main definitions

* `Rig.LeKerAtDvrPoints` — the algebraic form of the factorisation criterion of Stacks 0AR0:
  every adic homomorphism from a linearly topologized ring to a discrete valuation ring kills
  the given ideal.
* `AlgebraicGeometry.FormalSpace.HasAnnihilatedKerPowOnPullbackCharts` — condition (2).
* `AlgebraicGeometry.FormalSpace.HasRigSurjectiveOnPullbackCharts` — the same quantification
  with the chart map required to be rig-surjective, which is the shape in which Stacks 0AQS
  and Stacks 0AQV are used.
* `AlgebraicGeometry.FormalSpace.HasDvrFactorizationOnPullbackCharts` — the same
  quantification with the conclusion `Rig.LeKerAtDvrPoints`, which is the shape in which
  Stacks 0AR0 is used.

## Main results

* `Rig.leKerAtDvrPoints_of_mul_pow_eq_bot` and `Rig.exists_mul_pow_eq_bot_of_leKerAtDvrPoints`:
  the algebraic heart of Stacks 0GD5, that for a Noetherian adic ring an ideal `J` is killed at
  every adic discrete valuation point exactly when `I * J ^ n = 0` for an ideal of definition
  `I` and an `n ≥ 1`.
* `AlgebraicGeometry.FormalSpace.hasAnnihilatedKerPow_iff_hasDvrFactorization`: the previous
  equivalence transported to the charts over `f`.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_hasAnnihilatedKerPowOnPullbackCharts`:
  **Stacks 0GD5**, both directions, carrying three hypotheses — see below.
* `AlgebraicGeometry.FormalSpace.hasAnnihilatedKerPow_iff_hasDvrFactorization_of_hasSurjective`:
  the same equivalence of the two chart conditions, needing of Stacks 0AQI only its
  surjectivity clause.

## Implementation notes

Condition (2) is quantified exactly as condition (3) of Stacks 0GD4 is in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersion`: over a chart `V ⟶ Y` of
the target, a fibre product of `f` along it, adic Noetherian presenting rings `A` of `V` and
`C` of the fibre product, and a continuous homomorphism `g : A ⟶ C` inducing the chart map.
The source's `B → A` is the present `g : A ⟶ C`, so `J` is `RingHom.ker g.toRingHom`, and
`IJ^n = 0` is rendered as `I * RingHom.ker g.toRingHom ^ n = ⊥` with the ideal of definition
and the positive exponent existentially quantified, as in the source.

The two implications of the source's proof are, after the geometric reductions, one algebraic
equivalence, and that equivalence is what is proved here.

* `Rig.leKerAtDvrPoints_of_mul_pow_eq_bot` is the source's (2) ⟹ (1) step: if `I * J ^ n = 0`
  and `φ : A → R` lands in a domain without killing `I`, then for `b ∈ J` and `a ∈ I` with
  `φ a ≠ 0` the relation `a * b ^ n = 0` forces `φ b = 0`, so `φ` factors through `A / J`.
* `Rig.exists_mul_pow_eq_bot_of_leKerAtDvrPoints` is the source's (1) ⟹ (2) step. If no power
  of an ideal of definition `I₀` annihilates a power of `J`, then `I₀ * J` is a finitely
  generated non-nilpotent ideal, hence escapes some prime `p`, and then so do `I₀` and `J`.
  Since `A` is `I₀`-adically complete, `I₀` lies in the Jacobson radical (Stacks 00HQ is not
  needed: `Ideal.mem_jacobson_bot` suffices), so `p + I₀` is proper and sits inside a maximal
  ideal `m`. The localization of `A / p` at the image of `m` is a Noetherian local domain which
  is not a field, because an element of `I₀` outside `p` is a nonzero element of its maximal
  ideal, and **Stacks 00PH** dominates it by a discrete valuation ring `R`. The resulting
  `A → R` is adic — every ideal of definition lands in the maximal ideal of `R`, being inside
  the Jacobson radical and hence inside `m`, and lands there nontrivially, because a power of
  `I₀` lies inside it and escapes `p` — while `J` is not killed, which contradicts the
  criterion.

Three inputs are carried as explicit hypotheses, being the three results of the source's
`\uses` list which this library does not have in the shape the proof consumes. Stacks 00PH,
the fourth, is used for real.

* `hAQI` is **Stacks 0AQI** in the form Stacks 0GD4 already uses it,
  `AlgebraicGeometry.FormalSpace.HasAdicQuotientOnPullbackCharts`: the chart map is a surjection
  of `WAdm^{Noeth}` which is adic of topologically finite type. The source's proof opens by
  invoking exactly this, and it supplies the surjectivity conjunct of condition (2). What the
  library carries of Stacks 0AQI is the countably indexed case, and even that only given the
  tautness of Stacks 0AN5.
* `hAQV` is the equivalence of rig-surjectivity of `f` with rig-surjectivity of its chart base
  changes. Its forward direction is **Stacks 0AQS**, stability of rig-surjectivity under base
  change, and its backward direction is **Stacks 0AQV**, that rig-surjectivity is étale local
  on the target. The library has both —
  `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback` and
  `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_forall_pullback_snd` — but neither in
  the chart shape used here: the first needs the chart map presented as a projection of a fibre
  product rather than as `Spf` of `g`, and the second is stated for a jointly surjective family
  and carries two hypotheses of its own.
* `hAR0` is **Stacks 0AR0** applied to the chart maps, read through the full faithfulness of
  `Spf` (**Stacks 0AN0**): rig-surjectivity of `Spf C ⟶ Spf A` is the assertion that every adic
  morphism from the formal spectrum of a complete discrete valuation ring to `Spf A` factors
  through `Spf C`, that is, that `ker g` is killed by every adic homomorphism of `A` into a
  discrete valuation ring. The chart maps are closed immersions, hence monomorphisms, and are
  locally of finite type, so Stacks 0AR0 does apply to them; the library's form,
  `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_factorsAdicCompleteDvrPoints`, is stated
  for the geometric factorisation criterion rather than for the homomorphisms `A → R` which
  Stacks 0AN0 identifies it with, and carries Stacks 0AQD as a hypothesis of its own.

Neither direction of the equivalence being claimed is among the carried hypotheses: `hAQV` and
`hAR0` together identify rig-surjectivity of `f` with
`AlgebraicGeometry.FormalSpace.HasDvrFactorizationOnPullbackCharts`, and the passage from there
to condition (2) is the algebraic equivalence proved here.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0AQV](https://stacks.math.columbia.edu/tag/0AQV)
* [Stacks Project, Tag 0AR0](https://stacks.math.columbia.edu/tag/0AR0)
* [Stacks Project, Tag 0GD4](https://stacks.math.columbia.edu/tag/0GD4)
* [Stacks Project, Tag 0GD5](https://stacks.math.columbia.edu/tag/0GD5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Rig

/-- An ideal `J` of a topological ring `A` is *killed at the discrete valuation points* of `A`
when every homomorphism `φ : A → R` to a discrete valuation ring which is adic — the image of
each ideal of definition of `A` generating a nonzero ideal inside the maximal ideal of `R` —
kills `J`. For `A` adic this is the algebraic form of the right-hand side of Stacks 0AR0 for
the closed immersion `Spf (A / J) ⟶ Spf A`, read through the full faithfulness of `Spf`
(Stacks 0AN0). -/
def LeKerAtDvrPoints {A : Type u} [CommRing A] [TopologicalSpace A] (J : Ideal A) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (φ : A →+* R),
    (∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
        Ideal.map φ I ≠ ⊥ ∧ Ideal.map φ I ≤ IsLocalRing.maximalIdeal R) →
      J ≤ RingHom.ker φ

/-- If an ideal of definition `I` annihilates a positive power of `J`, then `J` is killed at
every discrete valuation point of `A`: a homomorphism into a domain which does not kill `I`
takes some `a ∈ I` to a nonzero element, and `a * b ^ n = 0` for `b ∈ J`, so `φ b` is
nilpotent, hence zero. -/
theorem leKerAtDvrPoints_of_mul_pow_eq_bot {A : Type u} [CommRing A] [TopologicalSpace A]
    {I J : Ideal A} (hI : TopologicalRing.IsIdealOfDefinition I) {n : ℕ} (hn : n ≠ 0)
    (h : I * J ^ n = ⊥) : LeKerAtDvrPoints J := by
  intro R _ _ _ φ hadic
  obtain ⟨hne, -⟩ := hadic I hI
  rw [Ne, Ideal.map_eq_bot_iff_le_ker, IsConcreteLE.not_le_iff_exists] at hne
  obtain ⟨a, haI, haker⟩ := hne
  intro b hb
  have hab : a * b ^ n = 0 := by
    simpa [h] using Ideal.mul_mem_mul haI (Ideal.pow_mem_pow hb n)
  have hz : φ a * φ b ^ n = 0 := by rw [← map_pow, ← map_mul, hab, map_zero]
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact absurd (RingHom.mem_ker.2 h1) haker
  · exact RingHom.mem_ker.2 ((pow_eq_zero_iff hn).1 h2)

/-- Every ideal of definition of a ring which is adically complete for one of them lies in the
Jacobson radical: a power of it is contained in that one, hence in the Jacobson radical, and a
maximal ideal containing a power of an element contains the element. -/
@[ega "0 7.1.10" "more general"]
private theorem idealOfDefinition_le_jacobson {A : Type u} [CommRing A] [TopologicalSpace A]
    {I₀ I : Ideal A} (hI₀ : TopologicalRing.IsIdealOfDefinition I₀) [IsAdicComplete I₀ A]
    (hI : TopologicalRing.IsIdealOfDefinition I) : I ≤ Ideal.jacobson (⊥ : Ideal A) := by
  obtain ⟨n, hn⟩ := hI.2 (I₀ : Set A) (hI₀.1.mem_nhds I₀.zero_mem)
  intro x hx
  have hxn : x ^ (n + 1) ∈ Ideal.jacobson (⊥ : Ideal A) :=
    IsAdicComplete.le_jacobson_bot I₀
      (hn (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hx (n + 1))))
  rw [Ideal.jacobson, Submodule.mem_sInf] at hxn ⊢
  exact fun K hK => hK.2.isPrime.mem_of_pow_mem (n + 1) (hxn K hK)

/-- A Noetherian local domain which is not a field is dominated by a discrete valuation ring
inside its fraction field. This is **Stacks 00PH** for the identity extension of the fraction
field, with domination recorded as sending the maximal ideal into the maximal ideal. -/
private theorem exists_dvr_of_isLocalDomain (T : Type u) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsLocalRing T] (hT : ¬ IsField T) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (ψ : T →+* R), Function.Injective ψ ∧
        ∀ y ∈ IsLocalRing.maximalIdeal T, ψ y ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨R, hRdvr, -, hRloc⟩ :=
    Stacks.DiscreteValuationRing.Existence.solution (R := T) (FractionRing T)
      (L := FractionRing T) hT
  have hinj : Function.Injective (algebraMap T R) := fun a b hab => by
    apply FaithfulSMul.algebraMap_injective T (FractionRing T)
    rw [IsScalarTower.algebraMap_apply T R (FractionRing T),
      IsScalarTower.algebraMap_apply T R (FractionRing T), hab]
  refine ⟨R, inferInstance, inferInstance, hRdvr, algebraMap T R, hinj, fun y hy => ?_⟩
  rw [IsLocalRing.mem_maximalIdeal] at hy ⊢
  exact fun hu => hy (hRloc.map_nonunit _ hu)

/-- A Noetherian domain with a nonzero prime `q` admits an injective homomorphism into a
discrete valuation ring taking `q` into the maximal ideal: localize at `q`, which is a
Noetherian local domain and not a field, and dominate it by Stacks 00PH. -/
private theorem exists_dvr_of_isPrime_ne_bot (D : Type u) [CommRing D] [IsDomain D]
    [IsNoetherianRing D] (q : Ideal D) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (ψ : D →+* R), Function.Injective ψ ∧
        ∀ y ∈ q, ψ y ∈ IsLocalRing.maximalIdeal R := by
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
    exact hy0 (hinj (by simpa [hbot] using hmem y hyq))
  obtain ⟨R, _, _, hRdvr, ψ, hψinj, hψloc⟩ :=
    exists_dvr_of_isLocalDomain (Localization.AtPrime q) hnotField
  exact ⟨R, inferInstance, inferInstance, hRdvr,
    ψ.comp (algebraMap D (Localization.AtPrime q)), hψinj.comp hinj,
    fun y hy => hψloc _ (hmem y hy)⟩

/-- A prime `p` of a Noetherian adic ring not containing an ideal of definition `I₀` is
dominated by an adic discrete valuation point: there is a discrete valuation ring `R` and a
homomorphism `A → R` whose kernel is inside `p` and which carries every ideal of definition
into the maximal ideal of `R`. -/
private theorem exists_dvr_ker_le_of_isPrime {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsNoetherianRing A] {I₀ : Ideal A}
    (hI₀ : TopologicalRing.IsIdealOfDefinition I₀) [IsAdicComplete I₀ A]
    {p : Ideal A} (hp : p.IsPrime) (hpI : ¬ I₀ ≤ p) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : A →+* R), RingHom.ker φ ≤ p ∧
        ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
          Ideal.map φ I ≤ IsLocalRing.maximalIdeal R := by
  classical
  have hne : p ⊔ I₀ ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ p ⊔ I₀ := htop ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨x, hx, a, ha, hxa⟩ := h1
    have hu : IsUnit x := by
      have h2 := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I₀ ha) (-1)
      rwa [show a * (-1) + 1 = x by linear_combination -hxa] at h2
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx hu)
  obtain ⟨m, hm, hmle⟩ := Ideal.exists_le_maximal _ hne
  have _ : (m.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by simpa [Ideal.mk_ker] using le_sup_left.trans hmle)
  have hjm : Ideal.jacobson (⊥ : Ideal A) ≤ m := sInf_le ⟨bot_le, hm⟩
  obtain ⟨x₀, hx₀I, hx₀p⟩ := IsConcreteLE.not_le_iff_exists.mp hpI
  have hqne : m.map (Ideal.Quotient.mk p) ≠ ⊥ := by
    intro hbot
    refine hx₀p (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    have hx₀ := Ideal.mem_map_of_mem (Ideal.Quotient.mk p) (le_sup_right.trans hmle hx₀I)
    rwa [hbot, Ideal.mem_bot] at hx₀
  obtain ⟨R, _, _, hRdvr, ψ, hψinj, hψq⟩ :=
    exists_dvr_of_isPrime_ne_bot (A ⧸ p) (m.map (Ideal.Quotient.mk p)) hqne
  exact ⟨R, inferInstance, inferInstance, hRdvr, ψ.comp (Ideal.Quotient.mk p),
    fun z hz => Ideal.Quotient.eq_zero_iff_mem.mp (hψinj (by simpa using hz)),
    fun I hI => Ideal.map_le_iff_le_comap.mpr fun z hz => Ideal.mem_comap.mpr
      (hψq _ (Ideal.mem_map_of_mem _ (hjm (idealOfDefinition_le_jacobson hI₀ hI hz))))⟩

/-- An ideal `J` of a Noetherian adic ring which is killed at every discrete valuation point
has a positive power annihilated by an ideal of definition: otherwise `I₀ * J` is a finitely
generated non-nilpotent ideal for an ideal of definition `I₀` defining the topology, so some
prime `p` contains neither `I₀` nor `J`, and the discrete valuation point dominating `p`
kills `I₀` on no ideal of definition yet fails to kill `J`. -/
theorem exists_mul_pow_eq_bot_of_leKerAtDvrPoints {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) {J : Ideal A} (h : LeKerAtDvrPoints J) :
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
    by_contra! ⟨hI₀P, hJP⟩
    obtain ⟨R, _, _, _, φ, hker, hmax⟩ := exists_dvr_ker_le_of_isPrime hI₀def hPp hI₀P
    refine hJP ((h R φ fun I hI => ⟨?_, hmax I hI⟩).trans hker)
    rw [Ne, Ideal.map_eq_bot_iff_le_ker]
    intro hIker
    obtain ⟨j, hj⟩ := hI₀def.2 (I : Set A) (hI.1.mem_nhds I.zero_mem)
    exact hI₀P ((Ideal.IsPrime.pow_le_iff (I := I₀) (P := P) (Nat.succ_ne_zero j)).mp
      ((Ideal.pow_le_pow_right (Nat.le_succ j)).trans (le_trans hj (hIker.trans hker))))
  obtain ⟨k, hk⟩ := hnil
  exact ⟨I₀ ^ (k + 1), AlgebraicGeometry.FormalSpace.isIdealOfDefinition_pow_succ hI₀adic k,
    k + 1, Nat.succ_ne_zero k, by rw [← mul_pow, pow_succ, hk, zero_mul, Ideal.zero_eq_bot]⟩

end Rig

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GD5, condition (2).** For every affine formal algebraic space `V`, every
representable étale `V ⟶ Y` and every fibre product of `f` along it, the induced morphism of
presenting rings of `WAdm^{Noeth}` is surjective and some ideal of definition `I` of the source
annihilates a positive power of its kernel `J`. -/
abbrev HasAnnihilatedKerPowOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (_hV : IsAffineFormalAlgebraicSpace B S hS V) (b : V ⟶ Y)
    (_hb : IsRepresentableEtale B S hS b) (U : FppfSheaf B S hS) (a : U ⟶ X) (t : U ⟶ V),
    IsPullback a t f b → ∀ (A C : Type u)
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [IsNoetherianRing A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
        [IsNoetherianRing C],
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
        (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (g : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
          Function.Surjective g.toRingHom ∧
            ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
              ∃ n : ℕ, n ≠ 0 ∧ I * RingHom.ker g.toRingHom ^ n = ⊥

/-- The condition of `AlgebraicGeometry.FormalSpace.HasAnnihilatedKerPowOnPullbackCharts` with
the conclusion replaced by rig-surjectivity of the chart map. This is the intermediate
condition through which the source's proof passes, by Stacks 0AQS in one direction and
Stacks 0AQV in the other. -/
abbrev HasRigSurjectiveOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (_hV : IsAffineFormalAlgebraicSpace B S hS V) (b : V ⟶ Y)
    (_hb : IsRepresentableEtale B S hS b) (U : FppfSheaf B S hS) (a : U ⟶ X) (t : U ⟶ V),
    IsPullback a t f b → ∀ (A C : Type u)
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [IsNoetherianRing A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
        [IsNoetherianRing C],
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
        (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (g : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
          IsRigSurjective B S hS (formalSpectrumMap hA g)

/-- The condition of `AlgebraicGeometry.FormalSpace.HasAnnihilatedKerPowOnPullbackCharts` with
the conclusion replaced by the kernel of the chart homomorphism being killed at every discrete
valuation point of the source. This is the shape in which Stacks 0AR0 is used. -/
abbrev HasDvrFactorizationOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (_hV : IsAffineFormalAlgebraicSpace B S hS V) (b : V ⟶ Y)
    (_hb : IsRepresentableEtale B S hS b) (U : FppfSheaf B S hS) (a : U ⟶ X) (t : U ⟶ V),
    IsPullback a t f b → ∀ (A C : Type u)
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [IsNoetherianRing A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
        [IsNoetherianRing C],
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
        (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (g : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
          Rig.LeKerAtDvrPoints (RingHom.ker g.toRingHom)

/-- Condition (2) of Stacks 0GD5 implies that the kernel of each chart homomorphism is killed at
every discrete valuation point of the chart ring. -/
private theorem hasDvrFactorization_of_hasAnnihilatedKerPow {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (h2 : HasAnnihilatedKerPowOnPullbackCharts B S hS f) :
    HasDvrFactorizationOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  obtain ⟨-, I, hI, n, hn, hmul⟩ := h2 V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
  exact Rig.leKerAtDvrPoints_of_mul_pow_eq_bot hI hn hmul

/-- The algebraic heart of **Stacks 0GD5**, transported to the charts over `f`: given that the
chart homomorphisms are surjective (Stacks 0AQI, the hypothesis `hAQI`), condition (2) of
Stacks 0GD5 holds exactly when the kernel of each chart homomorphism is killed at every
discrete valuation point of the chart ring. -/
theorem hasAnnihilatedKerPow_iff_hasDvrFactorization {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hAQI : HasAdicQuotientOnPullbackCharts B S hS f) :
    HasAnnihilatedKerPowOnPullbackCharts B S hS f ↔
      HasDvrFactorizationOnPullbackCharts B S hS f := by
  constructor
  · exact hasDvrFactorization_of_hasAnnihilatedKerPow B S hS f
  · intro h V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
    exact ⟨(hAQI V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg).1,
      Rig.exists_mul_pow_eq_bot_of_leKerAtDvrPoints hAdicA
        (h V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg)⟩

/-- **Stacks 0GD5**, both directions, carrying three hypotheses. Let `f : X ⟶ Y` be a closed
immersion of locally Noetherian formal algebraic spaces over `S`. Then `f` is rig-surjective
exactly when on every affine representable étale chart `V ⟶ Y` of the target the fibre product
`X ×_Y V ⟶ V` is given by a surjection of `WAdm^{Noeth}` some ideal of definition of whose
source annihilates a positive power of its kernel.

The hypothesis `hAQI` is Stacks 0AQI in the chart form of Stacks 0GD4, `hAQV` is the
equivalence of rig-surjectivity of `f` with rig-surjectivity of its chart base changes
(Stacks 0AQS forwards, Stacks 0AQV backwards), and `hAR0` is Stacks 0AR0 for the chart maps,
read through the full faithfulness of `Spf`. The passage from the factorisation criterion to
the annihilation condition is the algebraic equivalence proved here, which uses
**Stacks 00PH**. -/
@[stacks 0GD5 "both directions, carrying three hypotheses: Stacks 0AQI in the chart form of \
Stacks 0GD4, that the chart homomorphism is a surjection of WAdm^Noeth which is adic of \
topologically finite type (hAQI); the equivalence of rig-surjectivity of f with \
rig-surjectivity of its chart base changes, which is Stacks 0AQS forwards and Stacks 0AQV \
backwards (hAQV); and Stacks 0AR0 for the chart maps, read through the full faithfulness of \
Spf of Stacks 0AN0, identifying rig-surjectivity of a chart map with the factorisation of its \
adic discrete valuation points (hAR0). The algebraic equivalence joining the factorisation \
criterion to the annihilation condition, which is what the source's two implications come \
down to and which uses Stacks 00PH, is proved"]
theorem isRigSurjective_iff_hasAnnihilatedKerPowOnPullbackCharts {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (_hf : IsClosedImmersion B S hS f)
    (hAQI : HasAdicQuotientOnPullbackCharts B S hS f)
    (hAQV : IsRigSurjective B S hS f ↔ HasRigSurjectiveOnPullbackCharts B S hS f)
    (hAR0 : HasRigSurjectiveOnPullbackCharts B S hS f ↔
      HasDvrFactorizationOnPullbackCharts B S hS f) :
    IsRigSurjective B S hS f ↔ HasAnnihilatedKerPowOnPullbackCharts B S hS f :=
  (hAQV.trans hAR0).trans
    (hasAnnihilatedKerPow_iff_hasDvrFactorization B S hS f hAQI).symm

/-! ### The same statements with only the surjectivity clause of Stacks 0AQI -/

/-- The condition of `AlgebraicGeometry.FormalSpace.HasAnnihilatedKerPowOnPullbackCharts` with
the conclusion only that the chart homomorphism is surjective. This is the single clause of
Stacks 0AQI which the proof of Stacks 0GD5 consumes. -/
abbrev HasSurjectiveOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (_hV : IsAffineFormalAlgebraicSpace B S hS V) (b : V ⟶ Y)
    (_hb : IsRepresentableEtale B S hS b) (U : FppfSheaf B S hS) (a : U ⟶ X) (t : U ⟶ V),
    IsPullback a t f b → ∀ (A C : Type u)
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [IsNoetherianRing A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
        [IsNoetherianRing C],
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
        (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (g : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv → Function.Surjective g.toRingHom

/-- The chart condition of Stacks 0AQI implies its surjectivity clause, so every statement
taking `AlgebraicGeometry.FormalSpace.HasSurjectiveOnPullbackCharts` applies wherever
`AlgebraicGeometry.FormalSpace.HasAdicQuotientOnPullbackCharts` is available. -/
theorem hasSurjectiveOnPullbackCharts_of_hasAdicQuotient {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hAQI : HasAdicQuotientOnPullbackCharts B S hS f) :
    HasSurjectiveOnPullbackCharts B S hS f :=
  fun V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg =>
    (hAQI V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg).1

/-- The algebraic heart of Stacks 0GD5 transported to the charts over `f`, needing of
Stacks 0AQI only its surjectivity clause: condition (2) of Stacks 0GD5 holds exactly when the
kernel of each chart homomorphism is killed at every discrete valuation point of the chart
ring. -/
theorem hasAnnihilatedKerPow_iff_hasDvrFactorization_of_hasSurjective
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hsurj : HasSurjectiveOnPullbackCharts B S hS f) :
    HasAnnihilatedKerPowOnPullbackCharts B S hS f ↔
      HasDvrFactorizationOnPullbackCharts B S hS f := by
  constructor
  · exact hasDvrFactorization_of_hasAnnihilatedKerPow B S hS f
  · intro h V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
    exact ⟨hsurj V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg,
      Rig.exists_mul_pow_eq_bot_of_leKerAtDvrPoints hAdicA
        (h V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg)⟩

end AlgebraicGeometry.FormalSpace

end
