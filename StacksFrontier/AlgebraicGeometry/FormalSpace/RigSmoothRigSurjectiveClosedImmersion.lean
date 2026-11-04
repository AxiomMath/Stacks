module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersion

/-!
# Rig-smooth rig-surjective closed immersions

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a closed immersion
of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GD6** says that the following
three conditions are equivalent:

1. `f` is rig-smooth and rig-surjective,
2. `f` is rig-étale and rig-surjective, and
3. for every affine formal algebraic space `V` and every morphism `V ⟶ Y` which is
   representable by algebraic spaces and étale the morphism `X ×_Y V ⟶ V` corresponds to a
   surjective morphism `B → A` in `WAdm^{Noeth}` whose kernel `J` has the following property:
   `I * J = 0` for some ideal of definition `I` of `B`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAnnihilatedKerOnPullbackCharts` — condition (3).

## Main results

* `Rig.pow_mul_eq_bot_of_mul_pow_eq_bot`: the elementary ring input of the source's proof, that
  `I * J ^ n = 0` together with `I * J ≤ J ^ 2` forces `I ^ n * J = 0`.
* `Rig.exists_idealOfDefinition_mul_eq_bot`: the previous lemma with the two ideals of
  definition supplied by Stacks 0GD4 and Stacks 0GD5 reconciled into one.
* `AlgebraicGeometry.FormalSpace.isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion`:
  **Stacks 0GD6**, all three conditions and every implication between them, carrying the four
  hypotheses which Stacks 0GD4 and Stacks 0GD5 already carry in this library — see below.

## Implementation notes

Condition (3) is quantified exactly as condition (3) of Stacks 0GD4
(`AlgebraicGeometry.FormalSpace.HasAnnihilatedConormalOnPullbackCharts`) and condition (2) of
Stacks 0GD5 (`AlgebraicGeometry.FormalSpace.HasAnnihilatedKerPowOnPullbackCharts`) are: over a
chart `V ⟶ Y` of the target, a fibre product of `f` along it, adic Noetherian presenting rings
`A` of `V` and `C` of the fibre product, and a continuous homomorphism `g : A ⟶ C` inducing the
chart map. The source's `B → A` is the present `g : A ⟶ C`, so `J` is `RingHom.ker g.toRingHom`
and `IJ = 0` is `I * RingHom.ker g.toRingHom = ⊥`, with the ideal of definition existentially
quantified as in the source's "for some ideal of definition `I`".

The source calls this lemma "a trivial combination" of Stacks 0GD4 and Stacks 0GD5 together
with the ring-theoretic observation whose proof it omits. Both halves are carried out here.

* The easy direction is (3) ⟹ (1) and (3) ⟹ (2). From `I * J = ⊥` one reads off both
  `I * J ≤ J ^ 2`, which is condition (3) of Stacks 0GD4, and `I * J ^ 1 = ⊥`, which is
  condition (2) of Stacks 0GD5; so Stacks 0GD4 gives rig-smoothness and rig-étaleness and
  Stacks 0GD5 gives rig-surjectivity.
* The other direction needs the omitted observation. Rig-smoothness gives, through Stacks 0GD4,
  an ideal of definition `K` with `K * J ≤ J ^ 2`, and rig-surjectivity gives, through
  Stacks 0GD5, an ideal of definition `I'` and an `n ≥ 1` with `I' * J ^ n = ⊥`. These need not
  be the same ideal; since `A` is adic, a high enough power `M = I₀ ^ N` of the ideal `I₀`
  defining its topology lies inside both, and then `M * J ≤ J ^ 2` and `M * J ^ n = ⊥`.
  `Rig.pow_mul_eq_bot_of_mul_pow_eq_bot` turns these into `M ^ n * J = ⊥`, and `M ^ n` is the
  positive power `I₀ ^ (N * n)`, hence again an ideal of definition because `A` is Noetherian.
  The ring lemma itself is the induction `I ^ k * J ≤ J ^ (k + 1)`, whose step is
  `I ^ (k + 1) * J = I ^ k * (I * J) ≤ I ^ k * J ^ 2 = (I ^ k * J) * J ≤ J ^ (k + 2)`;
  taking `k = n - 1` and multiplying once more by `I` lands inside `I * J ^ n = ⊥`.

The four hypotheses carried are exactly those which the library's Stacks 0GD4 and Stacks 0GD5
carry; nothing new is assumed, and no hypothesis is an implication of this lemma.

* `hAQI` is **Stacks 0AQI** in the chart form of Stacks 0GD4,
  `AlgebraicGeometry.FormalSpace.HasAdicQuotientOnPullbackCharts`: the chart homomorphism is a
  surjection of `WAdm^{Noeth}` which is adic of topologically finite type. What the library
  carries of Stacks 0AQI is the countably indexed case, unconditionally; the charts here are
  Noetherian rather than countably indexed, so it does not apply.
* `hGCZ` is **Stacks 0GCZ** read as the proof of Stacks 0GD4 reads it: rig-étaleness of `f`
  need only be checked on the ring maps appearing in condition (3).
* `hAQV` is the equivalence of rig-surjectivity of `f` with rig-surjectivity of its chart base
  changes, **Stacks 0AQS** forwards and **Stacks 0AQV** backwards. As the module of
  Stacks 0GD5 records, it cannot be discharged because Tag 0AJG — `IsEtaleULift` implies
  `IsLocallyOfFiniteTypeULift` — has no carrier in this library.
* `hAR0` is **Stacks 0AR0** for the chart maps, read through the full faithfulness of `Spf`
  (**Stacks 0AN0**). As the module of Stacks 0GD5 records, it cannot be discharged because the
  substantial direction of Stacks 0AR0 rests on the existence half of Tag 0AQD, whose carriers
  supply uniqueness only.

## References

* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
* [Stacks Project, Tag 0AQV](https://stacks.math.columbia.edu/tag/0AQV)
* [Stacks Project, Tag 0AR0](https://stacks.math.columbia.edu/tag/0AR0)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GD4](https://stacks.math.columbia.edu/tag/0GD4)
* [Stacks Project, Tag 0GD5](https://stacks.math.columbia.edu/tag/0GD5)
* [Stacks Project, Tag 0GD6](https://stacks.math.columbia.edu/tag/0GD6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Rig

/-- Powers of `I` push `J` into the corresponding power of `J` once `I * J ≤ J ^ 2`: the step
is `I ^ (k + 1) * J = I ^ k * (I * J) ≤ I ^ k * J ^ 2 = (I ^ k * J) * J ≤ J ^ (k + 2)`. -/
private theorem pow_mul_le_pow_succ {R : Type u} [CommRing R] {I J : Ideal R}
    (hsq : I * J ≤ J ^ 2) (k : ℕ) : I ^ k * J ≤ J ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc I ^ (k + 1) * J = I ^ k * (I * J) := by rw [pow_succ, Ideal.mul_assoc]
      _ ≤ I ^ k * J ^ 2 := Ideal.mul_mono_right hsq
      _ = I ^ k * J * J := by rw [pow_two, Ideal.mul_assoc]
      _ ≤ J ^ (k + 1) * J := Ideal.mul_mono_left ih
      _ = J ^ (k + 1 + 1) := (pow_succ J (k + 1)).symm

/-- **The ring-theoretic observation whose proof Stacks 0GD6 omits.** If an ideal `I` of a
commutative ring annihilates a positive power `J ^ n` of an ideal `J` and in addition
`I * J ≤ J ^ 2` — that is, `I` annihilates the conormal module `J / J ^ 2` — then `I ^ n`
annihilates `J` itself. -/
theorem pow_mul_eq_bot_of_mul_pow_eq_bot {R : Type u} [CommRing R] {I J : Ideal R} {n : ℕ}
    (hn : n ≠ 0) (hpow : I * J ^ n = ⊥) (hsq : I * J ≤ J ^ 2) : I ^ n * J = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  refine le_antisymm ?_ bot_le
  calc I ^ (m + 1) * J = I * (I ^ m * J) := by
        rw [pow_succ, mul_comm (I ^ m) I, Ideal.mul_assoc]
    _ ≤ I * J ^ (m + 1) := Ideal.mul_mono_right (pow_mul_le_pow_succ hsq m)
    _ = ⊥ := hpow

/-- **The algebraic content of Stacks 0GD6.** Let `A` be a Noetherian adic topological ring and
`J` an ideal. Suppose some ideal of definition annihilates the conormal module `J / J ^ 2`, as
Stacks 0GD4 provides for a rig-smooth closed immersion, and some ideal of definition annihilates
a positive power of `J`, as Stacks 0GD5 provides for a rig-surjective one. Then some ideal of
definition annihilates `J` itself.

The two given ideals of definition need not agree, so both are first replaced by a common
high power of the ideal defining the topology of `A`; the conclusion is then
`Rig.pow_mul_eq_bot_of_mul_pow_eq_bot`, whose output power is again an ideal of definition. -/
theorem exists_idealOfDefinition_mul_eq_bot {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) {J : Ideal A}
    (hconormal : ∃ K : Ideal A, TopologicalRing.IsIdealOfDefinition K ∧ K * J ≤ J ^ 2)
    (hker : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
      ∃ n : ℕ, n ≠ 0 ∧ I * J ^ n = ⊥) :
    ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I * J = ⊥ := by
  obtain ⟨⟨I₀, hI₀def, hI₀adic⟩, -, -⟩ := hA
  obtain ⟨K, hK, hKsq⟩ := hconormal
  obtain ⟨I', hI', n, hn, hI'pow⟩ := hker
  obtain ⟨p, hp, -⟩ := hI₀def.exists_pow_le_and_pow_le hK
  obtain ⟨q, hq, -⟩ := hI₀def.exists_pow_le_and_pow_le hI'
  set N : ℕ := p + q + 1 with hN
  have hNK : I₀ ^ N ≤ K := (Ideal.pow_le_pow_right (by omega)).trans hp
  have hNI' : I₀ ^ N ≤ I' := (Ideal.pow_le_pow_right (by omega)).trans hq
  have hsq : I₀ ^ N * J ≤ J ^ 2 := (Ideal.mul_mono_left hNK).trans hKsq
  have hpow : I₀ ^ N * J ^ n = ⊥ :=
    le_antisymm (hI'pow.le.trans' (Ideal.mul_mono_left hNI')) bot_le
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨I₀ ^ (N * (m + 1)),
    AlgebraicGeometry.FormalSpace.isIdealOfDefinition_pow_succ hI₀adic (N * m + (p + q)), ?_⟩
  rw [pow_mul]
  exact pow_mul_eq_bot_of_mul_pow_eq_bot hn hpow hsq

end Rig

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GD6, condition (3).** For every affine formal algebraic space `V`, every
representable étale `V ⟶ Y` and every fibre product of `f` along it, the induced morphism of
presenting rings of `WAdm^{Noeth}` is surjective and some ideal of definition of the source
annihilates its kernel `J`. -/
abbrev HasAnnihilatedKerOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
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
              I * RingHom.ker g.toRingHom = ⊥

/-- Condition (3) of Stacks 0GD6 implies condition (3) of Stacks 0GD4: an ideal of definition
annihilating the kernel `J` annihilates the conormal module `J / J ^ 2` a fortiori. -/
theorem hasAnnihilatedConormal_of_hasAnnihilatedKer {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : HasAnnihilatedKerOnPullbackCharts B S hS f) :
    HasAnnihilatedConormalOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  obtain ⟨hsurj, I, hI, hmul⟩ := h V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
  exact ⟨hsurj, I, hI, hmul.le.trans bot_le⟩

/-- Condition (3) of Stacks 0GD6 implies condition (2) of Stacks 0GD5: an ideal of definition
annihilating the kernel `J` annihilates the positive power `J ^ 1`. -/
theorem hasAnnihilatedKerPow_of_hasAnnihilatedKer {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : HasAnnihilatedKerOnPullbackCharts B S hS f) :
    HasAnnihilatedKerPowOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  obtain ⟨hsurj, I, hI, hmul⟩ := h V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
  exact ⟨hsurj, I, hI, 1, one_ne_zero, by simpa using hmul⟩

/-- Conditions (3) of Stacks 0GD4 and (2) of Stacks 0GD5 together imply condition (3) of
Stacks 0GD6. This is the omitted ring-theoretic step of the source's proof, applied chart by
chart: the ideal of definition annihilating `J / J ^ 2` and the one annihilating a power of `J`
are reconciled by `Rig.exists_idealOfDefinition_mul_eq_bot`. -/
theorem hasAnnihilatedKer_of_hasAnnihilatedConormal_of_hasAnnihilatedKerPow
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hconormal : HasAnnihilatedConormalOnPullbackCharts B S hS f)
    (hker : HasAnnihilatedKerPowOnPullbackCharts B S hS f) :
    HasAnnihilatedKerOnPullbackCharts B S hS f := by
  intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
  obtain ⟨hsurj, hsq⟩ :=
    hconormal V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
  obtain ⟨-, hpow⟩ := hker V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
  exact ⟨hsurj, Rig.exists_idealOfDefinition_mul_eq_bot hAdicA hsq hpow⟩

/-- **Stacks 0GD6.** Let `f : X ⟶ Y` be a closed immersion of locally Noetherian formal
algebraic spaces over `S`. Then the following are equivalent: (1) `f` is rig-smooth and
rig-surjective; (2) `f` is rig-étale and rig-surjective; (3) on every affine representable étale
chart `V ⟶ Y` of the target the fibre product `X ×_Y V ⟶ V` is given by a surjection of
`WAdm^{Noeth}` whose kernel is annihilated by some ideal of definition of the source.

The equivalence of the two rigidity notions is Stacks 0GD4, the identification of
rig-surjectivity with the annihilation of a power of the kernel is Stacks 0GD5, and the
passage from "a power of `J` is annihilated and `J / J ^ 2` is annihilated" to "`J` is
annihilated" is `Rig.exists_idealOfDefinition_mul_eq_bot`, the ring-theoretic step whose proof
the source omits.

The hypotheses `hAQI`, `hGCZ`, `hAQV` and `hAR0` are precisely the ones the library's
Stacks 0GD4 and Stacks 0GD5 carry: Stacks 0AQI in chart form, Stacks 0GCZ as the proof of
Stacks 0GD4 uses it, the equivalence of rig-surjectivity of `f` with rig-surjectivity of its
chart base changes (Stacks 0AQS forwards, Stacks 0AQV backwards), and Stacks 0AR0 for the chart
maps read through Stacks 0AN0. -/
@[stacks 0GD6 "all three conditions and every implication between them, carrying exactly the \
four hypotheses which this library's Stacks 0GD4 and Stacks 0GD5 already carry and nothing \
more: Stacks 0AQI in the chart form of Stacks 0GD4, that the chart homomorphism is a surjection \
of WAdm^Noeth which is adic of topologically finite type (hAQI), whose library carrier covers \
only the countably indexed case, which the Noetherian charts here are not; Stacks \
0GCZ read as the proof of Stacks 0GD4 reads it, that rig-etaleness of f need only be checked \
on the ring maps appearing in condition (3) (hGCZ); the equivalence of rig-surjectivity of f \
with rig-surjectivity of its chart base changes, Stacks 0AQS forwards and Stacks 0AQV \
backwards (hAQV), undischargeable because Tag 0AJG, IsEtaleULift implies \
IsLocallyOfFiniteTypeULift, has no carrier in this library; and Stacks 0AR0 for the chart maps \
read through the full faithfulness of Spf of Stacks 0AN0 (hAR0), undischargeable because its \
substantial direction rests on the EXISTENCE half of Tag 0AQD, whose carriers supply \
uniqueness only. No carried hypothesis is an implication of this lemma. The combination the \
source calls trivial is proved, including the ring-theoretic observation the source omits: \
I * J ^ n = 0 together with I * J <= J ^ 2 forces I ^ n * J = 0"]
theorem isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hf : IsClosedImmersion B S hS f)
    (hAQI : HasAdicQuotientOnPullbackCharts B S hS f)
    (hGCZ : HasRigEtaleOnPullbackCharts B S hS f → IsRigEtale B S hS f)
    (hAQV : IsRigSurjective B S hS f ↔ HasRigSurjectiveOnPullbackCharts B S hS f)
    (hAR0 : HasRigSurjectiveOnPullbackCharts B S hS f ↔
      HasDvrFactorizationOnPullbackCharts B S hS f) :
    List.TFAE
      [IsRigSmooth B S hS f ∧ IsRigSurjective B S hS f,
        IsRigEtale B S hS f ∧ IsRigSurjective B S hS f,
        HasAnnihilatedKerOnPullbackCharts B S hS f] := by
  have h0GD4 : List.TFAE
      [IsRigSmooth B S hS f, IsRigEtale B S hS f,
        HasAnnihilatedConormalOnPullbackCharts B S hS f] :=
    isRigSmooth_tfae_of_isClosedImmersion B S hS f hX hY hf hAQI hGCZ
  have h0GD5 : IsRigSurjective B S hS f ↔ HasAnnihilatedKerPowOnPullbackCharts B S hS f :=
    isRigSurjective_iff_hasAnnihilatedKerPowOnPullbackCharts B S hS f hX hY hf hAQI hAQV hAR0
  tfae_have 2 → 1 := fun h => ⟨(h0GD4.out 2 1).mp h.1, h.2⟩
  tfae_have 1 → 3 := fun h =>
    hasAnnihilatedKer_of_hasAnnihilatedConormal_of_hasAnnihilatedKerPow B S hS f
      ((h0GD4.out 1 3).mp h.1) (h0GD5.mp h.2)
  tfae_have 3 → 2 := fun h =>
    ⟨(h0GD4.out 3 2).mp (hasAnnihilatedConormal_of_hasAnnihilatedKer B S hS f h),
      h0GD5.mpr (hasAnnihilatedKerPow_of_hasAnnihilatedKer B S hS f h)⟩
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
