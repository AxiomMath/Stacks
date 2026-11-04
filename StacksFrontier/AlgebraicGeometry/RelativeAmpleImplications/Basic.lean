module

public import StacksFrontier.AlgebraicGeometry.AmpleAffineBaseTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers

/-!
# Stacks Tags 01VN and 01VU: the Tag 0B3E premise is gone

Stacks Tag 01VN says a relatively very ample invertible module on a quasi-compact morphism is
relatively ample; Stacks Tag 01VU compares relative ampleness of `L` with relative very ampleness
of its high tensor powers. The implications of both that end in relative ampleness were proved in
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean` modulo one named hypothesis,
`Stacks.RelativeVeryAmple.AmplePullbackGap`, which is Stacks Tag 0B3E.

**That hypothesis is now a theorem, and this file removes it from the statements that still carry
it.** `Stacks.SectionExtension.amplePullbackGap`
(`../SectionExtension/AmpleConsumers.lean:174`) proves `AmplePullbackGap` outright, because the
last of the three premises `Stacks.RelativeVeryAmple.amplePullbackGap_of_premises` reduces it to —
clause (1) ⟹ (3) of Stacks Tag 01Q3 — is `Stacks.SectionExtension.isBasisNonvanishing_of_isAmple`
(`:112`), unconditional for an arbitrary invertible module.

## Two absence claims this file measures false

* `StacksFrontier/AlgebraicGeometry/NonvanishingPullback/Basic.lean` says of that last premise: "One
  premise remains, and it is not touched here: `hbasis`, **Stacks Tag 01Q3, (1) ⟹ (3)** [...]
  **Nothing in either tree provides it**: `AmpleTheory/Basic.lean` has it only for the structure
  sheaf and for a module with a nowhere-vanishing global basis in every tensor degree." Both
  sentences are false at HEAD. `Stacks.SectionExtension.isBasisNonvanishing_of_isAmple` has it for
  every ample invertible module on every scheme, with no premise, by way of
  `Stacks.SectionExtension.isSectionRatio_of_isAmple` — the ample case of Stacks Tag 01PW. The
  file's own reduction to that single premise is what makes the present file three lines long.
* `StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean:38-49` calls
  `AmplePullbackGap` "the single named input that is missing" and "the one input the argument below
  needs and the repository does not have". Also false at HEAD, for the same reason.

Neither docstring is edited here; both belong to other files.

## Main results

* `Stacks.RelativeAmpleImplications.isRelativelyAmple_of_exists_hasRelativeTwistImmersion`:
  **the implication (2) ⟹ (1) of Stacks Tag 01VU, with no premise.**
* `Stacks.RelativeAmpleImplications.isRelativelyAmple_of_eventually_hasRelativeTwistImmersion`:
  **the implication (3) ⟹ (1) of Stacks Tag 01VU, with no premise**, through (3) ⟹ (2).
* `Stacks.RelativeAmpleImplications.hasRelativeTwistImmersion_congr`: the hypothesis of Tag 01VN
  depends only on the isomorphism class of the module. New; nothing in the tree had it.
* `Stacks.RelativeAmpleImplications.isRelativelyAmple_of_exists_hasImmersionTwistOver`: the
  implication (5) ⟹ (2) of Stacks Tag 01VT on Stacks Tag 02NN alone.
* `Stacks.RelativeAmpleImplications.tfae` and `tfae_tensorPowerModule`: **Stacks Tag 01VT on two
  named inputs instead of three** — Stacks Tag 01VS and Stacks Tag 02NN.

The content of Tag 01VN itself needs nothing added: it is already unconditional in the tree, as
`Stacks.SectionExtension.isRelativelyAmple_of_relativeTwistImmersion`
(`../SectionExtension/AmpleConsumers.lean:180`). It is restated here only inside the two 01VU
implications, which are what the statement of Tag 01VU is written with.

## Why no Stacks attribute is attached, for either tag

Both tags are proved elsewhere, at Tag 01VM's relative very ampleness
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`: Tag 01VN is
`Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple`, and Tag 01VU is
`Stacks.VeryAmplePowersQuasiCompactBase.tfae`, with (1) ⟹ (3) as
`Stacks.VeryAmplePowersQuasiCompactBase.eventuallyVeryAmplePower_of_isRelativelyAmple`.

The hypothesis proved here, `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion`, is not Tag
01VM's `IsRelativelyVeryAmple`: it replaces `𝐏(E)` by an arbitrary `S`-scheme carrying a relatively
ample invertible module, which is the only property of `𝐏(E)` the source's argument uses. It is a
predicate the statements of these tags do not mention, so neither label is attached here.

## Implementation notes

**Ampleness is `Stacks.Ample.IsAmple` of
`StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean:245`**, deliberately: it is the one of the
two declarations carrying Stacks Tag 01PS that `Stacks.RelativeAmple.IsRelativelyAmple`,
`Stacks.RelativeVeryAmple.AmplePullbackGap` and `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`
are all written over. The other is `AlgebraicGeometry.Scheme.Modules.IsAmple`
(`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean:100`), and the two are not bridged anywhere.

**The transport lemma needs no invertibility on the target to be useful, but it does need one to be
stated.** `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` takes the invertibility of its
module as an instance binder, and its body does not use it — the module occurs only in
`Nonempty (L ≅ i^* M)` — so the transport below is the identity on every component but the final
isomorphism.

**The two 01VU implications are NOT restated over Stacks Tag 01CU's family of tensor powers**, and
the reason is an instance and not a choice. Unlike
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`, which takes no invertibility argument and
so can be moved across `Stacks.PowerFamilyBridge.tensorPowerModuleIso` by
`Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr` with nothing supplied,
`HasRelativeTwistImmersion` cannot even be *written* at
`Stacks.AmpleProjectiveImmersion.tensorPowerModule X L d` without a term of
`Stacks.Ample.IsInvertibleModule X (tensorPowerModule X L d)`, and there is none: `exact?`
closes no such goal, and the general transport of invertibility along an isomorphism that would
give it — `Stacks.SheafOfModules.Invertible.isInvertible_of_iso`
(`StacksFrontier/AlgebraicGeometry/Ample/DescentStep.lean:221`) — is stated over
`SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)` rather than
over the `def` `X.Modules`, which is the shape that does not transfer. The missing declaration is
therefore exactly `Stacks.Ample.isInvertibleModule_of_iso`, at the scheme spelling. With it and
`Stacks.RelativeAmpleImplications.hasRelativeTwistImmersion_congr` the restatement is two lines.
`Stacks.RelativeAmpleImplications.tfae_tensorPowerModule` does reach Tag 01CU's family, because the
conditions it moves are the `HasImmersionTwistOver` ones.

## References

* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [EGA II, Proposition 4.6.2]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.RelativeAmpleImplications

/-! ### Stacks Tag 0B3E is no longer a hypothesis -/

/-- **The implication (2) ⟹ (1) of Stacks Tag 01VU, with no premise.** If some positive tensor
power of `L` admits an immersion over the base onto a relatively ample invertible module — in
particular, if it is relatively very ample — then `L` is ample relative to `f`.

`Stacks.RelativeVeryAmple.isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule`
proves this on the named Stacks Tag 0B3E premise
`Stacks.RelativeVeryAmple.AmplePullbackGap`, and that premise is
`Stacks.SectionExtension.amplePullbackGap`. Quasi-compactness of `f` is the only part of Tag
01VU's finite-type hypothesis that is used. -/
theorem isRelativelyAmple_of_exists_hasRelativeTwistImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧
      Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeVeryAmple.isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule
    Stacks.SectionExtension.amplePullbackGap f L hf h

/-- **The implication (3) ⟹ (1) of Stacks Tag 01VU, with no premise**, through (3) ⟹ (2): if all
sufficiently high tensor powers of `L` admit an immersion over the base onto a relatively ample
invertible module, then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_eventually_hasRelativeTwistImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeVeryAmple.isRelativelyAmple_of_eventually_hasRelativeTwistImmersion_tensorPowModule
    Stacks.SectionExtension.amplePullbackGap f L hf h

/-! ### The hypothesis of Stacks Tag 01VN is an invariant of the isomorphism class -/

/-- **The hypothesis of Stacks Tag 01VN depends only on the isomorphism class of the module.**
Both halves compose the given isomorphism with the recorded one, leaving the scheme, the
morphisms, the immersion and the relative ampleness untouched; the invertibility binders of
`Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` are not used by its body.

This is the analogue for Tag 01VN's hypothesis of
`Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr` for Tag 01VS's conclusion, and of
`Stacks.RelativeVeryAmple.isRelativelyAmple_congr` for Tag 01VH's. Nothing in the tree had it. -/
theorem hasRelativeTwistImmersion_congr {X S : Scheme.{u}} (f : X ⟶ S) (M M' : X.Modules)
    [IsInvertibleModule X M] [IsInvertibleModule X M'] (e : M ≅ M') :
    Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f M ↔
      Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f M' := by
  have key {A B : X.Modules} [IsInvertibleModule X A] [IsInvertibleModule X B] (e' : B ≅ A) :
      Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f A →
        Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f B :=
    fun ⟨P, p, N, hN, i, him, hover, hample, ⟨j⟩⟩ =>
      ⟨P, p, N, hN, i, him, hover, hample, ⟨e' ≪≫ j⟩⟩
  exact ⟨key e.symm, key e⟩

/-! ### The dividend for Stacks Tag 01VT: three named inputs become two -/

/-- **The implication (5) ⟹ (2) of Stacks Tag 01VT, on Stacks Tag 02NN alone.** If some positive
tensor power of `L` is `𝒪(1)` pulled back along an immersion `X ⟶ ℙⁿ_S` over an affine base `S`,
then `L` is ample relative to `f`.

`Stacks.Tag01VT.isRelativelyAmple_of_exists_hasImmersionTwistOver` carries both Stacks
Tag 02NN and the Stacks Tag 0B3E premise; only the former is still a hypothesis. -/
theorem isRelativelyAmple_of_exists_hasImmersionTwistOver
    (h02NN : Stacks.Tag01VT.TwistAmpleOverAffine.{u}) {X S : Scheme.{u}} [IsAffine S]
      (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.Tag01VT.isRelativelyAmple_of_exists_hasImmersionTwistOver
    Stacks.SectionExtension.amplePullbackGap h02NN f L hf h

/-- **Stacks Tag 01VT, conditions (1), (2), (5) and (6), on two named inputs instead of three.**
For `f : X ⟶ S` locally of finite type and quasi-compact with `S` affine and `L` an invertible
`𝒪_X`-module, ampleness of `L`, relative ampleness of `L`, and the existence of an immersion into
`ℙⁿ_S` over `S` carrying `𝒪(1)` to one positive — equivalently to every sufficiently high — tensor
power of `L` are equivalent.

The two inputs left are Stacks Tag 01VS, in the form
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`, and Stacks Tag 02NN, in the form
`Stacks.Tag01VT.TwistAmpleOverAffine`. The third, Stacks Tag 0B3E, is discharged. -/
theorem tfae (hgap01VS : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    (h02NN : Stacks.Tag01VT.TwistAmpleOverAffine.{u}) {X S : Scheme.{u}} [IsAffine S]
      (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] (hqc : QuasiCompact f) :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))] :=
  Stacks.Tag01VT.tfae Stacks.SectionExtension.amplePullbackGap hgap01VS h02NN f L hqc

/-- **Stacks Tag 01VT over Stacks Tag 01CU's family of tensor powers, on two named inputs instead
of three.** This is the family the statement of Tag 01VT writes its conditions (5) and (6) with;
`Stacks.PowerFamilyBridge.tensorPowerModuleIso` identifies the two families in every integer
degree, so this is the same theorem as `Stacks.RelativeAmpleImplications.tfae`. -/
theorem tfae_tensorPowerModule
  (hgap01VS : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    (h02NN : Stacks.Tag01VT.TwistAmpleOverAffine.{u}) {X S : Scheme.{u}} [IsAffine S]
      (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] (hqc : QuasiCompact f) :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowerModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowerModule X L (d : ℤ))] :=
  Stacks.Tag01VT.tfae_tensorPowerModule Stacks.SectionExtension.amplePullbackGap
    hgap01VS h02NN
    f L hqc

end Stacks.RelativeAmpleImplications

end
