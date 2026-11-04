module

public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersUniformDegree.Basic

/-!
# Stacks Tag 01VT: ampleness over an affine base, from named hypotheses

Stacks Tag 01VT says that for `f : X ⟶ S` of finite type with `S` **affine** and `L` an
invertible `𝒪_X`-module, six conditions are equivalent:

1. `L` is ample on `X`;
2. `L` is `f`-ample;
3. `L ^⊗ d` is `f`-very ample for some `d ≥ 1`;
4. `L ^⊗ d` is `f`-very ample for every `d ≫ 1`;
5. for some `d ≥ 1` there are `n ≥ 1` and an immersion `i : X ⟶ ℙⁿ_S` over `S` with
   `L ^⊗ d ≅ i^* 𝒪(1)`;
6. the same, for every `d ≫ 1`.

This file proves the equivalence of (1), (2), (5) and (6) from three named hypotheses. All six
conditions are proved with no named input as `Stacks.AmpleRelativeFiniteType.tfae_six`, which
carries the Stacks Tag 01VT attribute; none is attached here.

## The named hypotheses

* `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` is **Stacks Tag 01VS**: all
  sufficiently high tensor powers of an ample invertible module on a scheme locally of finite
  type over `S` are `𝒪(1)` pulled back along an immersion into `ℙⁿ_S`
  (`Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform_iff`). It drives (1) ⟹ (6).
* `Stacks.Tag01VT.TwistAmpleOverAffine` is the statement that, over an affine base, `𝒪(1)` is an
  invertible ample module on `ℙⁿ_S`. It drives (5) ⟹ (2). It is proved as
  `Stacks.ProjectiveSpace.twistAmpleOverAffine`.
* `Stacks.RelativeVeryAmple.AmplePullbackGap` is the Tag 0B3E premise on which
  `Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion` proves Stacks
  Tag 01VN, that relative ampleness is inherited along an immersion over the base.

## The route

The cycle is (1) ⟹ (6) ⟹ (5) ⟹ (2) ⟹ (1).

* **(1) ⟹ (6)** is Tag 01VS at the single situation `(X, S, f, L)`. Over an affine base no
  covering of `S` and no glueing (Stacks Tag 01VR, as in Tag 01VU) is needed.
* **(6) ⟹ (5)** is `Stacks.RelativeVeryAmple.exists_one_le_and_of_eventually`.
* **(5) ⟹ (2)** builds `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` at `P = ℙⁿ_S`,
  `M = 𝒪(1)` from the immersion of (5) and the relative ampleness of `𝒪(1)` given by
  `Stacks.Tag01VT.isRelativelyAmple_projectiveSpaceTwistingSheaf`, and then applies Tag 01VN in
  the form
  `Stacks.RelativeVeryAmple.isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule`.
* **(2) ⟹ (1)** and **(1) ⟹ (2)** are the two halves of
  `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`, **Stacks Tag 01VK, which is
  unconditional**.

## Main definitions

* `Stacks.Tag01VT.projectiveSpaceHom`: the structure morphism `ℙⁿ_S ⟶ S`, which is the morphism
  the clause "over `S`" of conditions (5) and (6) is written against.
* `Stacks.Tag01VT.TwistAmpleOverAffine`: `𝒪(1)` is invertible and ample on `ℙⁿ_S` for `S`
  affine.

## Main results

* `Stacks.Tag01VT.isRelativelyAmple_projectiveSpaceTwistingSheaf`: `𝒪(1)` is ample relative to
  `ℙⁿ_S ⟶ S`, from `Stacks.Tag01VT.TwistAmpleOverAffine` by Tag 01VK.
* `Stacks.Tag01VT.hasRelativeTwistImmersion_of_hasImmersionTwistOver`: an immersion into `ℙⁿ_S`
  over `S` is a `HasRelativeTwistImmersion` witness.
* `Stacks.Tag01VT.isRelativelyAmple_of_exists_hasImmersionTwistOver`: **(5) ⟹ (2)**.
* `Stacks.Tag01VT.eventually_hasImmersionTwistOver_of_isAmple`: **(1) ⟹ (6)**.
* `Stacks.Tag01VT.tfae`: **Stacks Tag 01VT**, conditions (1), (2), (5), (6).
* `Stacks.Tag01VT.tfae_tensorPowerModule`: the same over Tag 01CU's family of tensor powers.

## Implementation notes

**The two spellings of the module pullback.** Conditions (5) and (6) are stated with
`AlgebraicGeometry.Scheme.Modules.pullback`, as `Stacks.AmpleProjectiveImmersion` writes them,
while `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` uses
`RingedSpaceModuleAdjunction.modulePullback _.toLRSHom.toShHom`. The two are the same functor by
`rfl`, so `Stacks.Tag01VT.hasRelativeTwistImmersion_of_hasImmersionTwistOver` passes the
isomorphism of (5) straight through.

**No lower bound on `n`.** `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` writes
`∃ n : ℕ, ∃ i : X ⟶ ℙⁿ_S, …` with no `1 ≤ n`, so conditions 3 and 4 of `Stacks.Tag01VT.tfae`
admit `n = 0`, where `ℙ⁰_S ≅ S`. `Stacks.AmpleProjectiveImmersion.hasImmersionTwistOverPos_iff`
proves the two spellings of the clause equivalent, and
`Stacks.AmpleRelativeFiniteType.tfae_six_pos` states Tag 01VT with the source's `1 ≤ n`.

**The invertibility of `𝒪(1)` is part of the hypothesis, not an instance.**
`HasRelativeTwistImmersion` takes the invertibility of its module as an existentially bound datum,
so `Stacks.Tag01VT.TwistAmpleOverAffine` supplies it the same way; ampleness cannot be stated
without it.

**`tensorPowModule` is the primary family.** `Stacks.Ample.tensorPowModule` is the family
relative ampleness, Tag 01VS and Tag 01VN are all written over; Tag 01CU's family is
`Stacks.AmpleProjectiveImmersion.tensorPowerModule`. The two are isomorphic in every integer
degree by `Stacks.PowerFamilyBridge.tensorPowerModuleIso`, and
`Stacks.Tag01VT.tfae_tensorPowerModule` is the same theorem over the second family.

## References

* [EGA II, Theorem 4.6.3]
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 02NN](https://stacks.math.columbia.edu/tag/02NN)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Tag01VT

/-! ### The structure morphism of projective space over a base -/

/-- **The structure morphism `ℙⁿ_S ⟶ S`.** `AlgebraicGeometry.projectiveSpaceOver n S` is the
fibre product `S ×_{Spec ℤ} ℙⁿ_ℤ`, and its `CanonicallyOver` instance is the first projection;
this is the spelling the clause "over `S`" of
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` is written against. -/
abbrev projectiveSpaceHom (n : ℕ) (S : Scheme.{u}) : projectiveSpaceOver n S ⟶ S :=
  pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))

/-! ### Ampleness of `𝒪(1)` over an affine base as a named hypothesis -/

/-- **Ampleness of `𝒪(1)` over an affine base, as a named hypothesis**: on projective `n`-space
over an affine scheme, the hyperplane sheaf `𝒪(1)` is an invertible module and it is ample. It is
proved as `Stacks.ProjectiveSpace.twistAmpleOverAffine`. -/
def TwistAmpleOverAffine : Prop :=
  ∀ (n : ℕ) (S : Scheme.{u}) [IsAffine S],
    ∃ hM : IsInvertibleModule (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S),
      letI : IsInvertibleModule (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S) := hM
      IsAmple (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S)

/-- **`𝒪(1)` is ample relative to `ℙⁿ_S ⟶ S` over an affine base**, given
`Stacks.Tag01VT.TwistAmpleOverAffine`. -/
theorem isRelativelyAmple_projectiveSpaceTwistingSheaf (h02NN : TwistAmpleOverAffine.{u})
    (n : ℕ) (S : Scheme.{u}) [IsAffine S] :
    ∃ hM : IsInvertibleModule (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S),
      letI : IsInvertibleModule (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S) := hM
      Stacks.RelativeAmple.IsRelativelyAmple (projectiveSpaceHom n S)
        (projectiveSpaceTwistingSheaf n S) := by
  obtain ⟨hM, hample⟩ := h02NN n S
  exact ⟨hM, (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
    (projectiveSpaceHom n S) _).mpr hample⟩

/-! ### From an immersion into `ℙⁿ_S` to the hypothesis of Stacks Tag 01VN -/

/-- **An immersion into `ℙⁿ_S` over `S` carrying `𝒪(1)` to `M` witnesses
`Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` at `M`**, given
`Stacks.Tag01VT.TwistAmpleOverAffine`. -/
theorem hasRelativeTwistImmersion_of_hasImmersionTwistOver (h02NN : TwistAmpleOverAffine.{u})
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (M : X.Modules) [IsInvertibleModule X M]
    (h : HasImmersionTwistOver f M) :
    Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f M := by
  obtain ⟨n, i, hi, hover, ⟨e⟩⟩ := h
  obtain ⟨hM, hMample⟩ := isRelativelyAmple_projectiveSpaceTwistingSheaf h02NN n S
  exact ⟨projectiveSpaceOver n S, projectiveSpaceHom n S, projectiveSpaceTwistingSheaf n S, hM,
    i, hi, hover, hMample, ⟨e⟩⟩

/-! ### (5) ⟹ (2) -/

/-- **The implication (5) ⟹ (2) of Stacks Tag 01VT.** If some positive tensor power of `L` is
`𝒪(1)` pulled back along an immersion `X ⟶ ℙⁿ_S` over `S`, then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_exists_hasImmersionTwistOver
    (hgap : Stacks.RelativeVeryAmple.AmplePullbackGap.{u}) (h02NN : TwistAmpleOverAffine.{u})
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hwit⟩ := h
  exact isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule hgap f L hf
    ⟨d, hd, hasRelativeTwistImmersion_of_hasImmersionTwistOver h02NN f _ hwit⟩

/-! ### (1) ⟹ (6) -/

/-- **The implication (1) ⟹ (6) of Stacks Tag 01VT.** For `L` ample on `X` and `f` locally of
finite type, every sufficiently high tensor power of `L` is `𝒪(1)` pulled back along an immersion
`X ⟶ ℙⁿ_S` over `S`. This is Stacks Tag 01VS at the single situation `(X, S, f, L)`. -/
theorem eventually_hasImmersionTwistOver_of_isAmple
    (hgap01VS : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [hft : LocallyOfFiniteType f] (hL : IsAmple X L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)) := by
  obtain ⟨d₀, hd₀, hd⟩ := hgap01VS X S f L hL hft
  exact ⟨d₀, hd₀, fun d hdd => (hasImmersionTwist_iff f _).mp (hd d hdd)⟩

/-! ### Stacks Tag 01VT -/

/-- **Stacks Tag 01VT, conditions (1), (2), (5) and (6).** For `f : X ⟶ S` locally of finite type
and quasi-compact with `S` affine and `L` an invertible `𝒪_X`-module, the following are
equivalent:

1. `L` is ample on `X`;
2. `L` is ample relative to `f`;
3. (the source's (5)) some positive tensor power of `L` is `𝒪(1)` pulled back along an
   immersion `X ⟶ ℙⁿ_S` over `S`;
4. (the source's (6)) every sufficiently high tensor power of `L` is.

The source's conditions (3) and (4), relative very ampleness, are not in this list; all six are
`Stacks.AmpleRelativeFiniteType.tfae_six`. -/
theorem tfae (hgap : Stacks.RelativeVeryAmple.AmplePullbackGap.{u})
    (hgap01VS : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    (h02NN : TwistAmpleOverAffine.{u})
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] (hqc : QuasiCompact f) :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))] := by
  tfae_have 1 → 4 := fun hL => eventually_hasImmersionTwistOver_of_isAmple hgap01VS f L hL
  tfae_have 4 → 3 := fun ⟨d₀, _, h⟩ =>
    Stacks.RelativeVeryAmple.exists_one_le_and_of_eventually ⟨d₀, h⟩
  tfae_have 3 → 2 := isRelativelyAmple_of_exists_hasImmersionTwistOver hgap h02NN f L hqc
  tfae_have 2 → 1 := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp
  tfae_have 1 → 2 := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mpr
  tfae_finish

/-- **Stacks Tag 01VT over Tag 01CU's family of tensor powers**: `Stacks.Tag01VT.tfae` with
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` in place of `Stacks.Ample.tensorPowModule`
in conditions 3 and 4. -/
theorem tfae_tensorPowerModule (hgap : Stacks.RelativeVeryAmple.AmplePullbackGap.{u})
    (hgap01VS : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    (h02NN : TwistAmpleOverAffine.{u})
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] (hqc : QuasiCompact f) :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowerModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowerModule X L (d : ℤ))] := by
  have hcongr : ∀ d : ℕ, HasImmersionTwistOver f (tensorPowerModule X L (d : ℤ)) ↔
      HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)) := fun d =>
    Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr f
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso X L (d : ℤ))
  have h := tfae hgap hgap01VS h02NN f L hqc
  have h3 : (∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowerModule X L (d : ℤ))) ↔
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)) :=
    exists_congr fun d => and_congr_right fun _ => hcongr d
  have h4 : (∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowerModule X L (d : ℤ))) ↔
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)) :=
    exists_congr fun _ => and_congr_right fun _ =>
      forall_congr' fun d => imp_congr_right fun _ => hcongr d
  tfae_have 1 → 2 := (h.out 1 2).mp
  tfae_have 2 → 3 := fun hr => h3.mpr ((h.out 2 3).mp hr)
  tfae_have 3 → 4 := fun hc => h4.mpr ((h.out 3 4).mp (h3.mp hc))
  tfae_have 4 → 1 := fun he => (h.out 4 1).mp (h4.mp he)
  tfae_finish

end Stacks.Tag01VT

end
