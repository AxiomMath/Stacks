module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# Stacks Tag 01VU, the implication (1) ⟹ (3): very ample powers over a finite affine cover

Stacks Tag 01VU says that for `f : X ⟶ S` of finite type with `S` quasi-compact and `L` an
invertible `𝒪_X`-module, the three conditions

1. `L` is `f`-ample,
2. `L ^⊗ d` is `f`-very ample for some `d ≥ 1`,
3. `L ^⊗ d` is `f`-very ample for every sufficiently large `d`,

are equivalent. The source proves (3) ⟹ (2) trivially, (2) ⟹ (1) by Tag 01VN, and (1) ⟹ (3) by
choosing a finite affine open covering `S = V₁ ∪ ⋯ ∪ V_m`, applying Tag 01VT to each
`f⁻¹(Vᵢ) ⟶ Vᵢ` to obtain a single `d₀` that works for all of them, and then glueing with Tag
01VR.

The two implications that end in (1) are proved in
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean`
(`Stacks.RelativeVeryAmple.isRelativelyAmple_of_exists_hasRelativeTwistImmersion_tensorPowModule`
and `isRelativelyAmple_of_eventually_hasRelativeTwistImmersion_tensorPowModule`), with the
projective bundle generalised away and Stacks Tag 0B3E taken as the named hypothesis
`Stacks.RelativeVeryAmple.AmplePullbackGap`. **This file does the first two steps of the source's
(1) ⟹ (3)**: the finite affine covering of the base, and the single uniform degree bound on it.

## Why the conclusion here is `ℙⁿ`, and why that is not a weakening

Relative very ampleness, Stacks Tag 01VM, quantifies over the projective bundle `𝐏(E)` of a
quasi-coherent `𝒪_S`-module. This file states its conclusion with projective space instead, and
Tag 01VU itself, with `𝐏(E)`, is proved elsewhere (see "Where Tag 01VU is"). Writing *some*
weaker surrogate would have been worthless: the natural weak one,
`Stacks.RelativeVeryAmple.HasRelativeTwistImmersion`, is satisfied by `P = X`, `M = L ^⊗ d`,
`i = 𝟙` as soon as `L ^⊗ d` is relatively ample
(`Stacks.RelativeVeryAmple.hasRelativeTwistImmersion_self`), so (1) ⟹ (3) in that surrogate is
a triviality and proves nothing.

The conclusion used here goes the other way. It is
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`: an immersion into *projective space*
`ℙⁿ_V` over the base, carrying `𝒪(1)` to the module. Over a base `V` this is **stronger** than
relative very ampleness over `V` — it is the case `E = 𝒪_V^{n+1}` of Tag 01VM — and it is exactly
clause (5)/(6) of Tag 01VT, which is the clause the source's proof of (1) ⟹ (3) actually produces
before quoting "projective space is a projective bundle". So the implication proved below implies
the one Tag 01VU wants, degree for degree and open for open; nothing is weakened, and the
conclusion is not satisfiable by an identity immersion.

## The one input, and that it is exactly Stacks Tag 01VS

`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` is
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` — the content of Stacks Tag 01VS, the only
thing that tag still owes after `StacksFrontier/AlgebraicGeometry/AmpleProjectiveImmersion/Basic.lean`
discharges everything formal in it — taken at every scheme, every morphism and every invertible
module rather than at one. `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform_iff`
proves, by elaboration rather than by prose, that it is Tag 01VS verbatim at every situation and
nothing more. It is stated as a hypothesis here, and it is discharged with no hypothesis by
`Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`
(`StacksFrontier/AlgebraicGeometry/ImmersionTwistGapUniform.lean`).

## Main definitions

* `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`: **Stacks Tag 01VS at every
  situation**, the single input of this file.

## Main results

* `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform_iff`: the input is Tag 01VS
  verbatim, at every situation, and nothing more.
* `Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr`: the conclusion of Tag 01VS at
  one degree depends only on the isomorphism class of the module.
* `Stacks.VeryAmplePowersUniformDegree.eventually_hasImmersionTwistOver_restrict`: **the local
  step, the content of Stacks Tag 01VT's (2) ⟹ (6) at one affine open of the base.** For `L` ample
  relative to `f` and `V ⊆ S` affine open, every sufficiently high power of `L`, restricted to
  `f⁻¹(V)`, is `𝒪(1)` pulled back along an immersion `f⁻¹(V) ⟶ ℙⁿ_V` over `V`.
* `VeryAmplePowersUniformDegree.exists_finite_affine_cover_eventually_hasImmersionTwistOver`:
  **the first two steps of Stacks Tag 01VU's (1) ⟹ (3)** — a finite affine covering of the
  quasi-compact base and one degree bound `d₀` that works simultaneously on every member of it.
  This is precisely the hypothesis (2) of Stacks Tag 01VR, for all `d ≥ d₀` at once.
* `VeryAmplePowersUniformDegree.exists_finite_affine_cover_exists_one_le_hasImmersionTwistOver`:
  the same in the existential shape of Tag 01VU's condition (2), through
  `Stacks.RelativeVeryAmple.exists_one_le_and_of_eventually`.
* `exists_finite_affine_cover_eventually_hasImmersionTwistOver_tensorPowerModule`:
  the main theorem over Tag 01CU's tensor powers, which is the family Tag 01VU writes its
  conditions with.

## The route, and what each step costs

Fix an affine open `V ⊆ S` and write `U = f⁻¹(V)`.

* Relative ampleness is *defined* in this repository by ampleness of `U.ι^* L` on `U` for every
  affine open `V` of `S` (`Stacks.RelativeAmple.IsRelativelyAmple`), so the ampleness hypothesis of
  Tag 01VS is available at `V` with no work: it is `hL.2 V hV` on the nose.
* `LocallyOfFiniteType (f ∣_ V)` is Mathlib's instance on `AlgebraicGeometry.morphismRestrict`, so
  the finite-type hypothesis of Tag 01VS costs nothing either. Note that `f ∣_ V : U ⟶ V` has
  `U = f ⁻¹ᵁ V` as its source *on the nose*, which is why no transport across an equality of open
  subschemes appears anywhere below.
* Tag 01VS then produces a bound for the powers of `U.ι^* L`, whereas Tag 01VR's hypothesis is
  about the restriction of the powers of `L`. The two are identified by
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, `U.ι^* (L ^⊗ d) ≅ (U.ι^* L) ^⊗ d`, and
  `Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr` moves the conclusion across it.
* Quasi-compactness of `S` gives a *finite* affine covering, `S.affineCover.finiteSubcover`, whose
  members are affine opens by `AlgebraicGeometry.isAffineOpen_opensRange` and cover `S` by
  `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`. The uniform bound is
  `max 1 (Finset.univ.sup d₀)` over that finite index type; the `max 1` is what makes the bound
  positive when the base is empty, where the supremum is `0`.

## Implementation notes

**The index type of the covering is existentially quantified, not a `Finset` of opens.** It is
`(S.affineCover.finiteSubcover).I₀`, which lands in `Type u` because `S.affineCover.I₀` is the
carrier of `S`; a `Finset S.Opens` would need a `DecidableEq` on `S.Opens` and buys nothing, since
every consumer of Tag 01VR's hypothesis (2) quantifies over the members one at a time.

**No invertibility instance has to be named.** The nested instance failure recorded in
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean` — `IsInvertibleModule` not being
synthesized for a tensor power of a pullback — does not arise here: the only module whose
invertibility is needed is `U.ι^* L`, which is
`Stacks.InvertiblePullback.isInvertibleModule_restrict`, an instance, and
`Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr` is stated with no invertibility
hypothesis at all so that moving across `pullbackTensorPowModuleIso` needs none.

**`Stacks.Ample.tensorPowModule` is the family the proofs run over**, not Tag 01CU's
`Stacks.SheafOfModules.TensorPower.tensorPower`. That is forced: the ampleness theory, relative
ampleness and `pullbackTensorPowModuleIso` are all written over it. Nothing is lost — the two
families are isomorphic in every integer degree by
`Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow`, and
`exists_finite_affine_cover_eventually_hasImmersionTwistOver_tensorPowerModule`
restates the main theorem over Tag 01CU's family, which is the one Tag 01VU is written
with. The matching transfer of the *input* is
`Stacks.PowerFamilyBridge.immersionTwistGap_iff`, so the hypothesis is one condition and not two.

**Ampleness is taken against `Stacks.Ample.IsAmple`** of
`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean`, which is the one of the two
declarations labelled with Stacks Tag 01PS that `Stacks.RelativeAmple.IsRelativelyAmple` and
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` are both written over. The other,
`StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean`, is not compared with it anywhere, so
nothing below is reachable from work stated against that one.

## Where Tag 01VU is

**Stacks Tag 01VU is proved, and nothing in this file carries its label.** The tag is
`Stacks.VeryAmplePowersQuasiCompactBase.tfae`, with (1) ⟹ (3) as
`Stacks.VeryAmplePowersQuasiCompactBase.eventuallyVeryAmplePower_of_isRelativelyAmple`, in
`StacksFrontier/AlgebraicGeometry/VeryAmplePowersQuasiCompactBase/Basic.lean`. It is stated with
Tag 01VM's `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, an immersion over `S` into the
relative `Proj` of the symmetric algebra of a quasi-coherent module. Its glueing step, Tag 01VR's
(2) ⟹ (1), is `Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover`, and its local step keeps
the generating families of sections
(`Stacks.QuasiProjectiveCompactification.eventually_familyImmersionTwist`) rather than going
through the immersion-only conclusion of this file. The input
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` is itself a theorem,
`Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`.

**The finite-type hypothesis is used only through `LocallyOfFiniteType`.** Tag 01VU states
its conditions under `CompactSpace S`, `LocallyOfFiniteType f` and `QuasiCompact f`. The results
below use `CompactSpace S` and `LocallyOfFiniteType f`; quasi-compactness of `f` enters only as the
first component of relative ampleness, so it is never assumed separately.

## References

* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.VeryAmplePowersUniformDegree

/-! ### Stacks Tag 01VS as a named hypothesis -/

/-- **Stacks Tag 01VS at every situation**, the single input of this file:
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` — all sufficiently high tensor powers of an
ample invertible module on a scheme locally of finite type over a base are `𝒪(1)` pulled back
along an immersion into projective space over that base — taken for every scheme, every morphism
and every invertible module.

It is quantified over the situation because Tag 01VU's proof applies Tag 01VT to the restriction
`f⁻¹(V) ⟶ V` of `f` over each member of an affine covering of the base, which is a different
situation for each member. `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform_iff` shows
this is Tag 01VS verbatim and nothing more. -/
def ImmersionTwistGapUniform : Prop :=
  ∀ (A B : Scheme.{u}) (g : A ⟶ B) (N : A.Modules) [IsInvertibleModule A N],
    ImmersionTwistGap g N (tensorPowModule A N)

/-- **`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` is Stacks Tag 01VS, verbatim,
at every situation.** The right-hand side is the conclusion of
`Stacks.AmpleProjectiveImmersion.exists_immersion_projectiveSpaceOver_of_isAmple'`, written out
with no reference to `Stacks.AmpleProjectiveImmersion.HasImmersionTwist`; the two are
interchanged by `Stacks.AmpleProjectiveImmersion.hasImmersionTwist_iff`, both halves of which are
proved there. So this file assumes the geometric content of Tag 01VS and nothing else. -/
theorem immersionTwistGapUniform_iff :
    ImmersionTwistGapUniform.{u} ↔
      ∀ (A B : Scheme.{u}) (g : A ⟶ B) (N : A.Modules) [IsInvertibleModule A N],
        IsAmple A N → LocallyOfFiniteType g →
          ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
            ∃ (n : ℕ) (i : A ⟶ projectiveSpaceOver n B),
              IsImmersion i ∧
              i ≫ pullback.fst (terminal.from B)
                (terminal.from (projectiveSpaceAtUniverse.{u} n)) = g ∧
              Nonempty (tensorPowModule A N (d : ℤ) ≅
                (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n B)) := by
  simp only [ImmersionTwistGapUniform, ImmersionTwistGap, EventualImmersionTwist,
    hasImmersionTwist_iff, HasImmersionTwistOver]

/-! ### Transport along an isomorphism of modules -/

/-- **The conclusion of Stacks Tag 01VS at one degree depends only on the isomorphism class of the
module.** Both halves compose the given isomorphism with the recorded one; no invertibility
hypothesis is needed, which is what lets the transport across
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` below name no instance. -/
theorem hasImmersionTwistOver_congr {X S : Scheme.{u}} (f : X ⟶ S) {M M' : X.Modules}
    (e : M ≅ M') : HasImmersionTwistOver f M ↔ HasImmersionTwistOver f M' := by
  constructor
  · rintro ⟨n, i, hi, hover, ⟨j⟩⟩
    exact ⟨n, i, hi, hover, ⟨e.symm ≪≫ j⟩⟩
  · rintro ⟨n, i, hi, hover, ⟨j⟩⟩
    exact ⟨n, i, hi, hover, ⟨e ≪≫ j⟩⟩

/-! ### The local step: Stacks Tag 01VT over one affine open of the base -/

/-- **The local step of Stacks Tag 01VU's (1) ⟹ (3), which is the content of Tag 01VT's
(2) ⟹ (6).** Let `L` be ample relative to `f : X ⟶ S`, let `f` be locally of finite type, and let
`V ⊆ S` be an affine open. Then there is a `d₀ ≥ 1` such that for every `d ≥ d₀` the restriction
of `L ^⊗ d` to `f⁻¹(V)` is `𝒪(1)` pulled back along an immersion `f⁻¹(V) ⟶ ℙⁿ_V` over `V`.

The ampleness hypothesis of Tag 01VS at `V` is the defining clause of relative ampleness, and the
finite-type hypothesis is Mathlib's instance for `AlgebraicGeometry.morphismRestrict`, so the only
step is the identification `f⁻¹(V).ι^* (L ^⊗ d) ≅ (f⁻¹(V).ι^* L) ^⊗ d` of
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. -/
theorem eventually_hasImmersionTwistOver_restrict (hgap : ImmersionTwistGapUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (V : S.Opens) (hV : IsAffineOpen V) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      HasImmersionTwistOver (f ∣_ V)
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
          (tensorPowModule X L (d : ℤ))) := by
  obtain ⟨d₀, hd₀, hd⟩ :=
    hgap (f ⁻¹ᵁ V).toScheme V.toScheme (f ∣_ V) _ (hL.2 V hV) inferInstance
  refine ⟨d₀, hd₀, fun d hdd => ?_⟩
  refine (hasImmersionTwistOver_congr (f ∣_ V)
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι L d)).mpr ?_
  exact (hasImmersionTwist_iff (f ∣_ V) _).mp (hd d hdd)

/-! ### The global step: a finite affine covering with one uniform degree bound -/

/-- **The first two steps of Stacks Tag 01VU's (1) ⟹ (3).** If `L` is ample relative to
`f : X ⟶ S` with `S` quasi-compact and `f` locally of finite type, then there are a *finite*
family of affine opens covering `S` and a single `d₀ ≥ 1` such that for every `d ≥ d₀` and every
member `V` of the family, the restriction of `L ^⊗ d` to `f⁻¹(V)` is `𝒪(1)` pulled back along an
immersion `f⁻¹(V) ⟶ ℙⁿ_V` over `V`.

This is exactly the hypothesis (2) of Stacks Tag 01VR, for all `d ≥ d₀` simultaneously and with
the projective bundle of that hypothesis replaced by projective space, which is the stronger
statement — see the module documentation. Tag 01VR itself, the glueing step, is not taken here;
see "Where Tag 01VU is" in the module documentation.

The covering is `S.affineCover.finiteSubcover`, finite because `S` is quasi-compact; the bound is
the supremum over its index type of the bounds supplied by
`Stacks.VeryAmplePowersUniformDegree.eventually_hasImmersionTwistOver_restrict`, raised to at least
`1` so that it stays positive over an empty base. -/
theorem exists_finite_affine_cover_eventually_hasImmersionTwistOver
    (hgap : ImmersionTwistGapUniform.{u}) {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [CompactSpace S] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Opens),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
        ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ j,
          HasImmersionTwistOver (f ∣_ V j)
            ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj
              (tensorPowModule X L (d : ℤ))) := by
  classical
  set 𝒰 := S.affineCover.finiteSubcover
  have hVaff : ∀ j : 𝒰.I₀, IsAffineOpen (𝒰.f j).opensRange := fun j =>
    isAffineOpen_opensRange _
  choose d₀ hd₀ hd using fun j : 𝒰.I₀ =>
    eventually_hasImmersionTwistOver_restrict hgap f L hL (𝒰.f j).opensRange (hVaff j)
  refine ⟨𝒰.I₀, inferInstance, fun j => (𝒰.f j).opensRange, hVaff,
    Scheme.OpenCover.iSup_opensRange 𝒰, max 1 (Finset.univ.sup d₀), le_max_left _ _,
    fun d hdd j => hd j d
      (((Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _)).trans hdd)⟩

/-- **The first two steps of Stacks Tag 01VU's (1) ⟹ (2)**, the existential shape in which the
source writes condition (2): one positive degree, rather than all sufficiently high ones. It is
`VeryAmplePowersUniformDegree.exists_finite_affine_cover_eventually_hasImmersionTwistOver` followed
by `Stacks.RelativeVeryAmple.exists_one_le_and_of_eventually`, which is the source's own
"trivially (3) implies (2)" and uses nothing about very ampleness. -/
theorem exists_finite_affine_cover_exists_one_le_hasImmersionTwistOver
    (hgap : ImmersionTwistGapUniform.{u}) {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [CompactSpace S] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Opens),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
        ∃ d : ℕ, 1 ≤ d ∧ ∀ j,
          HasImmersionTwistOver (f ∣_ V j)
            ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj
              (tensorPowModule X L (d : ℤ))) := by
  obtain ⟨ι, hι, V, hVaff, hVcov, d₀, hd₀, hd⟩ :=
    exists_finite_affine_cover_eventually_hasImmersionTwistOver hgap f L hL
  exact ⟨ι, hι, V, hVaff, hVcov,
    Stacks.RelativeVeryAmple.exists_one_le_and_of_eventually ⟨d₀, hd⟩⟩

/-! ### The same statement over Tag 01CU's tensor powers -/

/-- **The first two steps of Stacks Tag 01VU's (1) ⟹ (3), stated over Tag 01CU's tensor
powers.** The statement of Tag 01VU writes its conditions with Tag 01CU's `tensorPower`, whose library
form is `Stacks.SheafOfModules.TensorPower.tensorPower`; the statements above are written over
`Stacks.Ample.tensorPowModule`, which is the family relative ampleness itself is defined with.
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` is Tag 01CU's power with the invertibility
class converted, and `Stacks.PowerFamilyBridge.tensorPowerModuleIso` identifies the two families
in every integer degree, so neither family is privileged and this is the same theorem. -/
theorem exists_finite_affine_cover_eventually_hasImmersionTwistOver_tensorPowerModule
    (hgap : ImmersionTwistGapUniform.{u}) {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [CompactSpace S] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Opens),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
        ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ j,
          HasImmersionTwistOver (f ∣_ V j)
            ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj
              (tensorPowerModule X L (d : ℤ))) := by
  obtain ⟨ι, hι, V, hVaff, hVcov, d₀, hd₀, hd⟩ :=
    exists_finite_affine_cover_eventually_hasImmersionTwistOver hgap f L hL
  refine ⟨ι, hι, V, hVaff, hVcov, d₀, hd₀, fun d hdd j => ?_⟩
  exact (hasImmersionTwistOver_congr (f ∣_ V j)
    ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).mapIso
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso X L (d : ℤ)))).mpr (hd d hdd j)

end Stacks.VeryAmplePowersUniformDegree

end
