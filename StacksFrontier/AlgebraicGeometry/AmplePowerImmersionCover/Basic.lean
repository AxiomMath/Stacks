module

public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.VeryAmpleFiniteTypeCover.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersUniformDegree.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ImmersionTwistGapUniform

/-!
# Stacks Tag 02NR: relative ampleness read on a covering by projective immersions of powers

Stacks Tag 02NR says that for a morphism of schemes `f : X ⟶ S` of finite type and an invertible
`𝒪_X`-module `L` the following are equivalent:

(a) `L` is `f`-relatively ample, and
(b) there are an open covering `S = ⋃ V_j`, for each `j` integers `d_j ≥ 1` and `n_j ≥ 0`, and
    immersions `i_j : X_j = f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` with
    `L^{⊗ d_j}|_{X_j} ≅ i_j^* 𝒪(1)`.

Condition (a) is `Stacks.RelativeAmple.IsRelativelyAmple`, Stacks Tag 01VH. Condition (b) is
`Stacks.AmplePowerImmersionCover.HasPowerProjectiveImmersionCover`, assembled from
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` — the source's clause at one member of the
covering, written out — at the restricted morphism `f ∣_ V_j`, whose source is `f⁻¹(V_j)` *on the
nose*, so no transport across an equality of open subschemes occurs anywhere below. The degree
`d_j` is quantified inside the covering clause, so it varies with `j`, and `n_j` is quantified
inside `HasImmersionTwistOver`.

This is the ample analogue of Stacks Tag 02NQ, which is the same statement with "relatively ample"
replaced by "relatively very ample" and the power `L^{⊗ d_j}` replaced by `L` itself; that tag is
`StacksFrontier/AlgebraicGeometry/VeryAmpleFiniteTypeCover/Equivalence.lean`. **Both directions are
proved outright here**, and more cheaply than for Tag 02NQ: the very-ample statement has to glue
very ampleness over the base, through `f_* L`, whereas relative ampleness of `L` is
degree-insensitive and glues over the base by Stacks Tag 01VJ with the degrees `d_j` consumed one
member at a time.

## Main definitions

* `Stacks.AmplePowerImmersionCover.HasPowerProjectiveImmersionCover`: **condition (b) of Stacks
  Tag 02NR**, written out over the library's objects.

## Main results

* `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`:
  `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` — Stacks Tag 01VS at every
  situation — **discharged**, from the unconditional Tag 01VS.
* `exists_affine_cover_eventually_hasImmersionTwistOver_of_isRelativelyAmple` (in this namespace):
  the strengthening of (a) ⟹ (b) that the proof produces — the covering may be taken to consist of
  **affine** opens, and the conclusion holds not for one `d_j` but for **every sufficiently large**
  one, uniformly on each member.
* `Stacks.AmplePowerImmersionCover.hasPowerProjectiveImmersionCover_of_isRelativelyAmple`:
  **Stacks Tag 02NR, (a) ⟹ (b)**, with no hypothesis.
* `Stacks.AmplePowerImmersionCover.isAmple_preimage_of_hasImmersionTwistOver`: over an **affine**
  member of the covering, the clause of (b) gives ampleness of `L` on the preimage, with no
  hypothesis. This is the engine of the affine-covering case.
* `Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_affine_cover_hasImmersionTwistOver`:
  **the affine-covering case of (b) ⟹ (a), with no hypothesis.**
* `Stacks.AmplePowerImmersionCover.hasImmersionTwistOver_morphismRestrict`: **the immersion clause
  restricts to an open of the base**, which is what removes the affineness restriction from the
  previous item — projective space over a base is a fibre product over the terminal scheme, so its
  base change along an open immersion costs nothing.
* `Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_hasImmersionTwistOver`: the clause of (b)
  at a **single, not necessarily affine, base** already gives relative ampleness, with no
  hypothesis.
* `Stacks.AmplePowerImmersionCover.isAmple_preimage_of_isRelativelyAmple_morphismRestrict` and
  `Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_forall_isRelativelyAmple_morphismRestrict`:
  **Stacks Tag 01VJ, (2) ⟹ (1)** — relative ampleness glues over an open covering of the base,
  proved here from the library's pointwise-affine form of that tag.
* `Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_hasPowerProjectiveImmersionCover`:
  **Stacks Tag 02NR, (b) ⟹ (a)**, with no hypothesis.
* `Stacks.AmplePowerImmersionCover.isRelativelyAmple_iff_hasPowerProjectiveImmersionCover`:
  **Stacks Tag 02NR**, the equivalence, with no hypothesis.

## What of Stacks Tag 02NR is proved

**(a) ⟹ (b) is proved outright**, and in the stronger form with an affine covering and every
sufficiently large degree. The source's proof is "cover `S` by affine opens and apply Tag 01VS to
each restriction", and every input of that is available: ampleness of `L|_{f⁻¹(V)}` over an affine
`V` is the defining clause of relative ampleness, local finiteness of type of `f ∣_ V` is one of
Mathlib's instances on `AlgebraicGeometry.morphismRestrict`, and Tag 01VS itself is
`Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple`, which carries the
`@[stacks 01VS]` attribute with no hypothesis. The one piece of plumbing is
`Stacks.VeryAmplePowersUniformDegree.eventually_hasImmersionTwistOver_restrict`, which was written
against Tag 01VS as a *named hypothesis*;
`Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`
discharges that hypothesis here, and so this file assumes nothing for this direction.

**(b) ⟹ (a) is proved outright as well**, for the source's covering by arbitrary opens. Over an
affine member of the covering an immersion into `𝐏ⁿ` carrying `𝒪(1)` to a positive power of `L`
already forces ampleness:
`Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver` is proved with no
hypothesis, Stacks Tag 01VK (`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`)
converts relative ampleness over an affine base into absolute ampleness, and Stacks Tag 01VJ
(`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple`) assembles the
members into relative ampleness over `S`.

**The source's (b) does not ask the covering to be affine, and nothing is charged for dropping
that**, because the immersion clause itself restricts to an open of the base:
`Stacks.AmplePowerImmersionCover.hasImmersionTwistOver_morphismRestrict`. Projective space over a
base is a *fibre product over the terminal scheme* — `𝐏ⁿ_B = B ×_{⊤} 𝐏ⁿ_ℤ` — so its base change
along `V.ι : V ⟶ S` is formal: a morphism into `𝐏ⁿ_V` is a pair consisting of a morphism to `V`
and a morphism to the integral model, with no commuting square to check
(`Stacks.AmpleProjectiveImmersion.liftOver`), and the restricted morphism is an immersion because
its composite with the canonical `𝐏ⁿ_V ⟶ 𝐏ⁿ_S` is `f⁻¹(V) ↪ X ⟶ 𝐏ⁿ_S`. This is *not* the base
change of the relative homogeneous spectrum of a sheaf of graded algebras, which
`StacksFrontier/AlgebraicGeometry/ProjBundleBaseChangeReduction/Basic.lean` records as not
constructed; it is only the base change of a product, and it needs none of that machinery.

Consequently a member `V_j` of the covering may be refined to the affine opens inside it *after*
the immersion clause has been restricted to them, which is
`Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_hasImmersionTwistOver`: the clause of (b)
over an arbitrary base already gives relative ampleness over that base.

**Neither relative very ampleness nor Stacks Tag 01VR's (2) ⟹ (1) — the gluing of *very*
ampleness — is used anywhere in this file.** Gluing very ampleness would need a single degree
working on every member, which the source's condition (b) does not supply; the gluing is done
instead at the level of relative ampleness of `L`, which is degree-insensitive, and the covering
form of that gluing — Stacks Tag 01VJ's (2) ⟹ (1) — is proved here from the library's
pointwise-affine form of Tag 01VJ. The degrees `d_j` are therefore consumed one member at a time,
and no common degree has to be produced.

**No attribute is attached to the affine-covering case of (b) ⟹ (a).** It is a *restriction* of the
source's implication, not one of its clauses, so it is recorded as a lemma and the tag is carried
only by the two implications of the source and by their conjunction.

## Implementation notes

**The power is the restriction of `L^{⊗ d}`, not the `d`-th power of the restriction.** The source
writes `L^{⊗ d_j}|_{X_j}`, and condition (b) below transcribes that spelling: the module is
`(modulePullback (f ⁻¹ᵁ V_j).ι …).obj (tensorPowModule X L d_j)`. The other reading, the `d_j`-th
power of `L|_{X_j}`, is canonically isomorphic to it by
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, which is Stacks Tag 01CD iterated; that
isomorphism is the only place the two readings are interchanged, and
`Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr` carries the clause across it.

**The restriction of `L` is spelled with `RingedSpaceModuleAdjunction.modulePullback`**, as in
`Stacks.RelativeAmple.IsRelativelyAmple` and in
`Stacks.VeryAmpleFiniteTypeCover.HasProjectiveImmersionCover`, and not with
`AlgebraicGeometry.Scheme.Modules.pullback`: only the former carries the invertibility instance
needed to *state* the clause at the restricted module.

**The covering is an indexed family with `(⨆ j, V j) = ⊤`**, the shape
`Stacks.VeryAmpleFiniteTypeCover.HasProjectiveImmersionCover` uses for the same source condition.
The source writes `S = ⋃ V_j` with `d_j` and `n_j` depending on `j`, which the indexed shape
transcribes directly.

**Finite type is `LocallyOfFiniteType` together with `QuasiCompact`**, as elsewhere in these trees.
The direction (a) ⟹ (b) uses only local finiteness of type — quasi-compactness of `f` is already
part of relative ampleness — and (b) ⟹ (a) uses only quasi-compactness, so neither is stated with
the unused half.

**`Stacks.AmplePowerImmersionCover.HasPowerProjectiveImmersionCover` is not
`Stacks.VeryAmpleFiniteTypeCover.HasProjectiveImmersionCover` with a power substituted for the
module, and must not be replaced by it.** The latter asks for the immersion clause at one fixed
module; here the degree is existentially quantified *inside* the covering clause, which is what lets
it depend on the member, as the source's `d_j` does.

## References

* [Stacks Project, Tag 02NR](https://stacks.math.columbia.edu/tag/02NR)
* [Stacks Project, Tag 02NQ](https://stacks.math.columbia.edu/tag/02NQ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.AmplePowerImmersionCover

/-! ### Stacks Tag 01VS at every situation, discharged -/

/-! ### Condition (b) of Stacks Tag 02NR -/

/-- **Condition (b) of Stacks Tag 02NR.** There are an open covering `S = ⋃ V_j`, for each `j`
integers `d_j ≥ 1` and `n_j ≥ 0`, and immersions `i_j : X_j = f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j`
such that `L^{⊗ d_j}|_{X_j} ≅ i_j^* 𝒪_{𝐏^{n_j}_{V_j}}(1)`.

Each member of the covering contributes a degree `d_j ≥ 1` together with
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`, which is the source's clause written out —
an immersion into projective space over the base, lying over the base, pulling the hyperplane sheaf
back to the given module — at the restricted morphism `f ∣_ V_j`, whose source is `f⁻¹(V_j)` on the
nose. The integer `n_j` is the one that predicate quantifies over, and `d_j` is quantified here, so
both depend on `j` with nothing further to arrange. -/
def HasPowerProjectiveImmersionCover {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Prop :=
  ∃ (ι : Type u) (V : ι → S.Opens), (⨆ j, V j) = ⊤ ∧ ∀ j : ι, ∃ d : ℕ, 1 ≤ d ∧
    HasImmersionTwistOver (f ∣_ V j)
      ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj (tensorPowModule X L (d : ℤ)))

variable {X S : Scheme.{u}}

/-! ### Stacks Tag 02NR, (a) implies (b) -/

/-- **Stacks Tag 02NR, (a) ⟹ (b), with the covering taken affine and the degree taken eventual.**
For `f : X ⟶ S` locally of finite type and `L` relatively ample there are an open covering of `S`
**by affine opens** and, for each member `V`, a bound `d₀ ≥ 1` such that **every** degree `d ≥ d₀`
admits an `n` and an immersion `f⁻¹(V) ⟶ 𝐏ⁿ_V` over `V` carrying the hyperplane sheaf to
`L^{⊗ d}|_{f⁻¹(V)}`.

The source's condition (b) asks neither for an affine covering nor for more than one degree; both
extras are recorded because they are what the proof produces and what a consumer needing an affine
base, or needing to match degrees across members, can use. The covering is *all* of the affine opens
of `S`, which cover it by `AlgebraicGeometry.iSup_affineOpens_eq_top`, so neither a choice nor
quasi-compactness of `S` enters. -/
theorem exists_affine_cover_eventually_hasImmersionTwistOver_of_isRelativelyAmple (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ (ι : Type u) (V : ι → S.Opens), (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
      ∀ j : ι, ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver (f ∣_ V j)
          ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj
            (tensorPowModule X L (d : ℤ))) := by
  refine ⟨↥S.affineOpens, fun j => (j : S.Opens), fun j => j.2,
    iSup_affineOpens_eq_top S, fun j => ?_⟩
  exact Stacks.VeryAmplePowersUniformDegree.eventually_hasImmersionTwistOver_restrict
    Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform f L hL (j : S.Opens) j.2

/-- **Stacks Tag 02NR, (a) ⟹ (b).** Let `f : X ⟶ S` be of finite type and `L` an invertible
`𝒪_X`-module. If `L` is `f`-relatively ample then there are an open covering `S = ⋃ V_j`, for each
`j` integers `d_j ≥ 1` and `n_j ≥ 0`, and immersions `f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` carrying
the hyperplane sheaf to `L^{⊗ d_j}|_{f⁻¹(V_j)}`.

This is the source's own proof — take an affine open covering of `S` and apply Stacks Tag 01VS to
each of the restrictions of `f` and `L` — and it needs no hypothesis: Tag 01VS is proved
unconditionally, and the stronger affine-and-eventual form is
`exists_affine_cover_eventually_hasImmersionTwistOver_of_isRelativelyAmple`, from which one degree
is read off at the bound itself. Only local finiteness of type is used;
quasi-compactness of `f` is already part of relative ampleness. -/
@[stacks 02NR "(a) implies (b), with no hypothesis"]
theorem hasPowerProjectiveImmersionCover_of_isRelativelyAmple (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    HasPowerProjectiveImmersionCover f L := by
  obtain ⟨ι, V, -, hcov, h⟩ :=
    exists_affine_cover_eventually_hasImmersionTwistOver_of_isRelativelyAmple f L hL
  refine ⟨ι, V, hcov, fun j => ?_⟩
  obtain ⟨d₀, hd₀, hd⟩ := h j
  exact ⟨d₀, hd₀, hd d₀ le_rfl⟩

/-! ### The affine-covering case of (b) implies (a) -/

/-- The immersion clause for the restriction of `L^{⊗ d}` is the one for the `d`-th power of the
restriction of `L`. -/
private theorem hasImmersionTwistOver_tensorPow_restrict (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (V : S.Opens) (d : ℕ)
    (h : HasImmersionTwistOver (f ∣_ V)
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj (tensorPowModule X L (d : ℤ)))) :
    HasImmersionTwistOver (f ∣_ V)
      (tensorPowModule (f ⁻¹ᵁ V).toScheme
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) (d : ℤ)) :=
  (Stacks.VeryAmplePowersUniformDegree.hasImmersionTwistOver_congr (f ∣_ V)
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι L d)).mp h

/-- **Over an affine member of the covering, the clause of condition (b) gives ampleness of `L` on
the preimage.** If `V ⊆ S` is affine, `d ≥ 1`, and `L^{⊗ d}|_{f⁻¹(V)}` is the hyperplane sheaf
pulled back along an immersion `f⁻¹(V) ⟶ 𝐏ⁿ_V` over `V`, then `L|_{f⁻¹(V)}` is ample.

No hypothesis is needed. `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` moves the clause from
the restriction of the power to the power of the restriction,
`Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver` — proved with no
hypothesis — turns it into relative ampleness of `L|_{f⁻¹(V)}` over the affine base `V`, and Stacks
Tag 01VK converts that into absolute ampleness. -/
theorem isAmple_preimage_of_hasImmersionTwistOver (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [QuasiCompact f] {V : S.Opens} (hV : IsAffineOpen V) {d : ℕ}
    (hd : 1 ≤ d)
    (h : HasImmersionTwistOver (f ∣_ V)
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj (tensorPowModule X L (d : ℤ)))) :
    IsAmple (f ⁻¹ᵁ V).toScheme
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) := by
  have : IsAffine V.toScheme := hV
  exact (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (f ∣_ V) _).mp
    (Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver (f ∣_ V) _
      inferInstance ⟨d, hd, hasImmersionTwistOver_tensorPow_restrict f L V d h⟩)

/-- **The affine-covering case of Stacks Tag 02NR's (b) ⟹ (a), with no hypothesis.** If the covering
of condition (b) may be taken to consist of **affine** opens, then `L` is `f`-relatively ample.

Stacks Tag 01VJ reduces relative ampleness to ampleness of `L` on the preimage of one affine open
around each point of the base, and
`Stacks.AmplePowerImmersionCover.isAmple_preimage_of_hasImmersionTwistOver` supplies that at each
member. Only quasi-compactness of `f` is used.

This is **not** the source's implication, which does not ask the covering to be affine, and it
carries no `@[stacks]` attribute; see "What of Stacks Tag 02NR is proved". -/
theorem isRelativelyAmple_of_affine_cover_hasImmersionTwistOver (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f) {ι : Type*} (V : ι → S.Opens)
    (hVaff : ∀ j, IsAffineOpen (V j)) (hcov : (⨆ j, V j) = ⊤)
    (h : ∀ j : ι, ∃ d : ℕ, 1 ≤ d ∧
      HasImmersionTwistOver (f ∣_ V j)
        ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj (tensorPowModule X L (d : ℤ)))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  have : QuasiCompact f := hf
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L hf
    fun x => ?_
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  obtain ⟨d, hd, hdj⟩ := h j
  exact ⟨V j, hVaff j, hxj,
    isAmple_preimage_of_hasImmersionTwistOver f L (hVaff j) hd hdj⟩

/-! ### The immersion clause restricts to an open of the base -/

/-- **The immersion clause of condition (b) restricts to an open of the base.** If `M` is the
hyperplane sheaf pulled back along an immersion `X ⟶ 𝐏ⁿ_S` over `S`, then for every open `V ⊆ S`
the restriction `M|_{f⁻¹(V)}` is the hyperplane sheaf pulled back along an immersion
`f⁻¹(V) ⟶ 𝐏ⁿ_V` over `V`.

Projective space over a base is a fibre product over the terminal scheme — `𝐏ⁿ_B` is
`B ×_{⊤} 𝐏ⁿ_ℤ` — so its base change along `V.ι : V ⟶ S` costs nothing: the restricted immersion
is `Stacks.AmpleProjectiveImmersion.liftOver` of the pair consisting of `f ∣_ V` and the morphism
to the integral model `f⁻¹(V) ⟶ X ⟶ 𝐏ⁿ_S ⟶ 𝐏ⁿ_ℤ`, with no commuting square to check. It is an
immersion because its composite with the canonical `𝐏ⁿ_V ⟶ 𝐏ⁿ_S` is `f⁻¹(V) ↪ X ⟶ 𝐏ⁿ_S`, an open
immersion followed by an immersion, and `AlgebraicGeometry.IsImmersion.of_comp` reflects that.
The twist is carried across by `Stacks.AmpleProjectiveImmersion.liftOverTwistIso` together with
the pseudofunctoriality of the module pullback.

This is what makes Stacks Tag 02NR's (b) ⟹ (a) unconditional: the source's covering need not be
affine, because each member may be refined to affine opens *after* the immersion clause has been
restricted to them. -/
theorem hasImmersionTwistOver_morphismRestrict (f : X ⟶ S) (M : X.Modules) (V : S.Opens)
    (h : HasImmersionTwistOver f M) :
    HasImmersionTwistOver (f ∣_ V)
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj M) := by
  obtain ⟨n, i, him, hover, ⟨e⟩⟩ := h
  refine ⟨n, liftOver (f ∣_ V) ((f ⁻¹ᵁ V).ι ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S),
    ?_, liftOver_fst _ _, ⟨?_⟩⟩
  · have hcomp : IsImmersion ((f ⁻¹ᵁ V).ι ≫ i) := inferInstance
    have key : liftOver (f ∣_ V)
          ((f ⁻¹ᵁ V).ι ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ≫
          liftOver (pullback.fst (terminal.from V.toScheme)
              (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫ V.ι)
            (projectiveSpaceOver.toIntegralAtUniverse n V.toScheme) =
        (f ⁻¹ᵁ V).ι ≫ i := by
      refine pullback.hom_ext ?_ ?_
      · simp only [liftOver, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          morphismRestrict_ι, hover]
      · simp only [liftOver, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    have hI : IsImmersion (liftOver (f ∣_ V)
        ((f ⁻¹ᵁ V).ι ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ≫
        liftOver (pullback.fst (terminal.from V.toScheme)
            (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫ V.ι)
          (projectiveSpaceOver.toIntegralAtUniverse n V.toScheme)) := by
      rw [key]; exact hcomp
    exact IsImmersion.of_comp _
      (liftOver (pullback.fst (terminal.from V.toScheme)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫ V.ι)
        (projectiveSpaceOver.toIntegralAtUniverse n V.toScheme))
  · exact (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).mapIso e ≪≫
      (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).mapIso
        ((Scheme.Modules.pullbackComp i
          (projectiveSpaceOver.toIntegralAtUniverse n S)).app (twistingSheafAtUniverse n)) ≪≫
      (Scheme.Modules.pullbackComp (f ⁻¹ᵁ V).ι
          (i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).app (twistingSheafAtUniverse n) ≪≫
      (liftOverTwistIso (f ∣_ V)
        ((f ⁻¹ᵁ V).ι ≫ i ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).symm

/-- **The clause of condition (b) at one member of the covering already gives relative ampleness
over that member, with no hypothesis and with no affineness assumed.** If `f : X ⟶ S` is
quasi-compact, `d ≥ 1`, and `L^{⊗ d}` is the hyperplane sheaf pulled back along an immersion
`X ⟶ 𝐏ⁿ_S` over `S`, then `L` is `f`-relatively ample.

The base `S` is arbitrary. Relative ampleness is checked on the preimage of one affine open around
each point of the base — Stacks Tag 01VJ, in the library's pointwise-affine form
`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple` — and over such an
affine open `W` the immersion clause is available by
`Stacks.AmplePowerImmersionCover.hasImmersionTwistOver_morphismRestrict`, so
`Stacks.AmplePowerImmersionCover.isAmple_preimage_of_hasImmersionTwistOver` applies. The affine
opens cover `S` by `AlgebraicGeometry.iSup_affineOpens_eq_top`. -/
theorem isRelativelyAmple_of_hasImmersionTwistOver (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f) {d : ℕ} (hd : 1 ≤ d)
    (h : HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  have : QuasiCompact f := hf
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L hf
    fun x => ?_
  obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top S).ge (Set.mem_univ x))
  exact ⟨(W : S.Opens), W.2, hxW,
    isAmple_preimage_of_hasImmersionTwistOver f L W.2 hd
      (hasImmersionTwistOver_morphismRestrict f _ (W : S.Opens) h)⟩

/-! ### Relative ampleness glues over an open covering of the base -/

/-- **Ampleness of the restriction of a module to an open subscheme depends only on the open.**
A transport lemma, used to move ampleness between two spellings of one open of `X`. -/
theorem isAmple_pullbackModule_of_eq {Y : Scheme.{u}} (M : Y.Modules) [IsInvertibleModule Y M]
    {U U' : Y.Opens} (h : U = U')
    (hA : IsAmple U'.toScheme ((modulePullback U'.ι.toLRSHom.toShHom).obj M)) :
    IsAmple U.toScheme ((modulePullback U.ι.toLRSHom.toShHom).obj M) := by
  subst h; exact hA

/-- **Relative ampleness over an open `V` of the base gives ampleness over the preimage of any
affine open contained in `V`.** If `L|_{f⁻¹(V)}` is ample relative to `f ∣_ V` and `W ≤ V` is an
affine open of `S`, then `L|_{f⁻¹(W)}` is ample.

This is the one place where an open of `S` below `V` is matched with an open of `V.toScheme`. The
affine open of `V.toScheme` is `V.ι ⁻¹ᵁ W`, affine by
`AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion` because `W ≤ V` is `W` inside the range
of `V.ι`; `AlgebraicGeometry.image_morphismRestrict_preimage` identifies `f⁻¹(W)` with the image of
`(f ∣_ V)⁻¹(V.ι⁻¹ W)` under `(f⁻¹V).ι`, and `AlgebraicGeometry.Scheme.Hom.isoImage` is the
isomorphism onto that image, compatible with the two inclusions by
`AlgebraicGeometry.Scheme.Hom.isoImage_inv_ι`. Ampleness crosses the isomorphism by
`Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso` and the resulting composite of restrictions is
reassociated by `Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`. -/
theorem isAmple_preimage_of_isRelativelyAmple_morphismRestrict (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] {V W : S.Opens} (hWV : W ≤ V) (hW : IsAffineOpen W)
    (h : Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V)
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L)) :
    IsAmple (f ⁻¹ᵁ W).toScheme ((modulePullback (f ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj L) := by
  have hrange : W ≤ V.ι.opensRange := by simpa using hWV
  have hW' : IsAffineOpen (V.ι ⁻¹ᵁ W) := hW.preimage_of_isOpenImmersion V.ι hrange
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simpa using inf_eq_right.mpr hWV
  have hpre : f ⁻¹ᵁ W = (f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)) := by
    conv_lhs => rw [← himg]
    exact (image_morphismRestrict_preimage f V (V.ι ⁻¹ᵁ W)).symm
  have iV : IsInvertibleModule (f ⁻¹ᵁ V).toScheme
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_restrict (f ⁻¹ᵁ V) L
  have iW : IsInvertibleModule ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)).toScheme
      ((modulePullback ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)).ι.toLRSHom.toShHom).obj
        ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L)) :=
    Stacks.InvertiblePullback.isInvertibleModule_restrict _ _
  have iimg : IsInvertibleModule ((f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule
        ((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))).inv
        ((modulePullback ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)).ι.toLRSHom.toShHom).obj
          ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ _
  have hA := h.2 (V.ι ⁻¹ᵁ W) hW'
  refine isAmple_pullbackModule_of_eq L hpre ?_
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mpr
    (Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso
      ((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))).inv _ hA)
  refine Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
      (Scheme.Hom.isoImage_inv_ι (f ⁻¹ᵁ V).ι ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))).symm L ≪≫
    Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso _ _ L ≪≫
    (modulePullback
      ((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))).inv.toLRSHom.toShHom).mapIso
      (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso _ _ L)

/-- **Stacks Tag 01VJ, (2) implies (1): relative ampleness glues over an open covering of the
base.** Let `f : X ⟶ S` be quasi-compact and let `S = ⋃ V_j` be an open covering such that
`L|_{f⁻¹(V_j)}` is ample relative to `f ∣_ V_j` for every `j`. Then `L` is ample relative to `f`.

The library's form of Tag 01VJ is the *pointwise affine* one — relative ampleness from ampleness over
the preimage of one affine open around each point of the base — and this is the passage from it to
an arbitrary covering, which is the shape the source states. The refinement step is
`Stacks.AmplePowerImmersionCover.isAmple_preimage_of_isRelativelyAmple_morphismRestrict`: the affine
opens of `S` are a basis (`AlgebraicGeometry.Scheme.isBasis_affineOpens`), so each point of `S` has
an affine neighbourhood inside the member of the covering containing it, and relative ampleness over
the member gives ampleness over its preimage. -/
theorem isRelativelyAmple_of_forall_isRelativelyAmple_morphismRestrict (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f) {ι : Type*} (V : ι → S.Opens)
    (hcov : (⨆ j, V j) = ⊤)
    (h : ∀ j : ι, Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V j)
      ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L)) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L hf
    fun x => ?_
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  obtain ⟨W, hWaff, hxW, hWV⟩ :=
    Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) hxj
  exact ⟨W, hWaff, hxW,
    isAmple_preimage_of_isRelativelyAmple_morphismRestrict f L hWV hWaff (h j)⟩

/-! ### Stacks Tag 02NR, (b) implies (a) -/

/-- **Stacks Tag 02NR, (b) ⟹ (a).** Let `f : X ⟶ S` be quasi-compact and `L` an invertible
`𝒪_X`-module. If there are an open covering `S = ⋃ V_j`, for each `j` integers `d_j ≥ 1` and
`n_j ≥ 0`, and immersions `f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` carrying the hyperplane sheaf to
`L^{⊗ d_j}|_{f⁻¹(V_j)}`, then `L` is `f`-relatively ample.

The route is the source's, taken member by member. At a member `V_j` the clause of (b) is the
immersion `f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` carrying the hyperplane sheaf to
`L^{⊗ d_j}|_{f⁻¹(V_j)}`;
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` rewrites that module as the `d_j`-th power
of `L|_{f⁻¹(V_j)}`, and
`Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_hasImmersionTwistOver` turns the clause into
relative ampleness of `L|_{f⁻¹(V_j)}` over `V_j` — over a base that need not be affine, because
`Stacks.AmplePowerImmersionCover.hasImmersionTwistOver_morphismRestrict` restricts the immersion
clause to the affine opens of `V_j`. The members are then glued by
`Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_forall_isRelativelyAmple_morphismRestrict`,
which is Stacks Tag 01VJ's (2) ⟹ (1) and is proved above — so the gluing of *very* ampleness,
Stacks Tag 01VR's (2) ⟹ (1), is **not** needed, and neither is any statement about relative very
ampleness. Because the degrees `d_j` are consumed one member at a time, no common degree has to
be produced.

Only quasi-compactness of `f` is used, not the whole of the source's finite-type hypothesis. -/
@[stacks 02NR "(b) implies (a), with no hypothesis: the source's covering is by arbitrary opens, \
  and the immersion clause at a member is restricted to the affine opens of that member by \
  `hasImmersionTwistOver_morphismRestrict`, projective space over a base being a fibre product \
  over the terminal scheme"]
theorem isRelativelyAmple_of_hasPowerProjectiveImmersionCover (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : HasPowerProjectiveImmersionCover f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨ι, V, hcov, hj⟩ := h
  refine isRelativelyAmple_of_forall_isRelativelyAmple_morphismRestrict f L hf V hcov fun j => ?_
  obtain ⟨d, hd, hdj⟩ := hj j
  have : QuasiCompact f := hf
  have hqc : QuasiCompact (f ∣_ V j) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f (V j)).flip inferInstance
  have iVj : IsInvertibleModule (f ⁻¹ᵁ V j).toScheme
      ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_restrict (f ⁻¹ᵁ V j) L
  exact isRelativelyAmple_of_hasImmersionTwistOver (f ∣_ V j) _ hqc hd
    (hasImmersionTwistOver_tensorPow_restrict f L (V j) d hdj)

/-! ### The equivalence -/

/-- **Stacks Tag 02NR.** For `f : X ⟶ S` of finite type and `L` an invertible `𝒪_X`-module,
relative ampleness of `L` is equivalent to the existence of an open covering `S = ⋃ V_j`, of
integers `d_j ≥ 1` and `n_j ≥ 0` for each `j`, and of immersions `f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over
`V_j` carrying the hyperplane sheaf to `L^{⊗ d_j}|_{f⁻¹(V_j)}`.

The two implications are
`Stacks.AmplePowerImmersionCover.hasPowerProjectiveImmersionCover_of_isRelativelyAmple` and
`Stacks.AmplePowerImmersionCover.isRelativelyAmple_of_hasPowerProjectiveImmersionCover`; neither
has a hypothesis, and this is their conjunction. -/
@[stacks 02NR "the equivalence, with no hypothesis"]
theorem isRelativelyAmple_iff_hasPowerProjectiveImmersionCover (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] (hf : QuasiCompact f) :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔ HasPowerProjectiveImmersionCover f L :=
  ⟨hasPowerProjectiveImmersionCover_of_isRelativelyAmple f L,
    isRelativelyAmple_of_hasPowerProjectiveImmersionCover f L hf⟩

end Stacks.AmplePowerImmersionCover

end
