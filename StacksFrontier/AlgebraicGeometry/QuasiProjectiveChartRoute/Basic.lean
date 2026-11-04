module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineMorphism

/-!
# Stacks Tag 07RM needs one of Tag 01VS's four inputs, not all four

Stacks Tag 07RM factors a quasi-projective morphism over a quasi-compact quasi-separated base as
an open immersion followed by a projective morphism. It is proved, at Definition 01W8's
`AlgebraicGeometry.IsProjective`, as
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`. This file is
about a different route to its conclusion at H-projectivity, which runs through
`Stacks.HProjective.IsHQuasiProjective` — an immersion over the base into `ℙⁿ_S` — and reaches that
from Stacks Tag 01VS, in the form `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`.

**Tag 01VS is strictly more than Tag 07RM needs.** Tag 01VS asserts, for *every* sufficiently
high power of the ample module, an immersion into projective space over the base **together with
the identification of that power with the pullback of `𝒪(1)`**. Tag 07RM uses neither the twist
identification nor any degree beyond a single one: all it consumes is the bare existence of an
immersion over `S`. So of the four named inputs that
`Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist` needs for Tag 01VS —
`Stacks.AmpleImmersionReduction.TwistPullback`,
`Stacks.AmpleImmersionReduction.ChartImmersion`,
`Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers` and
`Stacks.AmpleImmersionReduction.TwistPassage` — **Tag 07RM needs only the second.**

The other three are what carry the twist and the degree range:

* `TwistPullback` is precisely the twist identification `M ≅ p ^* 𝒪(1)`;
* `TwistPassage` and `IsEventuallyFinGenPowers` are precisely the passage from one degree to
  every `d ≥ d₀`.

`Stacks.QuasiProjectiveChartRoute.isHQuasiProjective_of_chartImmersion` below is
`Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple` with `ChartImmersion` in
place of `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`, and the two signatures are where the
saving is visible. A second saving comes with it: the hypothesis no longer has to be transported
between the two families of tensor powers, so `Stacks.PowerFamilyBridge.immersionTwistGap_iff` does
not appear below, where both `StacksFrontier/AlgebraicGeometry/HProjective/AffineBase.lean` and
`StacksFrontier/AlgebraicGeometry/HProjective/AffineMorphism.lean` need it. `ChartImmersion` is
stated over `Stacks.Ample.tensorPowModule`, which is the family
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks` consumes.

## The route

`ChartImmersion f L` hands back a degree `N ≥ 1`, a generating family `s` of global sections of
`L ^⊗ N`, and the assertion that *any* morphism `p : X ⟶ ℙⁿ_S` lying over `S` and pinned on each
chart `X_{sᵢ}` by the coordinate ratios is an immersion. Such a `p` exists unconditionally — it is
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`, the morphism
of Stacks Tag 01NE. It is quasi-compact because `f` is and `ℙⁿ_S ⟶ S` is separated
(`Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated`, the use Tag 07RM's
source makes of [Stacks, Tag 03GI]). That is H-quasi-projectivity, and half 2 of Tag 07RM's own
proof —
`exists_isOpenImmersion_isHProjective_of_isHQuasiProjective`, unconditional — turns it into the
factorisation.

## Main definitions

* `Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform`:
  `Stacks.AmpleImmersionReduction.ChartImmersion` at every scheme, morphism and invertible module,
  in the shape of `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` so that the two
  are comparable line for line.

## Main results

* `Stacks.QuasiProjectiveChartRoute.chartImmersion_of_isImmersion`: `ChartImmersion f L` holds,
  with no further hypothesis, whenever `f` is itself an immersion — so the input below is
  satisfiable and the implications are not vacuous.
* `Stacks.QuasiProjectiveChartRoute.isHQuasiProjective_of_chartImmersion`: **H-quasi-projectivity
  from absolute ampleness and `ChartImmersion` alone.**
* `Stacks.QuasiProjectiveChartRoute.isHQuasiProjective_of_isQuasiProjective_of_isAffine`: **part
  (2) of Stacks Tag 087S over an affine base from `ChartImmersionUniform` alone**, where
  `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine` assumes all of Tag 01VS.
* `Stacks.QuasiProjectiveChartRoute.exists_isOpenImmersion_isHProjective_of_isAffine`: **Tag 07RM's
  conclusion over an affine base**, at `Stacks.HProjective.IsHProjective`, from the same single
  input.
* `Stacks.QuasiProjectiveChartRoute.isHQuasiProjective_of_isAmple_base_of_isAffineHom` and
  `Stacks.QuasiProjectiveChartRoute.exists_isOpenImmersion_isHProjective_of_isAffineHom`: the same
  for an affine morphism over an arbitrary base carrying an ample invertible module, which is where
  the ample sheaf on `S` of the statement does the work.

## Why no tag is attached here

**No Stacks tag attribute is attached anywhere in this file.** The Tag 07RM attribute is on
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`. Every
result below carries hypotheses the source does not —
`Stacks.AmpleImmersionReduction.ChartImmersion` in every case, and in addition either `IsAffine S`
or `IsAffineHom f` with an ample module on `S` — and concludes H-projectivity rather than
Definition 01W8's projectivity.

The conclusion of the tagged statement is Tag 01W8's `IsProjective` in the statement's own
spelling, through Tag 01OB's `projectiveBundle` and its `symmetricAlgebra_projAxioms`, which is
unproved in that spelling; the
library's `AlgebraicGeometry.IsProjective` is the same notion over the library's projective bundle,
and it is the predicate the registered Tag 07RM concludes. The predicate used throughout this file
is the H-projective one, Tag 0C61's `IsProjectiveMorphism`, which is
`Stacks.HProjective.IsHProjective` with the statement's projective space replaced by its library name.

**`IsAffine S` / `IsAffineHom f` are not removed by this file.** Removing them at H-projectivity
would need the passage from relative to absolute ampleness, which in general needs an ample module
on the base; the source's own route through [Stacks, Tag 01VU] and its glueing step
[Stacks, Tag 01VR] is the one the registered Tag 07RM takes, and it lands in Definition 01W8's
projectivity instead.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 03GI](https://stacks.math.columbia.edu/tag/03GI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleImmersionReduction

universe u

namespace Stacks.QuasiProjectiveChartRoute

/-! ### The single input -/

/-- **`Stacks.AmpleImmersionReduction.ChartImmersion` at every situation.** Written in the shape of
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` — the same quantifier prefix over a
scheme, a morphism and an invertible module — so that the two hypotheses are comparable where they
are used. -/
def ChartImmersionUniform : Prop :=
  ∀ (A B : Scheme.{u}) (g : A ⟶ B) (N : A.Modules) [IsInvertibleModule A N],
    ChartImmersion g N

/-! ### The input is satisfiable -/

/-- **`ChartImmersion f L` holds with no further hypothesis when `f` is itself an immersion.**

Every morphism the condition quantifies over lies over `S`, so it is a factor of `f` through
`ℙⁿ_S ⟶ S`, and `AlgebraicGeometry.IsImmersion.of_comp` makes it an immersion. The degree and the
generating family are supplied from ampleness alone by
`Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple`.

Recorded so that the implications below are visibly not implications from a false hypothesis. -/
theorem chartImmersion_of_isImmersion {X S : Scheme.{u}} (f : X ⟶ S) [IsImmersion f]
    (L : X.Modules) [IsInvertibleModule X L] : ChartImmersion f L := by
  intro hL _
  obtain ⟨N, n, s, hN, hgen, -⟩ := exists_generating_family_of_isAmple L hL
  refine ⟨(N : ℤ), n, s, by exact_mod_cast hN, hgen, fun p hpf _ => ?_⟩
  have : IsImmersion (p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) := by rw [hpf]; infer_instance
  exact IsImmersion.of_comp p
    (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))

/-! ### H-quasi-projectivity from the single input -/

/-- **H-quasi-projectivity from absolute ampleness and `ChartImmersion` alone.**

This is `Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple` with
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` replaced by
`Stacks.AmpleImmersionReduction.ChartImmersion`, which is one of the four inputs that gap is
reduced to by `Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist`. The
other three carry the twist identification and the degree range, and neither is used here.

The morphism is `Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`
— Stacks Tag 01NE's morphism, unconditional — pinned on every chart, which is exactly
the hypothesis under which `ChartImmersion` asserts it is an immersion. -/
theorem isHQuasiProjective_of_chartImmersion {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) [LocallyOfFiniteType f] (hqc : QuasiCompact f)
    (hch : ChartImmersion f L) : Stacks.HProjective.IsHQuasiProjective f := by
  obtain ⟨N, n, s, -, hgen, himm⟩ := hch hL inferInstance
  obtain ⟨p, hpf, hchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks s hgen f
  have hi : IsImmersion p := himm p hpf hchart
  rw [← Stacks.HProjective.over_projectiveSpaceOver] at hpf
  have hic : QuasiCompact (p ≫ (projectiveSpaceOver n S ↘ S)) := by rw [hpf]; exact hqc
  exact ⟨n, p, hi,
    Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated p _ inferInstance hic,
      hpf⟩

/-! ### Over an affine base -/

/-- **Part (2) of Stacks Tag 087S over an affine base, from `ChartImmersionUniform` alone.**

`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine` proves the same statement
from `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`, which is the whole of Stacks
Tag 01VS; the two signatures differ in exactly that hypothesis.

Relative ampleness becomes absolute ampleness over an affine base by
`Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine`, and that step is unchanged. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAffine (hch : ChartImmersionUniform.{u})
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (hf : Stacks.HProjective.IsQuasiProjective f) :
    Stacks.HProjective.IsHQuasiProjective f := by
  obtain ⟨⟨hft, hqc⟩, L, hLinv, hLamp⟩ := hf
  have := hLinv
  have := hft
  exact isHQuasiProjective_of_chartImmersion f L
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine f L hLamp) hqc (hch X S f L)

/-- **Stacks Tag 07RM's conclusion over an affine base**, at `Stacks.HProjective.IsHProjective`,
from `ChartImmersionUniform` alone: a quasi-projective morphism to an affine scheme factors as an
open immersion followed by an H-projective morphism.

The factorisation step is half 2 of Tag 07RM's own proof,
`exists_isOpenImmersion_isHProjective_of_isHQuasiProjective`, which is
unconditional and needs no quasi-compactness or quasi-separatedness of the base. -/
theorem exists_isOpenImmersion_isHProjective_of_isAffine (hch : ChartImmersionUniform.{u})
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f :=
  Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective_of_isHQuasiProjective
    (isHQuasiProjective_of_isQuasiProjective_of_isAffine hch f hf)

/-! ### For an affine morphism over an arbitrary base -/

/-- **An affine morphism locally of finite type to a base carrying an ample invertible module is
H-quasi-projective, from `ChartImmersionUniform` alone.**

This is `Stacks.HProjective.isHQuasiProjective_of_isAmple_base_of_isAffineHom` with Stacks Tag 01VS
traded for its second input. The ample module on `X` is the pullback of the one on `S`, by Stacks
Tag 0892 part (2) for an affine morphism, which needs no premise. -/
theorem isHQuasiProjective_of_isAmple_base_of_isAffineHom (hch : ChartImmersionUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] [LocallyOfFiniteType f] (M : S.Modules)
    [IsInvertibleModule S M] (hM : IsAmple S M) : Stacks.HProjective.IsHQuasiProjective f := by
  have hamp := Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom f M hM
  exact isHQuasiProjective_of_chartImmersion f _ hamp inferInstance (hch X S f _)

/-- **Stacks Tag 07RM's conclusion for an affine morphism over a base carrying an ample invertible
module**, at `Stacks.HProjective.IsHProjective`, from `ChartImmersionUniform` alone.

Only the `LocallyOfFiniteType` half of quasi-projectivity is consumed: an affine morphism
inherits an ample module from its target, so the relatively ample module of quasi-projectivity is
never used. -/
theorem exists_isOpenImmersion_isHProjective_of_isAffineHom (hch : ChartImmersionUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] (M : S.Modules) [IsInvertibleModule S M]
    (hM : IsAmple S M) (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f := by
  have := hf.locallyOfFiniteType
  exact
    QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective_of_isHQuasiProjective
    (isHQuasiProjective_of_isAmple_base_of_isAffineHom hch f M hM)

end Stacks.QuasiProjectiveChartRoute

end
