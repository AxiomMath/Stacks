module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackDatum.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmpleFiniteTypeCover.Basic
import Mathlib.Tactic.TFAE

/-!
# Quasi-projectivity over a base carrying an ample invertible sheaf

Over a scheme `S` on which some invertible module is ample, the five conditions of Tag 0B42 on a
morphism `f : X ⟶ S` agree: quasi-projectivity, H-quasi-projectivity, being a quasi-compact open
subscheme of a scheme projective over `S`, finite type together with an ample invertible module on
`X`, and finite type together with an `f`-very ample invertible module.

**Nothing is assumed.** The cycle run here is (1) ⟹ (4) ⟹ (2) ⟹ (1), with (2) ⟹ (3) ⟹ (5) ⟹ (1)
closing the other two conditions, and every step is proved.

An ample module `M` on `S` and a module `L` ample relative to `f` combine, by Tag 0892 part (1),
into an absolutely ample module `L ⊗ f^* M^{⊗ a}` on `X`; and an absolutely ample module on the
source of a morphism of finite type produces, by Tag 01VS, an immersion into `ℙⁿ_S` over `S`. So
quasi-projectivity, H-quasi-projectivity and condition (4) are equivalent with no hypothesis at
all, which is Tag 087S part (2). (1) ⟹ (2) is accordingly proved here rather than cited from Tag
087S, and (5) ⟹ (1) is Tag 01VN against the named twist.

## How (3) is reached and left

(2) ⟹ (3) is Tag 01WA: an H-quasi-projective morphism is a quasi-compact open subscheme of an
H-projective one, and H-projective implies projective.

For (3) ⟹ (5) the source goes through Tag 087S part (1), upgrading the projective morphism
`p : X' ⟶ S` of condition (3) to an H-projective one. That detour is not taken. Condition (3)
hands over a closed immersion `i : X' ⟶ 𝐏(ℰ)` over
`S` — this is what `AlgebraicGeometry.IsProjective` *is* — and `j ≫ i` is then an immersion of `X`
into `𝐏(ℰ)` over `S`, so `(j ≫ i)^* 𝒪_{𝐏(ℰ)}(1)` is `f`-very ample *by the definition* of relative
very ampleness, Tag 01VM. No comparison of `ℙⁿ_S` with `𝐏(𝒪_S^{n+1})` is needed, and so Tag 01VT's
(5) ⟹ (3) — which the source's (2) ⟹ (5) would need in this repository — is not used either.

What (3) ⟹ (5) does need is that `f` be of finite type, which the source gets from "a projective
morphism is of finite type". That is
`AlgebraicGeometry.IsProjective.locallyOfFiniteType` and
`AlgebraicGeometry.IsProjective.quasiCompact` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.FiniteType`, proved there from Tag 07ZY for
the graded algebra `Sym(ℰ)`.

## Main results

* `AlgebraicGeometry.isQuasiProjective_tfae_of_exists_isAmple`: **Tag 0B42**, all five
  conditions, with no hypothesis.
* `AlgebraicGeometry.isHQuasiProjective_of_isQuasiProjective`: **Tag 087S part (2)**,
  unconditionally.
* `AlgebraicGeometry.isProjectiveMorphism_of_isProjective`: **Tag 087S part (1)**,
  unconditionally.
* `AlgebraicGeometry.IsProjective.isQuasiProjective_and_isProper`: the forward implication of
  clause (1) of **Tag 0BCL**, from Tag 07RL and Tag 01WC, with no hypothesis on the base.

## Implementation notes

"`f` is of finite type" is the conjunction of `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact`, the spelling of Tag 01T1 that this repository uses throughout.

Invertibility of the module quantified over in conditions (4) and (5) is existentially bound as
data and reinstated as a local instance, because there is nothing for instance synthesis to key on
while the module is being quantified over.

Quasi-compactness of the open immersion of condition (3) is part of the source's condition and is
not derived; it is what makes the quasi-compactness of `f` available in (3) ⟹ (5), `f` being the
composite of that open immersion with a projective morphism.

## References

* [Stacks Project, Tag 0B42](https://stacks.math.columbia.edu/tag/0B42)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VY](https://stacks.math.columbia.edu/tag/01VY)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.Tag01VMVeryAmple

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### An ample module on the source -/

/-- **The source of a quasi-projective morphism to a base carrying an ample invertible module
carries one too.** If `L` is ample relative to `f : X ⟶ S` and `M` is ample on `S`, then
`L ⊗ f^* M^{⊗ a}` is ample on `X` for every sufficiently large `a`, by [Stacks, Tag 0892]
part (1). -/
theorem exists_isAmple_of_isQuasiProjective (f : X ⟶ S) (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M)
    (hf : IsQuasiProjective f) :
    ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
      letI : Stacks.Ample.IsInvertibleModule X L := hL
      Stacks.Ample.IsAmple X L := by
  obtain ⟨-, L, hL, hample⟩ := hf
  have : Stacks.Ample.IsInvertibleModule X L := hL
  obtain ⟨n, hn⟩ := Stacks.AmplePullbackDatum.exists_threshold_isAmple f L M
    ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mpr hample) hM
  exact ⟨Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M n, inferInstance, hn n le_rfl⟩

/-- **A morphism of finite type whose source carries an ample invertible module is
H-quasi-projective.** [Stacks, Tag 01VS] produces an immersion `i : X ⟶ ℙⁿ_S` over `S`, and it is
quasi-compact because `f` is and `ℙⁿ_S ⟶ S` is separated. No hypothesis on the base is used. -/
theorem isHQuasiProjective_of_exists_isAmple (f : X ⟶ S) (hft : LocallyOfFiniteType f)
    (hqc : QuasiCompact f)
    (h : ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
      letI : Stacks.Ample.IsInvertibleModule X L := hL
      Stacks.Ample.IsAmple X L) :
    IsHQuasiProjective f := by
  obtain ⟨L, hL, hample⟩ := h
  have : Stacks.Ample.IsInvertibleModule X L := hL
  have := hft
  obtain ⟨d₀, -, hd⟩ :=
    Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple f L hample
  obtain ⟨n, i, hi, hif, -⟩ := hd d₀ le_rfl
  rw [← Stacks.HProjective.over_projectiveSpaceOver] at hif
  exact Stacks.HProjective.isHQuasiProjective_of_hasHProjectiveImmersion hqc
    ⟨projectiveSpaceOver n S, projectiveSpaceOver n S ↘ S, i, hi, hif,
      Stacks.HProjective.isHProjective_over n S⟩

/-- **An H-quasi-projective morphism is quasi-projective**, at the `IsQuasiProjective` spelling of
relative ampleness. This is [Stacks, Tag 01VY], transported along
`AlgebraicGeometry.isQuasiProjective_iff_hProjectiveIsQuasiProjective`. -/
theorem isQuasiProjective_of_isHQuasiProjective (f : X ⟶ S) (hf : IsHQuasiProjective f) :
    IsQuasiProjective f :=
  (isQuasiProjective_iff_hProjectiveIsQuasiProjective f).mpr
    (Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f hf)

/-! ### Very ampleness from an immersion into a projective bundle -/

/-- **An immersion over `S` into the projective bundle of a quasi-coherent `𝒪_S`-module gives an
`f`-very ample invertible module**: the pullback of the twist `𝒪_{𝐏(E)}(1)`, which is what
[Stacks, Tag 01VM] asks for, read at
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`.

The immersion is taken as an explicit argument rather than as an instance because the call site
writes the bundle as `Stacks.SymGraded.schemeProjectiveBundle`, which is the same term as
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj (symAlgebra E)` but not syntactically so, and
instance synthesis does not unfold it. -/
theorem exists_isRelativelyVeryAmple_of_immersion_projectiveBundle (f : X ⟶ S) (E : S.Modules)
    [E.IsQuasicoherent]
    (k : X ⟶ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).scheme) (hk : IsImmersion k)
    (hover : k ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).toBase = f) :
    ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
      letI : Stacks.Ample.IsInvertibleModule X L := hL
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L := by
  let := hk
  exact ⟨(Scheme.Modules.pullback k).obj (Stacks.Tag01VMVeryAmple.twistOne E), inferInstance,
    Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_immersion f _ E k hk hover (Iso.refl _)⟩

/-! ### Stacks Tag 087S -/

/-- **A projective morphism is quasi-projective and proper.**

This is the forward implication of clause (1) of [Stacks, Tag 0BCL]. Unlike the equivalence there
it needs no hypothesis on the base at all: quasi-projectivity is [Stacks, Tag 07RL], at
`AlgebraicGeometry.IsProjective.isQuasiProjective`, and properness is [Stacks, Tag 01WC], at
`AlgebraicGeometry.IsProjective.isProper`, and both are proved in this repository with no
condition on `S`. -/
theorem IsProjective.isQuasiProjective_and_isProper {f : X ⟶ S} (hf : IsProjective f) :
    IsQuasiProjective f ∧ IsProper f :=
  ⟨hf.isQuasiProjective, hf.isProper⟩

/-- **Stacks Project, Tag 087S, part (2). Over a base carrying an ample invertible module, a
quasi-projective morphism is H-quasi-projective.**

The relatively ample module of quasi-projectivity and the ample module on the base combine into an
absolutely ample module on `X` by [Stacks, Tag 0892] part (1), and [Stacks, Tag 01VS] turns that
into a quasi-compact immersion into `ℙⁿ_S` over `S`. -/
@[stacks 087S "part (2)"]
theorem isHQuasiProjective_of_isQuasiProjective (f : X ⟶ S) (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M)
    (hf : IsQuasiProjective f) : IsHQuasiProjective f :=
  isHQuasiProjective_of_exists_isAmple f hf.1.1 hf.1.2
    (exists_isAmple_of_isQuasiProjective f M hM hf)

/-- **Stacks Project, Tag 087S, part (1). Over a base carrying an ample invertible module, a
projective morphism is H-projective.**

`AlgebraicGeometry.IsProjective.isQuasiProjective_and_isProper` makes `f` quasi-projective and
proper, from [Stacks, Tag 07RL] and [Stacks, Tag 01WC]; part (2) makes it H-quasi-projective; and
clause (2) of [Stacks, Tag 0BCL] turns H-quasi-projective and proper into H-projective. Nothing is
assumed beyond the source's hypothesis that `M` is an ample invertible module on `S`. -/
@[stacks 087S "part (1)"]
theorem isProjectiveMorphism_of_isProjective
    (f : X ⟶ S) (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M]
    (hM : Stacks.Ample.IsAmple S M) (hf : IsProjective f) : IsProjectiveMorphism f := by
  obtain ⟨hqp, hproper⟩ := hf.isQuasiProjective_and_isProper
  exact isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective f M hM hqp, hproper⟩

/-! ### Stacks Tag 0B42 -/

/-- **Stacks Project, Tag 0B42.** Let `S` be a scheme carrying an ample invertible module and let
`f : X ⟶ S` be a morphism of schemes. The following are equivalent:

1. `f` is quasi-projective;
2. `f` is H-quasi-projective;
3. `X` is a quasi-compact open subscheme, over `S`, of a scheme projective over `S`;
4. `f` is of finite type and `X` carries an ample invertible module;
5. `f` is of finite type and carries an `f`-very ample invertible module.

The cycle is (1) ⟹ (4) ⟹ (2) ⟹ (1), with (2) ⟹ (3), (3) ⟹ (5) and (5) ⟹ (1) closing the
remaining conditions. Nothing is assumed. -/
@[stacks 0B42 "all five conditions, with no hypothesis"]
theorem isQuasiProjective_tfae_of_exists_isAmple (f : X ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M) :
    List.TFAE
      [IsQuasiProjective f,
        IsHQuasiProjective f,
        ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (j : X ⟶ X'),
          IsOpenImmersion j ∧ QuasiCompact j ∧ j ≫ p = f ∧ IsProjective p,
        (LocallyOfFiniteType f ∧ QuasiCompact f) ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Ample.IsAmple X L,
        (LocallyOfFiniteType f ∧ QuasiCompact f) ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L] := by
  obtain ⟨M, hM, hSample⟩ := hS
  have : Stacks.Ample.IsInvertibleModule S M := hM
  tfae_have 1 → 4 := fun hf => ⟨hf.1, exists_isAmple_of_isQuasiProjective f M hSample hf⟩
  tfae_have 4 → 2 := fun hf => isHQuasiProjective_of_exists_isAmple f hf.1.1 hf.1.2 hf.2
  tfae_have 2 → 1 := isQuasiProjective_of_isHQuasiProjective f
  tfae_have 2 → 3 := by
    intro hf
    obtain ⟨X', j, p, hj, hp, hjp⟩ :=
      exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective hf
    have := isProper_of_isProjectiveMorphism p hp
    have : QuasiCompact (j ≫ p) := hjp ▸ hf.quasiCompact
    exact ⟨X', p, j, hj, QuasiCompact.of_comp j p, hjp, hp.isProjective⟩
  tfae_have 3 → 5 := by
    rintro ⟨X', p, j, hj, hjqc, hjp, hp⟩
    have := hp.locallyOfFiniteType
    have := hp.quasiCompact
    obtain ⟨E, hq, -, hqc, i, hi, hip⟩ := hp
    have : E.IsQuasicoherent := hq
    have : IsClosedImmersion i := hi
    have himm : IsImmersion (j ≫ i) := inferInstance
    have hover : (j ≫ i) ≫ (Stacks.SymGraded.schemeProjectiveBundle E hqc).toBase = f := by
      rw [Category.assoc, hip, hjp]
    exact ⟨hjp ▸ ⟨inferInstance, inferInstance⟩,
      exists_isRelativelyVeryAmple_of_immersion_projectiveBundle f E (j ≫ i) himm hover⟩
  tfae_have 5 → 1 := by
    rintro ⟨⟨hft, hqc⟩, L, hL, hvamp⟩
    have : Stacks.Ample.IsInvertibleModule X L := hL
    exact ⟨⟨hft, hqc⟩, L, hL,
      (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mp
        (Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f L hqc hvamp)⟩
  tfae_finish

end AlgebraicGeometry

end
