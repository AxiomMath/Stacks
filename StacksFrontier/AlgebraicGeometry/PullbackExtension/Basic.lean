module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Pullback

/-!
# [Stacks, Tag 01PW] for the pullback of an ample module, with no ampleness of the pullback

`StacksFrontier/AlgebraicGeometry/AmplePullbackPart1/Basic.lean` reduces part (1) of
[Stacks, Tag 0892] — and through it part (2) of [Stacks, Tag 087S] — to one pointwise datum,
`Stacks.AmplePullbackPart1.EventualAffineDatum`, and states under "The one missing input,
precisely" exactly what producing that datum needs:

> for `X` quasi-compact and quasi-separated, `N` invertible, `σ` a global section of `N ^⊗ m`
> with `m ≥ 1`, `F` invertible, and `s` a section of `F` over `X_σ`, there are `e ≥ 1` and
> `s' : Γ(F ⊗ N ^⊗ (m e), ⊤)` with `s'|_{X_σ} = s ⊗ (σ ^ e)|_{X_σ}`

with `N = f^* M`, and records that "dropping the ampleness of `N` is the genuine content of Tag
01PW that the repository does not have".

**That input is available, and this file instantiates it at `N = f^* M`.** The statement above is
`Stacks.SectionExtensionNoAmple.exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing`,
which replaces ampleness of the twisting module by
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` — and that hypothesis holds for the
pullback of an ample module along an **arbitrary** morphism, by
`Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_pullbackModule_of_isAmple`, with no
ampleness of the pullback anywhere. Only the two topological hypotheses on `X` have to be
supplied; see below.

## The quasi-separatedness hypothesis

`AmplePullbackPart1/Basic.lean` supplies `CompactSpace X` from the hypotheses of the statement
(`Stacks.AmplePullbackPart1.compactSpace_of_isAmple`) and then says of the other, under "Where
quasi-separatedness of `X` itself still stops", that assembling `QuasiSeparatedSpace X` from the
two halves it has is

> blocked by tooling, not by mathematics … `AlgebraicGeometry.IsZariskiLocalAtTarget
> @QuasiSeparated` is not synthesizable either, for the same reason. So the last step is one
> `set_option` away and is left undone deliberately.

**No `set_option` is needed.** The instance that does not synthesize here is
`AlgebraicGeometry.HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)`, and
it becomes `inferInstance` under

    attribute [local implicit_reducible] CategoryTheory.MorphismProperty
      AlgebraicGeometry.AffineTargetMorphismProperty

which is an attribute, not a compiler option. With the attribute out
of scope the instance fails with *"failed to synthesize instance of type class
`HasAffineProperty @QuasiSeparated fun X x x_1 x_2 ↦ QuasiSeparatedSpace ↥X`"*; with it in scope
`inferInstance` closes it. So `Stacks.Tag087SPullbackExtension.quasiSeparated_of_isRelativelyAmple`
is the affine-local characterisation applied directly, in four lines, and
`quasiSeparatedSpace_of_isRelativelyAmple` is the composition of the two halves.

The two halves it composes are the ones that file already identified: `S` is quasi-separated by
`Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple` applied to `M`, and `f⁻¹(V)` is
quasi-separated for every affine open `V` of `S` by the same lemma applied to the restriction of
`L`, which relative ampleness ([Stacks, Tag 01VH], `Stacks.RelativeAmple.IsRelativelyAmple`)
asserts is ample. Nothing new is proved about either half.

## Main results

* `Stacks.Tag087SPullbackExtension.quasiSeparated_of_isRelativelyAmple`: **a morphism carrying a
  relatively ample invertible module is quasi-separated.** The preimage of every affine open of
  the base carries an ample module, hence is a quasi-separated space, and quasi-separatedness of
  a morphism is affine-local on the target.
* `Stacks.Tag087SPullbackExtension.quasiSeparatedSpace_of_isRelativelyAmple`: **the source of a
  morphism with a relatively ample module over a base with an ample module is a quasi-separated
  space** — the step `AmplePullbackPart1/Basic.lean` records as left undone.
* `Stacks.Tag087SPullbackExtension.exists_tensorPow_tensorSection_pullbackModule`: **[Stacks, Tag
  01PW] for a module-valued coefficient and the twisting module `f^* M`, with no ampleness of
  `f^* M`** — the single input that `AmplePullbackPart1/Basic.lean` isolates as missing for
  part (1) of [Stacks, Tag 0892], with both of its topological hypotheses discharged from the
  hypotheses of [Stacks, Tag 087S] part (2) and nothing else assumed.

## What is still owed for part (1) of [Stacks, Tag 0892], and therefore for Tag 087S part (2)

`Stacks.AmplePullbackPart1.EventualAffineDatum` is **not** proved here, so neither
`Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` nor part (2) of Tag 087S moves. What
remains between this file and that datum is exactly the two bookkeeping points
`AmplePullbackPart1/Basic.lean` lists beside Tag 01PW under "What is not done", and they are
about *non-global* sections rather than about Tag 01PW:

1. the nonvanishing open of a section of a module over an open subscheme, and its compatibility
   with restriction along the open immersion — `Stacks.Ample.nonvanishingLocus` is defined for
   global sections only, as `AmplePullbackPart1/Restriction.lean` records under "What this does
   *not* give", so the affine open that ampleness of `U.ι^* L` produces on `U.toScheme` cannot
   yet be compared with the nonvanishing open of the section of `L ^⊗ n` over `U` that
   `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` builds from it;
2. the `m`-th power of such a section, which is what removes the divisibility condition the
   source's own proof carries.

The global analogues of both are in the library (`Stacks.SectionProduct.nonvanishingOpen_mul`,
`Stacks.NonvanishingPullback.preimage_nonvanishingLocus`). Note also that the final section of
the intended argument is `τ ⊗ σ ^ b` with `b ≥ 1` and not `τ` itself: Tag 01PW pins `τ` only on
`X_σ`, so `X_τ` need not lie inside `X_σ`, and it is the factor `σ ^ b` that cuts the
nonvanishing open down to the affine `V` off `X_σ`.

## No tag is attached

Neither label of [Stacks, Tag 087S] is closed by this file and no 087S attribute is attached
anywhere in it. Both are proved elsewhere, as
`AlgebraicGeometry.isHQuasiProjective_of_isQuasiProjective` (part (2)) and
`AlgebraicGeometry.isProjectiveMorphism_of_isProjective` (part (1)), in
`StacksFrontier/AlgebraicGeometry/Morphisms/Projective/QuasiProjectiveOverAmpleBase.lean`. The route
of `Stacks.Tag087SAmpleRoute.isHQuasiProjective_of_isQuasiProjective_of_isAmple` takes
`Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` and
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` as arguments (the second holds,
as `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`), and this file removes
neither.

No label of [Stacks, Tag 0892] or [Stacks, Tag 01PW] is closed either. Part (2) of Tag 0892 is
already tagged elsewhere (`../SectionRatioNoAmple/Pullback.lean`); part (1) still stands on the
datum above. Tag 01PW has four labels and
`Stacks.Tag087SPullbackExtension.exists_tensorPow_tensorSection_pullbackModule` is one of them
specialised to a particular twisting module, so it earns nothing there.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory
open Stacks.SectionExtensionNoAmple
open Stacks.SectionExtension (resTop)
open Stacks.SectionTensorFormula (tensorSection)

universe u

namespace Stacks.Tag087SPullbackExtension

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) (M : S.Modules)
  [IsInvertibleModule X L] [IsInvertibleModule S M]

/-! ### Quasi-separatedness, the hypothesis of Tag 01PW that was recorded as blocked -/

section QuasiSeparated

attribute [local implicit_reducible] CategoryTheory.MorphismProperty
  AlgebraicGeometry.AffineTargetMorphismProperty

/-- **A morphism carrying a relatively ample invertible module is quasi-separated.**

Relative ampleness ([Stacks, Tag 01VH]) says that the restriction of `L` to `f⁻¹(V)` is ample for
every affine open `V` of `S`, and a scheme carrying an ample invertible module is a
quasi-separated space (`Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`, the first
paragraph of the proof of [Stacks, Tag 01PY]). Quasi-separatedness of a morphism is affine-local
on the target, so the two fit together with nothing in between.

The affine-local step is `AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top` at the instance
`HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)`, over the family of
*all* affine opens of `S`, whose supremum is `⊤` by
`AlgebraicGeometry.iSup_affineOpens_eq_top`. That instance does not synthesize at this pin, which
is what `StacksFrontier/AlgebraicGeometry/AmplePullbackPart1/Basic.lean` records as leaving this
composition "one `set_option` away"; the local `implicit_reducible` attribute above makes it
`inferInstance`, and no compiler option is used. -/
theorem quasiSeparated_of_isRelativelyAmple (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    QuasiSeparated f := by
  refine HasAffineProperty.of_iSup_eq_top (P := @QuasiSeparated)
    (fun V : S.affineOpens => V) (iSup_affineOpens_eq_top S) ?_
  intro V
  exact Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple _
    (hL.isAmple_preimage f L V.1 V.2)

/-- **The source of a morphism carrying a relatively ample module over a base carrying an ample
module is a quasi-separated space.**

This is the composition `StacksFrontier/AlgebraicGeometry/AmplePullbackPart1/Basic.lean` names
and leaves undone: `S` is quasi-separated by
`Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple` applied to `M`, `f` is quasi-separated
by `Stacks.Tag087SPullbackExtension.quasiSeparated_of_isRelativelyAmple`, and
`AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` concludes.

Together with `Stacks.AmplePullbackPart1.compactSpace_of_isAmple` this is the whole hypothesis of
[Stacks, Tag 01PW] on `X`, available from the hypotheses of part (2) of [Stacks, Tag 087S] with
nothing added. -/
theorem quasiSeparatedSpace_of_isRelativelyAmple
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (hM : IsAmple S M) :
    QuasiSeparatedSpace X :=
  let : QuasiSeparatedSpace S := Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple M hM
  let : QuasiSeparated f := quasiSeparated_of_isRelativelyAmple f L hL
  quasiSeparatedSpace_of_quasiSeparated f

end QuasiSeparated

/-! ### Tag 01PW at the twisting module `f^* M` -/

section Extension

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **[Stacks, Tag 01PW] for a module-valued coefficient and the twisting module `f^* M`, with no
ampleness of `f^* M`.**

For `L` ample relative to `f : X ⟶ S` and `M` ample on `S`, `F` quasi-coherent on `X`, `n ≥ 1`
and `s` a global section of `(f^* M) ^⊗ n`: every section `t` of `F` over the nonvanishing open
of `s` extends, after twisting, to a global section. Precisely, there are a degree `p` divisible
by `n`, a global section `σ` of `(f^* M) ^⊗ p` with the *same* nonvanishing open as `s`, and a
global section `τ` of `F ⊗ (f^* M) ^⊗ p` restricting on that open to `t ⊗ σ`.

This is the input that
`StacksFrontier/AlgebraicGeometry/AmplePullbackPart1/Basic.lean` isolates under "The one missing
input, precisely" and calls "the genuine content of Tag 01PW that the repository does not have",
and that `Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` repeats as "no statement in the
repository extends a
section of an invertible `F` over `X_σ` to a global section of `F ⊗ N ^⊗ e`". **It is available**,
as
`Stacks.SectionExtensionNoAmple.exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing`,
which asks of the twisting module only
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` and not ampleness — and that hypothesis
holds for `f^* M` with `f` arbitrary by
`Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_pullbackModule_of_isAmple`, which needs
only ampleness of `M` on the base.

So all this theorem does is discharge the three hypotheses from the data of part (2) of
[Stacks, Tag 087S]: the pointwise nonvanishing by that lemma, `CompactSpace X` by
`Stacks.AmplePullbackPart1.compactSpace_of_isAmple`, and `QuasiSeparatedSpace X` by
`Stacks.Tag087SPullbackExtension.quasiSeparatedSpace_of_isRelativelyAmple`. No ampleness of
`f^* M` is used anywhere, which is the circularity the two records above were describing: the
ampleness of `f^* M` is part (2) of [Stacks, Tag 0892], which the source deduces *from* part (1).

The ampleness of `L` enters only through `CompactSpace X`, where relative ampleness supplies
quasi-compactness of `f`; the extension statement itself is indifferent to `L`. -/
theorem exists_tensorPow_tensorSection_pullbackModule
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (hM : IsAmple S M)
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (hn : 1 ≤ n)
    (s : Γ(tensorPowModule X (Stacks.AmpleLocallyClosed.pullbackModule f M) (n : ℤ), ⊤))
    (t : Γ(F, powNonvanishingOpen X (Stacks.AmpleLocallyClosed.pullbackModule f M) n s)) :
    ∃ (p : ℕ)
      (σ : Γ(tensorPowModule X (Stacks.AmpleLocallyClosed.pullbackModule f M) (p : ℤ), ⊤))
      (τ : Γ(F ⊗ tensorPowModule X (Stacks.AmpleLocallyClosed.pullbackModule f M) (p : ℤ), ⊤)),
      n ∣ p ∧
      powNonvanishingOpen X (Stacks.AmpleLocallyClosed.pullbackModule f M) n s =
          powNonvanishingOpen X (Stacks.AmpleLocallyClosed.pullbackModule f M) p σ ∧
        resTop (powNonvanishingOpen X (Stacks.AmpleLocallyClosed.pullbackModule f M) n s) τ =
          tensorSection F
            (tensorPowModule X (Stacks.AmpleLocallyClosed.pullbackModule f M) (p : ℤ)) t
            (resTop (powNonvanishingOpen X (Stacks.AmpleLocallyClosed.pullbackModule f M) n s)
              σ) :=
  let : CompactSpace X := Stacks.AmplePullbackPart1.compactSpace_of_isAmple f L M hL hM
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_isRelativelyAmple f L M hL hM
  exists_tensorPow_tensorSection_of_hasPointwiseNonvanishing _
    (hasPointwiseNonvanishing_pullbackModule_of_isAmple f M hM) F hn s t

end Extension

end Stacks.Tag087SPullbackExtension

end
