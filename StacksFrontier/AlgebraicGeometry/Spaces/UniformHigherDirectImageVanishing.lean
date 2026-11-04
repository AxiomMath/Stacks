module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# A base-change-uniform vanishing bound for the higher direct images

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S`.  [Stacks, Tag 073G] asserts that there is a single integer `n(X → Y)`, depending on
`f` alone, such that for *every* algebraic space `Y'`, *every* morphism `Y' ⟶ Y` and *every*
quasi-coherent module `𝓕'` on `X' = Y' ×_Y X` the higher direct images `R^i f'_*𝓕'` vanish for
`i ≥ n(X → Y)`.  The order of the quantifiers is the whole content: the bound is chosen before
the base change and before the coefficient module.

This file proves the step of the source's argument which is responsible for that uniformity in
`Y'`: **the bound for an arbitrary base follows, with the same bound, from the bound for bases
that are schemes.**  A module on the small étale site of `Y'` is zero as soon as its restriction
to every étale scheme chart `V'` of `Y'` is zero, and over such a chart the restriction of
`R^i f'_*𝓕'` is the degree-`i` higher direct image along the base change of `f` to `V'` — a base
change of `f` whose base `V'` *is* a scheme.  So one application of the scheme-base case, at a
chart of `Y'` rather than at `Y'` itself, discharges the arbitrary-base case; and since the
chart varies while the bound does not, the uniformity over `Y'` is genuinely produced here and
not assumed.

## Main definitions

* `AlgebraicGeometry.Space.IsRepresentableSpace`: an algebraic space over `S` is representable,
  that is, *is a scheme*, when its presheaf is isomorphic to a representable presheaf of the big
  fppf site.
* `AlgebraicGeometry.Space.SchemeBaseUniformVanishing`: the hypothesis `hscheme` carried below —
  the vanishing bound `N` for every base change of `f` along a morphism from a representable
  algebraic space.

## Main results

* `AlgebraicGeometry.Space.isRepresentableSpace_chartSpace`: an étale scheme chart of an
  algebraic space is a representable algebraic space.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_schemeBase`: the reduction,
  at a fixed bound `N`.
* `AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_modulePushforward`:
  **[Stacks, Tag 073G]** in its existential form, with the quantifiers of the source — one `N`,
  then every base change, then every quasi-coherent module, then every degree `≥ N`.

## Implementation notes

**Which half of the source's proof is here, and which is carried.**  The source argues in four
steps: (1) replace `Y` by an affine scheme `V` surjective étale over it, by [Stacks, Tag 03H6],
using the base-change compatibility [Stacks, Tag 03LX]; (2) reduce the quantifier over `Y'` to
affine schemes `Y'`; (3) for such a `Y'` deduce `R^i f'_*𝓕' = 0` from `H^i(X', 𝓕') = 0`, by the
quasi-coherence of the higher direct images [Stacks, Tag 0720] and the identification
`H^i(X', 𝓕') = H^0(Y', R^i f'_*𝓕')` of [Stacks, Tag 0733]; and (4) produce the bound itself from
the choices of [Stacks, Tag 072C], which base-change.  What is proved here is step (2), and in a
form that makes step (1) unnecessary: étale scheme charts of `Y'` are a detecting family for the
zero module (`AlgebraicGeometry.Space.isZero_iff_forall_isZero_etaleModulePullback_chartToSpace`),
so no surjective étale cover of `Y` has to be chosen and [Stacks, Tag 03H6] is not used.  Steps
(3) and (4) — everything that produces a number — are the hypothesis
`AlgebraicGeometry.Space.SchemeBaseUniformVanishing`, which is **not** proved here.  Its ingredient
[Stacks, Tag 072C] is in this development only with its own `h072B` carried
(`AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBase_of_isQuasiCompactSpace`), its
ingredient [Stacks, Tag 0720] only up to its affine-base case
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart`) and its
ingredient [Stacks, Tag 0733] only with three hypotheses carried
(`AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage`), so the affine case of the
bound cannot be assembled here.

**The reduction is to schemes, not to affine schemes.**  The source reduces to an affine base;
the detecting family used here is all étale scheme charts, so the hypothesis carried below is
the case of a base that is any scheme.  That is a *stronger* hypothesis than the source's affine
case, and the gap — the passage from a scheme base to an affine one, which is Zariski-local on
the base — is not bridged here.

**`h03F3`.**  The identification of `(R^i f'_*𝓕')|_{V'}` with the higher direct image along the
base change of `f'` to `V'` is the higher-direct-image clause of [Stacks, Tag 03LX], which this
development has as `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso`.  For a
chart base change along a non-representable `f'` the top arrow `V' ×_{Y'} X' ⟶ X'` is an étale
morphism of algebraic spaces and not the structure morphism of a scheme chart, so the
injective-preservation half of [Stacks, Tag 03F3], part (1), is needed for an arbitrary étale
morphism rather than in the chart form
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback_chartToSpace`.  It is
carried as `h03F3` in the statements below, in the form of a statement about every étale
morphism of algebraic spaces over `S`; it is discharged by
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`, and the conditional
form of the clause that consumes it is
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives`.

**Quasi-compactness of `Y` is not assumed.**  Hypothesis (2) of the source is used only in its
step (1), to choose the affine étale cover `V ⟶ Y`; the reduction proved here does not choose
one, so `IsQuasiCompactSpace` for `Y` is absent from the statements below.  Dropping a hypothesis
strengthens them.  Quasi-compactness and quasi-separatedness of `f`, hypothesis (1) of the
source, *are* assumed, and are used: they are what makes the base-changed morphism
`V' ×_{Y'} X' ⟶ V'` quasi-compact and quasi-separated, which is how `hscheme` is allowed to
demand those two properties of the base change it is applied to, and so is weaker than it would
otherwise be.

**Degrees.**  `R^i f'_*` is Mathlib's `CategoryTheory.Functor.rightDerived`, indexed by `ℕ`;
negative degrees do not occur, so an `ℕ`-indexed bound is the source's integer bound.  Vanishing
is the categorical predicate `IsZero`, and quasi-coherence is
`SheafOfModules.IsQuasicoherentOnSite`, that is [Stacks, Tag 03DL], part (6), on the small étale
site.

## References

* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Representable algebraic spaces -/

/-- An algebraic space over `S` is **representable**, that is, *is a scheme*, when its presheaf
is isomorphic to the presheaf represented by an object of the big fppf site over `S`.

Every such presheaf is an algebraic space, by [Stacks, Tag 025Z]; the condition is stated up to
isomorphism because being a scheme is invariant under isomorphism of algebraic spaces. -/
def IsRepresentableSpace (Y : AlgebraicSpaces B S hS) : Prop :=
  ∃ T : BigFppfOver B S hS, Nonempty (Y.1 ≅ yoneda.obj T)

/-- An étale scheme chart of an algebraic space is a representable algebraic space: the presheaf
of `AlgebraicGeometry.Space.chartSpace` is by definition the one represented by the scheme
underlying the chart. -/
theorem isRepresentableSpace_chartSpace (Z : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Z.1) : IsRepresentableSpace B S hS (chartSpace B S hS Z V) :=
  ⟨(SmallEtale.toOver B S hS Z.1).obj V, ⟨Iso.refl _⟩⟩

/-! ### The carried hypothesis: the vanishing bound over a scheme base -/

/-- The hypothesis `hscheme` of the two theorems below: the degree `N` works for every base
change of `f` along a morphism `Y'' ⟶ Y` whose source is a *representable* algebraic space, and
uniformly in the quasi-coherent module on the base change.

The base change is asked to be quasi-compact and quasi-separated; both follow from the
corresponding properties of `f` by [Stacks, Tag 03HF] and [Stacks, Tag 03KL], part (3), so
demanding them only weakens the hypothesis.

For an *affine* base this is steps (3) and (4) of the proof of [Stacks, Tag 073G]: the
quasi-coherence of the higher direct images, [Stacks, Tag 0720], and the identification
`H^i(X'', 𝓕'') = H^0(Y'', R^i f''_*𝓕'')` of [Stacks, Tag 0733], reduce the vanishing to that of
`H^i(X'', 𝓕'')`, which holds above the bound `max (p + d_p)` read off from the choices of
[Stacks, Tag 072C] — choices which survive base change, which is why the resulting integer
depends on `f` alone.  None of those three tags is available unconditionally in this
development; see the implementation notes of this file. -/
def SchemeBaseUniformVanishing {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (N : ℕ) : Prop :=
  ∀ (Y'' X'' : AlgebraicSpaces B S hS) (g : Y'' ⟶ Y) (i : X'' ⟶ X) (f'' : X'' ⟶ Y''),
    IsPullback i f'' f g → IsRepresentableSpace B S hS Y'' →
    IsQuasiCompact B S hS f''.hom → IsQuasiSeparated B S hS f''.hom →
    ∀ F : Modules.{u, u} B S hS X''.1 X''.2, F.IsQuasicoherentOnSite → ∀ q : ℕ, N ≤ q →
      have := hasInjectiveResolutions_modules B S hS X''.1 X''.2
      IsZero (((modulePushforward B S hS f'').rightDerived q).obj F)

/-! ### The reduction of an arbitrary base to a scheme base -/

/-- **Step (2) of the proof of [Stacks, Tag 073G]: an arbitrary base is reduced to a scheme
base, with the same bound.**

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S` and
let `N` be a degree which bounds the vanishing of the higher direct images for every base change
of `f` to a *representable* base, uniformly in the quasi-coherent coefficient module.  Then `N`
bounds it for *every* base change of `f`, again uniformly in the coefficient module.

The proof is the source's: a module on the small étale site of `Y'` is zero as soon as all of its
restrictions to the étale scheme charts of `Y'` are, and the restriction of `R^q f'_*𝓕'` to a
chart `V'` is the degree-`q` higher direct image of `𝓕'|_{V' ×_{Y'} X'}` along the base change of
`f'` to `V'`, by the higher-direct-image clause of [Stacks, Tag 03LX].  That base change is also
a base change of `f`, by pasting the two cartesian squares, its base `V'` is representable, and
its coefficient module is quasi-coherent because quasi-coherence is inherited by étale pullbacks;
so `hscheme` applies to it.

`h03F3` is the injective-preservation half of [Stacks, Tag 03F3], part (1), for the modules on
the small étale sites: it is what the cited clause of [Stacks, Tag 03LX] needs and this
development does not prove.  Quasi-compactness of `Y`, hypothesis (2) of the source, is not
needed and not assumed. -/
theorem isZero_rightDerived_modulePushforward_of_schemeBase {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (N : ℕ)
    (h03F3 : ∀ (Z W : AlgebraicSpaces B S hS) (i : W ⟶ Z) (hi : IsEtale B S hS i.hom),
      (etaleModulePullback.{u, u} B S hS i hi).PreservesInjectiveObjects)
    (hscheme : SchemeBaseUniformVanishing B S hS f N)
    (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback i' f' f g) (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hF' : F'.IsQuasicoherentOnSite) (q : ℕ) (hq : N ≤ q) :
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    IsZero (((modulePushforward B S hS f').rightDerived q).obj F') := by
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  rw [isZero_iff_forall_isZero_etaleModulePullback_chartToSpace]
  intro V'
  have hpaste : IsPullback (chartBaseChangeInclusion B S hS f' V' ≫ i')
      (chartBaseChangeProjection B S hS f' V') f (chartToSpace B S hS Y' V' ≫ g) :=
    (isPullback_chartBaseChangeInclusion B S hS f' V').paste_horiz sq
  have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f' V').1
    (chartBaseChangeSpace B S hS f' V').2
  refine IsZero.of_iso ?_
    ((moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives B S hS
      (chartBaseChangeInclusion B S hS f' V')
      (chartBaseChangeProjection B S hS f' V') f' (chartToSpace B S hS Y' V')
      (isPullback_chartBaseChangeInclusion B S hS f' V')
      (isEtale_chartToSpace B S hS Y' V') (h03F3 _ _ _ _) q).app F').symm
  exact hscheme (chartSpace B S hS Y' V') (chartBaseChangeSpace B S hS f' V')
    (chartToSpace B S hS Y' V' ≫ g) (chartBaseChangeInclusion B S hS f' V' ≫ i')
    (chartBaseChangeProjection B S hS f' V') hpaste
    (isRepresentableSpace_chartSpace B S hS Y' V')
    (isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ hpaste) hfqc)
    (isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ hpaste) hfqs)
    ((chartBaseChangeModulePullback B S hS f' V').obj F')
    (isQuasicoherentOnSite_etaleModulePullback B S hS _
      (isEtale_chartBaseChangeInclusion B S hS f' V') F' hF') q hq

/-! ### Stacks 073G -/

/-- **[Stacks, Tag 073G], with the scheme-base case carried.**  Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of algebraic spaces over `S`.  Then there is a single
degree `n(X → Y)` such that for every algebraic space `Y'`, every morphism `Y' ⟶ Y`, every
algebraic space `X'` making `X' ⟶ X`, `X' ⟶ Y'` a cartesian square over `f`, and every
quasi-coherent `𝒪_{X'}`-module `𝓕'`, the higher direct images `R^q f'_*𝓕'` vanish for
`q ≥ n(X → Y)`.

The quantifiers are the source's and in the source's order: `n(X → Y)` is produced once and for
all from `f`, before any base change and before any coefficient module.  The uniformity in `Y'`
is what `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_schemeBase` supplies;
the integer itself comes from `hscheme`, the case of a base which is a scheme, which is **not**
proved in this development. -/
@[stacks 073G "the source's quantifier order -- one n from f alone, outside the base change, \
the module and the degree -- and step (2) of its proof, the reduction of an arbitrary base to a \
scheme base. No number is produced: hscheme (that bound over a scheme base: Stacks 0720, 0733 \
and 072C) and h03F3 (Stacks 03F3(1), needed by 03LX) are carried; Y quasi-compact not assumed"]
theorem exists_forall_isZero_rightDerived_modulePushforward {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (h03F3 : ∀ (Z W : AlgebraicSpaces B S hS) (i : W ⟶ Z) (hi : IsEtale B S hS i.hom),
      (etaleModulePullback.{u, u} B S hS i hi).PreservesInjectiveObjects)
    (hscheme : ∃ N : ℕ, SchemeBaseUniformVanishing B S hS f N) :
    ∃ N : ℕ, ∀ (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback i' f' f g →
      ∀ F' : Modules.{u, u} B S hS X'.1 X'.2, F'.IsQuasicoherentOnSite → ∀ q : ℕ, N ≤ q →
        have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
        IsZero (((modulePushforward B S hS f').rightDerived q).obj F') := by
  obtain ⟨N, hN⟩ := hscheme
  exact ⟨N, fun Y' X' g i' f' sq F' hF' q hq =>
    isZero_rightDerived_modulePushforward_of_schemeBase B S hS f hfqc hfqs N h03F3 hN
      Y' X' g i' f' sq F' hF' q hq⟩

/-! ### Stacks 073G for a representable morphism, with `h03F3` discharged -/

/-- **Step (2) of the proof of [Stacks, Tag 073G] for a representable morphism, carrying nothing
but the scheme-base case.**

For a representable `f` the fibre product `V' ×_{Y'} X'` is an étale scheme *chart* of `X'`, so
the identification of `(R^q f'_*𝓕')|_{V'}` with the higher direct image along the base change is
Equation 69.3.0.1 of the source, [Stacks, Tag 071Z], in which the injective-preservation half of
[Stacks, Tag 03F3] is proved rather than assumed
(`AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`).  The hypothesis `h03F3` of
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_schemeBase` therefore disappears
here.

Representability of the base change `f'` is Mathlib's
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback` for
`CategoryTheory.Functor.relativelyRepresentable`, read on the cartesian square of presheaves
underlying `sq`. -/
theorem isZero_rightDerived_modulePushforward_of_schemeBase_of_representable
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) (N : ℕ)
    (hscheme : SchemeBaseUniformVanishing B S hS f N)
    (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback i' f' f g) (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hF' : F'.IsQuasicoherentOnSite) (q : ℕ) (hq : N ≤ q) :
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    IsZero (((modulePushforward B S hS f').rightDerived q).obj F') := by
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  have hf' : yoneda.relativelyRepresentable f'.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AlgebraicSpaces.isPullback_hom _ _ _ sq) hf
  rw [isZero_iff_forall_isZero_etaleModulePullback_chartToSpace]
  intro V'
  have hpaste : IsPullback
      (chartToSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V') ≫ i')
      (smallBaseChangeChartMap B S hS f' hf' V') f (chartToSpace B S hS Y' V' ≫ g) :=
    (isPullback_smallBaseChangeChart B S hS f' hf' V').paste_horiz sq
  have := hasInjectiveResolutions_modules B S hS
    (chartSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V')).1
    (chartSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V')).2
  refine IsZero.of_iso ?_
    ((moduleHigherPushforwardChartBaseChangeIso B S hS f' hf' V' q).app F').symm
  exact hscheme (chartSpace B S hS Y' V')
    (chartSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V'))
    (chartToSpace B S hS Y' V' ≫ g)
    (chartToSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V') ≫ i')
    (smallBaseChangeChartMap B S hS f' hf' V') hpaste
    (isRepresentableSpace_chartSpace B S hS Y' V')
    (isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ hpaste) hfqc)
    (isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ hpaste) hfqs)
    ((etaleModulePullback B S hS
      (chartToSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V'))
      (isEtale_chartToSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V'))).obj F')
    (isQuasicoherentOnSite_etaleModulePullback B S hS _
      (isEtale_chartToSpace B S hS X' ((smallBaseChange B S hS f' hf').obj V')) F' hF') q hq

/-- **[Stacks, Tag 073G] for a representable morphism, with only the scheme-base case carried.**
Let `f : X ⟶ Y` be a representable, quasi-compact and quasi-separated morphism of algebraic
spaces over `S`.  Then there is a single degree `n(X → Y)` above which every higher direct image
of every quasi-coherent module along every base change of `f` vanishes.

This is `AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_modulePushforward` with the
injective-preservation hypothesis `h03F3` discharged by representability. -/
@[stacks 073G "the same for a REPRESENTABLE f, with h03F3 discharged: there the chartwise \
identification is Stacks 071Z, which proves Stacks 03F3(1). hscheme is still carried and Y \
quasi-compact is still not assumed"]
theorem exists_forall_isZero_rightDerived_modulePushforward_of_representable
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hscheme : ∃ N : ℕ, SchemeBaseUniformVanishing B S hS f N) :
    ∃ N : ℕ, ∀ (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback i' f' f g →
      ∀ F' : Modules.{u, u} B S hS X'.1 X'.2, F'.IsQuasicoherentOnSite → ∀ q : ℕ, N ≤ q →
        have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
        IsZero (((modulePushforward B S hS f').rightDerived q).obj F') := by
  obtain ⟨N, hN⟩ := hscheme
  exact ⟨N, fun Y' X' g i' f' sq F' hF' q hq =>
    isZero_rightDerived_modulePushforward_of_schemeBase_of_representable B S hS f hf hfqc hfqs N
      hN Y' X' g i' f' sq F' hF' q hq⟩

end AlgebraicGeometry.Space

end
