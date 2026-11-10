module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology

/-!
# Conclusion (a) of Tag 0EX3: higher direct images still vanish after base change

[Stacks, Tag 0EX3] fixes a morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes and a
degree `d` above which the higher direct images of every quasi-coherent module vanish, together
with a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

and asserts as its conclusion (a) that `Rⁱ f'_* F' = 0` for `i > d` and every quasi-coherent
`𝒪_{X'}`-module `F'`. This file proves that conclusion, unconditionally.

The reduction to the case of an affine base was already available as
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_affineCase`,
which carried the affine case as an explicit hypothesis `haffine` that nothing discharged. What
this file adds is that affine case, and hence the conclusion.

## Main results

* `isZero_cohomology_of_isZero_rightDerivedPlus_pushforward`: over an affine base, vanishing of
  the higher direct image is vanishing of absolute cohomology. This is the converse of
  `isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`, and the two together say
  that over an affine base the two vanishings are the same condition.
* `isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom`: along an affine morphism,
  vanishing of the cohomology of the direct image is vanishing of the cohomology upstairs.
* `isZero_rightDerivedPlus_pushforward_baseChange_of_isAffine`: conclusion (a) in the case of a
  cartesian square whose two bases are affine, in a single degree and for a single module.
* `isZero_rightDerivedPlus_pushforward_baseChange`: **conclusion (a) of [Stacks, Tag 0EX3]**,
  unconditionally, for every top-degree base-change situation.

## Implementation notes

*The route is the source's, read through global sections rather than through `g_*`.* The source
argues that for `Y` and `Y'` affine the morphisms `g` and `g'` are affine, so that
`g_*(Rⁱ f'_* F') = Hⁱ(R g_* R f'_* F') = Hⁱ(R f_* R g'_* F') = Hⁱ(R f_* g'_* F') = Rⁱ f_* g'_* F'`
vanishes, and then concludes because `g_*` is the restriction functor on modules. Taking global
sections over the affine base `Y'` instead of pushing forward along `g` gives the same chain with
two advantages: it needs neither the composition of derived pushforwards nor the conservativity
of `g_*`, and every step is a formalized tag. In order:

* `Rⁱ f'_* F'` is quasi-coherent ([Stacks, Tag 01XJ]) and `Y'` is affine, so it vanishes as soon
  as its global sections do;
* `Γ(Y', Rⁱ f'_* F') = Hⁱ(X', F')` ([Stacks, Tag 01XK]);
* `Hⁱ(X', F') = Hⁱ(X, g'_* F')` because `g'` is affine ([Stacks, Tag 089W]);
* `Hⁱ(X, g'_* F') = Γ(Y, Rⁱ f_* g'_* F')` ([Stacks, Tag 01XK] again, now over `Y`);
* `g'_* F'` is quasi-coherent ([Stacks, Tag 02KG]), so the situation's own vanishing hypothesis
  applies to it.

The first two steps are packaged in both directions here:
`isZero_rightDerivedPlus_pushforward_of_isZero_cohomology` is one direction, and
`isZero_cohomology_of_isZero_rightDerivedPlus_pushforward` below is its converse, which is the
direction the second application of [Stacks, Tag 01XK] needs.

*Affineness of the two horizontal morphisms.* `g` is affine because its source and target are
(`AlgebraicGeometry.isAffineHom_of_isAffine`), and `g'` is its base change along `f`, so it is
affine as well; `f'` is the base change of `f` along `g`, so it is quasi-compact and
quasi-separated. All three come from Mathlib's `MorphismProperty.IsStableUnderBaseChange`
instances, with the square supplied explicitly and flipped where the base change runs the other
way.

*Two indexings.* [Stacks, Tag 01XK] is stated for Mathlib's `ℤ`-indexed
`Functor.rightDerivedPlus` and [Stacks, Tag 089W] for the `ℕ`-indexed `Functor.rightDerived`.
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` crosses between them, which is why the
affine case below takes the degree as an integer `i` together with a natural number `n` and the
equation `i = n` rather than as a nonnegative integer: the crossing then happens once, in the
statement, instead of inside the proof. The situation supplies `d : ℕ`, so `d < i` forces `i`
nonnegative and the top-level statement needs no such hypothesis.

*Reflecting vanishing through restriction of scalars.* Both comparisons are stated with the left
side restricted along the structure morphism. Restriction of scalars does not change the
underlying module, so vanishing transports in both directions by
`ModuleCat.isZero_iff_subsingleton`; the direction that needs it is the one reflecting a zero
object, since the direction that only pushes one forward is `Functor.map_isZero`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- In a cartesian square over affine bases, the base change `g'` of the affine `g` is affine. -/
private theorem isAffineHom_of_isPullback_of_isAffine
    {X₀ Y₀ X₁ Y₁ : Scheme.{u}} {f : X₀ ⟶ Y₀} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {g : Y₁ ⟶ Y₀}
    (sq : IsPullback g' f' f g) [IsAffine Y₀] [IsAffine Y₁] : IsAffineHom g' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) sq.flip
    (isAffineHom_of_isAffine g)

/-- Vanishing of a module over `S` follows from vanishing of its restriction of scalars. -/
private theorem isZero_of_isZero_restrictScalars {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat.{u} S) (h : IsZero ((ModuleCat.restrictScalars.{u} φ.hom).obj M)) :
    IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  assumption

/-- **Over an affine base, vanishing of the higher direct image is vanishing of cohomology.**
This is the converse of `isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`: both
directions are read off the one natural isomorphism of [Stacks, Tag 01XK], which identifies the
global sections of `Rⁱ g_* F` over the affine base with `Hⁱ(X₀, F)` after restricting scalars
along `g^♯`.

Restriction of scalars leaves the underlying module alone, so it reflects zero objects; that is
the only step this direction needs beyond the comparison itself. -/
theorem isZero_cohomology_of_isZero_rightDerivedPlus_pushforward
    {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [QuasiCompact g] [QuasiSeparated g] [IsAffine Y₀]
    (i : ℤ) (F : X₀.Modules) [F.IsQuasicoherent]
    (h : IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F)) :
    IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F) := by
  refine isZero_of_isZero_restrictScalars g.appTop _ ?_
  exact IsZero.of_iso ((moduleGlobalSections Y₀).map_isZero h)
      ((cohomologyIsoGlobalSectionsRightDerivedPushforward g i).app ⟨F, inferInstance⟩)

/-- **Along an affine morphism, vanishing of the cohomology of the direct image is vanishing of
the cohomology upstairs.** This is [Stacks, Tag 089W] used to reflect a zero object: that tag
identifies `Hⁿ(X₁, F₁)`, with scalars restricted along `g'^♯`, with `Hⁿ(X₀, g'_* F₁)`, and
restriction of scalars reflects vanishing.

The degree is given as an integer `i` together with a natural number `n` and the equation
`i = n`, because [Stacks, Tag 089W] is stated for the `ℕ`-indexed right derived functors while
the statements this feeds are `ℤ`-indexed. -/
theorem isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom
    {X₁ X₀ : Scheme.{u}} (g' : X₁ ⟶ X₀) [IsAffineHom g']
    (F₁ : X₁.Modules) [F₁.IsQuasicoherent] {i : ℤ} {n : ℕ} (hin : i = (n : ℤ))
    (h : IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj
      ((Scheme.Modules.pushforward g').obj F₁))) :
    IsZero (((moduleGlobalSections X₁).rightDerivedPlus i).obj F₁) := by
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ hin] at h ⊢
  refine isZero_of_isZero_restrictScalars g'.appTop _ ?_
  exact IsZero.of_iso h (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward g' F₁ n)

/-- **Conclusion (a) of [Stacks, Tag 0EX3] when both bases are affine**, in one degree and for
one module: if the higher direct image along `f` of the direct image of `F₁` along `g'` vanishes,
then the higher direct image of `F₁` along `f'` vanishes.

This is the source's argument, with global sections over the affine bases in place of the
pushforward along `g`. The chain runs
`Rⁱ f'_* F₁ = 0 ⟸ Hⁱ(X₁, F₁) = 0 ⟸ Hⁱ(X₀, g'_* F₁) = 0 ⟸ Rⁱ f_* g'_* F₁ = 0`,
the first step being
`isZero_rightDerivedPlus_pushforward_of_isZero_cohomology` over the affine base `Y₁`, the second
[Stacks, Tag 089W] along the affine `g'`, and the third the converse comparison over the affine
base `Y₀`.

The hypothesis is stated for the module `g'_* F₁` rather than quantified over all quasi-coherent
modules on `X₀`, so the statement is exactly as strong as the step it performs. -/
theorem isZero_rightDerivedPlus_pushforward_baseChange_of_isAffine
    {X₀ Y₀ X₁ Y₁ : Scheme.{u}} {f : X₀ ⟶ Y₀} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {g : Y₁ ⟶ Y₀}
    (sq : IsPullback g' f' f g) [IsAffine Y₀] [IsAffine Y₁]
    [QuasiCompact f] [QuasiSeparated f]
    {i : ℤ} {n : ℕ} (hin : i = (n : ℤ)) (F₁ : X₁.Modules) [F₁.IsQuasicoherent]
    (hvan : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj
      ((Scheme.Modules.pushforward g').obj F₁))) :
    IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj F₁) := by
  have hg' := isAffineHom_of_isPullback_of_isAffine sq
  have hqcf' : QuasiCompact f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq
      (inferInstanceAs (QuasiCompact f))
  have hqsf' : QuasiSeparated f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) sq
      (inferInstanceAs (QuasiSeparated f))
  exact isZero_rightDerivedPlus_pushforward_of_isZero_cohomology f' i F₁
    (isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom g' F₁ hin
      (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward f i _ hvan))

/-- **Conclusion (a) of [Stacks, Tag 0EX3].** In a top-degree base-change situation the higher
direct images along the base-changed morphism `f'` of a quasi-coherent module vanish above the
degree `d`.

`isZero_rightDerivedPlus_pushforward_of_affineCase` reduces this to the case of a cartesian
square whose two bases are affine, which it carried as the hypothesis `haffine`; that case is
`isZero_rightDerivedPlus_pushforward_baseChange_of_isAffine`, so the conclusion is now
unconditional.

The degree `d` of a situation is a natural number, so `d < j` makes `j` nonnegative and the
integer-to-natural crossing the affine case asks for is available. -/
@[stacks 0EX3 "(a)"]
theorem isZero_rightDerivedPlus_pushforward_baseChange
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (i : ℤ) (hi : (S.d : ℤ) < i) (F' : S.X'.Modules) [F'.IsQuasicoherent] :
    IsZero (((Scheme.Modules.pushforward S.f').rightDerivedPlus i).obj F') := by
  refine isZero_rightDerivedPlus_pushforward_of_affineCase S ?_ i hi F'
  intro X₀ Y₀ X₁ Y₁ f g' f'' g sq _ _ _ _ hvan j hj F₁ hF₁
  have : F₁.IsQuasicoherent := hF₁
  have hg' := isAffineHom_of_isPullback_of_isAffine sq
  have hjn : j = ((j.toNat : ℕ) : ℤ) :=
    (Int.toNat_of_nonneg ((Int.natCast_nonneg S.d).trans hj.le)).symm
  exact isZero_rightDerivedPlus_pushforward_baseChange_of_isAffine sq hjn F₁
    (hvan j hj ((Scheme.Modules.pushforward g').obj F₁) inferInstance)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
