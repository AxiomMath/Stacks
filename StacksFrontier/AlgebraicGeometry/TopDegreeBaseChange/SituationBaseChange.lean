module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hypotheses of Tag 0EX3 reproduce themselves after base change

[Stacks, Tag 0EX3] fixes a morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes, a
degree `d` above which the higher direct images of every quasi-coherent module vanish, and a
cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

Its conclusion (a) says that the higher direct images along `f'` vanish above `d` as well. That
is literally the tag's hypothesis (2) for `f'`, so — once `Y'` is itself quasi-compact and
quasi-separated — the base-changed morphism carries a top-degree base-change situation of its
own. The source uses exactly this twice: its proof of (c) ends *"by part (b) applied to `f'`"*,
and [Stacks, Tag 0E7D] (2) asks for a neighbourhood over which `f` and `d` *"satisfy the
assumptions and conclusions"* of the tag.

This file packages that. Conclusion (a) is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_baseChange`,
so nothing here is conditional.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.baseChange`: the situation carried by
  the base-changed morphism `f'`, together with an arbitrary further cartesian square over `Y'`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.quasiCompact_f'` and
  `quasiSeparated_f'`: the base-changed morphism inherits the two finiteness properties of `f`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.compactSpace_X'` and
  `quasiSeparatedSpace_X'`: over a quasi-compact quasi-separated `Y'`, so is `X'`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.isZero_cohomology_of_lt`: over an
  affine base `Y'`, the absolute cohomology `Hⁱ(X', F')` vanishes above `d`. This is the
  sentence the source's proof of conclusion (b) opens with.

## Implementation notes

*Where the finiteness hypotheses come from.* A situation records quasi-compactness and
quasi-separatedness of `X` and `Y` as properties of the underlying spaces, and Mathlib turns
those into the corresponding properties of `f` (`quasiCompact_of_compactSpace`,
`QuasiSeparated.of_quasiSeparatedSpace`). Both are stable under base change, which gives them
for `f'`, and then `QuasiCompact.compactSpace_of_compactSpace` and
`quasiSeparatedSpace_of_quasiSeparated` carry them back down to the space `X'` once `Y'` is
assumed quasi-compact and quasi-separated. `Y'` genuinely needs that assumption: the tag's
square is arbitrary, and the source only ever applies (b) and (c) after having reduced to an
affine `Y'`.

*Why the further square is an argument.* A situation bundles its base-change square as data, so
producing a situation for `f'` means choosing one. The square is therefore taken as an argument
rather than fixed, which is what the source's three-column diagram in the explanation of (c)
needs: `f''` is the base change of `f'` along `h : Y'' ⟶ Y'`.

*The degree-`i` cohomology spelling.* `Hⁱ(X', F')` is
`((Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerivedPlus i).obj F'`, the
spelling in which [Stacks, Tag 01XK] is stated and in which the affine-base comparisons of
`AffineBaseCohomology.lean` and `BaseChangeVanishing.lean` are phrased.

*No `@[stacks 0EX3]` attribute.* The tag's conclusions are (a), (b) and (c); (a) already carries
its attribute in `BaseChangeVanishing.lean`, and nothing here is a further conclusion of the
tag — this is the repackaging of (a) that the proofs of (b) and (c) consume.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace TopDegreeBaseChangeSituation

variable (S : TopDegreeBaseChangeSituation.{u})

/-- **The morphism of a top-degree base-change situation is quasi-compact.** The situation
records compactness of `X` and quasi-separatedness of `Y` as properties of the spaces. -/
theorem quasiCompact_f : QuasiCompact S.f :=
  have := S.isCompact_X
  have := S.isQuasiSeparated_Y
  inferInstance

/-- **The morphism of a top-degree base-change situation is quasi-separated.** The situation
records quasi-separatedness of `X` as a property of the space. -/
theorem quasiSeparated_f : QuasiSeparated S.f :=
  have := S.isQuasiSeparated_X
  inferInstance

/-- **The base-changed morphism is quasi-compact**, because quasi-compactness of morphisms is
stable under base change and the situation's square is cartesian. -/
@[ega "I 6.6.4" "(iii), case S = Y"]
theorem quasiCompact_f' : QuasiCompact S.f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) S.isPullback
    S.quasiCompact_f

/-- **The base-changed morphism is quasi-separated**, because quasi-separatedness of morphisms
is stable under base change and the situation's square is cartesian. -/
theorem quasiSeparated_f' : QuasiSeparated S.f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) S.isPullback
    S.quasiSeparated_f

/-- **Over a quasi-compact base the base-changed source is quasi-compact.** The source's
reduction makes `Y'` affine, hence quasi-compact, and `f'` is quasi-compact by base change. -/
theorem compactSpace_X' [CompactSpace S.Y'] : CompactSpace S.X' :=
  have := S.quasiCompact_f'
  QuasiCompact.compactSpace_of_compactSpace S.f'

/-- **Over a quasi-separated base the base-changed source is quasi-separated.** The source's
reduction makes `Y'` affine, hence quasi-separated, and `f'` is quasi-separated by base
change. -/
theorem quasiSeparatedSpace_X' [QuasiSeparatedSpace S.Y'] : QuasiSeparatedSpace S.X' :=
  have := S.quasiSeparated_f'
  quasiSeparatedSpace_of_quasiSeparated S.f'

/-- **The base-changed morphism of a top-degree base-change situation carries a top-degree
base-change situation of its own**, with the same degree `d` and with an arbitrary further
cartesian square

```
X'' --g''--> X'
|f''         |f'
v            v
Y'' --h----> Y'
```

tacked on. The vanishing hypothesis of the new situation is exactly conclusion (a) of
[Stacks, Tag 0EX3] for the old one, so this is unconditional; the finiteness hypotheses need
`Y'` quasi-compact and quasi-separated, which is the state the source's reduction puts it in.

This is what the source's *"by part (b) applied to `f'`"* in the proof of conclusion (c) asks
for, and what [Stacks, Tag 0E7D] (2) asserts about a small enough neighbourhood. -/
def baseChange [CompactSpace S.Y'] [QuasiSeparatedSpace S.Y'] {X'' Y'' : Scheme.{u}}
    (g'' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : IsPullback g'' f'' S.f' h) : TopDegreeBaseChangeSituation.{u} where
  X := S.X'
  Y := S.Y'
  f := S.f'
  d := S.d
  isCompact_X := S.compactSpace_X'
  isQuasiSeparated_X := S.quasiSeparatedSpace_X'
  isCompact_Y := ‹CompactSpace S.Y'›
  isQuasiSeparated_Y := ‹QuasiSeparatedSpace S.Y'›
  vanishes_above i hi F hF :=
    @Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_baseChange
      S i hi F hF
  X' := X''
  Y' := Y''
  g' := g''
  f' := f''
  g := h
  isPullback := sq

/-- The morphism `f` of `S.baseChange g'' f'' h sq` is `S.f'`. -/
@[simp]
theorem baseChange_f [CompactSpace S.Y'] [QuasiSeparatedSpace S.Y'] {X'' Y'' : Scheme.{u}}
    (g'' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : IsPullback g'' f'' S.f' h) : (S.baseChange g'' f'' h sq).f = S.f' :=
  rfl

/-- The degree `d` of `S.baseChange g'' f'' h sq` is the degree `S.d` of `S`. -/
@[simp]
theorem baseChange_d [CompactSpace S.Y'] [QuasiSeparatedSpace S.Y'] {X'' Y'' : Scheme.{u}}
    (g'' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : IsPullback g'' f'' S.f' h) : (S.baseChange g'' f'' h sq).d = S.d :=
  rfl

/-- The base-changed morphism `f'` of `S.baseChange g'' f'' h sq` is `f''`. -/
@[simp]
theorem baseChange_f' [CompactSpace S.Y'] [QuasiSeparatedSpace S.Y'] {X'' Y'' : Scheme.{u}}
    (g'' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : IsPullback g'' f'' S.f' h) : (S.baseChange g'' f'' h sq).f' = f'' :=
  rfl

/-- **Over an affine base, the absolute cohomology of the base-changed source vanishes above
`d`.** This is the sentence the source's proof of conclusion (b) opens with: *"By part (a) we
have `H^{d+1}(X', F') = 0` for any quasi-coherent `𝒪_{X'}`-module `F'`, see [Stacks, Tag
01XK]"*, and it is stated here in every degree above `d` rather than only in degree `d + 1`,
which is what the vanishing supplies and what the right-exactness step consumes.

It is conclusion (a) followed by the affine-base comparison
`isZero_cohomology_of_isZero_rightDerivedPlus_pushforward`. -/
theorem isZero_cohomology_of_lt [IsAffine S.Y'] (i : ℤ) (hi : (S.d : ℤ) < i)
    (F' : S.X'.Modules) [F'.IsQuasicoherent] :
    IsZero (((moduleGlobalSections S.X').rightDerivedPlus i).obj F') :=
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  TopDegreeBaseChange.isZero_cohomology_of_isZero_rightDerivedPlus_pushforward S.f' i F'
    (TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_baseChange S i hi F')

end TopDegreeBaseChangeSituation

end

end Stacks.AlgebraicGeometry

end
