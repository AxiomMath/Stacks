module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverFieldTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Field-valued points of a stack covered by the spectrum of a field are flat (Stacks 06MM)

Let `𝒵` be an algebraic stack over `S` admitting a surjective flat 1-morphism from the algebraic
stack of the spectrum of a field. **Stacks 06MM** asserts that every 1-morphism to `𝒵` from the
algebraic stack of the spectrum of a field is then surjective *and flat*. The surjectivity half
is `AlgebraicGeometry.Stack.isSurjective_of_fieldSpectrum_cover`; this file proves the flatness
half.

The source's argument is descent. Let `f : Spec k ⟶ 𝒵` be the given surjective flat 1-morphism
and `g : Spec k' ⟶ 𝒵` another field-valued point, and let `T = Spec k ×_𝒵 Spec k'`. The
projection `T ⟶ Spec k' ` is a base change of `f`, hence surjective and flat, while the
projection `T ⟶ Spec k` is flat *because `k` is a field*: every 1-morphism of algebraic stacks
whose target is the algebraic stack of the spectrum of a field is flat. So the composite
`T ⟶ Spec k ⟶ 𝒵` is flat, and **Stacks 06PZ** — descent of flatness along a surjective flat
1-morphism — makes `g` flat.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_to_fieldSpectrumStack`: every 1-morphism of
  algebraic stacks over `S` whose target is the algebraic stack of the spectrum of a field is
  flat.
* `AlgebraicGeometry.Stack.isFlat_of_fieldSpectrum_cover`: **Stacks 06MM**, flatness.

## Implementation notes

Flatness of a 1-morphism into the algebraic stack of a field spectrum is proved by composing with
a smooth surjective scheme atlas of the source and descending along it by **Stacks 06Q0**: the
composite is a 1-morphism between *represented* algebraic stacks, so the existential
smooth-diagram test of **Stacks 06PW** is flatness of the induced morphism of representing
algebraic spaces, which is `AlgebraicGeometry.Space.isFlat_to_field`. A smooth 1-morphism is
flat, so the atlas discharges the two hypotheses of Stacks 06Q0.

The 2-fibre product is the canonical one,
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`, which is the only model for which
the library's **Stacks 06PZ** is stated.

## References

* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **A 1-morphism of algebraic stacks to the algebraic stack of the spectrum of a field is
flat.** Choose a smooth surjective scheme atlas `b : V ⟶ 𝒳`. The composite `b ≫ h` is a
1-morphism between algebraic stacks represented by algebraic spaces, so its flatness
(**Stacks 06PW**) is flatness of the induced morphism of representing algebraic spaces, which
holds because the target is the spectrum of a field. The atlas is surjective and, being smooth,
flat, so **Stacks 06Q0** descends flatness from the composite to `h`. -/
theorem isFlat_to_fieldSpectrumStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (F : FieldSpectrum B S hS) (h : 𝒳 ⟶ schemeStack.{u, w} B S hS F.base) :
    IsFlat B S hS h := by
  obtain ⟨V, b, hbSmooth, hbSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  have hcomp : IsFlat B S hS (b ≫ h) := by
    rw [isFlat_iff_hasPropertyOnSomeSmoothDiagram,
      hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
        (schemeStack.{u, w} B S hS V).property
        (schemeStack.{u, w} B S hS F.base).property
        (yoneda.obj V) (yoneda.obj F.base)
        (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS F.base)
        (PresheafOfCategories.sliceElementsEquivalenceOver V)
        (PresheafOfCategories.sliceElementsEquivalenceOver F.base)]
    exact Space.isFlat_to_field B S hS (isAlgebraicSpace_yoneda B S hS V) F.isSpec _
  exact isFlat_of_isSurjective_of_isFlat_comp B S hS b h hcomp hbSurj
    (isFlat_of_isSmooth B S hS b hbSmooth)

end AlgebraicStacks

/-- **Stacks 06MM, flatness.** Let `𝒵` be an algebraic stack over `S` admitting a surjective flat
1-morphism from the algebraic stack of the spectrum of a field. Then every 1-morphism to `𝒵` from
the algebraic stack of the spectrum of a field is flat.

Form the canonical 2-fibre product of the given cover `f` with the 1-morphism `g` in question.
Its projection to the source of `f` is flat because that source is the algebraic stack of the
spectrum of a field, so the composite with `f` is flat; `f` being surjective and flat,
**Stacks 06PZ** descends that flatness to `g`.

The companion `AlgebraicGeometry.Stack.isSurjective_of_fieldSpectrum_cover` is the surjectivity
half of the tag, which needs no flatness hypothesis. -/
@[stacks 06MM "flatness"]
theorem isFlat_of_fieldSpectrum_cover (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (F F' : FieldSpectrum B S hS)
    (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (g : schemeStack.{u, w} B S hS F'.base ⟶ 𝒵)
    (hsurj : IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f) :
    AlgebraicStacks.IsFlat B S hS g :=
  AlgebraicStacks.isFlat_twoFibreProduct_fst_descent B S hS g f
    (twoFibreProductSquareAlgebraicStacks B S hS f g)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)
    hsurj hflat
    (AlgebraicStacks.isFlat_to_fieldSpectrumStack.{u, w} B S hS _ F _)

end AlgebraicGeometry.Stack

end
