module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Two bracketings of a triple of left adjoints, compared through two different middles

Let `Fr ⊣ Gr`, `Fg ⊣ Gg`, `Fa ⊣ Ga` be three composable adjunctions, so that `Fr ⋙ Fg ⋙ Fa` is a
left adjoint of `Ga ⋙ Gg ⋙ Gr`. Suppose the last two of the three are identified with a single
adjunction `Fjm ⊣ Gjm`, the triple with `Fjn ⊣ Gjn`, and the first two *composed with the third*
with a fourth `Fh ⋙ Fa ⊣ Ga ⋙ Gh`. There are then two ways of comparing `Fr ⋙ Fg ⋙ Fa` with
`Fjn`: through `Fr ⋙ Fjm`, or through `Fh ⋙ Fa`.

This file records that the two agree as soon as the corresponding comparisons of the *right*
adjoints agree. Every comparison in sight is a `CategoryTheory.Adjunction.leftAdjointCompIso`,
hence determined by its conjugate, and the hypothesis is exactly the equality of the two
conjugates.

`CategoryTheory.Adjunction.leftAdjointCompIso_assoc` is the same statement under the stronger
hypothesis that the comparison of right adjoints factors through `Gg ⋙ Gr ≅ Gh`, that is that
the first two adjunctions already compose to the fourth before the third is appended. That
hypothesis can fail: for instance when `Fg` and `Fh` are the extensions by zero from two
simplicial components into the total site, whose restrictions become comparable only after
restricting further along the augmentation.

## Main results

* `Stacks.CategoryTheory.leftAdjointCompIso_isoWhiskerLeft_trans`: the two comparisons agree.

## Implementation notes

Both sides are isomorphisms with the same source and target, so it suffices to compare their
inverses, and `CategoryTheory.conjugateEquiv` is injective on those. Each side then splits by
`CategoryTheory.conjugateEquiv_comp` into two factors, and all four factors are computed by
`CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv`, the one whiskered factor
after `CategoryTheory.conjugateEquiv_whiskerLeft` has turned the whiskering on the left adjoints
into a whiskering on the right adjoints. What is left is the hypothesis, read on `hom`.

The hypothesis is stated as an equality of isomorphisms rather than of their `hom`
transformations because that is the form in which it can be proved when the isomorphisms are
concrete composites: `CategoryTheory.Iso.trans` being `implicit_reducible`,
`CategoryTheory.Iso.trans_hom` no longer fires on `(α ≪≫ β).hom` there, whereas the identities
`CategoryTheory.Iso.trans_assoc` and `CategoryTheory.Iso.symm_self_id` still apply at the level
of isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {Fr : C₀ ⥤ C₁} {Gr : C₁ ⥤ C₀} {Fg : C₁ ⥤ C₂} {Gg : C₂ ⥤ C₁}
  {Fh : C₀ ⥤ C₂} {Gh : C₂ ⥤ C₀} {Fa : C₂ ⥤ C₃} {Ga : C₃ ⥤ C₂}
  {Fjm : C₁ ⥤ C₃} {Gjm : C₃ ⥤ C₁} {Fjn : C₀ ⥤ C₃} {Gjn : C₃ ⥤ C₀}

/-- **Two bracketings of a triple of left adjoints agree when their conjugates do.** Let
`adjr`, `adjg`, `adja` be three composable adjunctions, `adjjm` an adjunction identified with
the composite of the last two by `em`, `adjjn` one identified with the whole triple in two
steps, and `adjh` one whose composite with `adja` is identified with the composite of the first
two with `adja` by `eτ`. Then comparing `Fr ⋙ Fg ⋙ Fa` with `Fjn` through `Fr ⋙ Fjm` agrees
with comparing it through `Fh ⋙ Fa`, provided the two composites of right-adjoint comparisons
agree.

Unlike `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`, no comparison of `Gg ⋙ Gr` with
`Gh` is required: only of `(Ga ⋙ Gg) ⋙ Gr` with `Ga ⋙ Gh`. -/
theorem leftAdjointCompIso_isoWhiskerLeft_trans
    (adjr : Fr ⊣ Gr) (adjg : Fg ⊣ Gg) (adjh : Fh ⊣ Gh) (adja : Fa ⊣ Ga)
    (adjjm : Fjm ⊣ Gjm) (adjjn : Fjn ⊣ Gjn)
    (em : Ga ⋙ Gg ≅ Gjm) (esl : Gjm ⋙ Gr ≅ Gjn)
    (eτ : (Ga ⋙ Gg) ⋙ Gr ≅ Ga ⋙ Gh) (en : Ga ⋙ Gh ≅ Gjn)
    (h : Functor.isoWhiskerRight em Gr ≪≫ esl = eτ ≪≫ en) :
    Functor.isoWhiskerLeft Fr (Adjunction.leftAdjointCompIso adjg adja adjjm em) ≪≫
        Adjunction.leftAdjointCompIso adjr adjjm adjjn esl =
      Adjunction.leftAdjointCompIso adjr (adjg.comp adja) (adjh.comp adja) eτ ≪≫
        Adjunction.leftAdjointCompIso adjh adja adjjn en := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
  apply (conjugateEquiv (adjr.comp (adjg.comp adja)) adjjn).injective
  rw [Iso.trans_inv, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    ← conjugateEquiv_comp _ (adjr.comp adjjm), ← conjugateEquiv_comp _ (adjh.comp adja),
    conjugateEquiv_whiskerLeft (adjg.comp adja) adjjm adjr]
  simp only [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  simpa [Iso.trans_hom, Functor.isoWhiskerRight_hom] using congrArg Iso.hom h

end Stacks.CategoryTheory

end
