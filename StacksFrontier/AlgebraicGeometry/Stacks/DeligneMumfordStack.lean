module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack

/-!
# Deligne-Mumford stacks (Stacks 03YO)

An algebraic stack over a scheme `S` contained in a big fppf site is a *Deligne-Mumford stack*
when it admits a surjective **étale** presentation by a scheme, rather than merely a surjective
smooth one.

## Main definitions

* `AlgebraicGeometry.Stack.IsDeligneMumfordStack`: **Stacks 03YO**.
* `AlgebraicGeometry.Stack.IsDeligneMumfordStackUniv`: the same definition for a category over
  the site whose total category has arbitrary object and morphism universes.

## Main results

* `AlgebraicGeometry.Stack.isDeligneMumfordStackUniv_iff_isDeligneMumfordStack`: at the
  universes of `IsDeligneMumfordStack` the two definitions agree.

## Implementation notes

The definition mirrors `AlgebraicGeometry.Stack.IsAlgebraicStack` clause for clause, with
`AlgebraicGeometry.Space.IsEtale` in place of `AlgebraicGeometry.Space.IsSmooth` on the
presentation, and it retains the algebraic-stack condition explicitly rather than re-deriving
its first three clauses: the two predicates are used side by side, so neither is stated in terms
of the other.

Surjectivity and étaleness of the presentation are the relative-property condition of
Stacks 03YK written out for those two properties together, exactly as `IsAlgebraicStack` writes
it out for surjectivity and smoothness. Writing it out is what keeps the definition free of the
two instance arguments `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget` that
`AlgebraicGeometry.Stack.HasRelativeProperty` carries; the second of those is not available for
the combined property.

The presentation is a 1-morphism of the 2-category
`CategoryTheory.CatFiberedInGroupoids`, so its underlying functor is reached by
`CategoryTheory.CatFiberedInGroupoids.homFunctor`, and the fibred-in-groupoids witness of `𝒳` is
existentially quantified ahead of it — the same shape `IsAlgebraicStack` uses, and the shape the
statement of this tag uses. Being an abbreviation, the algebraic-stack hypothesis and the
presentation data are directly available to a downstream statement.

`IsDeligneMumfordStackUniv` is the same definition with the object and morphism universes of the
total category of `𝒳` independent of those of the site, as for `IsAlgebraicStack`: the presenting
scheme keeps the universes of the site, so the presentation is a `CategoryTheory.BasedFunctor`
between categories in different universes rather than a 1-morphism of one 2-category. This is
what lets a category whose morphisms are not small, such as a stackification, be Deligne-Mumford
in its own right rather than through a small model of it.

## References

* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

/-- **Stacks 03YO.** An algebraic stack over `S` is a *Deligne-Mumford stack* when it admits a
presentation by a scheme which is surjective and étale: a 1-morphism from the category
represented by a scheme `U` over `S`, representable by algebraic spaces, such that every
algebraic space representing its base change along a scheme-valued point of the stack has
surjective and étale structural morphism. -/
@[stacks 03YO]
abbrev IsDeligneMumfordStack.{u, w}
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)) : Prop :=
  IsAlgebraicStack.{u, w} B S hS 𝒳 ∧
    ∃ (h𝒳 : 𝒳.p.IsFiberedInGroupoids),
      let 𝒳' := CatFiberedInGroupoids.mk 𝒳 h𝒳
      ∃ (U : BigFppfOver B S hS)
        (f : schemeFibredCategory B S hS U ⟶ 𝒳'),
        IsRepresentableByAlgebraicSpaces B S hS f.hom ∧
          ∀ (V : BigFppfOver B S hS)
            (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
            (_hy : y ⋙ 𝒳.p = Over.map V.hom)
            (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
            (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
            Nonempty (StacksRepresentableCFG.EquivalenceOver
              (TwoFibreProductOver.fst (Over.map V.hom)
                (schemeFibredCategory B S hS U).val.p 𝒳.p y
                (CatFiberedInGroupoids.homFunctor f))
              (presheafOfCategories (F ⋙ typeToCat)).p) →
              (let g := (algebraicSpaceMap B S hS V
                ((spacesOverSmallerBaseFunctor
                  B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
               Space.IsSurjective B S hS g ∧ Space.IsEtale B S hS g)

/-- **Stacks 03YO, for a category over the site in arbitrary universes.** The definition of
`AlgebraicGeometry.Stack.IsDeligneMumfordStack` for a category `𝒳` over the big fppf site of `S`
whose total category has object and morphism universes independent of those of the site, as
`AlgebraicGeometry.Stack.IsAlgebraicStack` allows: `𝒳` is an algebraic stack admitting a
presentation by a scheme `U` over `S`, a based functor from the category represented by `U`
which is representable by algebraic spaces, such that every algebraic space representing its
base change along a scheme-valued point of `𝒳` has surjective and étale structural morphism.
At the universes of `IsDeligneMumfordStack` the two agree,
`AlgebraicGeometry.Stack.isDeligneMumfordStackUniv_iff_isDeligneMumfordStack`. -/
abbrev IsDeligneMumfordStackUniv.{u, w, v, t}
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) : Prop :=
  IsAlgebraicStack.{u, w} B S hS 𝒳 ∧
    ∃ (h𝒳 : 𝒳.p.IsFiberedInGroupoids),
      let 𝒳' := CatFiberedInGroupoids.mk 𝒳 h𝒳
      ∃ (U : BigFppfOver B S hS)
        (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳'.val),
        IsRepresentableByAlgebraicSpaces B S hS f ∧
          ∀ (V : BigFppfOver B S hS)
            (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
            (_hy : y ⋙ 𝒳.p = Over.map V.hom)
            (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
            (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
            Nonempty (StacksRepresentableCFG.EquivalenceOver
              (TwoFibreProductOver.fst (Over.map V.hom)
                (schemeFibredCategory B S hS U).val.p 𝒳.p y f.toFunctor)
              (presheafOfCategories (F ⋙ typeToCat)).p) →
              (let g := (algebraicSpaceMap B S hS V
                ((spacesOverSmallerBaseFunctor
                  B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
               Space.IsSurjective B S hS g ∧ Space.IsEtale B S hS g)

/-- At the universes of `AlgebraicGeometry.Stack.IsDeligneMumfordStack`, where the presentation
is a 1-morphism of `CategoryTheory.CatFiberedInGroupoids`, the universe-general definition
`AlgebraicGeometry.Stack.IsDeligneMumfordStackUniv` is the same condition. -/
theorem isDeligneMumfordStackUniv_iff_isDeligneMumfordStack.{u, w}
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)) :
    IsDeligneMumfordStackUniv.{u, w} B S hS 𝒳 ↔ IsDeligneMumfordStack.{u, w} B S hS 𝒳 := by
  constructor
  · rintro ⟨halg, hfib, U, f, hf, hprop⟩
    exact ⟨halg, hfib, U, Bicategory.InducedBicategory.mkHom f, hf, hprop⟩
  · rintro ⟨halg, hfib, U, f, hf, hprop⟩
    exact ⟨halg, hfib, U, f.hom, hf, hprop⟩

end AlgebraicGeometry.Stack

end
