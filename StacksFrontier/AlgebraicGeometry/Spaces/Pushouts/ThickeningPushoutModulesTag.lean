module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutFiniteModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutFlatModules
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08KV: the whole lemma

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over `S`,
let `Y' = Y ⨿_X X'` be their pushout (Stacks 07VX) and let `g : V' ⟶ Y'` be a morphism, with
`V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`.  Stacks 08KV asserts that
`𝒢' ↦ ((V ⟶ V')^*𝒢', (U' ⟶ V')^*𝒢', can)` is an equivalence from the quasi-coherent
`𝒪_{V'}`-modules flat over `Y'` onto the triples `(𝒢, ℱ', φ)`, and that under it (a) finite type
and (b), for `g` locally of finite presentation, finite presentation, are detected on the triple.
This file states the equivalence, (a) and (b) on one theorem.

## Main results

* `isEquivalence_flatRestrictionFunctor_and_finiteness_iff_restrict`: the restriction functor is
  an equivalence, and finite type and finite presentation are detected on the triple.

## Implementation notes

Each assertion is spelled exactly as the declaration proving it states it:
`AlgebraicGeometry.Space.PushoutModules.isEquivalence_flatRestrictionFunctor` (the equivalence),
`AlgebraicGeometry.Space.PushoutModules.isFiniteType_iff_restrict` ((a)) and
`AlgebraicGeometry.Space.PushoutModules.isFinitePresentationOnSite_iff_restrict` ((b)).  The
pushout is not assumed: it exists by Stacks 07VX
(`AlgebraicGeometry.Space.hasPushout_of_isThickeningHom_of_isAffineHom`), which is the instance
the statement binds.

## References

* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.PushoutModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)

/-- Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over
`S`, let `Y' = Y ⨿_X X'` be their pushout (Stacks 07VX) and let `g : V' ⟶ Y'` be a morphism, with
`V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`.

* The functor `𝒢' ↦ ((V ⟶ V')^*𝒢', (U' ⟶ V')^*𝒢', can)` is an **equivalence of categories**
  from the quasi-coherent `𝒪_{V'}`-modules flat over `Y'` onto the triples `(𝒢, ℱ', φ)` of a
  quasi-coherent `𝒪_V`-module `𝒢` flat over `Y`, a quasi-coherent `𝒪_{U'}`-module `ℱ'` flat over
  `X'` and an isomorphism `φ : (U ⟶ V)^*𝒢 ≅ (U ⟶ U')^*ℱ'`.
* Suppose `𝒢'` corresponds to the triple `(𝒢, ℱ', φ)`, so that `𝒢 = (V ⟶ V')^*𝒢'` and
  `ℱ' = (U' ⟶ V')^*𝒢'`. Then
  (a) `𝒢'` is of finite type if and only if `𝒢` and `ℱ'` are of finite type;
  (b) if `g` is locally of finite presentation, then `𝒢'` is of finite presentation if and only
  if `𝒢` and `ℱ'` are of finite presentation (Stacks 03DL (7),
  `SheafOfModules.IsFinitePresentationOnSite`).

The source writes "`ℱ'` … flat over `X`": `ℱ'` lives on `U' = X' ×_{Y'} V'`, which lies over
`X'`, so the condition is flatness over `X'`, as in the scheme case Stacks 08KU.  The pushout is
not assumed: it exists by Stacks 07VX
(`AlgebraicGeometry.Space.hasPushout_of_isThickeningHom_of_isAffineHom`), which is the instance
the statement binds.  The functor is written out as the lift to the two full subcategories of
`CategoryTheory.TripleGluing.restrictFunctor` at the canonical comparison
`AlgebraicGeometry.Space.PushoutModules.squareOverlap`; a quasi-inverse is the gluing functor
`(𝒢, ℱ', φ) ↦ (V ⟶ V')_*𝒢 ×_{(U ⟶ V')_*ℱ} (U' ⟶ V')_*ℱ'`
(`isEquivalence_flatRestrictionFunctor_of_hasPushout`). -/
@[stacks 08KV]
theorem isEquivalence_flatRestrictionFunctor_and_finiteness_iff_restrict :
    letI := hasPushout_of_isThickeningHom_of_isAffineHom B S hS i f hi hf
    ∀ {V' : AlgebraicSpaces B S hS} (g : V' ⟶ pushout i f),
      ((((FlatQuasicoherentTriple i f g).lift ((FlatQuasicoherentOver g).ι ⋙
          (TripleGluing.restrictFunctor (squareOverlap (commonToTarget i f g)
            (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
            (commonToAmbient_comp_eq i f g))))
        fun M => flatQuasicoherentTriple_restrict i f g M.obj M.property) :
        (FlatQuasicoherentOver g).FullSubcategory ⥤
          (FlatQuasicoherentTriple i f g).FullSubcategory)).IsEquivalence ∧
      (∀ (M : (FlatQuasicoherentOver g).FullSubcategory),
        M.obj.IsFiniteType ↔
          (((FlatQuasicoherentTriple i f g).lift ((FlatQuasicoherentOver g).ι ⋙
            (TripleGluing.restrictFunctor (squareOverlap (commonToTarget i f g)
              (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
              (commonToAmbient_comp_eq i f g))))
            fun M => flatQuasicoherentTriple_restrict i f g M.obj
              M.property).obj M).obj.target.IsFiniteType ∧
          (((FlatQuasicoherentTriple i f g).lift ((FlatQuasicoherentOver g).ι ⋙
            (TripleGluing.restrictFunctor (squareOverlap (commonToTarget i f g)
              (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
              (commonToAmbient_comp_eq i f g))))
            fun M => flatQuasicoherentTriple_restrict i f g M.obj
              M.property).obj M).obj.ambient.IsFiniteType) ∧
      (IsLocallyOfFinitePresentation B S hS g.hom →
        ∀ M : (FlatQuasicoherentOver g).FullSubcategory,
        (SheafOfModules.IsFinitePresentationOnSite M.obj ↔
          SheafOfModules.IsFinitePresentationOnSite
            (((FlatQuasicoherentTriple i f g).lift ((FlatQuasicoherentOver g).ι ⋙
              (TripleGluing.restrictFunctor (squareOverlap (commonToTarget i f g)
                (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
                (commonToAmbient_comp_eq i f g))))
              fun M => flatQuasicoherentTriple_restrict i f g M.obj M.property).obj M).obj.target ∧
          SheafOfModules.IsFinitePresentationOnSite
            (((FlatQuasicoherentTriple i f g).lift ((FlatQuasicoherentOver g).ι ⋙
              (TripleGluing.restrictFunctor (squareOverlap (commonToTarget i f g)
                (targetRestriction i f g) (commonToAmbient i f g) (ambientRestriction i f g)
                (commonToAmbient_comp_eq i f g))))
              fun M => flatQuasicoherentTriple_restrict i f g M.obj
                M.property).obj M).obj.ambient)) := by
  intro V' g
  exact ⟨isEquivalence_flatRestrictionFunctor i f hi hf g, isFiniteType_iff_restrict i f hi hf g,
    isFinitePresentationOnSite_iff_restrict i f hi hf g⟩

end AlgebraicGeometry.Space.PushoutModules

end
