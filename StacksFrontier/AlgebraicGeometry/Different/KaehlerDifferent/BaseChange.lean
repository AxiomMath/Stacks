module

public import StacksFrontier.AlgebraicGeometry.Different.KaehlerDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom

/-!
# Base change of the Kähler different

For a cartesian square of schemes

```
Y' ---> Y
|       |
f'      f
v       v
X' ---> X
```

with `f` locally of finite type, let `R ⊆ Y` and `R' ⊆ Y'` be the closed subschemes cut out by
the Kähler differents of `f` and of `f'`. Then `R'` is the inverse image of `R`: the two closed
subschemes of `Y'` have the same defining ideal sheaf, and consequently the morphism `Y' ⟶ Y`
induces an isomorphism `R' ≅ Y' ×_Y R` over `Y'`.

## Main definitions

* `Stacks.Discriminant.kaehlerDifferentSubschemeIsoPullback` is the induced isomorphism from the
  closed subscheme cut out by the Kähler different of the base change to the fibre product.

## Main results

* `Stacks.Discriminant.kaehlerDifferent_comap`: **Stacks Project, Tag 0BVX**, as an equality of
  ideal sheaves.
* `Stacks.Discriminant.kaehlerDifferentSubschemeIsoPullback_hom_fst`: the isomorphism of Tag 0BVX
  is an isomorphism of schemes over `Y'`.

## Implementation notes

The Kähler different is the zeroth Fitting ideal sheaf of the sheaf of relative differentials,
and the sheaf of relative differentials of a morphism locally of finite type is quasi-coherent of
finite type, so the two inputs of the Stacks proof apply: `Ω_{Y'/X'}` is the pullback of
`Ω_{Y/X}` by [Stacks, Tag 01V0] and Fitting ideal sheaves of quasi-coherent modules of finite
type commute with base change by `AlgebraicGeometry.fittingIdeal_comap`. Only the invariance of
Fitting ideal sheaves under isomorphism of modules is needed in addition, which is
`AlgebraicGeometry.fittingIdeal_eq_of_iso`.

Local finiteness of type of the base change is not an extra hypothesis: it is supplied in the
statements as the explicit instance argument
`MorphismProperty.IsStableUnderBaseChange.of_isPullback`, so the only assumption is on `f`.

## References

* [Stacks Project, Tag 0BVW](https://stacks.math.columbia.edu/tag/0BVW)
* [Stacks Project, Tag 0BVX](https://stacks.math.columbia.edu/tag/0BVX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Discriminant

/-- The Kähler different of a morphism of schemes locally of finite type is the zeroth Fitting
ideal sheaf of its sheaf of relative differentials. -/
theorem kaehlerDifferent_eq_fittingIdeal_relativeDifferentials {Y X : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] :
    kaehlerDifferent f = fittingIdeal (Scheme.Hom.relativeDifferentials f) 0 :=
  rfl

/-- **Stacks Project, Tag 0BVX.** For a cartesian square of schemes with right edge `f : Y ⟶ X`
locally of finite type, left edge `f' : Y' ⟶ X'` and top edge `g' : Y' ⟶ Y`, the Kähler
different of `f'` is the inverse image along `g'` of the Kähler different of `f`. -/
@[stacks 0BVX "equality of the ideal sheaves cutting out R' and the inverse image of R"]
theorem kaehlerDifferent_comap {Y' Y X' X : Scheme.{u}} (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (f : Y ⟶ X) (g : X' ⟶ X) (h : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    @kaehlerDifferent Y' X' f'
        (locallyOfFiniteType_isStableUnderBaseChange.of_isPullback h inferInstance) =
      (kaehlerDifferent f).comap g' := by
  have hf' : LocallyOfFiniteType f' :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback h inferInstance
  have hiso : IsIso (Scheme.Hom.relativeDifferentialsMap g' f f' g h.w) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback g' f' f g h
  show fittingIdeal (Scheme.Hom.relativeDifferentials f') 0 =
    (fittingIdeal (Scheme.Hom.relativeDifferentials f) 0).comap g'
  rw [fittingIdeal_comap g' (Scheme.Hom.relativeDifferentials f) 0]
  exact fittingIdeal_eq_of_iso
    (asIso (Scheme.Hom.relativeDifferentialsMap g' f f' g h.w)).symm 0

/-- **Stacks Project, Tag 0BVX.** The isomorphism from the closed subscheme `R'` of `Y'` cut out
by the Kähler different of the base change `f'` to the fibre product `Y' ×_Y R`, where `R ⊆ Y` is
cut out by the Kähler different of `f`. -/
@[stacks 0BVX "the induced isomorphism of closed subschemes"]
noncomputable def kaehlerDifferentSubschemeIsoPullback {Y' Y X' X : Scheme.{u}} (g' : Y' ⟶ Y)
    (f' : Y' ⟶ X') (f : Y ⟶ X) (g : X' ⟶ X) (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] :
    (@kaehlerDifferent Y' X' f'
        (locallyOfFiniteType_isStableUnderBaseChange.of_isPullback h inferInstance)).subscheme ≅
      pullback g' (kaehlerDifferent f).subschemeι :=
  eqToIso (congrArg (fun K : Y'.IdealSheafData => K.subscheme)
      (kaehlerDifferent_comap g' f' f g h)) ≪≫ (kaehlerDifferent f).comapIso g'

/-- **Stacks Project, Tag 0BVX.** The isomorphism `R' ≅ Y' ×_Y R` of Tag 0BVX is an isomorphism
of schemes over `Y'`: composing it with the first projection is the closed immersion of `R'` into
`Y'`. -/
@[stacks 0BVX "the induced isomorphism of closed subschemes is over Y'"]
theorem kaehlerDifferentSubschemeIsoPullback_hom_fst {Y' Y X' X : Scheme.{u}} (g' : Y' ⟶ Y)
    (f' : Y' ⟶ X') (f : Y ⟶ X) (g : X' ⟶ X) (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] :
    (kaehlerDifferentSubschemeIsoPullback g' f' f g h).hom ≫ pullback.fst _ _ =
      Scheme.IdealSheafData.subschemeι (@kaehlerDifferent Y' X' f'
        (locallyOfFiniteType_isStableUnderBaseChange.of_isPullback h inferInstance)) := by
  rw [kaehlerDifferentSubschemeIsoPullback, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact eqToHom_subscheme_comp_subschemeι _ _ (kaehlerDifferent_comap g' f' f g h)

end Stacks.Discriminant

end
