module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoCancel
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.IteratedSliceLocalizedSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.RelocalizedMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the relocalized morphism of ringed sites in the two site objects

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D`, `U` an object of `C` and `c : U ⟶ u(V)`, and let
`b : V' ⟶ V`, `a : U' ⟶ U` and `c' : U' ⟶ u(V')` satisfy `a ≫ c = c' ≫ u(b)`. The last
assertion of Stacks 04J1 is that the square

```
  (Sh(C/U'), O_{U'})  --j_{U'/U}-->  (Sh(C/U), O_U)
        | f_{c'}                          | f_c
  (Sh(D/V'), O'_{V'}) --j_{V'/V}-->  (Sh(D/V), O'_V)
```

commutes, the horizontal arrows being the relocalization morphisms of Stacks 04IY. This file
proves it, as a square of ringed topoi.

## The route

Everything reduces, by the 2-isomorphism calculus of Stacks 04IY's relocalization triangle and
of `AlgebraicGeometry.RingedSite.relocalizationComp`, to the case `U' = u(V')`, `a = u(b)`,
`c' = 𝟙`: that is `AlgebraicGeometry.RingedSite.Hom.localizedNaturalitySquare` below, the
naturality of the localized morphism of Stacks 04J0 in the object `V` of the target site.

That square is in turn Stacks 04J0's own commutative diagram, applied one localization down: it
is the diagram for the morphism of ringed sites `f' : (C/u(V), O_{u(V)}) ⟶ (D/V, O'_V)` at the
object `V'/V` of its target, read through the identifications of the two iterated slices
`(C/u(V))/(u(V')/u(V)) ≌ C/u(V')` and `(D/V)/(V'/V) ≌ D/V'` with the localizations at `u(V')`
and at `V'`. Those identifications turn the two localization morphisms of that diagram into the
two relocalization morphisms wanted here
(`AlgebraicGeometry.RingedSite.iteratedSliceRelocalizationTriangle`) and its localized morphism
into `f'_{V'}` (`AlgebraicGeometry.RingedSite.iteratedSliceLocalizedSquare`); the identification
left standing on the source is removed by
`AlgebraicGeometry.RingedToposHom.TwoIso.cancelRight`, which it admits because it is an
equivalence of ringed topoi.

Nothing in the chain asks `u` to be left exact. The localized morphism of Stacks 04J0 is
available for a morphism of sites in Stacks 03CF's own generality, and so is its localization at
a further object, because `Over.post u` is a morphism of sites whenever `u` is; the local
instance `CategoryTheory.Functor.isContinuous_overPost_of_isContinuous` is what keeps it so, and
no declaration here carries Stacks 03EF's finite-limit hypotheses.

## Main definitions

* `AlgebraicGeometry.RingedSite.Hom.localizedNaturalitySquare`: the localized morphism of Stacks
  04J0 is natural in the object of the target site, as a 2-isomorphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.Hom.relocalizedNaturalitySquare`: **Stacks 04J1**, the last
  assertion: the square comparing `f_c` and `f_{c'}` commutes, as a square of ringed topoi.

## References

* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04J1](https://stacks.math.columbia.edu/tag/04J1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {V' V : Y.C} (b : V' ⟶ V)

/-- **Stacks 04J0 is natural in the object of the target site.** For `b : V' ⟶ V` the square

```
  (Sh(C/u(V')), O_{u(V')}) --j_{u(V')/u(V)}--> (Sh(C/u(V)), O_{u(V)})
        | f'_{V'}                                     | f'_V
  (Sh(D/V'), O'_{V'})      --j_{V'/V}-->       (Sh(D/V), O'_V)
```

commutes, as a square of ringed topoi.

This is Stacks 04J0's commutative diagram for the morphism of ringed sites `f'_V` at the object
`V'/V` of `D/V`, read through the two iterated-slice identifications and with the one on the
source cancelled. -/
noncomputable def Hom.localizedNaturalitySquare :
    TwoIso (A := (X.over (f.u.obj V')).ringedTopos) (B := (Y.over V).ringedTopos)
      (AlgebraicGeometry.RingedToposHom.comp
        (X := (X.over (f.u.obj V')).ringedTopos) (Y := (Y.over V').ringedTopos)
        (Z := (Y.over V).ringedTopos)
        (Y.relocalizationRingedToposHom b) (f.localizedRingedToposHom V'))
      (AlgebraicGeometry.RingedToposHom.comp
        (X := (X.over (f.u.obj V')).ringedTopos) (Y := (X.over (f.u.obj V)).ringedTopos)
        (Z := (Y.over V).ringedTopos)
        (f.localizedRingedToposHom V) (X.relocalizationRingedToposHom (f.u.map b))) := by
  refine TwoIso.cancelRight (C := (Y.over V).ringedTopos)
    (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b))) ?_
  exact TwoIso.trans
      (A := ((X.over (f.u.obj V)).over
        ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
      (B := (Y.over V).ringedTopos)
    (TwoIso.symm
      (A := ((X.over (f.u.obj V)).over
        ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
      (B := (Y.over V).ringedTopos)
      ((TwoIso.whiskerLeft ((f.localized V).localizedRingedToposHom (Over.mk b))
          (Y.iteratedSliceRelocalizationTriangle (Over.mk b))).trans
        ((TwoIso.associator ((f.localized V).localizedRingedToposHom (Over.mk b))
            (Y.iteratedSliceRingedToposHom (Over.mk b))
            (Y.relocalizationRingedToposHom b)).symm.trans
          ((TwoIso.whiskerRight (f.iteratedSliceLocalizedSquare b)
              (Y.relocalizationRingedToposHom b)).trans
            (TwoIso.associator
              (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b)))
              (f.localizedRingedToposHom V') (Y.relocalizationRingedToposHom b))))))
    (TwoIso.trans
      (A := ((X.over (f.u.obj V)).over
        ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
      (B := (Y.over V).ringedTopos)
      ((f.localized V).localizedRingedSquare (Over.mk b))
      ((TwoIso.whiskerRight
          (X.iteratedSliceRelocalizationTriangle ((Over.post (X := V) f.u).obj (Over.mk b)))
          (f.localizedRingedToposHom V)).trans
        (TwoIso.associator
          (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b)))
          (X.relocalizationRingedToposHom (f.u.map b)) (f.localizedRingedToposHom V))))

variable {U' U : X.C} (c : U ⟶ f.u.obj V) (a : U' ⟶ U) (c' : U' ⟶ f.u.obj V')

/-- **Stacks 04J1**, the last assertion: for `a ≫ c = c' ≫ u(b)` the square

```
  (Sh(C/U'), O_{U'})  --j_{U'/U}-->  (Sh(C/U), O_U)
        | f_{c'}                          | f_c
  (Sh(D/V'), O'_{V'}) --j_{V'/V}-->  (Sh(D/V), O'_V)
```

commutes, as a square of ringed topoi.

Both `f_c` and `f_{c'}` are, by definition, the localized morphism of Stacks 04J0 after a
relocalization of Stacks 04IY. Reassociating, the two relocalizations of the source site compose
by `AlgebraicGeometry.RingedSite.relocalizationComp`, and the hypothesis says that the two
composites are the relocalization along one and the same morphism `a ≫ c = c' ≫ u(b)`; what is
left is `Hom.localizedNaturalitySquare`. -/
@[stacks 04J1 "the final assertion: for `b : V' ⟶ V`, `a : U' ⟶ U` and `c'` with \
`a ≫ c = c' ≫ u(b)`, the induced square of ringed topoi on the slices commutes"]
noncomputable def Hom.relocalizedNaturalitySquare (h : a ≫ c = c' ≫ f.u.map b) :
    TwoIso (A := (X.over U').ringedTopos) (B := (Y.over V).ringedTopos)
      (AlgebraicGeometry.RingedToposHom.comp
        (X := (X.over U').ringedTopos) (Y := (Y.over V').ringedTopos)
        (Z := (Y.over V).ringedTopos)
        (Y.relocalizationRingedToposHom b) (f.relocalized c'))
      (AlgebraicGeometry.RingedToposHom.comp
        (X := (X.over U').ringedTopos) (Y := (X.over U).ringedTopos)
        (Z := (Y.over V).ringedTopos)
        (f.relocalized c) (X.relocalizationRingedToposHom a)) := by
  refine (TwoIso.associator (X.relocalizationRingedToposHom c')
    (f.localizedRingedToposHom V') (Y.relocalizationRingedToposHom b)).trans ?_
  refine (TwoIso.whiskerLeft (X.relocalizationRingedToposHom c')
    (f.localizedNaturalitySquare b)).trans ?_
  refine (TwoIso.associator (X.relocalizationRingedToposHom c')
    (X.relocalizationRingedToposHom (f.u.map b))
    (f.localizedRingedToposHom V)).symm.trans ?_
  refine ((X.relocalizationComp c' (f.u.map b)).symm.whiskerRight
    (f.localizedRingedToposHom V)).trans ?_
  rw [← h]
  refine ((X.relocalizationComp a c).whiskerRight (f.localizedRingedToposHom V)).trans ?_
  exact TwoIso.associator (X.relocalizationRingedToposHom a)
    (X.relocalizationRingedToposHom c) (f.localizedRingedToposHom V)

end AlgebraicGeometry.RingedSite

end
