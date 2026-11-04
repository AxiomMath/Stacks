module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Relocalizing a morphism of ringed sites

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D`, `U` an object of `C` and `c : U ⟶ u(V)` a morphism of
`C`. Stacks 04J1 produces from these a morphism of ringed topoi

```
  (f_c, f_c♯) : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V) ,
```

namely the composition of the localized morphism `(f', (f')♯)` of Stacks 04J0, which goes from
the localization at `u(V)`, with the relocalization morphism of Stacks 04IY along `c`; and it
asserts that the resulting square with the two localization morphisms `j_U` and `j_V` commutes,
as does the square comparing `f_c` and `f_{c'}` for compatible `b : V' ⟶ V`, `a : U' ⟶ U` and
`c' : U' ⟶ u(V')`.

## Main definitions

* `AlgebraicGeometry.RingedSite.relocalizationTriangle`: the relocalization triangle of Stacks
  04IY, read as a 2-isomorphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.relocalizationComp`: functoriality of relocalization, as a
  2-isomorphism of ringed topoi: relocalizing along `a ≫ c` is relocalizing along `a` and then
  along `c`.
* `AlgebraicGeometry.RingedSite.Hom.relocalized`: the morphism of ringed topoi `f_c`, defined as
  Stacks defines it, as the composition of the morphism of Stacks 04J0 with the relocalization
  morphism of Stacks 04IY.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.relocalizedLocalizationSquare`: the localization square of
  Stacks 04J1 commutes, as a square of ringed topoi.

## Implementation notes

`relocalized` is *defined* to be the composite the source specifies, so the factorization
`f_c = f' ∘ j_{U/u(V)}` that Stacks 04J1 asserts holds by construction; that is faithful to the
source, whose proof of the factorization is that it is the definition.

The commutativity of the localization square is obtained the way the source obtains it: paste
the square of Stacks 04J0 for `f'` (`AlgebraicGeometry.RingedSite.Hom.localizedRingedSquare`)
with the triangle of Stacks 04IY for the relocalization along `c`, reassociating twice. The
pasting uses only the 2-isomorphism calculus of `AlgebraicGeometry.RingedToposHom.TwoIso`.

What makes the square of Stacks 04J0 available is that the comparison isomorphism of Stacks 03CF
clause (b) has computable components: it is the Beck-Chevalley mate of clause (d)
(`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom`), so its effect on the
structure sheaves is a unit/counit calculation. Clause (d), the *strict* identity
`f'_* j_U^{-1} = j_V^{-1} f_*`, is what the structure map of `f'` is built from and is recorded at
the assembled morphism as
`AlgebraicGeometry.RingedSite.Hom.overPullback_comp_localizedPushforward`.

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

/-- **Stacks 04IY**, as a 2-isomorphism of ringed topoi: localizing a ringed site at `V` is
localizing it at `U` followed by relocalizing along `a : V ⟶ U`.

The underlying isomorphism of direct images is the canonical comparison of the two chosen right
adjoints of the common inverse image, and its compatibility with the three structure maps is the
commutativity of the relocalization triangle. -/
noncomputable def relocalizationTriangle (X : RingedSite.{u, u, u}) {U V : X.C} (a : V ⟶ U) :
    TwoIso (A := ringedTopos (X.over V)) (B := ringedTopos X)
      (X.localizationRingedToposHom V)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
        (Y := ringedTopos (X.over U)) (Z := ringedTopos X)
        (X.localizationRingedToposHom U) (X.relocalizationRingedToposHom a)) where
  e := X.canonicalRelocalizationComparison a
  commutes := X.localizationMorphism_comp_relocalizationMorphism a

/-- **Functoriality of relocalization**, as a 2-isomorphism of ringed topoi: relocalizing along
`a ≫ c` is relocalizing along `a` and then along `c`.

The underlying isomorphism of direct images is the canonical comparison of the two chosen right
adjoints of the common inverse image; compatibility with the three structure maps holds because
all three are units and the comparison of the inverse images is the identity at the structure
sheaf. -/
noncomputable def relocalizationComp (X : RingedSite.{u, u, u}) {T U V : X.C} (a : V ⟶ U)
    (c : U ⟶ T) :
    TwoIso (A := ringedTopos (X.over V)) (B := ringedTopos (X.over T))
      (X.relocalizationRingedToposHom (a ≫ c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
        (Y := ringedTopos (X.over U)) (Z := ringedTopos (X.over T))
        (X.relocalizationRingedToposHom c) (X.relocalizationRingedToposHom a)) where
  e := X.relocalizationCompComparison a c
  commutes := by
    rw [show AlgebraicGeometry.RingedToposHom.forgetFSharp
          (X.relocalizationRingedToposHom (a ≫ c)) =
        (X.overMapMorphismOfTopoi (a ≫ c)).adj.unit.app
          ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) from
      X.forgetRing_relocalizationRingedToposHom_fSharp (a ≫ c),
      show AlgebraicGeometry.RingedToposHom.forgetFSharp
          (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
            (Y := ringedTopos (X.over U)) (Z := ringedTopos (X.over T))
            (X.relocalizationRingedToposHom c) (X.relocalizationRingedToposHom a)) =
        ((X.overMapMorphismOfTopoi c).adj.comp (X.overMapMorphismOfTopoi a).adj).unit.app
          ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) from
      X.forgetRing_relocalizationComp_fSharp a c]
    exact X.unit_relocalizationCompComparison_hom_app a c

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  {U : X.C} {V : Y.C} (c : U ⟶ f.u.obj V)

/-- **Stacks 04J1.** The morphism of ringed topoi
`(f_c, f_c♯) : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)` attached to a morphism of ringed sites
`(f, f♯)` and a morphism `c : U ⟶ u(V)` of the source site: the composition of the localized
morphism of Stacks 04J0, from the localization at `u(V)`, with the relocalization morphism of
Stacks 04IY along `c`.

The factorization that Stacks 04J1 asserts is this definition. -/
@[stacks 04J1 "the morphism `f_c` and its factorization as the morphism of 04J0 after the
  relocalization morphism of 04IY"]
noncomputable def Hom.relocalized :
    AlgebraicGeometry.RingedToposHom (ringedTopos (X.over U)) (ringedTopos (Y.over V)) :=
  AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
    (Y := ringedTopos (X.over (f.u.obj V))) (Z := ringedTopos (Y.over V))
    (f.localizedRingedToposHom V) (X.relocalizationRingedToposHom c)

/-- **Stacks 04J1**, the localization square: the square

```
  (Sh(C/U), O_U)   --j_U-->  (Sh(C), O)
       | f_c                     | f
  (Sh(D/V), O'_V)  --j_V-->  (Sh(D), O')
```

commutes, as a square of ringed topoi.

This is the square of Stacks 04J0 for the localized morphism `f'`
(`AlgebraicGeometry.RingedSite.Hom.localizedRingedSquare`), pasted with the relocalization
triangle of Stacks 04IY for `c : U ⟶ u(V)`. -/
@[stacks 04J1 "commutativity of the localization square, pasted from 04IY's triangle and the
  square of 04J0"]
noncomputable def Hom.relocalizedLocalizationSquare :
    TwoIso (A := ringedTopos (X.over U)) (B := ringedTopos Y)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (Y.over V)) (Z := ringedTopos Y)
        (Y.localizationRingedToposHom V) (f.relocalized c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos X) (Z := ringedTopos Y)
        f.ringedToposHom (X.localizationRingedToposHom U)) :=
  let r : AlgebraicGeometry.RingedToposHom (ringedTopos (X.over U))
      (ringedTopos (X.over (f.u.obj V))) := X.relocalizationRingedToposHom c
  let jU' : AlgebraicGeometry.RingedToposHom (ringedTopos (X.over (f.u.obj V)))
      (ringedTopos X) := X.localizationRingedToposHom (f.u.obj V)
  let jV : AlgebraicGeometry.RingedToposHom (ringedTopos (Y.over V)) (ringedTopos Y) :=
    Y.localizationRingedToposHom V
  let F : AlgebraicGeometry.RingedToposHom (ringedTopos (X.over (f.u.obj V)))
      (ringedTopos (Y.over V)) := f.localizedRingedToposHom V
  let g : AlgebraicGeometry.RingedToposHom (ringedTopos X) (ringedTopos Y) := f.ringedToposHom
  (TwoIso.associator r F jV).trans (((f.localizedRingedSquare V).whiskerLeft r).trans
    ((TwoIso.associator r jU' g).symm.trans
      ((relocalizationTriangle X c).whiskerRight g).symm))

end AlgebraicGeometry.RingedSite

end
