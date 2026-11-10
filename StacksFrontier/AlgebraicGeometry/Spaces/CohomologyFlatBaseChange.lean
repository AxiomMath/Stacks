module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.FlatBaseChange

/-!
# Flat base change for the cohomology of an algebraic space

Let

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

be a cartesian square of algebraic spaces over a scheme `S`, let `ℱ` be a quasi-coherent
`𝒪_X`-module and let `ℱ' = (g')^*ℱ`.  **Stacks 073K** asserts, for `g` flat and `f`
quasi-compact and quasi-separated, that

1. the base change map of **Stacks 0736** is an isomorphism `g^*R^if_*ℱ ⟶ R^if'_*ℱ'` for every
   `i ≥ 0`, and
2. if `Y = Spec(A)` and `Y' = Spec(B)` are affine, then `H^i(X, ℱ) ⊗_A B = H^i(X', ℱ')`.

The square and its coefficient are `AlgebraicGeometry.Space.BaseChangeDiagram`, the data of
**Stacks 073J**.  This file constructs, for that square, the base change map whose
invertibility clause (1) asserts, and proves the equation that characterizes it.

The base change map of **Stacks 0736** exists for a commutative square of ringed topoi whose
two horizontal morphisms are flat, so the two inputs that turn the square of algebraic spaces
above into one are: flatness of `g'`, which is **Stacks 03MO** and so is not an extra
hypothesis; and the translation of flatness of a morphism of algebraic spaces into flatness of
its morphism of small étale ringed topoi, which is **Stacks 073C**.  The commutativity datum
that **Stacks 0736** consumes is the comparison of the two composite direct images around the
square, assembled below from the composition law for direct images of **Stacks 03LU**.

## Main definitions

* `AlgebraicGeometry.Space.BaseChangeDiagram.directImageSquareIso`: the comparison
  `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images of `𝒪`-modules around the
  square, from the composition law of **Stacks 03LU** and the commutativity of the square.
* `AlgebraicGeometry.Space.BaseChangeDiagram.flatPullbackBase` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.flatPullbackSource`: the inverse images `g^*` and
  `(g')^*` of `𝒪`-modules on bounded below derived categories, for `g` flat.
* `AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeMap`: **the base change map**
  `g^*Rf_*ℱ ⟶ Rf'_*(g')^*ℱ` of **Stacks 0736** for the cartesian square.

## Main results

* `AlgebraicGeometry.Space.BaseChangeDiagram.isFlat_smallEtaleRingedToposHom_base` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.isFlat_smallEtaleRingedToposHom_source`: flatness
  of the morphisms of small étale ringed topoi of `g` and of `g'`, the two inputs that
  **Stacks 0736** asks of the square.
* `AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeMap_fac`: composed with the
  derived-functor unit of `Rf_*`, the base change map is the degreewise comparison on the
  bounded below homotopy category.  Since `Rf_* ⋙ g^*` is a right derived functor of
  `f_* ⋙ g^*` with that unit, this equation determines the map.

## Implementation notes

### Why the instance arguments are given explicitly

The functors below are formed at the small étale ringed topoi of algebraic spaces, which are
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`: the site has objects in `Type (u + 1)` and
morphisms and sections in `Type u`.  Elaboration does not recover those three universes from
the ambient data on its own, so the source and target ringed topoi of every direct and inverse
image below are supplied as named arguments.  For the same reason the two additivity instances
are restated at this seating: the general instances
`Stacks.Sheaves.RingedToposModules.additive_pushforwardModules` and
`Stacks.Sheaves.DerivedPullback.pullbackModules_additive` apply, but instance search does not
find them with the universes undetermined, and additivity is what lets the two images be
applied degreewise to complexes and hence right derived.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules (pushforwardModules)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image of `𝒪`-modules along a morphism of algebraic spaces, read through the
morphism of small étale ringed topoi of **Stacks 03G8**, is additive.  This is the general
additivity of the direct image of
**Stacks 03D6**, part (1), restated at the seating of the small étale ringed topoi. -/
instance additive_pushforwardModules_smallEtaleRingedToposHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (pushforwardModules
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom).Additive :=
  Stacks.Sheaves.RingedToposModules.additive_pushforwardModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y) _

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces, read through the
morphism of small étale ringed topoi of **Stacks 03G8**, is additive.  This is the general
additivity of the inverse image of
**Stacks 03D6**, part (2) — a left adjoint by **Stacks 03D7** — restated at the seating of the
small étale ringed topoi. -/
instance additive_pullbackModules_smallEtaleRingedToposHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules).Additive :=
  Stacks.Sheaves.DerivedPullback.pullbackModules_additive
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y) _

variable {B S hS}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-- The comparison `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images of
`𝒪`-modules around a cartesian square of algebraic spaces.

Both composites are compared with the direct image of the common composite `g' ≫ f = f' ≫ g`
by the composition law of **Stacks 03LU**; the direct images are those of **Stacks 03D6**,
part (1), for the morphisms of small étale ringed topoi of **Stacks 03G8**. -/
def directImageSquareIso :
    pushforwardModules (X := smallEtaleRingedTopos B S hS D.X')
        (Y := smallEtaleRingedTopos B S hS D.X)
        (smallEtaleRingedToposHom B S hS D.g').toRingedToposModulesHom ⋙
        pushforwardModules (X := smallEtaleRingedTopos B S hS D.X)
          (Y := smallEtaleRingedTopos B S hS D.Y)
          (smallEtaleRingedToposHom B S hS D.f).toRingedToposModulesHom ≅
      pushforwardModules (X := smallEtaleRingedTopos B S hS D.X')
          (Y := smallEtaleRingedTopos B S hS D.Y')
          (smallEtaleRingedToposHom B S hS D.f').toRingedToposModulesHom ⋙
        pushforwardModules (X := smallEtaleRingedTopos B S hS D.Y')
          (Y := smallEtaleRingedTopos B S hS D.Y)
          (smallEtaleRingedToposHom B S hS D.g).toRingedToposModulesHom :=
  Functor.isoWhiskerRight (modulePushforwardIso B S hS D.g') _ ≪≫
    Functor.isoWhiskerLeft _ (modulePushforwardIso B S hS D.f) ≪≫
    modulePushforwardCompIso B S hS D.g' D.f ≪≫
    eqToIso (congrArg (modulePushforward B S hS) D.isPullback.w) ≪≫
    (modulePushforwardCompIso B S hS D.f' D.g).symm ≪≫
    Functor.isoWhiskerLeft _ (modulePushforwardIso B S hS D.g).symm ≪≫
    Functor.isoWhiskerRight (modulePushforwardIso B S hS D.f').symm _

/-- **Stacks 073C** for the lower horizontal morphism of the square: if `g` is flat, so is its
morphism of small étale ringed topoi. -/
theorem isFlat_smallEtaleRingedToposHom_base (hg : IsFlat B S hS D.g.hom) :
    RingedToposHom.IsFlat (X := smallEtaleRingedTopos B S hS D.Y')
      (Y := smallEtaleRingedTopos B S hS D.Y) (smallEtaleRingedToposHom B S hS D.g) :=
  (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS D.g).1 hg

/-- The morphism of small étale ringed topoi of the upper horizontal morphism `g'` of the
square is flat as soon as `g` is: `g'` is flat as a base change of `g` (**Stacks 03MO**), and
**Stacks 073C** turns this into flatness of the morphism of ringed topoi. -/
theorem isFlat_smallEtaleRingedToposHom_source (hg : IsFlat B S hS D.g.hom) :
    RingedToposHom.IsFlat (X := smallEtaleRingedTopos B S hS D.X')
      (Y := smallEtaleRingedTopos B S hS D.X) (smallEtaleRingedToposHom B S hS D.g') :=
  (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS D.g').1
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback D.isPullback.flip hg)

/-- The inverse image `g^*` of `𝒪`-modules along the flat lower horizontal morphism of the
square, on bounded below derived categories.  Flatness makes it the degreewise inverse image,
by `Stacks.Cohomology.ToposBaseChange.flatPullbackComparison`. -/
abbrev flatPullbackBase (hg : IsFlat B S hS D.g.hom) :=
  Stacks.Cohomology.ToposBaseChange.flatPullback
    (X := smallEtaleRingedTopos B S hS D.Y') (Y := smallEtaleRingedTopos B S hS D.Y)
    (smallEtaleRingedToposHom B S hS D.g) (D.isFlat_smallEtaleRingedToposHom_base hg)

/-- The inverse image `(g')^*` of `𝒪`-modules along the flat upper horizontal morphism of the
square, on bounded below derived categories.  It is the functor that produces the coefficient
`ℱ' = (g')^*ℱ` of **Stacks 073J** from `ℱ`, derived. -/
abbrev flatPullbackSource (hg : IsFlat B S hS D.g.hom) :=
  Stacks.Cohomology.ToposBaseChange.flatPullback
    (X := smallEtaleRingedTopos B S hS D.X') (Y := smallEtaleRingedTopos B S hS D.X)
    (smallEtaleRingedToposHom B S hS D.g') (D.isFlat_smallEtaleRingedToposHom_source hg)

/-- **The base change map `g^*Rf_* ⟶ Rf'_*(g')^*`** of **Stacks 0736**, for the cartesian
square of small étale ringed topoi attached to a cartesian square of algebraic spaces whose
lower horizontal morphism `g` is flat.

**Stacks 073K**, part (1) asserts that it is invertible.  It is built from the comparison
`directImageSquareIso` of the two composite direct images and the flatness of the morphisms of
ringed topoi of `g` and `g'` (`isFlat_smallEtaleRingedToposHom_base`,
`isFlat_smallEtaleRingedToposHom_source`). -/
@[stacks 073K "the base change map of Tag 0736 for the cartesian square, whose invertibility is
  what part (1) asserts. The map is CONSTRUCTED and characterized; neither part (1) nor part (2)
  of the tag is proved here"]
def baseChangeMap (hg : IsFlat B S hS D.g.hom) :
    (pushforwardModules (X := smallEtaleRingedTopos B S hS D.X)
          (Y := smallEtaleRingedTopos B S hS D.Y)
          (smallEtaleRingedToposHom B S hS D.f).toRingedToposModulesHom).rightDerivedFunctorPlus ⋙
        D.flatPullbackBase hg ⟶
      D.flatPullbackSource hg ⋙
        (pushforwardModules (X := smallEtaleRingedTopos B S hS D.X')
          (Y := smallEtaleRingedTopos B S hS D.Y')
          (smallEtaleRingedToposHom B S hS D.f').toRingedToposModulesHom).rightDerivedFunctorPlus :=
  Stacks.Cohomology.ToposBaseChange.baseChangeMap
    (smallEtaleRingedToposHom B S hS D.f) (smallEtaleRingedToposHom B S hS D.f')
    (smallEtaleRingedToposHom B S hS D.g) (smallEtaleRingedToposHom B S hS D.g')
    D.directImageSquareIso (D.isFlat_smallEtaleRingedToposHom_base hg)
    (D.isFlat_smallEtaleRingedToposHom_source hg)

/-- **The base change map of the square is the canonical one.**  Composed with the
derived-functor unit of `Rf_*`, it is the degreewise comparison on the bounded below homotopy
category of `𝒪_X`-modules.  Since `Rf_* ⋙ g^*` is a right derived functor of `f_* ⋙ g^*` with
that unit, this equation determines the map. -/
@[stacks 073K "canonical characterization of the base change map of Tag 0736 for the cartesian
  square: it is determined by its agreement, after the derived-functor unit of Rf_*, with the
  degreewise comparison. Neither part (1) nor part (2) of the tag is proved here"]
theorem baseChangeMap_fac (hg : IsFlat B S hS D.g.hom) :
    Functor.whiskerRight
        (pushforwardModules (X := smallEtaleRingedTopos B S hS D.X)
          (Y := smallEtaleRingedTopos B S hS D.Y)
          (smallEtaleRingedToposHom B S hS
            D.f).toRingedToposModulesHom).rightDerivedFunctorPlusUnith
        (D.flatPullbackBase hg) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (D.baseChangeMap hg) =
        Stacks.Cohomology.ToposBaseChange.baseChangeOnHomotopyCategory
          (smallEtaleRingedToposHom B S hS D.f) (smallEtaleRingedToposHom B S hS D.f')
          (smallEtaleRingedToposHom B S hS D.g) (smallEtaleRingedToposHom B S hS D.g')
          D.directImageSquareIso (D.isFlat_smallEtaleRingedToposHom_base hg)
          (D.isFlat_smallEtaleRingedToposHom_source hg) :=
  Stacks.Cohomology.ToposBaseChange.baseChangeMap_fac
    (smallEtaleRingedToposHom B S hS D.f) (smallEtaleRingedToposHom B S hS D.f')
    (smallEtaleRingedToposHom B S hS D.g) (smallEtaleRingedToposHom B S hS D.g')
    D.directImageSquareIso (D.isFlat_smallEtaleRingedToposHom_base hg)
    (D.isFlat_smallEtaleRingedToposHom_source hg)

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
