module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalChangeOfAmbientAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalCoborderSquareAmbient

/-!
# The canonical map of the change-of-ambient square of the lifted square is invertible

Let `j : R ⟶ V` and `j' : R' ⟶ V'` be morphisms of the big fppf category over a scheme `S` whose
underlying morphisms of schemes are immersions, and let

```
R --j--→ V
|        |
b        a
↓        ↓
R' -j'-→ V'
```

commute.  Write `L` for the coborder lift of `j`, `C` for its ambient
`AlgebraicGeometry.Space.immersionCoborderObj`, `J` for
`AlgebraicGeometry.Space.coborderSquareLift`, `W` for its ambient
`AlgebraicGeometry.Space.coborderSquareObj` and `w` for
`AlgebraicGeometry.Space.coborderSquareHom`.  This file proves that the canonical map of
[Stacks Project, Tag 04CP] of the change-of-ambient square

```
R --J--→ W
|        |
𝟙        w
↓        ↓
R --L--→ C
```

is an **isomorphism**, in both the conormal-module spelling of
`AlgebraicGeometry.Space.conormalMapOfImmersions` and the kernel-ideal-power spelling of
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap`.

## Why this is the cancellation the reduction of part (2) needs, and not an `Opens.ι` matching

That square is the upper square of the stack by which the reduction of part (2) of
[Stacks Project, Tag 04G2] to a pair of ambient opens is transported back, and
`Stacks.CategoryTheory.square_transport_of_comp` takes the invertibility of its canonical map as
its hypothesis `hki`.

One might expect the invertibility to have to come from
`Stacks.Immersion.isIso_immersionConormalSheafMap_ι`, and therefore from an identification of
`AlgebraicGeometry.Space.coborderSquareHom` with an `AlgebraicGeometry.Scheme.Opens.ι`.  **It does
not**, and no such identification is made here.  The square above is cartesian — its left edge is
an identity and its right edge a monomorphism — and `w` is étale, being a composite of two
inclusions of opens of the site; so [Stacks Project, Tag 04CO] applies to it, and that tag is
formalized as an **isomorphism**,
`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso`, whose forward map is
exactly the canonical map of [Stacks Project, Tag 04CP] by
`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso_hom`.
`AlgebraicGeometry.Space.coborderEtaleRestrictionIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalChangeOfAmbientAgreement.lean` is the same
construction one level down, at the change-of-ambient square of `j` itself, and is the template
this file follows.

Two further records are corrected by measurement.
`AlgebraicGeometry.Space.coborderSquareHom` is `AlgebraicGeometry.Space.squareAmbientHom`, which
is a composite of **two** `AlgebraicGeometry.Space.openSubHom`s and **no**
`AlgebraicGeometry.Space.openSubMap`; it is `AlgebraicGeometry.Space.squareAmbientMap`, the other
edge, that carries the `openSubMap`.  That is what makes both the monomorphism property and
étaleness two applications of one lemma each.

## Main results

* `AlgebraicGeometry.Space.mono_coborderSquareHom` and
  `AlgebraicGeometry.Space.isEtale_representedSpaceMap_coborderSquareHom`: `w` is a monomorphism
  of the site and represents an étale morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isPullback_representedSpaceMap_coborderSquareHom`: the
  change-of-ambient square of the lifted square is cartesian, with the identity along the top.
* `AlgebraicGeometry.Space.coborderSquareEtaleRestrictionIso`: [Stacks Project, Tag 04CO] at that
  square.
* `AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_coborderSquare`: **the canonical map of
  [Stacks Project, Tag 04CP] of that square is an isomorphism.**
* `AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderSquare`: the same in the
  kernel-ideal-power spelling, which is the spelling the transported naturality squares are
  stated at.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- **The inclusion of the ambient of the lifted square into the coborder ambient of `j` is a
monomorphism.**  It is a composite of two inclusions of opens of the site, each of which is a
monomorphism by `AlgebraicGeometry.Space.mono_openSubHom_of_opens`. -/
theorem mono_coborderSquareHom (hsq : j ≫ a = b ≫ j') :
    Mono (coborderSquareHom B S hS j j' b a hsq) := by
  rw [coborderSquareHom, squareAmbientHom]
  exact @CategoryTheory.mono_comp _ _ _ _ _ _ (mono_openSubHom_of_opens _ _) _
    (mono_openSubHom_of_opens _ _)

/-- **The inclusion of the ambient of the lifted square represents an étale morphism of algebraic
spaces.**  It is a composite of two inclusions of opens of the site, each of which represents an
étale morphism by `AlgebraicGeometry.Space.isEtale_representedSpaceMap_openSubHom`. -/
theorem isEtale_representedSpaceMap_coborderSquareHom (hsq : j ≫ a = b ≫ j') :
    IsEtale B S hS (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq)).hom := by
  rw [coborderSquareHom, squareAmbientHom]
  change IsEtale B S hS (yoneda.map (_ ≫ _))
  rw [yoneda.map_comp]
  exact isEtale_comp B S hS (isEtale_representedSpaceMap_openSubHom B S hS _ _)
    (isEtale_representedSpaceMap_openSubHom B S hS _ _)

/-- **The change-of-ambient square of the lifted square is cartesian**, with the identity along
the top.  This is the square [Stacks Project, Tag 04CO] consumes; it is cartesian for the reason
`AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift` is, namely that a
square with an invertible top edge and a monomorphism along the bottom is cartesian. -/
theorem isPullback_representedSpaceMap_coborderSquareHom (hsq : j ≫ a = b ≫ j') :
    IsPullback (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
      (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
      (schemeSpaceMap (immersionCoborderLift B S hS j))
      (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq)) :=
  have : Mono (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq)) :=
    mono_representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq)
      (mono_coborderSquareHom B S hS j j' b a hsq)
  have hfac : schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq) ≫
      schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq) =
      schemeSpaceMap (immersionCoborderLift B S hS j) :=
    (representedSpaceMap_comp B S hS _ _).trans
      (congrArg (fun m : R ⟶ immersionCoborderObj B S hS j => schemeSpaceMap m)
        (coborderSquareLift_comp_coborderSquareHom B S hS j j' b a hsq))
  hfac ▸ isPullback_id_comp_of_mono _ _

/-- **[Stacks Project, Tag 04CO] at the change-of-ambient square of the lifted square.**  The
cartesian square is `AlgebraicGeometry.Space.isPullback_representedSpaceMap_coborderSquareHom` and
its bottom edge, the inclusion of the ambient of the lifted square, is étale. -/
def coborderSquareEtaleRestrictionIso (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS
          (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))).obj
        (immersionConormalModule B S hS
          (schemeSpaceMap (immersionCoborderLift B S hS j))
          (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)) ≅
      immersionConormalModule B S hS
        (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
        (isImmersion_of_isPullback B S hS
          (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq)
          (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)) :=
  conormalModuleOfImmersionEtaleRestrictionIso B S hS
    (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
    (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
    (schemeSpaceMap (immersionCoborderLift B S hS j))
    (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq))
    (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq)
    (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)
    (isEtale_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq)

/-- **The canonical map of [Stacks Project, Tag 04CP] of the change-of-ambient square of the
lifted square is an isomorphism.**  It is the forward map of
`AlgebraicGeometry.Space.coborderSquareEtaleRestrictionIso` by
`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso_hom`. -/
theorem isIso_conormalMapOfImmersions_coborderSquare (hsq : j ≫ a = b ≫ j') :
    IsIso (conormalMapOfImmersions B S hS
      (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
      (schemeSpaceMap (immersionCoborderLift B S hS j))
      (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
      (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq))
      (isImmersion_of_isPullback B S hS
        (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq)
        (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j))
      (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)
      (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq).w.symm) := by
  rw [← conormalModuleOfImmersionEtaleRestrictionIso_hom B S hS
    (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
    (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
    (schemeSpaceMap (immersionCoborderLift B S hS j))
    (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq))
    (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq)
    (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)
    (isEtale_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq)]
  infer_instance

/-- If the canonical map of a square of immersions is an isomorphism, so is its kernel-ideal-power
spelling, the two differing by the bridges of [Stacks Project, Tag 09RR]. -/
private theorem isIso_kernelIdealZPowSquareMap_of_isIso_conormalMapOfImmersions
    {Z Z' X X' : AlgebraicSpaces B S hS} (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom) (hsq : i ≫ g = f ≫ i')
    (h : IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' hsq)) :
    IsIso (kernelIdealZPowSquareMap B S hS i i' f g hsq 1) := by
  rw [conormalMapOfImmersions_eq_kernelIdealZPowSquareMap] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance
    (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h)

/-- **The canonical map of the change-of-ambient square of the lifted square is an isomorphism, at
the kernel-ideal-power spelling.**  This is the spelling the transported naturality squares of the
reduction of part (2) of [Stacks Project, Tag 04G2] are stated at, and hence the form in which
`Stacks.CategoryTheory.square_transport_of_comp` consumes the cancellation as its hypothesis
`hki`.

`AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdealZPowSquareMap` exhibits
`AlgebraicGeometry.Space.conormalMapOfImmersions` as this map conjugated by the bridge of
[Stacks Project, Tag 09RR] on each side, so the two cancellations are of two isomorphisms. -/
theorem isIso_kernelIdealZPowSquareMap_coborderSquare (hsq : j ≫ a = b ≫ j') :
    IsIso (kernelIdealZPowSquareMap B S hS
      (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
      (schemeSpaceMap (immersionCoborderLift B S hS j))
      (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
      (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq))
      (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq).w.symm 1) := by
  exact isIso_kernelIdealZPowSquareMap_of_isIso_conormalMapOfImmersions B S hS _ _ _ _ _ _ _
    (isIso_conormalMapOfImmersions_coborderSquare B S hS j j' b a hsq)

/-! ### The change-of-ambient square of `j` itself -/

/-- **The canonical map of [Stacks Project, Tag 04CP] of the change-of-ambient square of `j`
itself is an isomorphism.**  The square is
`AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift` and its right edge,
the inclusion of the coborder ambient, is étale, so this is the forward map of
`AlgebraicGeometry.Space.coborderEtaleRestrictionIso`. -/
theorem isIso_conormalMapOfImmersions_coborder :
    IsIso (conormalMapOfImmersions B S hS
      (schemeSpaceMap (immersionCoborderLift B S hS j))
      (schemeSpaceMap j)
      (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
      (schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
      (isImmersion_representedSpaceMap_immersionCoborderLift B S hS j)
      (isImmersion_representedSpaceMap B S hS j)
      (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm) := by
  rw [← conormalModuleOfImmersionEtaleRestrictionIso_hom B S hS
    (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
    (schemeSpaceMap (immersionCoborderLift B S hS j))
    (schemeSpaceMap j)
    (schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
    (isPullback_representedSpaceMap_immersionCoborderLift B S hS j)
    (isImmersion_representedSpaceMap B S hS j)
    (isEtale_representedSpaceMap_openSubHom B S hS V
      ((BigFppfOver.toScheme B S hS).map j).coborderRange)]
  infer_instance

/-- The same in the kernel-ideal-power spelling. -/
theorem isIso_kernelIdealZPowSquareMap_coborder :
    IsIso (kernelIdealZPowSquareMap B S hS
      (schemeSpaceMap (immersionCoborderLift B S hS j))
      (schemeSpaceMap j)
      (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
      (schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
      (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm 1) := by
  exact isIso_kernelIdealZPowSquareMap_of_isIso_conormalMapOfImmersions B S hS _ _ _ _ _ _ _
    (isIso_conormalMapOfImmersions_coborder B S hS j)

/-! ### The two changes of ambient stacked -/

/-- **The outer rectangle of the two change-of-ambient squares**, from the ambient of the lifted
square down to `V`: its top row is the closed factorisation of `j` through that ambient, its
bottom row is `j`, its left edge is a composite of identities and its right edge the composite of
the two inclusions of ambients. -/
theorem coborderSquare_comp_comm (hsq : j ≫ a = b ≫ j') :
    representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq) ≫
        representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) =
      (𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ≫
          𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS)) ≫
        representedSpaceMap B S hS j := by
  change schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq) ≫
        schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq) ≫
          schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) =
      (𝟙 (schemeSpace R : AlgebraicSpaces B S hS) ≫
          𝟙 (schemeSpace R : AlgebraicSpaces B S hS)) ≫
        schemeSpaceMap j
  have w₂ : schemeSpaceMap (immersionCoborderLift B S hS j) ≫
      schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) =
      𝟙 (schemeSpace R : AlgebraicSpaces B S hS) ≫ schemeSpaceMap j :=
    (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm
  rw [← Category.assoc,
    (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq).w.symm,
    Category.assoc, w₂, ← Category.assoc]

/-- **The canonical map of the outer rectangle of the two change-of-ambient squares is an
isomorphism.**  This is the cancellation
`Stacks.CategoryTheory.square_transport_of_comp` takes as its hypothesis `hki` when the reduction
of part (2) of [Stacks Project, Tag 04G2] is read with that rectangle as the upper square.

By `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` the rectangle's map is the inverse
composition comparison of [Stacks Project, Tag 03LU], the inverse image of the map of the lower
change of ambient, and the map of the upper one; the first is an isomorphism because it is a
comparison, and the other two are
`AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborder` and
`AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderSquare`. -/
theorem isIso_kernelIdealZPowSquareMap_coborderSquare_comp (hsq : j ≫ a = b ≫ j') :
    IsIso (kernelIdealZPowSquareMap B S hS
      (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
      (schemeSpaceMap j)
      (𝟙 (schemeSpace R : AlgebraicSpaces B S hS) ≫
        𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
      (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq) ≫
        schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
      (coborderSquare_comp_comm B S hS j j' b a hsq) 1) := by
  have := isIso_kernelIdealZPowSquareMap_coborderSquare B S hS j j' b a hsq
  have := isIso_kernelIdealZPowSquareMap_coborder B S hS j
  rw [kernelIdealZPowSquareMap_comp B S hS
    (schemeSpaceMap (coborderSquareLift B S hS j j' b a hsq))
    (schemeSpaceMap (immersionCoborderLift B S hS j))
    (schemeSpaceMap j)
    (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
    (schemeSpaceMap (coborderSquareHom B S hS j j' b a hsq))
    (𝟙 (schemeSpace R : AlgebraicSpaces B S hS))
    (schemeSpaceMap (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
    (isPullback_representedSpaceMap_coborderSquareHom B S hS j j' b a hsq).w.symm
    (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm
    (coborderSquare_comp_comm B S hS j j' b a hsq) 1]
  infer_instance

end AlgebraicGeometry.Space

end
