module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism

/-!
# Pushing the de Rham complex of a line bundle forward to its base

Let `f : X ⟶ S` be a morphism of schemes, let `L` be an invertible `𝒪_X`-module and let
`π : 𝕃 ⟶ X` be the total space of `L`, the relative spectrum of `Sym(L)`. The square

```
𝕃 --π--> X
|        |
S --𝟙--> S
```

commutes, so the functoriality of Section 50.3 of the source supplies a canonical map of
de Rham complexes `Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}`. This file names that map and records the two
properties of `π` that every statement about it needs: `π` is an affine morphism, and the
sheaves `Ω^p_{𝕃/S}` of relative differential forms on the total space are right acyclic for
its direct image, so that `π_*Ω^p_{𝕃/S} = Rπ_*Ω^p_{𝕃/S}` degreewise.

## Main definitions

* `Stacks.LineBundle.Situation.deRhamPushforward`: **the canonical map of de Rham complexes
  `Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}`** of the total space of a line bundle, read in abelian sheaves.

## Main results

* `Stacks.LineBundle.Situation.isAffineHom_totalSpaceToBase`: **the projection from the total
  space of a line bundle to its base is an affine morphism**, being the structure morphism of a
  relative spectrum.
* `Stacks.LineBundle.Situation.rightAcyclic_pushforward_totalSpaceForms`: **`Ω^p_{𝕃/S}` is
  right acyclic for `π_*`**, in every degree.
* `Stacks.LineBundle.Situation.isIso_rightDerivedFunctorPlusUnit_totalSpaceForms`:
  **`π_*Ω^p_{𝕃/S} = Rπ_*Ω^p_{𝕃/S}`**, the unit of the derived direct image being invertible on
  `Ω^p_{𝕃/S}` placed in degree zero.

## What this is for, and what it is not

[Stacks, Tag 0FUI] asserts, over a base on which `ℚ` acts, that `Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}` is a
quasi-isomorphism and that de Rham cohomology is therefore unchanged by passing to the total
space. **Neither half is proved here**, and nothing in this file carries a `@[stacks]`
attribute: the map is only constructed, and the two properties of `π` recorded are inputs to
the second half rather than the second half itself.

The acyclicity is stated for the sheaves `Ω^p_{𝕃/S}` as `𝒪_𝕃`-**modules**, which is the
category [Stacks, Tag 01XC] is available in
(`Stacks.AffineHigherDirectImage.rightAcyclic_pushforward`). The de Rham complex itself is a
complex of `(π ≫ f)^{-1}𝒪_S`-modules, and the comparison map above pushes it forward as a
complex of **abelian** sheaves, along
`Stacks.Cohomology.LerayLowDegree.abelianPushforward π.base`; the corresponding acyclicity
statement for that functor is not available in the development, so the degreewise identification
recorded here does not by itself make
`AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived` an isomorphism. The pattern a transfer
between two such readings follows is
`Stacks.DeRhamDirectImage.relativePushforwardHigherIso`, which carries the higher direct images
of an `𝒪_X`-module across the restriction of scalars to `f^{-1}𝒪_S` by Leray's composition
isomorphism, the restriction of scalars being exact.

## Implementation notes

`Stacks.LineBundle.Situation.totalSpaceToBase` is a `def`, so instance search does not see that
it is the structure morphism of a relative spectrum and does not find
`Stacks.RelativeSpec.isAffineHom_toBase`; the instance is therefore restated here at the
line-bundle spelling.

`HasDerivedCategory.standard` is given priority `10000`, as in
`StacksFrontier.AlgebraicGeometry.DerivedAcyclic.AffineMorphism`. At the default priority the
acyclicity statement below does not elaborate within the heartbeat budget: the import closure
of the de Rham tree offers competing choices of derived category, and unification has to unfold
`AlgebraicGeometry.Scheme.Modules` against each of them.

## References

* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Section 50.3](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The projection from the total space of a line bundle to its base is an affine
morphism.** The total space is the relative spectrum of `Sym(L)`, and the structure morphism of
a relative spectrum is affine. -/
instance Situation.isAffineHom_totalSpaceToBase : IsAffineHom D.totalSpaceToBase :=
  Stacks.RelativeSpec.isAffineHom_toBase D.relativeSpecSituation

/-- The square expressing that the total space of a line bundle is a scheme over the base of
the situation through the projection, the morphism of bases being the identity. -/
theorem Situation.totalSpaceToBase_comp :
    D.totalSpaceToBase ≫ D.f = (D.totalSpaceToBase ≫ D.f) ≫ 𝟙 D.S := by
  simp

/-- **The canonical map of de Rham complexes `Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}`** attached to the
total space of a line bundle, read in abelian sheaves: the map of Section 50.3 of the source
for the square whose horizontal arrows are the projection `π : 𝕃 ⟶ X` and the identity of the
base. [Stacks, Tag 0FUI] asserts that it is a quasi-isomorphism when `ℚ` acts on the base; that
is not proved here. -/
def Situation.deRhamPushforward :=
  Scheme.Hom.deRhamAbelianPushforwardMap D.totalSpaceToBase D.f
    (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp

section Acyclic

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts
attribute [local instance] RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint

/-- **The sheaf `Ω^p_{𝕃/S}` of relative differential `p`-forms on the total space of a line
bundle is right acyclic for the direct image along the projection to the base.** The forms are
quasi-coherent in every degree and the projection is affine, so [Stacks, Tag 01XC] applies. -/
theorem Situation.rightAcyclic_pushforward_totalSpaceForms (p : ℕ) :
    (Scheme.Modules.pushforward D.totalSpaceToBase).rightAcyclic
      (Scheme.Hom.relativeDifferentialForms (D.totalSpaceToBase ≫ D.f) (p : ℤ)) :=
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms
    (D.totalSpaceToBase ≫ D.f) p
  Stacks.AffineHigherDirectImage.rightAcyclic_pushforward _ _

/-- **`π_*Ω^p_{𝕃/S} = Rπ_*Ω^p_{𝕃/S}` for the total space of a line bundle**, in every degree:
the unit of the derived direct image is invertible on `Ω^p_{𝕃/S}` placed in degree zero. This is
the acyclicity above read at the unfolding of `CategoryTheory.Functor.rightAcyclic`, and it is
the degreewise form of the identification that the de Rham cohomology half of
[Stacks, Tag 0FUI] rests on. -/
theorem Situation.isIso_rightDerivedFunctorPlusUnit_totalSpaceForms (p : ℕ) :
    IsIso ((Scheme.Modules.pushforward D.totalSpaceToBase).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor D.totalSpace.Modules 0).obj
        (Scheme.Hom.relativeDifferentialForms (D.totalSpaceToBase ≫ D.f) (p : ℤ)))) :=
  D.rightAcyclic_pushforward_totalSpaceForms p

end Acyclic

end Stacks.LineBundle

end
