module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposCoefficientChange
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundary

/-!
# The horizontal morphisms of a complex of first order thickenings, as morphisms of ringed topoi

A complex of first order thickenings of a ringed topos presented on one site,
`Deformation.ToposThickening.FirstOrderThickeningComplex`, carries its two horizontal arrows as
morphisms of *structure sheaves*: `h^♯ : O'₂ ⟶ O'₁` and `O'₃ ⟶ O'₂`, both over `O`. The
corresponding morphisms of *ringed topoi*

```
  (Sh(C), O'₁) --h--> (Sh(C), O'₂) ----> (Sh(C), O'₃)
```

have the identity of `Sh(C)` for their underlying geometric morphism, so they are changes of
coefficient rings on a fixed site in the sense of
`AlgebraicGeometry.RingedToposHom.coefficientMorphism`. This file names them, so that the
horizontal squares of a diagram of thickenings over a diagram of thickenings of the base can be
stated as equalities of morphisms of ringed topoi — which is what it means for such a diagram to
commute, and the form in which
`Deformation.ToposThickening.ShortExactFlatThickeningSituation.comm₁₂` and `.comm₂₃` carry the
two horizontal squares of Situation **Stacks 08VX** in the three-site presentation.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickeningComplex.lowerHorizontalHom`: the morphism
  `h : (Sh(C), O'₁) ⟶ (Sh(C), O'₂)` of the complex.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.upperHorizontalHom`: the morphism
  `(Sh(C), O'₂) ⟶ (Sh(C), O'₃)` of the complex.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex.inverseImage_eq_of_horizontalSquare`
  and `.pushforward_eq_of_horizontalSquare`: a horizontal square of the diagram forces its two
  vertical arrows to have the same inverse image and the same direct image. This is the first
  thing such a square says, and the reason it is needed: the horizontal arrows of either row are
  the identity on topoi, so a square over them is in particular an identification of the two
  geometric morphisms it relates, and without it the two columns' inverse images of the base —
  hence the two columns' pullbacks `f^*𝒥ₖ` of the defining ideals of the lower row — are formed
  along unrelated functors.

## Implementation notes

Both are reducible abbreviations for `AlgebraicGeometry.RingedToposHom.coefficientMorphism`, so
nothing new is constructed: the whole content is the choice of which of the two structure sheaves
is the source and which the target. A morphism of ringed topoi
`g : (Sh(C), O_D) ⟶ (Sh(C), O_E)` has structure map `O_E ⟶ g_*O_D`, so the morphism of ringed
topoi attached to `h^♯ : O'₂ ⟶ O'₁` runs from the *first* thickening to the second, which is the
direction of the horizontal arrows in the source's diagram.

The implicit coefficient sheaves of `upperHorizontalHom` are supplied by name: the target of
`S.h₃₂` is `S.lower.O₂`, which is not the structure sheaf of `Y`, so unification has nothing to
pin the source of the morphism down from.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v' u' w' v'' u'' w'' v''' u''' w'''

namespace Deformation.ToposThickening

namespace FirstOrderThickeningComplex

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y} (S : FirstOrderThickeningComplex i)

/-- The morphism `h : (Sh(C), O'₁) ⟶ (Sh(C), O'₂)` of ringed topoi determined by the morphism
`h^♯ : O'₂ ⟶ O'₁` of thickened structure sheaves of the complex: the change of coefficient
rings on the site of `Y` along `h^♯`. -/
noncomputable abbrev lowerHorizontalHom : RingedToposHom Y (reshape Y S.lower.O₂) :=
  RingedToposHom.coefficientMorphism Y.J S.lower.hSharp

/-- The morphism `(Sh(C), O'₂) ⟶ (Sh(C), O'₃)` of ringed topoi determined by the morphism
`O'₃ ⟶ O'₂` of thickened structure sheaves of the complex: the change of coefficient rings on
the site of `Y` along it. -/
noncomputable abbrev upperHorizontalHom :
    RingedToposHom (reshape Y S.lower.O₂) (reshape Y S.O₃) :=
  RingedToposHom.coefficientMorphism (O := S.O₃) (O' := S.lower.O₂) Y.J S.h₃₂

section Square

variable {W : RingedTopos.{v'', u'', w''}} {Z : RingedTopos.{v''', u''', w'''}}
  [W.J.HasSheafCompose (forget RingCat.{w''})]
  [Z.J.HasSheafCompose (forget RingCat.{w'''})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})]
  {t : RingedToposHom W Z} (T : FirstOrderThickeningComplex t)

/-- **A horizontal square of the diagram identifies the inverse images of its two vertical
arrows.** The horizontal arrow of either row is the identity on topoi, so the square's underlying
equality of morphisms of topoi reads `g₂⁻¹ ∘ 𝟭 = 𝟭 ∘ g₁⁻¹`.

This is stated for an arbitrary square over a horizontal arrow of two complexes: both of the two
squares of Situation Stacks 08VX are of that shape, the second one with the complexes read at
their second thickenings. -/
theorem inverseImage_eq_of_horizontalSquare {g₁ : RingedToposHom Y Z}
    {g₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape Z T.lower.O₂)}
    (h : g₂.comp S.lowerHorizontalHom = T.lowerHorizontalHom.comp g₁) :
    g₂.toToposHom.inverseImage = g₁.toToposHom.inverseImage :=
  congrArg (fun m ↦ m.toToposHom.inverseImage) h

/-- **A horizontal square of the diagram identifies the direct images of its two vertical
arrows.** As for the inverse images: the square's underlying equality of morphisms of topoi reads
`𝟭 ∘ g₂_* = g₁_* ∘ 𝟭`. -/
theorem pushforward_eq_of_horizontalSquare {g₁ : RingedToposHom Y Z}
    {g₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape Z T.lower.O₂)}
    (h : g₂.comp S.lowerHorizontalHom = T.lowerHorizontalHom.comp g₁) :
    g₂.toToposHom.pushforward = g₁.toToposHom.pushforward :=
  congrArg (fun m ↦ m.toToposHom.pushforward) h

/-- **The second horizontal square identifies the inverse images of its two vertical arrows**,
the counterpart of
`Deformation.ToposThickening.FirstOrderThickeningComplex.inverseImage_eq_of_horizontalSquare` for
the arrow `O'₃ ⟶ O'₂` of the upper row and `O_{ℬ'₃} ⟶ O_{ℬ'₂}` of the lower one. -/
theorem inverseImage_eq_of_upperHorizontalSquare
    {g₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape Z T.lower.O₂)}
    {g₃ : RingedToposHom (reshape Y S.O₃) (reshape Z T.O₃)}
    (h : g₃.comp S.upperHorizontalHom = T.upperHorizontalHom.comp g₂) :
    g₃.toToposHom.inverseImage = g₂.toToposHom.inverseImage :=
  congrArg (fun m ↦ m.toToposHom.inverseImage) h

/-- **The second horizontal square identifies the direct images of its two vertical arrows.** -/
theorem pushforward_eq_of_upperHorizontalSquare
    {g₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape Z T.lower.O₂)}
    {g₃ : RingedToposHom (reshape Y S.O₃) (reshape Z T.O₃)}
    (h : g₃.comp S.upperHorizontalHom = T.upperHorizontalHom.comp g₂) :
    g₃.toToposHom.pushforward = g₂.toToposHom.pushforward :=
  congrArg (fun m ↦ m.toToposHom.pushforward) h

end Square

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
