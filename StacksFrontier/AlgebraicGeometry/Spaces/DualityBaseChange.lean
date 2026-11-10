module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for right adjoints of pushforward on algebraic spaces

Let `S` be a scheme and consider a cartesian square of algebraic spaces over `S`

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

in which `X` and `Y'` are Tor independent over `Y`. Write
`a : D_QCoh(𝒪_Y) → D_QCoh(𝒪_X)` and `a' : D_QCoh(𝒪_{Y'}) → D_QCoh(𝒪_{X'})` for right
adjoints of `Rf_*` and `Rf'_*`. The base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` has a
mate `Rg'_* ∘ a' ⟶ a ∘ Rg_*` between the right adjoints, and when that mate is invertible one
obtains the base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*` of the twisted inverse images.

## Main definitions

* `AlgebraicGeometry.Space.TorIndependentBaseChangeSquare` is the cartesian square together
  with its Tor independence hypothesis.
* `AlgebraicGeometry.Space.TorIndependentBaseChangeSquare.DualityData` collects the derived
  functors on the quasi-coherent derived categories of the four corners, their adjunctions,
  and the base change map between them.
* `TorIndependentBaseChangeSquare.DualityData.rightAdjointBaseChange` is the mate
  `Rg'_* ∘ a' ⟶ a ∘ Rg_*` of the base change map.
* `TorIndependentBaseChangeSquare.DualityData.twistedInverseImageBaseChange` is the resulting map
  `L(g')^* ∘ a ⟶ a' ∘ Lg^*`.

## Implementation notes

The quasi-coherent derived categories of the four corners are the ones of Tag 071X, so the
construction is stated about the derived categories of the algebraic spaces of the square
itself. The six derived functors on them, their four adjunctions and the base change map are
carried as data: the library has neither the derived pullback of a morphism of algebraic
spaces nor the restrictions of derived pullback and derived pushforward to quasi-coherent
complexes, and the right adjoints `a`, `a'` are supplied by Tag 0E55, which is an existence
statement. Invertibility of the mate is the content of Tag 0E5C; it is deduced here from
invertibility of the base change map itself, which is the geometric input that Tag 0E5C's
proof cites and which Tor independence provides.

## References

* [Stacks Project, Tag 0E5B](https://stacks.math.columbia.edu/tag/0E5B)
* [Stacks Project, Tag 0E5D](https://stacks.math.columbia.edu/tag/0E5D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

/-- A cartesian square of algebraic spaces over `S` whose upper right and
lower left corners are Tor independent over the lower right corner. -/
@[stacks 0E5B "the Tor-independent cartesian square"]
structure TorIndependentBaseChangeSquare (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) where
  /-- The upper right corner. -/
  X : AlgebraicSpaces B S hS
  /-- The lower right corner. -/
  Y : AlgebraicSpaces B S hS
  /-- The upper left corner. -/
  X' : AlgebraicSpaces B S hS
  /-- The lower left corner. -/
  Y' : AlgebraicSpaces B S hS
  /-- The right vertical arrow. -/
  f : X ⟶ Y
  /-- The bottom horizontal arrow. -/
  g : Y' ⟶ Y
  /-- The left vertical arrow. -/
  f' : X' ⟶ Y'
  /-- The top horizontal arrow. -/
  g' : X' ⟶ X
  /-- The square is cartesian. -/
  isPullback : IsPullback g' f' f g
  /-- The upper right and lower left corners are Tor independent over the lower right one. -/
  torIndependent : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (sq : TorIndependentBaseChangeSquare B S hS)
    [HasSheafify (smallEtaleRingedSite B S hS sq.X.1 sq.X.2).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS sq.X.1 sq.X.2).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify (smallEtaleRingedSite B S hS sq.Y.1 sq.Y.2).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS sq.Y.1 sq.Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify (smallEtaleRingedSite B S hS sq.X'.1 sq.X'.2).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS sq.X'.1 sq.X'.2).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify (smallEtaleRingedSite B S hS sq.Y'.1 sq.Y'.2).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS sq.Y'.1 sq.Y'.2).J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The derived functors entering base change for right adjoints of pushforward along a
Tor-independent cartesian square: derived pullback and derived pushforward along the two
horizontal arrows with their adjunctions, derived pushforward along the two vertical arrows
with right adjoints `a` and `a'`, and the base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*`,
all on the quasi-coherent derived categories of the corners. -/
structure TorIndependentBaseChangeSquare.DualityData where
  /-- Derived pullback `Lg^*` along the bottom arrow. -/
  pullbackG : QuasicoherentDerivedCategory.{u, m} B S hS sq.Y.1 sq.Y.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.Y'.1 sq.Y'.2
  /-- Derived pushforward `Rg_*` along the bottom arrow. -/
  pushforwardG : QuasicoherentDerivedCategory.{u, m} B S hS sq.Y'.1 sq.Y'.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.Y.1 sq.Y.2
  /-- The adjunction `Lg^* ⊣ Rg_*`. -/
  adjG : pullbackG ⊣ pushforwardG
  /-- Derived pullback `L(g')^*` along the top arrow. -/
  pullbackG' : QuasicoherentDerivedCategory.{u, m} B S hS sq.X.1 sq.X.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.X'.1 sq.X'.2
  /-- Derived pushforward `Rg'_*` along the top arrow. -/
  pushforwardG' : QuasicoherentDerivedCategory.{u, m} B S hS sq.X'.1 sq.X'.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.X.1 sq.X.2
  /-- The adjunction `L(g')^* ⊣ Rg'_*`. -/
  adjG' : pullbackG' ⊣ pushforwardG'
  /-- Derived pushforward `Rf_*` along the right arrow. -/
  pushforwardF : QuasicoherentDerivedCategory.{u, m} B S hS sq.X.1 sq.X.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.Y.1 sq.Y.2
  /-- A right adjoint `a` to `Rf_*`. -/
  twistedInverseImage : QuasicoherentDerivedCategory.{u, m} B S hS sq.Y.1 sq.Y.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.X.1 sq.X.2
  /-- The adjunction `Rf_* ⊣ a`. -/
  adjF : pushforwardF ⊣ twistedInverseImage
  /-- Derived pushforward `Rf'_*` along the left arrow. -/
  pushforwardF' : QuasicoherentDerivedCategory.{u, m} B S hS sq.X'.1 sq.X'.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.Y'.1 sq.Y'.2
  /-- A right adjoint `a'` to `Rf'_*`. -/
  twistedInverseImage' : QuasicoherentDerivedCategory.{u, m} B S hS sq.Y'.1 sq.Y'.2 ⥤
    QuasicoherentDerivedCategory.{u, m} B S hS sq.X'.1 sq.X'.2
  /-- The adjunction `Rf'_* ⊣ a'`. -/
  adjF' : pushforwardF' ⊣ twistedInverseImage'
  /-- The base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*`. -/
  baseChange : pushforwardF ⋙ pullbackG ⟶ pullbackG' ⋙ pushforwardF'

namespace TorIndependentBaseChangeSquare.DualityData

variable (D : TorIndependentBaseChangeSquare.DualityData.{u, m} B S hS sq)

/-- The base change map `Rg'_* ∘ a' ⟶ a ∘ Rg_*` between the right adjoints of pushforward,
the mate of the base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*`. -/
noncomputable def rightAdjointBaseChange :
    D.twistedInverseImage' ⋙ D.pushforwardG' ⟶ D.pushforwardG ⋙ D.twistedInverseImage :=
  conjugateEquiv (D.adjG'.comp D.adjF') (D.adjF.comp D.adjG) D.baseChange

/-- The mate of the base change map is an isomorphism as soon as the base change map is. -/
theorem isIso_rightAdjointBaseChange [IsIso D.baseChange] : IsIso D.rightAdjointBaseChange := by
  change IsIso (conjugateEquiv (D.adjG'.comp D.adjF') (D.adjF.comp D.adjG) D.baseChange)
  infer_instance

/-- The base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*` between twisted inverse
images, the composition of the unit of `Lg^* ⊣ Rg_*`, the inverse of the base change map
`Rg'_* ∘ a' ⟶ a ∘ Rg_*` between right adjoints, and the counit of `L(g')^* ⊣ Rg'_*`. -/
@[stacks 0E5D]
noncomputable def twistedInverseImageBaseChange (hbc : IsIso D.baseChange) :
    D.twistedInverseImage ⋙ D.pullbackG' ⟶ D.pullbackG ⋙ D.twistedInverseImage' :=
  haveI : IsIso D.baseChange := hbc
  haveI : IsIso D.rightAdjointBaseChange := D.isIso_rightAdjointBaseChange
  Functor.whiskerRight
      (D.twistedInverseImage.leftUnitor.inv ≫
        Functor.whiskerRight D.adjG.unit D.twistedInverseImage) D.pullbackG' ≫
    Functor.whiskerRight
      ((Functor.associator D.pullbackG D.pushforwardG D.twistedInverseImage).hom ≫
        Functor.whiskerLeft D.pullbackG (inv D.rightAdjointBaseChange) ≫
        (Functor.associator D.pullbackG D.twistedInverseImage' D.pushforwardG').inv)
      D.pullbackG' ≫
    ((Functor.associator (D.pullbackG ⋙ D.twistedInverseImage') D.pushforwardG'
          D.pullbackG').hom ≫
      Functor.whiskerLeft (D.pullbackG ⋙ D.twistedInverseImage') D.adjG'.counit ≫
      (D.pullbackG ⋙ D.twistedInverseImage').rightUnitor.hom)

end TorIndependentBaseChangeSquare.DualityData

end AlgebraicGeometry.Space

end
