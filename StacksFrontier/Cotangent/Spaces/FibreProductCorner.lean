module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.CategoryTheory.Triangulated.UpperRightCorner
public import StacksFrontier.Cotangent.Spaces.TransitivityTriangle

/-!
# Fibre products of algebraic spaces and the cotangent complex (Stacks 09DK)

Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, and let
`p : X ×_Z Y ⟶ X` and `q : X ×_Z Y ⟶ Y` be the projections of the fibre product. Stacks 09DK is
the diagram

```
Lp^*L_{X/Z} ──────▶ L_{X×_Z Y/Y} ──────▶ E
     ‖                    ▲              ▲
Lp^*L_{X/Z} ──────▶ L_{X×_Z Y/Z} ──────▶ L_{X×_Z Y/X}
                          ▲              ▲
                    Lq^*L_{Y/Z} ═══════ Lq^*L_{Y/Z}
```

in `D(𝒪_{X×_Z Y})`. Its middle row is the transitivity triangle of Stacks 08V1 for
`X ×_Z Y ⟶ X ⟶ Z`, its middle column the one for `X ×_Z Y ⟶ Y ⟶ Z`, and `E` is an object that
turns the top row and the right column into distinguished triangles. Such an `E` exists by the
nine diagram of Derived Categories, Proposition 05R0, and may be taken to be the cone of the map
`Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z} ⟶ L_{X×_Z Y/Z}`.

## Main definitions

* `AlgebraicGeometry.Space.fibreProductCotangentCorner`: **Stacks 09DK**, for a commutative
  square `p ≫ f = q ≫ g` of algebraic spaces: the object `E` of the upper right corner with its
  two triangles and its commuting square, the two middle triangles being distinguished and `E`
  being a cone of `Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z} ⟶ L_{W/Z}`.
* `AlgebraicGeometry.Space.fiberProductCotangentCorner`: the same for the fibre product
  `X ×_Z Y` itself.

## Implementation notes

The two middle triangles have the same middle vertex, `L_{W/Z}`, but they reach it through two
morphisms `p ≫ f` and `q ≫ g` that are equal rather than identical. The column is therefore read
through `AlgebraicGeometry.Space.cotangentComplexDerivedCongr`, the identification of the two
cotangent complexes along that equality; the row is the transitivity triangle of `p ≫ f` as it
stands.

Nothing in the construction uses that the square is cartesian, so it is stated for an arbitrary
commutative square; `AlgebraicGeometry.Space.fiberProductCotangentCorner` specializes it to the
fibre product of Stacks 02X2, which is the situation of the source.

The object `E` is a cone, and in a triangulated category a cone is available only as an existence
statement, so `E` is chosen; what is canonical, and recorded, is that it is a cone of the map out
of the direct sum and that it carries the diagram.

## References

* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 08V1](https://stacks.math.columbia.edu/tag/08V1)
* [Stacks Project, Tag 05R0](https://stacks.math.columbia.edu/tag/05R0)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] HasDerivedCategory.standard

section Square

variable {X Y Z W : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

/-- The cotangent complexes of two equal morphisms of algebraic spaces are identified along the
equality. -/
noncomputable def cotangentComplexDerivedCongr {a b : W ⟶ Z} (h : a = b) :
    cotangentComplexDerived B S hS a ≅ cotangentComplexDerived B S hS b :=
  eqToIso (by rw [h])

/-- A distinguished triangle whose middle vertex is the cotangent complex of `b` stays
distinguished when that vertex is read as the cotangent complex of a morphism `a = b`. -/
theorem distinguished_cotangentComplexDerivedCongr {a b : W ⟶ Z} (h : a = b)
    {A C : DerivedCategory (smallEtaleModulesULift B S hS W)}
    (α : A ⟶ cotangentComplexDerived B S hS b) (β : cotangentComplexDerived B S hS b ⟶ C)
    (δ : C ⟶ A⟦(1 : ℤ)⟧) (hT : Triangle.mk α β δ ∈ distTriang _) :
    Triangle.mk (α ≫ (cotangentComplexDerivedCongr h).inv)
        ((cotangentComplexDerivedCongr h).hom ≫ β) δ ∈ distTriang _ := by
  subst h
  simpa [cotangentComplexDerivedCongr] using hT

/-- The first arrow `Lq^*L_{Y/Z} ⟶ L_{W/Z}` of the middle column of Stacks 09DK, the middle vertex
read as the cotangent complex of `p ≫ f`. -/
noncomputable abbrev fibreProductColumnUnit (h : p ≫ f = q ≫ g) :
    (derivedPullbackULift q).obj (cotangentComplexDerived B S hS g) ⟶
      cotangentComplexDerived B S hS (p ≫ f) :=
  transitivityUnit q g ≫ (cotangentComplexDerivedCongr h).inv

/-- The second arrow `L_{W/Z} ⟶ L_{W/Y}` of the middle column of Stacks 09DK, the middle vertex
read as the cotangent complex of `p ≫ f`. -/
noncomputable abbrev fibreProductColumnCounit (h : p ≫ f = q ≫ g) :
    cotangentComplexDerived B S hS (p ≫ f) ⟶ cotangentComplexDerived B S hS q :=
  (cotangentComplexDerivedCongr h).hom ≫ transitivityCounit q g

/-- The middle column `Lq^*L_{Y/Z} ⟶ L_{W/Z} ⟶ L_{W/Y} ⟶ Lq^*L_{Y/Z}[1]` of Stacks 09DK is
distinguished: it is the transitivity triangle of Stacks 08V1 for `W ⟶ Y ⟶ Z`, read through the
identification of the cotangent complexes of `q ≫ g` and `p ≫ f`. -/
theorem exists_distTriang_fibreProductColumn (h : p ≫ f = q ≫ g) :
    ∃ δ : cotangentComplexDerived B S hS q ⟶
        ((derivedPullbackULift q).obj (cotangentComplexDerived B S hS g))⟦(1 : ℤ)⟧,
      Triangle.mk (fibreProductColumnUnit h) (fibreProductColumnCounit h) δ ∈
        distTriang (DerivedCategory (smallEtaleModulesULift B S hS W)) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_transitivity q g
  exact ⟨δ, distinguished_cotangentComplexDerivedCongr h _ _ δ hT⟩

/-- The map `Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z} ⟶ L_{W/Z}` out of the direct sum of the two first
vertices, whose cone is the object `E` of Stacks 09DK. -/
noncomputable abbrev fibreProductBiprodMap (h : p ≫ f = q ≫ g) :
    (derivedPullbackULift p).obj (cotangentComplexDerived B S hS f) ⊞
        (derivedPullbackULift q).obj (cotangentComplexDerived B S hS g) ⟶
      cotangentComplexDerived B S hS (p ≫ f) :=
  biprod.desc (transitivityUnit p f) (fibreProductColumnUnit h)

/-- **Stacks 09DK.** Let `p : W ⟶ X` and `q : W ⟶ Y` be morphisms of algebraic spaces over `S`
with `p ≫ f = q ≫ g` for morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, for instance the two projections
of `W = X ×_Z Y`. In `D(𝒪_W)` the diagram

```
Lp^*L_{X/Z} ──────▶ L_{W/Y} ──────▶ E
     ‖                ▲             ▲
Lp^*L_{X/Z} ──────▶ L_{W/Z} ──────▶ L_{W/X}
                      ▲             ▲
                Lq^*L_{Y/Z} ═════ Lq^*L_{Y/Z}
```

exists: its middle row is the transitivity triangle of Stacks 08V1 for `W ⟶ X ⟶ Z`, its middle
column the one for `W ⟶ Y ⟶ Z`, and the object `E` of the upper right corner, with its two
incoming and two outgoing arrows, turns the top row and the right column into distinguished
triangles and makes the remaining square commute. The value of the definition is that upper
right corner, together with the distinguishedness of the two middle triangles and the triangle
`Lp^*L_{X/Z} ⊕ Lq^*L_{Y/Z} ⟶ L_{W/Z} ⟶ E ⟶`, which exhibits `E` as the cone of the map out of
the direct sum. -/
@[stacks 09DK "the diagram for a commutative square, in particular for the two projections of a \
  fibre product; `E` is the cone of the map out of the direct sum"]
noncomputable def fibreProductCotangentCorner (h : p ≫ f = q ≫ g) :
    { E : Triangulated.UpperRightCorner (transitivityUnit p f) (transitivityCounit p f)
          (fibreProductColumnUnit h) (fibreProductColumnCounit h) //
      (∃ δ : cotangentComplexDerived B S hS p ⟶
          ((derivedPullbackULift p).obj (cotangentComplexDerived B S hS f))⟦(1 : ℤ)⟧,
        Triangle.mk (transitivityUnit p f) (transitivityCounit p f) δ ∈
          distTriang (DerivedCategory (smallEtaleModulesULift B S hS W))) ∧
      (∃ δ : cotangentComplexDerived B S hS q ⟶
          ((derivedPullbackULift q).obj (cotangentComplexDerived B S hS g))⟦(1 : ℤ)⟧,
        Triangle.mk (fibreProductColumnUnit h) (fibreProductColumnCounit h) δ ∈
          distTriang (DerivedCategory (smallEtaleModulesULift B S hS W))) ∧
      ∃ (ε : cotangentComplexDerived B S hS (p ≫ f) ⟶ E.obj)
        (ζ : E.obj ⟶ ((derivedPullbackULift p).obj (cotangentComplexDerived B S hS f) ⊞
          (derivedPullbackULift q).obj (cotangentComplexDerived B S hS g))⟦(1 : ℤ)⟧),
        Triangle.mk (fibreProductBiprodMap h) ε ζ ∈
          distTriang (DerivedCategory (smallEtaleModulesULift B S hS W)) } :=
  have h₁ := exists_distTriang_transitivity p f
  have h₂ := exists_distTriang_fibreProductColumn h
  have hc := distinguished_cocone_triangle (fibreProductBiprodMap h)
  ⟨Triangulated.UpperRightCorner.ofBiprodCone h₁.choose_spec h₂.choose_spec
      hc.choose_spec.choose_spec.choose_spec,
    h₁, h₂, ⟨_, _, hc.choose_spec.choose_spec.choose_spec⟩⟩

end Square

section FiberProduct

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- **Stacks 09DK**, for the fibre product `X ×_Z Y` of algebraic spaces (Stacks 02X2) with its
projections `p` and `q`: the diagram of
`AlgebraicGeometry.Space.fibreProductCotangentCorner` in `D(𝒪_{X ×_Z Y})`, built on the
transitivity triangles of `X ×_Z Y ⟶ X ⟶ Z` and `X ×_Z Y ⟶ Y ⟶ Z`. -/
@[stacks 09DK "the diagram for the fibre product `X ×_Z Y` and its two projections"]
noncomputable def fiberProductCotangentCorner :=
  fibreProductCotangentCorner (B := B) (S := S) (hS := hS)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w

end FiberProduct

end AlgebraicGeometry.Space

end
