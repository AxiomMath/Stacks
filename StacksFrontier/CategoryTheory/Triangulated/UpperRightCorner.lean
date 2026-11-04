module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# The upper right corner of two distinguished triangles sharing a middle vertex

Let `A₁ ⟶ M ⟶ C₁ ⟶ A₁⟦1⟧` and `A₂ ⟶ M ⟶ C₂ ⟶ A₂⟦1⟧` be distinguished triangles in a
triangulated category with the same middle vertex `M`. They are the middle row and the middle
column of

```
      A₁ ──────▶ C₂ ──────▶ E
      ‖          ▲          ▲
      A₁ ──────▶ M  ──────▶ C₁
                 ▲          ▲
                 A₂ ═══════ A₂
```

where the first arrow of the top row is the composite `A₁ ⟶ M ⟶ C₂` and the first arrow of the
right column is the composite `A₂ ⟶ M ⟶ C₁`. An object `E` *fits into the upper right corner*
when it turns both the top row and the right column into distinguished triangles and the
remaining square commutes. Such an `E` always exists: this is the nine diagram
`CategoryTheory.Triangulated.exists_nine_diagram` applied to the lower left square, with a zero
object in the empty spot, so that the left column and the bottom row are the contractible
triangles on `A₁` and on `A₂`. More explicitly, `E` may be taken to be any cone of the map
`A₁ ⊞ A₂ ⟶ M` with components `A₁ ⟶ M` and `A₂ ⟶ M`.

## Main definitions

* `CategoryTheory.Triangulated.UpperRightCorner` is the object `E`, its two incoming and two
  outgoing arrows, the two distinguished triangles they close, and the commuting square.
* `CategoryTheory.Triangulated.UpperRightCorner.ofBiprodCone` exhibits any cone of
  `A₁ ⊞ A₂ ⟶ M` as an upper right corner.

## Main results

* `CategoryTheory.Triangulated.nonempty_upperRightCorner`: an upper right corner exists.
* `CategoryTheory.Triangulated.exists_upperRightCorner_isCone`: an upper right corner exists
  whose object is a cone of `A₁ ⊞ A₂ ⟶ M`.

## Implementation notes

The object `E` is a field of a structure rather than the value of a definition. In a
triangulated category a cone is available only as an existence statement
(`CategoryTheory.Pretriangulated.distinguished_cocone_triangle`), so no construction of `E`
has a body, and the source asserts exactly that such an `E` exists.

`ofBiprodCone` uses the octahedron axiom twice, on the two factorizations of `A₁ ⊞ A₂ ⟶ M`
through the two biproduct inclusions. Each gives one of the two triangles, and the two
`CategoryTheory.Triangulated.Octahedron.comm₃` identities say that both composites
`M ⟶ C₂ ⟶ E` and `M ⟶ C₁ ⟶ E` are the second arrow `M ⟶ E` of the cone triangle, which is the
commuting square.

### Scope of the `@[stacks 09DK]` attributes

Tag 09DK is a displayed diagram in the section on fibre products of algebraic spaces and the
cotangent complex, with no enclosing numbered statement; the assertion is the prose explaining
it. That prose has three clauses, and the two carried here are the second and the third: that an
object fitting into the upper right corner exists, by the nine diagram applied to the lower left
square with a zero object in the empty spot, and that it may be taken to be the cone of the map
out of the direct sum. Both are stated here at the generality of an arbitrary triangulated
category, which is how the clause strings of the two attributes read.

The first clause carries no attribute and is not proved here. It asserts that, for morphisms
`X ⟶ B` and `Y ⟶ B` of algebraic spaces over a scheme `S` with `W = X ×_B Y` and projections
`p : W ⟶ X` and `q : W ⟶ Y`, the middle row and the middle column are the fundamental triangles
of Tag 08V1 for `W ⟶ X ⟶ B` and for `W ⟶ Y ⟶ B`, so that `M = L_{W/B}`, `C₁ = L_{W/X}`,
`C₂ = L_{W/Y}`, `A₁ = Lp^*L_{X/B}` and `A₂ = Lq^*L_{Y/B}`. Nothing in this development states
Tag 08V1: the fundamental triangle for a tower of ring maps is available, as Tag 08QX
(`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`), but the chain from there to a morphism of
ringed topoi runs on through Tags 08SV and 08SZ, of which 08SV is not proved — see the
`No @[stacks 08SV]` section of
`StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolution`.

Naming the vertices is blocked independently of that, because Tag 08VD — the cotangent complex
of a morphism of algebraic spaces — is not available either. `Sheaf.cotangentComplex` requires
its sheaves of rings in `CommRingCat.{max u v w}` for a site with objects in `Type u` and
morphisms in `Type v`, whereas `AlgebraicGeometry.Space.smallEtaleRingedTopos` is a
`RingedTopos.{u, u + 1, u}`, whose structure sheaf is therefore one universe too low; lifting it
is not done here.

## References

* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 05R0](https://stacks.math.columbia.edu/tag/05R0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The upper right corner of the two distinguished triangles `(α₁, β₁, _)` and `(α₂, β₂, _)`
sharing their middle vertex `M`.

The field `obj` is the object `E`. `topMap` and `rightMap` are the arrows into it from the top
row and from the right column, `topConnecting` and `rightConnecting` close those two triangles,
and the three conditions are that the top row, whose first arrow is the composite `α₁ ≫ β₂`, is
distinguished, that the right column, whose first arrow is the composite `α₂ ≫ β₁`, is
distinguished, and that the remaining square of the diagram commutes. -/
structure UpperRightCorner {A₁ A₂ M C₁ C₂ : D}
    (α₁ : A₁ ⟶ M) (β₁ : M ⟶ C₁) (α₂ : A₂ ⟶ M) (β₂ : M ⟶ C₂) where
  /-- The object `E` in the upper right corner. -/
  obj : D
  /-- The second arrow of the top row. -/
  topMap : C₂ ⟶ obj
  /-- The second arrow of the right column. -/
  rightMap : C₁ ⟶ obj
  /-- The arrow closing the top row. -/
  topConnecting : obj ⟶ A₁⟦(1 : ℤ)⟧
  /-- The arrow closing the right column. -/
  rightConnecting : obj ⟶ A₂⟦(1 : ℤ)⟧
  /-- The top row is a distinguished triangle. -/
  top_distinguished : Triangle.mk (α₁ ≫ β₂) topMap topConnecting ∈ distTriang D
  /-- The right column is a distinguished triangle. -/
  right_distinguished : Triangle.mk (α₂ ≫ β₁) rightMap rightConnecting ∈ distTriang D
  /-- The upper right square of the diagram commutes. -/
  square_comm : β₂ ≫ topMap = β₁ ≫ rightMap

/-- The biproduct triangle read with the second inclusion first: `A₂ ⟶ A₁ ⊞ A₂ ⟶ A₁` is
distinguished, being `CategoryTheory.Pretriangulated.binaryBiproductTriangle` of `A₂` and `A₁`
composed with the braiding. -/
theorem biprod_inr_triangle_distinguished (A₁ A₂ : D) :
    Triangle.mk (biprod.inr : A₂ ⟶ A₁ ⊞ A₂) (biprod.fst : A₁ ⊞ A₂ ⟶ A₁)
        (0 : A₁ ⟶ A₂⟦(1 : ℤ)⟧) ∈ distTriang D :=
  isomorphic_distinguished _ (binaryBiproductTriangle_distinguished A₂ A₁) _
    (Triangle.isoMk _ _ (Iso.refl _) (biprod.braiding A₁ A₂) (Iso.refl _)
      (by dsimp [binaryBiproductTriangle]
          exact biprod.hom_ext _ _ (by simp) (by simp))
      (by dsimp [binaryBiproductTriangle]; simp)
      (by dsimp [binaryBiproductTriangle]; simp))

section

variable [IsTriangulated D] {A₁ A₂ M C₁ C₂ : D}
  {α₁ : A₁ ⟶ M} {β₁ : M ⟶ C₁} {γ₁ : C₁ ⟶ A₁⟦(1 : ℤ)⟧}
  {α₂ : A₂ ⟶ M} {β₂ : M ⟶ C₂} {γ₂ : C₂ ⟶ A₂⟦(1 : ℤ)⟧}

/-- **Stacks 09DK.** Two distinguished triangles sharing their middle vertex have an upper right
corner: an object `E` turning both the top row `A₁ ⟶ C₂ ⟶ E` and the right column
`A₂ ⟶ C₁ ⟶ E` of the diagram into distinguished triangles, with the remaining square
commutative.

This is the nine diagram of Tag 05R0 applied to the lower left square of the diagram, whose
left column and bottom row are the contractible triangles `0 ⟶ A₁ ⟶ A₁` and `0 ⟶ A₂ ⟶ A₂`;
the square commutes because both of its composites leave a zero object. The identity second
arrow of each contractible triangle is what identifies the first arrow of the third row with
`α₁ ≫ β₂` and the first arrow of the third column with `α₂ ≫ β₁`. -/
@[stacks 09DK "existence of the upper right corner, in a triangulated category"]
theorem nonempty_upperRightCorner (h₁ : Triangle.mk α₁ β₁ γ₁ ∈ distTriang D)
    (h₂ : Triangle.mk α₂ β₂ γ₂ ∈ distTriang D) :
    Nonempty (UpperRightCorner α₁ β₁ α₂ β₂) := by
  obtain ⟨E, w₁, w₂, w₃, c₁, c₂, c₃, hw, hc, hcol, -, hrow, hsquare, -, -, -, -⟩ :=
    exists_nine_diagram (contractible_distinguished₁ A₂) h₁
      (contractible_distinguished₁ A₁) h₂ (by simp)
  have hrow' : α₁ ≫ β₂ = w₁ := by simpa using hrow
  have hcol' : α₂ ≫ β₁ = c₁ := by simpa using hcol.symm
  exact ⟨E, w₂, c₂, w₃, c₃, hrow' ▸ hw, hcol' ▸ hc, hsquare.symm⟩

/-- **Stacks 09DK.** Any cone of the map `A₁ ⊞ A₂ ⟶ M` out of the direct sum, with components
the first arrows `α₁` and `α₂` of the two given triangles, is an upper right corner.

The two arrows into the cone come from the octahedron axiom for the two factorizations of
`biprod.desc α₁ α₂` through the biproduct inclusions: factoring through `biprod.inr` has
`A₁` as the cone of the first map and `C₂` as the cone of the composite, so the octahedron is
the top row, and factoring through `biprod.inl` has `A₂` and `C₁`, so the octahedron is the
right column. In each case the first arrow of the octahedron becomes the required composite
after precomposition with the complementary inclusion. -/
@[stacks 09DK "the cone of the direct sum as an upper right corner, in a triangulated category"]
noncomputable def UpperRightCorner.ofBiprodCone (h₁ : Triangle.mk α₁ β₁ γ₁ ∈ distTriang D)
    (h₂ : Triangle.mk α₂ β₂ γ₂ ∈ distTriang D) {E : D} {ε : M ⟶ E}
    {ζ : E ⟶ (A₁ ⊞ A₂)⟦(1 : ℤ)⟧}
    (hE : Triangle.mk (biprod.desc α₁ α₂) ε ζ ∈ distTriang D) :
    UpperRightCorner α₁ β₁ α₂ β₂ :=
  let top := someOctahedron (u₁₂ := (biprod.inr : A₂ ⟶ A₁ ⊞ A₂))
    (u₂₃ := biprod.desc α₁ α₂) (by simp) (biprod_inr_triangle_distinguished A₁ A₂) hE h₂
  let right := someOctahedron (u₁₂ := (biprod.inl : A₁ ⟶ A₁ ⊞ A₂))
    (u₂₃ := biprod.desc α₁ α₂) (by simp) (binaryBiproductTriangle_distinguished A₁ A₂) hE h₁
  have htop : top.m₁ = α₁ ≫ β₂ := by
    simpa using (biprod.inl : A₁ ⟶ A₁ ⊞ A₂) ≫= top.comm₁
  have hright : right.m₁ = α₂ ≫ β₁ := by
    simpa using (biprod.inr : A₂ ⟶ A₁ ⊞ A₂) ≫= right.comm₁
  { obj := E
    topMap := top.m₃
    rightMap := right.m₃
    topConnecting := ζ ≫ (biprod.fst : A₁ ⊞ A₂ ⟶ A₁)⟦(1 : ℤ)⟧'
    rightConnecting := ζ ≫ (biprod.snd : A₁ ⊞ A₂ ⟶ A₂)⟦(1 : ℤ)⟧'
    top_distinguished := by rw [← htop]; exact top.mem
    right_distinguished := by rw [← hright]; exact right.mem
    square_comm := top.comm₃.trans right.comm₃.symm }

/-- The object of the upper right corner built from a cone is that cone. -/
@[simp]
theorem UpperRightCorner.ofBiprodCone_obj (h₁ : Triangle.mk α₁ β₁ γ₁ ∈ distTriang D)
    (h₂ : Triangle.mk α₂ β₂ γ₂ ∈ distTriang D) {E : D} {ε : M ⟶ E}
    {ζ : E ⟶ (A₁ ⊞ A₂)⟦(1 : ℤ)⟧}
    (hE : Triangle.mk (biprod.desc α₁ α₂) ε ζ ∈ distTriang D) :
    (UpperRightCorner.ofBiprodCone h₁ h₂ hE).obj = E :=
  rfl

/-- **Stacks 09DK.** There is an upper right corner whose object is a cone of the map
`A₁ ⊞ A₂ ⟶ M` out of the direct sum. -/
theorem exists_upperRightCorner_isCone (h₁ : Triangle.mk α₁ β₁ γ₁ ∈ distTriang D)
    (h₂ : Triangle.mk α₂ β₂ γ₂ ∈ distTriang D) :
    ∃ (E : D) (ε : M ⟶ E) (ζ : E ⟶ (A₁ ⊞ A₂)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.desc α₁ α₂) ε ζ ∈ distTriang D ∧
        ∃ c : UpperRightCorner α₁ β₁ α₂ β₂, c.obj = E := by
  obtain ⟨E, ε, ζ, hE⟩ := distinguished_cocone_triangle (biprod.desc α₁ α₂)
  exact ⟨E, ε, ζ, hE, UpperRightCorner.ofBiprodCone h₁ h₂ hE, rfl⟩

end

end CategoryTheory.Triangulated

end
