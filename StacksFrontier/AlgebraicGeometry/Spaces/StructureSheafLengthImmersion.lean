module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The length of the structure sheaf along closed immersions and isomorphisms

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S` and let `x̄` be a
geometric point of `X`. The germ map `𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` of étale local rings is
surjective, so `𝒪_{X, x̄}` is a quotient of `𝒪_{Y, f(x̄)}`, and a quotient module has at most
the length of the module. Since the stalk of the structure sheaf at a geometric point is the
étale local ring as a module over itself, this gives

`length(𝒪_X at x̄) ≤ length(𝒪_Y at f(x̄))`.

An isomorphism and its inverse are both closed immersions, so for an isomorphism the two
lengths agree; by Stacks 0EE1 they then agree at any two geometric points over corresponding
points of `|X|` and `|Y|`. This is the invariance of the multiplicities of Stacks 0EE9 under an
isomorphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.geometricLength_structureSheafModule_le_of_isClosedImmersion`: the
  length of the structure sheaf does not drop along a closed immersion.
* `AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_of_iso`: an isomorphism of
  algebraic spaces preserves the length of the structure sheaf, at any two geometric points over
  corresponding points.

## Implementation notes

The comparison for an isomorphism is obtained from the inequality in both directions rather
than from a ring isomorphism of étale local rings: the germ map of an isomorphism is
surjective by the closed-immersion case, and its injectivity would need the functoriality of
the germ maps of Stacks 04NG, which the inequality does not. The two geometric points are
allowed to be arbitrary over corresponding points of the point spaces, the change of geometric
point being Stacks 0EE1, `AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The length of the structure sheaf does not drop along a closed immersion.** For a closed
immersion `f : X ⟶ Y` of algebraic spaces over `S` and a geometric point `x̄` of `X`, the length
of `𝒪_X` at `x̄` is at most the length of `𝒪_Y` at `f(x̄)`.

Both stalks are the étale local rings as modules over themselves, and the germ map
`φ : 𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` is surjective. Restricting scalars along `φ` does not change the
length of `𝒪_{X, x̄}`, and as a module over `𝒪_{Y, f(x̄)}` it is a quotient of
`𝒪_{Y, f(x̄)}`. -/
theorem geometricLength_structureSheafModule_le_of_isClosedImmersion {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1) :
    geometricLength B S hS X x (structureSheafModule B S hS X) ≤
      geometricLength B S hS Y (geometricPointMap f.hom x) (structureSheafModule B S hS Y) := by
  rw [geometricLength, geometricLength,
    (structureSheafGeometricStalkEquiv B S hS X x).length_eq,
    (structureSheafGeometricStalkEquiv B S hS Y (geometricPointMap f.hom x)).length_eq]
  set φ := etaleLocalRingMap X.2 f.hom x
  have hφ : Function.Surjective φ :=
    surjective_etaleLocalRingMap_of_isClosedImmersion B S hS f hf x
  let : Algebra (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
      (etaleLocalRing B S hS X.1 x) := φ.toAlgebra
  have hres : Module.length (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x))
        (etaleLocalRing B S hS X.1 x) =
      Module.length (etaleLocalRing B S hS X.1 x) (etaleLocalRing B S hS X.1 x) :=
    Module.length_eq_of_surjective_of_addEquiv φ hφ (AddEquiv.refl _) fun _ _ => rfl
  rw [← hres]
  exact Module.length_le_of_surjective (Algebra.linearMap _ _) hφ

/-- **An isomorphism of algebraic spaces preserves the length of the structure sheaf.** Let
`e : X ≅ Y` be an isomorphism of algebraic spaces over `S`, and let `x̄` and `ȳ` be geometric
points of `X` and `Y` over points of `|X|` and `|Y|` that `e` matches. Then `𝒪_X` has the same
length at `x̄` as `𝒪_Y` has at `ȳ`.

The inequality along a closed immersion applies to `e` and to its inverse, and Stacks 0EE1 moves
the geometric points. -/
theorem geometricLength_structureSheafModule_eq_of_iso {X Y : AlgebraicSpaces B S hS}
    (e : X.1 ≅ Y.1) (x : GeometricPoint B S hS X.1) (y : GeometricPoint B S hS Y.1)
    (hxy : y.image = pointsMap B S hS X.1 e.hom x.image) :
    geometricLength B S hS X x (structureSheafModule B S hS X) =
      geometricLength B S hS Y y (structureSheafModule B S hS Y) := by
  let f : X ⟶ Y := ObjectProperty.homMk e.hom
  let g : Y ⟶ X := ObjectProperty.homMk e.inv
  have hle₁ := geometricLength_structureSheafModule_le_of_isClosedImmersion f
    (isClosedImmersion_of_isIso B S hS e.hom) x
  have hle₂ := geometricLength_structureSheafModule_le_of_isClosedImmersion g
    (isClosedImmersion_of_isIso B S hS e.inv) y
  rw [geometricLength_eq_of_image_eq B S hS Y.2 (geometricPointMap f.hom x) y hxy.symm] at hle₁
  have himg : (geometricPointMap g.hom y).image = x.image := by
    show pointsMap B S hS Y.1 e.inv y.image = x.image
    rw [hxy, ← Function.comp_apply (f := pointsMap B S hS Y.1 e.inv), ← pointsMap_comp,
      e.hom_inv_id, pointsMap_id, id]
  rw [geometricLength_eq_of_image_eq B S hS X.2 (geometricPointMap g.hom y) x himg] at hle₂
  exact le_antisymm hle₁ hle₂

end AlgebraicGeometry.Space

end
