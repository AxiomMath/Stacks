module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.GeometricOrbits

/-!
# Set-theoretic invariance, separation of orbits, and orbit spaces

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`, and
let `j : R ⟶ U ×_Z U` be a pre-relation. A morphism out of `U` is *set-theoretically
invariant* when it identifies the two endpoints of every arrow of `j` between points over an
algebraically closed field, and it *separates orbits* when, in addition, two such points with
the same image lie in one orbit. An *orbit space* for `j` is a morphism out of `U` which
equalizes the target and the source of `j`, separates its orbits, and is surjective on
points.

A morphism invariant under `j` in the sense of **Stacks 048E** is set-theoretically
invariant; only the pre-relation is needed for this, not any equivalence-relation property.

## Main definitions

* `AlgebraicGeometry.Space.IsSetTheoreticallyInvariant`: invariance on the points over an
  algebraically closed field.
* `AlgebraicGeometry.Space.SeparatesOrbits`: set-theoretic invariance together with detection
  of the orbits of `AlgebraicGeometry.Space.PreRelation.orbit`.
* `AlgebraicGeometry.Space.IsOrbitSpace`: the orbit-space condition.

## Main results

* `AlgebraicGeometry.Space.isSetTheoreticallyInvariant_of_isInvariant`: a morphism invariant
  under a pre-relation is set-theoretically invariant.

## Implementation notes

The codomain is an arbitrary presheaf, not necessarily one over the base, exactly as for
`AlgebraicGeometry.Space.IsInvariant`, which is the invariance condition of **Stacks 048E**
and is used here directly: it is stated over an arbitrary base object of an arbitrary category
whose slice has binary products, so it applies to the slice of presheaves used here.

The three predicates are abbreviations, so clients may use the endpoint equation, the orbit
implication and the surjectivity condition directly.

## References

* [Stacks Project, Tag 048V](https://stacks.math.columbia.edu/tag/048V)
* [Stacks Project, Tag 048X](https://stacks.math.columbia.edu/tag/048X)
* [Stacks Project, Tag 0493](https://stacks.math.columbia.edu/tag/0493)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism out of `U` is *set-theoretically invariant* under a
pre-relation when it takes the same value at the two endpoints of every arrow of the
pre-relation between points over an algebraically closed field. -/
@[stacks 048V "part (1): set-theoretic invariance"]
abbrev IsSetTheoreticallyInvariant (j : PreRelation R U) (φ : U.left ⟶ X) : Prop :=
  ∀ (p : GeometricPoint B S hS Z)
    (x y : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U),
    j.Rel (yonedaEquiv.symm p.val.value) x y → x.1 ≫ φ = y.1 ≫ φ

/-- A morphism out of `U` *separates the orbits* of a pre-relation
when it is set-theoretically invariant and two points over an algebraically closed field with
the same image lie in one orbit. -/
@[stacks 048V "part (2): separation of orbits"]
abbrev SeparatesOrbits (j : PreRelation R U) (φ : U.left ⟶ X) : Prop :=
  IsSetTheoreticallyInvariant j φ ∧
    ∀ (p : GeometricPoint B S hS Z)
      (x y : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U),
      x.1 ≫ φ = y.1 ≫ φ → y ∈ j.orbit p x

/-- A morphism which is invariant under a pre-relation is set-theoretically invariant. -/
@[stacks 048X]
theorem isSetTheoreticallyInvariant_of_isInvariant (j : PreRelation R U) (φ : U.left ⟶ X)
    (hφ : IsInvariant j φ) :
    IsSetTheoreticallyInvariant j φ := by
  rintro p x y ⟨r, hrx, hry⟩
  simpa only [← Category.assoc, hrx, hry] using
    congrArg (fun f : R.left ⟶ X ↦ r.1 ≫ f) hφ

/-- A morphism out of `U` is an *orbit space* for a pre-relation when it is
invariant under the pre-relation, separates its orbits, and is surjective on points. -/
@[stacks 0493]
abbrev IsOrbitSpace (j : PreRelation R U) (φ : U.left ⟶ X) : Prop :=
  IsInvariant j φ ∧ SeparatesOrbits j φ ∧ IsSurjective B S hS φ

end AlgebraicGeometry.Space

end
