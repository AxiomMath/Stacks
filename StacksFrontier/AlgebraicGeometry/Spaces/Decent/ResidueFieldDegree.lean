module

public import Mathlib.LinearAlgebra.Dimension.Free
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField

/-!
# The degree of the residue field extension of a morphism of decent algebraic spaces

A morphism `f : X ⟶ Y` of decent algebraic spaces induces at every point `x` of `X` a
homomorphism from the residue field at the image of `x` to the residue field at `x`. Its
*degree* is the dimension of the latter as a vector space over the former. Degrees multiply
along a composite, because the three residue fields form a tower and transcendence-free
dimension is multiplicative in a tower of fields.

## Main definitions

* `AlgebraicGeometry.Space.degreeOfFieldHom`: the degree of the field extension presented by a
  homomorphism of fields.
* `AlgebraicGeometry.Space.residueDegree`: the degree of the residue field extension of a
  morphism of decent algebraic spaces at a point.

## Main results

* `AlgebraicGeometry.Space.residueDegree_comp`: the residue degree of a composite at a point is
  the product of the residue degree of the second morphism at the image point and the residue
  degree of the first at the point.

## Implementation notes

The degree is `Module.finrank`, which is zero on an extension that is not finite; no finiteness
is assumed, and multiplicativity holds regardless because a field is a free module over any
subfield, which is all that `Module.finrank_mul_finrank` needs. On a tower in which one step is
infinite both sides of the multiplicativity statement vanish.

The homomorphism of residue fields of a composite is not literally the composite of the two
homomorphisms: its source is the residue field at `|f ≫ g| x` while the source of the composite
is the residue field at `|g| (|f| x)`, and those two points of `|Z|` are equal only
propositionally, by `AlgebraicGeometry.Space.pointsMap_comp`. The two are therefore compared
after replacing the point of `X` by a field-valued representative, at which the equation of
points holds by definitional unfolding, so no transport appears. That the composite is the
induced homomorphism is then the uniqueness clause of
`AlgebraicGeometry.Space.existsUnique_isInducedResidueFieldHom`, applied to the composite of
the two squares over the target.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- The degree of the field extension presented by a homomorphism of fields: the dimension of
the target as a vector space over the source. -/
noncomputable def degreeOfFieldHom {K L : Type u} [Field K] [Field L] (φ : K →+* L) : ℕ :=
  @Module.finrank K L _ _ (RingHom.toAlgebra φ).toModule

/-- Degrees of field extensions multiply in a tower: a field is a free module over any subfield,
so the tower law for dimensions applies with no finiteness hypothesis. -/
theorem degreeOfFieldHom_comp {K L M : Type u} [Field K] [Field L] [Field M]
    (φ : K →+* L) (ψ : L →+* M) :
    degreeOfFieldHom (ψ.comp φ) = degreeOfFieldHom φ * degreeOfFieldHom ψ := by
  let _ : Algebra K L := φ.toAlgebra
  let _ : Algebra L M := ψ.toAlgebra
  let _ : Algebra K M := (ψ.comp φ).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact (Module.finrank_mul_finrank K L M).symm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The degree of the residue field extension of a morphism of decent algebraic spaces at a
point: the dimension of the residue field at the point as a vector space over the residue field
at its image. -/
noncomputable def residueDegree (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) : ℕ :=
  degreeOfFieldHom (residueFieldHom B S hS X Y hY hXdec hYdec f x)

/-- The residue degree of a composite of morphisms of decent algebraic spaces at a point is the
product of the residue degree of the second morphism at the image point and the residue degree
of the first morphism at the point. -/
theorem residueDegree_comp (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (hZdec : IsDecentSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X) :
    residueDegree B S hS X Z hZ hXdec hZdec (f ≫ g) x =
      residueDegree B S hS Y Z hZ hYdec hZdec g (pointsMap B S hS X f x) *
        residueDegree B S hS X Y hY hXdec hYdec f x := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hf := residueFieldHom_spec B S hS X Y hY hXdec hYdec f (Quot.mk _ p)
  have hg := residueFieldHom_spec B S hS Y Z hZ hYdec hZdec g
    (pointsMap B S hS X f (Quot.mk _ p))
  change ∃ _, _ ∧ _ at hf hg
  obtain ⟨cf, hcfSpec, hcfComm⟩ := hf
  obtain ⟨cg, hcgSpec, hcgComm⟩ := hg
  have hcomp : residueFieldHom B S hS X Z hZ hXdec hZdec (f ≫ g) (Quot.mk _ p) =
      (residueFieldHom B S hS X Y hY hXdec hYdec f (Quot.mk _ p)).comp
        (residueFieldHom B S hS Y Z hZ hYdec hZdec g
          (pointsMap B S hS X f (Quot.mk _ p))) := by
    refine (existsUnique_isInducedResidueFieldHom B S hS X Z hZ hXdec hZdec (f ≫ g)
      (Quot.mk _ p)).unique
      (residueFieldHom_spec B S hS X Z hZ hXdec hZdec (f ≫ g) (Quot.mk _ p)) ?_
    refine ⟨cf ≫ cg, ?_, ?_⟩
    · change B.inclusion.map (cf.left ≫ cg.left) = _
      rw [Functor.map_comp, hcfSpec, hcgSpec, ← Spec.map_comp]
      rfl
    · change yoneda.map (cf ≫ cg) ≫ residueFieldMorphism B S hS Z hZdec
          (pointsMap B S hS Y g (pointsMap B S hS X f (Quot.mk _ p))) =
        residueFieldMorphism B S hS X hXdec (Quot.mk _ p) ≫ f ≫ g
      calc yoneda.map (cf ≫ cg) ≫ residueFieldMorphism B S hS Z hZdec
              (pointsMap B S hS Y g (pointsMap B S hS X f (Quot.mk _ p)))
          = yoneda.map cf ≫ yoneda.map cg ≫ residueFieldMorphism B S hS Z hZdec
              (pointsMap B S hS Y g (pointsMap B S hS X f (Quot.mk _ p))) := by
            rw [yoneda.map_comp, Category.assoc]
        _ = yoneda.map cf ≫ residueFieldMorphism B S hS Y hYdec
              (pointsMap B S hS X f (Quot.mk _ p)) ≫ g := by rw [hcgComm]
        _ = (yoneda.map cf ≫ residueFieldMorphism B S hS Y hYdec
              (pointsMap B S hS X f (Quot.mk _ p))) ≫ g := by rw [Category.assoc]
        _ = (residueFieldMorphism B S hS X hXdec (Quot.mk _ p) ≫ f) ≫ g := by rw [hcfComm]
        _ = residueFieldMorphism B S hS X hXdec (Quot.mk _ p) ≫ f ≫ g := by
            rw [Category.assoc]
  change degreeOfFieldHom (residueFieldHom B S hS X Z hZ hXdec hZdec (f ≫ g) (Quot.mk _ p)) =
      degreeOfFieldHom (residueFieldHom B S hS Y Z hZ hYdec hZdec g
          (pointsMap B S hS X f (Quot.mk _ p))) *
        degreeOfFieldHom (residueFieldHom B S hS X Y hY hXdec hYdec f (Quot.mk _ p))
  exact (congrArg degreeOfFieldHom hcomp).trans (degreeOfFieldHom_comp _ _)

end AlgebraicGeometry.Space

end
