module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Elementary étale neighborhoods of a point of an algebraic space

An *elementary étale neighborhood* of a point `x` of an algebraic space `F` over `S` is a
scheme étale over `F`, pointed above `x`, whose residue-field point maps monomorphically to
`F`. A morphism of elementary étale neighborhoods is a morphism over `F` carrying the
distinguished point to the distinguished point; these morphisms make the elementary étale
neighborhoods of `x` a category.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldObject` and
  `AlgebraicGeometry.Space.residueFieldMap` are the residue-field point of a scheme in the
  big fppf site over `S` and its canonical morphism to that scheme.
* `AlgebraicGeometry.Space.residueFieldObjectMap` is the morphism of residue-field points
  induced by a morphism of the site.
* `AlgebraicGeometry.Space.presheafPoint` is the point of a represented presheaf determined
  by a point of the representing scheme.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood` is an elementary étale neighborhood
  of a point of an algebraic space, and
  `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.Hom` is a morphism of such.

## Main results

* `AlgebraicGeometry.Space.residueFieldObjectMap_comp` and
  `AlgebraicGeometry.Space.isIso_residueFieldObjectMap` record that the induced morphism of
  residue-field points commutes with the canonical morphisms to the schemes, and that it is
  invertible as soon as the morphism of schemes induces an isomorphism of residue fields.

There are no further propositional results beyond the simplification lemmas for the category
structure.

## Implementation notes

The scheme of a neighborhood is an object of the chosen big fppf site. The field spectrum of
its distinguished point is also recorded as an object of that site, so that the canonical
map into the algebraic space is represented by a natural transformation. The condition that
the distinguished point lies above `x` is expressed through the point-set quotient of Tag
03BU and the induced map on points. The category structure on neighborhoods is the one
inherited from the underlying maps of schemes over `S`.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The residue-field point of a scheme in the big fppf site over `S`. -/
def residueFieldObject (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    BigFppfOver B S hS :=
  Over.mk (⟨U.left.1.fromSpecResidueField u ≫ U.hom.1⟩ : B.obj hu ⟶ B.obj hS)

/-- The canonical morphism from the residue-field point to its scheme. -/
def residueFieldMap (U : BigFppfOver B S hS)
    (u : U.left.1) (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    residueFieldObject B S hS U u hu ⟶ U :=
  Over.homMk (⟨U.left.1.fromSpecResidueField u⟩ : B.obj hu ⟶ U.left)

/-- The morphism of residue-field points of the site induced by a morphism of the site. -/
def residueFieldObjectMap (T Q : BigFppfOver B S hS) (f : T ⟶ Q) (p : T.left.1) :
    residueFieldObject B S hS T p (B.residueField_spec_contains T.left.property p) ⟶
      residueFieldObject B S hS Q (f.left.1 p)
        (B.residueField_spec_contains Q.left.property (f.left.1 p)) :=
  Over.homMk ⟨Spec.map (f.left.1.residueFieldMap p)⟩ (by
    apply ObjectProperty.hom_ext
    change Spec.map (f.left.1.residueFieldMap p) ≫
      (Q.left.1.fromSpecResidueField (f.left.1 p) ≫ Q.hom.1) =
      T.left.1.fromSpecResidueField p ≫ T.hom.1
    rw [← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc]
    congr 1
    exact congrArg (fun k ↦ k.1) f.w)

/-- The induced morphism of residue-field points is compatible with the canonical morphisms to
the schemes. -/
theorem residueFieldObjectMap_comp (T Q : BigFppfOver B S hS) (f : T ⟶ Q)
    (p : T.left.1) :
    residueFieldObjectMap B S hS T Q f p ≫
        residueFieldMap B S hS Q (f.left.1 p)
          (B.residueField_spec_contains Q.left.property (f.left.1 p)) =
      residueFieldMap B S hS T p (B.residueField_spec_contains T.left.property p) ≫ f := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f.left.1 p

/-- The induced morphism of residue-field points is an isomorphism as soon as the morphism of
schemes induces an isomorphism of residue fields. -/
theorem isIso_residueFieldObjectMap (T Q : BigFppfOver B S hS) (f : T ⟶ Q)
    (p : T.left.1) [IsIso (f.left.1.residueFieldMap p)] :
    IsIso (residueFieldObjectMap B S hS T Q f p) := by
  have : IsIso (B.inclusion.map ((Over.forget (B.obj hS)).map
      (residueFieldObjectMap B S hS T Q f p))) := by
    change IsIso (Spec.map (f.left.1.residueFieldMap p))
    infer_instance
  have : IsIso ((Over.forget (B.obj hS)).map (residueFieldObjectMap B S hS T Q f p)) :=
    isIso_of_reflects_iso _ B.inclusion
  exact isIso_of_reflects_iso _ (Over.forget (B.obj hS))

/-- The point of the functor represented by `U` specified by `u`.

This runs the other way from `AlgebraicGeometry.Space.schemePoint`, which sends a
field-valued point of `yoneda.obj U` to a point of `U`. -/
def presheafPoint (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    points B S hS (yoneda.obj U) :=
  (⟨U.left.1.residueField u, hu, U.left.1.fromSpecResidueField u ≫ U.hom.1,
      residueFieldMap B S hS U u hu⟩ :
      FieldValuedPoint B S hS (yoneda.obj U)).class B S hS (yoneda.obj U)

/-- **Stacks 0BGU, elementary étale neighborhoods.** A scheme étale over an
algebraic space, pointed above `x`, for which the residue-field point is a
monomorphism into the space. -/
@[stacks 0BGU "elementary étale neighborhoods"]
structure ElementaryEtaleNeighborhood (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) where
  /-- The scheme over the base. -/
  scheme : BigFppfOver B S hS
  /-- The distinguished point of the scheme. -/
  point : scheme.left.1
  /-- Its residue-field spectrum belongs to the chosen big site. -/
  residueField_contained : B.Contains (Spec (.of (scheme.left.1.residueField point)))
  /-- The morphism from the scheme to the algebraic space. -/
  toSpace : yoneda.obj scheme ⟶ F
  /-- The morphism is étale. -/
  etale_toSpace : IsEtale B S hS toSpace
  /-- The distinguished point lies above `x`. -/
  map_point : pointsMap B S hS (yoneda.obj scheme) toSpace
    (presheafPoint B S hS scheme point residueField_contained) = x
  /-- The canonical map from the residue-field point into the space is monic. -/
  mono_residueField : Mono
    (yoneda.map (residueFieldMap B S hS scheme point residueField_contained) ≫ toSpace)

namespace ElementaryEtaleNeighborhood

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {x : points B S hS F}

/-- **Stacks 0BGU, morphisms.** A map of elementary étale neighborhoods is
a map over the algebraic space carrying the chosen point to the chosen point. -/
@[ext, stacks 0BGU "morphisms of elementary étale neighborhoods"]
structure Hom (V W : ElementaryEtaleNeighborhood B S hS F hF x) where
  /-- The map of schemes over `S`. -/
  hom : V.scheme ⟶ W.scheme
  /-- The map is over the algebraic space. -/
  over : yoneda.map hom ≫ W.toSpace = V.toSpace
  /-- The chosen point is preserved. -/
  map_point : hom.left.1 V.point = W.point

/-- The category of elementary étale neighborhoods of `x`, with the morphisms of
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.Hom`; identities and composition are those
of the underlying maps of schemes over `S`. -/
instance : Category (ElementaryEtaleNeighborhood B S hS F hF x) where
  Hom := Hom
  id V := { hom := 𝟙 V.scheme, over := by simp, map_point := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      over := by simp only [yoneda.map_comp, Category.assoc, g.over, f.over]
      map_point := by simp [f.map_point, g.map_point] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- The map of schemes underlying the identity of a neighborhood is the identity. -/
@[simp]
theorem id_hom (V : ElementaryEtaleNeighborhood B S hS F hF x) :
    Hom.hom (𝟙 V) = 𝟙 V.scheme := rfl

/-- The map of schemes underlying a composite of morphisms of neighborhoods is the composite of
the underlying maps. -/
@[simp]
theorem comp_hom {V W Z : ElementaryEtaleNeighborhood B S hS F hF x}
    (f : V ⟶ W) (g : W ⟶ Z) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

end ElementaryEtaleNeighborhood

end AlgebraicGeometry.Space

end
