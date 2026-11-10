module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ActionGroupoid

/-!
# The unit-fixing subgroup scheme of the general linear group

Let `d` be a positive integer. The group `G ⊆ GL_d` named in Stacks 05YQ is the closed subgroup of
invertible `d` by `d` matrices whose first column is the first standard basis vector, that is,
those fixing the vector `e₁` which the structures of Stacks 05YM take as their unit. This file
realizes that group as an affine group scheme over the integers: its coordinate ring is the
coordinate ring of `GL_d` with the first column of the generic matrix set equal to `e₁`, and it
represents the group-valued functor `T ↦ G(Γ(T, 𝒪_T))`, whose values are the
groups `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingSubgroup` already used to describe the
arrows of `FA_d`.

## Main definitions

* `AlgebraicGeometry.generalLinearCoordinate`: the `(i, j)` entry of the generic matrix, as an
  element of the coordinate ring of `GL_d`.
* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingRelations`,
  `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingCoordinateRing` and
  `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingScheme`: the relations saying that the first
  column of the generic matrix is `e₁`, the resulting coordinate ring, and its spectrum.
* `AlgebraicGeometry.FiniteFreeAlgebra.UnitFixingMatrix.mapMonoidHom`: extension of scalars of a
  unit-fixing matrix, as a group homomorphism.
* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingGroupFunctor`: the group-valued functor of
  unit-fixing matrices over global sections.
* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingOver`: the unit-fixing scheme as a scheme over
  the integers, and `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingGrpObj` its group-object
  structure.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingHomEquiv`: homomorphisms out of the unit-fixing
  coordinate ring are exactly unit-fixing invertible matrices.
* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingRepresentableBy`: the unit-fixing scheme over
  the integers represents the group-valued functor of unit-fixing matrices over global sections.
* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingGrpObj`: consequently `G` is a group scheme
  over the integers, with the group law on points being matrix multiplication.

## Implementation notes

A matrix with first column `e₁` is invertible exactly when the complementary `(d-1)` by `(d-1)`
block is, so `G` is isomorphic to `GL_{d-1} × 𝔸^{d-1}` as a scheme; here `G` is instead presented
by the first-column relations inside the coordinate ring of `GL_d`.

The group-object structure is obtained from the functor of points through
`CategoryTheory.GrpObj.ofRepresentableBy`, so the multiplication of `G` is matrix multiplication
by construction. Since `Spec ℤ` is terminal in
schemes, the structure morphism is the unique one and is taken to be
`AlgebraicGeometry.specULiftZIsTerminal.from`.

## References

* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The `(i, j)` entry of the generic invertible matrix, as an element of the coordinate ring of
`GL_d`. Its image in global sections is `AlgebraicGeometry.generalLinearCoordinateSection`. -/
noncomputable abbrev generalLinearCoordinate (d : ℕ) (i j : Fin d) :
    generalLinearCoordinateRing.{u} d :=
  algebraMap (MvPolynomial (Fin d × Fin d) (ULift.{u} ℤ)) (generalLinearCoordinateRing.{u} d)
    (MvPolynomial.X (i, j))

/-- The `(i, j)` entry of the invertible matrix corresponding to a homomorphism `φ` out of the
coordinate ring of `GL_d` is the image under `φ` of the `(i, j)` generic coordinate. -/
theorem generalLinearHomEquiv_val {d : ℕ} {A : Type u} [CommRing A]
    (φ : generalLinearCoordinateRing.{u} d →+* A) (i j : Fin d) :
    ((localizedPolynomialHomEquiv d A φ).val : Matrix (Fin d) (Fin d) A) i j =
      φ (generalLinearCoordinate.{u} d i j) := by
  simp [localizedPolynomialHomEquiv, generalLinearOfLocalizedPolynomialHom]

namespace FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-- The relations cutting the unit-fixing subgroup out of `GL_d`: the first column of the
generic matrix is the first standard basis vector. -/
def unitFixingRelations : Set (generalLinearCoordinateRing.{u} d) :=
  Set.range fun k : Fin d =>
    generalLinearCoordinate.{u} d k 0 - (if k = 0 then 1 else 0)

/-- The coordinate ring of the unit-fixing subgroup scheme of `GL_d`: the coordinate ring of
`GL_d` with the first column of the generic matrix set equal to the first basis vector. -/
abbrev unitFixingCoordinateRing : Type u :=
  generalLinearCoordinateRing.{u} d ⧸ Ideal.span (unitFixingRelations.{u} d)

/-- The group `G` of Stacks 05YQ as an affine scheme over the integers: the closed subscheme of
`GL_d` where the first column of the generic matrix is the first basis vector. -/
noncomputable abbrev unitFixingScheme : Scheme.{u} :=
  Spec (CommRingCat.of (unitFixingCoordinateRing.{u} d))

/-- In the unit-fixing coordinate ring the first column of the generic matrix is the first
basis vector. -/
theorem quotientMk_generalLinearCoordinate (k : Fin d) :
    (Ideal.Quotient.mk (Ideal.span (unitFixingRelations.{u} d)))
        (generalLinearCoordinate.{u} d k 0) = if k = 0 then 1 else 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span (unitFixingRelations.{u} d)))
      (generalLinearCoordinate.{u} d k 0 - (if k = 0 then 1 else 0)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
  rw [map_sub, sub_eq_zero] at h
  rw [h]
  split <;> simp

/-- A homomorphism out of the coordinate ring of `GL_d` sends the first column of the generic
matrix to the first basis vector exactly when the corresponding invertible matrix is
unit-fixing. -/
theorem mem_unitFixingSubgroup_iff {A : Type u} [CommRing A]
    (φ : generalLinearCoordinateRing.{u} d →+* A) :
    localizedPolynomialHomEquiv d A φ ∈ unitFixingSubgroup A d ↔
      ∀ k : Fin d, φ (generalLinearCoordinate.{u} d k 0) = if k = 0 then 1 else 0 :=
  ⟨fun h k => (generalLinearHomEquiv_val φ k 0).symm.trans (h k),
    fun h k => (generalLinearHomEquiv_val φ k 0).trans (h k)⟩

/-- Homomorphisms out of the unit-fixing coordinate ring are exactly the invertible matrices
whose first column is the first basis vector. -/
noncomputable def unitFixingHomEquiv (A : Type u) [CommRing A] :
    (unitFixingCoordinateRing.{u} d →+* A) ≃ UnitFixingMatrix A d where
  toFun f :=
    ⟨localizedPolynomialHomEquiv d A
        (f.comp (Ideal.Quotient.mk (Ideal.span (unitFixingRelations.{u} d)))), by
      rw [mem_unitFixingSubgroup_iff]
      intro k
      change f ((Ideal.Quotient.mk (Ideal.span (unitFixingRelations.{u} d)))
        (generalLinearCoordinate.{u} d k 0)) = _
      rw [quotientMk_generalLinearCoordinate]
      split <;> simp⟩
  invFun g :=
    Ideal.Quotient.lift _ ((localizedPolynomialHomEquiv d A).symm g.1) (by
      have hmem : localizedPolynomialHomEquiv d A
          ((localizedPolynomialHomEquiv d A).symm g.1) ∈ unitFixingSubgroup A d := by
        rw [(localizedPolynomialHomEquiv d A).apply_symm_apply]
        exact g.2
      have hle : Ideal.span (unitFixingRelations.{u} d) ≤
          RingHom.ker ((localizedPolynomialHomEquiv d A).symm g.1) := by
        refine Ideal.span_le.2 ?_
        rintro p ⟨k, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, (mem_unitFixingSubgroup_iff d _).1 hmem k]
        split <;> simp
      exact fun a ha => hle ha)
  left_inv f := Ideal.Quotient.ringHom_ext <| (Ideal.Quotient.lift_comp_mk _ _ _).trans
    ((localizedPolynomialHomEquiv d A).symm_apply_apply _)
  right_inv g := by
    apply Subtype.ext
    change localizedPolynomialHomEquiv d A
      ((Ideal.Quotient.lift _ _ _).comp
        (Ideal.Quotient.mk (Ideal.span (unitFixingRelations.{u} d)))) = g.1
    rw [Ideal.Quotient.lift_comp_mk, Equiv.apply_symm_apply]

/-- Extension of scalars of a unit-fixing matrix is a group homomorphism. -/
def UnitFixingMatrix.mapMonoidHom {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) : UnitFixingMatrix R d →* UnitFixingMatrix S d where
  toFun := UnitFixingMatrix.map f
  map_one' := Subtype.ext (Matrix.GeneralLinearGroup.map_one f)
  map_mul' g h := Subtype.ext (Matrix.GeneralLinearGroup.map_mul f g.1 h.1)

/-- `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingHomEquiv` is compatible with postcomposition
by a ring homomorphism, which on matrices is extension of scalars. -/
theorem unitFixingHomEquiv_comp {A B : Type u} [CommRing A] [CommRing B]
    (f : unitFixingCoordinateRing.{u} d →+* A) (ρ : A →+* B) :
    unitFixingHomEquiv d B (ρ.comp f) =
      UnitFixingMatrix.map ρ (unitFixingHomEquiv d A f) := by
  apply Subtype.ext
  change localizedPolynomialHomEquiv d B ((ρ.comp f).comp (Ideal.Quotient.mk _)) =
    Matrix.GeneralLinearGroup.map ρ
      (localizedPolynomialHomEquiv d A (f.comp (Ideal.Quotient.mk _)))
  rw [← localizedPolynomialHomEquiv_comp]
  rfl

/-- The group-valued functor sending a scheme to the group of invertible `d` by `d` matrices
over its ring of global sections whose first column is the first basis vector. This is the
functor of points of `G` in Stacks 05YN. -/
def unitFixingGroupFunctor : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u} where
  obj X := GrpCat.of (UnitFixingMatrix (Scheme.Γ.obj X) d)
  map f := GrpCat.ofHom (UnitFixingMatrix.mapMonoidHom (Scheme.Γ.map f).hom)
  map_id _ := GrpCat.ext fun _ ↦ Subtype.ext <| Units.ext <| Matrix.ext fun _ _ ↦ rfl
  map_comp _ _ := GrpCat.ext fun _ ↦ Subtype.ext <| Units.ext <| Matrix.ext fun _ _ ↦ rfl

/-- Morphisms from a scheme to the unit-fixing scheme are exactly the unit-fixing invertible
matrices over its ring of global sections. -/
noncomputable def unitFixingSchemeHomEquiv (X : Scheme.{u}) :
    (X ⟶ unitFixingScheme.{u} d) ≃ UnitFixingMatrix (Scheme.Γ.obj (op X)) d :=
  (specRingHomEquiv (unitFixingCoordinateRing.{u} d) X).trans
    (unitFixingHomEquiv d (Scheme.Γ.obj (op X)))

/-- `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingSchemeHomEquiv` is natural: precomposing a
morphism to the unit-fixing scheme with `f : X ⟶ Y` corresponds to extension of scalars of the
matrix along the map on global sections induced by `f`. -/
theorem unitFixingSchemeHomEquiv_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ unitFixingScheme.{u} d) :
    unitFixingSchemeHomEquiv d X (f ≫ g) =
      UnitFixingMatrix.map (Scheme.Γ.map f.op).hom (unitFixingSchemeHomEquiv d Y g) := by
  change unitFixingHomEquiv d _ (specRingHomEquiv _ X (f ≫ g)) = _
  rw [specRingHomEquiv_comp, unitFixingHomEquiv_comp]
  rfl

/-- The unit-fixing scheme, as a scheme over the integers. -/
noncomputable abbrev unitFixingOver : Over (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  Over.mk (specULiftZIsTerminal.from (unitFixingScheme.{u} d))

/-- The group-valued functor of unit-fixing matrices over global sections, on schemes over the
integers. -/
noncomputable abbrev unitFixingGroupOverFunctor :
    (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))).op ⋙ unitFixingGroupFunctor.{u} d

/-- Morphisms of schemes over the integers to the unit-fixing scheme are exactly the unit-fixing
invertible matrices over global sections. -/
noncomputable def unitFixingOverHomEquiv (X : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (X ⟶ unitFixingOver.{u} d) ≃ UnitFixingMatrix (Scheme.Γ.obj (op X.left)) d where
  toFun f := unitFixingSchemeHomEquiv d X.left f.left
  invFun g := Over.homMk ((unitFixingSchemeHomEquiv d X.left).symm g)
    (specULiftZIsTerminal.hom_ext _ _)
  left_inv f := Over.OverMorphism.ext ((unitFixingSchemeHomEquiv d X.left).left_inv f.left)
  right_inv g := (unitFixingSchemeHomEquiv d X.left).right_inv g

/-- The unit-fixing scheme over the integers represents the group-valued functor of unit-fixing
invertible matrices over global sections (Stacks 05YN). -/
noncomputable def unitFixingRepresentableBy :
    (unitFixingGroupOverFunctor.{u} d ⋙ forget GrpCat).RepresentableBy
      (unitFixingOver.{u} d) where
  homEquiv {X} := unitFixingOverHomEquiv d X
  homEquiv_comp f g := unitFixingSchemeHomEquiv_comp d f.left g.left

/-- The unit-fixing subgroup of `GL_d` is a group scheme over the integers, whose group law on
points is matrix multiplication (Stacks 05YN). -/
noncomputable instance unitFixingGrpObj : GrpObj (unitFixingOver.{u} d) :=
  GrpObj.ofRepresentableBy _ (unitFixingGroupOverFunctor.{u} d) (unitFixingRepresentableBy d)

end FiniteFreeAlgebra

end AlgebraicGeometry

end
