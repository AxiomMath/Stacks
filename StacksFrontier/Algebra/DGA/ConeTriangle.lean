module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.Algebra.DGA.HomotopyCategoryShift
public import StacksFrontier.Algebra.DGA.Cone
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeTriangle

/-!
# Cone triangles in the homotopy category of differential graded modules

A homomorphism `f : K ⟶ L` of right differential graded `A`-modules sits in the triangle
`K ⟶ L ⟶ C(f) ⟶ K[1]` built from the mapping cone and its canonical inclusion and
projection.  This file records that triangle in the homotopy category and the class of
triangles isomorphic to one of this form, which is the class of distinguished triangles of the
homotopy category.

## Main definitions

* `DifferentialGradedModule.coneTriangle` is the cone triangle of a homomorphism, as a triangle
  in the homotopy category.
* `DifferentialGradedModule.distinguishedConeTriangles` is the class of triangles isomorphic to
  a cone triangle.

## Main results

* `DifferentialGradedModule.isomorphic_mem_distinguishedConeTriangles`: the class is closed
  under isomorphism of triangles.
* `DifferentialGradedModule.exists_mem_distinguishedConeTriangles`: every morphism of the
  homotopy category is the first morphism of a triangle in the class.
* `DifferentialGradedModule.isZero_quotient_coneObject_id`: the cone on an identity is zero in
  the homotopy category, and
  `DifferentialGradedModule.contractible_mem_distinguishedConeTriangles`: the contractible
  triangle on an object lies in the class.

## Implementation notes

The third morphism of the cone triangle is the canonical projection `C(f) ⟶ K[1]` followed by
the identification of the class of `K[1]` with the shift of the class of `K`.  Those two objects
are in fact equal, by `DifferentialGradedModule.quotient_obj_shift`, the shift on the homotopy
category being induced from the one on differential graded modules; but the equality is not
natural in the module, and the induced shift is irreducible, so the transport along it cannot be
compared with the shift of a morphism.  The identification used is therefore
`DifferentialGradedModule.quotientShiftIso`, the component of the isomorphism witnessing that
the quotient functor commutes with the shift, whose naturality is
`DifferentialGradedModule.quotient_map_shiftMap_comp_quotientShiftIso`.

Every morphism of the homotopy category is the class of a homomorphism, the quotient functor
being full, and an object of the homotopy category is the class of its own representative, so
the cone triangle of a chosen representative has the given morphism as its first morphism with
no comparison isomorphism needed.

The cone on an identity is contractible: its underlying module is `K ⊕ K[1]` with differential
`(l, k) ↦ (dl + k, -dk)`, and `(l, k) ↦ (0, l)` is a homotopy from the identity to zero.  It
lowers the degree by one and is right `A`-linear because it is built from a projection and an
injection of the direct sum.

## References

* [Stacks Project, Tag 09KA](https://stacks.math.columbia.edu/tag/09KA)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-- The cone triangle `K ⟶ L ⟶ C(f) ⟶ K[1]` of a homomorphism of right differential graded
`A`-modules, as a triangle in the homotopy category. -/
noncomputable def coneTriangle {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) :
    Triangle (HomotopyCategory.{u, v, w} A) :=
  Triangle.mk ((toHomotopyCategory A).map f) ((toHomotopyCategory A).map (coneIncl f))
    ((toHomotopyCategory A).map (coneProj f) ≫ (quotientShiftIso K 1).hom)

section

variable {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L)

/-- The first vertex of the cone triangle of `f : K ⟶ L` is the class of `K`. -/
@[simp] theorem coneTriangle_obj₁ : (coneTriangle f).obj₁ = (toHomotopyCategory A).obj K := rfl

/-- The second vertex of the cone triangle of `f : K ⟶ L` is the class of `L`. -/
@[simp] theorem coneTriangle_obj₂ : (coneTriangle f).obj₂ = (toHomotopyCategory A).obj L := rfl

/-- The third vertex of the cone triangle of `f` is the class of the cone on `f`. -/
@[simp] theorem coneTriangle_obj₃ :
    (coneTriangle f).obj₃ = (toHomotopyCategory A).obj (coneObject f) := rfl

/-- The first morphism of the cone triangle of `f` is the class of `f`. -/
@[simp] theorem coneTriangle_mor₁ : (coneTriangle f).mor₁ = (toHomotopyCategory A).map f := rfl

/-- The second morphism of the cone triangle of `f` is the class of the cone inclusion. -/
@[simp] theorem coneTriangle_mor₂ :
    (coneTriangle f).mor₂ = (toHomotopyCategory A).map (coneIncl f) := rfl

/-- The third morphism of the cone triangle of `f : K ⟶ L` is the class of the cone projection
followed by the identification `DifferentialGradedModule.quotientShiftIso` of the class of `K[1]`
with the shift of the class of `K`. -/
@[simp] theorem coneTriangle_mor₃ :
    (coneTriangle f).mor₃ =
      (toHomotopyCategory A).map (coneProj f) ≫ (quotientShiftIso K 1).hom := rfl

end

/-- The class of distinguished triangles of the homotopy category of right differential graded
`A`-modules: the triangles isomorphic to the cone triangle of a homomorphism. -/
def distinguishedConeTriangles : Set (Triangle (HomotopyCategory.{u, v, w} A)) :=
  fun T => ∃ (K L : DifferentialGradedModule.{u, v, w} A) (f : K ⟶ L),
    Nonempty (T ≅ coneTriangle f)

/-- A triangle isomorphic to a cone triangle is one. -/
theorem isomorphic_mem_distinguishedConeTriangles
    (T₁ : Triangle (HomotopyCategory.{u, v, w} A))
    (hT₁ : T₁ ∈ distinguishedConeTriangles.{u, v, w} (A := A))
    (T₂ : Triangle (HomotopyCategory.{u, v, w} A)) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedConeTriangles.{u, v, w} (A := A) := by
  obtain ⟨K, L, f, ⟨e₁⟩⟩ := hT₁
  exact ⟨K, L, f, ⟨e ≪≫ e₁⟩⟩

/-- Every morphism of the homotopy category is the first morphism of a cone triangle: it is the
class of a homomorphism, and that homomorphism has a cone. -/
theorem exists_mem_distinguishedConeTriangles {X Y : HomotopyCategory.{u, v, w} A} (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory.{u, v, w} A) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedConeTriangles.{u, v, w} (A := A) := by
  obtain ⟨f₀, rfl⟩ := (toHomotopyCategory A).map_surjective f
  exact ⟨_, (coneTriangle f₀).mor₂, (coneTriangle f₀).mor₃,
    X.as, Y.as, f₀, ⟨Iso.refl _⟩⟩

/-- A homotopy from the identity of the cone on an identity to zero: on `K ⊕ K[1]` the map
`(l, k) ↦ (0, l)` lowers the degree by one, and the cone differential `(l, k) ↦ (dl + k, -dk)`
makes it a contracting homotopy. -/
noncomputable def coneIdContraction (K : DifferentialGradedModule.{u, v, w} A) :
    Homotopy (Hom.id (coneObject (𝟙 K))) 0 where
  toLinearMap :=
    (LinearMap.inr (MulOpposite A.A) K.M K.M).comp (LinearMap.fst (MulOpposite A.A) K.M K.M)
  map_grading n x hx := by
    refine (coneGrading_mem (n - 1) (0, x.1)).mpr ⟨(K.grading (n - 1)).zero_mem, ?_⟩
    have := ((coneGrading_mem n x).mp hx).1
    rwa [show n - 1 + 1 = n by ring]
  homotopy_eq x := by
    have h₁ : (coneObject (𝟙 K)).d ((0 : K.M), x.1) = (K.d 0 + x.1, -K.d x.1) :=
      coneD_apply (𝟙 K) _
    have h₂ : (coneObject (𝟙 K)).d x = (K.d x.1 + x.2, -K.d x.2) := coneD_apply (𝟙 K) x
    refine Prod.ext ?_ ?_
    · change (x - 0).1 = ((coneObject (𝟙 K)).d ((0 : K.M), x.1)).1 + (0 : K.M)
      rw [h₁]
      simp
    · change (x - 0).2 =
        ((coneObject (𝟙 K)).d ((0 : K.M), x.1)).2 + ((coneObject (𝟙 K)).d x).1
      rw [h₁, h₂]
      simp

/-- The cone on an identity is a zero object of the homotopy category: its identity is
homotopic to zero. -/
theorem isZero_quotient_coneObject_id (K : DifferentialGradedModule.{u, v, w} A) :
    IsZero ((toHomotopyCategory A).obj (coneObject (𝟙 K))) := by
  rw [IsZero.iff_id_eq_zero, ← (toHomotopyCategory A).map_id]
  exact (Quotient.functor_map_eq_iff (homotopyRel.{u, v, w} A) _ _).mpr ⟨coneIdContraction K⟩

/-- The contractible triangle `X ⟶ X ⟶ 0 ⟶ X[1]` on an object of the homotopy category is the
cone triangle of the identity of a representative. -/
theorem contractible_mem_distinguishedConeTriangles (X : HomotopyCategory.{u, v, w} A) :
    contractibleTriangle X ∈ distinguishedConeTriangles.{u, v, w} (A := A) := by
  have hz := isZero_quotient_coneObject_id (A := A) X.as
  refine isomorphic_mem_distinguishedConeTriangles
    (Triangle.mk (𝟙 X) (coneTriangle (𝟙 X.as)).mor₂ (coneTriangle (𝟙 X.as)).mor₃)
    ⟨X.as, X.as, 𝟙 X.as, ⟨Iso.refl _⟩⟩ _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ((isZero_zero _).iso hz)
      (by simp only [Iso.refl_hom]; rfl)
      (hz.eq_of_tgt _ _)
      ((isZero_zero (HomotopyCategory.{u, v, w} A)).eq_of_src _ _))

end DifferentialGradedModule

end

/-!
## The two sign conventions for the triangle of a mapping cone

The differential graded theory carries two triangles on the mapping cone of a homomorphism
`f : K ⟶ L` of right differential graded `A`-modules, and they are not the same triangle:

* `DifferentialGradedModule.coneTriangle`, whose third arrow is the cone projection composed
  with the natural comparison isomorphism `DifferentialGradedModule.quotientShiftIso`;
* `DifferentialGradedModule.mappingConeTriangle`, whose third arrow is the *negative* of the
  cone projection, composed with the transport along the equality of the same two objects.

This section measures the difference exactly: the two triangles have the same three vertices and
the same first two arrows, and their third arrows differ by a sign.

### Main results

* `DifferentialGradedModule.mappingConeTriangle_obj₃_eq`,
  `DifferentialGradedModule.mappingConeTriangle_mor₁_eq` and
  `DifferentialGradedModule.mappingConeTriangle_mor₂_eq`: the two triangles agree on the third
  vertex and on the first two arrows.
* `DifferentialGradedModule.mappingConeTriangle_mor₃_eq_neg`: the third arrows differ by a sign.

### Implementation notes

The two underlying cone constructions are *definitionally* the same object:
`DifferentialGradedModule.coneModule`, the module of the mapping cone
`DifferentialGradedModule.cone`, and `DifferentialGradedModule.coneObject` are built from the same
product module, the same grading and the same matrix differential, so
`DifferentialGradedModule.coneProj` and `DifferentialGradedModule.coneProjection` are
interchangeable by `rfl`.  The whole of the divergence between the two families is therefore the
sign recorded here, together with the two spellings of the comparison map `K[1]`-of-a-class
versus class-of-`K[1]`, which `DifferentialGradedModule.quotientShiftIso_hom_eq_eqToHom`
identifies.

Both conventions occur in the Stacks project: the triangle of an admissible short exact sequence
rotates to a cone triangle with the unsigned projection — see
`DifferentialGradedModule.rotatedAssociatedTriangle_iso_connectingConeTriangle`, which follows
the sign convention of the Stacks project — while its inverse rotation produces the signed one,
see `DifferentialGradedModule.inverseRotatedAssociatedTriangle_iso_mappingConeTriangle`.  Which
of the two a pretriangulated structure on the homotopy category is built from therefore decides
which class of triangles that structure declares distinguished, and the two classes are different.

### References

* [Stacks Project, Tag 09KF](https://stacks.math.columbia.edu/tag/09KF)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- The two cone triangles have the same third vertex: the two mapping cone constructions build
the same differential graded module. -/
theorem mappingConeTriangle_obj₃_eq (f : K ⟶ L) :
    (mappingConeTriangle f).obj₃ = (coneTriangle f).obj₃ :=
  rfl

/-- The two cone triangles have the same first arrow. -/
theorem mappingConeTriangle_mor₁_eq (f : K ⟶ L) :
    (mappingConeTriangle f).mor₁ = (coneTriangle f).mor₁ :=
  rfl

/-- The two cone triangles have the same second arrow: both are the class of the canonical
inclusion of `L` into the cone. -/
theorem mappingConeTriangle_mor₂_eq (f : K ⟶ L) :
    (mappingConeTriangle f).mor₂ = (coneTriangle f).mor₂ :=
  rfl

/-- The third arrows of the two cone triangles differ by a sign.  This is the whole of the
difference between the two mapping cone triangle families. -/
theorem mappingConeTriangle_mor₃_eq_neg (f : K ⟶ L) :
    (mappingConeTriangle f).mor₃ = -(coneTriangle f).mor₃ := by
  dsimp [mappingConeTriangle, coneTriangle]
  rw [quotientShiftIso_hom_eq_eqToHom, Functor.map_neg, Preadditive.neg_comp]
  rfl

end DifferentialGradedModule

end
