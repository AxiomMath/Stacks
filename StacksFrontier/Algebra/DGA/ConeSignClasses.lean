module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.ConeTriangle
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated

/-!
# The two cone sign conventions against the admissible short exact sequences

The homotopy category of right differential graded `A`-modules carries two classes of triangles:
`DifferentialGradedModule.distinguishedConeTriangles`, the triangles isomorphic to the cone
triangle of a homomorphism, and `DifferentialGradedModule.IsDistinguishedTriangle`, the triangles
isomorphic to the triangle of an admissible short exact sequence. This file identifies the two:
a triangle lies in the first exactly when negating its third arrow gives a triangle of the
second. The two classes are therefore the two sign conventions related by
`DifferentialGradedModule.mappingConeTriangle_mor₃_eq_neg`, and need not be the same class.

## Main results

* `DifferentialGradedModule.mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃`:
  a triangle is isomorphic to a cone triangle exactly when negating its third arrow gives a
  triangle of an admissible short exact sequence.

## Implementation notes

Negating the third arrow of a triangle carries isomorphisms of triangles to isomorphisms and is
involutive up to isomorphism, and it exchanges the cone triangle of a homomorphism with the
triangle of Tag 09KF, whose third arrow is the negative of the cone projection. Identifying that
signed triangle with the triangle of an admissible short exact sequence is Tag 09KF itself, in
the two directions `DifferentialGradedModule.isDistinguishedTriangle_mappingConeTriangle` and
`DifferentialGradedModule.exists_mappingConeTriangle_iso_associatedTriangle`.

## References

* [Stacks Project, Tag 09KF](https://stacks.math.columbia.edu/tag/09KF)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- Negating the third arrow of a triangle carries an isomorphism of triangles to one. -/
noncomputable def negMor₃Iso {T S : Triangle (HomotopyCategory.{u, v, w} A)} (e : T ≅ S) :
    Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ≅ Triangle.mk S.mor₁ S.mor₂ (-S.mor₃) := by
  have h₁ : e.hom.hom₁ ≫ e.inv.hom₁ = 𝟙 T.obj₁ := by
    have h := congrArg (fun q : T ⟶ T => q.hom₁) e.hom_inv_id
    change e.hom.hom₁ ≫ e.inv.hom₁ = 𝟙 _ at h
    exact h
  have h₂ : e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 T.obj₂ := by
    have h := congrArg (fun q : T ⟶ T => q.hom₂) e.hom_inv_id
    change e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 _ at h
    exact h
  have h₃ : e.hom.hom₃ ≫ e.inv.hom₃ = 𝟙 T.obj₃ := by
    have h := congrArg (fun q : T ⟶ T => q.hom₃) e.hom_inv_id
    change e.hom.hom₃ ≫ e.inv.hom₃ = 𝟙 _ at h
    exact h
  have k₁ : e.inv.hom₁ ≫ e.hom.hom₁ = 𝟙 S.obj₁ := by
    have h := congrArg (fun q : S ⟶ S => q.hom₁) e.inv_hom_id
    change e.inv.hom₁ ≫ e.hom.hom₁ = 𝟙 _ at h
    exact h
  have k₂ : e.inv.hom₂ ≫ e.hom.hom₂ = 𝟙 S.obj₂ := by
    have h := congrArg (fun q : S ⟶ S => q.hom₂) e.inv_hom_id
    change e.inv.hom₂ ≫ e.hom.hom₂ = 𝟙 _ at h
    exact h
  have k₃ : e.inv.hom₃ ≫ e.hom.hom₃ = 𝟙 S.obj₃ := by
    have h := congrArg (fun q : S ⟶ S => q.hom₃) e.inv_hom_id
    change e.inv.hom₃ ≫ e.hom.hom₃ = 𝟙 _ at h
    exact h
  exact Triangle.isoMk _ _ ⟨e.hom.hom₁, e.inv.hom₁, h₁, k₁⟩
    ⟨e.hom.hom₂, e.inv.hom₂, h₂, k₂⟩ ⟨e.hom.hom₃, e.inv.hom₃, h₃, k₃⟩
    e.hom.comm₁ e.hom.comm₂
    (by
      change (-T.mor₃) ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) 1).map e.hom.hom₁ =
        e.hom.hom₃ ≫ (-S.mor₃)
      rw [Preadditive.neg_comp, Preadditive.comp_neg, e.hom.comm₃])

/-- Negating the third arrow of a triangle twice gives back the triangle. -/
noncomputable def negMor₃NegMor₃Iso (T : Triangle (HomotopyCategory.{u, v, w} A)) :
    Triangle.mk T.mor₁ T.mor₂ (- -T.mor₃) ≅ T :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)

/-- The triangle of Tag 09KF is the cone triangle of the same homomorphism with its third arrow
negated. -/
noncomputable def mappingConeTriangleIsoNegMor₃ConeTriangle (f : K ⟶ L) :
    mappingConeTriangle f ≅
      Triangle.mk (coneTriangle f).mor₁ (coneTriangle f).mor₂ (-(coneTriangle f).mor₃) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans
      ((mappingConeTriangle_mor₁_eq f).trans (Category.id_comp _).symm))
    ((Category.comp_id _).trans
      ((mappingConeTriangle_mor₂_eq f).trans (Category.id_comp _).symm))
    ((congrArg (fun x => (mappingConeTriangle f).mor₃ ≫ x)
          (CategoryTheory.Functor.map_id _ _)).trans
      ((Category.comp_id _).trans
        ((mappingConeTriangle_mor₃_eq_neg f).trans (Category.id_comp _).symm)))

/-- Negating the third arrow of the triangle of Tag 09KF gives the cone triangle of the same
homomorphism. -/
noncomputable def negMor₃MappingConeTriangleIsoConeTriangle (f : K ⟶ L) :
    Triangle.mk (mappingConeTriangle f).mor₁ (mappingConeTriangle f).mor₂
        (-(mappingConeTriangle f).mor₃) ≅ coneTriangle f :=
  (negMor₃Iso (mappingConeTriangleIsoNegMor₃ConeTriangle f)).trans
    (negMor₃NegMor₃Iso (coneTriangle f))

/-- A triangle isomorphic to a cone triangle becomes, after its third arrow is negated, a
triangle of an admissible short exact sequence. -/
theorem isDistinguishedTriangle_negMor₃_of_mem_distinguishedConeTriangles
    (T : Triangle (HomotopyCategory.{u, v, w} A))
    (hT : T ∈ distinguishedConeTriangles.{u, v, w} (A := A)) :
    IsDistinguishedTriangle A (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) := by
  obtain ⟨K', L', f, ⟨e⟩⟩ := hT
  exact isDistinguishedTriangle_of_iso A
    ((mappingConeTriangleIsoNegMor₃ConeTriangle f).trans (negMor₃Iso e).symm)
    (isDistinguishedTriangle_mappingConeTriangle A f)

/-- The triangle of an admissible short exact sequence becomes, after its third arrow is negated,
a triangle isomorphic to a cone triangle. -/
theorem mem_distinguishedConeTriangles_negMor₃_of_isDistinguishedTriangle
    (T : Triangle (HomotopyCategory.{u, v, w} A)) (hT : IsDistinguishedTriangle A T) :
    Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distinguishedConeTriangles.{u, v, w} (A := A) := by
  obtain ⟨K', L', M', f, g, hfg, ⟨e⟩⟩ := hT
  obtain ⟨q, hq, e', -, -, -⟩ := exists_mappingConeTriangle_iso_associatedTriangle f g hfg
  exact ⟨K', L', f, ⟨(negMor₃Iso (e.trans e'.symm)).trans
    (negMor₃MappingConeTriangleIsoConeTriangle f)⟩⟩

/-- A triangle of the homotopy category is isomorphic to a cone triangle exactly when negating
its third arrow gives the triangle of an admissible short exact sequence: the two classes are the
two sign conventions for the third arrow of the triangle of a homomorphism. -/
@[stacks 09KF "the two cone sign conventions against the admissible-sequence class"]
theorem mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃
    (T : Triangle (HomotopyCategory.{u, v, w} A)) :
    T ∈ distinguishedConeTriangles.{u, v, w} (A := A) ↔
      IsDistinguishedTriangle A (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) := by
  refine ⟨isDistinguishedTriangle_negMor₃_of_mem_distinguishedConeTriangles T, fun h => ?_⟩
  exact isomorphic_mem_distinguishedConeTriangles _
    (mem_distinguishedConeTriangles_negMor₃_of_isDistinguishedTriangle _ h) T
    (negMor₃NegMor₃Iso T).symm

end DifferentialGradedModule

end
