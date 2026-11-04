module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.ConeSignClasses
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived

/-!
# Exactness of tensoring with a complex, against the cone triangles

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. Tensoring with
`K` and localizing the target is an exact functor `K(Mod_(E, d)) ⥤ D(O)` for the pretriangulated
structure on `K(Mod_(E, d))` whose distinguished triangles come from admissible short exact
sequences (Tag 09LW). The other class of triangles on `K(Mod_(E, d))`, those isomorphic to a cone
triangle, is the same class with the third arrow negated (Tag 09KF), so the image of a cone
triangle becomes distinguished in `D(O)` after its third arrow is negated — and in particular has
the same three vertices as a distinguished triangle of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_negMor₃_distinguished`: the
  image of a cone triangle, with its third arrow negated, is a distinguished triangle of `D(O)`.

## References

* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW)
* [Stacks Project, Tag 09KF](https://stacks.math.columbia.edu/tag/09KF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- The image in `D(O)` of a triangle isomorphic to a cone triangle of `K(Mod_(E, d))` is
distinguished once its third arrow is negated: that negation turns a cone triangle into the
triangle of an admissible short exact sequence, which tensoring with `K` keeps distinguished. -/
@[stacks 09LW "exactness against the cone triangles, up to the sign of the third arrow",
  stacks 09KF "the sign that relates the two classes of triangles"]
theorem tensorWithComplexToDerivedCategory_negMor₃_distinguished
    (T : Triangle (DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))
    (hT : T ∈ distinguishedConeTriangles.{0, max u v w t s, max u v w t s}
      (A := (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)) :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).mapTriangle.obj
        (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) ∈
      distTriang (DerivedCategory (TensorModO.{u, v, w, t, s} X)) := by
  have := tensorWithComplexHomotopy_isTriangulated.{u, v, w, t, s, 0} X ℤ K
  have : (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).IsTriangulated :=
    show (tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙
      DerivedCategory.Qh (C := TensorModO.{u, v, w, t, s} X)).IsTriangulated from inferInstance
  refine (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).map_distinguished _ ?_
  rw [distinguishedTriangles_eq]
  exact (mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃ T).1 hT

end AlgebraicGeometry.RingedSite

end
