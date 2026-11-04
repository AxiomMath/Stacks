module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# The Betti numbers at two geometric points above one point of an algebraic space

For an object `E` of `D(𝒪_X)` on an algebraic space `X` over `S` and a geometric point `ȳ` of `X`
dominated by a geometric point `x̄`, the Betti numbers of `E` at `x̄` and at `ȳ` are both Betti
numbers of the one object `Lx̄^* E` on the spectrum of the algebraically closed field of `x̄`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-- The geometric point of the spectrum of the field of `x̄` presented by a morphism into that
spectrum out of the field spectrum of a geometric point `ȳ`. -/
def dominationFieldSpacePoint (x y : GeometricPoint B S hS X.1)
    (f : y.val.siteObject ⟶ x.val.siteObject) :
    GeometricPoint B S hS (fieldValuedPointSpace B S hS x.val).1 :=
  ⟨{ carrier := y.val.carrier
     contained := y.val.contained
     toBase := y.val.toBase
     value := f }, y.property⟩

/-- The image of `AlgebraicGeometry.Space.dominationFieldSpacePoint` under the morphism to `X`
presented by `x̄` is `ȳ`, when `f` witnesses that `x̄` dominates `ȳ`. -/
theorem geometricPointMap_dominationFieldSpacePoint (x y : GeometricPoint B S hS X.1)
    (f : y.val.siteObject ⟶ x.val.siteObject) (hf : X.1.map f.op x.val.value = y.val.value) :
    geometricPointMap (fieldMorphism B S hS X.1 x.val)
        (dominationFieldSpacePoint B S hS x y f) = y :=
  Subtype.ext <| congrArg
    (fun v : X.1.obj (Opposite.op y.val.siteObject) =>
      ({ carrier := y.val.carrier, field := y.val.field, contained := y.val.contained
         toBase := y.val.toBase, value := v } : FieldValuedPoint B S hS X.1)) hf

variable (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (i : ℤ)

/-- The `i`-th Betti number of `E` at a geometric point `x̄` is the `i`-th Betti number of
`Lx̄^* E` at the tautological geometric point of the spectrum of the field of `x̄`. -/
theorem geometricFibreBetti_tautologicalGeometricPoint (x : GeometricPoint B S hS X.1) :
    geometricFibreBetti B S hS ((fieldPullback B S hS x.val).obj E) i
        (tautologicalGeometricPoint B S hS x) =
      geometricFibreBetti B S hS E i x :=
  (geometricFibreBetti_derivedPullback B S hS (fieldHom B S hS x.val) E i
    (tautologicalGeometricPoint B S hS x)).trans
      (congrArg (geometricFibreBetti B S hS E i)
        (geometricPointMap_fieldMorphism_tautological B S hS x))

/-- The `i`-th Betti number of `E` at a geometric point `ȳ` dominated by `x̄` is the `i`-th Betti
number of `Lx̄^* E` at the geometric point of the spectrum of the field of `x̄` that the
domination presents. -/
theorem geometricFibreBetti_dominationFieldSpacePoint (x y : GeometricPoint B S hS X.1)
    (f : y.val.siteObject ⟶ x.val.siteObject) (hf : X.1.map f.op x.val.value = y.val.value) :
    geometricFibreBetti B S hS ((fieldPullback B S hS x.val).obj E) i
        (dominationFieldSpacePoint B S hS x y f) =
      geometricFibreBetti B S hS E i y :=
  (geometricFibreBetti_derivedPullback B S hS (fieldHom B S hS x.val) E i
    (dominationFieldSpacePoint B S hS x y f)).trans
      (congrArg (geometricFibreBetti B S hS E i)
        (geometricPointMap_dominationFieldSpacePoint B S hS x y f hf))

/-- The Betti numbers of `E` at two geometric points of `X` above the same point of `|X|` agree,
provided that on the spectrum of an algebraically closed field they do not depend on the geometric
point (the hypothesis `hfs`). -/
theorem geometricFibreBetti_eq_of_image_eq_of_fieldSpace
    (hfs : ∀ (p : GeometricPoint B S hS X.1) (M : DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (fieldValuedPointSpace B S hS p.val))))
      (z w : GeometricPoint B S hS (fieldValuedPointSpace B S hS p.val).1),
      geometricFibreBetti B S hS M i z = geometricFibreBetti B S hS M i w)
    (x y : GeometricPoint B S hS X.1) (h : x.image = y.image) :
    geometricFibreBetti B S hS E i x = geometricFibreBetti B S hS E i y := by
  obtain ⟨r, ⟨fx, hfx⟩, ⟨fy, hfy⟩⟩ :=
    GeometricPoint.exists_common_extension x y (rfl : x.LiesOver x.image) h.symm
  have key : ∀ (p : GeometricPoint B S hS X.1) (f : r.val.siteObject ⟶ p.val.siteObject)
      (hf : X.1.map f.op p.val.value = r.val.value),
      geometricFibreBetti B S hS E i p = geometricFibreBetti B S hS E i r := fun p f hf =>
    ((geometricFibreBetti_tautologicalGeometricPoint B S hS E i p).symm.trans
      (hfs p ((fieldPullback B S hS p.val).obj E) _
        (dominationFieldSpacePoint B S hS p r f))).trans
      (geometricFibreBetti_dominationFieldSpacePoint B S hS E i p r f hf)
  exact (key x fx hfx).trans (key y fy hfy).symm

end AlgebraicGeometry.Space

end
