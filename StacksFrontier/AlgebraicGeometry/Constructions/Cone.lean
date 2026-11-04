module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Data.DFinsupp.BigOperators
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf

/-!
# Cones over a scheme

A *cone* over a scheme `S` is an affine morphism `π : C ⟶ S` together with a nonnegative grading
of the sheaf of algebras `π_* 𝒪_C` whose degree-zero part is `𝒪_S`. A morphism of cones is a
morphism of total spaces over `S` whose pullback on functions preserves the grading.

## Main definitions

* `AlgebraicGeometry.pushforwardHomogeneousSum` sums a finitely supported family of homogeneous
  local sections inside `π_* 𝒪_C`.
* `AlgebraicGeometry.AbstractCone` is a cone over a scheme.
* `AlgebraicGeometry.AbstractCone.Hom` is a morphism of cones.

## Implementation notes

The grading is recorded by its homogeneous sheaves of `𝒪_S`-modules and their inclusions into
the direct image, as a `SheafOfModules.GradedAlgebra` over `S.ringCatSheaf`; the ringed site of
`S` is the site of its open subsets with its structure sheaf, so its underlying sheaf of rings is
exactly `S.ringCatSheaf`.

That the homogeneous pieces decompose the direct image is expressed by two conditions on the
finite-support sum `pushforwardHomogeneousSum`: it is injective on sections, and every section is
*locally* in its image. Together these say that the *sheafified* direct sum of the homogeneous
pieces is the direct image; global finite support is not required, and would be wrong on a
non-quasi-compact open.

A morphism of cones retains the induced map on direct images explicitly, together with its
compatibility with the homogeneous pieces, because downstream constructions use only that map.
The name `AbstractCone` avoids the clash with `CategoryTheory.Limits.Cone`.

## References

* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

/-- The sum of a finitely supported family of homogeneous sections of a graded algebra on the
ringed site of `S`, taken inside `π_* 𝒪_C`. -/
public noncomputable def pushforwardHomogeneousSum {C S : Scheme.{u}} (π : C ⟶ S)
    (A : SheafOfModules.GradedAlgebra S.ringCatSheaf)
    (ι : ∀ n, A.piece n ⟶ Stacks.Morphisms.pushforwardStructureSheaf π) (U : S.Opens) :
    (Π₀ n : ℤ, (A.piece n).val.obj (op U)) →+
      (Stacks.Morphisms.pushforwardStructureSheaf π).val.obj (op U) :=
  DFinsupp.sumAddHom fun n ↦ ((ι n).val.app (op U)).hom.toAddHom

/-- A cone over `S`: an affine morphism whose direct-image algebra is nonnegatively graded and
has degree-zero part `𝒪_S`. -/
@[stacks 062R "cones"]
public structure AbstractCone (S : Scheme.{u}) where
  /-- The total space. -/
  C : Scheme.{u}
  /-- The projection to the base. -/
  π : C ⟶ S
  /-- The projection is affine. -/
  isAffine : IsAffineHom π
  /-- The homogeneous pieces and their multiplication. -/
  grading : SheafOfModules.GradedAlgebra S.ringCatSheaf
  /-- Inclusion of every homogeneous piece in `π_* 𝒪_C`. -/
  ι (n : ℤ) : grading.piece n ⟶ Stacks.Morphisms.pushforwardStructureSheaf π
  /-- A finite homogeneous decomposition, where it exists, is unique. -/
  decomposition_unique (U : S.Opens) :
    Function.Injective (pushforwardHomogeneousSum π grading ι U)
  /-- Every section is locally a finite sum of homogeneous sections. -/
  decomposition_locally (U : S.Opens)
      (a : (Stacks.Morphisms.pushforwardStructureSheaf π).val.obj (op U)) (x : S)
      (hx : x ∈ U) :
    ∃ (V : S.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : Π₀ n : ℤ, (grading.piece n).val.obj (op V),
        pushforwardHomogeneousSum π grading ι V s =
          (Stacks.Morphisms.pushforwardStructureSheaf π).val.map (homOfLE hVU).op a
  /-- Multiplication of homogeneous elements is the multiplication in `π_* 𝒪_C`. -/
  ι_mul (i j : ℤ) (U : S.Opens) (a : (grading.piece i).val.obj (op U))
      (b : (grading.piece j).val.obj (op U)) :
    ((ι (i + j)).val.app (op U) ((grading.mul i j).app (op U) a b) :
        C.presheaf.obj (op (π ⁻¹ᵁ U))) =
      (show C.presheaf.obj (op (π ⁻¹ᵁ U)) from (ι i).val.app (op U) a) *
        (show C.presheaf.obj (op (π ⁻¹ᵁ U)) from (ι j).val.app (op U) b)
  /-- Negative homogeneous pieces vanish. -/
  negative_isZero (n : ℤ) (hn : n < 0) : IsZero (grading.piece n)
  /-- The degree-zero piece is the structure sheaf of the base. -/
  degreeZero : grading.piece 0 ≅ SheafOfModules.unit S.ringCatSheaf
  /-- The degree-zero identification respects multiplication. -/
  degreeZero_mul (U : S.Opens) (a b : (grading.piece 0).val.obj (op U)) :
    ((degreeZero.hom.val.app (op U)) ((grading.mul 0 0).app (op U) a b) :
        S.presheaf.obj (op U)) =
      (show S.presheaf.obj (op U) from degreeZero.hom.val.app (op U) a) *
        (show S.presheaf.obj (op U) from degreeZero.hom.val.app (op U) b)
  /-- The distinguished degree-zero element corresponds to `1`. -/
  degreeZero_one (U : S.Opens) :
    (degreeZero.hom.val.app (op U) (grading.one.eval (op U)) : S.presheaf.obj (op U)) =
      (1 : S.presheaf.obj (op U))
  /-- Inclusion of degree zero is the structure map `𝒪_S ⟶ π_* 𝒪_C`. -/
  ι_zero (U : S.Opens) (a : (grading.piece 0).val.obj (op U)) :
    (ι 0).val.app (op U) a = π.c.app (op U) (degreeZero.hom.val.app (op U) a)

namespace AbstractCone

/-- A morphism of cones.  The map on direct images is the pullback on functions induced by the
displayed morphism of total spaces. -/
@[stacks 062R "morphisms of cones"]
public structure Hom {S : Scheme.{u}} (X Y : AbstractCone S) where
  /-- The morphism of total spaces. -/
  f : X.C ⟶ Y.C
  /-- The morphism lies over `S`. -/
  comm : f ≫ Y.π = X.π
  /-- The induced pullback on direct images. -/
  pullback : Stacks.Morphisms.pushforwardStructureSheaf Y.π ⟶
    Stacks.Morphisms.pushforwardStructureSheaf X.π
  /-- The stored map is the map on functions induced by `f`. -/
  pullback_app (U : S.Opens) (a : Y.C.presheaf.obj (op (Y.π ⁻¹ᵁ U))) :
    pullback.val.app (op U) a = comm ▸ f.c.app (op (Y.π ⁻¹ᵁ U)) a
  /-- The pullback map on functions is degree preserving. -/
  graded : SheafOfModules.GradedAlgebra.Hom Y.grading X.grading
  /-- On every homogeneous piece, the graded map realizes pullback of functions. -/
  ι_naturality (n : ℤ) : Y.ι n ≫ pullback = graded.app n ≫ X.ι n

end AbstractCone

end AlgebraicGeometry
