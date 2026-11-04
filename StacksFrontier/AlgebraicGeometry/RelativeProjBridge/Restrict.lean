module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing

/-!
# Restricting the graded algebra of Situation 01NN to an open subscheme

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra in the sheaf-theoretic form of
Situation 01NN. For an open immersion `f : X ⟶ S` this file builds the restriction `A|_X`, again
graded algebra data of Situation 01NN on `X`. Since
`Γ(M|_X, V) = Γ(M, f ''ᵁ V)` by definition (`AlgebraicGeometry.Scheme.Modules.restrict_obj`), the
graded ring of sections of `A|_X` over `V` is equal to that of `A` over `f ''ᵁ V`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.restrict`: the restriction of
  the graded algebra of Situation 01NN along an open immersion.

## Main results

* `...SheafGradedAlgebra.restrict_piece`, `restrict_mul_app` and `restrict_one`: the pieces, the
  multiplication and the unit of the restriction.
* `...SheafGradedAlgebra.restrict_sectionPieces`, `restrict_sectionRing` and `restrict_grading`:
  the graded ring of sections of `A|_X` over `V` is the graded ring of sections of `A` over
  `f ''ᵁ V`, with the same internal grading.
* `...SheafGradedAlgebra.restrict_ι_grading_top`: for the inclusion of an open subscheme `U`, the
  graded ring of global sections of `A|_U` is the graded ring of sections of `A` over `U`, with
  the same internal grading.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace SheafGradedAlgebra

variable {S X : Scheme.{u}} (A : SheafGradedAlgebra S) (f : X ⟶ S) [IsOpenImmersion f]

/-- The restriction of the graded algebra of Situation 01NN along an open immersion `f`: the
pieces are the module restrictions of the pieces of `A`, and the multiplication and unit over `V`
are those of `A` over `f ''ᵁ V`. -/
noncomputable def restrict : SheafGradedAlgebra X where
  piece n := Scheme.Modules.restrict (A.piece n) f
  mul i j :=
    { app V := (A.mul i j).app (f ''ᵁ V)
      map_smul_left V r x y := (A.mul i j).map_smul_left (f ''ᵁ V) ((f.appIso V).inv r) x y
      map_smul_right V r x y := (A.mul i j).map_smul_right (f ''ᵁ V) ((f.appIso V).inv r) x y
      naturality {_ _} h x y := (A.mul i j).naturality (Scheme.Hom.image_mono f h) x y }
  one V := A.one (f ''ᵁ V)
  one_res h := A.one_res (Scheme.Hom.image_mono f h)
  mul_assoc i j k V a b c := A.mul_assoc i j k (f ''ᵁ V) a b c
  one_mul i V a := A.one_mul i (f ''ᵁ V) a
  mul_one i V a := A.mul_one i (f ''ᵁ V) a
  mul_comm i j V a b := A.mul_comm i j (f ''ᵁ V) a b
  negative_isZero n hn :=
    (Scheme.Modules.restrictFunctor f).map_isZero (A.negative_isZero n hn)
  isQuasicoherent n := Scheme.Modules.isQuasicoherent_restrictFunctor f (A.piece n)

/-- The pieces of the restriction are the restrictions of the pieces. -/
@[simp] theorem restrict_piece (n : ℤ) :
    (A.restrict f).piece n = Scheme.Modules.restrict (A.piece n) f := rfl

/-- The multiplication of the restriction over `V` is that of `A` over `f ''ᵁ V`. -/
@[simp] theorem restrict_mul_app (i j : ℤ) (V : X.Opens) :
    ((A.restrict f).mul i j).app V = (A.mul i j).app (f ''ᵁ V) := rfl

/-- The unit of the restriction over `V` is that of `A` over `f ''ᵁ V`. -/
@[simp] theorem restrict_one (V : X.Opens) : (A.restrict f).one V = A.one (f ''ᵁ V) := rfl

/-! ### The graded ring of sections of a restriction -/

/-- The homogeneous sections of the restriction over `V` are the homogeneous sections of `A` over
`f ''ᵁ V`. -/
theorem restrict_sectionPieces (V : X.Opens) (n : ℕ) :
    (A.restrict f).sectionPieces V n = A.sectionPieces (f ''ᵁ V) n := rfl

/-- The graded ring of sections of the restriction over `V` is the graded ring of sections of
`A` over `f ''ᵁ V`. -/
theorem restrict_sectionRing (V : X.Opens) :
    (A.restrict f).sectionRing V = A.sectionRing (f ''ᵁ V) := rfl

/-- The internal grading of the section ring of the restriction over `V` is that of `A` over
`f ''ᵁ V`. -/
theorem restrict_grading (V : X.Opens) :
    (A.restrict f).grading V = A.grading (f ''ᵁ V) := rfl

/-- The graded ring of global sections of the restriction of `A` to an open subscheme `U` is the
graded ring of sections of `A` over `U`. -/
theorem restrict_ι_sectionRing_top (U : S.Opens) :
    (A.restrict U.ι).sectionRing ⊤ = A.sectionRing U :=
  congrArg A.sectionRing U.ι_image_top

/-- If `f ''ᵁ V = W`, the internal grading of the section ring of the restriction over `V` is that
of `A` over `W`. -/
theorem restrict_grading_of_image_eq {V : X.Opens} {W : S.Opens} (h : f ''ᵁ V = W) :
    HEq ((A.restrict f).grading V) (A.grading W) := by
  subst h
  rfl

/-- The internal grading of the graded ring of global sections of `A|_U` is the internal grading
of the graded ring of sections of `A` over `U`. -/
theorem restrict_ι_grading_top (U : S.Opens) :
    HEq ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) (A.grading U) :=
  A.restrict_grading_of_image_eq U.ι U.ι_image_top

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
