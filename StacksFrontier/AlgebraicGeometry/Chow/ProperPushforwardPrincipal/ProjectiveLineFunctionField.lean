module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineDimension

/-!
# The function field of the projective line is the field of rational functions

The function field of the projective line over a field `k` is `RatFunc k`, and the order of
vanishing and the residue degree at a point of the first chart may be computed on the affine
line.

The first chart is a dense open immersion `Spec k[X] ⟶ ℙ¹`, so it induces an isomorphism of
function fields (`Stacks.Chow.functionFieldEquiv_openImmersion`), and the function field of
`Spec k[X]` is a fraction field of `k[X]` by
`AlgebraicGeometry.functionField_isFractionRing_of_affine`, hence canonically `RatFunc k`.

## Main definitions

* `AlgebraicGeometry.affineLineFunctionFieldEquiv`: the function field of the affine line over
  `k` is `RatFunc k`, as `k[X]`-algebras.
* `AlgebraicGeometry.projectiveLineFunctionFieldEquiv`: the function field of the projective
  line over `k` is `RatFunc k`.

## Main results

* `AlgebraicGeometry.ord_projectiveLine_xChart`: the order of vanishing of a rational function
  on the projective line at a point of the first chart is its order of vanishing on the affine
  line.
* `AlgebraicGeometry.residueDegree_projectiveLine_xChart`: the residue degree of the structure
  morphism of the projective line at a point of the first chart is the residue degree of the
  structure morphism of the affine line.
* `AlgebraicGeometry.ord_projectiveLine_genericPoint_eq_zero`: the order of vanishing at the
  generic point vanishes.

## Implementation notes

Mathlib's `Algebra ↑R ↑(Spec R).functionField` instance is not found by instance synthesis at
`R = CommRingCat.of k[X]`: `Scheme.functionField` is the stalk at `genericPoint`, which carries
the `IrreducibleSpace` instance as an argument, and the instance resolved from `[IsDomain ↑R]`
inside Mathlib's declaration is not the one synthesis produces here. The instance is therefore
registered again at the spelling used in this file, by applying Mathlib's own instance; the same
is done for `IsFractionRing`.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The `k[X]`-algebra structure on the function field of the affine line over `k`. -/
instance algebra_polynomial_affineLine_functionField :
    Algebra (Polynomial k) ((Spec (.of (Polynomial k))).functionField) :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial k))

/-- The function field of the affine line over `k` is a fraction field of `k[X]`. -/
instance isFractionRing_polynomial_affineLine_functionField :
    IsFractionRing (Polynomial k) ((Spec (.of (Polynomial k))).functionField) :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial k))

/-- The function field of the affine line over `k` is the field of rational functions in one
variable, as a `k[X]`-algebra: both are fraction fields of `k[X]`. -/
def affineLineFunctionFieldEquiv :
    (Spec (.of (Polynomial k))).functionField ≃ₐ[Polynomial k] RatFunc k :=
  IsLocalization.algEquiv (nonZeroDivisors (Polynomial k)) _ _

/-- The function field of the projective line over a field `k` is `RatFunc k`. -/
def projectiveLineFunctionFieldEquiv : (projectiveLine k).functionField ≃+* RatFunc k :=
  (Stacks.Chow.functionFieldEquiv_openImmersion (projectiveLineXChart k)).trans
    (affineLineFunctionFieldEquiv k).toRingEquiv

/-- The order of vanishing of a rational function on the projective line at a point of the first
chart is its order of vanishing, as a rational function on the affine line, at that point. -/
theorem ord_projectiveLine_xChart (f : (projectiveLine k).functionField)
    (y : Spec (.of (Polynomial k))) :
    (projectiveLine k).ord f ((projectiveLineXChart k).base y) =
      (Spec (.of (Polynomial k))).ord
        (Stacks.Chow.functionFieldEquiv_openImmersion (projectiveLineXChart k) f) y :=
  (Stacks.Chow.ord_dominantFunctionFieldMap_of_isOpenImmersion
    (projectiveLineXChart k) f y).symm

/-- The residue degree of the structure morphism of the projective line at a point of the first
chart is the residue degree of the structure morphism of the affine line at that point. -/
theorem residueDegree_projectiveLine_xChart (y : Spec (.of (Polynomial k))) :
    (projectiveLine k ↘ Spec (.of k)).residueDegree ((projectiveLineXChart k).base y) =
      (projectiveLineAffineStructureMorphism k).residueDegree y := by
  rw [← Stacks.Chow.residueDegree_isOpenImmersion_comp (projectiveLineXChart k)
    (projectiveLine k ↘ Spec (.of k)) y, projectiveLineXChart_comp_structureMorphism]

/-- The order of vanishing at the generic point of the projective line is zero. -/
theorem ord_projectiveLine_genericPoint_eq_zero (f : (projectiveLine k).functionField) :
    (projectiveLine k).ord f (genericPoint (projectiveLine k)) = 0 := by
  refine Scheme.ord_eq_zero_of_coheight_neq_one ?_ f
  have hmax : IsMax (genericPoint (projectiveLine k)) := fun b _ ↦ genericPoint_specializes b
  rw [Order.IsMax.coheight_eq_zero hmax]
  exact zero_ne_one

end AlgebraicGeometry

end

end
