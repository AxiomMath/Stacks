module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne

/-!
# Finiteness of a proper dominant morphism with finite function field extension

Let `f : X ⟶ Y` be a proper dominant morphism of integral schemes with `Y` locally Noetherian,
and suppose the induced extension of function fields `R(Y) ⊂ R(X)` is finite. Then `f` is finite
over an open neighbourhood of any point `ξ` of `Y` whose local ring has dimension one.

## Main results

* `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_module_finite_functionField`: the
  neighbourhood over which `f` is finite.

## Implementation notes

This is the special case of Stacks 0AB7,
`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one`,
in which the generic condition holds for the single generic point of the irreducible source:
the residue field extension there is the function field extension `R(Y) ⊂ R(X)`, which is
finite and hence algebraic. The identification of the two is
`AlgebraicGeometry.residueFieldMap_comp_genericResidueEquivOfDominant`.

The extension of function fields is `AlgebraicGeometry.functionFieldMap`, and its finiteness is
`Module.Finite` for the algebra structure that map defines. The local ring of `Y` at `ξ` is
Noetherian because `Y` is locally Noetherian, so hypothesis (4) of the source is used only
through the bound `dim (𝒪_{Y, ξ}) ≤ 1`.

## References

* [Stacks Project, Tag 02RM](https://stacks.math.columbia.edu/tag/02RM)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02RM.** Let `f : X ⟶ Y` be a morphism of schemes and `ξ` a point of
`Y`. Assume that `X` and `Y` are integral, that `Y` is locally Noetherian, that `f` is proper and
dominant with `R(Y) ⊂ R(X)` finite, and that `dim (𝒪_{Y, ξ}) = 1`. Then there is an open
neighbourhood `V` of `ξ` such that the restriction `f⁻¹(V) → V` is finite. -/
@[stacks 02RM]
theorem exists_isFinite_morphismRestrict_of_module_finite_functionField
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ξ : Y) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsProper f] [IsDominant f]
    (hfin : letI := (functionFieldMap f).toAlgebra
      Module.Finite Y.functionField X.functionField)
    (hξ : ringKrullDim (Y.presheaf.stalk ξ) = 1) :
    ∃ V : Y.Opens, ξ ∈ V ∧ IsFinite (f ∣_ V) := by
  let : Algebra Y.functionField X.functionField := (functionFieldMap f).toAlgebra
  let : Module.Finite Y.functionField X.functionField := hfin
  refine exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one f ξ hξ.le (Or.inl ?_)
  intro η hη
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hη
  subst hη
  let : Algebra (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) :=
    (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq (genericResidueEquivOfDominant f)
      (genericResidueEquiv X) (residueFieldMap_comp_genericResidueEquivOfDominant f)).mpr
    (Algebra.IsAlgebraic.of_finite _ _)

end AlgebraicGeometry

end
