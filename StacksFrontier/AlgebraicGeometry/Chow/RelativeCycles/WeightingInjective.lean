module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Weighting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm

/-!
# A family of zero-cycles on the fibres is determined by its weighting

For a locally quasi-finite morphism the inseparable degree of the residue-field extension at a
point is positive, so the function `w_α` attached to a family `α` of `0`-cycles on the fibres
determines `α`: the coefficient of `α` at a point of a fibre is `w_α` there divided by that
degree.

## Main results

* `Stacks.Chow.finInsepDegree_residueField_pos` — the inseparable degree of the residue-field
  extension at a point of the source of a locally quasi-finite morphism is positive.
* `Stacks.Chow.coeff_eq_of_relativeCycleWeight_eq` — two families with the same weighting have
  the same coefficient at the canonical point of the fibre through each point of the source.
* `Stacks.Chow.relativeCycleWeight_injective` — the construction `α ↦ w_α` is injective.

## Implementation notes

A point `y` of the scheme-theoretic fibre over `s` is the canonical point `f.asFiber x` of the
fibre through `x = f.fiberι s y`, because `f.fiberι s` is injective and
`f.fiberι (f x) (f.asFiber x) = x`. The base point is substituted away rather than transported,
so no `eqToHom` appears.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- The inseparable degree of the residue-field extension at a point of the source of a locally
quasi-finite morphism is positive, the extension being finite. -/
theorem finInsepDegree_residueField_pos {X S : Scheme.{u}} (f : X ⟶ S) [LocallyQuasiFinite f]
    (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    0 < Field.finInsepDegree (S.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hfin : Module.Finite (S.residueField (f x)) (X.residueField x) :=
    AlgebraicGeometry.module_finite_residueFieldMap f x
  have : Module.Finite ↥(separableClosure ↥(S.residueField (f x)) ↥(X.residueField x))
      ↥(X.residueField x) :=
    Module.Finite.of_restrictScalars_finite ↥(S.residueField (f x)) _ _
  unfold Field.finInsepDegree
  exact Module.finrank_pos

/-- Two families of `0`-cycles on the fibres with the same weighting have the same coefficient at
the canonical point of the fibre through any point of the source. -/
theorem coeff_eq_of_relativeCycleWeight_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {α β : FamilyOfCycles f 0}
    (h : relativeCycleWeight f α = relativeCycleWeight f β) (x : X) :
    (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) =
      (β (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hx : (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) *
      (Field.finInsepDegree ↥(S.residueField (f x)) ↥(X.residueField x) : ℤ) =
      (β (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x) *
      (Field.finInsepDegree ↥(S.residueField (f x)) ↥(X.residueField x) : ℤ) := congrFun h x
  exact mul_right_cancel₀ (by exact_mod_cast (finInsepDegree_residueField_pos f x).ne') hx

/-- The construction `α ↦ w_α` of Stacks Tag 0H5P is injective on families of `0`-cycles on the
fibres of a locally quasi-finite morphism. -/
theorem relativeCycleWeight_injective {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    Function.Injective (relativeCycleWeight f) := by
  intro α β h
  suffices H : ∀ (x : X) (s : S), f x = s → ∀ y : f.fiber s, f.fiberι s y = x →
      (α s : AlgebraicCycle (f.fiber s) ℤ) y = (β s : AlgebraicCycle (f.fiber s) ℤ) y from
    funext fun s ↦ Subtype.ext <| Function.locallyFinsuppWithin.ext fun y ↦
      H (f.fiberι s y) s (f.fiberHomeo s y).2 y rfl
  rintro x s rfl y hy
  obtain rfl : y = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (by rw [hy, f.fiberι_asFiber])
  exact coeff_eq_of_relativeCycleWeight_eq f h x

end Stacks.Chow

end
