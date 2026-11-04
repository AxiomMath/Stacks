module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular

/-!
# Uniqueness of the nonsingular projective model of a curve

Let `k` be a field and let `X` be a curve over `k`. A nonsingular projective model of `X`,
`AlgebraicGeometry.NonsingularProjectiveModel`, is a regular projective curve `Y` over `k`
together with a `k`-algebra isomorphism `k(X) ≃ k(Y)`. The source observes, right after the
definition, that such a model is determined up to unique isomorphism, and that is what this file
proves: two models of one curve have isomorphic underlying schemes over `k`, by the isomorphism
that matches their identifications of the function field, and there is only one such isomorphism.

## Main results

* `AlgebraicGeometry.NonsingularProjectiveModel.exists_iso`: two nonsingular projective models of
  one curve over `k` are isomorphic over `k`, by an isomorphism carrying one identification of
  function fields to the other.
* `AlgebraicGeometry.NonsingularProjectiveModel.hom_ext`: a morphism between the underlying
  schemes of two models, over `k` and dominant, is determined by the map of function fields it
  induces; so the isomorphism of the previous item is unique.

## Implementation notes

The content is [Stacks, Tag 0BY1], the correspondence between regular projective curves over `k`
and finitely generated extensions of `k` of transcendence degree one; the half of it used here is
full faithfulness, which is unconditional in this library. It is applied through
`AlgebraicGeometry.exists_isIso_of_algEquiv` and
`AlgebraicGeometry.over_hom_ext_of_functionFieldMap`, both stated for
`AlgebraicGeometry.Variety` and the `k`-algebra structure
`AlgebraicGeometry.varietyFunctionFieldAlgebra`, while a model carries the `k`-algebra structure
`AlgebraicGeometry.functionFieldAlgebra`. The two structures are the same, which is
`AlgebraicGeometry.varietyFunctionFieldAlgebra_eq_functionFieldAlgebra` below, so no comparison
map intervenes.

A model is regular and projective, which gives the normality and properness those results ask
for: normality by `AlgebraicGeometry.isNormal_of_isRegular`, properness from the instance
carrying `AlgebraicGeometry.IsProjectiveVariety` to `AlgebraicGeometry.IsProperVariety`.

## References

* [Stacks Project, Tag 0BY2](https://stacks.math.columbia.edu/tag/0BY2), the model.
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1), the correspondence that
  makes it unique.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The `k`-algebra structure on the function field of a variety over `k` and the one carried by
a curve over `k` through its structure morphism are the same: both are the ring homomorphism
`k ⟶ Γ(X, ⊤) ⟶ k(X)` read as an algebra. -/
public theorem varietyFunctionFieldAlgebra_eq_functionFieldAlgebra (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsCurve k sX] :
    varietyFunctionFieldAlgebra (⟨X, sX⟩ : Variety k) = functionFieldAlgebra k sX := by
  rw [varietyFunctionFieldAlgebra_eq_germToFunctionField (⟨X, sX⟩ : Variety k)]
  rfl

namespace NonsingularProjectiveModel

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsCurve k sX]

/-- The underlying scheme of a nonsingular projective model is normal, being regular. -/
public theorem isNormal (M : NonsingularProjectiveModel k X sX) : IsNormal M.Y :=
  isNormal_of_isRegular _ M.isRegular

private instance (M : NonsingularProjectiveModel k X sX) : IsCurve k M.structureMap := M.isCurve

private instance (M : NonsingularProjectiveModel k X sX) : IsNormal M.Y := M.isNormal

private instance (M : NonsingularProjectiveModel k X sX) : IsProper M.structureMap :=
  M.isProper_structureMap

/-- **Two nonsingular projective models of one curve over `k` are isomorphic over `k`**, by an
isomorphism matching the two identifications of the function field: the map of function fields it
induces is `k(Y₂) ≃ k(X) ≃ k(Y₁)`.

This is the source's remark, made just after the definition of a nonsingular projective model,
that the model "is determined up to unique isomorphism by Theorem 0BY1". The isomorphism is
unique by `AlgebraicGeometry.NonsingularProjectiveModel.hom_ext`. -/
public theorem exists_iso (M₁ M₂ : NonsingularProjectiveModel k X sX) :
    ∃ e : M₁.Y ≅ M₂.Y, e.hom ≫ M₂.structureMap = M₁.structureMap ∧
      ∃ _ : IsDominant e.hom,
        letI : IsCurve k M₁.structureMap := M₁.isCurve
        letI : IsCurve k M₂.structureMap := M₂.isCurve
        letI : Algebra k X.functionField := functionFieldAlgebra k sX
        letI : Algebra k M₁.Y.functionField := functionFieldAlgebra k M₁.structureMap
        letI : Algebra k M₂.Y.functionField := functionFieldAlgebra k M₂.structureMap
        functionFieldMap e.hom =
          (M₂.functionFieldEquiv.symm.trans M₁.functionFieldEquiv).toAlgHom.toRingHom := by
  let : Algebra k X.functionField := functionFieldAlgebra k sX
  let : Algebra k M₁.Y.functionField := functionFieldAlgebra k M₁.structureMap
  let : Algebra k M₂.Y.functionField := functionFieldAlgebra k M₂.structureMap
  have key := exists_isIso_of_algEquiv
    (⟨M₁.Y, M₁.structureMap⟩ : Variety k) (⟨M₂.Y, M₂.structureMap⟩ : Variety k)
  rw [varietyFunctionFieldAlgebra_eq_functionFieldAlgebra k M₁.structureMap,
    varietyFunctionFieldAlgebra_eq_functionFieldAlgebra k M₂.structureMap] at key
  obtain ⟨g, hiso, hdom, hff⟩ :=
    key (M₂.functionFieldEquiv.symm.trans M₁.functionFieldEquiv)
  let := hiso
  have hleft : IsIso g.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map g))
  exact ⟨asIso g.left, Over.w g, hdom, hff⟩

/-- A morphism over `k` between the underlying schemes of two nonsingular projective models of a
curve is determined by the map of function fields it induces. In particular the isomorphism of
`AlgebraicGeometry.NonsingularProjectiveModel.exists_iso` is the only one over `k` matching the
two identifications of the function field. -/
public theorem hom_ext (M₁ M₂ : NonsingularProjectiveModel k X sX)
    (f g : M₁.Y ⟶ M₂.Y) (hf : f ≫ M₂.structureMap = M₁.structureMap)
    (hg : g ≫ M₂.structureMap = M₁.structureMap)
    (hdf : letI : IsCurve k M₁.structureMap := M₁.isCurve
           letI : IsCurve k M₂.structureMap := M₂.isCurve
           IsDominant f)
    (hdg : letI : IsCurve k M₁.structureMap := M₁.isCurve
           letI : IsCurve k M₂.structureMap := M₂.isCurve
           IsDominant g)
    (h : letI : IsCurve k M₁.structureMap := M₁.isCurve
         letI : IsCurve k M₂.structureMap := M₂.isCurve
         letI := hdf
         letI := hdg
         functionFieldMap f = functionFieldMap g) : f = g := by
  let := hdf
  let := hdg
  have : IsDominant (Over.homMk f hf :
      Over.mk M₁.structureMap ⟶ Over.mk M₂.structureMap).left := hdf
  have : IsDominant (Over.homMk g hg :
      Over.mk M₁.structureMap ⟶ Over.mk M₂.structureMap).left := hdg
  have hg₁₂ := over_hom_ext_of_functionFieldMap
    (⟨M₁.Y, M₁.structureMap⟩ : Variety k) (⟨M₂.Y, M₂.structureMap⟩ : Variety k)
    (Over.homMk f hf) (Over.homMk g hg) (by exact h)
  exact congrArg CategoryTheory.Over.Hom.left hg₁₂

end NonsingularProjectiveModel

end AlgebraicGeometry

end
