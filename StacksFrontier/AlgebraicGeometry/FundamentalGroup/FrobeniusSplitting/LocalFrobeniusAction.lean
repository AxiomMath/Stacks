module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusGeneration

/-!
# The action of a Frobenius element on a geometric fibre

Let `x` be a closed point with finite residue field `κ(x)` of a connected scheme `X`, and `c` the
choices producing a Frobenius element at `x`: an algebraic closure `Ω` of `κ(x)`, giving the
geometric point `x̄ : Spec Ω ⟶ Spec κ(x) ⟶ X`, and a path from the fibre functor at `x̄` to the
fibre functor at the base point.

For a finite étale cover `A` of `X`, the geometric fibre at `x̄` is the set of lifts
`q : Spec Ω ⟶ A` of `x̄`. The local Frobenius element (the image in `π₁(X, x̄)` of the arithmetic
Frobenius `φ` of `Ω / κ(x)`) acts on it by precomposition with `Spec φ`:
`φ · q = Spec φ ≫ q`. If the Frobenius element `c.element ∈ π₁(X, base)` acts trivially on the
fibre of `A` at the base point, then the local Frobenius element acts trivially on the fibre at
`x̄`: the path is an isomorphism of fibre functors which conjugates the one into the other.

## Main results

* `AlgebraicGeometry.FrobeniusData.localElement_app_apply`: `φ · q = Spec φ ≫ q`.
* `AlgebraicGeometry.FrobeniusData.localElement_app_eq_of_element_app_eq`: triviality transfers
  from the base point to `x̄`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FrobeniusData

variable {X : Scheme.{u}} [ConnectedSpace X] {base : GeometricPoint X} {x : closedPoints X}

/-- The arithmetic Frobenius `a ↦ a ^ #κ(x)` of the algebraic closure `Ω` of `κ(x)`, the element
of `Gal(Ω/κ(x))` whose image is the local Frobenius element. -/
def frobenius (c : FrobeniusData base x) : c.closure ≃ₐ[X.residueField x.1] c.closure :=
  have : Finite (X.residueField x.1) := c.finite_residueField
  let _ : Fintype (X.residueField x.1) := Fintype.ofFinite _
  FiniteField.frobeniusAlgEquivOfAlgebraic (X.residueField x.1) c.closure

/-- The geometric point `x̄ : Spec Ω ⟶ X` above `x`. -/
abbrev geometricPoint (c : FrobeniusData base x) : GeometricPoint X :=
  (algebraicClosureGeometricPoint (X.residueField x.1) c.closure).map (X.fromSpecResidueField x.1)

/-- **The local Frobenius element acts on the geometric fibre at `x̄` by precomposition with the
spectrum of the arithmetic Frobenius.** -/
theorem localElement_app_apply (c : FrobeniusData base x) (A : FiniteEtaleOver X)
    (q : finiteEtaleFiber c.geometricPoint A) :
    ((c.localElement.asIso.app A).hom q).1 =
      Spec.map (CommRingCat.ofHom (c.frobenius : c.closure →+* c.closure)) ≫ q.1 := by
  have : Finite (X.residueField x.1) := c.finite_residueField
  let _ : Fintype (X.residueField x.1) := Fintype.ofFinite _
  set j := X.fromSpecResidueField x.1
  set x₀ := algebraicClosureGeometricPoint (X.residueField x.1) c.closure
  set p := (finiteEtaleFiberProjectionEquiv j x₀ A).symm q
  have hp : p.1 = Spec.map (CommRingCat.ofHom (algebraMap c.closure c.closure)) ≫ p.1 := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact (Category.id_comp p.1).symm
  have h := galoisEquivEtaleFundamentalGroup_apply (X.residueField x.1) c.closure c.closure
    ((finiteEtaleBaseChange j).obj A)
    (FiniteField.frobeniusAlgEquivOfAlgebraic (X.residueField x.1) c.closure) p p.1 hp
  change (finiteEtaleFiberProjection j x₀ A ((((galoisEquivEtaleFundamentalGroup
    (X.residueField x.1) c.closure c.closure)
    (FiniteField.frobeniusAlgEquivOfAlgebraic (X.residueField x.1) c.closure)).asIso.app
      ((finiteEtaleBaseChange j).obj A)).hom p)).1 = _
  simp only [finiteEtaleFiberProjection]
  rw [h, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  change (𝟙 _ ≫ _ ≫ p.1) ≫ pullback.fst A.hom j = _
  rw [Category.id_comp]
  exact (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_fst _ _ _))

/-- **Triviality of a Frobenius element transfers to the geometric point above `x`.** If the
Frobenius element `c.element` acts trivially on the fibre of `A` at the base point, then the
local Frobenius element acts trivially on the fibre of `A` at `x̄`. -/
theorem localElement_app_eq_of_element_app_eq (c : FrobeniusData base x) (A : FiniteEtaleOver X)
    (h : ∀ z : (finiteEtaleFiberFunctor base).obj A, ((c.element.asIso.app A).hom z) = z)
    (q : finiteEtaleFiber c.geometricPoint A) : (c.localElement.asIso.app A).hom q = q := by
  have h2 := h (c.path.hom.app A q)
  change ((c.path.conjAut c.localElement).asIso.app A).hom (c.path.hom.app A q) = _ at h2
  rw [Stacks.FundamentalGroup.conjAut_app_apply c.path c.localElement A q] at h2
  simpa using congrArg (c.path.inv.app A) h2

/-- If the Frobenius element acts trivially on the fibre at the base point, every lift
`q : Spec Ω ⟶ A` of `x̄` is fixed by the arithmetic Frobenius: `Spec φ ≫ q = q`. -/
theorem specMap_frobenius_comp_eq (c : FrobeniusData base x) (A : FiniteEtaleOver X)
    (h : ∀ z : (finiteEtaleFiberFunctor base).obj A, ((c.element.asIso.app A).hom z) = z)
    (q : finiteEtaleFiber c.geometricPoint A) :
    Spec.map (CommRingCat.ofHom (c.frobenius : c.closure →+* c.closure)) ≫ q.1 = q.1 := by
  rw [← localElement_app_apply c A q, localElement_app_eq_of_element_app_eq c A h q]

end AlgebraicGeometry.FrobeniusData

end
