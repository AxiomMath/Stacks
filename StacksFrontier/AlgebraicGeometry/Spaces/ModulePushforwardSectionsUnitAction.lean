module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness

/-!
# Regular functions acting injectively on the sections of a direct image

Let `j : X' ⟶ X` be an affine morphism of algebraic spaces and `G` an `𝒪_{X'}`-module.  Over an
affine étale chart `U` of `X`, the sections of `j_*G` are the sections of `G` over the affine
chart `W` of `X'` above `X' ×_X U`, through the canonical map of
`AlgebraicGeometry.Space.modulePushforwardCounitApp`, which is semilinear along the pullback of
regular functions `𝒪_X(U) ⟶ 𝒪_{X'}(W)`.  Hence a regular function on `U` whose pullbacks to the
charts of `X'` above `U` are units acts injectively on `(j_*G)(U)`.

This is how one sees that the direct image along the inclusion `j : X_K ⟶ X` of the generic
fibre of an algebraic space over a valuation ring `R` is torsion free over `R`: every nonzero
element of `R` becomes a unit on `X_K`.

## Main results

* `AlgebraicGeometry.Space.injective_smul_modulePushforward_of_isUnit`: a regular function on an
  affine chart `U` of `X` whose pullback to every chart diagram over `j` with target `U` is a
  unit acts injectively on `(j_*G)(U)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A regular function becoming a unit above acts injectively on a direct image.**  Let
`j : X' ⟶ X` be affine, let `U` be an étale scheme chart of `X` with affine underlying scheme and
let `c` be a regular function on `U` whose pullback along every chart diagram over `j` with
target `U` is a unit.  Then `c` acts injectively on the sections of `j_*G` over `U`, for every
`𝒪_{X'}`-module `G`. -/
theorem injective_smul_modulePushforward_of_isUnit {X' X : AlgebraicSpaces B S hS} (j : X' ⟶ X)
    (hj : IsAffineHom B S hS j.hom) (G : Modules.{u, u} B S hS X'.1 X'.2)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (chartScheme U))
    (c : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj
      (op U))
    (hc : ∀ (W : SmallEtale B S hS X'.1)
      (b : (SmallEtale.toOver B S hS X'.1).obj W ⟶ (SmallEtale.toOver B S hS X.1).obj U)
      (hb : W.1.hom ≫ j.hom = yoneda.map b ≫ U.1.hom),
        IsUnit (chartDiagramPullback B S hS j ⟨W, U, b, hb⟩ c)) :
    Function.Injective fun x : ((modulePushforward B S hS j).obj G).val.obj (op U) => c • x := by
  obtain ⟨W, b, hb, -, hbij, -⟩ :=
    exists_affine_chart_bijective_modulePushforwardCounitApp j hj U hU
  let d : ChartDiagram B S hS X'.1 X.1 j.hom := ⟨W, U, b, hb⟩
  intro x y hxy
  apply (hbij G).1
  have h := congrArg (modulePushforwardCounitApp B S hS j G d) hxy
  simp only at h
  rw [modulePushforwardCounitApp_smul, modulePushforwardCounitApp_smul] at h
  exact (hc W b hb).smul_left_cancel.mp h

end AlgebraicGeometry.Space

end
