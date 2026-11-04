module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeSections

/-!
# The square of clause (2) of Tag 02NC on every section of `A_n ⊗ L_n`

The square of clause (2) of Tag 02NC is stated on pure tensors `a ⊗ l` of sections over an open of
the base (`Stacks.AlgebraicGeometry.RelativeTwistSections.SquareAt`). For quasi-coherent `A_n` and
`L_n`, the square over every open forces the two routes to agree on **every** section of the sheaf
`A_n ⊗ L_n`, not only on the image of `A_n(V) ⊗ L_n(V)`: the comparison `θ` carries `ψ_B(b)` to
the *multiply* map applied to `b`. Over an affine open the sections of the tensor product sheaf
are `A_n(V) ⊗ L_n(V)`
(`Stacks.AlgebraicGeometry.AffineOpenTensorSections.bijective_gammaTensorMap`), and a section over
an arbitrary open is determined by its restrictions to the affine opens inside.

## Main results

* `Stacks.AlgebraicGeometry.RelativeTwistSections.multiplyHom_app_gammaTensorMap`: the multiply
  map on the image of `A_n(V) ⊗ L_n(V)` is the lower route.
* `Stacks.AlgebraicGeometry.RelativeTwistSections.thetaSections_eq_multiplyHom_of_squareAt`:
  **the square over every open gives `θ ∘ ψ_B = ψ^C` on every section.**

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct
open Stacks.AlgebraicGeometry.AffineOpenTensorSections

universe u

namespace Stacks.AlgebraicGeometry.RelativeTwistSections

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {S P P' : Scheme.{u}} (π : P ⟶ S) {An Ln : S.Modules} {FA : P.Modules}
  (ψA : An ⟶ (Scheme.Modules.pushforward π).obj FA)

/-- **The multiply map on the image of `A_n(V) ⊗ L_n(V)` is the lower route.** -/
theorem multiplyHom_app_gammaTensorMap (V : S.Opens) (z : Γ(An, V) ⊗[Γ(S, V)] Γ(Ln, V)) :
    (multiplyHom π ψA).val.app (op V) (gammaTensorMap An Ln V z) = lowerRoute π ψA V z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    refine (congrArg ((multiplyHom π ψA).val.app (op V)) (map_zero (gammaTensorMap An Ln V))).trans
      ?_
    exact ((multiplyHom π ψA).val.app (op V)).hom.map_zero.trans (map_zero _).symm
  | tmul a l => exact multiplyHom_app_gammaTmul π ψA V a l
  | add z z' hz hz' =>
    refine (congrArg ((multiplyHom π ψA).val.app (op V))
      (map_add (gammaTensorMap An Ln V) z z')).trans ?_
    refine ((multiplyHom π ψA).val.app (op V)).hom.map_add _ _ |>.trans ?_
    exact (congrArg₂ (· + ·) hz hz').trans (map_add (lowerRoute π ψA V) z z').symm

variable (π' : P' ⟶ S) (g : P ⟶ P') (hg : g ≫ π' = π) {FB : P'.Modules}
  (ψB : tensorMod An Ln ⟶ (Scheme.Modules.pushforward π').obj FB)
  (θ : (Scheme.Modules.pullback g).obj FB ⟶ tensorMod FA ((Scheme.Modules.pullback π).obj Ln))

/-- **The square of clause (2) over every open of the base gives `θ ∘ ψ_B = ψ^C` on every
section of `A_n ⊗ L_n`**, for `A_n` and `L_n` quasi-coherent. -/
theorem thetaSections_eq_multiplyHom_of_squareAt [An.IsQuasicoherent] [Ln.IsQuasicoherent]
    (hsq : ∀ V : S.Opens, SquareAt π π' g hg ψA ψB θ V) (V : S.Opens)
    (b : Γ(tensorMod An Ln, V)) :
    thetaSections π π' g hg θ V (ψB.val.app (op V) b) = (multiplyHom π ψA).val.app (op V) b := by
  refine eq_of_isBasis π (Scheme.isBasis_affineOpens S)
    (tensorMod FA ((Scheme.Modules.pullback π).obj Ln)) fun W => ?_
  obtain ⟨W, hWa, hWV⟩ := W
  refine (thetaSections_res π π' g hg θ hWV _).trans ?_
  have hψ := PresheafOfModules.naturality_apply ψB.val (homOfLE hWV).op b
  have hm := PresheafOfModules.naturality_apply (multiplyHom π ψA).val (homOfLE hWV).op b
  refine (congrArg (thetaSections π π' g hg θ W) hψ.symm).trans ?_
  refine Eq.trans ?_ hm
  obtain ⟨z, hz⟩ := (bijective_gammaTensorMap hWa An Ln).surjective
    ((tensorMod An Ln).val.map (homOfLE hWV).op b)
  rw [← hz]
  exact (upperRoute_eq_lowerRoute π π' g hg ψA ψB θ (hsq W) z).trans
    (multiplyHom_app_gammaTensorMap π ψA W z).symm

end Stacks.AlgebraicGeometry.RelativeTwistSections

end
