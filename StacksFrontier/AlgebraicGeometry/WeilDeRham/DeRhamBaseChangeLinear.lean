module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilBaseChange
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChange

/-!
# The base change map of de Rham cohomology, extended linearly

Let `k ⟶ K` be an extension of fields and `X` a smooth projective scheme over `k`, with base
change `X_K = X ×_{Spec k} Spec K` and projection `pr : X_K ⟶ X`. Pullback along the square
`(pr, Spec K ⟶ Spec k)` is the base change map `H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)`
(`Stacks.DeRhamWeil.baseChangePiece`), semilinear along `k ⟶ K`. This file extends it to the
`K`-linear map `K ⊗_k H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)`, the comparison map of Section 0FWC whose
bijectivity ([Stacks, Tag 0FM0] over a field) is the input of Lemma 0FVT for de Rham cohomology.

## Main definitions

* `Stacks.WeilDeRham.deRhamBaseChangeLinear`: `K ⊗_k H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)`,
  `c ⊗ x ↦ c · pr^* x`.

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped TensorProduct

universe u

namespace Stacks.WeilDeRham

attribute [local instance] RestrictScalars.moduleOrig

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The base change map `H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)`, as a `k`-linear map** into
`H^n_{dR}(X_K/K)` with scalars restricted to `k`. -/
def deRhamBaseChangePieceLinear (n : ℤ) :
    DeRhamWeil.piece X n →ₗ[k]
      RestrictScalars k K (DeRhamWeil.piece ((fieldBaseChange k K).obj X) n) where
  toFun x := (RestrictScalars.addEquiv k K _).symm
    (DeRhamWeil.baseChangePiece (fieldBaseChangeProj X) (fieldBaseChangeProj_comp_hom X) n x)
  map_add' x y := by
    rw [map_add, map_add]
  map_smul' c x := by
    rw [DeRhamWeil.baseChangePiece_smul, RingHom.id_apply, RestrictScalars.smul_def]
    rfl

/-- **The comparison map `K ⊗_k H^n_{dR}(X/k) ⟶ H^n_{dR}(X_K/K)`**, `c ⊗ x ↦ c · pr^* x`, the
`K`-linear extension of the base change map `pr^*` along the square `(pr, Spec K ⟶ Spec k)`. -/
def deRhamBaseChangeLinear (n : ℤ) :
    K ⊗[k] DeRhamWeil.piece X n →ₗ[K] DeRhamWeil.piece ((fieldBaseChange k K).obj X) n where
  toFun t := RestrictScalars.addEquiv k K _ ((deRhamBaseChangePieceLinear K X n).liftBaseChange K t)
  map_add' s t := by
    rw [map_add, map_add]
  map_smul' c t := by
    rw [map_smul]
    rfl

/-- The comparison map sends `c ⊗ x` to `c · pr^* x`. -/
theorem deRhamBaseChangeLinear_tmul (n : ℤ) (c : K) (x : DeRhamWeil.piece X n) :
    deRhamBaseChangeLinear K X n (c ⊗ₜ x) =
      c • DeRhamWeil.baseChangePiece (fieldBaseChangeProj X) (fieldBaseChangeProj_comp_hom X) n x :=
  rfl

end Stacks.WeilDeRham

end
