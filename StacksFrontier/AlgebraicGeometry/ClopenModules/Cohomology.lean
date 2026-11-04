module

public import StacksFrontier.AlgebraicGeometry.ClopenModules.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# Cohomology on an open and closed piece

Let `X = U ⊔ V` with `U` and `V` open and disjoint, over a field `k`. Then `H^n(U, ℱ|_U)` is a
direct summand of `H^n(X, ℱ)`: it is `H^n(X, j_*(ℱ|_U))` because `j : U ⟶ X` is a closed
immersion, and `j_*(ℱ|_U)` is a direct summand of `ℱ`.

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_restrict_of_isZero`: `H^n(X, ℱ) = 0` implies
  `H^n(U, ℱ|_U) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Vanishing of cohomology passes to an open and closed piece**: if `X = U ⊔ V` with `U`, `V`
open and disjoint and `H^n(X, ℱ) = 0`, then `H^n(U, ℱ|_U) = 0`, for any structure morphism `f'`
of `U` equal to `U ⟶ X ⟶ Spec k`. -/
theorem isZero_cohomologyOverField_restrict_of_isZero {U V : X.Opens} (hdisj : U ⊓ V = ⊥)
    (hcov : U ⊔ V = ⊤) {f' : U.toScheme ⟶ Spec (.of k)} (hf' : U.ι ≫ f = f') (F : X.Modules)
    (n : ℕ) (h : IsZero (cohomologyOverField k f F n)) :
    IsZero (cohomologyOverField k f' (F.restrict U.ι) n) := by
  subst hf'
  have hcl : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, show (U : Set X) = (V : Set X)ᶜ from Set.ext fun x =>
      ⟨fun hx hxV => hdisj.le ⟨hx, hxV⟩, fun hx => (hcov.ge trivial).resolve_right hx⟩]
    exact V.isOpen.isClosed_compl)
  refine IsZero.of_iso ?_ (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k U.ι f _ n)
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_comp_restrictAdjunction_unit_app_eq_id hdisj hcov F
  rw [IsZero.iff_id_eq_zero, ← cohomologyOverFieldMap_id, ← hs, cohomologyOverFieldMap_comp,
    h.eq_of_tgt (cohomologyOverFieldMap k f s n) 0, zero_comp]

end AlgebraicGeometry
