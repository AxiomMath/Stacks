module

public import StacksFrontier.RingTheory.OrderOfVanishing.ResidualCokernel
public import StacksFrontier.Algebra.Module.Reflexive

/-!
# The double dual of a finite module is its torsion-free quotient

Over an integral domain the canonical map `M ⟶ M^**` kills exactly the torsion submodule, and
over a Dedekind domain — in particular over a discrete valuation ring — it is surjective on a
finite module by [Stacks, Tag 0B36]. So for `M` finite over a Dedekind domain the double dual
is the torsion-free quotient `M ⧸ torsion`, naturally in `M`.

This is the algebraic content of the reflexive hull at a codimension-one point of a regular
scheme, where the local ring is a discrete valuation ring: it turns the double transpose that
`AlgebraicGeometry.Scheme.Modules.detStalkEquiv_stalkHom_detMap` produces for the determinant
comparison of [Stacks, Tag 0B3T] into the map `Stacks.OrderOfVanishing.torsionQuotientMap` that
the determinant bound of `StacksFrontier.RingTheory.OrderOfVanishing.ExteriorDeterminant` is stated
at.

## Main results

* `dual_apply_eq_zero_of_mem_torsion`: over a domain a functional kills a torsion element.
* `ker_dualEval_eq_torsion`: over a domain, the kernel of `Module.Dual.eval` on a finite module
  is the torsion submodule.
* `bijective_dualMap_of_surjective_of_ker_le_torsion` and
  `bijective_dualMap_dualMap_of_surjective_of_ker_le_torsion`: **a surjection whose kernel is
  torsion is invisible to the dual** — its transpose and its double transpose are bijective.
* `torsionQuotientDualEquiv`: **over a Dedekind domain the double dual of a finite module is its
  torsion-free quotient.**
* `Stacks.OrderOfVanishing.torsionQuotientDualEquiv_torsionQuotientMap`: that identification is
  natural — it carries `torsionQuotientMap f` to the double transpose of `f`.

## Implementation notes

One inclusion of `ker_dualEval_eq_torsion` is the second assertion of
`isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff`, which gives only that
the kernel is a torsion module; the other is the one-line observation that a functional kills a
torsion element because the ring is a domain. Surjectivity is `surjective_dualEval_of_finite`.

The naturality statement carries `[IsDiscreteValuationRing R]` rather than `[IsDedekindDomain R]`
because `Stacks.OrderOfVanishing.torsionQuotientMap`, which it is stated about, is declared under
that hypothesis; the equivalence itself needs only a Dedekind domain.

**Why the torsion hypothesis on the kernel.** The double transpose of a bare surjection need not
be surjective: over a two-dimensional regular local ring the double transpose of `R ^ 2 ↠ (x, y)`
has image `(x, y)`. That kernel is free of rank one, not torsion. When the kernel *is* torsion
— equivalently, when the surjection becomes an isomorphism over the fraction field — no
functional sees it, and the transpose is already bijective.

## References

* [Stacks Project, Tag 0AV0](https://stacks.math.columbia.edu/tag/0AV0)
* [Stacks Project, Tag 0B36](https://stacks.math.columbia.edu/tag/0B36)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

universe u

variable {R : Type*} [CommRing R] [IsDomain R] {M M' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

omit [IsDomain R] in
/-- **Over a domain a functional kills a torsion element.** The scalar witnessing the torsion
is a nonzerodivisor, and it annihilates the value of the functional. -/
public theorem dual_apply_eq_zero_of_mem_torsion (phi : Module.Dual R M) {m : M}
    (hm : m ∈ Submodule.torsion R M) : phi m = 0 := by
  obtain ⟨s, hs⟩ := hm
  have h : (s : R) * phi m = 0 := by
    have h0 := congrArg phi (Submonoid.smul_def s m ▸ hs)
    rw [map_smul, map_zero, smul_eq_mul] at h0
    exact h0
  exact (mem_nonZeroDivisors_iff.mp s.2).1 (phi m) h

/-- **Over a domain the canonical map to the double dual kills exactly the torsion.** -/
public theorem ker_dualEval_eq_torsion [Module.Finite R M] :
    LinearMap.ker (Module.Dual.eval R M) = Submodule.torsion R M := by
  have htor : Module.IsTorsion R (LinearMap.ker (Module.Dual.eval R M)) :=
    ((isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).2.1 inferInstance).1
  refine le_antisymm (fun m hm => ?_) (fun m hm => ?_)
  · obtain ⟨s, hs⟩ := @htor ⟨m, hm⟩
    exact ⟨s, Subtype.ext_iff.mp hs⟩
  · exact LinearMap.ext fun phi => by
      simpa using dual_apply_eq_zero_of_mem_torsion phi hm

omit [IsDomain R] in
/-- **The transpose of a surjection whose kernel is torsion is bijective.** Injectivity is
`LinearMap.dualMap_injective_of_surjective`; for surjectivity, a functional on the source kills
the kernel, so it descends along the surjection. -/
public theorem bijective_dualMap_of_surjective_of_ker_le_torsion {u : M →ₗ[R] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion R M) :
    Function.Bijective u.dualMap := by
  refine ⟨LinearMap.dualMap_injective_of_surjective hu, fun phi => ?_⟩
  have hkphi : LinearMap.ker u ≤ LinearMap.ker phi := fun m hm =>
    dual_apply_eq_zero_of_mem_torsion phi (hker hm)
  refine ⟨(Submodule.liftQ _ phi hkphi).comp
    (LinearMap.quotKerEquivOfSurjective u hu).symm.toLinearMap, LinearMap.ext fun m => ?_⟩
  have hmk : (LinearMap.quotKerEquivOfSurjective u hu).symm (u m)
      = (Submodule.Quotient.mk m : M ⧸ LinearMap.ker u) :=
    (LinearEquiv.symm_apply_eq _).mpr
      (LinearMap.quotKerEquivOfSurjective_apply_mk (f := u) hu m).symm
  change (Submodule.liftQ _ phi hkphi)
    ((LinearMap.quotKerEquivOfSurjective u hu).symm (u m)) = phi m
  rw [hmk, Submodule.liftQ_apply]

omit [IsDomain R] in
/-- **The double transpose of a surjection whose kernel is torsion is bijective**, and in
particular surjective — which the double transpose of a bare surjection need not be. -/
public theorem bijective_dualMap_dualMap_of_surjective_of_ker_le_torsion {u : M →ₗ[R] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion R M) :
    Function.Bijective u.dualMap.dualMap :=
  (LinearEquiv.ofBijective u.dualMap
    (bijective_dualMap_of_surjective_of_ker_le_torsion hu hker)).dualMap.bijective

/-- **Over a Dedekind domain the double dual of a finite module is its torsion-free quotient.**
The canonical map is surjective by [Stacks, Tag 0B36] and has kernel the torsion submodule. -/
public def torsionQuotientDualEquiv [IsDedekindDomain R] [Module.Finite R M] :
    (M ⧸ Submodule.torsion R M) ≃ₗ[R] Module.Dual R (Module.Dual R M) :=
  (Submodule.quotEquivOfEq _ _ ker_dualEval_eq_torsion.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_dualEval_of_finite R M))

/-- The identification sends the class of `m` to evaluation at `m`. -/
public theorem torsionQuotientDualEquiv_mk [IsDedekindDomain R] [Module.Finite R M] (m : M) :
    torsionQuotientDualEquiv (Submodule.Quotient.mk m : M ⧸ Submodule.torsion R M)
      = Module.Dual.eval R M m := rfl

namespace Stacks.OrderOfVanishing

/-- **The identification of the double dual with the torsion-free quotient is natural**: it
carries `torsionQuotientMap f` to the double transpose of `f`. -/
public theorem torsionQuotientDualEquiv_torsionQuotientMap [IsLocalRing R]
    [IsDiscreteValuationRing R] [Module.Finite R M] [Module.Finite R M'] (f : M →ₗ[R] M')
    (q : M ⧸ Submodule.torsion R M) :
    torsionQuotientDualEquiv (torsionQuotientMap f q)
      = f.dualMap.dualMap (torsionQuotientDualEquiv q) := by
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    have hL : torsionQuotientMap f (Submodule.Quotient.mk m : M ⧸ Submodule.torsion R M)
        = (Submodule.Quotient.mk (f m) : M' ⧸ Submodule.torsion R M') := rfl
    rw [hL, torsionQuotientDualEquiv_mk, torsionQuotientDualEquiv_mk]
    exact (LinearMap.congr_fun (Module.Dual.eval_naturality f) m).symm

end Stacks.OrderOfVanishing

end
