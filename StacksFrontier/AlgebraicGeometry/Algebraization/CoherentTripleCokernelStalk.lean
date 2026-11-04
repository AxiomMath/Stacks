module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Stalks
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PrincipalIdealExtension

/-!
# The stalks of `F / a F`

For a module `F` on a scheme `X` and a global section `a` of the structure sheaf, the quotient
`F / a F` is the cokernel of multiplication by `a`,
`Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom F a 1`. This file computes its
stalks: at a point `x` the stalk is `F_x ⧸ (germ_x a) · F_x`.

## Main definitions

* `Stacks.Algebraization.cokernelSmulPowHomStalkLinearEquiv`: the displayed identification, as a
  linear equivalence over the local ring `𝒪_{X, x}`.

## Main results

* `Stacks.Algebraization.stalkLinearMap_smulPowHom_one`: the stalk map of multiplication by `a`
  is multiplication by the germ of `a`.
* `Stacks.Algebraization.range_stalkLinearMap_smulPowHom_one`: its range is the submodule
  `(germ_x a) · F_x`.
* `Stacks.Algebraization.isAssociatedPoint_cokernel_smulPowHom_one_iff`: the associated-point
  dictionary — `x` is associated to `F / a F` exactly when the maximal ideal of `𝒪_{X, x}` is an
  associated prime of `F_x ⧸ (germ_x a) F_x`.

This is one of the two stalk computations the closed-fibre monicity of the third clause of
`Stacks.Algebraization.HasHilbertInductionStep` was waiting on; the other is in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleStalkKernel`, and the consumer that
joins them is
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleAssociatedPointsTransfer`. The
submodule divided out is written `Ideal.span {germ a} • ⊤`, which is the shape
`Stacks.Divisors.isAssociatedPoint_pullback_iff_quotient` presents its quotient in, so the two
compose without a comparison.

## Implementation notes

Exactness of the stalk functor is not re-proved: `Stacks.Chow.cokernelStalkLinearEquiv`
identifies the stalk of a cokernel with the quotient of the stalk by the *range* of the stalk
map, for an arbitrary morphism of modules on a scheme. All that is added is the evaluation of
that range for `smulPowHom`, which is the ideal multiple, and the resulting dictionary.

`Stacks.Algebraization.stalkLinearMap_smulPowHom_one_germ` is stated separately from the
general element form because its proof needs a local section to compute with, and the general
form then follows by `TopCat.Presheaf.exists_germ_eq`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Limits
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom smulPowHom_app restrictTop)

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- **The stalk map of multiplication by a global section is multiplication by its germ**, on
the germ of a local section. -/
theorem stalkLinearMap_smulPowHom_one_germ (F : X.Modules) (a : Γ(X, ⊤)) (x : X) (U : X.Opens)
    (hx : x ∈ U) (m₀ : Γ(F, U)) :
    AlgebraicGeometry.stalkLinearMap F F (smulPowHom F a 1) x
        (F.presheaf.germ U x hx m₀) =
      (X.presheaf.Γgerm x).hom a • F.presheaf.germ U x hx m₀ := by
  have h : (smulPowHom F a 1).val.app (op U) m₀ = restrictTop a U • m₀ := by
    rw [show (smulPowHom F a 1).val.app (op U) m₀ = (smulPowHom F a 1).app U m₀ from rfl,
      smulPowHom_app, pow_one]
  have h2 : (F.presheaf.germ U x hx) (restrictTop a U • m₀) =
      (X.presheaf.germ U x hx).hom (restrictTop a U) • (F.presheaf.germ U x hx) m₀ :=
    PresheafOfModules.germ_smul F.val x U hx (restrictTop a U) m₀
  have h3 : (X.presheaf.germ U x hx).hom (restrictTop a U) = (X.presheaf.Γgerm x).hom a :=
    X.presheaf.germ_res_apply (homOfLE le_top) x hx a
  refine (AlgebraicGeometry.stalkLinearMap_germ F F (smulPowHom F a 1) U x hx m₀).trans ?_
  refine (congrArg (fun t => (F.presheaf.germ U x hx) t) h).trans ?_
  exact h2.trans (congrArg (fun r => r • (F.presheaf.germ U x hx) m₀) h3)

/-- The stalk map of multiplication by a global section is multiplication by its germ. -/
theorem stalkLinearMap_smulPowHom_one (F : X.Modules) (a : Γ(X, ⊤)) (x : X)
    (m : F.presheaf.stalk x) :
    AlgebraicGeometry.stalkLinearMap F F (smulPowHom F a 1) x m =
      (X.presheaf.Γgerm x).hom a • m := by
  obtain ⟨U, hx, m₀, hm⟩ := F.presheaf.exists_germ_eq m
  subst hm
  exact stalkLinearMap_smulPowHom_one_germ F a x U hx m₀

/-- The range of the stalk map of multiplication by a global section `a` is the submodule
`(a) · F_x` of the stalk. -/
theorem range_stalkLinearMap_smulPowHom_one (F : X.Modules) (a : Γ(X, ⊤)) (x : X) :
    LinearMap.range (AlgebraicGeometry.stalkLinearMap F F (smulPowHom F a 1) x) =
      Ideal.span {(X.presheaf.Γgerm x).hom a} •
        (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨m, rfl⟩
    rw [stalkLinearMap_smulPowHom_one]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · refine Submodule.smul_le.mpr fun r hr m _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    refine ⟨c • m, ?_⟩
    rw [map_smul, stalkLinearMap_smulPowHom_one, smul_smul]

/-- **The stalk of `F / a F`.** The stalk at `x` of the cokernel of multiplication by a global
section `a` is the quotient of the stalk of `F` by the submodule `(a) · F_x`. -/
noncomputable def cokernelSmulPowHomStalkLinearEquiv (F : X.Modules) (a : Γ(X, ⊤)) (x : X) :
    (F.presheaf.stalk x ⧸ (Ideal.span {(X.presheaf.Γgerm x).hom a} •
        (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))) : Type u)
      ≃ₗ[X.presheaf.stalk x] (cokernel (smulPowHom F a 1)).presheaf.stalk x :=
  (Submodule.quotEquivOfEq _ _ (range_stalkLinearMap_smulPowHom_one F a x).symm).trans
    (Stacks.Chow.cokernelStalkLinearEquiv (smulPowHom F a 1) x)

/-- **The associated-point dictionary for `F / a F`.** A point `x` is associated to the cokernel
of multiplication by a global section `a` exactly when the maximal ideal of `𝒪_{X, x}` is an
associated prime of `F_x ⧸ (a) F_x`. -/
theorem isAssociatedPoint_cokernel_smulPowHom_one_iff (F : X.Modules) (a : Γ(X, ⊤)) (x : X) :
    Stacks.Divisors.IsAssociatedPoint (cokernel (smulPowHom F a 1)) x ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk x)
        (F.presheaf.stalk x ⧸ (Ideal.span {(X.presheaf.Γgerm x).hom a} •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
  ⟨Stacks.Divisors.isAssociatedPrimeStacks_of_linearEquiv
      (cokernelSmulPowHomStalkLinearEquiv F a x).symm,
    Stacks.Divisors.isAssociatedPrimeStacks_of_linearEquiv
      (cokernelSmulPowHomStalkLinearEquiv F a x)⟩

end Stacks.Algebraization

end
