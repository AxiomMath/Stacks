module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.IdealPowers
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PrincipalIdealExtension
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.TorsionFreeAndDivisibleSystems

/-!
# Multiplication by a section on a coherent adic system along a principal ideal

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf and `(F_n)` a coherent adic system along
`ℐ`, so that `F_n` is annihilated by `ℐ ⁿ⁺¹` and the transition `F_{n+1} ⟶ F_n` presents `F_n`
as `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1}`. Let `t` be a global section of `𝒪_X` lying in `ℐ` on every affine
open — for `ℐ = (t)` this is automatic.

Multiplication by `t` on `F_{n+1}` then kills `ℐ ⁿ⁺¹ F_{n+1}`, because `t · ℐ ⁿ⁺¹ ⊆ ℐ ⁿ⁺²` and
`ℐ ⁿ⁺² F_{n+1} = 0`. So it factors through the transition map, and the factorization
`ι_n : F_n ⟶ F_{n+1}` is the first datum of condition (1) of [Stacks, Tag 0H39] for
multiplication by `t`: that condition asks for a map `ι_n` with
`(F_{n+1} ⟶ F_n) ≫ ι_n = t·` whose cokernel sequence `0 → F_n → F_{n+1} → F_1 → 0` is short
exact.

This file constructs `ι_n` and proves the factorization identity. What is left of condition (1)
is the short exactness of `0 → F_n → F_{n+1} → F_1 → 0`; in the proof of [Stacks, Tag 0DXW] that
remaining step is the one which uses finite local freeness of `F_n` over `𝒪_X / ℐ ⁿ` and the
hypothesis that `t` is a nonzerodivisor, and nothing here uses either.

## Main definitions

* `Stacks.Coherent.mulGlobalSection` — multiplication by a global section of `𝒪_X`, as an
  endomorphism of the identity functor of `𝒪_X`-modules, which is the shape
  `Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.Condition1` takes its scalar in.
* `Stacks.Coherent.mulSection` — the same multiplication on a single `𝒪_X`-module.
* `Stacks.Coherent.mulSectionDesc` — multiplication by `t` on a module annihilated by
  `ℐ ⁿ⁺¹`, read as a map out of the quotient by `ℐ ⁿ`.
* `Stacks.Coherent.IsCoherentAdicSystem.principalRaise` — the map `ι_n : F_n ⟶ F_{n+1}`.

## Main results

* `Stacks.Coherent.idealPowerMultiple_ι_comp_mulSection` — multiplication by `t`
  annihilates `ℐ ⁿ M` when `ℐ ⁿ⁺¹ M = 0`.
* `Stacks.Coherent.mulSection_eq_zero` — multiplication by `t` is zero on a module annihilated
  by `ℐ`.
* `Stacks.Coherent.IsCoherentAdicSystem.map_comp_principalRaise` — the factorization identity
  `(F_{n+1} ⟶ F_n) ≫ ι_n = t·`.
* `Stacks.Coherent.IsCoherentAdicSystem.principalRaise_comp_eq_zero` — every morphism
  `F_{n+1} ⟶ F_1` kills the image of `ι_n`; in particular the composite
  `F_n ⟶ F_{n+1} ⟶ F_1` of `principalRaise_comp_proj` vanishes.
* `Stacks.Coherent.IsCoherentAdicSystem.condition1_of_shortExact` — condition (1) of
  [Stacks, Tag 0H39] follows from the short exactness of `0 → F_n → F_{n+1} → F_1 → 0` for the
  maps constructed here.

## Implementation notes

The hypothesis on `t` is `∀ V : X.affineOpens, restrictTop t V ∈ ℐ(V)` rather than an equality
`ℐ = (t)`, so that a consumer whose ideal sheaf is presented differently — as the pullback to an
open of the ideal sheaf of a closed subscheme, say — needs only that membership and no
identification of ideal sheaves. For `ℐ = (t)` it is
`Stacks.AlgebraicGeometry.PrincipalIdealExtension.restrictTop_mem_ideal_principalIdealSheaf`.

That multiplication by `t` kills `ℐ ⁿ M` is proved through the sectionwise kernel
`Stacks.Algebraization.kernelSubmodule`: the affine-local universal property of `ℐ ⁿ M` reduces
it to the statement that `t · a` annihilates the sections of `M` over an affine open for
`a ∈ ℐ(V) ⁿ`, which is `t · a ∈ ℐ(V) ⁿ⁺¹` together with the annihilation hypothesis.

Vanishing of multiplication by `t` on `F_1` is the case `n = 0` of the same computation, since
`ℐ ⁰ M` is all of `M`.

Multiplication by `t` is carried both as an endomorphism `mulGlobalSection` of the identity
functor of `SheafOfModules X.ringCatSheaf` and as a morphism `mulSection` of `X.Modules`. The
two categories are the same, but `X.Modules` is a separate definition, so a term whose type is
stated in the first presentation does not accept the field projection `Hom.app` of the second;
every computation on sections is therefore run with `mulSection`, and `mulGlobalSection_app`
transports the result to the shape [Stacks, Tag 0H39] asks for.

## References

* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
open Stacks.Algebraization
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (restrictTop smulPowHom smulPowHom_app)
open Stacks.Cohomology.InverseSystems.TorsionFreeDivisible (Condition1 proj)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-! ### Multiplication by a global section -/

/-- **Multiplication by a global section of `𝒪_X`**, as an endomorphism of the identity functor
of `𝒪_X`-modules. This is the shape in which [Stacks, Tag 0H39] takes its scalar. -/
abbrev mulGlobalSection (X : Scheme.{u}) (t : Γ(X, ⊤)) :
    End (𝟭 (SheafOfModules.{u} X.ringCatSheaf)) :=
  Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf (⊤ : X.Opens) isTerminalTop t

/-- **Multiplication by a global section of `𝒪_X` on a single module.** -/
abbrev mulSection (t : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M := smulPowHom M t 1

/-- Multiplication by `t` on sections is multiplication by the restriction of `t`. -/
theorem mulSection_app (t : Γ(X, ⊤)) (M : X.Modules) (V : X.Opens) (x : Γ(M, V)) :
    (mulSection t M).app V x = restrictTop t V • x := by
  rw [mulSection, smulPowHom_app, pow_one]

/-- The endomorphism of the identity functor evaluates to multiplication by `t`. -/
theorem mulGlobalSection_app (t : Γ(X, ⊤)) (M : X.Modules) :
    (mulGlobalSection X t).asHom.app M = mulSection t M := by
  rw [mulSection, Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom, pow_one]

/-- Multiplication by `t` is natural in the module: it commutes with every morphism of
`𝒪_X`-modules, these being `𝒪_X`-linear. -/
theorem mulSection_naturality (t : Γ(X, ⊤)) {M N : X.Modules} (g : M ⟶ N) :
    mulSection t M ≫ g = g ≫ mulSection t N := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change g.app V ((mulSection t M).app V x) = (mulSection t N).app V (g.app V x)
  rw [mulSection_app, mulSection_app, Scheme.Modules.Hom.app_smul]

/-! ### Multiplication by `t` kills `ℐ ⁿ M` when `ℐ ⁿ⁺¹ M = 0` -/

variable (I : X.IdealSheafData) (t : Γ(X, ⊤))

/-- **Multiplication by `t` kills `ℐ ⁿ M` as soon as `ℐ ⁿ⁺¹ M = 0`.** On an affine open the
subsheaf `ℐ ⁿ M` is generated by the products `a · x` with `a ∈ ℐ(V) ⁿ`, and `t · a` lies in
`ℐ(V) ⁿ⁺¹`, which annihilates the sections of `M`. -/
theorem idealPowerMultiple_le_kernelSubmodule_mulSection
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (n : ℕ) (M : X.Modules) (hM : idealPowerMultiple I (n + 1) M = ⊥) :
    idealPowerMultiple I n M ≤ kernelSubmodule (mulSection t M) := by
  refine (idealPowerMultiple_le_iff I n M _).mpr fun V => ?_
  refine Submodule.smul_le.mpr fun a ha x _ => ?_
  rw [kernelSubmodule_toSubmodule_obj]
  have hmem : restrictTop t V.1 * a ∈ I.ideal V ^ (n + 1) := by
    rw [pow_succ, mul_comm]
    exact Ideal.mul_mem_mul (ht V) ha
  have hzero : (mulSection t M).app V.1 (a • x) = 0 := by
    rw [mulSection_app, smul_smul]
    exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot hM V hmem x
  exact hzero

/-- Multiplication by `t` kills every section of `ℐ ⁿ M` when `ℐ ⁿ⁺¹ M = 0`. -/
private theorem mulSection_app_eq_zero_of_mem_idealPowerMultiple
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (n : ℕ) (M : X.Modules) (hM : idealPowerMultiple I (n + 1) M = ⊥) (V : X.Opens)
    (x : Γ(M, V)) (hx : x ∈ (idealPowerMultiple I n M).toSubmodule.obj (op V)) :
    (mulSection t M).app V x = 0 := by
  have hx := idealPowerMultiple_le_kernelSubmodule_mulSection I t ht n M hM (op V) hx
  rwa [kernelSubmodule_toSubmodule_obj] at hx

/-- The inclusion of `ℐ ⁿ M` into `M`, followed by multiplication by `t`, is zero when
`ℐ ⁿ⁺¹ M = 0`. -/
theorem idealPowerMultiple_ι_comp_mulSection
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (n : ℕ) (M : X.Modules) (hM : idealPowerMultiple I (n + 1) M = ⊥) :
    ((idealPowerMultiple I n M).ι :
        ((idealPowerMultiple I n M).toSheafOfModules : X.Modules) ⟶ M) ≫ mulSection t M =
      (0 : ((idealPowerMultiple I n M).toSheafOfModules : X.Modules) ⟶ _) := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  exact mulSection_app_eq_zero_of_mem_idealPowerMultiple I t ht n M hM V _ x.property

/-- **Multiplication by `t` is zero on a module annihilated by `ℐ`.** This is the case `n = 0`
of `idealPowerMultiple_le_kernelSubmodule_mulSection`, the zeroth ideal-power multiple being all
of the module. -/
theorem mulSection_eq_zero
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (N : X.Modules) (hN : idealPowerMultiple I 1 N = ⊥) :
    mulSection t N = (0 : N ⟶ N) := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  refine mulSection_app_eq_zero_of_mem_idealPowerMultiple I t ht 0 N hN V x ?_
  rw [Stacks.Algebraization.idealPowerMultiple_zero I N, AlgebraicGeometry.sheafTop_obj]
  trivial

/-! ### The factorization through the quotient -/

/-- **Multiplication by `t`, read as a map out of `M / ℐ ⁿ M`.** It exists because
multiplication by `t` kills `ℐ ⁿ M` when `ℐ ⁿ⁺¹ M = 0`. -/
def mulSectionDesc
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (n : ℕ) (M : X.Modules) (hM : idealPowerMultiple I (n + 1) M = ⊥) :
    idealPowerQuotient I n M ⟶ M :=
  cokernel.desc (C := X.Modules) (idealPowerMultiple I n M).ι (mulSection t M)
    (idealPowerMultiple_ι_comp_mulSection I t ht n M hM)

/-- The defining property of `mulSectionDesc`. -/
@[reassoc]
theorem cokernel_π_comp_mulSectionDesc
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (n : ℕ) (M : X.Modules) (hM : idealPowerMultiple I (n + 1) M = ⊥) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι ≫
        mulSectionDesc I t ht n M hM = mulSection t M :=
  cokernel.π_desc _ _ _

namespace IsCoherentAdicSystem

variable {I} {F : ℕᵒᵖ ⥤ X.Modules}

/-- **The map `ι_n : F_n ⟶ F_{n+1}` of condition (1) of [Stacks, Tag 0H39].** It is
multiplication by `t` on `F_{n+1}`, read through the presentation of `F_n` as
`F_{n+1} / ℐ ⁿ⁺¹ F_{n+1}`. -/
def principalRaise (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V) (n : ℕ) :
    F.obj (op n) ⟶ F.obj (op (n + 1)) :=
  (hF.quotientIso n).inv ≫
    mulSectionDesc I t ht (n + 1) (F.obj (op (n + 1))) (hF.idealPowerMultiple_eq_bot (n + 1))

/-- **The factorization identity.** Multiplication by `t` on `F_{n+1}` is the transition map
followed by `ι_n`. -/
@[reassoc]
theorem map_comp_principalRaise (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V) (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)).op ≫ principalRaise hF t ht n =
      mulSection t (F.obj (op (n + 1))) := by
  rw [principalRaise, ← hF.cokernel_π_comp_quotientIso n, Category.assoc,
    ← Category.assoc (hF.quotientIso n).hom, Iso.hom_inv_id, Category.id_comp,
    cokernel_π_comp_mulSectionDesc]

/-- The underlying family of terms of the system, zero-indexed: term `n` is the source's
`F_{n+1}`. This is the shape
`Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.Condition1` takes its system in. -/
abbrev objFamily (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) : X.Modules := F.obj (op n)

/-- The successive transition maps of the system. -/
abbrev mapFamily (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) : objFamily F (n + 1) ⟶ objFamily F n :=
  F.map (homOfLE (Nat.le_succ n)).op

/-- **Every morphism `F_{n+1} ⟶ F_1` kills the image of `ι_n`.** Precomposing with the
epimorphism `F_{n+1} ⟶ F_n` turns `ι_n ≫ φ` into multiplication by `t` followed by `φ`, which by
naturality is `φ` followed by multiplication by `t` on `F_1`; and `t` annihilates `F_1`. -/
theorem principalRaise_comp_eq_zero (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V) (n : ℕ)
    (φ : objFamily F (n + 1) ⟶ objFamily F 0) :
    principalRaise hF t ht n ≫ φ = 0 := by
  have hepi : Epi (mapFamily F n) := hF.epi_map_succ n
  refine (cancel_epi (mapFamily F n)).mp ?_
  rw [comp_zero, ← Category.assoc, map_comp_principalRaise hF t ht n,
    mulSection_naturality t φ,
    mulSection_eq_zero I t ht (objFamily F 0) (hF.idealPowerMultiple_eq_bot 0), comp_zero]

/-- **The composite `F_n ⟶ F_{n+1} ⟶ F_1` vanishes.** -/
theorem principalRaise_comp_proj (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V) (n : ℕ) :
    principalRaise hF t ht n ≫ proj (objFamily F) (mapFamily F) (n + 1) = 0 :=
  principalRaise_comp_eq_zero hF t ht n (proj (objFamily F) (mapFamily F) (n + 1))

/-- **Condition (1) of [Stacks, Tag 0H39] for a coherent adic system along a principal ideal.**
Everything but the short exactness of `0 → F_n → F_{n+1} → F_1 → 0` is supplied by the
construction above, so that is all a caller has to prove. -/
theorem condition1_of_shortExact (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (hse : ∀ n : ℕ, (ShortComplex.mk (principalRaise hF t ht n)
      (proj (objFamily F) (mapFamily F) (n + 1))
      (principalRaise_comp_proj hF t ht n)).ShortExact) :
    Condition1 (mulGlobalSection X t) (objFamily F) (mapFamily F) := fun n =>
  ⟨principalRaise hF t ht n, principalRaise_comp_proj hF t ht n,
    (map_comp_principalRaise hF t ht n).trans
      (mulGlobalSection_app t (objFamily F (n + 1))).symm, hse n⟩

end IsCoherentAdicSystem

end Stacks.Coherent

end
