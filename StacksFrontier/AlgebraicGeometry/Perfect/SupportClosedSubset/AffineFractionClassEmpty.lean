module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassMap
import StacksCore.Tactic.StacksAttribute

/-!
# The affine description of the fraction class map for the empty family

Let `A` be a commutative ring and `M` an `A`-module, and take `X = Spec A` and `ℱ = M~`. For the
empty family of equations (`c = 0`) the closed subset they cut out is `X` itself, the extended
alternating Čech complex is `ℱ` in degree `0`, and the description of Tag 0G7R reads

`M/(f₁, …, f_c)M = M ⟶ Coker(0 ⟶ M_{f₁⋯f_c}) = M_1`,  `s ↦ s/1`.

This file proves it for the map `c_{f₁, …, f_c}` of Tag 0G7Q, in the form
`Stacks.Perfect.FractionClass.quotientClassMap`, read on global sections through the canonical
isomorphisms

`M/(f₁, …, f_c)M ≅ Γ(Spec A, ℱ/(f₁, …, f_c)ℱ)` and `M_{f₁⋯f_c} ≅ Γ(Spec A, H⁰(ℱ^•))`,

the second being `M_1 = M = Γ(Spec A, ℱ)` followed by the identification `ℱ ≅ H⁰(ℱ^•)` of the
degree-`0` cohomology of a complex concentrated in degree `0`.

## Main definitions

* `Stacks.Perfect.AffineFractionClassEmpty.sourceIsoEmpty` and
  `Stacks.Perfect.AffineFractionClassEmpty.targetIsoEmpty`: the two canonical isomorphisms.

## Main results

* `Stacks.Perfect.AffineFractionClassEmpty.targetIsoEmpty_inv_Γ_quotientClassMap_sourceIsoEmpty`:
  for `c = 0`, the map `c_{f₁, …, f_c}` on global sections sends the class of `s` to `s/1`.

## References

* [Stacks Project, Tag 0G7R](https://stacks.math.columbia.edu/tag/0G7R)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Perfect.ExtendedAlternatingCech Stacks.Perfect.FractionClass

universe u

namespace Stacks.Perfect.AffineFractionClassEmpty

variable {R : CommRingCat.{u}}

/-- The empty family of global functions on `Spec R` determined by the empty family of elements
of `R`. -/
abbrev specFunEmpty (f : Fin 0 → R) : Fin 0 → Γ(Spec R, ⊤) :=
  fun i => (Scheme.ΓSpecIso R).inv (f i)

/-- For the empty family the map `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` is zero, its source being the empty
coproduct. -/
theorem equationsMap_empty {X : Scheme.{u}} (g : Fin 0 → Γ(X, ⊤)) (F : X.Modules) :
    equationsMap g F = 0 :=
  Sigma.hom_ext _ _ fun i => i.elim0

/-- For the empty family the projection `ℱ ⟶ ℱ/(f₁, …, f_c)ℱ` onto the cokernel of
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` is an isomorphism. -/
instance isIso_cokernelπ_equationsMap_empty {X : Scheme.{u}} (g : Fin 0 → Γ(X, ⊤))
    (F : X.Modules) : IsIso (cokernel.π (equationsMap g F)) :=
  cokernel.π_of_zero (equationsMap_empty g F)

/-- For the empty family the extended alternating Čech complex is `ℱ` in degree `0`, so its
degree-`0` cohomology is `ℱ`: both differentials at degree `0` vanish, and the inclusion of the
cycles and the projection to cohomology are isomorphisms. -/
def homologyZeroIsoEmpty {X : Scheme.{u}} (g : Fin 0 → Γ(X, ⊤)) (F : X.Modules) :
    F ≅ (cplx g F).homology 0 :=
  haveI : IsIso ((cplx g F).iCycles 0) :=
    (cplx g F).isIso_iCycles 0 1 (by simp) (d_top_eq_zero g F)
  haveI : IsIso ((cplx g F).homologyπ 0) :=
    (cplx g F).isIso_homologyπ 0 0 (by simp) ((cplx g F).shape 0 0 (by simp))
  (asIso ((cplx g F).iCycles 0)).symm ≪≫ asIso ((cplx g F).homologyπ 0)

/-- For the empty family the fraction class `ℱ ⟶ H⁰(ℱ^•)` is the identification of `ℱ` with
the degree-`0` cohomology of its extended alternating Čech complex: the fraction of a section by
the empty product is the section itself. -/
theorem classMap_empty {X : Scheme.{u}} (g : Fin 0 → Γ(X, ⊤)) (F : X.Modules) :
    classMap g F = (homologyZeroIsoEmpty g F).hom := by
  have : IsIso ((cplx g F).iCycles 0) :=
    (cplx g F).isIso_iCycles 0 1 (by simp) (d_top_eq_zero g F)
  have hc : fracCycle g F = inv ((cplx g F).iCycles 0) :=
    (cancel_mono ((cplx g F).iCycles 0)).1
      ((fracCycle_comp_iCycles g F).trans (IsIso.inv_hom_id ((cplx g F).iCycles 0)).symm)
  rw [classMap, hc]
  rfl

variable (f : Fin 0 → R) (M : ModuleCat.{u} R)

/-- For the empty family `(f₁, …, f_c)M = 0`. -/
theorem span_range_empty_smul_top :
    Ideal.span (Set.range f) • (⊤ : Submodule R M) = ⊥ := by
  rw [Set.range_eq_empty, Ideal.span_empty, Submodule.bot_smul]

/-- The localization of `M` at the powers of the empty product `1` is `M`. -/
def localizedEmptyEquiv :
    M ≃ₗ[R] LocalizedModule (Submonoid.powers (∏ i, f i)) M :=
  LinearEquiv.ofBijective (LocalizedModule.mkLinearMap _ M) <| by
    have hS : ∀ s : Submonoid.powers (∏ i, f i), (s : R) = 1 := by
      rintro ⟨_, k, rfl⟩
      simp
    refine ⟨fun a b h => ?_, fun x => ?_⟩
    · obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq).1 h
      simpa [Submonoid.smul_def, hS] using hu
    · induction x using LocalizedModule.induction_on with
      | h m s =>
        refine ⟨m, ?_⟩
        rw [LocalizedModule.mkLinearMap_apply]
        exact (LocalizedModule.mk_eq).2 ⟨1, by simp [Submonoid.smul_def, hS]⟩

/-- **The source comparison for the empty family.** The canonical isomorphism
`M/(f₁, …, f_c)M ≅ Γ(Spec R, ℱ/(f₁, …, f_c)ℱ)` for `ℱ = M~`, sending the class of `s ∈ M` to the
class of the section `s`. -/
def sourceIsoEmpty :
    ModuleCat.of R (M ⧸ Ideal.span (Set.range f) • (⊤ : Submodule R M)) ≅
      moduleSpecΓFunctor.obj (equationsQuotient (specFunEmpty f) (tilde M)) :=
  (Submodule.quotEquivOfEqBot _ (span_range_empty_smul_top f M)).toModuleIso ≪≫
    tilde.isoTop M ≪≫
    moduleSpecΓFunctor.mapIso (@asIso _ _ _ _ (cokernel.π (equationsMap (specFunEmpty f) (tilde M)))
      (isIso_cokernelπ_equationsMap_empty _ _))

/-- **The target comparison for the empty family.** The canonical isomorphism
`M_{f₁⋯f_c} ≅ Γ(Spec R, H⁰(ℱ^•))` for `ℱ = M~`, sending `s/1` to the class of the section `s`. -/
def targetIsoEmpty :
    ModuleCat.of R (LocalizedModule (Submonoid.powers (∏ i, f i)) M) ≅
      moduleSpecΓFunctor.obj ((cplx (specFunEmpty f) (tilde M)).homology 0) :=
  (localizedEmptyEquiv f M).symm.toModuleIso ≪≫ tilde.isoTop M ≪≫
    moduleSpecΓFunctor.mapIso (homologyZeroIsoEmpty (specFunEmpty f) (tilde M))

/-- For the empty family (`c = 0`), let `A` be a commutative ring, let `M` be an `A`-module and
take `X = Spec A`, `ℱ = M~` and the empty family of equations. Then the map `c_{f₁, …, f_c}` of
Tag 0G7Q, read on global sections through the canonical isomorphisms
`M/(f₁, …, f_c)M ≅ Γ(Spec A, ℱ/(f₁, …, f_c)ℱ)` (`sourceIsoEmpty`) and
`M_{f₁⋯f_c} ≅ Γ(Spec A, H⁰(ℱ^•))` (`targetIsoEmpty`), sends the class of `s ∈ M` to the fraction
`s/(f₁⋯f_c)`; here `f₁⋯f_c = 1`, the cokernel of the map out of the empty direct sum is
`M_{f₁⋯f_c}` itself, and the map is `s ↦ s/1`. -/
@[stacks 0G7R "the case c = 0: for X = Spec A, ℱ = M~ and the empty family, Tag 0G7Q's map on \
global sections, conjugated by the canonical isomorphisms sourceIsoEmpty and targetIsoEmpty, \
sends the class of s ∈ M to s/(f₁⋯f_c) = s/1"]
theorem targetIsoEmpty_inv_Γ_quotientClassMap_sourceIsoEmpty (s : M) :
    (targetIsoEmpty f M).inv
        ((moduleSpecΓFunctor.map (quotientClassMap (specFunEmpty f) (tilde M))).hom
          ((sourceIsoEmpty f M).hom (Submodule.Quotient.mk s))) =
      LocalizedModule.mk s ⟨∏ i, f i, Submonoid.mem_powers _⟩ := by
  refine ((targetIsoEmpty f M).toLinearEquiv.symm_apply_eq).2 ?_
  have h₂ : (localizedEmptyEquiv f M).symm
      (LocalizedModule.mk s ⟨∏ i, f i, Submonoid.mem_powers _⟩) = s :=
    (localizedEmptyEquiv f M).symm_apply_eq.2 rfl
  rw [Iso.toLinearEquiv_apply]
  show (moduleSpecΓFunctor.map (quotientClassMap (specFunEmpty f) (tilde M))).hom
      ((moduleSpecΓFunctor.map (cokernel.π (equationsMap (specFunEmpty f) (tilde M)))).hom
        ((tilde.isoTop M).hom ((Submodule.quotEquivOfEqBot _ (span_range_empty_smul_top f M))
          (Submodule.Quotient.mk s)))) =
    (moduleSpecΓFunctor.map (homologyZeroIsoEmpty (specFunEmpty f) (tilde M)).hom).hom
      ((tilde.isoTop M).hom ((localizedEmptyEquiv f M).symm
        (LocalizedModule.mk s ⟨∏ i, f i, Submonoid.mem_powers _⟩)))
  rw [h₂, Submodule.quotEquivOfEqBot_apply_mk]
  have e := congrArg (fun φ => (moduleSpecΓFunctor.map φ).hom ((tilde.isoTop M).hom s))
    ((cokernelπ_comp_quotientClassMap (specFunEmpty f) (tilde M)).trans
      (classMap_empty (specFunEmpty f) (tilde M)))
  simp only at e
  exact e

end Stacks.Perfect.AffineFractionClassEmpty
