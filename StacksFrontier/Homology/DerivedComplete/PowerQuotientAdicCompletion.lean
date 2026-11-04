module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequences
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteFlatTensor
import all StacksFrontier.Homology.DerivedComplete.NoetherianCompleteFlatTensor

/-!
# The limit of the power-quotient tower is the ordinary adic completion

`CompletionSequences.powerQuotientSystem A M f` is the inverse system of cokernels of
multiplication by `f ^ (n + 1)` on an `A`-module `M`. Its limit is the ordinary `f`-adic
completion of `M`, that is, Mathlib's `AdicCompletion (Ideal.span {f}) M`: the cokernel of
multiplication by `f ^ (n + 1)` is `M ⧸ (f) ^ (n + 1) M`, because the range of multiplication by
`f ^ (n + 1)` is the submodule `(f) ^ (n + 1) • ⊤`.

The identification matters because the formal-functions sequence of Stacks 0BLD, and the
comparison diagram of Stacks 0H32 that produces it, write their left-hand term as
`limit (CompletionSequences.powerQuotientSystem A M f)`, while the completeness hypotheses
available for that term — for instance
`AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing` — are stated with Mathlib's
`IsAdicComplete`. The consequence used downstream is
`Stacks.PowerQuotient.isIso_completionComparison`: for an `f`-adically complete module the
canonical map into the limit of the power-quotient tower is an isomorphism.

## Main definitions

* `Stacks.PowerQuotient.completionCone` — the cone on the power-quotient tower given by the
  canonical quotient maps out of `M`.
* `Stacks.PowerQuotient.completionComparison` — the induced map from `M` to the limit of its
  power-quotient tower.
* `Stacks.PowerQuotient.limitIsoAdicCompletion` — the limit of the power-quotient tower is the
  ordinary `f`-adic completion.

## Main results

* `Stacks.PowerQuotient.range_powerMultiplication` — the range of multiplication by `a` on a
  module is `(a) • ⊤`.
* `Stacks.PowerQuotient.completionComparison_limitIsoAdicCompletion` — the comparison map becomes
  Mathlib's `AdicCompletion.of` under that identification.
* `Stacks.PowerQuotient.isIso_completionComparison` — for an `f`-adically complete module the
  comparison map is an isomorphism.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits PrincipalTorsionTower

universe u v

namespace Stacks.PowerQuotient

section General

variable {A : Type u} [CommRing A]

/-- The range of multiplication by `a` on a module is the submodule `(a) • ⊤`. -/
public theorem range_powerMultiplication (M : ModuleCat.{v} A) (a : A) :
    LinearMap.range (powerMultiplication A M a).hom =
      Ideal.span {a} • (⊤ : Submodule A M) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp [powerMultiplication]

/-- The canonical quotient maps `M ⟶ M / f ^ (n + 1) M`, as a cone on the power-quotient tower. -/
public def completionCone (M : ModuleCat.{v} A) (f : A) :
    Cone (CompletionSequences.powerQuotientSystem A M f) :=
  ⟨M, NatTrans.ofOpSequence (G := CompletionSequences.powerQuotientSystem A M f)
    (fun n ↦ cokernel.π (powerMultiplication A M (f ^ (n + 1)))) (by
      intro n
      change 𝟙 M ≫ cokernel.π (powerMultiplication A M (f ^ (n + 1))) =
        cokernel.π (powerMultiplication A M (f ^ (n + 2))) ≫
          (CompletionSequences.powerQuotientSystem A M f).map (homOfLE (Nat.le_succ n)).op
      rw [Category.id_comp, CompletionSequences.powerQuotientSystem_map_succ]
      exact (CompletionSequences.π_powerQuotientTransition A M f n).symm)⟩

/-- **The canonical map from a module to the limit of its power-quotient tower.** -/
public def completionComparison (M : ModuleCat.{v} A) (f : A) :
    (M : ModuleCat.{v} A) ⟶ limit (CompletionSequences.powerQuotientSystem A M f) :=
  limit.lift _ (completionCone M f)

/-- The `n`-th projection of `completionComparison M f` is the quotient map
`M ⟶ M / f ^ (n + 1) M`. -/
@[reassoc (attr := simp)]
public theorem completionComparison_π (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    completionComparison M f ≫ limit.π (CompletionSequences.powerQuotientSystem A M f) ⟨n⟩ =
      cokernel.π (powerMultiplication A M (f ^ (n + 1))) :=
  limit.lift_π (completionCone M f) ⟨n⟩

end General

section EqualUniverse

variable {A : Type u} [CommRing A]

/-- The `n`-th term of the power-quotient tower is `M ⧸ (f) ^ (n + 1) M`. -/
private def componentIso (M : ModuleCat.{u} A) (f : A) (n : ℕ) :
    cokernel (powerMultiplication A M (f ^ (n + 1))) ≅
      ModuleCat.of A (M ⧸ (Ideal.span {f} ^ (n + 1) • ⊤ : Submodule A M)) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    (Submodule.quotEquivOfEq _ _ (by
      rw [range_powerMultiplication, Ideal.span_singleton_pow])).toModuleIso

@[reassoc]
private theorem π_componentIso (M : ModuleCat.{u} A) (f : A) (n : ℕ) :
    cokernel.π (powerMultiplication A M (f ^ (n + 1))) ≫ (componentIso M f n).hom =
      ModuleCat.ofHom (Submodule.mkQ (Ideal.span {f} ^ (n + 1) • (⊤ : Submodule A M))) := by
  rw [componentIso, Iso.trans_hom, ← Category.assoc,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  ext x
  rfl

/-- The power-quotient tower maps to the tower of `(f)`-adic quotients. -/
private def systemHom (M : ModuleCat.{u} A) (f : A) :
    CompletionSequences.powerQuotientSystem A M f ⟶
      AdicCompletionTor.adicQuotientSystem (Ideal.span {f}) M :=
  NatTrans.ofOpSequence (fun n ↦ (componentIso M f n).hom) (by
    intro n
    rw [CompletionSequences.powerQuotientSystem_map_succ]
    change CompletionSequences.powerQuotientTransition A M f n ≫ (componentIso M f n).hom
        = (componentIso M f (n + 1)).hom ≫
          ModuleCat.ofHom (AdicCompletion.transitionMap (Ideal.span {f}) (M : Type u)
            (Nat.add_le_add_right (n.le_add_right 1) 1))
    apply (cancel_epi (cokernel.π (powerMultiplication A M (f ^ (n + 2))))).1
    rw [CompletionSequences.π_powerQuotientTransition_assoc, π_componentIso,
      π_componentIso_assoc]
    ext x
    rfl)

private instance isIso_systemHom_app (M : ModuleCat.{u} A) (f : A) (n : ℕᵒᵖ) :
    IsIso ((systemHom M f).app n) := by
  change IsIso (componentIso M f n.unop).hom
  infer_instance

/-- The power-quotient tower is the tower of `(f)`-adic quotients. -/
private def systemIso (M : ModuleCat.{u} A) (f : A) :
    CompletionSequences.powerQuotientSystem A M f ≅
      AdicCompletionTor.adicQuotientSystem (Ideal.span {f}) M :=
  haveI : IsIso (systemHom M f) := NatIso.isIso_of_isIso_app _
  asIso (systemHom M f)

private theorem systemIso_hom_app (M : ModuleCat.{u} A) (f : A) (n : ℕ) :
    (systemIso M f).hom.app ⟨n⟩ = (componentIso M f n).hom :=
  rfl

/-- **The limit of the power-quotient tower is the ordinary `f`-adic completion.** The `n`-th
projection of the limit becomes evaluation at `n + 1` on the completion. -/
public def limitIsoAdicCompletion (M : ModuleCat.{u} A) (f : A) :
    limit (CompletionSequences.powerQuotientSystem A M f) ≅
      ModuleCat.of A (AdicCompletion (Ideal.span {f}) M) :=
  HasLimit.isoOfNatIso (systemIso M f) ≪≫
    AdicCompletionFlatTensor.limitAdicQuotientIso (Ideal.span {f}) M

private theorem limitIsoAdicCompletion_hom_eval (M : ModuleCat.{u} A) (f : A) (n : ℕ) :
    (limitIsoAdicCompletion M f).hom ≫
        ModuleCat.ofHom (AdicCompletion.eval (Ideal.span {f}) (M : Type u) (n + 1)) =
      limit.π (CompletionSequences.powerQuotientSystem A M f) ⟨n⟩ ≫ (componentIso M f n).hom := by
  have h : (AdicCompletionFlatTensor.limitAdicQuotientIso (Ideal.span {f}) M).hom ≫
      ModuleCat.ofHom (AdicCompletion.eval (Ideal.span {f}) (M : Type u) (n + 1)) =
      limit.π (AdicCompletionTor.adicQuotientSystem (Ideal.span {f}) M) ⟨n⟩ :=
    IsLimit.conePointUniqueUpToIso_hom_comp _
      (AdicCompletionFlatTensor.adicCompletionConeIsLimit (Ideal.span {f}) M) ⟨n⟩
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k : limit (AdicCompletionTor.adicQuotientSystem
      (Ideal.span {f}) M) ⟶
      ModuleCat.of A (M ⧸ (Ideal.span {f} ^ (n + 1) • ⊤ : Submodule A M)) ↦
      (HasLimit.isoOfNatIso (systemIso M f)).hom ≫ k) h) ?_
  exact HasLimit.isoOfNatIso_hom_π (systemIso M f) ⟨n⟩

private theorem completionComparison_componentIso (M : ModuleCat.{u} A) (f : A) (n : ℕ) :
    completionComparison M f ≫ limit.π (CompletionSequences.powerQuotientSystem A M f) ⟨n⟩ ≫
        (componentIso M f n).hom =
      ModuleCat.ofHom (Submodule.mkQ (Ideal.span {f} ^ (n + 1) • (⊤ : Submodule A M))) := by
  refine Eq.trans (Eq.symm (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun k : (M : ModuleCat.{u} A) ⟶
      (CompletionSequences.powerQuotientSystem A M f).obj ⟨n⟩ ↦
      k ≫ (componentIso M f n).hom) (completionComparison_π M f n)) ?_
  exact π_componentIso M f n

/-- **The comparison map is Mathlib's `AdicCompletion.of`.** -/
public theorem completionComparison_limitIsoAdicCompletion (M : ModuleCat.{u} A) (f : A) :
    completionComparison M f ≫ (limitIsoAdicCompletion M f).hom =
      ModuleCat.ofHom (AdicCompletion.of (Ideal.span {f}) (M : Type u)) := by
  have key : ∀ n : ℕ, completionComparison M f ≫ (limitIsoAdicCompletion M f).hom ≫
      ModuleCat.ofHom (AdicCompletion.eval (Ideal.span {f}) (M : Type u) (n + 1)) =
      ModuleCat.ofHom (Submodule.mkQ (Ideal.span {f} ^ (n + 1) • (⊤ : Submodule A M))) := by
    intro n
    refine Eq.trans (congrArg (fun k : limit (CompletionSequences.powerQuotientSystem A M f) ⟶
        ModuleCat.of A (M ⧸ (Ideal.span {f} ^ (n + 1) • ⊤ : Submodule A M)) ↦
        completionComparison M f ≫ k) (limitIsoAdicCompletion_hom_eval M f n)) ?_
    exact completionComparison_componentIso M f n
  ext x k
  match k with
  | 0 =>
    have : Subsingleton (M ⧸ (Ideal.span {f} ^ 0 • ⊤ : Submodule A M)) := by
      simp only [pow_zero, one_smul]
      infer_instance
    exact Subsingleton.elim _ _
  | (n + 1) =>
    exact ConcreteCategory.congr_hom (key n) x

/-- **A module which is `f`-adically complete is the limit of its power-quotient tower.** -/
public theorem isIso_completionComparison (M : ModuleCat.{u} A) (f : A)
    [IsAdicComplete (Ideal.span {f}) M] : IsIso (completionComparison M f) := by
  have h : IsIso (completionComparison M f ≫ (limitIsoAdicCompletion M f).hom) := by
    rw [completionComparison_limitIsoAdicCompletion,
      show ModuleCat.ofHom (AdicCompletion.of (Ideal.span {f}) (M : Type u)) =
        (AdicCompletion.ofLinearEquiv (Ideal.span {f}) (M : Type u)).toModuleIso.hom from rfl]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (limitIsoAdicCompletion M f).hom

/-- **The power-quotient limit of an `f`-adically complete module, as an isomorphism.** -/
@[expose] public def isoLimitPowerQuotient (M : ModuleCat.{u} A) (f : A)
    [IsAdicComplete (Ideal.span {f}) M] :
    (M : ModuleCat.{u} A) ≅ limit (CompletionSequences.powerQuotientSystem A M f) :=
  @asIso _ _ _ _ (completionComparison M f) (isIso_completionComparison M f)

/-- The forward map of `isoLimitPowerQuotient M f` is `completionComparison M f`. -/
@[simp]
public theorem isoLimitPowerQuotient_hom (M : ModuleCat.{u} A) (f : A)
    [IsAdicComplete (Ideal.span {f}) M] :
    (isoLimitPowerQuotient M f).hom = completionComparison M f :=
  rfl

end EqualUniverse

end Stacks.PowerQuotient

end
