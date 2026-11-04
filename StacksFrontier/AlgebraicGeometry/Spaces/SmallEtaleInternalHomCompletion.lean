module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomSmallSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor

/-!
# The completed internal Hom on an algebraic space at the module universe `u`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (M N : Modules.{u, u} B S hS F hF)

/-- The internal Hom `𝓗om(M, -)` at the module universe `u`, as a functor. -/
abbrev smallEtaleInternalHomSmallFunctor :
    Modules.{u, u} B S hS F hF ⥤ Modules.{u, u} B S hS F hF :=
  RingedSite.internalHomSheafSmallFunctor (smallEtaleRingedSite B S hS F hF) M

/-- The equivalence `smallEtaleInternalHomSmallSectionsEquiv` sends the zero section to the zero
morphism. -/
theorem smallEtaleInternalHomSmallSectionsEquiv_zero (U : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ) :
    smallEtaleInternalHomSmallSectionsEquiv B S hS F hF M N U 0 = 0 := by
  have key : (equivShrink.{u} ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F
      hF) M N).val.obj U)).symm 0 = 0 := equivShrink_symm_zero
  exact (congrArg (fun s => (⟨s⟩ : M.over U.unop ⟶ N.over U.unop)) key).trans rfl

/-- `𝓘ᵏ` annihilates `𝓗om(M, N)` when it annihilates `N`. -/
theorem smul_smallEtaleInternalHomSmall_eq_zero (k : ℕ) (hN : IsPowAnnihilated B S hS F hF 𝓘 k N)
    (U : SmallEtale B S hS F) (r : chartRing B S hS F hF U)
    (hr : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k)
    (x : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj (op U)) : r • x = 0 := by
  apply (smallEtaleInternalHomSmallSectionsEquiv B S hS F hF M N (op U)).injective
  rw [smallEtaleInternalHomSmallSectionsEquiv_zero]
  ext ⟨V⟩ z
  rw [smallEtaleInternalHomSmallSectionsEquiv_smul]
  exact hN V.left _ (chartRestrict_mem_chartIdeal_pow B S hS F hF 𝓘 V.hom k hr) _

/-- Postcomposition `𝓗om(M, N) ⟶ 𝓗om(M, P)` with a morphism `N ⟶ P`. -/
def internalHomPostcomp {N P : Modules.{u, u} B S hS F hF} (g : N ⟶ P) :
    smallEtaleInternalHomSmall B S hS F hF M N ⟶ smallEtaleInternalHomSmall B S hS F hF M P :=
  (smallEtaleInternalHomSmallFunctor B S hS F hF M).map g

/-- Postcomposition with a composite `g ≫ g'` is the composite of the postcompositions. -/
theorem internalHomPostcomp_comp {N P Q : Modules.{u, u} B S hS F hF} (g : N ⟶ P) (g' : P ⟶ Q) :
    internalHomPostcomp B S hS F hF M (g ≫ g') =
      internalHomPostcomp B S hS F hF M g ≫ internalHomPostcomp B S hS F hF M g' :=
  (smallEtaleInternalHomSmallFunctor B S hS F hF M).map_comp g g'

/-- **The comparison `𝓗om(M, N) / 𝓘ⁿ 𝓗om(M, N) ⟶ 𝓗om(M, N / 𝓘ⁿ N)`**, induced by postcomposition
with the projection `N ⟶ N / 𝓘ⁿ N`. -/
def internalHomAdicComparison (n : ℕ) :
    idealPowerQuotient B S hS F hF 𝓘 n (smallEtaleInternalHomSmall B S hS F hF M N) ⟶
      smallEtaleInternalHomSmall B S hS F hF M (idealPowerQuotient B S hS F hF 𝓘 n N) :=
  cokernel.desc _ (internalHomPostcomp B S hS F hF M
      (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 n N).ι)) (by
    rw [idealPowerMultiple_ι_comp_eq_zero_iff]
    intro U r hr x
    rw [map_smul]
    exact smul_smallEtaleInternalHomSmall_eq_zero B S hS F hF 𝓘 M _ n
      (isPowAnnihilated_idealPowerQuotient B S hS F hF 𝓘 n N) U r hr _)

/-- The comparison `internalHomAdicComparison` composed with the projection onto
`𝓗om(M, N) / 𝓘ⁿ 𝓗om(M, N)` is postcomposition with the projection `N ⟶ N / 𝓘ⁿ N`. -/
@[reassoc (attr := simp)]
theorem π_internalHomAdicComparison (n : ℕ) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 n (smallEtaleInternalHomSmall B S hS F hF M N)).ι ≫
        internalHomAdicComparison B S hS F hF 𝓘 M N n =
      internalHomPostcomp B S hS F hF M (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 n N).ι) :=
  cokernel.π_desc _ _ _

/-- The comparisons are compatible with the transition maps. -/
theorem idealPowerQuotientMapOfLE_comp_internalHomAdicComparison {k l : ℕ} (h : k ≤ l) :
    idealPowerQuotientMapOfLE B S hS F hF 𝓘 h (smallEtaleInternalHomSmall B S hS F hF M N) ≫
        internalHomAdicComparison B S hS F hF 𝓘 M N k =
      internalHomAdicComparison B S hS F hF 𝓘 M N l ≫
        internalHomPostcomp B S hS F hF M (idealPowerQuotientMapOfLE B S hS F hF 𝓘 h N) := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE, π_internalHomAdicComparison,
    π_internalHomAdicComparison_assoc, ← internalHomPostcomp_comp, π_comp_idealPowerQuotientMapOfLE]

/-- **The comparison of towers** `(𝓗om(M, N) / 𝓘ⁿ⁺¹)_n ⟶ (𝓗om(M, N / 𝓘ⁿ⁺¹ N))_n`. -/
def internalHomAdicComparisonSystem :
    adicQuotientSystem B S hS F hF 𝓘 (smallEtaleInternalHomSmall B S hS F hF M N) ⟶
      adicQuotientSystem B S hS F hF 𝓘 N ⋙ smallEtaleInternalHomSmallFunctor B S hS F hF M where
  app n := internalHomAdicComparison B S hS F hF 𝓘 M N (n.unop + 1)
  naturality _ _ f := idealPowerQuotientMapOfLE_comp_internalHomAdicComparison B S hS F hF 𝓘 M N
    (Nat.add_le_add_right (leOfHom f.unop) 1)

end AlgebraicGeometry.Space
