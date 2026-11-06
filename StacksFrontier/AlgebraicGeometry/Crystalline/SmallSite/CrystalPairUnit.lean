module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairEquivalence07JH
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFunctor07JG

/-!
# The pair of the structure sheaf under the functor of [Stacks, Tag 07JG]

The functor `...SmallSite.crystalPairFunctor` of [Stacks, Lemma 60.17.3, Tag 07JG] attaches to a
crystal `ℱ` the module `M = lim_e Γ(T_e, ℱ)` over `D` with the connection read off the Taylor
expansion of `ℱ`.  For the structure sheaf `ℱ = 𝒪_{X/S}` this is the pair `(D, d)`: the module
`lim_e Γ(T_e, 𝒪)` is free of rank one on the unit section, `r ↦ r · 1` being an isomorphism
`D ≅ M` because `D` is the inverse limit of the section rings of the levels; the Taylor
coefficients of `1` vanish in positive degree, so `∇ 1 = 0`; and by the Leibniz rule
`∇ (r · 1) = 1 ⊗ d r`.

## Main definitions

* `...SmallSite.pairUnitOne` — the unit section `1 ∈ lim_e Γ(T_e, 𝒪)`.
* `...SmallSite.pairUnitEquiv` — the `D`-linear isomorphism `D ≅ lim_e Γ(T_e, 𝒪)`, `r ↦ r · 1`.

## Main results

* `...SmallSite.crystalTheta_unit_one` — the Taylor coefficients of `1` vanish in positive
  degree.
* `...SmallSite.pairConnection_unit_one` — `∇ 1 = 0`.
* `...SmallSite.pairConnection_unit_pairUnitEquiv` — `∇ (r · 1) = 1 ⊗ d r`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **The unit section `1 ∈ lim_e Γ(T_e, 𝒪)`** of the structure sheaf over the system of
thickenings of [Stacks, Tag 07JN]. -/
def pairUnitOne : wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌ :=
  wholeSpaceSectionsMk hp (quasiCoherentCrystalUnit S) (fun _ ↦ (1 : (structureSheaf S).obj.obj _))
    (fun _ ↦ map_one ((structureSheaf S).obj.map _).hom)

/-- The level components of `r · 1` are the scalars `levelSectionsScalars`. -/
theorem wholeSpaceSectionsVal_smul_pairUnitOne (r : pairRing hp) (e : ℕ) :
    wholeSpaceSectionsVal hp (quasiCoherentCrystalUnit S) (r • pairUnitOne hp) e =
      levelSectionsScalars hp ⦋0⦌ e r := by
  refine (wholeSpaceSectionsVal_smul hp (quasiCoherentCrystalUnit S) (n := ⦋0⦌) r
    (pairUnitOne hp) e).trans ?_
  exact mul_one (levelSectionsScalars hp ⦋0⦌ e r)

/-- **The module `lim_e Γ(T_e, 𝒪)` of the structure sheaf is free of rank one over `D` on the unit
section**: `r ↦ r · 1` is a `D`-linear isomorphism, `D` being the inverse limit of the section
rings of the levels (`...SmallSite.envelopeLevelRingLimitEquiv`). -/
def pairUnitEquiv :
    pairRing hp ≃ₗ[pairRing hp] wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌ :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (pairRing hp) _ (pairUnitOne hp)) <| by
    refine ⟨fun r s hrs ↦ ?_, fun m ↦ ?_⟩
    · have hval : ∀ e, levelSectionsScalars hp ⦋0⦌ e r = levelSectionsScalars hp ⦋0⦌ e s :=
        fun e ↦ by
          rw [← wholeSpaceSectionsVal_smul_pairUnitOne, ← wholeSpaceSectionsVal_smul_pairUnitOne]
          exact congrArg (fun m ↦ wholeSpaceSectionsVal hp _ m e) hrs
      have hL : envelopeLevelRingLimitEquiv hp 0 ((wholeSpaceSystemEnvelopeRingEquiv hp 0).symm r) =
          envelopeLevelRingLimitEquiv hp 0 ((wholeSpaceSystemEnvelopeRingEquiv hp 0).symm s) :=
        Subtype.ext (funext fun e ↦
          (levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e r).symm.trans
            ((hval e).trans (levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e s)))
      exact (wholeSpaceSystemEnvelopeRingEquiv hp 0).symm.injective
        ((envelopeLevelRingLimitEquiv hp 0).injective hL)
    · let a : ↥(levelRingLimit S ((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))) :=
        ⟨fun e ↦ wholeSpaceSectionsVal hp (quasiCoherentCrystalUnit S) m e,
          fun h ↦ wholeSpaceSectionsVal_restrict hp (quasiCoherentCrystalUnit S) m h⟩
      refine ⟨wholeSpaceSystemEnvelopeRingEquiv hp 0 ((envelopeLevelRingLimitEquiv hp 0).symm a),
        wholeSpaceSectionsVal_injective hp _ fun e ↦ ?_⟩
      refine (wholeSpaceSectionsVal_smul_pairUnitOne hp _ e).trans ?_
      refine (levelSectionsScalars_eq_envelopeLevelRingLimitEquiv hp ⦋0⦌ e _).trans ?_
      have h1 : (wholeSpaceSystemEnvelopeRingEquiv hp 0).symm
          (wholeSpaceSystemEnvelopeRingEquiv hp 0 ((envelopeLevelRingLimitEquiv hp 0).symm a)) =
          (envelopeLevelRingLimitEquiv hp 0).symm a := RingEquiv.symm_apply_apply _ _
      have h2 : envelopeLevelRingLimitEquiv hp 0 ((envelopeLevelRingLimitEquiv hp 0).symm a) = a :=
        RingEquiv.apply_symm_apply _ _
      exact (congrArg (fun x ↦ (envelopeLevelRingLimitEquiv hp 0 x).val e) h1).trans
        (congrArg (fun x ↦ x.val e) h2)

/-- The isomorphism `pairUnitEquiv` sends `r` to `r · 1`. -/
@[simp] theorem pairUnitEquiv_apply (r : pairRing hp) :
    pairUnitEquiv hp r = r • pairUnitOne hp := rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- Restricting the unit section of the structure sheaf along a morphism of `Cris(X/S)` gives the
unit section. -/
theorem crysRestrict_unit_one {A B : CrystallineThickening S} (k : A ⟶ B) :
    @Eq ((structureSheaf S).obj.obj (op A) : Type u)
      (crysRestrict (quasiCoherentCrystalUnit S).obj k (1 : (structureSheaf S).obj.obj (op B))) 1 :=
  map_one ((structureSheaf S).obj.map k.op).hom

/-- **The Taylor coefficients of the unit section vanish in positive degree**: `θ_K(1) = 0` for
`K ≠ 0`, since `p₁^* 1 = 1 = ξ^{[0]} · p₀^* 1`. -/
theorem crystalTheta_unit_one {K : wholeSpaceIndex S hp →₀ ℕ} (hK : K ≠ 0) :
    crystalTheta hp (quasiCoherentCrystalUnit S) K (pairUnitOne hp) = 0 := by
  refine wholeSpaceSectionsVal_injective hp _ fun e ↦ ?_
  rw [wholeSpaceSectionsVal_crystalTheta]
  have hc : (levelTaylorExpansion hp (quasiCoherentCrystalUnit S) e).coeffs
      (wholeSpaceSectionsVal hp _ (pairUnitOne hp) e) =
        Finsupp.single 0 (wholeSpaceSectionsVal hp _ (pairUnitOne hp) e) := by
    refine TaylorExpansion.coeffs_eq_of_taylorSum _ ?_
    rw [taylorSum_single]
    show levelTaylorMonomial hp e 0 • crysRestrict (quasiCoherentCrystalUnit S).obj _
        (1 : (structureSheaf S).obj.obj _) =
      crysRestrict (quasiCoherentCrystalUnit S).obj _ (1 : (structureSheaf S).obj.obj _)
    rw [crysRestrict_unit_one, crysRestrict_unit_one, levelTaylorMonomial,
      envelopeTaylorMonomial_zero, map_one]
    exact one_mul (1 : (structureSheaf S).obj.obj (op (levelObj hp 1 e)))
  rw [levelTheta, TaylorExpansion.theta_apply, hc, Finsupp.single_eq_of_ne hK]
  rfl

/-- **`∇ 1 = 0`** for the connection of the pair of the structure sheaf: the coordinate operators
`-θ_c` of the connection kill the unit section, and the completed tensor product is `p`-adically
separated. -/
theorem pairConnection_unit_one :
    pairConnection hp (quasiCoherentCrystalUnit S) (pairUnitOne hp) = 0 := by
  let := completedTensorTopology S.p (pairRing hp) (pairForms hp)
    (wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌)
  have := t2Space_adicModuleTopology (DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p)
    (CompletedTensor S.p (pairRing hp) (pairForms hp)
      (wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌)) inferInstance
  have h := isCoordinateExpansion_pairConnection hp (quasiCoherentCrystalUnit S) (pairUnitOne hp)
  have hc : ∀ c : (wholeSpaceIndex S hp),
      crystalTheta hp (quasiCoherentCrystalUnit S) (Finsupp.single c 1) (pairUnitOne hp) = 0 :=
    fun c ↦ crystalTheta_unit_one hp (Finsupp.single_ne_zero.mpr one_ne_zero)
  have h0 : HasSum (fun c : (wholeSpaceIndex S hp) ↦
      toCompletedTensor S.p (pairRing hp) (pairForms hp)
        (wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌)
        ((-crystalTheta hp (quasiCoherentCrystalUnit S) (Finsupp.single c 1) (pairUnitOne hp)) ⊗ₜ
          pairDx hp c)) 0 := by
    simpa only [hc, neg_zero, TensorProduct.zero_tmul, map_zero] using hasSum_zero
  exact h.unique h0

/-- **The connection of the pair of the structure sheaf is `∇ (r · 1) = 1 ⊗ d r`**: the Leibniz
rule and `∇ 1 = 0`. -/
theorem pairConnection_unit_pairUnitEquiv (r : pairRing hp) :
    pairConnection hp (quasiCoherentCrystalUnit S) (pairUnitEquiv hp r) =
      toCompletedTensor S.p (pairRing hp) (pairForms hp)
        (wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌)
        (pairUnitOne hp ⊗ₜ[pairRing hp] derivationFun ((affineSituation S hp).A : Type u)
          (pairRing hp) _ (pairForms hp) (pairDerivation hp) r) := by
  have h := (pairConnection hp (quasiCoherentCrystalUnit S)).leibniz r (pairUnitOne hp)
  have h1 := pairConnection_unit_one hp
  have h2 : r • pairConnection hp (quasiCoherentCrystalUnit S) (pairUnitOne hp) = 0 := by
    rw [h1]
    exact smul_zero r
  exact h.trans ((congrArg (· + _) h2).trans (zero_add _))

end Crystalline.GlobalCrystallineSituation.SmallSite

end
