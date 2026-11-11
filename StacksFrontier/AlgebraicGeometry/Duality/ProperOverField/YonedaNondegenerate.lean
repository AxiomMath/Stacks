module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsHomUnit

/-!
# Duality as a nondegenerate Yoneda pairing

Let `f : X ⟶ Spec k` be proper, with relative dualizing complex `ω_X^• = a(𝒪_{Spec k})`
([Stacks, Tag 0FVV]). For `M` in `D_QCoh(𝒪_X)`, every nonzero morphism `𝒪_X[0] ⟶ M` composes
nontrivially with some morphism `M ⟶ ω_X^•`. That is, the Yoneda pairing

`Hom(𝒪_X[0], M) × Hom(M, ω_X^•) ⟶ Hom(𝒪_X[0], ω_X^•),  (y, α) ↦ y ≫ α`

is nondegenerate in `y`. This is part (5) of [Stacks, Tag 0FVV] in degree zero, read through
`Hom_{D(𝒪_X)}(𝒪_X[0], M) = H⁰(X, M)` and the naturality of the duality pairing.

For a smooth proper surface with `ω_X ≅ 𝒪_X` and `M = Ω_{X/k}[1]`, `y` is a class in `H¹(X, Ω)`
and `α ∈ Ext¹(Ω, ω_X)`. So every nonzero `c₁(L) ∈ H¹(X, Ω)` has a nonzero Yoneda product
with some extension class of `Ω` by `ω_X ≅ 𝒪_X` ([Stacks, Tag 0D1R]).

## Main results

* `Stacks.Duality.bijective_homToHomology_derivedGlobalSectionsOver`:
  `Hom_{D(𝒪_X)}(𝒪_X[0], M) = H⁰(X, M)` in the derived-category model of the duality files.
* `Stacks.Duality.exists_comp_ne_zero_of_ne_zero`: **the Yoneda pairing against `ω_X^•` is
  nondegenerate**.

## References

* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

-- The locally small derived-category models of the duality files (see
-- `StacksFrontier.Homology.DerivedCategory.LocallySmall`).
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.CorepresentedRightDerived

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `𝒪_X[0]`, as the object of `D(𝒪_X)` out of which `homToHomology` is defined. -/
abbrev structureSheafSingle : DerivedCategory X.Modules :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
    (single₀ (SheafOfModules.unit X.ringCatSheaf)))

/-- **`Hom_{D(𝒪_X)}(𝒪_X[0], M) = H⁰(X, M)`**: `x ↦ H⁰(RΓ x)(1)` is bijective. -/
theorem bijective_homToHomology_derivedGlobalSectionsOver (M : DerivedCategory X.Modules) :
    Function.Bijective (homToHomology (globalSectionsOver f)
      (SheafOfModules.unit X.ringCatSheaf) (globalSectionsOverOne f) (derivedGlobalSectionsOver f)
      (derivedGlobalSectionsOverUnit f) M) :=
  bijective_homToHomology _ _ _ _ _ (bijective_globalSectionsOverOne_comp f)
    (fun I hI =>
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
        (homotopyGlobalSectionsOver f) (Scheme.Modules.exists_quasiIso_isKInjective X)).2
          DerivedCategory.Qh _ (derivedGlobalSectionsOverUnit f) I hI)
    (Scheme.Modules.exists_quasiIso_isKInjective X) M

variable [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- **The Yoneda pairing against the dualizing complex is nondegenerate.** For `M` in
`D_QCoh(𝒪_X)` and a nonzero `y : 𝒪_X[0] ⟶ M`, there is `α ∈ Ext⁰(M, ω_X^•)` with
`y ≫ α ≠ 0`. -/
theorem exists_comp_ne_zero_of_ne_zero (M : quasiCoherentDerivedCategory X)
    (y : structureSheafSingle (X := X) ⟶ M.obj) (hy : y ≠ 0) :
    ∃ α : DerivedCategory.Ext M.obj (ωX).obj 0, y ≫ α ≠ 0 := by
  let H := homToHomology (globalSectionsOver f) (SheafOfModules.unit X.ringCatSheaf)
    (globalSectionsOverOne f) (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
  have hH0 : ∀ N : DerivedCategory X.Modules, H N 0 = 0 := fun N => by
    simp [H, homToHomology]
  -- the class `v = H⁰(RΓ y)(1)` is nonzero
  have hv : (H M.obj y).hom 1 ≠ 0 := by
    intro hv
    have hz : H M.obj y = 0 := ModuleCat.hom_ext (LinearMap.ext_ring (by simpa using hv))
    exact hy ((bijective_homToHomology_derivedGlobalSectionsOver f M.obj).1
      (hz.trans (hH0 M.obj).symm))
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k _, φ ((H M.obj y).hom 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff k _).1 h)
  obtain ⟨α, hα⟩ := (bijective_dualityPairing_zero f M).2 (ModuleCat.ofHom φ)
  refine ⟨α, fun h0 => hφ ?_⟩
  have hzero : dualityPairing f structureSheafSingle 0 0 = 0 := by
    let := Scheme.linearOver f
    have h := (dualityLinearMap f (structureSheafSingle (X := X)) 0).map_zero
    rw [dualityLinearMap_apply] at h
    exact ModuleCat.hom_ext h
  have h2 : H M.obj y ≫ dualityPairing f M.obj 0 α = 0 := by
    have e1 : H M.obj y ≫ dualityPairing f M.obj 0 α =
        unitDerived (globalSectionsOver f) (SheafOfModules.unit X.ringCatSheaf)
          (globalSectionsOverOne f) (derivedGlobalSectionsOver f)
          (derivedGlobalSectionsOverUnit f) ≫
          dualityPairing f structureSheafSingle 0 (y ≫ α) := by
      rw [dualityPairing_comp]
      simp only [H, homToHomology, Category.assoc]
      rfl
    rw [e1, h0, hzero, Limits.comp_zero]
  have h3 := congrArg (fun g => g.hom (1 : k)) h2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h3
  rw [hα] at h3
  exact h3

end Stacks.Duality

end
