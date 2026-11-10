module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingCoinduction
public import StacksFrontier.Algebra.Module.Injective.ZModPrimePower
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Projective `ℤ/pᵐ[G]`-modules are injective

Let `G` be a finite group and `R = ℤ/pᵐℤ[G]`.  A projective `R`-module `P` is injective: it is
flat over `ℤ/pᵐℤ` (a retract of a free `R`-module, which is free over `ℤ/pᵐℤ`), hence injective
over the self-injective ring `ℤ/pᵐℤ` (Baer's criterion); coinduction carries it to an injective
`R`-module, and `P` is a retract of its coinduced module, the counit of Frobenius reciprocity
being surjective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Stacks.ZModPrimePower

variable {p m : ℕ}

/-- Finitely supported functions with values in a module with the exactness property have it. -/
theorem isPowExact_finsupp_of (X : Type*) {M : Type*} [AddCommGroup M] (hM : IsPowExact p m M) :
    IsPowExact p m (X →₀ M) := by
  classical
  intro a ha x hx
  let c : M → M := fun r =>
    if h : p ^ a • r = 0 then (if r = 0 then 0 else (hM a ha r h).choose) else 0
  have hc0 : c 0 = 0 := by simp [c]
  refine ⟨Finsupp.mapRange c hc0 x, ?_⟩
  ext i
  have hi : p ^ a • x i = 0 := by simpa using congrArg (fun z => z i) hx
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, c, dite_eq_left hi]
  by_cases h0 : x i = 0
  · simp [h0]
  · rw [ite_eq_right h0]
    exact (hM a ha (x i) hi).choose_spec

end Stacks.ZModPrimePower

namespace Stacks.EtaleCohomology

open Stacks.ZModPrimePower

variable {p m : ℕ} [Fact p.Prime] (G : Type) [Group G]

omit [Group G] in
/-- `ℤ/pᵐℤ[G]` has the exactness property: it is free over `ℤ/pᵐℤ`. -/
theorem isPowExact_groupRing : IsPowExact p m (MonoidAlgebra (ZMod (p ^ m)) G) :=
  IsPowExact.of_addEquiv MonoidAlgebra.coeffAddEquiv.symm (isPowExact_finsupp G)

/-- **A projective `ℤ/pᵐℤ[G]`-module has the exactness property.** -/
theorem isPowExact_of_projective_groupRing (P : Type*) [AddCommGroup P]
    [Module (MonoidAlgebra (ZMod (p ^ m)) G) P]
    [Module.Projective (MonoidAlgebra (ZMod (p ^ m)) G) P] : IsPowExact p m P := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1
    (inferInstance : Module.Projective (MonoidAlgebra (ZMod (p ^ m)) G) P)
  have hF := isPowExact_finsupp_of (p := p) (m := m) P (isPowExact_groupRing G)
  intro a ha x hx
  obtain ⟨y, hy⟩ := hF a ha (s x) (by rw [← map_nsmul, hx, map_zero])
  refine ⟨Finsupp.linearCombination _ id y, ?_⟩
  rw [← map_nsmul, hy]
  exact congrArg (fun f => f x) hs

variable [Finite G]

/-- **Projective `ℤ/pᵐℤ[G]`-modules are injective.** -/
theorem injective_of_projective_groupRing (P : ModuleCat.{v} (MonoidAlgebra (ZMod (p ^ m)) G))
    [Projective P] : Injective P := by
  have := Fintype.ofFinite G
  let k₀ := ZMod (p ^ m)
  let res := ModuleCat.restrictScalars.{v} (groupRingScalars k₀ G)
  have hproj : Module.Projective (MonoidAlgebra k₀ G) P :=
    (IsProjective.iff_projective P).2 inferInstance
  have hpow : IsPowExact p m (res.obj P) := isPowExact_of_projective_groupRing G P
  have hbaer : Module.Baer k₀ (res.obj P) := baer_of_isPowExact hpow
  have hinj : Injective (res.obj P) :=
    (Module.injective_iff_injective_object k₀ (res.obj P)).1 hbaer.injective
  have : res.IsRightAdjoint :=
    (groupRingCoinductionAdj.{v} k₀ G).isRightAdjoint
  have hinj' : Injective ((groupRingCoinduction k₀ G).obj (res.obj P)) :=
    (ModuleCat.restrictCoextendScalarsAdj.{v} (groupRingScalars k₀ G)).map_injective _ hinj
  let ε := (groupRingCoinductionAdj.{v} k₀ G).counit.app P
  have hε : Epi ε := by
    rw [ModuleCat.epi_iff_surjective]
    exact fun x => ⟨groupRingCoinductionDelta (res.obj P) x, groupRingCoinductionLift_delta (𝟙 _) x⟩
  have r : Retract P ((groupRingCoinduction k₀ G).obj (res.obj P)) :=
    ⟨Projective.factorThru (𝟙 P) ε, ε, Projective.factorThru_comp _ _⟩
  exact @Retract.injective _ _ _ _ r hinj'

end Stacks.EtaleCohomology

end
