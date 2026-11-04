module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
import StacksCore.Tactic.StacksAttribute

/-!
# Degree one continuous group cohomology is the group of continuous cocycles

Let `G` be a topological group and `M` a discrete `G`-module. The group `H ¹(G, M)` of
`continuousGroupCohomology` is the first right derived functor of invariants, so it carries no
description by cocycles by construction. This file supplies the comparison in degree one: if
every locally constant `1`-cocycle `G → M` is a coboundary, then `H ¹(G, M) = 0`.

## Main results

* `Stacks.GroupCohomology.rightDerivedPlusZeroIso`: a left exact functor is naturally isomorphic
  to its zeroth right derived functor.
* `Stacks.GroupCohomology.isZero_rightDerivedPlus_one_of_epi_map_g`: `R ¹F(A) = 0` as soon as `A`
  sits in a short exact sequence with injective middle term on which `F` stays surjective.
* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_one_of_forall_isCoboundary`:
  `H ¹(G, M) = 0` when every locally constant `1`-cocycle with values in `M` is a coboundary.

## Implementation notes

The vanishing criterion is the one half of the standard comparison between the cocycle
description of degree one cohomology and the derived functor description that needs no
acyclicity of the injective objects. Choose an injective embedding `0 → M → J → Q → 0`. The
connecting map `Q ᴳ → H ¹(G, M)` is surjective because `H ¹(G, J) = 0`, and it kills the image of
`J ᴳ`, so `H ¹(G, M) = 0` as soon as `J ᴳ → Q ᴳ` is surjective. Given an invariant `y ∈ Q` lift it
to `x ∈ J`; then `g ↦ g • x - x` takes values in `M`, is locally constant because `J` is discrete
with continuous action, and is a `1`-cocycle. A coboundary `m` for it makes `x - m` invariant and
still lifts `y`.

## References

* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ContinuousCohomology

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.GroupCohomology

/-! ### The zeroth right derived functor of a left exact functor -/

section Derived

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- The right-derived-functor unit read on complexes concentrated in degree zero. -/
noncomputable def zeroUnitAppSingle (F : C ⥤ D) [F.Additive] :
    HomotopyCategory.Plus.singleFunctor C 0 ⋙ F.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor D 0 ⟶
      HomotopyCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.Qh ⋙
        F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D 0 :=
  Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor C 0)
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnit
      (DerivedCategory.Plus.homologyFunctor D 0))

/-- **A left exact functor is its own zeroth right derived functor**, as a natural isomorphism
`F ≅ R ⁰F`. -/
noncomputable def rightDerivedPlusZeroIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    F ≅ F.rightDerivedPlus 0 := by
  have hunit : IsIso (zeroUnitAppSingle F) := by
    have : ∀ X, IsIso ((zeroUnitAppSingle F).app X) :=
      (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
        F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit).2.2.2 inferInstance
    exact NatIso.isIso_of_isIso_app _
  exact
    (Functor.isoWhiskerRight (Functor.mapSingleFunctorCompQhIso F)
      (DerivedCategory.Plus.homologyFunctor D 0) ≪≫
      Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0) ≪≫
      Functor.rightUnitor F).symm ≪≫
    asIso (zeroUnitAppSingle F) ≪≫
    (Functor.isoWhiskerRight (Functor.singleFunctorPlusIsoCompQh 0)
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D 0)).symm

/-- **A vanishing criterion in degree one for a right derived functor.** If `A` is the kernel of
a surjection `J → Q` with `J` injective and `F(J) → F(Q)` is still surjective, then
`R ¹F(A) = 0`: the connecting map `F(Q) → R ¹F(A)` is surjective because `R ¹F(J) = 0`, and it
vanishes because it kills the image of `F(J)`. -/
theorem isZero_rightDerivedPlus_one_of_epi_map_g (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {S : ShortComplex C} (hS : S.ShortExact)
    (hinj : Injective S.X₂) (hg : Epi (F.map S.g)) :
    IsZero ((F.rightDerivedPlus 1).obj S.X₁) := by
  let Δ := Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor F
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure F)
    (Stacks.DerivedIndexing.canonicalδ F) (fun _ _ ↦ rfl)
  have hJ : IsZero ((F.rightDerivedPlus (1 : ℤ)).obj S.X₂) :=
    Functor.isZero_rightDerivedPlus_obj_injective F 1 one_ne_zero S.X₂
  have h1 : (Δ.functor 1).map S.f = 0 := hJ.eq_of_tgt _ _
  have hepi : Epi (Δ.δ hS 0) := Δ.epi_δ_of_map_f_eq_zero hS 0 h1
  have h0' : Epi ((F.rightDerivedPlus (0 : ℤ)).map S.g) := by
    rw [← NatIso.naturality_1 (rightDerivedPlusZeroIso F) S.g]
    infer_instance
  have h0 : Epi ((Δ.functor 0).map S.g) := h0'
  exact (IsZero.of_epi_eq_zero (Δ.δ hS 0) (zero_of_epi_comp _ (Δ.map_g_δ hS 0)) :)

end Derived

/-! ### Degree one continuous group cohomology -/

section Continuous

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

-- `ℤ`-modules are regarded as topological spaces with the discrete topology, which is the
-- convention under which `ContinuousGModule` is formed.
attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat

/-- Taking invariants of a discrete `G`-module is left exact, as a composite of functors
preserving finite limits. -/
lemma preservesFiniteLimits_invariants :
    PreservesFiniteLimits (continuousGModuleInvariants.{u, v} G) := by
  have hdisc := preservesFiniteLimits_ι (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G))
  have hcont := preservesFiniteLimits_ι (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G))
  show PreservesFiniteLimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G)) ⋙
      Rep.ActionToRep ℤ G ⋙ Rep.invariantsFunctor ℤ G ⋙
        forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})
  infer_instance

/-- The action of a product of group elements on a discrete `G`-module is the composite action. -/
private lemma rho_mul_apply {H : Type u} [Group H] (V : Action (ModuleCat.{v} ℤ) H)
    (g₁ g₂ : H) (w : V.V) : (V.ρ (g₁ * g₂)).hom w = (V.ρ g₁).hom ((V.ρ g₂).hom w) := by
  rw [map_mul]; rfl

/-- **A function on `G` constant on the left cosets of the stabiliser of an element of a
discrete `G`-module is locally constant.** The stabiliser is open because the action is
continuous and the module discrete. -/
lemma isLocallyConstant_of_stabilizer {α : Type*} (N : ContinuousGModule.{u, v} G)
    (z : N.obj.obj.V) (φ : G → α)
    (hφ : ∀ g₁ g₂ : G, (N.obj.obj.ρ g₁).hom z = (N.obj.obj.ρ g₂).hom z → φ g₁ = φ g₂) :
    IsLocallyConstant φ := by
  have hone : ∀ w : N.obj.obj.V, (N.obj.obj.ρ 1).hom w = w := by
    intro w
    rw [map_one]; rfl
  intro s
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  have hopen : IsOpen ((fun h : G ↦ g⁻¹ * h) ⁻¹' {k : G | (N.obj.obj.ρ k).hom z = z}) :=
    (isOpen_stabilizer ℤ G N z).preimage (by fun_prop)
  have hmem : g ∈ (fun h : G ↦ g⁻¹ * h) ⁻¹' {k : G | (N.obj.obj.ρ k).hom z = z} := by
    simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel]
    exact hone z
  refine ⟨_, fun h hh ↦ ?_, hopen, hmem⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hh
  have hgh : (N.obj.obj.ρ h).hom z = (N.obj.obj.ρ g).hom z := by
    simpa only [mul_inv_cancel_left, hh] using rho_mul_apply N.obj.obj g (g⁻¹ * h) z
  exact Set.mem_preimage.mpr (by rw [hφ h g hgh]; exact hg)

variable {G}

/-- **Degree one continuous group cohomology vanishes when every continuous `1`-cocycle is a
coboundary.** The cocycle condition is `c(g₁g₂) = g₁ • c(g₂) + c(g₁)` and the coboundary
condition is `c(g) = g • x - x`; `H ¹(G, M)` is the derived functor group of Stacks 04JR. -/
theorem isZero_continuousGroupCohomology_one_of_forall_isCoboundary
    (M : ContinuousGModule.{u, max u v} G)
    (hM : ∀ c : G → M.obj.obj.V, IsLocallyConstant c →
        (∀ g₁ g₂ : G, c (g₁ * g₂) = (M.obj.obj.ρ g₁).hom (c g₂) + c g₁) →
        ∃ x : M.obj.obj.V, ∀ g : G, (M.obj.obj.ρ g).hom x - x = c g) :
    IsZero (continuousGroupCohomology.{u, v} G 1 M) := by
  have : PreservesFiniteLimits (continuousGModuleInvariants.{u, max u v} G) :=
    preservesFiniteLimits_invariants G
  let U := continuousGModuleUnderlying.{u, max u v} G
  let P : InjectivePresentation M := Classical.choice (EnoughInjectives.presentation M)
  have : Injective P.J := P.injective
  have : Mono P.f := P.mono
  let S : ShortComplex (ContinuousGModule.{u, max u v} G) :=
    ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel P.f)) inferInstance inferInstance
  have hSu : (S.map U).ShortExact := hS.map_of_exact U
  let fl : M.obj.obj.V →ₗ[ℤ] P.J.obj.obj.V := P.f.hom.hom.hom.hom
  let gl : P.J.obj.obj.V →ₗ[ℤ] (cokernel P.f).obj.obj.V :=
    (cokernel.π P.f).hom.hom.hom.hom
  have hgsurj : Function.Surjective gl := hSu.moduleCat_surjective_g
  have hfinj : Function.Injective fl := hSu.moduleCat_injective_f
  have hexact : ∀ z : P.J.obj.obj.V, gl z = 0 → ∃ m : M.obj.obj.V, fl m = z :=
    (ShortComplex.moduleCat_exact_iff _).mp hSu.exact
  have hgfl : ∀ m : M.obj.obj.V, gl (fl m) = 0 :=
    fun m ↦ ShortComplex.moduleCat_zero_apply (S.map U) m
  have hfeq : ∀ (g : G) (m : M.obj.obj.V),
      fl ((M.obj.obj.ρ g).hom m) = (P.J.obj.obj.ρ g).hom (fl m) :=
    fun g m ↦ ConcreteCategory.congr_hom (P.f.hom.hom.comm g) m
  have hgeq : ∀ (g : G) (z : P.J.obj.obj.V),
      gl ((P.J.obj.obj.ρ g).hom z) = ((cokernel P.f).obj.obj.ρ g).hom (gl z) :=
    fun g z ↦ ConcreteCategory.congr_hom ((cokernel.π P.f).hom.hom.comm g) z
  refine isZero_rightDerivedPlus_one_of_epi_map_g
    (continuousGModuleInvariants.{u, max u v} G) hS P.injective ?_
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  obtain ⟨x, hx⟩ := hgsurj y.1
  have hyinv : ∀ g : G, ((cokernel P.f).obj.obj.ρ g).hom y.1 = y.1 := fun g ↦ y.2 g
  have hker : ∀ g : G, ∃ m : M.obj.obj.V, fl m = (P.J.obj.obj.ρ g).hom x - x := by
    intro g
    refine hexact _ ?_
    rw [map_sub, hgeq, hx, hyinv]
    exact sub_self _
  choose c hc using hker
  have hcoc : ∀ g₁ g₂ : G, c (g₁ * g₂) = (M.obj.obj.ρ g₁).hom (c g₂) + c g₁ := by
    intro g₁ g₂
    refine hfinj ?_
    simp only [hc, map_add, hfeq, map_sub, rho_mul_apply P.J.obj.obj]
    abel
  have hcloc : IsLocallyConstant c :=
    isLocallyConstant_of_stabilizer G P.J x c fun g₁ g₂ h ↦ hfinj (by rw [hc, hc, h])
  obtain ⟨m₀, hm₀⟩ := hM c hcloc hcoc
  have hfix : ∀ g : G, (P.J.obj.obj.ρ g).hom (x - fl m₀) = x - fl m₀ := by
    intro g
    have hmg : (M.obj.obj.ρ g).hom m₀ = c g + m₀ := by rw [← hm₀ g]; abel
    rw [map_sub, ← hfeq, hmg, map_add, hc]
    abel
  refine ⟨⟨x - fl m₀, hfix⟩, Subtype.ext ?_⟩
  show gl (x - fl m₀) = y.1
  rw [map_sub, hgfl, hx]
  exact sub_zero _

end Continuous

end Stacks.GroupCohomology

end
