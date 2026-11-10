module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeOneCocycles

/-!
# A bound on cocycles bounds degree one continuous group cohomology

If `e` times every locally constant `1`-cocycle of a topological group `G` with values in a
discrete `G`-module `M` is a coboundary, then `e` kills the derived functor group `H ¹(G, M)` of
Stacks 04JR. This is the bounded form of
`Stacks.GroupCohomology.isZero_continuousGroupCohomology_one_of_forall_isCoboundary` (the case
`e = 1`), proved the same way: for an injective embedding `0 → M → J → Q → 0` the connecting map
`Q ᴳ → H ¹(G, M)` is surjective and kills the image of `J ᴳ`, and `e • Q ᴳ` lies in that image.

It is how a bound on continuous cocycles of an inertia group
(`Stacks.EtaleCohomology.InertiaLevelsKilledBy`) bounds the étale cohomology of the spectrum of
the fraction field of a strict henselization, through Stacks 03QU.

## Main results

* `Stacks.GroupCohomology.nsmul_id_rightDerivedPlus_one_eq_zero`.
* `Stacks.GroupCohomology.nsmul_id_continuousGroupCohomology_one_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ContinuousCohomology

universe u v w

namespace Stacks.GroupCohomology

section Derived

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
  [HasDerivedCategory AddCommGrpCat.{w}]

/-- **A bound in degree one for a right derived functor to abelian groups.** If `A` is the kernel
of a surjection `J → Q` with `J` injective and `e • F(Q)` lies in the image of `F(J)`, then `e`
kills `R ¹F(A)`. -/
theorem nsmul_id_rightDerivedPlus_one_eq_zero (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    [PreservesFiniteLimits F] {S : ShortComplex C} (hS : S.ShortExact)
    (hinj : Injective S.X₂) (e : ℕ)
    (hg : ∀ y : F.obj S.X₃, ∃ x : F.obj S.X₂, (F.map S.g).hom x = e • y) :
    e • 𝟙 ((F.rightDerivedPlus 1).obj S.X₁) = 0 := by
  have := hinj
  let Δ := Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor F
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure F)
    (Stacks.DerivedIndexing.canonicalδ F) (fun _ _ ↦ rfl)
  have h1 : (Δ.functor 1).map S.f = 0 :=
    (Functor.isZero_rightDerivedPlus_obj_injective F 1 one_ne_zero S.X₂).eq_of_tgt _ _
  have hsurj : Function.Surjective (Δ.δ hS 0).hom :=
    (AddCommGrpCat.epi_iff_surjective _).1 (Δ.epi_δ_of_map_f_eq_zero hS 0 h1)
  let iso := rightDerivedPlusZeroIso F
  have hnat : ∀ x : F.obj S.X₂, (iso.hom.app S.X₃).hom ((F.map S.g).hom x) =
      ((F.rightDerivedPlus 0).map S.g).hom ((iso.hom.app S.X₂).hom x) := fun x =>
    ConcreteCategory.congr_hom (iso.hom.naturality S.g) x
  suffices h : e • 𝟙 ((Δ.functor (0 + 1)).obj S.X₁) = 0 from h
  ext z
  obtain ⟨y', rfl⟩ := hsurj z
  obtain ⟨x, hx⟩ := hg ((iso.inv.app S.X₃).hom y')
  have hy' : e • y' = ((Δ.functor 0).map S.g).hom ((iso.hom.app S.X₂).hom x) := by
    change e • y' = ((F.rightDerivedPlus 0).map S.g).hom ((iso.hom.app S.X₂).hom x)
    rw [← hnat, hx, map_nsmul]
    congr 1
    exact (ConcreteCategory.congr_hom (iso.inv_hom_id_app S.X₃) y').symm
  have hz : e • (Δ.δ hS 0).hom y' = 0 := by
    rw [← map_nsmul, hy']
    exact ConcreteCategory.congr_hom (Δ.map_g_δ hS 0) ((iso.hom.app S.X₂).hom x)
  simpa using hz

end Derived

section Continuous

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  HasDerivedCategory.standard

/-- **A bound on continuous cocycles bounds `H ¹(G, M)`.** If `e` times every locally constant
`1`-cocycle `c : G → M` (`c(g₁g₂) = g₁ • c(g₂) + c(g₁)`) is a coboundary `g ↦ g • x - x`, then
`e` kills the derived functor group `H ¹(G, M)` of Stacks 04JR. The standard model
`HasDerivedCategory.standard` is used because `continuousGroupCohomology` is defined there. -/
theorem nsmul_id_continuousGroupCohomology_one_eq_zero
    (M : ContinuousGModule.{u, max u v} G) (e : ℕ)
    (hM : ∀ c : G → M.obj.obj.V, IsLocallyConstant c →
        (∀ g₁ g₂ : G, c (g₁ * g₂) = (M.obj.obj.ρ g₁).asHom.hom (c g₂) + c g₁) →
        ∃ x : M.obj.obj.V, ∀ g : G, (M.obj.obj.ρ g).asHom.hom x - x = e • c g) :
    e • 𝟙 (continuousGroupCohomology.{u, v} G 1 M) = 0 := by
  let : PreservesFiniteLimits (continuousGModuleInvariants.{u, max u v} G) :=
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
      fl ((M.obj.obj.ρ g).asHom.hom m) = (P.J.obj.obj.ρ g).asHom.hom (fl m) :=
    fun g m ↦ ConcreteCategory.congr_hom (P.f.hom.hom.comm g) m
  have hgeq : ∀ (g : G) (z : P.J.obj.obj.V),
      gl ((P.J.obj.obj.ρ g).asHom.hom z) = ((cokernel P.f).obj.obj.ρ g).asHom.hom (gl z) :=
    fun g z ↦ ConcreteCategory.congr_hom ((cokernel.π P.f).hom.hom.comm g) z
  have hmul : ∀ (g₁ g₂ : G) (z : P.J.obj.obj.V), (P.J.obj.obj.ρ (g₁ * g₂)).asHom.hom z =
      (P.J.obj.obj.ρ g₁).asHom.hom ((P.J.obj.obj.ρ g₂).asHom.hom z) := by
    intro g₁ g₂ z
    rw [map_mul]
    rfl
  refine nsmul_id_rightDerivedPlus_one_eq_zero
    (continuousGModuleInvariants.{u, max u v} G) hS P.injective e fun y => ?_
  obtain ⟨x, hx⟩ := hgsurj y.1
  have hyinv : ∀ g : G, ((cokernel P.f).obj.obj.ρ g).asHom.hom y.1 = y.1 := y.2
  have hker : ∀ g : G, ∃ m : M.obj.obj.V, fl m = (P.J.obj.obj.ρ g).asHom.hom x - x :=
    fun g ↦ hexact _ (by rw [map_sub, hgeq, hx, hyinv]; exact sub_self _)
  choose c hc using hker
  have hcoc : ∀ g₁ g₂ : G, c (g₁ * g₂) = (M.obj.obj.ρ g₁).asHom.hom (c g₂) + c g₁ := by
    intro g₁ g₂
    refine hfinj ?_
    simp only [hc, map_add, hfeq, map_sub, hmul]
    abel
  have hcloc : IsLocallyConstant c :=
    isLocallyConstant_of_stabilizer G P.J x c fun g₁ g₂ h ↦ hfinj (by rw [hc, hc, h])
  obtain ⟨m₀, hm₀⟩ := hM c hcloc hcoc
  -- `e • x - m₀` is invariant and lifts `e • y`
  have hfix : ∀ g : G, (P.J.obj.obj.ρ g).asHom.hom (e • x - fl m₀) = e • x - fl m₀ := by
    intro g
    have hmg : (M.obj.obj.ρ g).asHom.hom m₀ = e • c g + m₀ := by rw [← hm₀ g]; abel
    rw [map_sub, ← hfeq, hmg, map_add, map_nsmul, map_nsmul, hc, smul_sub]
    abel
  refine ⟨⟨e • x - fl m₀, hfix⟩, ?_⟩
  apply Subtype.ext
  change gl (e • x - fl m₀) = (e • y).1
  rw [map_sub, hgfl, map_nsmul, hx, sub_zero]
  rfl

end Continuous

end Stacks.GroupCohomology

end
