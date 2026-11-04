module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSecondCohomologyRightExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian

/-!
# Injectivity of `ψ_N` descends along epimorphisms

`ψ_N : H²(C, j_!ℱ_N) ⟶ N_π` is natural in `N` and surjective for every `N`, and both
`N ↦ H²(C, j_!ℱ_N)` and `N ↦ N_π` are right exact.  So if `p : Q ⟶ N` is an epimorphism and
`ψ_Q` is injective, then `ψ_N` is injective: the five-lemma step of the proof of Tag 03VK, where
`Q` is a coinduced module whose `H²` is computed on a finite étale cover.

## Main results

* `Stacks.EtaleCohomology.exists_finiteTypeContinuousModuleCoinvariantsMap_kernel_eq` — the
  coinvariants are right exact: for an epimorphism `p : Q ⟶ N` every element of `Q_G` killed
  by `p` comes from `(ker p)_G`.
* `Stacks.EtaleCohomology.injective_curveRepresentationCoinvariantsMap_of_epi` — the descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

section Coinvariants

variable (Λ : Type) [Ring Λ] [Finite Λ] {G : Type (u + 1)} [Group G] [TopologicalSpace G]

/-- **The coinvariants are right exact**: for an epimorphism `p : Q ⟶ N` of finite `Λ`-modules
with continuous `G`-action, an element of `Q_G` mapping to `0` in `N_G` comes from `(ker p)_G`. -/
theorem exists_finiteTypeContinuousModuleCoinvariantsMap_kernel_eq
    {Q N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} (p : Q ⟶ N) [Epi p]
    (z : Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ G Q))
    (hz : finiteTypeContinuousModuleCoinvariantsMap Λ G p z = 0) :
    ∃ w, finiteTypeContinuousModuleCoinvariantsMap Λ G (kernel.ι p) w = z := by
  have h1 := preservesFiniteLimits_finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ G
  have h2 := preservesFiniteColimits_finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ G
  have h3 := preservesFiniteLimits_continuousModuleToModuleCat.{0, u + 1, u + 1} Λ G
  have h4 := preservesFiniteColimits_continuousModuleToModuleCat.{0, u + 1, u + 1} Λ G
  let Φ := finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ G ⋙
    continuousModuleToModuleCat.{0, u + 1, u + 1} Λ G
  have hsurj : Function.Surjective p.hom.hom.hom.hom.hom :=
    (ModuleCat.epi_iff_surjective (Φ.map p)).1 inferInstance
  have hex : ∀ x, p.hom.hom.hom.hom.hom x = 0 → ∃ w, (kernel.ι p).hom.hom.hom.hom.hom w = x :=
    (ShortComplex.moduleCat_exact_iff _).1 ((ShortComplex.exact_kernel p).map Φ)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  have hpx : p.hom.hom.hom.hom.hom x ∈
      Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ G N) :=
    (Submodule.Quotient.mk_eq_zero _).1 hz
  have hle : Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ G N) ≤
      (Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ G Q)).map
        p.hom.hom.hom.hom.hom := by
    rw [Stacks.Trace.coinvariantsKer, Submodule.span_le]
    rintro _ ⟨⟨g, n⟩, rfl⟩
    obtain ⟨x₀, rfl⟩ := hsurj n
    refine ⟨finiteTypeContinuousModuleRepresentation Λ G Q g x₀ - x₀,
      Submodule.subset_span ⟨(g, x₀), rfl⟩, ?_⟩
    simp only [map_sub, finiteTypeContinuousModule_hom_comm]
  obtain ⟨x₁, hx₁, hpx₁⟩ := hle hpx
  obtain ⟨w, hw⟩ := hex (x - x₁) (by rw [map_sub, hpx₁, sub_self])
  refine ⟨Stacks.Trace.coinvariantsMk _ w, ?_⟩
  rw [finiteTypeContinuousModuleCoinvariantsMap_mk, hw]
  exact (Submodule.Quotient.eq _).2 (by simpa using hx₁)

end Coinvariants

/-- **The five-lemma chase for `ψ`**, in linear algebra: `ψ_N ∘ T(p) = p_* ∘ ψ_Q`,
`ψ_Q ∘ T(ι) = ι_* ∘ ψ_K`, `T(p)` surjective, `T(p) ∘ T(ι) = 0`, `ψ_K` surjective,
`ker p_* ⊆ im ι_*` and `ψ_Q` injective give `ψ_N` injective. -/
theorem injective_of_surjective_of_comp_eq_zero_of_naturality {R : Type*} [Ring R]
    {TK TQ TN CK CQ CN : Type*} [AddCommGroup TK] [AddCommGroup TQ] [AddCommGroup TN]
    [AddCommGroup CK] [AddCommGroup CQ] [AddCommGroup CN] [Module R TK] [Module R TQ]
    [Module R TN] [Module R CK] [Module R CQ] [Module R CN]
    {Tp : TQ →ₗ[R] TN} {Tι : TK →ₗ[R] TQ} {cp : CQ →ₗ[R] CN} {cι : CK →ₗ[R] CQ}
    {ψN : TN →ₗ[R] CN} {ψQ : TQ →ₗ[R] CQ} {ψK : TK →ₗ[R] CK}
    (hp : ψN ∘ₗ Tp = cp ∘ₗ ψQ) (hι : ψQ ∘ₗ Tι = cι ∘ₗ ψK) (hTp : Function.Surjective Tp)
    (h0 : Tp ∘ₗ Tι = 0) (hK : Function.Surjective ψK) (hex : ∀ z, cp z = 0 → ∃ w, cι w = z)
    (hQ : Function.Injective ψQ) : Function.Injective ψN := by
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun x hx => ?_)
  obtain ⟨x', rfl⟩ := hTp x
  have hx' : cp (ψQ x') = 0 := (LinearMap.congr_fun hp x').symm.trans hx
  obtain ⟨w', hw'⟩ := hex _ hx'
  obtain ⟨w, rfl⟩ := hK w'
  have hw : ψQ (Tι w) = ψQ x' := (LinearMap.congr_fun hι w).trans hw'
  rw [← hQ hw]
  exact LinearMap.congr_fun h0 w

section Psi

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] (Λ : Type) [Ring Λ] [Finite Λ]
  (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (y : GeometricPoint U.1)
  [Smooth q] [IsProper q] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (jC : U.1 ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

/-- **Injectivity of `ψ` descends along epimorphisms**: if `p : Q ⟶ N` is an epimorphism and
`ψ_Q` is injective, so is `ψ_N`. -/
theorem injective_curveRepresentationCoinvariantsMap_of_epi
    {Q N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)}
    (p : Q ⟶ N) [Epi p]
    (hQ : Function.Injective (curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin Q)) :
    Function.Injective (curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N) := by
  have := preservesFiniteColimits_representationSheaf B U y Λ
  have := preservesFiniteLimits_representationSheaf B U y Λ
  have : (etaleModuleExtensionByZero.{u, 0} Λ jC).IsLeftAdjoint :=
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).isLeftAdjoint
  refine injective_of_surjective_of_comp_eq_zero_of_naturality
    (LinearMap.ext (curveRepresentationCoinvariantsMap_naturality B U y q Λ hn hζ jC hfin p))
    (LinearMap.ext (curveRepresentationCoinvariantsMap_naturality B U y q Λ hn hζ jC hfin
      (kernel.ι p)))
    ((ModuleCat.epi_iff_surjective _).1 (epi_rightDerivedPlus_two_map_of_epi q Λ _)) ?_
    (surjective_curveRepresentationCoinvariantsMap q Λ B U y hn hζ jC hfin (kernel p))
    (exists_finiteTypeContinuousModuleCoinvariantsMap_kernel_eq Λ p) hQ
  have : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).Additive :=
    (Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor (etaleModuleGlobalSections.{u, 0} Λ C)
      (Stacks.DerivedIndexing.derivedDeltaFunctorStructure _)
      (Stacks.DerivedIndexing.canonicalδ _) (fun _ _ => rfl)).additive 2
  rw [← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    kernel.condition, Functor.map_zero, Functor.map_zero, Functor.map_zero, ModuleCat.hom_zero]

end Psi

end Stacks.EtaleCohomology

end
