module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ProperDirectImageCompletionMap

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartComparisonMapTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartIsoOverComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.IdealPowerAnnihilationSurjectiveChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine

/-!
# Pushing a coherent adic system forward along a proper representable morphism

**Stacks 08BD.**  Let `f : X ⟶ Y` be a representable proper morphism of Noetherian algebraic
spaces over `S`, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals, and assume `f` is an
isomorphism over `Y ∖ V(𝒦)`.  Set `𝓘 = f⁻¹𝒥 𝒪_X`.  Let `(𝒢_n)` be an object of `Coh(Y, 𝒥)`, `𝓕` a
coherent `𝒪_X`-module and `β : (f^*𝒢_n) ⟶ 𝓕^∧` an isomorphism in `Coh(X, 𝓘)`.  Then there is a map
`α : (𝒢_n) ⟶ (f_*𝓕)^∧` in `Coh(Y, 𝒥)` whose kernel and cokernel are annihilated by a power of `𝒦`
(`AlgebraicGeometry.Space.exists_hom_completion_modulePushforward_annihilated`).

The map `α` is the unique map whose composites with the comparison `(f_*𝓕)^∧ ⟶ f_*(𝓕^∧)` are the
maps `γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/𝓘ⁿ⁺¹𝓕)`: over every affine étale chart of `Y` the comparison
induces a bijection on the limits of the sections, by the theorem on formal functions
(`AlgebraicGeometry.Space.C1573.bijective_adicSectionLimitMap_chart`), and
`AlgebraicGeometry.Space.C1573.factorThroughLimitBijective` glues the factorizations.  For the
annihilation, over a surjective affine chart `U` with Noetherian ring of functions the situation
is transported to the affine scheme of `U`, where it is the scheme case Stacks 088B
(`AlgebraicGeometry.Space.C1573.exists_chartTopIdeal_pow_annihilates`); the isomorphism over the
complement of `V(𝒦)` is transported by
`AlgebraicGeometry.Space.C1573.isIso_chartBaseChangeSchemeHom_restrict_compl_support`, and
annihilation over the single surjective chart gives annihilation on `Y` because the kernels and
cokernels are cartesian on affine charts
(`AlgebraicGeometry.Space.C1573.idealPowerMultiple_kernel_eq_bot_of_surjective_affineChart`,
`AlgebraicGeometry.Space.C1573.idealPowerMultiple_cokernel_eq_bot_of_surjective_affineChart`).

## Implementation notes

`V(𝒦)` is the closed subspace `Z` with defining ideal `𝒦` (Stacks 03MB), and "`f` is an
isomorphism over `Y ∖ V(𝒦)`" is that the projection `f⁻¹(Y ∖ Z) ⟶ Y ∖ Z` is an isomorphism.  The
isomorphism `β` is stated as an isomorphism of the underlying inverse systems; coherent adic
systems form a full subcategory, so this is an isomorphism in `Coh(X, 𝓘)`.  The coherence of
`f_*𝓕`, which the source quotes from Stacks 08AR to make sense of `(f_*𝓕)^∧`, is part of the
conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08BD.**  For a representable proper morphism `f : X ⟶ Y` of Noetherian algebraic
spaces which is an isomorphism over the complement of the closed subspace `Z = V(𝒦)`, a coherent
`𝒥`-adic system `(𝒢_n)` on `Y`, a coherent `𝒪_X`-module `𝓕` and an isomorphism
`β : (f^*𝒢_n) ≅ 𝓕^∧` of inverse systems on `X` (for the ideal `𝓘 = f⁻¹𝒥 𝒪_X`), the direct image
`f_*𝓕` is coherent and there is a map `α : (𝒢_n) ⟶ (f_*𝓕)^∧` of coherent `𝒥`-adic systems whose
kernel and cokernel are annihilated by a power of `𝒦`. -/
@[stacks 08BD]
theorem exists_hom_completion_modulePushforward_annihilated
    (hZ0 : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hX : IsNoetherian B S hS hZ0 X.1) (hY : IsNoetherian B S hS hZ0 Y.1)
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) (hfp : IsProper B S hS f.hom)
    (J K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJ : J.toSheafOfModules.IsQuasicoherentOnSite)
    (Z : ClosedSubspaces B S hS Y.1) (hZ : definingIdealSheaf B S hS Y Z = K)
    (hiso : IsIso ((openComplement B S hS Z.1).fromPreimage f.hom))
    (G : CoherentAdicSystems B S hS Y.1 Y.2 J)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (β : G.obj ⋙ modulePullback B S hS f ≅
      adicQuotientSystem B S hS X.1 X.2 (C1573.inverseImageIdeal B S hS f hf J) F) :
    haveI : Fact (HasEtaleLocalProperty B S hS Y.1
        (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hY.2.2⟩
    ∃ hP : IsCoherent B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj F),
      ∃ α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJ).obj
          ⟨(modulePushforward B S hS f).obj F, hP⟩,
        IsSystemKernelCokernelAnnihilatedByPower B S hS Y.1 Y.2 K α.hom :=
  by apply C1573.exists_hom_completion_modulePushforward_annihilated <;> assumption

end AlgebraicGeometry.Space

end
