module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectAnnihilator
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceChartDerivedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceCoheratorAssociatedModule
public import StacksFrontier.Homology.PseudoCoherent.CayleyHamiltonRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsAnnihilatorSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealQuotientSpecClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionLiftAndCompactNeighbourhood

/-!
# The derived existence theorem with supports, over an affine `X`: the support of each `Hⁱ(K)`

In the situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` (Stacks 0DIR, `X`
flat over `A`), the source asserts that the object `K ∈ D(𝒪_X)` it constructs is supported on a
closed subset of `|X|` proper over `A`. That assertion fails in general (see
`StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported` and the entry for
0DIR in `errata.md`). What holds is the per-degree statement: for every `i` the support of the
cohomology sheaf `Hⁱ(K)` lies in a closed subset `Tᵢ ⊆ |X|` proper over `A`. This file proves it
when `X` is affine, `X = Spec R`:

* `M = RΓ(X, K)` is pseudo-coherent in `D(A)`: it is `RΓ(X, 𝒪_X ⊗^L K)`, and the existence proof
  shows `RΓ(X, E ⊗^L K)` pseudo-coherent for every perfect `E`;
* `M` is the restriction of scalars of `RΓ(U, K) ∈ D(R)` for the terminal chart `U = Spec R` of
  `X` (`AlgebraicGeometry.Space.derivedPushforwardSectionsIsoEtaleChartOfIso`), and `R` is of
  finite type over `A`, so Cayley–Hamilton for pseudo-coherent complexes gives an ideal `J ⊆ R`
  with `R ⧸ J` finite over `A` killing `Hⁱ(RΓ(U, K)) = Γ(U, Hⁱ(K))`;
* hence `Supp Hⁱ(K) ⊆ V(J)` (Stacks 07TY and 056I on the chart), and `V(J)` is the image of the
  closed immersion `Spec (R ⧸ J) ⟶ X`, which is finite, hence proper, over `Spec A`.

## Main results

* `…SeparatedDerivedExistenceSystem.exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_…`:
  the existence theorem with its object named, `K = DQ_X(R lim Kₙ)`.
* `…SupportedDerivedExistenceSystem.isPseudoCoherent_limitSectionsFunctor_quasicoherentLimit`:
  `RΓ(X, K)` is pseudo-coherent in `D(A)`.
* `…SupportedDerivedExistenceSystem.exists_isProperOver_supportOfSheaf_homology_…_subset`:
  for `X` affine and every `i`, `Supp Hⁱ(K)` lies in a closed subset of `|X|` proper over `A`.
* `…exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_of_isAffineSpace`: the conclusion
  of `…SupportedDerivedExistenceSystem.exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso`
  together with the per-degree support clause, for `X` affine.

## Implementation notes

The object `K` is the one of the existence proof, `K = DQ_X(R lim Kₙ)`. Its definition is
forgotten (`exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_stageDerivedPullback_iso` returns
it existentially, with the equation) before the compatibility of the `ψₙ` is unfolded: the kernel
does not check that unfolding in reasonable time against the explicit `K`.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
* [Stacks Project, Tag 056I](https://stacks.math.columbia.edu/tag/056I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] pointTopology
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **The derived existence theorem with its object named.** In the situation of
`AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem`, if the `Mₙ` are pseudo-coherent, then
`K = DQ_X(R lim Kₙ)` is pseudo-coherent on `X` and has isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` with
`ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`. -/
theorem exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_stageDerivedPullback_iso
    (hpc : D.StageSectionsPseudoCoherent) :
    ∃ (K : D.limitDerivedCategory) (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n),
      K = (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
          D.quasicoherentLimit ∧
        D.IsPseudoCoherentOnLimit K ∧
        ∀ n : ℕ, (ψ n).hom = (D.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n := by
  obtain ⟨ψ, -, hψ⟩ := D.exists_iso_isCompatibleRestriction_of_isIso D.coherator
    D.coheratorAdjunction (fun n => D.conjugateEquiv_stageDerivedPullbackCompIso_hom n)
    (D.isIso_coheratorLimitPullbackMap_of_forall_isPerfect D.coherator D.coheratorAdjunction
      (fun n E hE => D.isIso_stageSections_map_tensor_coheratorLimitPullbackMap D.coherator
        D.coheratorAdjunction hpc n E hE))
  have hKpc := D.isPseudoCoherentOnLimit_coheratorObj_of_forall_isDerivedLimit
    (fun hp K hK E hE => D.isPseudoCoherent_limitTensorSections_of_isDerivedLimit hpc hp K hK E
      hE) D.coherator D.coheratorAdjunction D.derivedLimit D.isDerivedLimit_derivedLimit
  -- forget the definition of `K` before unfolding the compatibility
  have h : ∃ (K : D.limitDerivedCategory) (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n),
      K = (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
          D.quasicoherentLimit ∧
        D.IsPseudoCoherentOnLimit K ∧ D.IsCompatibleRestriction fun n => (ψ n).hom :=
    ⟨_, ψ, rfl, hKpc, hψ⟩
  obtain ⟨K, ψ, hKeq, hKpc, hψ⟩ := h
  exact ⟨K, ψ, hKeq, hKpc, hψ⟩

end SeparatedDerivedExistenceSystem

namespace SupportedDerivedExistenceSystem

variable (D : SupportedDerivedExistenceSystem.{u})

/-- **`RΓ(X, K)` is pseudo-coherent in `D(A)`** for `K = DQ_X(R lim Kₙ)`: it is
`RΓ(X, 𝒪_X ⊗^L K)`, and `𝒪_X` is perfect. -/
theorem isPseudoCoherent_limitSectionsFunctor_quasicoherentLimit :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      (D.limitSectionsFunctor.obj
        ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
          D.quasicoherentLimit)) := by
  obtain ⟨hp, hK⟩ := D.isDerivedLimit_quasicoherentLimit
  have h := D.isPseudoCoherent_limitTensorSections_of_isDerivedLimit
    D.stageSectionsPseudoCoherent hp _ hK _ (isPerfect_unit D.X.left)
  exact h.ofIso (D.limitSectionsFunctor.mapIso
    (smallEtaleDerivedTensorUnitLeftIso D.B (limitBase D.system) D.containsLimitBase D.X.left _))

/-- **The support of each cohomology sheaf of `K` is proper over `A`, for `X` affine.** For
`K = DQ_X(R lim Kₙ)` and every `i` there is a closed subset `T ⊆ |X|`, proper over `Spec A`,
containing the support of `Hⁱ(K)`: with `X ≅ Spec R`, an ideal `J ⊆ R` with `R ⧸ J` finite over
`A` kills `Γ(X, Hⁱ(K)) = Hⁱ(RΓ(X, K))` (Cayley–Hamilton for the pseudo-coherent `RΓ(X, K)`), and
`T` is the image of `Spec (R ⧸ J) ⟶ X`. -/
theorem exists_isProperOver_supportOfSheaf_homology_quasicoherentLimit_subset
    (hX : IsAffineSpace D.B (limitBase D.system) D.containsLimitBase D.X.left.1) (i : ℤ) :
    ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
      (hT : IsClosed T),
      IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) T hT ∧
        supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              D.X.left.2).O)).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
              D.containsLimitBase D.X.left.1 D.X.left.2) i).obj
              ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
                D.X.left).ι.obj D.quasicoherentLimit))) ⊆ T := by
  classical
  let B := D.B
  let S := limitBase D.system
  let hS := D.containsLimitBase
  let X := D.X.left
  let e := affineSpaceAffineChartIso B S hS X.1 hX
  let T' := affineSpaceAffineChart B S hS X.1 hX
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') :=
    isAffine_affineSpaceAffineChart B S hS X.1 hX
  let U := etaleChartOfIso B S hS e
  let K := (spaceQuasicoherentProp B S hS X).ι.obj D.quasicoherentLimit
  let T₀ := limitBaseObject D.system D.B D.containsLimitBase
  let h : X ⟶ ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩ := D.X.hom
  let g := etaleChartOfIsoBaseHom e h
  let φ := (representedAffineCommRingCatHom B S hS g).hom
  -- `Γ(T₀) ⟶ Γ(T')` is of finite type
  have hg : yoneda.map g = e.inv ≫ h.hom := Functor.map_preimage yoneda _
  have hfp : IsFinitePresentation B S hS (yoneda.map g) := by
    rw [hg]
    exact IsFinitePresentation.of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS T') X.2
      (isAlgebraicSpace_yoneda B S hS T₀) (isAlgebraicSpace_yoneda B S hS T₀)
      (IsPullback.of_horiz_isIso (fst := e.inv) (snd := e.inv ≫ h.hom) (f := h.hom)
        (g := 𝟙 _) ⟨by simp⟩) D.finitePresentation
  have hφ : φ.FiniteType := by
    have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g) :=
      (finitePresentation_of_isFinitePresentation_yoneda_map B S hS g hfp).1
    exact HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  -- `RΓ(U, K)` is pseudo-coherent over `Γ(T₀)`
  have hM := (D.isPseudoCoherent_limitSectionsFunctor_quasicoherentLimit).ofIso
    (derivedPushforwardSectionsIsoEtaleChartOfIso e h K)
  obtain ⟨J, hJfin, hJ⟩ :=
    StacksDraft.PseudoCoherence.exists_ideal_finite_quotient_smul_homologyFunctor_eq_zero
      φ hφ _ hM i
  -- `J` kills `Γ(U, Hⁱ(K))`
  let F := (spaceDerivedHomology B S hS X i).obj K
  have hFq : F.IsQuasicoherentOnSite := D.quasicoherentLimit.property i
  have hU : IsAffineChart B S hS X.1 U := isAffine_toScheme_etaleChartOfIso e
  let v := chartDerivedSectionsHomologyIso B S hS X K D.quasicoherentLimit.property U hU i
  let RU := (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (Opposite.op U)
  have hJF : ∀ r ∈ J, ∀ s : F.val.obj (Opposite.op U), (show RU from r) • s = 0 := by
    intro r hr s
    apply (ModuleCat.mono_iff_injective v.hom).1 inferInstance
    calc v.hom.hom ((show RU from r) • s) = (show RU from r) • v.hom.hom s := map_smul _ _ _
      _ = 0 := hJ r hr _
      _ = v.hom.hom 0 := (map_zero _).symm
  -- the closed subspace `Spec (Γ(T') ⧸ J) ⟶ X`
  let ι := yoneda.map (idealQuotientSpecMap B S hS J) ≫ e.inv
  have hι : IsClosedImmersion B S hS ι :=
    isClosedImmersion_comp B S hS _ _
      (isClosedImmersion_yoneda_map_idealQuotientSpecMap B S hS J)
      (isClosedImmersion_of_isIso B S hS e.inv)
  have hTc := isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 ι hι
  refine ⟨_, hTc, isProperOver_of_isClosedImmersion_of_range B S hS
    (isAlgebraicSpace_yoneda B S hS _) X.2 (isAlgebraicSpace_yoneda B S hS T₀) ι hι h.hom _ _
    hTc rfl ?_, ?_⟩
  · have : ι ≫ h.hom = yoneda.map (idealQuotientSpecMap B S hS J ≫ g) := by
      rw [Functor.map_comp, hg, Category.assoc]
    rw [this]
    exact isProper_yoneda_map_idealQuotientSpecMap_comp B S hS J g hJfin
  · intro p hp
    let y := pointsEquivScheme B S hS T' (pointsMap B S hS X.1 e.hom p)
    have hpy : pointsMap B S hS (yoneda.obj T') U.obj.hom
        ((pointsEquivScheme B S hS T').symm y) = p := by
      simp only [y, Equiv.symm_apply_apply]
      change pointsMap B S hS _ e.inv (pointsMap B S hS X.1 e.hom p) = p
      rw [← Function.comp_apply (f := pointsMap B S hS _ e.inv), ← pointsMap_comp,
        e.hom_inv_id, pointsMap_id, id_eq]
    have hpy' : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y) = p := hpy
    have hy : y ∈ SheafOfModules.supp (restrictToChart B S hS X.2 F U) := by
      have hmem : y ∈ (fun u => pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
          U.obj.hom ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm u)) ⁻¹'
            supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
        change pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom
          ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y) ∈
            supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)
        rw [hpy']
        exact hp
      rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X U F]
      exact hmem
    obtain ⟨z, hz⟩ := pointsEquivScheme_symm_mem_range_idealQuotientSpecMap B S hS J y
      (isoSpec_mem_zeroLocus_of_mem_supp_restrictToChart B S hS X F hFq U J
        (fun r hr s => hJF r hr s) y hy)
    refine ⟨z, ?_⟩
    rw [pointsMap_comp, Function.comp_apply, hz]
    exact hpy

/-- `exists_isProperOver_supportOfSheaf_homology_quasicoherentLimit_subset`, for an object of
`D(𝒪_X)` given as equal to `K = DQ_X(R lim Kₙ)`. -/
theorem exists_isProperOver_supportOfSheaf_homology_subset_of_eq
    (hX : IsAffineSpace D.B (limitBase D.system) D.containsLimitBase D.X.left.1)
    (K : D.limitDerivedCategory)
    (hK : K = (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
      D.quasicoherentLimit) (i : ℤ) :
    ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
      (hT : IsClosed T),
      IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) T hT ∧
        supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              D.X.left.2).O)).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
              D.containsLimitBase D.X.left.1 D.X.left.2) i).obj K)) ⊆ T := by
  subst hK
  exact D.exists_isProperOver_supportOfSheaf_homology_quasicoherentLimit_subset hX i

/-- **Grothendieck's existence theorem in its derived form, with supports proper over the base,
for `X` affine (Stacks 0DIR, `X` flat over `A`, the per-degree support clause).** If `X` is
affine, there is `K ∈ D(𝒪_X)`, pseudo-coherent relative to `A`, with isomorphisms
`ψₙ : Ljₙ^* K ≅ Kₙ` such that `ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`, and such that for
every `i` the support of the cohomology sheaf `Hⁱ(K)` lies in a closed subset of `|X|` proper
over `Spec A`. The source's clause that the whole of `K` is supported on one closed subset
proper over `A` fails (see the module
`StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported`); this is the
per-degree form, which holds. -/
theorem exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso_of_isAffineSpace
    (hX : IsAffineSpace D.B (limitBase D.system) D.containsLimitBase D.X.left.1) :
    ∃ (K : D.limitDerivedCategory)
      (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n)
      (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
      IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          D.X.left.2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
        (∀ n : ℕ, (ψ n).hom = (D.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n) ∧
        ∀ i : ℤ, ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
          (hT : IsClosed T),
          IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
              (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
              (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
                D.containsLimitBase D.finitePresentation.1) T hT ∧
            supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
                  D.X.left.2).O)).obj
                ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
                  D.containsLimitBase D.X.left.1 D.X.left.2) i).obj K)) ⊆ T := by
  obtain ⟨K, ψ, hKeq, hKpc, hψ⟩ :=
    D.1.exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_stageDerivedPullback_iso
      D.stageSectionsPseudoCoherent
  have hK := derivedCategoryB_of_isPseudoCoherent_unconditional D.B (limitBase D.system)
    D.containsLimitBase _ _ K hKpc
  exact ⟨K, ψ, hK, (isRelativelyPseudoCoherent_iff_isPseudoCoherent D.B (limitBase D.system)
    D.containsLimitBase D.X.hom D.flat D.finitePresentation.1 ⟨K, hK⟩).2 hKpc, hψ,
    D.exists_isProperOver_supportOfSheaf_homology_subset_of_eq hX K hKeq⟩

end SupportedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
