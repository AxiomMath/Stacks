module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistencePushforwardTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TopCohomologyFinitenessGeneral
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveRepresents
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic

/-!
# A uniform upper bound for the objects of Situation 0DIK

In Situation [Stacks, Tag 0DIK] the objects `Kₙ` of `D(𝒪_{Xₙ})` are pseudo-coherent and
`Liₙ^* Kₙ₊₁ ≅ Kₙ`. This file proves that they are bounded above *uniformly*: there is one `b` with
`Hʲ(Kₙ) = 0` for all `n` and all `j > b`.

## Main results

* `AlgebraicGeometry.Space.DerivedExistenceSystem.exists_isZero_homology_K_gt`: each `Kₙ` is
  bounded above.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.isFiniteTypeOnSite_homology_K`: the top
  cohomology of `Kₙ` is of finite type.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.isZero_homology_K_succ`: if `Kₙ₊₁` lives in
  degrees `≤ c` and `Kₙ` in degrees `< c`, then `Hᶜ(Kₙ₊₁) = 0`.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.exists_isZero_homology_K_gt_uniform`: the objects
  `Kₙ` are uniformly bounded above.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.exists_isZero_homology_towerObj_gt_uniform`: the
  same bound for the tower `Rjₙ,* Kₙ` in `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 08FX](https://stacks.math.columbia.edu/tag/08FX)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace DerivedCategory

/-- **Hom-vanishing through an adjunction.** Let `L ⊣ R` be an adjunction `D(𝒜') ⇄ D(𝒜)` whose
right adjoint carries `M[-c]` to `G(M)[-c]`. If `K'` lives in degrees `≤ c` and `L K' ≅ K` with
`Hⁱ(K) = 0` for `i ≥ c`, then every morphism `Hᶜ(K') ⟶ G(M)` vanishes. -/
theorem homology_hom_eq_zero_of_adjunction {C C' : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [Category* C'] [Abelian C'] [HasDerivedCategory C'] (G : C ⥤ C')
    {L : DerivedCategory C' ⥤ DerivedCategory C} {R : DerivedCategory C ⥤ DerivedCategory C'}
    (adj : L ⊣ R) (c : ℤ) (M : C)
    (eM : R.obj ((singleFunctor C c).obj M) ≅ (singleFunctor C' c).obj (G.obj M))
    (K' : DerivedCategory C') (K : DerivedCategory C) (φ : L.obj K' ≅ K)
    (hK' : ∀ i : ℤ, c < i → IsZero ((homologyFunctor C' i).obj K'))
    (hK : ∀ i : ℤ, c ≤ i → IsZero ((homologyFunctor C i).obj K))
    (g : (homologyFunctor C' c).obj K' ⟶ G.obj M) : g = 0 := by
  have : K'.IsLE c := (isLE_iff _ _).2 hK'
  have : K.IsLE c := (isLE_iff _ _).2 fun i hi => hK i hi.le
  obtain ⟨f, rfl⟩ := (bijective_homologyToSingle_of_isLE K' (G.obj M) c).2 g
  have h1 : φ.inv ≫ (adj.homEquiv _ _).symm (f ≫ eM.inv) = 0 :=
    (bijective_homologyToSingle_of_isLE K M c).1 ((hK c le_rfl).eq_of_src _ _)
  rw [Iso.inv_comp_eq, comp_zero, Equiv.symm_apply_eq, Adjunction.homEquiv_unit] at h1
  have := adj.isRightAdjoint
  have hf : f = 0 := by rw [← cancel_mono eM.inv, h1, Functor.map_zero, comp_zero, zero_comp]
  rw [hf, map_zero]

end DerivedCategory

/-- An object whose maps to every image of a right adjoint vanish has a zero image under the left
adjoint. -/
theorem CategoryTheory.Adjunction.isZero_obj_of_forall_eq_zero {A A' : Type*} [Category* A]
    [Category* A'] [HasZeroMorphisms A] [HasZeroMorphisms A'] {P : A ⥤ A'} {Q : A' ⥤ A}
    (adj : P ⊣ Q) (F : A) (h : ∀ (N : A') (g : F ⟶ Q.obj N), g = 0) : IsZero (P.obj F) :=
  (IsZero.iff_id_eq_zero _).2 <| (adj.homEquiv _ _).injective ((h _ _).trans (h _ _).symm)

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- The inverse-limit base `Spec A` is affine. -/
theorem isAffine_limitBaseObject :
    IsAffine ((BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase)) :=
  inferInstanceAs (IsAffine (limitBase D.system))

/-- `X` is quasi-compact. -/
theorem isQuasiCompactSpace_X :
    IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase D.X.left.1 :=
  isQuasiCompactSpace_source_of_isQuasiCompact D.B (limitBase D.system) D.containsLimitBase
    (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
    (isQuasiCompactSpace_yoneda_of_isAffine D.B (limitBase D.system) D.containsLimitBase _
      D.isAffine_limitBaseObject) D.finitePresentation.2.1

/-- Each `Xₙ` is quasi-compact. -/
theorem isQuasiCompactSpace_stage (n : ℕ) :
    IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase (D.stage n).1 :=
  isQuasiCompactSpace_of_isClosedImmersion _ _ _ D.isQuasiCompactSpace_X
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom
    (D.toDerivedExistenceSituation.closedSpaceProjection n)

/-- **Each `Kₙ` is bounded above**: a pseudo-coherent object on the quasi-compact algebraic space
`Xₙ` has vanishing cohomology in all large degrees. -/
theorem exists_isZero_homology_K_gt (n : ℕ) :
    letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
    ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) j).obj (D.K n)) := by
  obtain ⟨E, hE, e⟩ := D.pseudoCoherent n
  exact exists_isZero_homology_gt_of_isPseudoCoherentFrom D.B (limitBase D.system)
    D.containsLimitBase _ (D.stage n).2 (D.isQuasiCompactSpace_stage n) (D.K n) 0 ⟨E, hE 0, e⟩

/-- **The top cohomology of `Kₙ` is of finite type**: if `Hⁱ(Kₙ) = 0` for `i > m` then `Hᵐ(Kₙ)`
is an `𝒪_{Xₙ}`-module of finite type. -/
theorem isFiniteTypeOnSite_homology_K (n : ℕ) (m : ℤ)
    (h : letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
      ∀ i : ℤ, m < i →
        IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) i).obj (D.K n))) :
    letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
    SheafOfModules.IsFiniteTypeOnSite
      ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) m).obj (D.K n)) := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage n))
  obtain ⟨E, hE, e⟩ := D.pseudoCoherent n
  exact Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _
    (RingedSite.isFiniteType_homology_general _ (D.K n) m ⟨E, hE m, e⟩ h)

/-- Every morphism from `Hᶜ(Kₙ₊₁)` to a direct image `iₙ,* M` vanishes, when `Kₙ₊₁` lives in
degrees `≤ c` and `Kₙ` in degrees `< c`. -/
theorem homology_K_succ_hom_toposPushforward_eq_zero (n : ℕ) (c : ℤ)
    (hc : letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
      ∀ i : ℤ, c < i → IsZero
        ((DerivedCategory.homologyFunctor (D.toposModules (D.stage (n + 1))) i).obj (D.K (n + 1))))
    (hn : letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
      ∀ i : ℤ, c ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) i).obj (D.K n)))
    (M : D.toposModules (D.stage n))
    (g : letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
      (DerivedCategory.homologyFunctor (D.toposModules (D.stage (n + 1))) c).obj (D.K (n + 1)) ⟶
        (D.toposPushforward
          (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj M) :
    g = 0 := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage n))
  let := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
  have := D.additive_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  have := D.preservesFiniteLimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  have := D.preservesFiniteColimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.toDerivedExistenceSituation.closedTransitionSpace n)
  have := D.φ_isIso n
  exact DerivedCategory.homology_hom_eq_zero_of_adjunction (D.toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
    (D.transitionAdjunction n) c M
    (((D.toposPushforward (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt
      D.X n)).mapDerivedCategorySingleFunctor c).app M)
    (D.K (n + 1)) (D.K n) (asIso (D.φ n)) hc hn g

/-- If `Kₙ₊₁` lives in degrees `≤ c` and `Kₙ` in degrees `< c`, then `Hᶜ(Kₙ₊₁) = 0`. -/
theorem isZero_homology_K_succ (n : ℕ) (c : ℤ)
    (hc : letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
      ∀ i : ℤ, c < i → IsZero
        ((DerivedCategory.homologyFunctor (D.toposModules (D.stage (n + 1))) i).obj (D.K (n + 1))))
    (hn : letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
      ∀ i : ℤ, c ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) i).obj (D.K n))) :
    letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
    IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage (n + 1))) c).obj
      (D.K (n + 1))) := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
  refine isZero_of_isZero_modulePullback D.B (limitBase D.system) D.containsLimitBase
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (surjective_pointsMap_transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n
      (D.transition_surjective n) (D.transition_locallyNilpotent n)) _
    (D.isQuasicoherentOnSite_homology_K (n + 1) c) (D.isFiniteTypeOnSite_homology_K (n + 1) c hc) ?_
  exact CategoryTheory.Adjunction.isZero_obj_of_forall_eq_zero
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt
        D.X n)).pullbackAdjPushforwardModulesViaComparison
    _ (fun N g => D.homology_K_succ_hom_toposPushforward_eq_zero n c hc hn N g)

/-- **The uniform upper bound**: there is one `b` with `Hʲ(Kₙ) = 0` for all `n` and all
`j > b`. -/
theorem exists_isZero_homology_K_gt_uniform :
    ∃ b : ℤ, ∀ (n : ℕ) (j : ℤ), b < j →
      letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
      IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage n)) j).obj (D.K n)) := by
  obtain ⟨b, hb⟩ := D.exists_isZero_homology_K_gt 0
  refine ⟨b, fun n => ?_⟩
  induction n with
  | zero => exact hb
  | succ n ih =>
    obtain ⟨b', hb'⟩ := D.exists_isZero_homology_K_gt (n + 1)
    have step : ∀ k : ℕ, ∀ j : ℤ, b' - k < j → b < j →
        letI := HasDerivedCategory.standard (D.toposModules (D.stage (n + 1)))
        IsZero ((DerivedCategory.homologyFunctor (D.toposModules (D.stage (n + 1))) j).obj
          (D.K (n + 1))) := by
      intro k
      induction k with
      | zero => intro j hj _; exact hb' j (by simpa using hj)
      | succ k ihk =>
        intro j hj hbj
        by_cases hjk : b' - k < j
        · exact ihk j hjk hbj
        · exact D.isZero_homology_K_succ n j
            (fun i hi => ihk i (by push_cast at hj; omega) (by omega))
            (fun i hi => ih i (by omega))
    intro j hj
    exact step (b' - b).toNat j (by omega) hj

/-- **The uniform upper bound passes to the tower `Rjₙ,* Kₙ`** in `D(𝒪_X)`. -/
theorem exists_isZero_homology_towerObj_gt_uniform :
    ∃ b : ℤ, ∀ (n : ℕ) (j : ℤ), b < j →
      letI := HasDerivedCategory.standard (D.toposModules D.X.left)
      IsZero ((DerivedCategory.homologyFunctor (D.toposModules D.X.left) j).obj (D.towerObj n)) :=
  D.exists_isZero_homology_K_gt_uniform.imp fun _ hb n j hj =>
    D.isZero_homology_towerObj n j (hb n j hj)

end DerivedExistenceSystem

end AlgebraicGeometry.Space
