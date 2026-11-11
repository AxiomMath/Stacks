module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportDisjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.Homology.Perfect.BaseChangeVanishingAbove
public import StacksFrontier.Homology.Tor.BaseChangeTensorIsoSupplement

/-!
# The derived existence theorem: the cohomology of `K` in degrees `≥ i` has closed support

In the situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` let
`K = DQ_X(R lim Kₙ)` be the object of the existence theorem. For every `i` the union
`⋃_{j ≥ i} Supp Hʲ(K)` is closed in `|X|`. This is step (a) of the per-degree support clause of
the errata entry 0DIR(support of K).

## The proof

Let `x` lie in no `Supp Hʲ(K)`, `j ≥ i`, and let `U = Spec R ⟶ X` be an affine étale chart
through `x`, at the prime `𝔭`. The object `M = RΓ(U, K)` of `D(R)` is pseudo-coherent and
`Hʲ(M) = Γ(U, Hʲ(K))`, whose localization at `𝔭` vanishes for `j ≥ i`. So
`Hʲ(M ⊗^L_R R_𝔭) = Hʲ(M)_𝔭 = 0` for `j ≥ i`, and the vanishing spreads out
(`StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_baseChange`): there is
`g ∉ 𝔭` with `Hʲ(M)_g = 0` for all `j ≥ i`. The image of `D(g)` in `|X|` is an open
neighbourhood of `x` missing every `Supp Hʲ(K)`, `j ≥ i`.

## Main results

* `…SupportedDerivedExistenceSystem.exists_isOpen_disjoint_supportOfSheaf_homology_…`: a point
  outside every `Supp Hʲ(K)`, `j ≥ i`, has an open neighbourhood missing all of them.
* `…SupportedDerivedExistenceSystem.isClosed_iUnion_supportOfSheaf_homology_quasicoherentLimit`:
  the main statement.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] pointTopology
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance 10000] HasDerivedCategory.standard

namespace SupportedDerivedExistenceSystem

variable (D : SupportedDerivedExistenceSystem.{u})

/-- **A point outside the supports of the `Hʲ(K)`, `j ≥ i`, has an open neighbourhood outside
them.** For `K = DQ_X(R lim Kₙ)` and `x ∈ |X|` lying in no `Supp Hʲ(K)` with `j ≥ i`, there is
an open `O ∋ x` disjoint from every `Supp Hʲ(K)` with `j ≥ i`: on an affine étale chart
`Spec R` through `x`, at the prime `𝔭`, the pseudo-coherent `M = RΓ(Spec R, K)` has
`Hʲ(M)_𝔭 = 0` for `j ≥ i`, hence `Hʲ(M)_g = 0` for `j ≥ i` and some `g ∉ 𝔭`, and `O` is the
image of `D(g)`. -/
theorem exists_isOpen_disjoint_supportOfSheaf_homology_quasicoherentLimit (i : ℤ)
    (x : points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)
    (hx : ∀ j : ℤ, i ≤ j → x ∉ supportOfSheaf D.B (limitBase D.system) D.containsLimitBase
      D.X.left.1
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
            D.X.left.2).O)).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
            D.containsLimitBase D.X.left.1 D.X.left.2) j).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj D.quasicoherentLimit)))) :
    ∃ O : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1),
      IsOpen O ∧ x ∈ O ∧ ∀ j : ℤ, i ≤ j → Disjoint O
        (supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
              D.X.left.2).O)).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
              D.containsLimitBase D.X.left.1 D.X.left.2) j).obj
              ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
                D.X.left).ι.obj D.quasicoherentLimit)))) := by
  classical
  let B := D.B
  let S := limitBase D.system
  let hS := D.containsLimitBase
  let X := D.X.left
  let K := (spaceQuasicoherentProp B S hS X).ι.obj D.quasicoherentLimit
  obtain ⟨W, b, hWaff, hb, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X.1 X.2 x
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hb⟩
  have hU : IsAffineChart B S hS X.1 U := hWaff
  have : IsAffine (chartScheme U) := hWaff
  let T := (SmallEtale.toOver B S hS X.1).obj U
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hU
  let u := representedChartToSpace X U
  let R := Γ(chartScheme U, ⊤)
  -- the chart point map and the derived sections `M = RΓ(U, K)`
  let c : chartScheme U → points B S hS X.1 := fun z =>
    pointsMap B S hS (yoneda.obj T) U.obj.hom ((pointsEquivScheme B S hS T).symm z)
  let L := (smallEtaleDerivedModulePullback B S hS u).obj K
  have hLq : QcohDerived B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ L :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS u K D.quasicoherentLimit.property
  let M := (representedAffineDerivedSections B S hS T).obj L
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M := by
    obtain ⟨K', ψ, hK'eq, hpc, -⟩ :=
      D.exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_stageDerivedPullback_iso
        D.stageSectionsPseudoCoherent
    rw [hK'eq] at hpc
    rw [@StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _ _ (_)]
    intro m'
    obtain ⟨L', hL', e'⟩ := hpc
    exact isPseudoCoherentFrom_representedAffineDerivedSections_obj B S hS T L hLq m'
      (isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general u K m' ⟨L', hL' m', e'⟩)
  -- `Hʲ(M) ≅ Γ(U, Hʲ(K))`
  let e : ∀ j : ℤ, (DerivedCategory.homologyFunctor _ j).obj M ≅
      ((spaceDerivedHomology B S hS X j).obj K).val.obj (op U) := fun j =>
    (DerivedCategory.homologyFunctor _ j).mapIso
        ((representedAffineDerivedSections B S hS T).mapIso
          ((smallEtaleDerivedModulePullbackIsoEtale B S hS u
            (isEtale_representedChartToSpace X U)).app K)) ≪≫
      homologyRepresentedAffineDerivedSectionsEtaleIso X U hU K D.quasicoherentLimit.property j
  -- the point `z` of the chart over `x` and its prime `𝔭`
  let z := pointsEquivScheme B S hS W w
  have hzx : c z = x := by
    change pointsMap B S hS (yoneda.obj W) b ((pointsEquivScheme B S hS W).symm z) = x
    rw [Equiv.symm_apply_apply]
    exact hw
  let p := ((chartScheme U).isoSpec.hom z).asIdeal
  have : p.IsPrime := ((chartScheme U).isoSpec.hom z).isPrime
  -- `Hʲ(M)_𝔭 = 0` for `j ≥ i`
  have hloc : ∀ j : ℤ, i ≤ j → Subsingleton (LocalizedModule p.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj M)) := by
    intro j hj
    let F := (spaceDerivedHomology B S hS X j).obj K
    have hF : F.IsQuasicoherentOnSite := D.quasicoherentLimit.property j
    let G : (chartScheme U).Modules := @id (chartScheme U).Modules (restrictToChart B S hS X.2 F U)
    have : G.IsQuasicoherent := isQuasicoherent_restrictToChart B S hS X F hF U
    have hz : z ∉ SheafOfModules.supp G := by
      intro hz
      have h' : z ∈ SheafOfModules.supp (restrictToChart B S hS X.2 F U) := hz
      rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X U F,
        Set.mem_preimage] at h'
      exact hx j hj (hzx ▸ h')
    rw [← mem_support_sections_iff_mem_supp_top] at hz
    have hz := Module.notMem_support_iff.1
      (show ((chartScheme U).isoSpec.hom z : PrimeSpectrum R) ∉ Module.support R Γ(G, ⊤) from hz)
    let φ : (Γ(G, ⊤) : Type u) ≃ₗ[R] (F.val.obj (op U) : Type u) :=
      ((moduleGlobalSections (chartScheme U)).mapIso
          (restrictToChartIsoChartRestrictionSheaf B S hS X F U)).toLinearEquiv.trans
        (chartRestrictionSheafTopEquiv B S hS X F U).symm
    let ψ : ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj M : Type u) ≃ₗ[R]
        (Γ(G, ⊤) : Type u) := (e j).toLinearEquiv.trans φ.symm
    rw [LocalizedModule.subsingleton_iff] at hz ⊢
    intro m
    obtain ⟨s, hs, hsm⟩ := hz (ψ m)
    refine ⟨s, hs, ψ.injective ?_⟩
    rw [map_smul, hsm, map_zero]
  -- `Hʲ(M ⊗^L R_𝔭) = 0` for `j ≥ i`
  let f := algebraMap R (Localization.AtPrime p)
  have hvan : ∀ j : ℤ, i - 1 < j → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.AtPrime p)) j).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          f).functor.obj M)) := by
    intro j hj
    have h := ((CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIsoAtModel
      (R := R) (A := Localization.AtPrime p) p.primeCompl j).app M)
    have hz : IsZero ((ModuleCat.restrictScalars f).obj ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.AtPrime p)) j).obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            f).functor.obj M))) := by
      refine IsZero.of_iso ?_ h
      rw [ModuleCat.isZero_iff_subsingleton]
      exact hloc j (by omega)
    rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
    exact hz
  obtain ⟨g, hg, hgM⟩ :=
    StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_baseChange f
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) M hM (i - 1) hvan
  have hcomap : Ideal.comap f (IsLocalRing.maximalIdeal (Localization.AtPrime p)) = p := by
    exact Localization.AtPrime.under_maximalIdeal ..
  rw [hcomap] at hg
  -- the open set
  let O : Set (points B S hS X.1) :=
    c '' {z' | g ∉ ((chartScheme U).isoSpec.hom z').asIdeal}
  refine ⟨O, ?_, ⟨z, hg, hzx⟩, fun j hj => ?_⟩
  · have he : Continuous (pointsEquivScheme B S hS T) := by
      rw [continuous_def]
      intro V hV
      rw [isOpen_pointTopology_yoneda_iff_isOpen_image]
      rwa [show pointsToScheme B S hS T '' (pointsEquivScheme B S hS T ⁻¹' V) = V from
        Set.image_preimage_eq V (pointsEquivScheme B S hS T).surjective]
    have hopen : IsOpen {z' : chartScheme U | g ∉ ((chartScheme U).isoSpec.hom z').asIdeal} :=
      (PrimeSpectrum.isOpen_basicOpen (a := g)).preimage (chartScheme U).isoSpec.hom.continuous
    have hO : O = pointsMap B S hS (yoneda.obj T) U.obj.hom ''
        ((pointsEquivScheme B S hS T).symm ''
          {z' : chartScheme U | g ∉ ((chartScheme U).isoSpec.hom z').asIdeal}) := by
      rw [Set.image_image]
    rw [hO]
    refine isOpenMap_pointsMap_of_presheafEtale B S hS U.obj.hom hb _ ?_
    rw [Equiv.image_eq_preimage_symm, Equiv.symm_symm]
    exact hopen.preimage he
  · rw [Set.disjoint_left]
    rintro _ ⟨z', hz'g, rfl⟩ hz'
    let F := (spaceDerivedHomology B S hS X j).obj K
    have hF : F.IsQuasicoherentOnSite := D.quasicoherentLimit.property j
    have hz'supp : z' ∈ SheafOfModules.supp (restrictToChart B S hS X.2 F U) := by
      rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X U F,
        Set.mem_preimage]
      exact hz'
    obtain ⟨m, hm⟩ := exists_forall_smul_eq_zero_mem_of_mem_supp_restrictToChart X F hF U z'
      hz'supp
    have := hgM j (by omega)
    rw [LocalizedModule.subsingleton_iff] at this
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := this ((e j).toLinearEquiv.symm m)
    refine hz'g (((chartScheme U).isoSpec.hom z').isPrime.mem_of_pow_mem k (hm (g ^ k) ?_))
    have := congrArg (e j).toLinearEquiv hk
    rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at this
    exact this

/-- **The cohomology of `K` in degrees `≥ i` has closed support** (step (a) of the errata entry
0DIR(support of K), per-degree clause). For `K = DQ_X(R lim Kₙ)` and every `i`, the union
`⋃_{j ≥ i} Supp Hʲ(K)` is closed in `|X|`. -/
theorem isClosed_iUnion_supportOfSheaf_homology_quasicoherentLimit (i : ℤ) :
    IsClosed (⋃ (j : ℤ) (_ : i ≤ j),
      supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
            D.X.left.2).O)).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
            D.containsLimitBase D.X.left.1 D.X.left.2) j).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj D.quasicoherentLimit)))) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hx
  obtain ⟨O, hO, hxO, hOd⟩ :=
    D.exists_isOpen_disjoint_supportOfSheaf_homology_quasicoherentLimit i x hx
  refine ⟨O, fun y hy => ?_, hO, hxO⟩
  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  exact fun j hj hyj => Set.disjoint_left.1 (hOd j hj) hy hyj

end SupportedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
