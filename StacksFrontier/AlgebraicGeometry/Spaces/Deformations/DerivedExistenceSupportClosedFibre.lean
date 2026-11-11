module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportDisjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineHomologySupport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareStep
public import StacksFrontier.Homology.Perfect.BaseChangeVanishingAbove
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayLocus

/-!
# The derived existence theorem: the cohomology of `K` along `X₀` lies over `Z₀`

In the situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` let
`K = DQ_X(R lim Kₙ)` be the object of the existence theorem and `j₀ : X₀ ⟶ X` the closed
immersion of the closed fibre. Then for every `i` the points of the support of `Hⁱ(K)` lying in
`|X₀|` lie in the image of the closed subset `Z₀ ⊆ |X₀|` supporting `K₀`.

## The proof

Let `x₀ ∈ |X₀|` with `x = j₀(x₀) ∉ j₀(Z₀)`. Take an affine étale chart `u : U = Spec R ⟶ X` at a
point `z` over `x`, and `U₀ = U ×_{Spec A} Spec A₀ = Spec R₀`, which maps to `X₀`. The derived
sections `M = RΓ(U, Lu^*K)` are pseudo-coherent, and `Φ_{R₀}(M ⊗^L_R R₀) ≅ L(u₀)^*K₀` is
supported on the preimage of `Z₀`. A point `z₀` of `U₀` over `z` and over `x₀` misses that
preimage, so its prime `q` is outside the support of every `Hⁱ(M ⊗^L_R R₀)`. By Nakayama
(`StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_baseChange` along
`R ⟶ (R₀)_q`), some `g ∈ R` not vanishing at `z` kills every `Hⁱ(M) = Γ(U, Hⁱ(K))` after
localization, so `x` is not in the support of `Hⁱ(K)`.

## Main results

* `StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_notMem_support`: the
  algebraic input, Nakayama read off the supports of the cohomology of a derived base change.
* `…SupportedDerivedExistenceSystem.supportOfSheaf_homology_quasicoherentLimit_inter_range_subset`:
  the main statement.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)
open CochainComplex.DerivedExtensionScalars

universe u

/-! ### Nakayama from the supports of a derived base change -/

section Algebra

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- **Spreading out the vanishing of the cohomology of a derived base change at a prime.** Let
`f : R → R'` be a ring map, `q` a prime of `R'` and `K` a pseudo-coherent object of `D(R)` such
that `q` is outside the support of `Hⁱ(K ⊗_R^L R')` for all `i > b`. Then there is `g ∈ R`
outside `q ∩ R` with `Hⁱ(K)_g = 0` for all `i > b`: apply
`StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_baseChange` along
`R → R'_q`, flat base change to `R'_q` being localization of the cohomology. -/
theorem exists_away_forall_subsingleton_localizedModule_of_notMem_support {R R' : Type u}
    [CommRing R] [CommRing R'] (f : R →+* R') (q : PrimeSpectrum R')
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (b : ℤ)
    (hq : ∀ i : ℤ, b < i → q ∉ Module.support R'
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
        ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K))) :
    ∃ g : R, g ∉ q.asIdeal.comap f ∧ ∀ i : ℤ, b < i →
      Subsingleton (LocalizedModule (Submonoid.powers g)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) := by
  let L := Localization.AtPrime q.asIdeal
  let a : R' →+* L := algebraMap R' L
  have ha : a.Flat := RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat L q.asIdeal.primeCompl)
  obtain ⟨g, hg, hgi⟩ := exists_away_forall_subsingleton_localizedModule_of_baseChange (a.comp f)
    (IsLocalRing.maximalIdeal L) K hK b fun i hi => by
      have h1 : IsZero ((ModuleCat.extendScalars.{u, u, u} a).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
            ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K))) :=
        ModuleCat.isZero_iff_subsingleton.2
          ((Dualizing.subsingleton_extendScalars_localizationAtPrime_iff_notMem_support.{u, u}
            q _).2 (hq i hi))
      exact (h1.of_iso ((CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, u}
        a ha i).app _)).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
          ((totalDerivedExtensionScalarsComp.{u, u} f a).app K).symm)
  refine ⟨g, ?_, hgi⟩
  rwa [← Ideal.comap_comap, show (IsLocalRing.maximalIdeal L).comap a = q.asIdeal from
    Localization.AtPrime.under_maximalIdeal] at hg

end StacksDraft.Perfect

end Algebra

/-! ### The cohomology of `K` along `X₀` -/

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] pointTopology
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance 10000] HasDerivedCategory.standard

namespace SupportedDerivedExistenceSystem

variable (D : SupportedDerivedExistenceSystem.{u})

/-- **The cohomology sheaves of `K` along the closed fibre lie over `Z₀`.** In the situation of
`AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` let `K = DQ_X(R lim Kₙ)` and let
`j₀ : X₀ ⟶ X` be the closed immersion of the closed fibre, `K₀` being supported on `Z₀ ⊆ |X₀|`.
Then for every `i` a point of the support of `Hⁱ(K)` in the image of `|X₀|` is in `j₀(Z₀)`: at a
point `x₀ ∉ Z₀` the derived fibre of `K` vanishes, and by Nakayama so does every `Hⁱ(K)` near
`j₀(x₀)`. -/
theorem supportOfSheaf_homology_quasicoherentLimit_inter_range_subset (i : ℤ) :
    supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
            D.X.left.2).O)).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
            D.containsLimitBase D.X.left.1 D.X.left.2) i).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj D.quasicoherentLimit))) ∩
        Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase _
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom) ⊆
      pointsMap D.B (limitBase D.system) D.containsLimitBase _
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom ''
        D.support 0 := by
  classical
  let B := D.B
  let S := limitBase D.system
  let hS := D.containsLimitBase
  let X := D.X.left
  let K := (spaceQuasicoherentProp B S hS X).ι.obj D.quasicoherentLimit
  let j₀ := spaceProjection D.system B hS D.containsBaseAt D.X 0
  rintro x ⟨hx, x₀, rfl⟩
  by_contra hxZ
  -- an affine étale chart `u : U ⟶ X` at `x`, with point `z`
  obtain ⟨W, b, hWaff, hb, w, hw⟩ :=
    exists_affine_etale_chart_at_point B S hS X.1 X.2 (pointsMap B S hS _ j₀.hom x₀)
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hb⟩
  have hU : IsAffineChart B S hS X.1 U := hWaff
  have : IsAffine (chartScheme U) := hWaff
  let T := (SmallEtale.toOver B S hS X.1).obj U
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hWaff
  let u := representedChartToSpace X U
  let F := (spaceDerivedHomology B S hS X i).obj K
  have hF : F.IsQuasicoherentOnSite := D.quasicoherentLimit.property i
  let z := pointsEquivScheme B S hS W w
  have hzx :
      pointsMap B S hS (yoneda.obj W) U.obj.hom ((pointsEquivScheme B S hS W).symm z) =
        pointsMap B S hS _ j₀.hom x₀ := by
    rw [Equiv.symm_apply_apply]
    exact hw
  have hz : z ∈ SheafOfModules.supp (restrictToChart B S hS X.2 F U) := by
    rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent, Set.mem_preimage]
    change pointsMap B S hS (yoneda.obj W) U.obj.hom ((pointsEquivScheme B S hS W).symm z) ∈ _
    rw [hzx]
    exact hx
  obtain ⟨m, hm⟩ := exists_forall_smul_eq_zero_mem_of_mem_supp_restrictToChart X F hF U z hz
  -- the closed fibre `V = U ×_{Spec A} Spec A₀` of the chart, and its map `u₀ : V ⟶ X₀`
  let π₀ := baseObjectProjection D.system B hS D.containsBaseAt 0
  let tA : T ⟶ limitBaseObject D.system B hS := Over.homMk T.hom (Category.comp_id _)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (limitBaseObject D.system B hS)) :=
    D.isAffine_limitBaseObject
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (baseObjectAt D.system B hS D.containsBaseAt 0)) :=
    inferInstanceAs (IsAffine (Spec _))
  let V := pullback tA π₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
    IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) tA π₀).hom
  have hterm : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (p q : P ⟶ yoneda.obj (limitBaseObject D.system B hS)), p = q := by
    intro P p q
    ext Y a
    exact (Over.mkIdTerminal (X := B.obj hS)).hom_ext _ _
  let u₀ : yoneda.obj V ⟶ (spaceAt D.system B hS D.containsBaseAt D.X 0).1 :=
    pullback.lift (yoneda.map (pullback.snd tA π₀)) (yoneda.map (pullback.fst tA π₀) ≫ u.hom)
      (hterm _ _)
  let u₀' : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
      spaceAt D.system B hS D.containsBaseAt D.X 0 := ObjectProperty.homMk u₀
  have hu₀ : u₀ ≫ j₀.hom = yoneda.map (pullback.fst tA π₀) ≫ u.hom := pullback.lift_snd _ _ _
  -- a point `z₀` of `V` over `z` and over `x₀`
  have sq : IsPullback (yoneda.map (pullback.fst tA π₀)) (yoneda.map (pullback.snd tA π₀))
      (yoneda.map tA) (yoneda.map π₀) := (IsPullback.of_hasPullback tA π₀).map yoneda
  obtain ⟨z₀, hz₀, hz₀'⟩ := exists_points_of_isPullback B S hS sq w
    (pointsMap B S hS _ (spaceBaseProjection D.system B hS D.containsBaseAt D.X 0).hom x₀) (by
      have h1 : yoneda.map tA = u.hom ≫ D.X.hom.hom := hterm _ _
      refine ((congrArg (fun φ => pointsMap B S hS _ φ w) h1).trans
        (pointsMap_comp_apply B S hS u.hom D.X.hom.hom w)).trans ?_
      refine (congrArg (pointsMap B S hS _ D.X.hom.hom) hw).trans ?_
      refine (pointsMap_comp_apply B S hS j₀.hom D.X.hom.hom x₀).symm.trans ?_
      refine (congrArg (fun φ => pointsMap B S hS _ φ x₀)
        (pullback.condition (f := (baseSpaceProjection D.system B hS D.containsBaseAt 0).hom)
          (g := D.X.hom.hom)).symm).trans ?_
      exact pointsMap_comp_apply B S hS _ _ x₀)
  have hz₀Z : pointsMap B S hS _ u₀ z₀ ∉ D.support 0 := by
    intro h
    refine hxZ ⟨_, h, ?_⟩
    exact (pointsMap_comp_apply B S hS u₀ j₀.hom z₀).symm.trans
      ((congrArg (fun φ => pointsMap B S hS _ φ z₀) hu₀).trans
        ((pointsMap_comp_apply B S hS _ u.hom z₀).trans
          ((congrArg (pointsMap B S hS _ u.hom) hz₀).trans hw)))
  -- `M = RΓ(U, Lu^*K)` and its base change `N = M ⊗^L_R R₀`
  let g := pullback.fst tA π₀
  let L := (smallEtaleDerivedModulePullback B S hS u).obj K
  have hLq : QcohDerived B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ L :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS u K D.quasicoherentLimit.property
  let M := (representedAffineDerivedSections B S hS T).obj L
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS T L hLq
  let cL : (representedAffineDerivedAssociated B S hS T).obj M ≅ L :=
    asIso ((representedAffineDerivedAdjunction B S hS T).counit.app L)
  let N := (representedAffineDerivedExtension B S hS g).functor.obj M
  let E := (representedAffineDerivedAssociated B S hS V).obj N
  obtain ⟨K', ψ, hK'eq, hpc, -⟩ :=
    D.exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_stageDerivedPullback_iso
      D.stageSectionsPseudoCoherent
  -- `Φ_{R₀}(N) ≅ L(u₀)^*K₀`, supported on the preimage of `Z₀`
  have hcomp : representedSpaceMap B S hS g ≫ u = u₀' ≫ j₀ := by
    ext1
    exact hu₀.symm
  let eE : E ≅ (smallEtaleDerivedModulePullback B S hS u₀').obj (D.K 0) :=
    ((representedAffineDerivedBaseChangeIso B S hS g).app M).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).mapIso cL ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g) u).app K ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS hcomp).app K ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS u₀' j₀).app K).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS u₀').mapIso
        (eqToIso (by rw [hK'eq]) ≪≫ ψ 0)
  have hEs : CohomologySupportedOn B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
      (pointsMap B S hS _ u₀ ⁻¹' D.support 0) E :=
    cohomologySupportedOn_of_iso' B S hS eE.symm
      (cohomologySupportedOn_smallEtaleDerivedModulePullback u₀' (D.K 0) (D.supported 0))
  -- the prime `q` of `z₀` is outside the support of every `Hⁱ(N)`
  let xs := pointsEquivScheme B S hS V z₀
  let q : PrimeSpectrum Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom xs
  let eN : N ≅ (representedAffineDerivedSections B S hS V).obj E :=
    asIso ((representedAffineDerivedAdjunction B S hS V).unit.app N)
  have hq : ∀ i' : ℤ, i - 1 < i' → q ∉ Module.support Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) i').obj N) := by
    intro i' _ hqs
    apply hz₀Z
    have := pointsEquivScheme_symm_mem_of_mem_support_homology B S hS V E
      (qcohDerived_representedAffineDerivedAssociated_obj B S hS V N) _ hEs i' xs (by
        rwa [← ((DerivedCategory.homologyFunctor _ i').mapIso eN).toLinearEquiv.support_eq])
    rwa [Equiv.symm_apply_apply] at this
  -- `M` is pseudo-coherent
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M := by
    rw [hK'eq] at hpc
    rw [@StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _ _ (_)]
    intro m'
    obtain ⟨L', hL', e'⟩ := hpc
    exact isPseudoCoherentFrom_representedAffineDerivedSections_obj B S hS T L hLq m'
      (isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general u K m' ⟨L', hL' m', e'⟩)
  obtain ⟨s, hs, hsi⟩ :=
    StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_notMem_support
      (representedAffineCommRingCatHom B S hS g).hom q M hM (i - 1) hq
  -- `q` lies over the prime of `z`
  have hgz : (BigFppfOver.toScheme B S hS).map g xs = z := by
    apply (pointsEquivScheme B S hS T).symm.injective
    rw [← pointsMap_yoneda_map_symm, Equiv.symm_apply_apply, hz₀]
    exact ((pointsEquivScheme B S hS W).symm_apply_apply w).symm
  have hcomap : q.asIdeal.comap (representedAffineCommRingCatHom B S hS g).hom =
      ((chartScheme U).isoSpec.hom z).asIdeal := by
    rw [← hgz, ← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply]
    rfl
  rw [hcomap] at hs
  -- the conclusion, on the sections of `Hⁱ(K)` over `U`
  let e : (DerivedCategory.homologyFunctor _ i).obj M ≅ F.val.obj (op U) :=
    (DerivedCategory.homologyFunctor _ i).mapIso
        ((representedAffineDerivedSections B S hS T).mapIso
          ((smallEtaleDerivedModulePullbackIsoEtale B S hS u
            (isEtale_representedChartToSpace X U)).app K)) ≪≫
      homologyRepresentedAffineDerivedSectionsEtaleIso X U hU K D.quasicoherentLimit.property i
  obtain ⟨r, ⟨k, rfl⟩, hr⟩ :=
    LocalizedModule.subsingleton_iff.1 (hsi i (by omega)) (e.toLinearEquiv.symm m)
  refine hs (((chartScheme U).isoSpec.hom z).isPrime.mem_of_pow_mem k (hm _ ?_))
  have := congrArg e.toLinearEquiv hr
  rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at this
  exact this

end SupportedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
