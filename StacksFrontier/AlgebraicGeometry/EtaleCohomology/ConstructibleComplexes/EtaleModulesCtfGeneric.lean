module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GenericTrivialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed

/-!
# A constructible flat sheaf is locally constant near a generic point

Let `X` be a reduced scheme and `Λ` an arbitrary ring. Around every generic point of an
irreducible component of `X` a constructible flat sheaf of `Λ`-modules is locally constant with
finite projective values on an open neighbourhood. This is the dévissage the proof of Tag 03UG
uses in Step 3 ("the assumptions on `𝓕` come from unwinding the definition of `D_ctf`"): an
object of `D_ctf` on a quasi-compact and quasi-separated scheme is a bounded complex of
constructible flat sheaves (`Stacks.EtaleCohomology.isCtf_iff_of_qcqs`), and each of those is
finite locally constant with finite projective values on a dense open.

## Main results

* `exists_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_isConstructibleFlatModuleSheaf`
  — on the small étale site of Stacks 021B.
* `Stacks.EtaleCohomology.exists_isOpenImmersion_isFiniteProjectiveLocallyConstant` — the same for
  a constructible flat sheaf on Mathlib's small étale site, the conclusion being read on the
  transport of its restriction to the open.

## Implementation notes

The argument is that of
`exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf`,
with the condition on the strata "locally constant with finite projective values" in place of
"locally constant of finite type": the stratum through the generic point contains an open
neighbourhood of it, over which, `X` being reduced, the stratum is an open immersion.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 005K](https://stacks.math.columbia.edu/tag/005K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **A constructible flat sheaf is locally constant with finite projective values on an open
neighbourhood of each generic point.** Let `X` be a reduced scheme of a big étale site, `G` a
constructible flat sheaf of `Λ`-modules on its small étale site, for an arbitrary ring `Λ`, and
`η` a generic point of an irreducible component of `X`. Then there is an open immersion
`o : O ⟶ X` whose image contains `η` and along which the inverse image of `G` is locally constant
with finite projective values. -/
public theorem
    exists_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_isConstructibleFlatModuleSheaf
    (X : B.Scheme) [IsReduced X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hG : IsConstructibleFlatModuleSheaf B X Λ G) {η : X.obj} (hη : η ∈ genericPoints X.obj) :
    ∃ (O : B.Scheme) (o : O ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧
      η ∈ Set.range (B.inclusion.map o).base ∧
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B O.obj O.property)
        (((smallEtaleBaseChange B o).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B O.obj O.property)).obj G) := by
  obtain ⟨U, hU, hηU⟩ : ∃ U : X.obj.Opens, IsAffineOpen U ∧ η ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
      X.obj.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
    exact ⟨U, hU, hηU⟩
  obtain ⟨s, hs⟩ := hG ⟨U, hU⟩
  have hηcov : η ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := s.covers ▸ hηU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hηcov
  set f := B.inclusion.map (s.inclusion i) with hf
  have : IsImmersion f := s.isImmersion i
  have : IsAffine U.toScheme := hU
  have hspec : SpectralSpace U.toScheme :=
    Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace U.toScheme
  let ηU : U.toScheme := ⟨η, hηU⟩
  have hηU' : ηU ∈ genericPoints U.toScheme :=
    TopologicalSpace.mem_genericPoints_of_forall_specializes_eq fun y hy =>
      U.ι.isOpenEmbedding.injective
        (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hη _
          (hy.map U.ι.base.hom.continuous))
  set T := U.ι.base ⁻¹' Set.range f.base with hT
  have hTc : Topology.IsConstructible T := s.constructible i
  have hηT : ηU ∈ T := hi
  have hnot : ηU ∉ closure Tᶜ :=
    Topology.notMem_closure_of_mem_genericPoints_of_isConstructible hηU' hTc.compl
      (fun h => h hηT)
  let OU : U.toScheme.Opens := ⟨(closure Tᶜ)ᶜ, isClosed_closure.isOpen_compl⟩
  let O : X.obj.Opens := U.ι ''ᵁ OU
  have hO : (O : Set X.obj) ⊆ Set.range f.base := by
    rintro x ⟨y, hy, rfl⟩
    by_contra hyT
    exact hy (subset_closure hyT)
  have hηO : η ∈ O := ⟨ηU, hnot, rfl⟩
  have hc : B.Contains (f ⁻¹ᵁ O).toScheme :=
    Scheme.size_lt_of_isOpenImmersion (f ⁻¹ᵁ O).ι (s.piece i).property
  let ι' : B.obj (f ⁻¹ᵁ O).toScheme hc ⟶ s.piece i := ObjectProperty.homMk (f ⁻¹ᵁ O).ι
  have hmap : B.inclusion.map (ι' ≫ s.inclusion i) = (f ⁻¹ᵁ O).ι ≫ f := rfl
  refine ⟨B.obj (f ⁻¹ᵁ O).toScheme hc, ι' ≫ s.inclusion i, ?_, ?_, ?_⟩
  · rw [hmap]
    have : IsReduced (B.inclusion.obj X) := ‹IsReduced X.obj›
    exact isOpenImmersion_comp_of_isImmersion_of_subset_range f O hO
  · obtain ⟨p, hp⟩ := hO hηO
    refine ⟨⟨p, show f.base p ∈ O from hp ▸ hηO⟩, ?_⟩
    rw [hmap]
    exact hp
  · exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
      ((smallEtaleSheafPullbackCompIso B _ _ X ι' (s.inclusion i)
        (ModuleCat.{max (u + 1) r} Λ)).app G)
      (isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ ι' _ (hs i))

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- **The dévissage of Step 3 of Tag 03UG.** A constructible flat sheaf `F` of `Λ`-modules on
Mathlib's small étale site of a reduced scheme `X`, for an arbitrary ring `Λ`, is locally constant
with finite projective values on an open neighbourhood of every generic point `η`: there is an
open immersion `o : O ⟶ X` whose image contains `η` such that the transport of `o^{-1} F` to the
small étale site of Stacks 021B of `O` is locally constant with finite projective values. -/
public theorem exists_isOpenImmersion_isFiniteProjectiveLocallyConstant (X : B.Scheme)
    [IsReduced X.obj] {F : EtaleModules.{u, r} Λ X.obj}
    (hF : IsConstructibleFlatEtaleModule B X Λ F) {η : X.obj} (hη : η ∈ genericPoints X.obj) :
    ∃ (O : B.Scheme) (o : O ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧
      η ∈ Set.range (B.inclusion.map o).base ∧
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B O.obj O.property)
        ((etaleModulesToSmallEtale B O Λ).obj
          ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map o)).obj F)) := by
  obtain ⟨O, o, ho, hηo, hloc⟩ :=
    exists_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_isConstructibleFlatModuleSheaf
      B Λ X _ hF hη
  exact ⟨O, o, ho, hηo, Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
    (etaleModulesToSmallEtalePullbackIso B Λ o F).symm hloc⟩

end Stacks.EtaleCohomology

end
