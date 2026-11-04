module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.ChowClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedChowSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedFlatPullback

/-!
# Flat pullback along a represented affine-space bundle is surjective up to rational equivalence

Let `g : A → T` be a morphism of schemes of the big fppf site which is flat of relative
dimension `r` and Zariski-locally on `T` the projection `U × 𝐀^r → U`, with `h_T → B` and
`h_A → B` good in Situation 0EDT. Every `(k + r)`-cycle on `h_A` is rationally equivalent, in
the sense of Stacks 0EQ6 (through the principal divisors at the canonical embeddings of
Stacks 0ENK), to the flat pullback along `h_g` of a `k`-cycle on `h_T`.

## Main results

* `isCanonicallyRationallyEquivalentToZeroWithin_of_cycleGroupEquivScheme_mem`: a cycle on `h_U`
  whose corresponding cycle on `U` under `cycleGroupEquivScheme` is rationally equivalent to zero
  in the sense of Stacks 02RW is a locally finite sum of canonical principal divisors.
* `exists_isCanonicallyRationallyEquivalentToZeroWithin_flatPullbackMap_sub_of_isAffineSpaceBundle`
  says that flat pullback along `h_A → h_T` is surjective modulo rational equivalence.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section RationalEquivalence

variable {D : BaseSpaceDimensionSituation.{u}} {U : BigFppfOver D.site D.base D.base_mem}
    {sX : yoneda.obj U ⟶ D.space} (hX : D.IsGood sX) {C : Stacks.Chow.ChowSituation.{u}}
    {s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S} [LocallyOfFiniteType s₀]

/-- **Rational equivalence on the representing scheme gives rational equivalence on the
represented space.** Let `h_U → B` be good and `s₀ : U → C.S` a δ-compatible scheme situation.
A `k`-cycle on `h_U` whose corresponding `k`-cycle on `U` is rationally equivalent to zero in the
sense of Stacks 02RW is rationally equivalent to zero in the sense of Stacks 0EQ6, the principal
divisors being taken at the canonical embeddings of Stacks 0ENK. -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_of_cycleGroupEquivScheme_mem
    (h : IsDeltaCompatible D U sX C s₀) (k : ℤ) (α : CycleGroup D sX k)
    (hα : cycleGroupEquivScheme sX s₀ h k α ∈ Stacks.Chow.rationalEquivalences C s₀ k) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, u} D sX hX k α Set.univ := by
  set e := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U
  set hU := schemePointsHomeomorph D.site D.base D.base_mem U
  have hsupp : ∀ (V : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).IdealSheafData)
      (hV : IsIntegral V.subscheme),
      subspacePointSet D.site D.base D.base_mem (yoneda.obj U)
          (e.symm (Stacks.Chow.genericPointOf V hV)).subspace = hU ⁻¹' (V.support : Set _) := by
    intro V hV
    rw [Stacks.Chow.support_eq_closure_genericPointOf V hV,
      ← IntegralClosedSubspace.image_subspacePointSet_equivSchemePoints_symm]
    exact (hU.preimage_image _).symm
  obtain ⟨J, V, hV, hdim, hloc, g, hg⟩ := hα
  set W := fun j => e.symm (Stacks.Chow.genericPointOf (V j) (hV j))
  have hVW : ∀ j, Stacks.Chow.genericPointOf (V j) (hV j) =
      (W j).schemeGenericPoint D.site D.base D.base_mem U := fun j =>
    (IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm _ _ _ U _).symm
  choose f hf hfeq using fun j =>
    (W j).exists_cycleClosedPushforward_eq hX s₀ (V j) (hV j) (hVW j) (g j)
  have hk : ∀ j, deltaDimensionClosed D ((W j).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (W j)) Set.univ isClosed_univ =
        ((k + 1 : ℤ) : EInt) := fun j => by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX (W j), h.deltaDimension_eq,
      ← hVW, Stacks.Chow.relativeDimension_genericPointOf C s₀ (V j) (hV j) (hdim j)]
  refine ⟨J, W, ?_, fun j => canonicalPrincipalDivisorCycleAt D ((W j).subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX (W j)) (W j).isIntegralSpace (hf j).unit (hk j),
    fun _ => Set.subset_univ _, fun j => ⟨hk j, (hf j).unit, rfl⟩, ?_⟩
  · convert hloc.preimage_continuous hU.continuous using 1
    exact funext fun j => hsupp (V j) (hV j)
  · refine Subtype.ext (funext fun Z => ?_)
    obtain ⟨x, rfl⟩ := e.symm.surjective Z
    show (cycleGroupEquivScheme sX s₀ h k α).1 x = _
    rw [hg x, cycleFamilySum_apply]
    exact finsum_congr fun j => (hfeq j x).symm

end RationalEquivalence

section AffineSpace

variable {D : BaseSpaceDimensionSituation.{u}}

/-- The represented morphism of a flat morphism of schemes of the site is flat. -/
theorem isFlat_yoneda_map_of_flat {A T : BigFppfOver D.site D.base D.base_mem} (g : A ⟶ T)
    [Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map g)] :
    IsFlat D.site D.base D.base_mem (yoneda.map g) :=
  (holdsOnEveryEtaleChart_yoneda_map_iff D.site D.base D.base_mem
    isEtaleLocalOnSourceAndTarget_flat g).2 inferInstance

/-- **Stacks 02TT for a represented affine-space bundle.** Let `g : A → T` be a morphism of
schemes of the big fppf site which is flat, locally of finite type, of relative dimension `r` and
Zariski-locally on `T` the projection `U × 𝐀^r → U`, and let `h_T → B` and `h_A → B` be good, the
latter over the former. For every `(k + r)`-cycle `α` on `h_A` there is a `k`-cycle `β` on `h_T`
with `h_g^*β - α` a locally finite sum of canonical principal divisors. -/
theorem
    exists_isCanonicallyRationallyEquivalentToZeroWithin_flatPullbackMap_sub_of_isAffineSpaceBundle
    {A T : BigFppfOver D.site D.base D.base_mem} (g : A ⟶ T)
    [LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map g)]
    [Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map g)] (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) r)
    (hbundle : Stacks.Chow.IsAffineSpaceBundle
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) r)
    (sT : yoneda.obj T ⟶ D.space) (hsT : D.IsGood sT) (sA : yoneda.obj A ⟶ D.space)
    (hsA : D.IsGood sA) (hbase : yoneda.map g ≫ sT = sA) (k : ℤ)
    (α : CycleGroup D sA (k + (r : ℤ))) :
    ∃ β : CycleGroup D sT k,
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, u} D sA hsA (k + (r : ℤ))
        (flatPullbackMap D sA hsA sT hsT (yoneda.map g) hbase r (isFlat_yoneda_map_of_flat g)
          ((hasRelativeDimension_yoneda_map_iff D.site D.base D.base_mem g r).2 hrel) k
          (k + (r : ℤ)) rfl β - α) Set.univ := by
  subst hbase
  have hδT := isDeltaCompatible_representedChowSituation D sT hsT
  have hδA := hδT.comp hsT g
  obtain ⟨b, hb⟩ := Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_general
    (representedChowSituation D sT hsT)
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map g ≫ 𝟙 _) (𝟙 _)
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) rfl r hrel hbundle k
    (QuotientAddGroup.mk' _ (cycleGroupEquivScheme _ _ hδA (k + (r : ℤ)) α))
  obtain ⟨β', rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  rw [Stacks.Chow.flatPullbackChow_mk, QuotientAddGroup.mk'_eq_mk'] at hb
  obtain ⟨z, hz, hzeq⟩ := hb
  refine ⟨(cycleGroupEquivScheme sT _ hδT k).symm β', ?_⟩
  refine isCanonicallyRationallyEquivalentToZeroWithin_of_cycleGroupEquivScheme_mem hsA hδA _ _ ?_
  rw [map_sub, cycleGroupEquivScheme_flatPullbackMap hsA hsT g rfl r
    (isFlat_yoneda_map_of_flat g)
    ((hasRelativeDimension_yoneda_map_iff D.site D.base D.base_mem g r).2 hrel) hδT hδA,
    AddEquiv.apply_symm_apply]
  have hz' : Stacks.Chow.flatPullback (representedChowSituation D sT hsT)
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map g ≫ 𝟙 _) (𝟙 _)
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) rfl r hrel k β' -
      cycleGroupEquivScheme _ _ hδA (k + (r : ℤ)) α = -z := by
    rw [← hzeq]
    abel
  exact hz' ▸ neg_mem hz

end AffineSpace

end AlgebraicGeometry.Space

end
