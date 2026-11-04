module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinDivisorKeyFormulaCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoringChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusCycleOnDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernRuleSubspaceImagePrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection

/-!
# The component rule of the Gysin map, transported to a member of a presenting family

In Situation 0EDT let `X/B` be good, `ℒ` invertible with a global section `σ`, `E = Z(σ)`, and let
`V ⊆ X` be an integral closed subspace of δ-dimension `k + 2` — a member of the family presenting
a cycle rationally equivalent to zero, as in the proof of Stacks 0ERA.  The refined Gysin map of
Stacks 0ER1 is read through the component rule `AlgebraicGeometry.Space.restrictedSectionChernRule`
of Stacks 0EQJ (`i_*(i^*α) = c₁ ∩ α`), and the reduction of Stacks 0ERA to `V` transports that
rule to `V` by `AlgebraicGeometry.Space.closedSubspaceChernRule`.  This file compares the
transported rule with the rules on `V` that the source's two cases use.

* Off the divisor it **is** the generator rule of the source's choice `s_i = σ|_V` on `V`
  (`closedSubspaceChernRule_restrictedSectionChernRule_eq_memberGeneratorChernRule`):
  both values are cycles `[E ⊓ T]_k` of one closed subspace of `X`, by Stacks 0EQF, once the
  vanishing locus of `σ|_V` is identified with `E ∩ V`
  (`AlgebraicGeometry.Space.vanishingLocus_integralClosedSubspaceRestrictSection`) and the cycle of
  a closed subspace is seen not to depend on the ambient space.
* On the divisor it differs from the canonical rule of `ℒ|_V` by principal divisors
  (`isPrincipalDivisorCycleOfGood_closedSubspaceChernRule_sub_canonicalFirstChernRule`), and so
  does the generator rule
  (`isPrincipalDivisorCycleOfGood_canonicalFirstChernRule_sub_memberGeneratorChernRule`),
  by Stacks 0EPT.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L)

include hL in
/-- The vanishing locus of the restriction of `σ` to an integral closed subspace `V` is the
inverse image of the vanishing locus of `σ`. -/
theorem vanishingLocus_integralClosedSubspaceRestrictSection
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    vanishingLocus D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
        (integralClosedSubspaceRestrict D p hp L V)
        (integralClosedSubspaceRestrictSection D p hp L σ V) =
      interOnClosedSubspace D p hp L σ ⟨V.subspace, V.isClosedSubspace⟩ :=
  (interOnClosedSubspace_eq_zeroScheme D p hp L σ ⟨V.subspace, V.isClosedSubspace⟩ hL).symm

/-- **Stacks 0EPT at the canonical embeddings**, the difference itself: two regular meromorphic
sections of one invertible module on a good integral space have Weil divisors differing by a
principal divisor. -/
theorem isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (τ τ' : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ)
    (hτ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ') {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k
      (canonicalDivisorCycleAt D sY hY hint M hM τ hτ hk -
        canonicalDivisorCycleAt D sY hY hint M hM τ' hτ' hk) := by
  simpa only [one_smul] using
    isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D sY hY hint M hM τ τ' hτ hτ'
      hk 1

/-! ### The cycle of an intersection, read in three ambient spaces -/

section IntersectionCycle

variable {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (F : ClosedSubspaces D.site D.base D.base_mem Y) (k : ℤ)

/-- The cycle of `F ∩ W` formed in `W` and pushed forward to `Y` is the cycle of `F ⊓ W` formed in
`Y`. -/
theorem cycleClosedPushforward_cycleCoeffOfClosedSubspace_preimage_eq_inf
    (W : ClosedSubspaces D.site D.base D.base_mem Y) :
    cycleClosedPushforward D hY.1 W.2.1 (D.isDecentSpace_of_isGood sY hY) W.2.2
        (cycleCoeffOfClosedSubspace D (W.1.ι ≫ sY) (isGood_closedSubspace D sY hY W)
          (F.1.preimage W.1.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem W.1.ι F.1 hY.1 W.2.1 F.2) k
          (canonicalGeometricPoint D.site D.base D.base_mem (F.1.preimage W.1.ι).toFunctor)) =
      cycleCoeffOfClosedSubspace D sY hY (F.1 ⊓ W.1)
        (inf_isClosedSubspace D.site D.base D.base_mem Y hY.1 F W) k
        (canonicalGeometricPoint D.site D.base D.base_mem (F.1 ⊓ W.1).toFunctor) :=
  cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D sY hY W.1 W.2
    (isGood_closedSubspace D sY hY W) (F.1.preimage W.1.ι) _ (F.1 ⊓ W.1)
    (inf_isClosedSubspace D.site D.base D.base_mem Y hY.1 F W)
    (preimageInfHom' F.1 W.1) (preimageInfHom'_comp_ι F.1 W.1) k

variable (V : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor)

/-- The comparison of `(F ∩ V) ⊓ T₀ ⊆ V` with `F ⊓ i_V(T₀) ⊆ Y`: a section of `V` lying in the
inverse image of `F` and in `T₀` is, in `Y`, a section of `F` and of the image of `T₀`. -/
def preimageInfImageHom :
    ((F.1.preimage V.subspace.ι) ⊓ T₀.subspace).toFunctor ⟶
      (F.1 ⊓ (integralClosedSubspaceImage D sY hY V T₀).subspace).toFunctor where
  app U := ↾fun x => ⟨x.1.1, x.2.1, by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (IntegralClosedSubspace.pushforwardIso_hom_comp_ι
        D.site D.base D.base_mem hY.1 V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY)
        V.isClosedSubspace.2 T₀) U) ⟨x.1, x.2.2⟩
    rw [show x.1.1 = (T₀.subspace.ι ≫ V.subspace.ι).app U ⟨x.1, x.2.2⟩ from rfl, ← h]
    exact ((IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hY.1
      V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY) V.isClosedSubspace.2 T₀).hom.app U
        ⟨x.1, x.2.2⟩).2⟩
  naturality _ _ _ := rfl

instance : IsIso (preimageInfImageHom D sY hY F V T₀) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro U
  rw [isIso_iff_bijective]
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1) hxy))
  · set e := IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hY.1
      V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY) V.isClosedSubspace.2 T₀
    set z := e.inv.app U ⟨y.1, y.2.2⟩
    have hz : z.1.1 = y.1 := by
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app
        (IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp
          D.site D.base D.base_mem hY.1 V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY)
          V.isClosedSubspace.2 T₀) U) ⟨y.1, y.2.2⟩
      exact h
    refine ⟨⟨z.1, ?_, z.2⟩, Subtype.ext hz⟩
    change z.1.1 ∈ F.1.obj U
    rw [hz]
    exact y.2.1

/-- The comparison is a morphism over `Y`. -/
theorem preimageInfImageHom_comp_ι :
    preimageInfImageHom D sY hY F V T₀ ≫
        (F.1 ⊓ (integralClosedSubspaceImage D sY hY V T₀).subspace).ι =
      ((F.1.preimage V.subspace.ι) ⊓ T₀.subspace).ι ≫ V.subspace.ι :=
  rfl

/-- The cycle of `(F ∩ V) ⊓ T₀` formed in `V` and pushed forward to `Y` is the cycle of
`F ⊓ i_V(T₀)` formed in `Y`. -/
theorem cycleClosedPushforward_cycleCoeffOfClosedSubspace_preimage_inf_eq_inf_image :
    cycleClosedPushforward D hY.1 V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY)
        V.isClosedSubspace.2
        (cycleCoeffOfClosedSubspace D (V.subspace.ι ≫ sY)
          (isGood_integralClosedSubspace D sY hY V) ((F.1.preimage V.subspace.ι) ⊓ T₀.subspace)
          (inf_isClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor
            V.isClosedSubspace.1
            ⟨F.1.preimage V.subspace.ι, isClosedSubspace_preimage D.site D.base D.base_mem
              V.subspace.ι F.1 hY.1 V.isClosedSubspace.1 F.2⟩
            ⟨T₀.subspace, T₀.isClosedSubspace⟩) k
          (canonicalGeometricPoint D.site D.base D.base_mem
            ((F.1.preimage V.subspace.ι) ⊓ T₀.subspace).toFunctor)) =
      cycleCoeffOfClosedSubspace D sY hY
        (F.1 ⊓ (integralClosedSubspaceImage D sY hY V T₀).subspace)
        (inf_isClosedSubspace D.site D.base D.base_mem Y hY.1 F
          ⟨(integralClosedSubspaceImage D sY hY V T₀).subspace,
            (integralClosedSubspaceImage D sY hY V T₀).isClosedSubspace⟩) k
        (canonicalGeometricPoint D.site D.base D.base_mem
          (F.1 ⊓ (integralClosedSubspaceImage D sY hY V T₀).subspace).toFunctor) :=
  cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D sY hY V.subspace V.isClosedSubspace
    (isGood_integralClosedSubspace D sY hY V) _ _ _ _
    (preimageInfImageHom D sY hY F V T₀) (preimageInfImageHom_comp_ι D sY hY F V T₀) k

end IntersectionCycle

/-! ### The member's own pair `(ℒ|_V, σ|_V)` -/

section Member

variable (k : ℤ) (V : IntegralClosedSubspace D.site D.base D.base_mem X)

include hL in
/-- `ℒ|_V` is invertible (Stacks 0B8P). -/
theorem isInvertibleModule_memberRestrict :
    IsInvertibleModule (B := D.site)
      ⟨V.subspace.toFunctor, (isGood_integralClosedSubspace D p hp V).1⟩
      (integralClosedSubspaceRestrict D p hp L V) :=
  isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL V

/-- The δ-dimension of `V` computed on `V`. -/
theorem deltaDimensionClosed_member (hVdim : deltaDimension D p V = k + 1 + 1) :
    deltaDimensionClosed D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
      Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt) :=
  (deltaDimensionClosed_univ_integralClosedSubspace D p hp V).trans
    (congrArg (fun m : ℤ => (m : EInt)) hVdim)

/-- **The generator rule on the member `V`**: the component rule of Stacks 0EQJ on `V` given by
the source's choice of generators `s_i = σ|_V` of `(ℒ|_V)_ξ` off the vanishing locus of `σ|_V`,
`AlgebraicGeometry.Space.generatorChernRule` at
`AlgebraicGeometry.Space.sectionGeneratorUnit`. -/
abbrev memberGeneratorChernRule (hVdim : deltaDimension D p V = k + 1 + 1) :
    FirstChernComponentCycleRule D (V.subspace.ι ≫ p) k :=
  generatorChernRule D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
    V.isIntegralSpace (integralClosedSubspaceRestrict D p hp L V)
    (isInvertibleModule_memberRestrict D p hp L hL V) (deltaDimensionClosed_member D p hp k V hVdim)
    (sectionGeneratorUnit D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
      V.isIntegralSpace (integralClosedSubspaceRestrict D p hp L V)
      (isInvertibleModule_memberRestrict D p hp L hL V)
      (integralClosedSubspaceRestrictSection D p hp L σ V))

include hL in
/-- An integral closed subspace `T₀` of `V` lies in the vanishing locus of `σ|_V` exactly when
its image in `X` lies in the vanishing locus of `σ`. -/
theorem le_vanishingLocus_member_iff
    (T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor) :
    T₀.subspace ≤ (vanishingLocus D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
        (integralClosedSubspaceRestrict D p hp L V)
        (integralClosedSubspaceRestrictSection D p hp L σ V)).1 ↔
      (integralClosedSubspaceImage D p hp V T₀).subspace ≤ (vanishingLocus D p hp L σ).1 := by
  rw [vanishingLocus_integralClosedSubspaceRestrictSection D p hp L σ hL V]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine le_of_subspacePointSet_subset_of_integral D hp.1 _ (vanishingLocus D p hp L σ).2 _ ?_
    rw [IntegralClosedSubspace.subspacePointSet_pushforward, Set.image_subset_iff]
    refine (subspacePointSet_mono_of_le D h).trans ?_
    rw [subspacePointSet_preimage]
  · refine le_of_subspacePointSet_subset_of_integral D V.isClosedSubspace.1 _
      (interOnClosedSubspace D p hp L σ ⟨V.subspace, V.isClosedSubspace⟩).2 _ ?_
    rw [subspacePointSet_preimage, ← Set.image_subset_iff,
      ← IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem hp.1
        V.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp) V.isClosedSubspace.2 T₀]
    exact subspacePointSet_mono_of_le D h

include hL in
/-- **Off the divisor the transported Gysin rule is the member's generator rule, exactly.**  Let
`V ⊆ X` be an integral closed subspace of δ-dimension `k + 2` and `T₀ ⊆ V` one of δ-dimension
`k + 1` not contained in the vanishing locus of `σ|_V`.  The rule
`AlgebraicGeometry.Space.restrictedSectionChernRule` of `(ℒ, σ)` on `X`, transported to `V` by
`AlgebraicGeometry.Space.closedSubspaceChernRule`, takes at `T₀` the same cycle as the generator
rule of the source's choice `s_i = σ|_V` on `V`.

Both are the Weil divisor of a restricted global section, `σ|_{i_V(T₀)}` on `X` and
`(σ|_V)|_{T₀}` on `V`.  They are compared after pushing forward to `X`, where both become the
cycle `[E ⊓ i_V(T₀)]_k` of Stacks 0EE9 of one closed subspace of `X`: on `X` by Stacks 0EQF read
through `AlgebraicGeometry.Space.gysinPushforwardComponentCoeff`, on `V` by the same followed by
the identification of the vanishing locus of `σ|_V` with `E ∩ V`
(`AlgebraicGeometry.Space.vanishingLocus_integralClosedSubspaceRestrictSection`) and the
independence of the cycle of a closed subspace from the ambient space.  Pushforward along a closed
immersion is injective. -/
theorem closedSubspaceChernRule_restrictedSectionChernRule_eq_memberGeneratorChernRule
    (chern : FirstChernComponentCycleRule D p k) (hVdim : deltaDimension D p V = k + 1 + 1)
    (T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor)
    (hT₀ : deltaDimension D (V.subspace.ι ≫ p) T₀ = k + 1)
    (hT₀E : ¬ T₀.subspace ≤ (vanishingLocus D (V.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp V) (integralClosedSubspaceRestrict D p hp L V)
      (integralClosedSubspaceRestrictSection D p hp L σ V)).1) :
    closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
        (restrictedSectionChernRule D p hp L σ hL k chern) T₀ hT₀ =
      memberGeneratorChernRule D p hp L σ hL k V hVdim T₀ hT₀ := by
  have hV := isGood_integralClosedSubspace D p hp V
  have hT : deltaDimension D p (integralClosedSubspaceImage D p hp V T₀) = k + 1 :=
    (deltaDimension_integralClosedSubspaceImage D p hp V T₀).trans hT₀
  have hTE : ¬ (integralClosedSubspaceImage D p hp V T₀).subspace ≤
      (vanishingLocus D p hp L σ).1 := fun h =>
    hT₀E ((le_vanishingLocus_member_iff D p hp L σ hL V T₀).2 h)
  have h₁ : cycleClosedPushforward D hp.1 V.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
      V.isClosedSubspace.2
      (firstChernComponentCycle D (V.subspace.ι ≫ p) hV k
        (closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
          (restrictedSectionChernRule D p hp L σ hL k chern)) T₀).1 =
      cycleCoeffOfClosedSubspace D p hp
        ((vanishingLocus D p hp L σ).1 ⊓ (integralClosedSubspaceImage D p hp V T₀).subspace)
        (inf_isClosedSubspace D.site D.base D.base_mem X hp.1 (vanishingLocus D p hp L σ)
          ⟨(integralClosedSubspaceImage D p hp V T₀).subspace,
            (integralClosedSubspaceImage D p hp V T₀).isClosedSubspace⟩) k
        (canonicalGeometricPoint D.site D.base D.base_mem
          ((vanishingLocus D p hp L σ).1 ⊓
            (integralClosedSubspaceImage D p hp V T₀).subspace).toFunctor) := by
    rw [cycleClosedPushforward_firstChernComponentCycle_closedSubspaceChernRule D p hp
        V.subspace V.isClosedSubspace k _ T₀,
      ← gysinPushforwardComponentCoeff_eq_firstChernComponentCycle D p hp L σ hL k chern,
      gysinPushforwardComponentCoeff_of_not_le D p hp L σ k chern hT hTE]
    exact cycleClosedPushforward_cycleCoeffOfClosedSubspace_preimage_eq_inf D p hp
      (vanishingLocus D p hp L σ) k
      ⟨(integralClosedSubspaceImage D p hp V T₀).subspace,
        (integralClosedSubspaceImage D p hp V T₀).isClosedSubspace⟩
  have hinjV := injective_cycleGroupClosedPushforward D hp.1 V.isClosedSubspace.1
    (D.isDecentSpace_of_isGood p hp) V.isClosedSubspace.2 p hp.2.2 (V.subspace.ι ≫ p) rfl k
  refine injective_cycleGroupClosedPushforward D hV.1 T₀.isClosedSubspace.1
    (D.isDecentSpace_of_isGood _ hV) T₀.isClosedSubspace.2 _ hV.2.2 _ rfl k ?_
  refine (firstChernComponentCycle_of_deltaDimension_eq D (V.subspace.ι ≫ p) hV k _ hT₀).symm.trans
    (Eq.trans ?_ (firstChernComponentCycle_of_deltaDimension_eq D (V.subspace.ι ≫ p) hV k _ hT₀))
  refine hinjV (Subtype.ext (h₁.trans (Eq.symm ?_)))
  change cycleClosedPushforward D hp.1 V.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
    V.isClosedSubspace.2 _ = _
  rw [memberGeneratorChernRule,
    ← restrictedSectionChernRule_generatorChernRule D (V.subspace.ι ≫ p) hV V.isIntegralSpace
      (integralClosedSubspaceRestrict D p hp L V)
      (isInvertibleModule_memberRestrict D p hp L hL V)
      (deltaDimensionClosed_member D p hp k V hVdim)
      (integralClosedSubspaceRestrictSection D p hp L σ V)
      (isInvertibleModule_memberRestrict D p hp L hL V),
    ← gysinPushforwardComponentCoeff_eq_firstChernComponentCycle D (V.subspace.ι ≫ p) hV
      (integralClosedSubspaceRestrict D p hp L V)
      (integralClosedSubspaceRestrictSection D p hp L σ V)
      (isInvertibleModule_memberRestrict D p hp L hL V) k,
    gysinPushforwardComponentCoeff_of_not_le D (V.subspace.ι ≫ p) hV
      (integralClosedSubspaceRestrict D p hp L V)
      (integralClosedSubspaceRestrictSection D p hp L σ V)
      k _ hT₀ hT₀E,
    cycleClosedPushforward_cycleCoeffOfClosedSubspace_preimage_eq_inf D (V.subspace.ι ≫ p) hV
      _ k ⟨T₀.subspace, T₀.isClosedSubspace⟩]
  rw [vanishingLocus_integralClosedSubspaceRestrictSection D p hp L σ hL V]
  exact cycleClosedPushforward_cycleCoeffOfClosedSubspace_preimage_inf_eq_inf_image D p hp
    (vanishingLocus D p hp L σ) k V T₀

include hL in
/-- **The member's generator rule and the canonical rule differ by principal divisors.**  At an
integral closed subspace `T₀ ⊆ V` of δ-dimension `k + 1` both rules are Weil divisors of regular
meromorphic sections of `(ℒ|_V)|_{T₀}` (Stacks 0EQE), so they differ by a principal divisor on
`T₀` at the canonical embeddings (Stacks 0EPT). -/
theorem isPrincipalDivisorCycleOfGood_canonicalFirstChernRule_sub_memberGeneratorChernRule
    (hVdim : deltaDimension D p V = k + 1 + 1)
    (T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor)
    (hT₀ : deltaDimension D (V.subspace.ι ≫ p) T₀ = k + 1) :
    IsPrincipalDivisorCycleOfGood D (T₀.subspace.ι ≫ V.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D (V.subspace.ι ≫ p)
        (isGood_integralClosedSubspace D p hp V) T₀)
      T₀.isIntegralSpace k
      (canonicalFirstChernRule D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
          (integralClosedSubspaceRestrict D p hp L V)
          (isInvertibleModule_memberRestrict D p hp L hL V) k T₀ hT₀ -
        memberGeneratorChernRule D p hp L σ hL k V hVdim T₀ hT₀) := by
  have hcod := codimension_integralClosedSubspaceSupport_eq_one D (V.subspace.ι ≫ p)
    (isGood_integralClosedSubspace D p hp V) V.isIntegralSpace
    (deltaDimensionClosed_member D p hp k V hVdim) hT₀
  rw [show memberGeneratorChernRule D p hp L σ hL k V hVdim T₀ hT₀ = _ from dif_pos hcod]
  exact isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub D _ _ T₀.isIntegralSpace
    _ _ _ _ _ _ _

include hL in
/-- **On the divisor the transported Gysin rule and the member's canonical rule differ by
principal divisors.**  Let `T₀ ⊆ V` be an integral closed subspace of δ-dimension `k + 1` whose
image `T = i_V(T₀)` lies in `E = Z(σ)`.  The Gysin rule of Stacks 0ER1 takes at `T` the free
clause (1)(b), the Weil divisor `div_{ℒ|_T}(t_T)` of the regular meromorphic section of
Stacks 0EPQ; transported to `T₀` it differs from the canonical rule of Stacks 0EQJ on `V` at `T₀`
by a principal divisor at the canonical embeddings.

On `T` the Gysin value and the canonical rule on `X` are two Weil divisors of regular sections of
`ℒ|_T` (Stacks 0EPT), and the canonical rules on `X` and on `V` differ by a principal divisor on
`T`; the sum is carried to `T₀` along the identification `T ≅ T₀`. -/
theorem isPrincipalDivisorCycleOfGood_closedSubspaceChernRule_sub_canonicalFirstChernRule
    (T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor)
    (hT₀ : deltaDimension D (V.subspace.ι ≫ p) T₀ = k + 1)
    (hTE : (integralClosedSubspaceImage D p hp V T₀).subspace ≤ (vanishingLocus D p hp L σ).1) :
    IsPrincipalDivisorCycleOfGood D (T₀.subspace.ι ≫ V.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D (V.subspace.ι ≫ p)
        (isGood_integralClosedSubspace D p hp V) T₀)
      T₀.isIntegralSpace k
      (closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
          (restrictedSectionChernRule D p hp L σ hL k (restrictedDivisorCycle D p hp L k hL))
          T₀ hT₀ -
        canonicalFirstChernRule D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
          (integralClosedSubspaceRestrict D p hp L V)
          (isInvertibleModule_memberRestrict D p hp L hL V) k T₀ hT₀) := by
  have hT : deltaDimension D p (integralClosedSubspaceImage D p hp V T₀) = k + 1 :=
    (deltaDimension_integralClosedSubspaceImage D p hp V T₀).trans hT₀
  have hTg := isGood_integralClosedSubspace D p hp (integralClosedSubspaceImage D p hp V T₀)
  have hT₀g := isGood_integralClosedSubspace D (V.subspace.ι ≫ p)
    (isGood_integralClosedSubspace D p hp V) T₀
  have hi : IsPrincipalDivisorCycleOfGood D
      ((integralClosedSubspaceImage D p hp V T₀).subspace.ι ≫ p) hTg
      (integralClosedSubspaceImage D p hp V T₀).isIntegralSpace k
      (restrictedDivisorCycle D p hp L k hL (integralClosedSubspaceImage D p hp V T₀) hT -
        canonicalFirstChernRule D p hp L hL k (integralClosedSubspaceImage D p hp V T₀) hT) :=
    isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub D _ hTg
      (integralClosedSubspaceImage D p hp V T₀).isIntegralSpace _
      (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL _) _ _
      (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem hTg.1
        (integralClosedSubspaceImage D p hp V T₀).isIntegralSpace
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hTg) _
        (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL _))
      (isRegularMeromorphicSection_componentMeromorphicSection p hp
        (subspaceDivisorSetupOfIsGood D p hp) L hL (integralClosedSubspaceImage D p hp V T₀)) _
  have hsum := hi.add
    (isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_pushforwardCycleTransport
      D p hp V T₀ L hL k hT 1)
  rw [one_smul, sub_add_sub_cancel] at hsum
  have htr := isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D _ hTg _ hT₀g
    (integralClosedSubspaceImage D p hp V T₀).isIntegralSpace T₀.isIntegralSpace
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hp.1 V.isClosedSubspace.1
      (D.isDecentSpace_of_isGood p hp) V.isClosedSubspace.2 T₀).symm
    (pushforwardIso_symm_hom_comp D p hp V.subspace V.isClosedSubspace T₀) k hsum
  rw [map_sub] at htr
  convert htr using 2
  · rw [closedSubspaceChernRule, restrictedSectionChernRule_of_le D p hp L σ hL k _ _ hTE]
  · exact Subtype.ext (cycleClosedPushforward_hom_comp_inv_eq_self D hT₀g.1 hTg.1
      (D.isDecentSpace_of_isGood _ hT₀g) (D.isDecentSpace_of_isGood _ hTg)
      (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hp.1 V.isClosedSubspace.1
        (D.isDecentSpace_of_isGood p hp) V.isClosedSubspace.2 T₀).symm _).symm

end Member

end AlgebraicGeometry.Space

end
