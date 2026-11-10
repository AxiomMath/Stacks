module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAnyCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningBlowupEtaleBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatCompositionUnassumed
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties

/-!
# A flattened strict transform stays flattened after a further blowup

Let `g : T ⟶ W` be an algebraic space over `W`, let `G` be a quasi-coherent `𝒪_T`-module and
let `c : W₁ ⟶ W` be the blowup of `W` in a closed subspace `Z` such that the strict transform
of `G` is of finite presentation and flat over `W₁`.  For a finitely presented closed subspace
`Z' ⊆ W`, the blowup `c₂ : W₂ ⟶ W₁` of `W₁` in `c⁻¹(Z')` composes with `c` to the blowup of `W`
in `Z + Z'` (Stacks 085Y), and the strict transform of `G` along `c₂ ≫ c` is again of finite
presentation and flat, over `W₂`: it is the strict transform along `c₂` of the strict transform
along `c` (Stacks 0868, part (1)), and the latter being flat, its strict transform along `c₂` is
its pullback (Stacks 0865, part (2)), which is of finite presentation and flat over `W₂`
(Stacks 03DO, 05VW).

This is the middle of the second paragraph of the proof of Stacks 087C: there `W` is an affine
étale chart of the base, `c` the blowup produced by the case of schemes, and `Z + Z'` the
inverse image of the centre provided by Stacks 087B.

## Main results

* `AlgebraicGeometry.Space.compl_subspacePointSet_subset_range_of_isBlowupAlong`: a blowup is
  surjective on points over the complement of its centre.
* `AlgebraicGeometry.Space.isCompositeCentre_sumClosedSubspaces`: the sum `Z + Z'` satisfies the
  condition on the composite centre of Stacks 0868 for `c` and `c⁻¹(Z')`.
* `AlgebraicGeometry.Space.exists_isBlowupAlong_sum_isFinitePresentation_isFlatOver`: the
  statement above, by part (1) of Stacks 0868
  (`exists_strictTransformSheaf_comp_iso_unconditional`) and part (2) of Stacks 0865
  (`isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint_unconditional`).

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 085Y](https://stacks.math.columbia.edu/tag/085Y)
* [Stacks Project, Tag 0865](https://stacks.math.columbia.edu/tag/0865)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A blowup is surjective on points over the complement of its centre**, being an isomorphism
there (Stacks 085T, part (1)). -/
theorem compl_subspacePointSet_subset_range_of_isBlowupAlong {W W₁ : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS W.1} {c : W₁ ⟶ W} (hc : IsBlowupAlong B S hS Z c) :
    (subspacePointSet B S hS W.1 Z.1)ᶜ ⊆ Set.range (pointsMap B S hS W₁.1 c.hom) := by
  intro p hp
  set O := openComplementOfClosedSubspace B S hS W Z
  rw [← subspacePointSet_openComplement B S hS W Z] at hp
  obtain ⟨q, rfl⟩ := hp
  have := isIso_fromPreimage_openComplement hc
  obtain ⟨r, hr⟩ := isSurjective_of_isIso B S hS (O.1.fromPreimage c.hom) q
  refine ⟨pointsMap B S hS _ (O.1.preimage c.hom).ι r, ?_⟩
  rw [← pointsMap_comp_apply, ← (Subfunctor.isPullback_preimage c.hom O.1).w,
    pointsMap_comp_apply, hr]

/-- **The sum is a composite centre.**  For the blowup `c : W₁ ⟶ W` of `W` in `Z` and a closed
subspace `Z' ⊆ W`, the points of `Z + Z'` are those of `Z` together with the image of the points
of `c⁻¹(Z')`: off `Z` the blowup is surjective. -/
theorem isCompositeCentre_sumClosedSubspaces {W W₁ : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS W.1} {c : W₁ ⟶ W} (hc : IsBlowupAlong B S hS Z c)
    (Z' : ClosedSubspaces B S hS W.1) :
    IsCompositeCentre B S hS c Z (preimageClosedSubspace c Z')
      (sumClosedSubspaces B S hS W Z Z') := by
  change subspacePointSet B S hS W.1 (sumClosedSubspaces B S hS W Z Z').1 =
    subspacePointSet B S hS W.1 Z.1 ∪
      pointsMap B S hS W₁.1 c.hom '' Set.range (pointsMap B S hS _ (Z'.1.preimage c.hom).ι)
  rw [subspacePointSet_sumClosedSubspaces, range_pointsMap_preimage_ι,
    Set.image_preimage_eq_inter_range]
  apply le_antisymm
  · rintro p (hp | hp)
    · exact Or.inl hp
    · by_cases hpZ : p ∈ subspacePointSet B S hS W.1 Z.1
      · exact Or.inl hpZ
      · exact Or.inr ⟨hp, compl_subspacePointSet_subset_range_of_isBlowupAlong hc hpZ⟩
  · exact Set.union_subset_union_right _ Set.inter_subset_left

/-- **A flattened strict transform stays flattened after a further blowup in a finitely
presented centre**, by Stacks 0865 part (2) and Stacks 0868 part (1).
Let `c : W₁ ⟶ W` be the blowup of `W` in `Z` and let `G` be a quasi-coherent `𝒪_T`-module on
`g : T ⟶ W` whose strict transform along `c` is of finite presentation and flat over `W₁`.
For a finitely presented `Z' ⊆ W` there is a blowup `c₂ : W₂ ⟶ W₁` with `c₂ ≫ c` the blowup of
`W` in `Z + Z'`, along which the strict transform of `G` is of finite presentation and flat
over `W₂`. -/
theorem exists_isBlowupAlong_sum_isFinitePresentation_isFlatOver
    {W T W₁ : AlgebraicSpaces B S hS} (g : T ⟶ W) (G : Modules.{u, u} B S hS T.1 T.2)
    {Z : ClosedSubspaces B S hS W.1} (Z' : ClosedSubspaces B S hS W.1)
    (hZ' : IsFinitePresentation B S hS Z'.1.ι) {c : W₁ ⟶ W} (hc : IsBlowupAlong B S hS Z c)
    (hfp : (strictTransformSheaf B S hS g c (Z.1.preimage c.hom) G).IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (strictTransformPullback B S hS g c).2
      (strictTransformPullbackToBlowUp B S hS g c).hom
      (strictTransformSheaf B S hS g c (Z.1.preimage c.hom) G)) :
    ∃ (W₂ : AlgebraicSpaces B S hS) (c₂ : W₂ ⟶ W₁),
      IsBlowupAlong B S hS (sumClosedSubspaces B S hS W Z Z') (c₂ ≫ c) ∧
      (strictTransformSheaf B S hS g (c₂ ≫ c)
        ((sumClosedSubspaces B S hS W Z Z').1.preimage (c₂ ≫ c).hom) G).IsFinitePresentationOnSite ∧
      IsFlatOver B S hS (strictTransformPullback B S hS g (c₂ ≫ c)).2
        (strictTransformPullbackToBlowUp B S hS g (c₂ ≫ c)).hom
        (strictTransformSheaf B S hS g (c₂ ≫ c)
          ((sumClosedSubspaces B S hS W Z Z').1.preimage (c₂ ≫ c).hom) G) := by
  obtain ⟨W₂, c₂, hc₂⟩ := exists_isBlowupAlong_of_isFinitePresentation
    (preimageClosedSubspace c Z') (isFinitePresentation_ι_preimage c Z' hZ')
  have hY := hc.comp_sumClosedSubspaces hc₂
  obtain ⟨e, -, hblow, cmp, -⟩ := exists_strictTransformSheaf_comp_iso_unconditional B S hS g c c₂
    Z (preimageClosedSubspace c Z') (sumClosedSubspaces B S hS W Z Z') G hc hc₂
    (isCompositeCentre_sumClosedSubspaces hc Z') hY
  set G₁ := strictTransformSheaf B S hS g c (Z.1.preimage c.hom) G
  have hG₁ : G₁.IsQuasicoherentOnSite := have := hfp; inferInstance
  have hiso := isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint_unconditional B S hS
    (strictTransformPullbackToBlowUp B S hS g c) c₂ (preimageClosedSubspace c Z') G₁ hG₁ hc₂
    fun xbar _ =>
      (have := hG₁; (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS _ G₁).1 hflat xbar)
  set Q := (modulePullback B S hS (strictTransformPullbackToSource B S hS
    (strictTransformPullbackToBlowUp B S hS g c) c₂)).obj G₁
  have eQ := cmp ≪≫ (asIso (strictTransformSheafQuotient B S hS
    (strictTransformPullbackToBlowUp B S hS g c) c₂ ((preimageClosedSubspace c Z').1.preimage
      c₂.hom) G₁)).symm
  have hQfp : Q.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B S hS _ _ hfp
  have hQqc : Q.IsQuasicoherentOnSite := have := hQfp; inferInstance
  have hQflat : IsFlatOver B S hS _ (strictTransformPullbackToBlowUp B S hS
      (strictTransformPullbackToBlowUp B S hS g c) c₂).hom Q :=
    have := hG₁
    have := hQqc
    isFlatOver_modulePullback B S hS (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _) G₁ hflat
  set N := strictTransformSheaf B S hS g (c₂ ≫ c)
    ((sumClosedSubspaces B S hS W Z Z').1.preimage (c₂ ≫ c).hom) G
  have hNfp : N.IsFinitePresentationOnSite :=
    (isFinitePresentationOnSite_modulePullback_iso_iff e N).1
      (SheafOfModules.IsFinitePresentationOnSite.of_iso eQ.symm hQfp)
  refine ⟨W₂, c₂, hY, hNfp, ?_⟩
  have hNqc : N.IsQuasicoherentOnSite := have := hNfp; inferInstance
  refine (isFlatOver_modulePullback_iso_iff e _ N hNqc).1 ?_
  rw [hblow]
  exact (isFlatOver_iff_of_iso B S hS _ _ eQ).2 hQflat

end AlgebraicGeometry.Space

end
