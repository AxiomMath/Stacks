module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedClosedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeComponentCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# Flat pullback on a represented space and on the representing scheme

Let `U` and `V` be schemes of the big fppf site with `h_U → B` and `h_V → B` good in
Situation 0EDT, and let `C` be a base situation of Chapter 42 whose dimension functions compute
`δ_{h_U/B}` and `δ_{h_V/B}` (`AlgebraicGeometry.Space.IsDeltaCompatible`). This file compares the
flat pullback of cycles of Stacks 0EP8 along a morphism `h_f : h_U → h_V` with the flat pullback
of Stacks 02RB along `f`.

The multiplicities of Stacks 0EE9 are lengths of étale local rings at geometric points. On a
represented space they are lengths of local rings of the scheme: a closed subspace `Y ⊆ h_U` cut
out by a closed immersion `i : Z → U` is isomorphic to `h_Z`, that isomorphism is an étale chart
of `Y`, and Stacks 0EE1 reads the length at a geometric point on any étale chart. Hence the cycle
`[Y]_k` of Stacks 0EE9 is the cycle `[Z]_k` of Stacks 02QU; at a point of `Z` which is not a
generic point of a component both coefficients vanish, the local ring having positive dimension
and so infinite length.

The inverse image of the closed subspace cut out by `j : R → V` along `h_f` is the closed
subspace cut out by the inverse image `f⁻¹𝓘_R` of the ideal sheaf, because inverse image of
ideal sheaves is left adjoint to direct image. Flatness and relative dimension of `h_f` are
flatness and relative dimension of `f`, the second read on the identity charts. So the
multiplicity of Stacks 0EP8 is the coefficient of the cycle of the scheme-theoretic inverse image
of the reduced closure of a point, and the pullback formulas agree: in the sum
`∑_W α_W [f^{-1}(W)]` only the term at the image of the point survives, by flatness.

## Main results

* `AlgebraicGeometry.Space.geometricLength_unit_eq_length_stalk_of_iso`: the length of the
  structure sheaf of `F ≅ h_Z` at a geometric point is the length of the local ring of `Z`.
* `AlgebraicGeometry.Space.cycleGroupEquivScheme_closedSubspaceCycle`: `[Y]_k` corresponds to
  `[Z]_k` under `Z_k(h_U) ≅ Z_k(U)`.
* `AlgebraicGeometry.Space.preimage_range_yoneda_map_eq_range`: the inverse image of a closed
  subspace cut out by a closed immersion is cut out by the inverse image ideal sheaf.
* `AlgebraicGeometry.Space.hasRelativeDimension_yoneda_map_iff`: relative dimension of `h_f` is
  relative dimension of `f`.
* `AlgebraicGeometry.Space.flatPullbackMult_equivSchemePoints_symm`: the multiplicity of
  Stacks 0EP8 is the coefficient of the cycle of the scheme-theoretic inverse image.
* `AlgebraicGeometry.Space.cycleGroupEquivScheme_flatPullbackMap`: flat pullback along `h_f`,
  Stacks 0EP8, is flat pullback along `f`, Stacks 02RB.
* `AlgebraicGeometry.Space.flatPullbackMap_closedSubspaceCycle_of_yoneda`: the cycle identity
  `h_f^*[Y]_m = [h_f^{-1}(Y)]_{m+r}` of Stacks 0EPB, part (1), for a closed subspace `Y ⊆ h_V`,
  from Stacks 02RE, part (1).

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Length

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The multiplicity of a represented algebraic space at a point is the length of the local
ring of the scheme.** If `F ≅ h_Z`, the length of `𝒪_F` at a geometric point `ȳ` of `F` lying
over the point corresponding to `ζ ∈ Z`, Stacks 0EE1, is the length of `𝒪_{Z, ζ}` over itself:
the isomorphism is an étale chart of `F` and `ζ` is a point of it over `ȳ`. -/
theorem geometricLength_unit_eq_length_stalk_of_iso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {Z : BigFppfOver B S hS} (e : yoneda.obj Z ≅ F)
    (y : GeometricPoint B S hS F) (ζ : (BigFppfOver.toScheme B S hS).obj Z)
    (hy : y.image = pointsMap B S hS (yoneda.obj Z) e.hom ((pointsEquivScheme B S hS Z).symm ζ)) :
    geometricLength B S hS ⟨F, hF⟩ y (SheafOfModules.unit _) =
      Module.length (((BigFppfOver.toScheme B S hS).obj Z).presheaf.stalk ζ)
        (((BigFppfOver.toScheme B S hS).obj Z).presheaf.stalk ζ) :=
  geometricLength_unit_eq_length_stalk ⟨F, hF⟩ y
    (⟨CostructuredArrow.mk e.hom, presheaf_etale_of_iso B S hS e⟩ : SmallEtale B S hS F) ζ
    (by rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]; exact hy.symm)

end Length

/-- A point of `h_R` pushed along `h_R ≅ Y ⊆ h_U` lies over its image under `R → U`. -/
private theorem pointsToScheme_pointsMap_pointsMap_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {R U : BigFppfOver B S hS} (i : R ⟶ U) (Y : Subfunctor (yoneda.obj U))
    (e : yoneda.obj R ≅ Y.toFunctor) (he : e.hom ≫ Y.ι = yoneda.map i)
    (z : (BigFppfOver.toScheme B S hS).obj R) :
    pointsToScheme B S hS U (pointsMap B S hS Y.toFunctor Y.ι
      (pointsMap B S hS (yoneda.obj R) e.hom ((pointsEquivScheme B S hS R).symm z))) =
        (BigFppfOver.toScheme B S hS).map i z := by
  rw [← pointsMap_comp_apply, he, pointsToScheme_pointsMap]
  exact congrArg _ ((pointsEquivScheme B S hS R).apply_symm_apply z)

section ClosedSubspaceCycle

variable {D : BaseSpaceDimensionSituation.{u}} {U : BigFppfOver D.site D.base D.base_mem}
    {sX : yoneda.obj U ⟶ D.space} (hX : D.IsGood sX) {C : Stacks.Chow.ChowSituation.{u}}
    {s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S} [LocallyOfFiniteType s₀]

/-- **The cycle of a closed subspace of a represented space is the cycle of the closed
subscheme.** Let `Y ⊆ h_U` be the closed subspace cut out by a closed immersion of schemes
`i : Z → U`. Under `Z_k(h_U) ≅ Z_k(U)`, the `k`-cycle `[Y]_k` of Stacks 0EE9, whose coefficients
are lengths at geometric points, is the `k`-cycle `[Z]_k` of Stacks 02QU, whose coefficients are
lengths of local rings. -/
theorem cycleGroupEquivScheme_closedSubspaceCycle (h : IsDeltaCompatible D U sX C s₀)
    {Z : BigFppfOver D.site D.base D.base_mem} (i : Z ⟶ U)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme D.site D.base D.base_mem).map i)]
    (Y : Subfunctor (yoneda.obj U)) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (hYi : Y = Subfunctor.range (yoneda.map i)) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt)) :
    cycleGroupEquivScheme sX s₀ h k (closedSubspaceCycle D sX hX Y hY k hdim) =
      Stacks.Chow.cycleAssociatedToClosedSubscheme C s₀
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map i) k := by
  classical
  obtain ⟨e, he⟩ := exists_iso_yoneda_of_eq_range D.site D.base D.base_mem i Y hYi
  set i₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map i
  set eU := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U
  set eZ := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem Z
  have hZalg := isAlgebraicSpace_yoneda D.site D.base D.base_mem Z
  have hYdec : IsDecentSpace D.site D.base D.base_mem Y.toFunctor :=
    isDecentSpace_of_relativelyRepresentable D.site D.base D.base_mem hY.1 _ hY.2.1
      (D.isDecentSpace_of_isGood sX hX)
  set Φ := IntegralClosedSubspace.equivOfIso _ _ _ hZalg hY.1 (isDecentSpace_yoneda _ _ _ Z) hYdec e
  have hamb : ∀ ζ, (Φ (eZ.symm ζ)).ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem (yoneda.obj Z) e.hom
        ((pointsEquivScheme D.site D.base D.base_mem Z).symm ζ) := by
    intro ζ
    rw [IntegralClosedSubspace.ambientGenericPoint_equivOfIso]
    congr 1
    rw [Equiv.eq_symm_apply]
    exact IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm _ _ _ Z ζ
  have himg : ∀ ζ, (closedSubspaceComponentImage D sX hX Y hY (Φ (eZ.symm ζ))).schemeGenericPoint
      D.site D.base D.base_mem U = i₀ ζ := by
    intro ζ
    rw [IntegralClosedSubspace.schemeGenericPoint_eq_pointsToScheme,
      IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem hX.1 hY.1,
      hamb]
    exact pointsToScheme_pointsMap_pointsMap_eq D.site D.base D.base_mem i Y e he ζ
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  show (closedSubspaceCycle D sX hX Y hY k hdim).1 (eU.symm x) =
    Stacks.Chow.closedSubschemeCycleCoeff C s₀ i₀ k x
  by_cases hx : x ∈ Set.range i₀
  · obtain ⟨ζ, rfl⟩ := hx
    have hW : eU.symm (i₀ ζ) = closedSubspaceComponentImage D sX hX Y hY (Φ (eZ.symm ζ)) := by
      rw [Equiv.symm_apply_eq, IntegralClosedSubspace.equivSchemePoints_apply, himg]
    rw [hW, closedSubspaceCycle_apply_closedSubspaceComponentImage, ← hW, h.deltaDimension_eq,
      IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm,
      geometricLength_unit_eq_length_stalk_of_iso hY.1 e _ ζ
        (by rw [canonicalGeometricPoint_image, hamb])]
    unfold Stacks.Chow.closedSubschemeCycleCoeff
    by_cases hgen : ζ ∈ genericPoints ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Z)
    · by_cases hk : Stacks.Chow.relativeDimension C.dimensionFunction s₀ (i₀ ζ) = k
      · have hex : ∃ ξ : genericPoints ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Z),
            i₀ ξ.1 = i₀ ζ ∧ Stacks.Chow.relativeDimension C.dimensionFunction s₀ (i₀ ζ) = k :=
          ⟨⟨ζ, hgen⟩, rfl, hk⟩
        have hch : Classical.choose hex = ⟨ζ, hgen⟩ :=
          Subtype.ext (i₀.isClosedEmbedding.injective (Classical.choose_spec hex).1)
        rw [ite_eq_left hk, dite_eq_left hex, hch,
          Stacks.Chow.componentMultiplicity_eq_length_stalk]
      · rw [ite_eq_right hk, dite_eq_right (fun ⟨_, _, h⟩ => hk h)]
    · rw [dite_eq_right fun ⟨ξ, hξ, _⟩ =>
        hgen (by rw [← i₀.isClosedEmbedding.injective hξ]; exact ξ.2)]
      have htop :
          Module.length (((BigFppfOver.toScheme D.site D.base D.base_mem).obj Z).presheaf.stalk ζ)
            (((BigFppfOver.toScheme D.site D.base D.base_mem).obj Z).presheaf.stalk ζ) = ⊤ := by
        by_contra hne
        apply hgen
        rw [← ringKrullDim_stalk_eq_zero_iff_mem_genericPoints]
        have : IsArtinianRing
            (((BigFppfOver.toScheme D.site D.base D.base_mem).obj Z).presheaf.stalk ζ) :=
          (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 hne)).2
        exact ringKrullDimZero_iff_ringKrullDim_eq_zero.1 inferInstance
      split_ifs
      · rw [htop]
        rfl
      · rfl
  · rw [closedSubspaceCycle_apply_eq_zero_of_forall_ne]
    · unfold Stacks.Chow.closedSubschemeCycleCoeff
      rw [dite_eq_right (fun ⟨ξ, hξ, _⟩ => hx ⟨ξ.1, hξ⟩)]
    · intro W' hW'
      apply hx
      obtain ⟨V, rfl⟩ := Φ.surjective W'
      refine ⟨V.schemeGenericPoint D.site D.base D.base_mem Z, ?_⟩
      have h₁ := himg (V.schemeGenericPoint D.site D.base D.base_mem Z)
      rw [show eZ.symm (V.schemeGenericPoint D.site D.base D.base_mem Z) = V from
        eZ.symm_apply_apply V, hW'] at h₁
      rw [← h₁, IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]

end ClosedSubspaceCycle

section Morphisms

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of a closed subscheme.** Let `j : R → U` be a closed immersion of schemes
of the site and `f : U' → U` a morphism of the site. The inverse image along `h_f` of the closed
subspace of `h_U` cut out by `j` is the closed subspace of `h_{U'}` cut out by any closed
immersion `j' : R' → U'` whose ideal sheaf is the inverse image `f⁻¹𝓘_R` of the ideal sheaf of
`j`: a point `k` of `h_{U'}` factors through `j'` exactly when `𝓘_R` vanishes on `k ∘ f`, and the
inverse image of ideal sheaves is left adjoint to their direct image. -/
theorem preimage_range_yoneda_map_eq_range {R U U' R' : BigFppfOver B S hS} (j : R ⟶ U)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] (f : U' ⟶ U)
    (j' : R' ⟶ U')
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')]
    (hker : ((BigFppfOver.toScheme B S hS).map j').ker =
      ((BigFppfOver.toScheme B S hS).map j).ker.comap ((BigFppfOver.toScheme B S hS).map f)) :
    (Subfunctor.range (yoneda.map j)).preimage (yoneda.map f) =
      Subfunctor.range (yoneda.map j') := by
  ext T k
  show (yoneda.map f).app T k ∈ (Subfunctor.range (yoneda.map j)).obj T ↔ _
  rw [mem_range_yoneda_map_iff B S hS j inferInstance, mem_range_yoneda_map_iff B S hS j'
    inferInstance, hker]
  show _ ≤ ((BigFppfOver.toScheme B S hS).map (k ≫ f)).ker ↔ _
  have hk : ((BigFppfOver.toScheme B S hS).map (k ≫ f)).ker =
      ((BigFppfOver.toScheme B S hS).map k).ker.map ((BigFppfOver.toScheme B S hS).map f) := by
    rw [CategoryTheory.Functor.map_comp,
      ← Scheme.IdealSheafData.map_bot ((BigFppfOver.toScheme B S hS).map k ≫ _),
      ← Scheme.IdealSheafData.map_bot ((BigFppfOver.toScheme B S hS).map k),
      Scheme.IdealSheafData.map_comp]
  rw [hk, Scheme.IdealSheafData.le_map_iff_comap_le]

/-- The inverse image along `h_f` of the range of `h_j` is the range of `h_{j'}` for a closed
immersion `j'` whose ideal sheaf is the inverse image of that of `j`. -/
private theorem exists_closedImmersion_ker_comap_preimage_range {R U U' : BigFppfOver B S hS}
    (j : R ⟶ U) [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (f : U' ⟶ U) : ∃ (R' : BigFppfOver B S hS) (j' : R' ⟶ U'),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j') ∧
      ((BigFppfOver.toScheme B S hS).map j').ker =
        ((BigFppfOver.toScheme B S hS).map j).ker.comap ((BigFppfOver.toScheme B S hS).map f) ∧
      (Subfunctor.range (yoneda.map j)).preimage (yoneda.map f) =
        Subfunctor.range (yoneda.map j') := by
  obtain ⟨R', j', hj', hker'⟩ := exists_closedImmersion_ker_eq B S hS U'
    (((BigFppfOver.toScheme B S hS).map j).ker.comap ((BigFppfOver.toScheme B S hS).map f))
  exact ⟨R', j', hj', hker', preimage_range_yoneda_map_eq_range B S hS j f j' hker'⟩

/-- **Relative dimension of a represented morphism.** A morphism of schemes `k` of the site,
locally of finite type, has relative dimension `r` in the sense of Stacks 02NJ exactly when
`h_k` has relative dimension `r` in the sense of Stacks 04NM and 06LR: the latter is read on the
identity charts, where it is the local dimension of the fibres of `k`. -/
theorem hasRelativeDimension_yoneda_map_iff {V U : BigFppfOver B S hS} (k : V ⟶ U)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k)] (r : ℕ) :
    HasRelativeDimension r B S hS (yoneda.map k) ↔
      AlgebraicGeometry.RelativeDimension ((BigFppfOver.toScheme B S hS).map k) r := by
  have hpt : ∀ v, HasRelativeDimensionAt (r : ℕ∞) B S hS (yoneda.map k)
      ((pointsEquivScheme B S hS V).symm v) ↔
        topologicalKrullDimAt (((BigFppfOver.toScheme B S hS).map k).fiber
            ((BigFppfOver.toScheme B S hS).map k v))
          (((BigFppfOver.toScheme B S hS).map k).asFiber v) = ((r : ℕ∞) : WithBot ℕ∞) := by
    intro v
    have h := hasRelativeDimensionAt_pointsMap_iff B S hS (r : ℕ∞) (yoneda.map k) V U
      (yoneda.map (𝟙 V)) (yoneda.map (𝟙 U)) k (presheaf_yoneda_map_id_etale B S hS V)
      (presheaf_yoneda_map_id_etale B S hS U) (by simp) v
    rwa [CategoryTheory.Functor.map_id, pointsMap_id, id_eq] at h
  rw [relativeDimension_iff_forall_topologicalKrullDimAt]
  constructor
  · intro h v
    exact (hpt v).1 (h _)
  · intro h p
    rw [← (pointsEquivScheme B S hS V).symm_apply_apply p]
    exact (hpt _).2 (h _)

end Morphisms

section FlatPullback

variable {D : BaseSpaceDimensionSituation.{u}} {U V : BigFppfOver D.site D.base D.base_mem}
    {sX : yoneda.obj U ⟶ D.space} (hX : D.IsGood sX) {sY : yoneda.obj V ⟶ D.space}
    (hY : D.IsGood sY) {C : Stacks.Chow.ChowSituation.{u}}
    {t₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj V ⟶ C.S} [LocallyOfFiniteType t₀]
    (f : U ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀)]
    (hbase : yoneda.map f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem (yoneda.map f))
    (hr : HasRelativeDimension r D.site D.base D.base_mem (yoneda.map f))

omit [LocallyOfFiniteType t₀] in
/-- **The multiplicity of Stacks 0EP8 on a represented space.** For an integral closed subspace
`W ⊆ h_V` with generic point `w ∈ V`, the multiplicity of the integral closed subspace of `h_U`
corresponding to a point `x ∈ U` in `f^*[W] = [f^{-1}(W)]` is the coefficient at `x` of the
cycle of the scheme-theoretic inverse image `f⁻¹(closure {w})` of the reduced closure of `w`,
Stacks 02QU: the inverse image of `W` is cut out by the inverse image of its ideal sheaf. -/
theorem flatPullbackMult_equivSchemePoints_symm
    (hδX : IsDeltaCompatible D U sX C ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀))
    (W : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj V))
    (x : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U) :
    flatPullbackMult D sX hX sY hY (yoneda.map f) hbase r hflat hr W
        ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) =
      Stacks.Chow.closedSubschemeCycleCoeff C
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀)
        ((Stacks.Chow.integralComponentAt (W.schemeGenericPoint D.site D.base D.base_mem V)).comap
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)).subschemeι
        (deltaDimension D sY W + (r : ℤ)) x := by
  obtain ⟨R, j, e, hj, hW, he⟩ := W.exists_iso_yoneda D.site D.base D.base_mem
  have := hj
  have : IsIntegral ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R) :=
    isIntegral_of_iso_integralClosedSubspace W e
  have hkerj : ((BigFppfOver.toScheme D.site D.base D.base_mem).map j).ker =
      Stacks.Chow.integralComponentAt (W.schemeGenericPoint D.site D.base D.base_mem V) := by
    rw [Stacks.Chow.ker_eq_integralComponentAt, W.map_genericPoint_eq_schemeGenericPoint j e he]
  obtain ⟨R', j', hj', hker', hpre⟩ :=
    exists_closedImmersion_ker_comap_preimage_range D.site D.base D.base_mem j f
  rw [hkerj] at hker'
  have := hj'
  have hYi : W.subspace.preimage (yoneda.map f) = Subfunctor.range (yoneda.map j') := by
    rw [hW]
    exact hpre
  show (cycleGroupEquivScheme sX ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀) hδX
    (deltaDimension D sY W + (r : ℤ))
    (closedSubspaceCycle D sX hX (W.subspace.preimage (yoneda.map f))
      (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY (yoneda.map f) W)
      (deltaDimension D sY W + (r : ℤ))
      (deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY (yoneda.map f)
        hbase r hflat hr W))).1 x = _
  rw [cycleGroupEquivScheme_closedSubspaceCycle hX hδX j' _ _ hYi]
  obtain ⟨ε, hε⟩ := Stacks.Chow.exists_iso_of_ker_eq
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map j')
    ((Stacks.Chow.integralComponentAt (W.schemeGenericPoint D.site D.base D.base_mem V)).comap
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)).subschemeι
    (by rw [hker', Scheme.IdealSheafData.ker_subschemeι])
  exact Stacks.Chow.closedSubschemeCycleCoeff_eq_of_iso C _ _ _ ε hε _ x

/-- Over a point `x ∈ U` the inverse image of the reduced closure of a point `w ≠ f(x)` of `V`
contributes nothing to the cycle of Stacks 02QU at `x`, `f` being flat: every generic point of
`f⁻¹(closure {w})` lies over `w`. -/
theorem closedSubschemeCycleCoeff_comap_integralComponentAt_eq_zero
    [Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)]
    [LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)]
    (w : (BigFppfOver.toScheme D.site D.base D.base_mem).obj V)
    (x : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U)
    (hw : (BigFppfOver.toScheme D.site D.base D.base_mem).map f x ≠ w) (k : ℤ) :
    Stacks.Chow.closedSubschemeCycleCoeff C
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀)
        ((Stacks.Chow.integralComponentAt w).comap
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)).subschemeι k x = 0 := by
  set f₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map f
  have := Stacks.Chow.isIntegral_integralComponentAt w
  set i := (Stacks.Chow.integralComponentAt w).subschemeι
  obtain ⟨ε, hε⟩ := Stacks.Chow.exists_iso_of_ker_eq
    ((Stacks.Chow.integralComponentAt w).comap f₀).subschemeι (Limits.pullback.fst f₀ i) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
        Scheme.IdealSheafData.ker_subschemeι])
  rw [Stacks.Chow.closedSubschemeCycleCoeff_eq_of_iso C _ _ _ ε hε]
  refine Stacks.Chow.closedSubschemeCycleCoeff_pullbackFst_eq_zero C _ t₀ f₀ i k x ?_
  have hgen : i (_root_.genericPoint (Stacks.Chow.integralComponentAt w).subscheme) = w :=
    Stacks.Chow.genericPointOf_integralComponentAt w
  rwa [hgen]

/-- **Flat pullback on a represented space is flat pullback on the representing scheme.** Let
`f : U → V` be a morphism of schemes of the site with `h_f : h_U → h_V` flat of relative
dimension `r` over the good space `h_V → B`, and let `t₀ : V → C.S` and `f ∘ t₀ : U → C.S` be
δ-compatible scheme situations. Then under `Z_k(h_V) ≅ Z_k(V)` and `Z_{k+r}(h_U) ≅ Z_{k+r}(U)`
the flat pullback of cycles along `h_f`, Stacks 0EP8, is the flat pullback along `f`,
Stacks 02RB; `f` is flat of relative dimension `r` as a morphism of schemes. -/
theorem cycleGroupEquivScheme_flatPullbackMap
    (hδY : IsDeltaCompatible D V sY C t₀)
    (hδX : IsDeltaCompatible D U sX C ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀))
    (m : ℤ) (α : CycleGroup D sY m) :
    haveI : LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map f) :=
      locallyOfFiniteType_of_comp _ t₀
    haveI : Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map f) :=
      (holdsOnEveryEtaleChart_yoneda_map_iff D.site D.base D.base_mem
        isEtaleLocalOnSourceAndTarget_flat f).1 hflat
    cycleGroupEquivScheme sX ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀) hδX
        (m + (r : ℤ)) (flatPullbackMap D sX hX sY hY (yoneda.map f) hbase r hflat hr m
          (m + (r : ℤ)) rfl α) =
      Stacks.Chow.flatPullback C ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀) t₀
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map f) rfl r
        ((hasRelativeDimension_yoneda_map_iff D.site D.base D.base_mem f r).1 hr) m
        (cycleGroupEquivScheme sY t₀ hδY m α) := by
  have : LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map f) :=
    locallyOfFiniteType_of_comp _ t₀
  have : Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map f) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff D.site D.base D.base_mem
      isEtaleLocalOnSourceAndTarget_flat f).1 hflat
  set f₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map f
  set eV := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem V
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [Stacks.Chow.flatPullback_apply, cycleGroupEquivScheme_apply, cycleGroupEquivScheme_apply,
    flatPullbackMap_apply, finsum_eq_single _ (eV.symm (f₀ x))]
  · by_cases hα : α.1 (eV.symm (f₀ x)) = 0
    · rw [hα, zero_mul, zero_mul]
    · rw [flatPullbackMult_equivSchemePoints_symm hX hY f hbase r hflat hr hδX,
        IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm, α.2.2 _ hα]
      rfl
  · intro W hW
    rw [flatPullbackMult_equivSchemePoints_symm hX hY f hbase r hflat hr hδX,
      closedSubschemeCycleCoeff_comap_integralComponentAt_eq_zero f _ x _ _, mul_zero]
    intro h
    apply hW
    rw [h, ← IntegralClosedSubspace.equivSchemePoints_apply, Equiv.symm_apply_apply]

/-- **Stacks 0EPB, part (1), on a represented space.** Let `h_f : h_U → h_V` be flat of relative
dimension `r` and let `Y ⊆ h_V` be a closed subspace with `dim_δ(Y) ≤ m`. Then the flat pullback
of the cycle of `Y` is the cycle of its scheme-theoretic inverse image:
`h_f^*[Y]_m = [h_f^{-1}(Y)]_{m+r}`. Through the comparison with the representing schemes this is
the cycle identity of Stacks 02RE, part (1), for the closed subscheme of `V` cutting out `Y`. -/
theorem flatPullbackMap_closedSubspaceCycle_of_yoneda (hδY : IsDeltaCompatible D V sY C t₀)
    (hδX : IsDeltaCompatible D U sX C ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ t₀))
    (Y : Subfunctor (yoneda.obj V)) (hYc : IsClosedSubspace D.site D.base D.base_mem Y) (m : ℤ)
    (hm : deltaDimensionSubspace D sY hY Y hYc ≤ (m : EInt)) :
    flatPullbackMap D sX hX sY hY (yoneda.map f) hbase r hflat hr m (m + (r : ℤ)) rfl
        (closedSubspaceCycle D sY hY Y hYc m hm) =
      closedSubspaceCycle D sX hX (Y.preimage (yoneda.map f))
        (isClosedSubspace_preimage D.site D.base D.base_mem (yoneda.map f) Y hY.1 hX.1 hYc)
        (m + (r : ℤ))
        (deltaDimensionSubspace_preimage_le D sX hX sY hY (yoneda.map f) hbase r hflat hr m Y hYc
          hm) := by
  have : LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map f) :=
    locallyOfFiniteType_of_comp _ t₀
  have : Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map f) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff D.site D.base D.base_mem
      isEtaleLocalOnSourceAndTarget_flat f).1 hflat
  set f₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map f
  apply (cycleGroupEquivScheme sX (f₀ ≫ t₀) hδX (m + (r : ℤ))).injective
  rw [cycleGroupEquivScheme_flatPullbackMap hX hY f hbase r hflat hr hδY hδX]
  obtain ⟨R, i, hi, hYi⟩ := exists_closedImmersion_range D.site D.base D.base_mem Y hYc
  have := hi
  set i₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map i
  obtain ⟨R', i', hi', hker', hpre⟩ :=
    exists_closedImmersion_ker_comap_preimage_range D.site D.base D.base_mem i f
  have := hi'
  have hYi' : Y.preimage (yoneda.map f) = Subfunctor.range (yoneda.map i') := by
    rw [hYi]
    exact hpre
  rw [cycleGroupEquivScheme_closedSubspaceCycle hY hδY i Y hYc hYi,
    cycleGroupEquivScheme_closedSubspaceCycle hX hδX i' _ _ hYi']
  have hZ : Stacks.Chow.schemeDeltaDimension C (i₀ ≫ t₀) ≤ (m : EInt) := by
    obtain ⟨e, he⟩ := exists_iso_yoneda_of_eq_range D.site D.base D.base_mem i Y hYi
    refine Stacks.Chow.schemeDeltaDimension_le_of_forall_relativeDimension_le C t₀ i₀ fun z => ?_
    have h₁ := (deltaDimensionClosed_le_coe_iff D sY hY _
      (isClosed_subspacePointSet_of_isClosedSubspace D hY.1 Y hYc) m).1 hm
      (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
        (pointsMap D.site D.base D.base_mem (yoneda.obj R) e.hom
          ((pointsEquivScheme D.site D.base D.base_mem R).symm z))) ⟨_, rfl⟩
    rw [← pointsToScheme_pointsMap_pointsMap_eq D.site D.base D.base_mem i Y e he z, hδY]
    exact h₁
  rw [Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le C _ t₀ f₀ rfl r _ i₀ m hZ]
  obtain ⟨ε, hε⟩ := Stacks.Chow.exists_iso_of_ker_eq (Limits.pullback.fst f₀ i₀)
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map i')
    (by rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, hker'])
  exact Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso C _ _ _ ε hε _

end FlatPullback

end AlgebraicGeometry.Space

end
