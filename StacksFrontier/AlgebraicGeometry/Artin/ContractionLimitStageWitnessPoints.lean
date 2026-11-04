module

public import StacksFrontier.AlgebraicGeometry.Limits.EmptyFibreAtStage
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitClosedStage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent

/-!
# Points avoiding the image of a locally closed set, at a stage of a limit

For a cofiltered limit `V = lim V_k` of schemes with affine transition morphisms, a morphism
`n : N ⟶ V_i` from a Noetherian scheme and a locally closed subset `O ∩ K` of `N`, if no point
of `V` maps into `n(O ∩ K)` then no point of some stage `V_j` does.

This is the descent step used in the proof of Stacks 0GI5 to make the descended proper model
`Y_j ⟶ V_j` of a witness satisfy `|q_j|⁻¹ Z_j = |x_j|⁻¹ T'` at a finite stage.

## Main results

* `AlgebraicGeometry.exists_forall_notMem_image_inter_of_isLimit`: the scheme statement.

## References

* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **No point of a later stage maps into the image of a locally closed set** once no point of
the limit does. Let `V = lim V_k` be a cofiltered limit of schemes with affine transition
morphisms, `n : N ⟶ V_i` a morphism from a Noetherian scheme, `O ⊆ N` open and `K ⊆ N` closed.
If no point of `V` maps into `n(O ∩ K)`, then for some `j ⟶ i` no point of `V_j` does.

The set `n(O ∩ K)` is the image of the quasi-compact scheme `C`, a closed subscheme of the open
subscheme `O` with support `O ∩ K`; emptiness of `C ×_{V_i} V` descends to a stage
(`AlgebraicGeometry.exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app`). -/
theorem exists_forall_notMem_image_inter_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i : I) {N : Scheme.{u}} [IsLocallyNoetherian N]
    [CompactSpace N] (n : N ⟶ D.obj i) {O K : Set N} (hO : IsOpen O) (hK : IsClosed K)
    (h : ∀ v : c.pt, (c.π.app i).base v ∉ n.base '' (O ∩ K)) :
    ∃ (j : I) (F : j ⟶ i), ∀ v : D.obj j, (D.map F).base v ∉ n.base '' (O ∩ K) := by
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  have : IsNoetherian N := {}
  let U : N.Opens := ⟨O, hO⟩
  obtain ⟨C, cl, hcl, hrange⟩ := exists_isClosedImmersion_range_eq (U.ι.base ⁻¹' K)
    (hK.preimage U.ι.base.hom.continuous)
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set N))
  have := hcl
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace cl
  let t : C ⟶ D.obj i := cl ≫ U.ι ≫ n
  have ht : Set.range t.base = n.base '' (O ∩ K) := by
    rw [show ⇑t.base = n.base ∘ U.ι.base ∘ cl.base from rfl, Set.range_comp, Set.range_comp,
      hrange, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm K]
    rfl
  have hT : IsEmpty (pullback (c.π.app i) t : Scheme.{u}) := by
    rw [Scheme.isEmpty_pullback_iff, ht, Set.disjoint_left]
    rintro _ ⟨v, rfl⟩
    exact h v
  obtain ⟨j, F, hF⟩ := exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app D c hc i t hT
  rw [Scheme.isEmpty_pullback_iff, ht, Set.disjoint_left] at hF
  exact ⟨j, F, fun v => hF ⟨v, rfl⟩⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **No point of a later stage maps into the image of a locally closed set of a quasi-compact
algebraic space locally of finite type over a Noetherian stage**, once no point of the limit
does. Let `V = lim V_k` be a cofiltered limit of affine objects of the site, `q : Y ⟶ V_i` a
morphism locally of finite type from a quasi-compact algebraic space to a locally Noetherian
stage, `O ⊆ |Y|` open and `K ⊆ |Y|` closed. If no point of `V` maps into `|q|(O ∩ K)`, then for
some `j ⟶ i` no point of `V_j` does.

A quasi-compact étale atlas `N ⟶ Y` is a Noetherian scheme over `V_i` whose image of the
inverse image of `O ∩ K` is `|q|(O ∩ K)`, and the scheme statement
`AlgebraicGeometry.exists_forall_notMem_image_inter_of_isLimit` applies. -/
theorem exists_stage_forall_notMem_image_inter_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))) (i : I)
    (hEi : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsQuasiCompactSpace B S hS Y)
    (q : Y ⟶ yoneda.obj (E.obj i)) (hq : IsLocallyOfFiniteType B S hS q)
    {O K : Set (points B S hS Y)} (hO : IsOpen O) (hK : IsClosed K)
    (h : ∀ v : points B S hS (yoneda.obj c.pt),
      pointsMap B S hS _ (yoneda.map (c.π.app i)) v ∉ pointsMap B S hS Y q '' (O ∩ K)) :
    ∃ (j : I) (F : j ⟶ i), ∀ v : points B S hS (yoneda.obj (E.obj j)),
      pointsMap B S hS _ (yoneda.map (E.map F)) v ∉ pointsMap B S hS Y q '' (O ∩ K) := by
  let T := BigFppfOver.toScheme B S hS
  have : ∀ i, IsAffine ((E ⋙ T).obj i) := hE
  have : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.IsAffineHom ((E ⋙ T).map f) := fun f =>
    isAffineHom_of_isAffine _
  obtain ⟨N, n, hNc, hnsurj, hnet⟩ := hY
  have hnet' := hnet N (yoneda.map (𝟙 N)) (presheaf_yoneda_map_id_etale B S hS N)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hnet'
  let n₀ : N ⟶ E.obj i := yoneda.preimage (n ≫ q)
  have hn₀ : yoneda.map n₀ = n ≫ q := yoneda.map_preimage _
  have hlft : LocallyOfFiniteType (T.map n₀) :=
    hq N (E.obj i) n (yoneda.map (𝟙 (E.obj i))) n₀ hnet'
      (presheaf_yoneda_map_id_etale B S hS (E.obj i))
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id, hn₀])
  have := hEi
  have : IsLocallyNoetherian (T.obj N) := LocallyOfFiniteType.isLocallyNoetherian (T.map n₀)
  have : CompactSpace (T.obj N) := hNc
  let φ := schemePointsHomeomorph B S hS N
  let O' : Set (T.obj N) := φ.symm ⁻¹' (pointsMap B S hS _ n ⁻¹' O)
  let K' : Set (T.obj N) := φ.symm ⁻¹' (pointsMap B S hS _ n ⁻¹' K)
  have hO' : IsOpen O' := (hO.preimage (continuous_pointsMap B S hS n)).preimage φ.symm.continuous
  have hK' : IsClosed K' :=
    (hK.preimage (continuous_pointsMap B S hS n)).preimage φ.symm.continuous
  have hsurj := surjective_pointsMap_of_presheaf_surjective B S hS n hnsurj
  -- the image of `O ∩ K` is read on the atlas
  have key : ∀ x : points B S hS (yoneda.obj (E.obj i)),
      x ∈ pointsMap B S hS Y q '' (O ∩ K) ↔
        pointsToScheme B S hS (E.obj i) x ∈ (T.map n₀).base '' (O' ∩ K') := by
    refine fun x => ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := hsurj y
      refine ⟨φ z, ?_, ?_⟩
      · change pointsMap B S hS _ n (φ.symm (φ z)) ∈ O ∩ K
        rwa [φ.symm_apply_apply]
      · change (T.map n₀).base (pointsToScheme B S hS N z) = _
        rw [← pointsToScheme_pointsMap_yoneda, hn₀, pointsMap_comp_apply]
    · rintro ⟨z, hz, hzx⟩
      refine ⟨pointsMap B S hS _ n (φ.symm z), hz, ?_⟩
      apply (schemePointsHomeomorph B S hS (E.obj i)).injective
      change pointsToScheme B S hS _ _ = pointsToScheme B S hS _ _
      rw [← pointsMap_comp_apply, ← hn₀, pointsToScheme_pointsMap_yoneda, hzx.symm]
      change (T.map n₀).base (φ (φ.symm z)) = _
      rw [φ.apply_symm_apply]
  obtain ⟨j, F, hF⟩ := exists_forall_notMem_image_inter_of_isLimit (E ⋙ T) (T.mapCone c) hc i
    (T.map n₀) hO' hK' (fun v hv => by
      have := h ((schemePointsHomeomorph B S hS c.pt).symm v)
      rw [key, pointsToScheme_pointsMap_yoneda] at this
      refine this ?_
      change (T.map (c.π.app i)).base ((schemePointsHomeomorph B S hS c.pt)
        ((schemePointsHomeomorph B S hS c.pt).symm v)) ∈ _
      rwa [Homeomorph.apply_symm_apply])
  refine ⟨j, F, fun v hv => hF (pointsToScheme B S hS _ v) ?_⟩
  rwa [key, pointsToScheme_pointsMap_yoneda] at hv

end AlgebraicGeometry.Space

end
