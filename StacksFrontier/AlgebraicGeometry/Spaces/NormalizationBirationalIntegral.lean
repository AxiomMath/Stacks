module

public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace

/-!
# The normalization of an integral algebraic space is a birational morphism of integral spaces

Let `S` be a scheme and `F` a decent algebraic space over `S` with finitely many irreducible
components. If `F` is reduced, its normalization morphism `ν : F^ν ⟶ F` is birational, and if
`F` is integral, so is `F^ν`.

## Main results

* `AlgebraicGeometry.Space.GenericChart.exists_compatible`: a chart at a point refines to one
  compatible, along a morphism, with a prescribed chart at the image point.
* `AlgebraicGeometry.Space.isField_genericChart_localRing_of_isReduced`: on a reduced algebraic
  space the local ring of any chart at a point of codimension zero is a field.
* `AlgebraicGeometry.Space.NormalizationData.isBirational_hom`: the normalization morphism of a
  reduced decent algebraic space with finitely many irreducible components is birational.
* `AlgebraicGeometry.Space.NormalizationData.isIntegralSpace`: the normalization of an integral
  algebraic space is integral.

## Implementation notes

Birationality of `ν` is checked at the generic points. The bijection on generic points is part
(3) of Stacks 0BB4 through Stacks 0ABV. On local rings at a generic point the chart map of `ν`
is surjective by `AlgebraicGeometry.Space.NormalizationData.surjective_stalkMap_of_genericChart`;
its source, a reduced local ring of dimension zero, is a field, so it is also injective.

Integrality of `F^ν`: it is normal, hence reduced; it is decent by Stacks 0ABT; and its space
of points, being sober with exactly one generic point (the generic points biject with those of
the irreducible space `|F|`), is irreducible.

## References

* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Compatible charts along a morphism.** Given a morphism `f : F ⟶ G`, a chart `c` of `F` at
`x` and a chart `d` of `G` at the image of `x`, there is a chart `c'` of `F` at `x` refining `c`
together with a morphism of chart schemes `c'.U ⟶ d.U` lying over `f` and carrying the chosen
point of `c'` to that of `d`. -/
theorem GenericChart.exists_compatible {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : points B S hS F}
    {y : points B S hS G} (f : F ⟶ G) (hfx : pointsMap B S hS F f x = y)
    (c : GenericChart B S hS x) (d : GenericChart B S hS y) :
    ∃ (c' : GenericChart B S hS x) (b : c'.U ⟶ d.U),
      c'.immersion ≫ f = yoneda.map b ≫ d.immersion ∧
      (BigFppfOver.toScheme B S hS).map b (schemePoint B S hS c'.U c'.point) =
        schemePoint B S hS d.U d.point := by
  let p := FieldValuedPoint.map B S hS _ (c.immersion ≫ f) c.point
  have heq : (FieldValuedPoint.map B S hS _ d.immersion d.point).class B S hS G =
      p.class B S hS G := by
    show pointsMap B S hS _ d.immersion (d.point.class B S hS (yoneda.obj d.U)) =
      pointsMap B S hS _ (c.immersion ≫ f) (c.point.class B S hS (yoneda.obj c.U))
    rw [pointsMap_comp, Function.comp_apply, c.mapsTo, d.mapsTo, hfx]
  obtain ⟨s, hs⟩ := exists_lift_fieldPoint_of_isOpenImmersion B S hS d.immersion d.isOpen
    p d.point heq
  obtain ⟨W, a, b', hpb⟩ := d.isOpen.1 (c.immersion ≫ f)
  let b : W ⟶ d.U := yoneda.preimage b'
  have hb : yoneda.map b = b' := yoneda.map_preimage b'
  let ℓ := hpb.lift s (yonedaEquiv.symm c.point.value) (by
    rw [hs]
    exact (yonedaEquiv_symm_naturality_right _ (c.immersion ≫ f) c.point.value).symm)
  let cp := FieldValuedPoint.ofHom B S hS c.point ℓ
  have hca : pointsMap B S hS _ (yoneda.map a) (cp.class B S hS (yoneda.obj W)) =
      c.point.class B S hS (yoneda.obj c.U) :=
    FieldValuedPoint.pointsMap_class_ofHom_eq B S hS c.point ℓ (yoneda.map a)
      (hpb.lift_snd _ _ _)
  have hcb : pointsMap B S hS _ b' (cp.class B S hS (yoneda.obj W)) =
      d.point.class B S hS (yoneda.obj d.U) := by
    have : Mono d.immersion := mono_of_presheaf_isOpenImmersion d.isOpen
    apply pointsMap_injective_of_mono B S hS d.immersion
    have h := congrArg (fun k => pointsMap B S hS _ k (cp.class B S hS (yoneda.obj W))) hpb.w
    rw [pointsMap_comp, pointsMap_comp, Function.comp_apply, Function.comp_apply, hca] at h
    exact h.trans heq.symm
  have hc' : IsOpenImmersion B S hS (yoneda.map a ≫ c.immersion) :=
    MorphismProperty.comp_mem _ _ _ (isOpenImmersion_yoneda_map B S hS a (d.isOpen.2 _ _ _ hpb))
      c.isOpen
  let c' : GenericChart B S hS x :=
    ⟨W, yoneda.map a ≫ c.immersion, hc', cp, by
      rw [pointsMap_comp, Function.comp_apply, hca, c.mapsTo]⟩
  refine ⟨c', b, ?_, ?_⟩
  · show (yoneda.map a ≫ c.immersion) ≫ f = yoneda.map b ≫ d.immersion
    rw [Category.assoc, hb, hpb.w]
  · exact (schemePoint_map_yoneda B S hS b cp).symm.trans
      (schemePoint_eq_of_class_eq B S hS _ _ _ (hb ▸ hcb))

/-- **On a reduced algebraic space over `S` the local ring of any chart at a point of
codimension zero is a field.** The chart is an open immersion, hence étale, so its scheme is
reduced and, by Stacks 0BAM, its local ring at the chosen point has Krull dimension zero; a
reduced local ring of dimension zero is a field. -/
theorem isField_genericChart_localRing_of_isReduced
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F
      (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z))
    (x : points B S hS F) (hx : localRingDimension B S hS x = 0) (c : GenericChart B S hS x) :
    IsField (c.localRing B S hS) := by
  let T := BigFppfOver.toScheme B S hS
  let t := schemePoint B S hS c.U c.point
  have heta := presheaf_etale_of_isOpenImmersion B S hS c.isOpen
  have hredU : _root_.AlgebraicGeometry.IsReduced (T.obj c.U) :=
    (exists_atlas_iff_forall_etale B S hS F
      (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z) hF).mp hred c.U
      c.immersion heta
  have hchart : ChartPoint B S hS c.U c.immersion t x := ⟨c.point, rfl, c.mapsTo⟩
  have hdim : ringKrullDim (c.localRing B S hS) = 0 :=
    (hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS hF x 0).mp
      ((localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hF x 0).mp hx)
      c.U c.immersion t heta hchart
  have : _root_.IsReduced (c.localRing B S hS) :=
    inferInstanceAs (_root_.IsReduced ((T.obj c.U).presheaf.stalk t))
  have : Ring.KrullDimLE 0 (c.localRing B S hS) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  exact Ring.KrullDimLE.isField_of_isReduced

/-- On compatible charts at a generic point, the chart map of a birational morphism is an
isomorphism on local rings. -/
theorem IsBirational.isIso_stalkMap_of_compatible {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    {hdecX : IsDecentSpace B S hS X} {hdecY : IsDecentSpace B S hS Y}
    {hfiniteX : (irreducibleComponents (points B S hS X)).Finite}
    {hfiniteY : (irreducibleComponents (points B S hS Y)).Finite} {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f) {x : points B S hS X}
    (hx : x ∈ genericPoints (points B S hS X)) {y : points B S hS Y}
    (hxy : pointsMap B S hS X f x = y) (c : GenericChart B S hS x)
    (d : GenericChart B S hS y) (k : c.U ⟶ d.U)
    (hk : c.immersion ≫ f = yoneda.map k ≫ d.immersion)
    (hkp : (BigFppfOver.toScheme B S hS).map k (schemePoint B S hS c.U c.point) =
      schemePoint B S hS d.U d.point) :
    IsIso (((BigFppfOver.toScheme B S hS).map k).stalkMap
      (schemePoint B S hS c.U c.point)) := by
  subst hxy
  have hy := (hf.bijOn B S hS hX hY _ _ hfiniteX hfiniteY).mapsTo hx
  have h := hf.isIso_genericLocalRingMap B S hS hX hY _ _ hfiniteX hfiniteY x hx
  have he := (exists_genericLocalRingMap B S hS hX hY
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX)
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecY)
    hfiniteX hfiniteY f x hx hy).choose_spec c d k hk hkp
  rw [show genericLocalRingMap B S hS hX hY _ _ hfiniteX hfiniteY f x hx hy = _ from he] at h
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h

/-- **A composite of birational morphisms is birational.** -/
theorem IsBirational.comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    {hZ : IsAlgebraicSpace B S hS Z}
    {hdecX : IsDecentSpace B S hS X} {hdecY : IsDecentSpace B S hS Y}
    {hdecZ : IsDecentSpace B S hS Z}
    {hfiniteX : (irreducibleComponents (points B S hS X)).Finite}
    {hfiniteY : (irreducibleComponents (points B S hS Y)).Finite}
    {hfiniteZ : (irreducibleComponents (points B S hS Z)).Finite} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f)
    (hg : IsBirational B S hS hY hZ hdecY hdecZ hfiniteY hfiniteZ g) :
    IsBirational B S hS hX hZ hdecX hdecZ hfiniteX hfiniteZ (f ≫ g) := by
  have hfb := hf.bijOn B S hS hX hY _ _ hfiniteX hfiniteY
  have hcomp : pointsMap B S hS X (f ≫ g) = pointsMap B S hS Y g ∘ pointsMap B S hS X f :=
    pointsMap_comp B S hS X f g
  have hbij : Set.BijOn (pointsMap B S hS X (f ≫ g)) (genericPoints (points B S hS X))
      (genericPoints (points B S hS Z)) :=
    hcomp ▸ (hg.bijOn B S hS hY hZ _ _ hfiniteY hfiniteZ).comp hfb
  refine ⟨hbij, fun x hx => ?_⟩
  let T := BigFppfOver.toScheme B S hS
  have hy := hfb.mapsTo hx
  have hz := hbij.mapsTo hx
  let e := schematicGenericChart B S hS hZ
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hZ hdecZ) hfiniteZ _ hz
  let d₀ := schematicGenericChart B S hS hY
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecY) hfiniteY _ hy
  let c₀ := schematicGenericChart B S hS hX
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX) hfiniteX x hx
  obtain ⟨d, k₂, hk₂, hk₂p⟩ := GenericChart.exists_compatible g
    (by rw [hcomp, Function.comp_apply]) d₀ e
  obtain ⟨c, k₁, hk₁, hk₁p⟩ := GenericChart.exists_compatible f rfl c₀ d
  have hk : c.immersion ≫ (f ≫ g) = yoneda.map (k₁ ≫ k₂) ≫ e.immersion := by
    rw [← Category.assoc, hk₁, Category.assoc, hk₂, ← Category.assoc, ← Functor.map_comp]
  have hkp : T.map (k₁ ≫ k₂) (schemePoint B S hS c.U c.point) =
      schemePoint B S hS e.U e.point := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hk₁p, hk₂p]
  have h₁ := hf.isIso_stalkMap_of_compatible hx rfl c d k₁ hk₁ hk₁p
  have h₂ := hg.isIso_stalkMap_of_compatible hy (by rw [hcomp, Function.comp_apply]) d e k₂
    hk₂ hk₂p
  have h₂' : IsIso ((T.map k₂).stalkMap (T.map k₁ (schemePoint B S hS c.U c.point))) := by
    have key : ∀ p, p = schemePoint B S hS d.U d.point → IsIso ((T.map k₂).stalkMap p) := by
      rintro p rfl
      exact h₂
    exact key _ hk₁p
  have h₁₂ : IsIso ((T.map (k₁ ≫ k₂)).stalkMap (schemePoint B S hS c.U c.point)) := by
    have key : ∀ φ, φ = T.map k₁ ≫ T.map k₂ →
        IsIso (φ.stalkMap (schemePoint B S hS c.U c.point)) := by
      rintro φ rfl
      rw [Scheme.Hom.stalkMap_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₂' h₁
    exact key _ (Functor.map_comp T k₁ k₂)
  have he := (exists_genericLocalRingMap B S hS hX hZ
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecX)
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hZ hdecZ)
    hfiniteX hfiniteZ (f ≫ g) x hx hz).choose_spec c e (k₁ ≫ k₂) hk hkp
  rw [show genericLocalRingMap B S hS hX hZ _ _ hfiniteX hfiniteZ (f ≫ g) x hx hz = _ from he]
  infer_instance

namespace NormalizationData

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The normalization morphism of a reduced decent algebraic space with finitely many
irreducible components is birational.** -/
theorem isBirational_hom (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F)
    (hdec : IsDecentSpace B S hS F)
    (hred : HasEtaleLocalProperty B S hS F
      (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z))
    (hfinite : (irreducibleComponents (points B S hS F)).Finite) :
    IsBirational B S hS D.isAlgebraicSpace hF (D.isDecentSpace hF hdec) hdec
      (D.finite_irreducibleComponents hF hdec hfinite) hfinite D.hom := by
  have hNdec : IsDecentSpace B S hS D.space := D.isDecentSpace hF hdec
  have hbij := D.bijOn_genericPoints_hom hF hdec
  refine ⟨hbij, fun z hz => ?_⟩
  let T := BigFppfOver.toScheme B S hS
  let y := pointsMap B S hS D.space D.hom z
  have hy : y ∈ genericPoints (points B S hS F) := hbij.mapsTo hz
  have hz0 := (mem_genericPoints_iff_localRingDimension_eq_zero B S hS
    D.isAlgebraicSpace hNdec z).1 hz
  have hy0 := (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hF hdec y).1 hy
  let d := schematicGenericChart B S hS hF
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hF hdec) hfinite y hy
  let c₀ := schematicGenericChart B S hS D.isAlgebraicSpace
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS D.isAlgebraicSpace hNdec)
    (D.finite_irreducibleComponents hF hdec hfinite) z hz
  obtain ⟨c, k, hk, hkp⟩ := GenericChart.exists_compatible D.hom rfl c₀ d
  let t := schemePoint B S hS c.U c.point
  have hsurj : Function.Surjective ((T.map k).stalkMap t).hom :=
    D.surjective_stalkMap_of_genericChart hF z hz0 c d k hk
  have hfield : IsField ((T.obj d.U).presheaf.stalk (T.map k t)) := by
    rw [hkp]
    exact isField_genericChart_localRing_of_isReduced hF hred y hy0 d
  let : Field ((T.obj d.U).presheaf.stalk (T.map k t)) := hfield.toField
  have hkIso : IsIso ((T.map k).stalkMap t) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨((T.map k).stalkMap t).hom.injective, hsurj⟩
  have he := (exists_genericLocalRingMap B S hS D.isAlgebraicSpace hF
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS D.isAlgebraicSpace hNdec)
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hF hdec)
    (D.finite_irreducibleComponents hF hdec hfinite) hfinite D.hom z hz hy).choose_spec
      c d k hk hkp
  rw [show genericLocalRingMap B S hS D.isAlgebraicSpace hF _ _
    (D.finite_irreducibleComponents hF hdec hfinite) hfinite D.hom z hz hy = _ from he]
  infer_instance

/-- **The normalization of an integral algebraic space is integral.** -/
theorem isIntegralSpace (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F)
    (hint : IsIntegralSpace B S hS F) : IsIntegralSpace B S hS D.space := by
  have hdec := hint.isDecentSpace B S hS F
  have hNdec : IsDecentSpace B S hS D.space := D.isDecentSpace hF hdec
  refine ⟨hasEtaleLocalProperty_isReduced_of_isNormal B S hS D.space (D.isNormal hF), hNdec, ?_⟩
  have hsoberF := stacksSober_points_of_isDecentSpace B S hS hF hdec
  have : QuasiSober (points B S hS F) := (stacksSober_iff_t0_and_quasiSober.mp hsoberF).2
  have : T0Space (points B S hS F) := (stacksSober_iff_t0_and_quasiSober.mp hsoberF).1
  have hsoberN := stacksSober_points_of_isDecentSpace B S hS D.isAlgebraicSpace hNdec
  have : QuasiSober (points B S hS D.space) := (stacksSober_iff_t0_and_quasiSober.mp hsoberN).2
  have : T0Space (points B S hS D.space) := (stacksSober_iff_t0_and_quasiSober.mp hsoberN).1
  have : IrreducibleSpace (points B S hS F) := hint.2.2
  have hbij := D.bijOn_genericPoints_hom hF hdec
  have hFeq : genericPoints (points B S hS F) = {genericPoint (points B S hS F)} :=
    genericPoints_eq_singleton
  obtain ⟨g, hg, -⟩ := hbij.surjOn (hFeq ▸ Set.mem_singleton _ :
    genericPoint (points B S hS F) ∈ genericPoints (points B S hS F))
  have hNeq : genericPoints (points B S hS D.space) = {g} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hg, fun w hw => hbij.injOn hw hg ?_⟩
    have h1 := hbij.mapsTo hw
    have h2 := hbij.mapsTo hg
    rw [hFeq] at h1 h2
    exact h1.trans h2.symm
  have hclosure : closure ({g} : Set (points B S hS D.space)) = Set.univ := by
    rw [← hNeq]
    exact genericPoints.closure
  have hirr : IsIrreducible (Set.univ : Set (points B S hS D.space)) := by
    have hgc : closure ({g} : Set (points B S hS D.space)) ∈
        irreducibleComponents (points B S hS D.space) := hg
    rw [← hclosure]
    exact hgc.1
  exact (irreducibleSpace_def _).mpr hirr

end NormalizationData

end AlgebraicGeometry.Space

end
