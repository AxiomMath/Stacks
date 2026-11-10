module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Local quasi-finiteness over a field

Let `𝒳` be an algebraic stack over a field `k` whose structure 1-morphism is locally
quasi-finite in the sense of [Stacks, Tag 06PU], and let `f : V ⟶ 𝒳` be a locally quasi-finite
1-morphism out of a scheme `V` of the site. Then `V ⟶ Spec(k)` is locally quasi-finite as a
morphism of schemes.

## Main results

* `AlgebraicGeometry.Stack.locallyOfFiniteType_structureMap`: if a 1-morphism from a represented
  algebraic stack to the one represented by the terminal object of the site is locally of finite
  type, then so is the structure morphism of the scheme.
* `AlgebraicGeometry.Stack.AlgebraicStacks.discreteTopology_points_of_isLocallyQuasiFinite`: an
  algebraic stack locally quasi-finite over a field-valued point of the base has discrete space
  of points.
* `AlgebraicGeometry.Stack.eq_of_specializes_of_isLocallyQuasiFinite_pair`: a specialization of
  points of a scheme over a field which lifts to one point of an algebraic space mapping
  locally quasi-finitely to the scheme in two ways is trivial.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_specializes_of_isLocallyQuasiFinite`: the
  specialization relation on the points of `V` is trivial.
* `AlgebraicGeometry.Stack.AlgebraicStacks.locallyQuasiFinite_of_isLocallyQuasiFinite_over_field`:
  the structure morphism `V ⟶ Spec(k)` is locally of finite type and locally quasi-finite.

## Implementation notes

`AlgebraicGeometry.Stack.pointTopology` is a `def` and not an instance; the topologies are
supplied explicitly.

## References

* [Stacks Project, Tag 01TH](https://stacks.math.columbia.edu/tag/01TH)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06RU](https://stacks.math.columbia.edu/tag/06RU)
* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
* [Stacks Project, Tag 06UA](https://stacks.math.columbia.edu/tag/06UA)
* [Stacks Project, Tag 06UC](https://stacks.math.columbia.edu/tag/06UC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] AlgebraicGeometry.Space.pointTopology
  AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If the 1-morphism from the algebraic stack represented by `U` to the one represented by the
terminal object of the site is locally of finite type, then so is the structure morphism of `U`
as a morphism of schemes. -/
theorem locallyOfFiniteType_structureMap
    (U : BigFppfOver B S hS)
    (q : schemeStack.{u, w} B S hS U ⟶
      schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))
    (hq : AlgebraicStacks.IsLocallyOfFiniteType B S hS q) :
    LocallyOfFiniteType (B.inclusion.map U.hom) := by
  classical
  have _ := Space.isMultiplicative_presheaf_etale B S hS
  have hrep : IsRepresentableByAlgebraicSpaces B S hS q.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS q.hom
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
  have hP : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ r => Space.IsLocallyOfFiniteType B S hS r) :=
    Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS
  have hlt : (spaceProperty B S hS
      (fun _ _ r => Space.IsLocallyOfFiniteType B S hS r)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have hrel := (hasPropertyOnEverySmoothDiagram_iff_relative.{u, u + 1, w} B S hS _ hP
    (schemeStack.{u, w} B S hS U).property
    (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property q.hom hrep).1 hq
  have hrm := (hasRelativeProperty_iff_prop_representingMap.{u, u + 1} B S hS _ q.hom hrep
    (yoneda.obj U) (yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS))))
    (representedChart B S hS U)
    (representedChart B S hS (Over.mk (𝟙 (B.obj hS))))).1 hrel
  have heq : representingMap B S hS (schemeStack.{u, w} B S hS U).val
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
      (yoneda.obj U) (yoneda.obj (Over.mk (𝟙 (B.obj hS))))
      (representedChart B S hS U)
      (representedChart B S hS (Over.mk (𝟙 (B.obj hS)))) q.hom =
      yoneda.map (Over.homMk U.hom (Category.comp_id U.hom) :
        U ⟶ Over.mk (𝟙 (B.obj hS))) := by
    ext W z
    exact Limits.IsTerminal.hom_ext Over.mkIdTerminal _ _
  rw [heq] at hrm
  exact hrm U (Over.mk (𝟙 (B.obj hS))) (𝟙 _) (𝟙 _)
    (Over.homMk U.hom (Category.comp_id U.hom)) (MorphismProperty.id_mem _ _)
    (MorphismProperty.id_mem _ _) (by simp)

namespace AlgebraicStacks

/-- An algebraic stack locally quasi-finite over a field has discrete space of points: if
`Spec(k) ⟶ S` is a field-valued point of the base presented as a scheme of the site and
`p : 𝒳 ⟶ Spec(k)` is locally quasi-finite, then the space of points of `𝒳` is discrete. -/
theorem discreteTopology_points_of_isLocallyQuasiFinite
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    (p : 𝒳 ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (hp : IsLocallyQuasiFinite B S hS p) :
    @DiscreteTopology (Stack.points B S hS 𝒳.val.val 𝒳.val.property)
      (Stack.pointTopology B S hS 𝒳.val) := by
  classical
  let _ := Stack.pointTopology B S hS 𝒳.val
  have hdisc0 := hp.2.2 k hk toBase (𝟙 _)
  have hdisc : DiscreteTopology (points B S hS
      (Stack.twoFibreProductAlgebraicStack B S hS p (𝟙 _))) := hdisc0
  let _ := hdisc
  have hiso := Stack.graph_fst_iso B S hS p p (𝟙 _) (Bicategory.rightUnitor p).symm
  have key : ∀ z, pointsMap B S hS
      (Stack.graph B S hS p p (𝟙 _) (Bicategory.rightUnitor p).symm ≫
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS p (𝟙 _)).fst) z = z := by
    intro z
    rw [← pointsMap_eq_of_hom₂ B S hS hiso.hom, pointsMap_id B S hS]
    rfl
  have hinj : Function.Injective (pointsMap B S hS
      (Stack.graph B S hS p p (𝟙 _) (Bicategory.rightUnitor p).symm)) := by
    intro a b hab
    have hcc := pointsMap_comp B S hS
      (Stack.graph B S hS p p (𝟙 _) (Bicategory.rightUnitor p).symm)
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS p (𝟙 _)).fst
    have ha := key a
    have hb := key b
    rw [congrFun hcc a] at ha
    rw [congrFun hcc b] at hb
    simp only [Function.comp_apply] at ha hb
    rw [← ha, ← hb, hab]
  have hcont := Stack.continuous_pointsMap B S hS 𝒳.val
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS p (𝟙 _)).pt.val
    (Stack.graph B S hS p p (𝟙 _) (Bicategory.rightUnitor p).symm).hom.hom
  rw [discreteTopology_iff_isOpen_singleton]
  intro z
  have hpre := (isOpen_discrete
    ({pointsMap B S hS (Stack.graph B S hS p p (𝟙 _) (Bicategory.rightUnitor p).symm) z} :
      Set _)).preimage hcont
  convert hpre using 1
  ext a
  simp only [Set.mem_singleton_iff]
  exact hinj.eq_iff.symm

end AlgebraicStacks

/-- Let `U` be an object of the site over a field `k` whose structure morphism is locally of
finite type, let `F` be an algebraic space with two morphisms `s, t : F ⟶ U`, the second locally
quasi-finite, and let `r` be a point of `F` whose images under `s` and `t` are `x` and `y`. If `x`
specializes to `y` then `x = y`. -/
theorem eq_of_specializes_of_isLocallyQuasiFinite_pair
    (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (U : BigFppfOver B (Spec (.of k)) hk)
    (hU : LocallyOfFiniteType (B.inclusion.map U.hom))
    {F : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (.of k)) hk F)
    (s t : F ⟶ yoneda.obj U)
    (ht : Space.IsLocallyQuasiFinite B (Spec (.of k)) hk t)
    (r : Space.points B (Spec (.of k)) hk F)
    (x y : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U)
    (hx : Space.pointsToScheme B (Spec (.of k)) hk U
      (Space.pointsMap B (Spec (.of k)) hk F s r) = x)
    (hy : Space.pointsToScheme B (Spec (.of k)) hk U
      (Space.pointsMap B (Spec (.of k)) hk F t r) = y)
    (hxy : x ⤳ y) :
    x = y := by
  classical
  have _ := hU
  have _ := Space.isMultiplicative_presheaf_etale B (Spec (.of k)) hk
  obtain ⟨W, c, hcsurj, hcetale⟩ := hF.exists_atlas
  obtain ⟨w, hw⟩ := Space.isSurjective_of_presheafSurjective B (Spec (.of k)) hk c hcsurj r
  have hm : yoneda.map (yoneda.preimage (c ≫ t)) = c ≫ t := yoneda.map_preimage _
  have hqm := ht W U c (𝟙 _) (yoneda.preimage (c ≫ t)) hcetale
    (MorphismProperty.id_mem _ _) (by rw [hm]; simp)
  have hpt : ∀ (u : F ⟶ yoneda.obj U) (z : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U),
      Space.pointsToScheme B (Spec (.of k)) hk U (Space.pointsMap B (Spec (.of k)) hk F u r) = z →
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (yoneda.preimage (c ≫ u))
        (Space.pointsToScheme B (Spec (.of k)) hk W w) = z := by
    intro u z hz
    rw [← Space.pointsToScheme_pointsMap, yoneda.map_preimage,
      Space.pointsMap_comp B (Spec (.of k)) hk (yoneda.obj W) c u]
    simp only [Function.comp_apply, hw]
    exact hz
  have hnx := hpt s x hx
  have hmy := hpt t y hy
  have hcomp : (BigFppfOver.toScheme B (Spec (.of k)) hk).map (yoneda.preimage (c ≫ s)) ≫
      B.inclusion.map U.hom =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (yoneda.preimage (c ≫ t)) ≫
        B.inclusion.map U.hom := by
    change B.inclusion.map (yoneda.preimage (c ≫ s)).left ≫ B.inclusion.map U.hom =
      B.inclusion.map (yoneda.preimage (c ≫ t)).left ≫ B.inclusion.map U.hom
    rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, Over.w, Over.w]
  have _ : LocallyQuasiFinite ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
    (yoneda.preimage (c ≫ t))) := hqm.2
  have hres := AlgebraicGeometry.eq_of_specialization_of_common_lift_over_field
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (yoneda.preimage (c ≫ s)))
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (yoneda.preimage (c ≫ t)))
    (B.inclusion.map U.hom) hcomp (Space.pointsToScheme B (Spec (.of k)) hk W w)
    (by rw [hnx, hmy]; exact hxy)
  rwa [hnx, hmy] at hres

namespace AlgebraicStacks

/-- The specialization relation on the points of a scheme `U`, locally of finite type over a
field, which maps by a locally quasi-finite 1-morphism representable by algebraic spaces to an
algebraic stack with discrete space of points, is trivial. -/
theorem eq_of_specializes_of_isLocallyQuasiFinite
    (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    {𝒳 : Stack.AlgebraicStacks.{u, w} B (Spec (.of k)) hk}
    (U : BigFppfOver B (Spec (.of k)) hk)
    (hU : LocallyOfFiniteType (B.inclusion.map U.hom))
    (f : Stack.schemeStack.{u, w} B (Spec (.of k)) hk U ⟶ 𝒳)
    (hfrep : Stack.IsRepresentableByAlgebraicSpaces B (Spec (.of k)) hk f.hom.hom)
    (hflqf : Stack.IsLocallyQuasiFinite B (Spec (.of k)) hk f.hom)
    (hX : @DiscreteTopology (Stack.points B (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property)
      (Stack.pointTopology B (Spec (.of k)) hk 𝒳.val))
    (x y : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U) (hxy : x ⤳ y) :
    x = y := by
  classical
  let _ := Stack.pointTopology B (Spec (.of k)) hk
    (Stack.schemeFibredCategory B (Spec (.of k)) hk U)
  let _ := Stack.pointTopology B (Spec (.of k)) hk 𝒳.val
  let _ := hX
  have hcont : Continuous (fun z : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U =>
      Stack.pointsMap B (Spec (.of k)) hk
        (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val.val
        (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val.property 𝒳.val.property
        f.hom.hom ((Stack.pointsHomeomorphScheme B (Spec (.of k)) hk U).symm z)) :=
    (Stack.continuous_pointsMap B (Spec (.of k)) hk
      (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val 𝒳.val f.hom.hom).comp
      (Stack.pointsHomeomorphScheme B (Spec (.of k)) hk U).symm.continuous
  have himg := specializes_iff_eq.mp (hxy.map hcont)
  have hQ := Stack.isTwoFibreProduct_underlying_algebraicStacks B (Spec (.of k)) hk
    (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f)
  obtain ⟨r, hr1, hr2⟩ := Stack.exists_point_of_isTwoFibreProduct B (Spec (.of k)) hk
    (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f).underlying hQ
    ((Stack.pointsHomeomorphScheme B (Spec (.of k)) hk U).symm x)
    ((Stack.pointsHomeomorphScheme B (Spec (.of k)) hk U).symm y) himg
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
      B (Spec (.of k)) hk (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val 𝒳.val
      (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val f.hom f.hom
      (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f).underlying hQ hfrep
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B (Spec (.of k)) hk U)
  obtain ⟨rF, hrF⟩ := (Stack.bijective_spacePointMap_representing B (Spec (.of k)) hk F
    (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f).underlying.pt eF).2 r
  have ht := Stack.prop_representingMap_of_hasRelativeProperty.{u, u + 1} B (Spec (.of k)) hk
    (Space.locallyQuasiFiniteProperty B (Spec (.of k)) hk) f.hom hfrep hflqf
    (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val f.hom
    (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f).underlying.swap
    (Bicategory.isTwoFibreProduct_swap hQ)
    F (yoneda.obj U) hF (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U) eF
    (Stack.representedChart B (Spec (.of k)) hk U)
  have hrc : ∀ z, Stack.representedChartPointMap B (Spec (.of k)) hk U z =
      Stack.spacePointMap B (Spec (.of k)) hk (yoneda.obj U)
        (Stack.schemeFibredCategory B (Spec (.of k)) hk U)
        (Stack.representingEquivalence B (Spec (.of k)) hk (yoneda.obj U)
          (Stack.schemeFibredCategory B (Spec (.of k)) hk U)
          (Stack.representedChart B (Spec (.of k)) hk U)).functor z :=
    fun _ => rfl
  have hid : ∀ (π :
        (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f).underlying.pt ⟶
          (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val)
      (z : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U),
      Stack.pointsMap B (Spec (.of k)) hk _ _ _ π.hom r =
        (Stack.pointsHomeomorphScheme B (Spec (.of k)) hk U).symm z →
      Space.pointsToScheme B (Spec (.of k)) hk U
        (Space.pointsMap B (Spec (.of k)) hk F
          (Stack.representingMap B (Spec (.of k)) hk
            (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f).underlying.pt
            (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val F (yoneda.obj U) eF
            (Stack.representedChart B (Spec (.of k)) hk U) π) rF) = z := by
    intro π z hπ
    rw [← Stack.pointsHomeomorphScheme_representedChartPointMap B (Spec (.of k)) hk U, hrc,
      Stack.spacePointMap_representing_naturality B (Spec (.of k)) hk F (yoneda.obj U)
        (Stack.twoFibreProductSquareAlgebraicStacks B (Spec (.of k)) hk f f).underlying.pt
        (Stack.schemeStack.{u, w} B (Spec (.of k)) hk U).val eF
        (Stack.representedChart B (Spec (.of k)) hk U) π rF, hrF, hπ]
    exact (Stack.pointsHomeomorphScheme B (Spec (.of k)) hk U).apply_symm_apply z
  exact Stack.eq_of_specializes_of_isLocallyQuasiFinite_pair B k hk U hU hF _ _ ht rF x y
    (hid _ x hr1) (hid _ y hr2) hxy

/-- Let `𝒳 ⟶ Spec(k)` be a locally quasi-finite 1-morphism, where `𝒳` is an
algebraic stack over the field `k`, and let `f : V ⟶ 𝒳` be a locally quasi-finite 1-morphism out
of the algebraic stack represented by a scheme `V` of the site with structure morphism
`g : V ⟶ Spec(k)`. Then `g` is locally quasi-finite: it is locally of finite type and locally
quasi-finite as a morphism of schemes. -/
@[stacks 06UC]
theorem locallyQuasiFinite_of_isLocallyQuasiFinite_over_field
    (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    {𝒳 : Stack.AlgebraicStacks.{u, w} B (Spec (.of k)) hk}
    (p : 𝒳 ⟶ Stack.schemeStack.{u, w} B (Spec (.of k)) hk (Over.mk (𝟙 (B.obj hk))))
    (hp : IsLocallyQuasiFinite B (Spec (.of k)) hk p)
    (V : Scheme.{u}) (hV : B.Contains V) (g : V ⟶ Spec (.of k))
    (f : Stack.schemeStack.{u, w} B (Spec (.of k)) hk
      (Over.mk (⟨g⟩ : B.obj hV ⟶ B.obj hk)) ⟶ 𝒳)
    (hf : IsLocallyQuasiFinite B (Spec (.of k)) hk f) :
    LocallyOfFiniteType g ∧ LocallyQuasiFinite g := by
  classical
  have hgft : LocallyOfFiniteType g :=
    Stack.locallyOfFiniteType_structureMap B (Spec (.of k)) hk
      (Over.mk (⟨g⟩ : B.obj hV ⟶ B.obj hk)) (f ≫ p)
      (isLocallyOfFiniteType_comp B (Spec (.of k)) hk f p hf.2.1 hp.2.1)
  have hfrep : Stack.IsRepresentableByAlgebraicSpaces B (Spec (.of k)) hk f.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B (Spec (.of k)) hk
      𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B (Spec (.of k)) hk _) f.hom
  have hflqf : Stack.IsLocallyQuasiFinite B (Spec (.of k)) hk f.hom :=
    Stack.isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology
      B (Spec (.of k)) hk f hfrep hf.2.1 hf.2.2
  have hX := discreteTopology_points_of_isLocallyQuasiFinite B (Spec (.of k)) hk k hk
    (𝟙 (Spec (.of k))) p hp
  have _ := hgft
  rw [← AlgebraicGeometry.forall_quasiFiniteAt_iff g]
  exact AlgebraicGeometry.forall_quasiFiniteAt_of_specialization_eq g
    (fun x y hxy => eq_of_specializes_of_isLocallyQuasiFinite B k hk
      (Over.mk (⟨g⟩ : B.obj hV ⟶ B.obj hk)) hgft f hfrep hflqf hX x y hxy)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
