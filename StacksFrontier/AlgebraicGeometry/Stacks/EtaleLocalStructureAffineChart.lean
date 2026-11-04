module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartedSliceFlatDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatChartOpenChart
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureQuasiSplittingChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackOfPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeOpenChartThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsSurjectivityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidStabilizerDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp

/-!
# An affine flat, locally quasi-finite chart through a point of a quasi-DM stack

The first step of the proofs of **Stacks 0DU3** and **Stacks 0DU4**: for an algebraic stack `𝒳`
which is quasi-DM and a point `x ∈ |𝒳|`, choose an affine scheme `U` and a flat, locally finitely
presented, locally quasi-finite 1-morphism `U ⟶ 𝒳` such that `x` is the image of a point of `U`.
This is possible by **Stacks 06MF**: restrict the surjective, flat, locally finitely presented,
locally quasi-finite presentation it provides to an affine open neighbourhood of a point over `x`.

## Main results

* `AlgebraicGeometry.Stack.EtaleLocalStructure.exists_isAffine_chart`: the chart.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.isLocallyQuasiFinite_schemeStackMap_comp`: local
  quasi-finiteness (Stacks 04XB) of a chart passes to its restriction to an open subscheme.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The Yoneda image of an open immersion of the site is locally quasi-finite. -/
theorem isLocallyQuasiFinite_yoneda_map_of_isOpenImmersion {V W : BigFppfOver B S hS}
    (i : V ⟶ W) [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i)] :
    Space.IsLocallyQuasiFinite B S hS (yoneda.map i) :=
  (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite i).2
    ⟨inferInstance, inferInstance⟩

/-- A 1-morphism from the algebraic stack of a scheme of the site to an algebraic stack is
representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_schemeStack_hom {W : BigFppfOver B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : schemeStack.{u, w} B S hS W ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom := by
  obtain ⟨_, _, hdiag, _⟩ := 𝒳.property
  exact isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source B S hS hdiag
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) f.hom

/-- **Local quasi-finiteness of a chart passes to its restriction along an open immersion.** -/
theorem isLocallyQuasiFinite_schemeStackMap_comp {V W : BigFppfOver B S hS} (i : V ⟶ W)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i)]
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (hf : IsLocallyQuasiFinite B S hS f.hom) :
    IsLocallyQuasiFinite B S hS (schemeStackMap.{u, w} B S hS i ≫ f).hom := by
  have : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  exact hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
    (Space.locallyQuasiFiniteProperty B S hS) (schemeStackMap.{u, w} B S hS i).hom f.hom
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS i)
    (isRepresentableByAlgebraicSpaces_schemeStack_hom B S hS f)
    (hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
      (Space.locallyQuasiFiniteProperty B S hS) i
      (isLocallyQuasiFinite_yoneda_map_of_isOpenImmersion B S hS i)) hf

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An affine flat, locally quasi-finite chart through a point of a quasi-DM stack.** For an
algebraic stack `𝒳` over `S` which is quasi-DM (Stacks 050D) and a point `x ∈ |𝒳|`, there are an
object `U` of the site with affine underlying scheme and a 1-morphism `U ⟶ 𝒳` which is flat
(Stacks 06PW), locally of finite presentation (Stacks 06Q2) and locally quasi-finite (Stacks 04XB),
with `x` in the image of `|U| ⟶ |𝒳|`.

This is **Stacks 06MF** — the presentation it provides — restricted to an affine open
neighbourhood of a point over `x`. -/
theorem exists_isAffine_chart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧ AlgebraicStacks.IsFlat B S hS f ∧
        AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∧
          IsLocallyQuasiFinite B S hS f.hom ∧
            x ∈ Set.range (AlgebraicStacks.pointsMap B S hS f) := by
  obtain ⟨W, w, hsurj, hflat, hlfp, hlqf⟩ :=
    hasQuasiDMPresentation_of_isAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳 h𝒳
  obtain ⟨p, rfl⟩ := hsurj x
  set w₀ := pointsHomeomorphScheme B S hS W p
  obtain ⟨Q, hQ, hw₀Q, -⟩ := exists_isAffineOpen_mem_and_subset (x := w₀)
    (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj W).Opens)) trivial
  let U := BigFppfOver.openSubObj B S hS W Q
  let i : U ⟶ W := BigFppfOver.openSubHom B S hS W Q
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) := by
    rw [Space.openSubHom_toScheme]
    infer_instance
  refine ⟨U, schemeStackMap.{u, w} B S hS i ≫ w, hQ, ?_, ?_, ?_, ?_⟩
  · exact AlgebraicStacks.isFlat_comp B S hS _ _
      (isFlat_schemeStackMap.{u, w} B S hS i inferInstance) hflat
  · exact AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS _ _
      (isLocallyOfFinitePresentation_schemeStackMap.{u, w} B S hS i inferInstance) hlfp
  · exact isLocallyQuasiFinite_schemeStackMap_comp B S hS i w hlqf
  · let := pointTopology B S hS (schemeFibredCategory B S hS U)
    let := pointTopology B S hS (schemeFibredCategory B S hS W)
    obtain ⟨u, hu⟩ : w₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map i).base := by
      rwa [Space.openSubHom_toScheme, Scheme.Opens.range_ι]
    let p' := (pointsHomeomorphScheme B S hS U).symm u
    refine ⟨p', ?_⟩
    rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply]
    congr 1
    apply (pointsHomeomorphScheme B S hS W).injective
    show pointsHomeomorphScheme B S hS W
        (pointsMap B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property (schemeFibredCategory B S hS W).property
          (schemeFibredCategoryMap B S hS i).hom p') = _
    rw [pointsHomeomorphScheme_naturality, Homeomorph.apply_symm_apply, hu]

/-! ### The open substack of the image, and the chart onto it -/

section OpenImage

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hflat : AlgebraicStacks.IsFlat B S hS f)
  (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)

include hflat hlfp in
/-- The image of a flat, locally finitely presented chart is open (Stacks 04XL). -/
theorem isOpen_range_pointsMap :
    @IsOpen _ (pointTopology B S hS 𝒳.val) (Set.range (AlgebraicStacks.pointsMap B S hS f)) := by
  let := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
  let := pointTopology B S hS 𝒳.val
  exact (AlgebraicStacks.isOpenMap_pointsMap.{u, w} B S hS f hflat hlfp).isOpen_range

/-- **The open substack of `𝒳` with the image of a flat, locally finitely presented chart as its
points** (Stacks 04XL and 06FJ). -/
noncomputable def imageSubstack : OpenSubstack 𝒳 :=
  openSubstackOfPoints 𝒳 _ (isOpen_range_pointsMap f hflat hlfp)

/-- The points of the image substack are the image of the chart. -/
theorem pointSet_imageSubstack :
    (imageSubstack f hflat hlfp).pointSet B S hS =
      Set.range (AlgebraicStacks.pointsMap B S hS f) :=
  pointSet_openSubstackOfPoints 𝒳 _ _

/-- Every object in the image of the chart lies in the image substack. -/
theorem imageSubstack_property (z : (schemeStack.{u, w} B S hS U).val.val.obj) :
    (imageSubstack f hflat hlfp).property (f.hom.hom.toFunctor.obj z) := by
  show (openSubstackOfPoints 𝒳 _ (isOpen_range_pointsMap f hflat hlfp)).property _
  rw [openSubstackOfPoints_property]
  exact (pointsWithin_obj_iff 𝒳 f.hom.hom _ z).2 fun r _ => ⟨_, rfl⟩

/-- The membership condition of `AlgebraicGeometry.Stack.FlatChart.restrictChart'` at the whole
of `U`. -/
theorem imageSubstack_property_iff (z : (schemeStack.{u, w} B S hS U).val.val.obj) :
    (imageSubstack f hflat hlfp).property (f.hom.hom.obj z) ↔
      Set.range ⇑((BigFppfOver.toScheme B S hS).map z.hom) ⊆
        ((⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) : Set _) :=
  ⟨fun _ _ _ => trivial, fun _ => imageSubstack_property f hflat hlfp z⟩

/-- The open subscheme `⊤` of `U`, as an object of the site; it is `U` up to the isomorphism
`AlgebraicGeometry.Stack.FlatChart.restrictHom`. -/
noncomputable abbrev imageChartObj : BigFppfOver B S hS :=
  FlatChart.restrictObj (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)

/-- **The chart onto the image substack**: the chart, read as a 1-morphism into the open substack
of its image, through the 2-fibre product `𝒳' ×_𝒳 𝒮_U`. -/
noncomputable abbrev imageChart :
    schemeStack.{u, w} B S hS (imageChartObj (U := U)) ⟶
      (imageSubstack f hflat hlfp).toAlgebraicStack :=
  FlatChart.restrictChart' f (imageSubstack f hflat hlfp) ⊤
    (imageSubstack_property_iff f hflat hlfp)

/-- The image chart is flat (Stacks 06PY), being an equivalent of a base change of the chart. -/
theorem isFlat_imageChart : AlgebraicStacks.IsFlat B S hS (imageChart f hflat hlfp) :=
  AlgebraicStacks.isFlat_comp_of_isEquivalence B S hS _ _
    (FlatChart.isEquivalence_restrictLift f _ ⊤ (imageSubstack_property_iff f hflat hlfp))
    (AlgebraicStacks.isFlat_baseChange B S hS f _ _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f) hflat)

/-- The image chart is locally of finite presentation (Stacks 06Q4). -/
theorem isLocallyOfFinitePresentation_imageChart :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (imageChart f hflat hlfp) :=
  AlgebraicStacks.isLocallyOfFinitePresentation_comp_of_isEquivalence B S hS _ _
    (FlatChart.isEquivalence_restrictLift f _ ⊤ (imageSubstack_property_iff f hflat hlfp))
    (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS f _ _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f) hlfp)

/-- The image chart is locally quasi-finite (Stacks 04XB) when the chart is. -/
theorem isLocallyQuasiFinite_imageChart (hlqf : IsLocallyQuasiFinite B S hS f.hom) :
    IsLocallyQuasiFinite B S hS (imageChart f hflat hlfp).hom := by
  have : Functor.IsEquivalence
      (FlatChart.restrictLift f _ ⊤ (imageSubstack_property_iff f hflat hlfp)).hom.hom.toFunctor :=
    FlatChart.isEquivalence_restrictLift f _ ⊤ (imageSubstack_property_iff f hflat hlfp)
  have : Functor.IsEquivalence
      (BasedFunctor.id (imageSubstack f hflat hlfp).toAlgebraicStack.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  exact relativeProperty_of_equivalences B S hS (Space.locallyQuasiFiniteProperty B S hS)
    (imageChart f hflat hlfp).hom.hom
    (chartBaseChangeSquare (imageSubstack f hflat hlfp).inclusion f).fst.hom.hom
    (FlatChart.restrictLift f _ ⊤ (imageSubstack_property_iff f hflat hlfp)).hom.hom
    (BasedFunctor.id _) (Iso.refl _)
    (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.locallyQuasiFiniteProperty B S hS)
      (schemeStack.{u, w} B S hS U).val 𝒳.val (imageSubstack f hflat hlfp).toAlgebraicStack.val
      f.hom (imageSubstack f hflat hlfp).inclusion.hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (imageSubstack f hflat hlfp).inclusion.hom f.hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (imageSubstack f hflat hlfp).inclusion.hom f.hom) hlqf)

/-- On points, the image chart followed by the inclusion of the image substack is the chart
precomposed with the isomorphism `⊤ ⟶ U`. -/
theorem pointsMap_imageChart_inclusion :
    AlgebraicStacks.pointsMap B S hS
        (imageChart f hflat hlfp ≫ (imageSubstack f hflat hlfp).inclusion) =
      AlgebraicStacks.pointsMap B S hS
        (schemeStackMap.{u, w} B S hS (FlatChart.restrictHom
          (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)) ≫ f) :=
  pointsMap_congr_of_obj_eq _ _ _ _ fun _ => rfl

/-- Every point of `|𝒮_U|` is the image of a point of `|𝒮_⊤|` under the isomorphism `⊤ ⟶ U`. -/
private theorem exists_pointsMap_restrictHom_top
    (p : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)) :
    ∃ p₀, AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS
      (FlatChart.restrictHom (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens))) p₀ = p :=
  isSurjective_schemeStackMap.{u, w} B S hS
    (FlatChart.restrictHom (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)) (by
      intro x
      refine ⟨⟨x, trivial⟩, ?_⟩
      rw [Space.openSubHom_toScheme]; rfl) p

/-- The image chart is surjective. -/
theorem isSurjective_imageChart : IsSurjective B S hS (imageChart f hflat hlfp) := by
  intro y
  have hy : AlgebraicStacks.pointsMap B S hS (imageSubstack f hflat hlfp).inclusion y ∈
      Set.range (AlgebraicStacks.pointsMap B S hS f) := by
    rw [← pointSet_imageSubstack f hflat hlfp]
    exact ⟨y, rfl⟩
  obtain ⟨p, hp⟩ := hy
  obtain ⟨p₀, hp₀⟩ := exists_pointsMap_restrictHom_top.{u, w} p
  refine ⟨p₀, ?_⟩
  apply pointsMap_injective_of_fullyFaithful B S hS (imageSubstack f hflat hlfp).inclusion
  show AlgebraicStacks.pointsMap B S hS (imageSubstack f hflat hlfp).inclusion
      (AlgebraicStacks.pointsMap B S hS (imageChart f hflat hlfp) p₀) =
    AlgebraicStacks.pointsMap B S hS (imageSubstack f hflat hlfp).inclusion y
  rw [← Function.comp_apply (f := AlgebraicStacks.pointsMap B S hS
      (imageSubstack f hflat hlfp).inclusion), ← AlgebraicStacks.pointsMap_comp,
    congrFun (pointsMap_imageChart_inclusion f hflat hlfp) p₀,
    AlgebraicStacks.pointsMap_comp, Function.comp_apply, hp₀, hp]

/-- A point of `|𝒳|` in the image of the chart is in the image of the image chart followed by the
inclusion of the image substack. -/
theorem exists_point_imageChart (x : AlgebraicStacks.points B S hS 𝒳)
    (hx : x ∈ Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    x ∈ Set.range (AlgebraicStacks.pointsMap B S hS
      (imageChart f hflat hlfp ≫ (imageSubstack f hflat hlfp).inclusion)) := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨p₀, hp₀⟩ := exists_pointsMap_restrictHom_top.{u, w} p
  refine ⟨p₀, ?_⟩
  rw [pointsMap_imageChart_inclusion, AlgebraicStacks.pointsMap_comp, Function.comp_apply, hp₀]

end OpenImage

/-! ### The self-intersection of the chart is represented by an object of the site -/

section Relation

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)

/-- The fibre product of two representable presheaves over a representable one is
representable. -/
theorem isRepresentable_pullback_yoneda_map {X Y Z : BigFppfOver B S hS} (a : X ⟶ Z)
    (b : Y ⟶ Z) : (Limits.pullback (yoneda.map a) (yoneda.map b)).IsRepresentable :=
  CategoryTheory.isRepresentable_of_natIso (yoneda.obj (Limits.pullback a b))
    (Limits.PreservesPullback.iso yoneda a b)

/-- The square `U ×_S U` of the object space of the groupoid of a chart is representable. -/
theorem isRepresentable_objectPairs_pointGroupoid (Rsp : AlgebraicSpaces B S hS)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.p
      (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p) :
    (GroupoidInAlgebraicSpaces.objectPairs
      (SelfIntersection.pointGroupoid B S hS U f Rsp eR)).obj.IsRepresentable := by
  let G := SelfIntersection.pointGroupoid B S hS U f Rsp eR
  obtain ⟨a, ha⟩ : ∃ a, yoneda.map a = G.objectsToBase.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  show (Limits.pullback G.objectsToBase.hom G.objectsToBase.hom).IsRepresentable
  have := isRepresentable_pullback_yoneda_map a a
  exact CategoryTheory.isRepresentable_of_natIso _ (Limits.pullback.congrHom ha ha)

/-- **The self-intersection `U ×_𝒳 U` of a chart of a quasi-DM stack with separated diagonal is
represented by an object of the site** (Stacks 03XX): the pair `(t, s) : U ×_𝒳 U ⟶ U ×_S U` is a
base change of the diagonal, hence locally quasi-finite and separated, into the representable
algebraic space `U ×_S U`. -/
theorem exists_representation_relation (hQ : IsQuasiDMOver B S hS 𝒳)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    ∃ V : BigFppfOver B S hS, Nonempty (StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val
        f.hom.hom).val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) := by
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  let Rsp : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let G := SelfIntersection.pointGroupoid B S hS U f Rsp eR₀
  have : Robj.IsRepresentable :=
    Space.isRepresentable_of_locallyQuasiFinite_separated B S hS Robj
      (GroupoidInAlgebraicSpaces.objectPairs G).obj hRobj
      (GroupoidInAlgebraicSpaces.objectPairs G).property
      (GroupoidInAlgebraicSpaces.sourceTarget G).hom
      (isRepresentable_objectPairs_pointGroupoid f Rsp eR₀)
      (SelfIntersection.isLocallyQuasiFinite_sourceTarget_pointGroupoid B S hS U f Rsp eR₀ hQ)
      (SelfIntersection.isSeparated_sourceTarget_pointGroupoid B S hS U f Rsp eR₀ hΔ)
  exact ⟨Robj.reprX, ⟨eR₀.trans (PresheafOfCategories.equivalenceOverOfIso Robj.reprW.symm)⟩⟩

end Relation

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
