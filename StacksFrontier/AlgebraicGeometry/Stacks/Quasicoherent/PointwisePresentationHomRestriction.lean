module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackHomRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSheafFppf

/-!
# Maps out of a quasi-coherent module, through a pointwise groupoid presentation (Stacks 076S)

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`, let `𝒳` be a category fibred in
groupoids over `(Sch/S)_{fppf}` and let `F` be a fully faithful 1-morphism from the pointwise
groupoid fibration `[U/_pR]` to `𝒳` such that every object of `𝒳` is, fppf locally, in the image
of `F`; let `x : 𝒮_U ⟶ 𝒳` be the induced object over `U`.  For an algebraic stack with a flat
groupoid presentation (`AlgebraicGeometry.Stack.FlatGroupoidPresentation`) and for the quotient
stack `[U/R]` itself this is the situation of Stacks 076S.

For a quasi-coherent `𝒪_𝒳`-module `ℱ` and an arbitrary `𝒪_𝒳`-module `ℋ` the map
`Hom_{𝒪_𝒳}(ℱ, ℋ) ⟶ Hom_{𝒪_U}(x^*ℱ|_{U_étale}, x^*ℋ|_{U_étale})` is injective, and its image
consists of the `φ` for which some `χ` makes the two squares through the comparison maps of
equation 076R along `s` and `t` commute
(`AlgebraicGeometry.Stack.presentationObjectRestrictionMap_injective_and_range`).

The proof is the one of
`AlgebraicGeometry.Stack.quotientStackObjectRestrictionMap_injective_and_range` (the case
`𝒳 = [U/R]`), run through `F`: the charted points (points of `U` over affine objects, factored
through affine étale charts) are cover-dense in `𝒳`; over a charted point the sections of `ℱ` are
the base change of its sections over the chart, which defines the extension of `φ`; the two squares
make these extensions natural for every arrow between charted points; and a cover-dense full
subcategory glues them to a morphism of sheaves.

This is the form of Stacks 076S used in the proof of Stacks 0778, where `ℋ` is a module with the
flat base change property and is not quasi-coherent.

## References

* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The coefficient homomorphism of `AlgebraicGeometry.Space.etaleChartStructureHom` is
surjective on sections over an étale chart: it is induced by an equality of objects. -/
theorem etaleChartStructureHom_app_surjective {U : AlgebraicSpaces B S hS}
    {𝒰 : Type*} [Category 𝒰] {𝒳 : Type*} [Category 𝒳]
    (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) (W : SmallEtale B S hS U.1)
    (c : FibredSite.objRing B S hS r ((etaleChartToFibred B S hS p eU f).obj W)) :
    ∃ c₀, (etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op W) c₀ = c := by
  have e := Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) W
  refine ⟨(BigFppfOver.structureSheaf B S hS).obj.map (eqToHom e.symm).op c, ?_⟩
  rw [etaleChartStructureHom_app]
  show ((BigFppfOver.structureSheaf B S hS).obj.map (eqToHom e.symm).op ≫
    (BigFppfOver.structureSheaf B S hS).obj.map (eqToHom e).op) c = c
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS}

section Points

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)

include hF in
/-- The object of the site under the image of a point is the base of the point. -/
theorem presentation_obj_eq (w : PointwiseFibration G) : p.obj (F.obj w) = w.base :=
  Functor.congr_obj hF w

include hF in
/-- The image of an arrow of the pointwise groupoid fibration lies over its base. -/
theorem isHomLift_presentation_map {w w' : PointwiseFibration G} (m : w ⟶ w') :
    p.IsHomLift m.base (F.map m) := by
  have : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      m.base m := IsHomLift.map _ m
  exact Functor.isHomLift_map_of_comp_eq hF m.base m

/-- The charted points, through the pointwise presentation. -/
abbrev presentationChartedPointFunctor : ChartedPointCat G ⥤ 𝒳 :=
  inducedFunctor _ ⋙ F

/-- The charted points functor of a full pointwise presentation is full. -/
instance [F.Full] : (presentationChartedPointFunctor F).Full :=
  inferInstanceAs (inducedFunctor _ ⋙ F).Full

/-- The charted points functor of a faithful pointwise presentation is faithful. -/
instance [F.Faithful] : (presentationChartedPointFunctor F).Faithful :=
  inferInstanceAs (inducedFunctor _ ⋙ F).Faithful

variable (hp : p.IsFiberedInGroupoids)

include hF hp in
/-- **The charted points cover the image of a point.** -/
theorem coverByImage_presentationChartedPointFunctor_mem (w : PointwiseFibration G) :
    Sieve.coverByImage (presentationChartedPointFunctor F) (F.obj w) ∈
      BigFppfOver.associatedTopology C S hS p .fppf (F.obj w) := by
  rw [Functor.mem_inheritedTopology_iff_functorPushforward p
    (BigFppfOver.baseOverTopology C S hS .fppf) hp]
  show _ ∈ BigFppfOver.topology C S hS _
  have hw := presentation_obj_eq F hF w
  refine (BigFppfOver.topology C S hS).superset_covering ?_
    ((BigFppfOver.topology C S hS).pullback_stable (eqToHom hw)
      (Space.generate_affineChartPresieve_mem C S hS G.objects w.fiber))
  rintro V f ⟨V'', e, h, ⟨hV'', W, hW, g, hg⟩, hfac⟩
  let c : ChartedPoint G := ⟨V'', hV'', G.objects.obj.map h.op w.fiber, W, hW, g, hg⟩
  let m : (presentationChartedPointFunctor F).obj c ⟶ F.obj w :=
    F.map (pointwiseSpecial G h w.fiber)
  have hm : p.IsHomLift h m := isHomLift_presentation_map F hF (pointwiseSpecial G h w.fiber)
  have hc := presentation_obj_eq F hF c.toPoint
  let st : Presieve.CoverByImageStructure (presentationChartedPointFunctor F) m :=
    { obj := c, lift := 𝟙 _, map := m, fac := Category.id_comp _ }
  refine ⟨_, m, e ≫ eqToHom hc.symm, ⟨st⟩, ?_⟩
  have hfac' : f = e ≫ h ≫ eqToHom hw.symm := by
    simpa using (congrArg (· ≫ eqToHom hw.symm) hfac).symm
  rw [IsHomLift.fac' p h m, hfac']
  simp only [Category.assoc]
  have key : ∀ {X : BigFppfOver C S hS} (a : V'' = X) (b : X = V''),
      eqToHom a ≫ eqToHom b ≫ h ≫ eqToHom hw.symm = h ≫ eqToHom hw.symm := by
    intro X a b; subst a; simp
  exact (congrArg (e ≫ ·) (key _ _)).symm

include hF hp in
/-- **The charted points are cover-dense** for a pointwise presentation which is fppf locally
essentially surjective. -/
theorem isCoverDense_presentationChartedPointFunctor
    (hloc : ∀ y : 𝒳, ∃ (I : Type u) (x : I → PointwiseFibration G) (g : ∀ i, F.obj (x i) ⟶ y),
      Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS p .fppf y) :
    (presentationChartedPointFunctor F).IsCoverDense
      (BigFppfOver.associatedTopology C S hS p .fppf) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨I, x, g, hg⟩ := hloc y
  refine (BigFppfOver.associatedTopology C S hS p .fppf).transitive hg _ ?_
  rintro Z f ⟨Z', h, f', ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine (BigFppfOver.associatedTopology C S hS p .fppf).pullback_stable h ?_
  refine (BigFppfOver.associatedTopology C S hS p .fppf).superset_covering ?_
    (coverByImage_presentationChartedPointFunctor_mem F hF hp (x i))
  rintro Y k ⟨st⟩
  let st' : Presieve.CoverByImageStructure (presentationChartedPointFunctor F) (k ≫ g i) :=
    { obj := st.obj, lift := st.lift, map := st.map ≫ g i, fac := by rw [← Category.assoc, st.fac] }
  exact ⟨st'⟩

end Points

/-! ### The data of Stacks 076S for a pointwise presentation -/

section Data

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  {hp : p.IsFiberedInGroupoids}

/-- **`ℱ ↦ x^*ℱ|_{U_étale}`** on modules on the fppf site of `𝒳`. -/
abbrev presentationObjectRestriction
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)) :
    Space.Modules.{u, u} C S hS G.objects.1 G.objects.2 :=
  pointwisePresentationRestriction (hp := hp) F hF ((fppfToEtaleSheafOfModules C S hS p hp).obj M)

/-- **`ψ ↦ x^*ψ|_{U_étale}`** on morphisms of modules on the fppf site of `𝒳`. -/
abbrev presentationObjectRestrictionMap
    {M H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)}
    (ψ : M ⟶ H) : presentationObjectRestriction F hF M ⟶ presentationObjectRestriction F hF H :=
  pointwisePresentationRestrictionMap (hp := hp) F hF
    ((fppfToEtaleSheafOfModules C S hS p hp).map ψ)

/-- **`ℱ ↦ (x ∘ s)^*ℱ|_{R_étale}`**, the common target of the two comparison maps. -/
abbrev presentationArrowRestriction
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)) :=
  Space.etaleRestrictedModuleInverseImage C S hS (U := G.arrows) (spaceProj G.arrows) p
    (isFiberedInGroupoids_arrows G) hp (spacePresentation G.arrows)
    (pointwisePresentationSource F) (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    ((fppfToEtaleSheafOfModules C S hS p hp).obj M)

/-- **`ψ ↦ (x ∘ s)^*ψ|_{R_étale}`**. -/
abbrev presentationArrowRestrictionMap
    {M H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)}
    (ψ : M ⟶ H) : presentationArrowRestriction F hF M ⟶ presentationArrowRestriction F hF H :=
  Space.etaleRestrictedModuleInverseImageMap C S hS (U := G.arrows) (spaceProj G.arrows) p
    (isFiberedInGroupoids_arrows G) hp (spacePresentation G.arrows)
    (pointwisePresentationSource F) (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    ((fppfToEtaleSheafOfModules C S hS p hp).map ψ)

/-- The comparison map through the source, on modules on the fppf site of `𝒳`. -/
abbrev presentationSourceComparison
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)) :
    (Space.modulePullback C S hS G.source).obj (presentationObjectRestriction F hF M) ⟶
      presentationArrowRestriction F hF M :=
  pointwisePresentationSourceComparison (hp := hp) F hF
    ((fppfToEtaleSheafOfModules C S hS p hp).obj M)

/-- The comparison map through the target, on modules on the fppf site of `𝒳`. -/
abbrev presentationTargetComparison
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)) :
    (Space.modulePullback C S hS G.target).obj (presentationObjectRestriction F hF M) ⟶
      presentationArrowRestriction F hF M :=
  pointwisePresentationTargetComparison (hp := hp) F hF
    ((fppfToEtaleSheafOfModules C S hS p hp).obj M)

end Data

/-! ### Sections over the image of a point -/

section Sections

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  {hp : p.IsFiberedInGroupoids}

include hF in
/-- An object over an affine base has affine image. -/
theorem presentation_isAffineOver {w : PointwiseFibration G} (h : IsAffineOver C S hS w.base) :
    IsAffineOver C S hS (p.obj (F.obj w)) :=
  (presentation_obj_eq F hF w) ▸ h

include hF in
/-- **A section of a module over the image of a point is determined locally on the base.** -/
theorem presentationSections_ext
    (H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf))
    (w : PointwiseFibration G) {P : Presieve w.base}
    (hP : Sieve.generate P ∈ BigFppfOver.topology C S hS w.base)
    {σ τ : H.val.obj (op (F.obj w))}
    (h : ∀ ⦃V : BigFppfOver C S hS⦄ (k : V ⟶ w.base), P k →
      H.val.map (F.map (pointwiseSpecial G k w.fiber)).op σ =
        H.val.map (F.map (pointwiseSpecial G k w.fiber)).op τ) :
    σ = τ := by
  have hw := presentation_obj_eq F hF w
  let : p.IsFibered := hp.isFibered
  have hS := Functor.functorPullback_mem_inheritedTopology p
    (BigFppfOver.baseOverTopology C S hS .fppf) (F.obj w)
    ((BigFppfOver.topology C S hS).pullback_stable (eqToHom hw) hP)
  refine (H.isSheaf_sections.isSheafFor _ hS).isSeparatedFor.ext ?_
  rintro z f ⟨V, e, k, hk, hfac⟩
  let m := F.map (pointwiseSpecial G k w.fiber)
  have hm : p.IsHomLift k m := isHomLift_presentation_map F hF (pointwiseSpecial G k w.fiber)
  have hcart := hp.isStronglyCartesian_homLift k m
  have hl : p.IsHomLift (e ≫ k) f := by
    refine IsHomLift.of_fac p _ _ rfl hw ?_
    rw [hfac]; simp
  obtain ⟨f', ⟨-, hf'⟩, -⟩ := @Functor.IsStronglyCartesian.universal_property' _ _ _ _
    p _ _ _ _ k m hcart z e f hl
  rw [← hf']
  exact (H.val.map_comp_apply m.op f'.op σ).trans
    ((congrArg (H.val.map f'.op) (h k hk)).trans (H.val.map_comp_apply m.op f'.op τ).symm)

end Sections

/-! ### Charts -/

section Charts

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  (hp : p.IsFiberedInGroupoids)

/-- **The comparison morphism of the triangle through the source**, on a commutative square of
charts over `s`, is the image of the arrow of the pointwise fibration underlying it. -/
theorem presentationSource_comparisonMorphism
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.source.hom) :
    Space.comparisonMorphism C S hS (spaceProj G.arrows) (spaceProj G.objects)
      (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.source)
      (pointwisePresentationSource F) (pointwisePresentationObject F)
      (Iso.refl (pointwisePresentationSource F)) G.source (spaceFunctorChartIso G.source) d =
    F.map (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm) := by
  unfold Space.comparisonMorphism Space.comparisonChartHom
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  show F.map ((pointwiseObjectInclusion G).map _) = _
  congr 1

/-- **The comparison morphism of the triangle through the target**, on a commutative square of
charts over `t`, is the image of the arrow given by the point of `R` of the chart, followed by
the arrow underlying the square. -/
theorem presentationTarget_comparisonMorphism
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.target.hom) :
    ∃ g : arrowChartPoint G d.U ⟶
        ⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U,
          G.target.hom.app _ (yonedaEquiv d.U.obj.hom)⟩,
      g.base = 𝟙 _ ∧
      (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ g.fiber).1 = yonedaEquiv d.U.obj.hom ∧
      Space.comparisonMorphism C S hS (spaceProj G.arrows) (spaceProj G.objects)
        (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
        (pointwisePresentationSource F) (pointwisePresentationObject F)
        (pointwisePresentationTwoIso F) G.target (spaceFunctorChartIso G.target) d =
      F.map (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm) := by
  refine ⟨(pointwiseTwoArrow G).app ((Space.restrictionFunctor C S hS G.arrows.obj
    (spaceProj G.arrows) (spacePresentation G.arrows)).obj d.U), rfl,
    pointwiseArrow_vertHom G _ _ rfl rfl, ?_⟩
  unfold Space.comparisonMorphism Space.comparisonChartHom
  refine Eq.trans ?_ (F.map_comp _ _).symm
  show F.map ((pointwiseTwoArrow G).app _) ≫ F.map ((pointwiseObjectInclusion G).map _) = _
  congr 2

end Charts

/-! ### Extending a morphism over the charted points -/

section PtExt

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  {hp : p.IsFiberedInGroupoids}


attribute [local instance] FibredSite.objModule

variable {M H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)}
  (φ : presentationObjectRestriction F hF M ⟶ presentationObjectRestriction F hF H)
  (χ : presentationArrowRestriction F hF M ⟶ presentationArrowRestriction F hF H)
  (hM : M.IsQuasicoherentOnSite)

/-- The value of `φ : x^*ℱ|_{U_étale} ⟶ x^*ℋ|_{U_étale}` on sections over an étale chart `W` of
`U`, as a map of sections of `ℱ` and `ℋ` over `x(u_U W)`. -/
noncomputable def presentationChartSectionValue (W : Space.SmallEtale C S hS G.objects.obj) :
    M.val.obj (op (F.obj (chartPoint G W))) →+
      H.val.obj (op (F.obj (chartPoint G W))) :=
  (φ.val.app (op W)).hom.toAddMonoidHom

/-- The value of `φ` over a chart is linear over the ring of global functions of the chart. -/
theorem presentationChartSectionValue_smul (W : Space.SmallEtale C S hS G.objects.obj)
    (c : FibredSite.objRing C S hS p (F.obj (chartPoint G W)))
    (x : M.val.obj (op (F.obj (chartPoint G W)))) :
    presentationChartSectionValue F hF φ W (c • x) =
      c • presentationChartSectionValue F hF φ W x := by
  obtain ⟨c₀, rfl⟩ := Space.etaleChartStructureHom_app_surjective (spaceProj G.objects) p
    (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationObject F hF hp) W c
  exact (φ.val.app (op W)).hom.map_smul c₀ x

/-- The morphism `x(c) ⟶ x(u_U W)` from (the image of) a charted point to its chart. -/
noncomputable abbrev presentationChartMap (c : ChartedPoint G) :
    F.obj c.toPoint ⟶ F.obj (chartPoint G c.W) :=
  F.map c.special

/-- The linear map `f ↦ b^*φ(f)` out of the sections of `ℱ` over the image of a chart, along a
morphism `b` to it. -/
noncomputable def presentationSeedAlong {z : 𝒳} {W : Space.SmallEtale C S hS G.objects.obj}
    (b : z ⟶ F.obj (chartPoint G W)) :
    letI := FibredSite.objAlgebra C S hS p b
    letI : Module (FibredSite.objRing C S hS p
        (F.obj (chartPoint G W))) (H.val.obj (op z)) :=
      Module.compHom _ (algebraMap (FibredSite.objRing C S hS p
        (F.obj (chartPoint G W)))
        (FibredSite.objRing C S hS p z))
    M.val.obj (op (F.obj (chartPoint G W))) →ₗ[
      FibredSite.objRing C S hS p
        (F.obj (chartPoint G W))] H.val.obj (op z) :=
  letI := FibredSite.objAlgebra C S hS p b
  letI : Module (FibredSite.objRing C S hS p
      (F.obj (chartPoint G W))) (H.val.obj (op z)) :=
    Module.compHom _ (algebraMap (FibredSite.objRing C S hS p
      (F.obj (chartPoint G W)))
      (FibredSite.objRing C S hS p z))
  { toFun := fun x => H.val.map b.op (presentationChartSectionValue F hF φ W x)
    map_add' := fun a b' => (congrArg (H.val.map b.op) (map_add _ a b')).trans
      (map_add (H.val.map b.op).hom _ _)
    map_smul' := fun r x => (congrArg (H.val.map b.op)
      (presentationChartSectionValue_smul F hF φ W r x)).trans (H.val.map_smul b.op r _) }

/-- **The extension of `φ` over a charted point**: the linear map `ℱ(x(c)) ⟶ ℋ(x(c))` sending
`b^*f` to `b^*φ(f)`, for `b` the morphism to the chart. -/
noncomputable def presentationChartedExtension (c : ChartedPoint G) :
    M.val.obj (op ((presentationChartedPointFunctor F).obj c)) →ₗ[
      FibredSite.objRing C S hS p ((presentationChartedPointFunctor F).obj c)]
      H.val.obj (op ((presentationChartedPointFunctor F).obj c)) :=
  FibredSite.extendAlong M hM (presentationChartMap F c)
    (presentation_isAffineOver (w := chartPoint G c.W) F hF c.hW)
    (presentation_isAffineOver (w := c.toPoint) F hF c.hT) H
    (presentationSeedAlong F hF φ (presentationChartMap F c))

/-- The extension over a charted point is `φ` on restrictions of sections over the chart. -/
theorem presentationChartedExtension_chartMap (c : ChartedPoint G)
    (x : M.val.obj (op (F.obj (chartPoint G c.W)))) :
    presentationChartedExtension F hF φ hM c (M.val.map (presentationChartMap F c).op x) =
      H.val.map (presentationChartMap F c).op (presentationChartSectionValue F hF φ c.W x) :=
  FibredSite.extendAlong_map M hM (presentationChartMap F c)
    (presentation_isAffineOver (w := chartPoint G c.W) F hF c.hW)
    (presentation_isAffineOver (w := c.toPoint) F hF c.hT) H
    (presentationSeedAlong F hF φ (presentationChartMap F c)) x

/-- The extension over a charted point is compatible with restriction of the charted point. -/
theorem presentationMap_chartedExtension (c : ChartedPoint G) {T' : BigFppfOver C S hS}
    (k : T' ⟶ c.T) (hT' : IsAffineOver C S hS T')
    (σ : M.val.obj (op ((presentationChartedPointFunctor F).obj c))) :
    H.val.map (F.map (pointwiseSpecial G k c.pt)).op
        (presentationChartedExtension F hF φ hM c σ) =
      presentationChartedExtension F hF φ hM (c.restrict k hT')
        (M.val.map (F.map (pointwiseSpecial G k c.pt)).op σ) := by
  have hn : F.map (pointwiseSpecial G k c.pt) ≫ (presentationChartMap F c) =
      (presentationChartMap F (c.restrict k hT')) :=
    (F.map_comp _ _).symm.trans (congrArg F.map (ChartedPoint.special_restrict c k hT'))
  refine FibredSite.map_extendAlong' M hM (presentationChartMap F c)
    (presentation_isAffineOver (w := chartPoint G c.W) F hF c.hW)
    (presentation_isAffineOver (w := c.toPoint) F hF c.hT) H _ _ hn
    (presentation_isAffineOver F hF hT') _ _ (fun x => ?_) σ
  show H.val.map (presentationChartMap F (c.restrict k hT')).op
      (presentationChartSectionValue F hF φ c.W x) =
    H.val.map (F.map (pointwiseSpecial G k c.pt)).op
      (H.val.map (presentationChartMap F c).op (presentationChartSectionValue F hF φ c.W x))
  rw [← hn]
  exact H.val.map_comp_apply _ _ _

/-- The value of `χ : (x ∘ s)^*ℱ|_{R_étale} ⟶ (x ∘ s)^*ℋ|_{R_étale}` on sections over an étale
chart `V` of `R`. -/
noncomputable def presentationArrowChartSectionValue (V : Space.SmallEtale C S hS G.arrows.obj) :
    M.val.obj (op (F.obj (arrowChartPoint G V))) →+
      H.val.obj (op (F.obj (arrowChartPoint G V))) :=
  (χ.val.app (op V)).hom.toAddMonoidHom

/-- The value of `χ` over a chart is linear over the ring of global functions of the chart. -/
theorem presentationArrowChartSectionValue_smul (V : Space.SmallEtale C S hS G.arrows.obj)
    (c : FibredSite.objRing C S hS p (F.obj (arrowChartPoint G V)))
    (x : M.val.obj (op (F.obj (arrowChartPoint G V)))) :
    presentationArrowChartSectionValue F hF χ V (c • x) =
      c • presentationArrowChartSectionValue F hF χ V x := by
  obtain ⟨c₀, rfl⟩ := Space.etaleChartStructureHom_app_surjective (spaceProj G.arrows) p
    (isFiberedInGroupoids_arrows G) hp (spacePresentation G.arrows)
    (pointwisePresentationSource F) (isFibredOneMorphism_pointwisePresentationSource F hF hp) V c
  exact (χ.val.app (op V)).hom.map_smul c₀ x

/-- **The square through the source, on sections.**  If it commutes, `χ` carries the restriction
of a section of `ℱ` along a square of charts over `s` to the restriction of its image by `φ`. -/
theorem presentationSource_square_app
    (hsq : presentationSourceComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ presentationSourceComparison F hF H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.source.hom)
    (x : M.val.obj (op (F.obj (chartPoint G d.V)))) :
    presentationArrowChartSectionValue F hF χ d.U (M.val.map (F.map
        (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm)).op x) =
      H.val.map (F.map
        (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm)).op
          (presentationChartSectionValue F hF φ d.V x) := by
  rw [← presentationSource_comparisonMorphism F]
  exact Space.comparisonAlgebraicSpacesModules_square_app (ϕ := φ) (χ := χ) (hsq := hsq)
    C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d x

/-- **The square through the target, on sections**, over a square of charts over `t`. -/
theorem presentationTarget_square_app
    (hsq : presentationTargetComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ presentationTargetComparison F hF H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.target.hom)
    (g : arrowChartPoint G d.U ⟶
        ⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U,
          G.target.hom.app _ (yonedaEquiv d.U.obj.hom)⟩)
    (hg : Space.comparisonMorphism C S hS (spaceProj G.arrows) (spaceProj G.objects)
        (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
        (pointwisePresentationSource F) (pointwisePresentationObject F)
        (pointwisePresentationTwoIso F) G.target (spaceFunctorChartIso G.target) d =
      F.map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm))
    (x : M.val.obj (op (F.obj (chartPoint G d.V)))) :
    presentationArrowChartSectionValue F hF χ d.U (M.val.map (F.map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm)).op x) =
      H.val.map (F.map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm)).op
          (presentationChartSectionValue F hF φ d.V x) := by
  rw [← hg]
  exact Space.comparisonAlgebraicSpacesModules_square_app (ϕ := φ) (χ := χ) (hsq := hsq)
    C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d x

/-- The linear map `f ↦ j^*χ(f)` out of the sections of `ℱ` over the image of a chart of `R`. -/
noncomputable def presentationArrowSeedAlong {z : 𝒳}
    {V : Space.SmallEtale C S hS G.arrows.obj}
    (j : z ⟶ F.obj (arrowChartPoint G V)) :
    letI := FibredSite.objAlgebra C S hS p j
    letI : Module (FibredSite.objRing C S hS p
        (F.obj (arrowChartPoint G V))) (H.val.obj (op z)) :=
      Module.compHom _ (algebraMap (FibredSite.objRing C S hS p
        (F.obj (arrowChartPoint G V)))
        (FibredSite.objRing C S hS p z))
    M.val.obj (op (F.obj (arrowChartPoint G V))) →ₗ[
      FibredSite.objRing C S hS p
        (F.obj (arrowChartPoint G V))] H.val.obj (op z) :=
  letI := FibredSite.objAlgebra C S hS p j
  letI : Module (FibredSite.objRing C S hS p
      (F.obj (arrowChartPoint G V))) (H.val.obj (op z)) :=
    Module.compHom _ (algebraMap (FibredSite.objRing C S hS p
      (F.obj (arrowChartPoint G V)))
      (FibredSite.objRing C S hS p z))
  { toFun := fun x => H.val.map j.op (presentationArrowChartSectionValue F hF χ V x)
    map_add' := fun a b' => (congrArg (H.val.map j.op) (map_add _ a b')).trans
      (map_add (H.val.map j.op).hom _ _)
    map_smul' := fun r x => (congrArg (H.val.map j.op)
      (presentationArrowChartSectionValue_smul F hF χ V r x)).trans (H.val.map_smul j.op r _) }

/-- The extension of `φ` along a morphism from an affine object to the image of an affine chart
of `U`. -/
noncomputable def presentationExtAlong {z : 𝒳} {W : Space.SmallEtale C S hS G.objects.obj}
    (b : z ⟶ F.obj (chartPoint G W))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W))
    (hz : IsAffineOver C S hS (p.obj z)) :
    M.val.obj (op z) →ₗ[FibredSite.objRing C S hS p z] H.val.obj (op z) :=
  FibredSite.extendAlong M hM b (presentation_isAffineOver F hF hW) hz H
    (presentationSeedAlong F hF φ b)

/-- The extension depends only on the morphism. -/
theorem presentationExtAlong_congr {z : 𝒳} {W : Space.SmallEtale C S hS G.objects.obj}
    {b b' : z ⟶ F.obj (chartPoint G W)} (h : b = b')
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W))
    (hz : IsAffineOver C S hS (p.obj z)) :
    presentationExtAlong F hF φ hM b hW hz = presentationExtAlong F hF φ hM b' hW hz := by
  subst h; rfl

/-- The extension of `χ` along a morphism from an affine object to the image of an affine chart
of `R`. -/
noncomputable def presentationArrowExtAlong {z : 𝒳}
    {V : Space.SmallEtale C S hS G.arrows.obj}
    (j : z ⟶ F.obj (arrowChartPoint G V))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V))
    (hz : IsAffineOver C S hS (p.obj z)) :
    M.val.obj (op z) →ₗ[FibredSite.objRing C S hS p z] H.val.obj (op z) :=
  FibredSite.extendAlong M hM j (presentation_isAffineOver F hF hV) hz H
    (presentationArrowSeedAlong F hF χ j)

/-- Extending `φ` along `j ≫ a` is extending `χ` along `j`, if `χ` and `φ` agree through `a`. -/
private theorem presentationExtAlong_comp_of_square {z : 𝒳}
    {V : Space.SmallEtale C S hS G.arrows.obj} {W : Space.SmallEtale C S hS G.objects.obj}
    (a : F.obj (arrowChartPoint G V) ⟶ F.obj (chartPoint G W))
    (ha : ∀ x, presentationArrowChartSectionValue F hF χ V (M.val.map a.op x) =
      H.val.map a.op (presentationChartSectionValue F hF φ W x))
    (j : z ⟶ F.obj (arrowChartPoint G V))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W))
    (hz : IsAffineOver C S hS (p.obj z)) :
    presentationExtAlong F hF φ hM (j ≫ a) hW hz =
      presentationArrowExtAlong F hF χ hM j hV hz :=
  FibredSite.extendAlong_comp M hM j (presentation_isAffineOver F hF hV) hz H a
    (presentation_isAffineOver F hF hW) _ _ fun x =>
    (H.val.map_comp_apply a.op j.op _).trans (congrArg (H.val.map j.op) (ha x).symm)

/-- Extending `φ` along a morphism through a square of charts over the source is extending `χ`. -/
theorem presentationExtAlong_src {z : 𝒳}
    (hsq : presentationSourceComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ presentationSourceComparison F hF H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.source.hom)
    (j : z ⟶ F.obj (arrowChartPoint G d.U))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj d.V))
    (hz : IsAffineOver C S hS (p.obj z)) :
    presentationExtAlong F hF φ hM (j ≫ F.map
        (chartDiagramPoint G G.source.hom d.U d.V d.g d.comm)) hW hz =
      presentationArrowExtAlong F hF χ hM j hV hz := by
  exact presentationExtAlong_comp_of_square F hF φ χ hM _
    (presentationSource_square_app F hF φ χ hsq d) j hV hW hz

/-- Extending `φ` along a morphism through a square of charts over the target is extending `χ`. -/
theorem presentationExtAlong_tgt {z : 𝒳}
    (hsq : presentationTargetComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ presentationTargetComparison F hF H)
    (d : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.target.hom)
    (g : arrowChartPoint G d.U ⟶
        ⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U,
          G.target.hom.app _ (yonedaEquiv d.U.obj.hom)⟩)
    (hg : Space.comparisonMorphism C S hS (spaceProj G.arrows) (spaceProj G.objects)
        (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
        (pointwisePresentationSource F) (pointwisePresentationObject F)
        (pointwisePresentationTwoIso F) G.target (spaceFunctorChartIso G.target) d =
      F.map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm))
    (j : z ⟶ F.obj (arrowChartPoint G d.U))
    (hV : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj d.U))
    (hW : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj d.V))
    (hz : IsAffineOver C S hS (p.obj z)) :
    presentationExtAlong F hF φ hM (j ≫ F.map
        (g ≫ chartDiagramPoint G G.target.hom d.U d.V d.g d.comm)) hW hz =
      presentationArrowExtAlong F hF χ hM j hV hz := by
  exact presentationExtAlong_comp_of_square F hF φ χ hM _
    (presentationTarget_square_app F hF φ χ hsq d g hg) j hV hW hz

/-- **The extension over a charted point is compatible with every arrow to a chart.**  For an
arrow `q` of the pointwise groupoid fibration from a charted point to the point of an affine
chart `W'` of `U` (a point of `R`, possibly not an identity), the extension sends `q^*f` to
`q^*φ(f)`.  Fppf locally on the base, `q` factors through an affine chart of `R` carrying
squares of charts over the source and the target, and both are then the extension of `χ`. -/
theorem presentationChartedExtension_naturality
    (hsqs : presentationSourceComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ presentationSourceComparison F hF H)
    (hsqt : presentationTargetComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ presentationTargetComparison F hF H)
    (c : ChartedPoint G) {W' : Space.SmallEtale C S hS G.objects.obj}
    (hW' : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W'))
    (q : c.toPoint ⟶ chartPoint G W')
    (x : M.val.obj (op (F.obj (chartPoint G W')))) :
    presentationChartedExtension F hF φ hM c (M.val.map (F.map q).op x) =
      H.val.map (F.map q).op (presentationChartSectionValue F hF φ W' x) := by
  let ρ := pointwiseArrow G q
  have hρs : G.source.hom.app _ ρ = c.pt :=
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ q.fiber).2.1
  have hρt : G.target.hom.app _ ρ = G.objects.obj.map q.base.op (yonedaEquiv W'.obj.hom) :=
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ q.fiber).2.2
  refine presentationSections_ext F hF H c.toPoint (Space.generate_twoChartPresieve_mem C S hS
    G.source G.target ρ c.W W' c.g q.base (hρs.trans c.hpt) hρt) (fun T' k hk => ?_)
  obtain ⟨hT', V, hV, kV, ds, dt, hcs, hct, hρk, hg₁, hg₂⟩ := hk
  let dS : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.source.hom :=
    ⟨V, c.W, ds, hcs⟩
  let dT : Space.ChartDiagram C S hS G.arrows.obj G.objects.obj G.target.hom :=
    ⟨V, W', dt, hct⟩
  obtain ⟨g₀, hg₀b, hg₀a, hg₀⟩ := presentationTarget_comparisonMorphism F dT
  have hK : G.objects.obj.map k.op c.pt =
      G.objects.obj.map kV.op (G.source.hom.app _ (yonedaEquiv V.obj.hom)) := by
    rw [← NatTrans.naturality_apply, ← hρk, NatTrans.naturality_apply, hρs]
  let mK : (c.restrict k hT').toPoint ⟶ arrowChartPoint G V := ⟨kV, eqToHom hK⟩
  have hmK : pointwiseArrow G mK = G.toGroupoidInFunctors.identity _ (c.restrict k hT').pt :=
    evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ hK
  have h₁ : mK ≫ chartDiagramPoint G G.source.hom dS.U dS.V dS.g dS.comm =
      (c.restrict k hT').special := by
    apply pointwiseHom_ext G.toGroupoidInFunctors
    · exact hg₁.symm
    · refine (pointwiseArrow_comp_of_left G _ _ hmK).trans ?_
      rw [pointwiseArrow_chartDiagramPoint]
      refine (Deformation.evalMap_identity G.toGroupoidInFunctors kV.op _).trans ?_
      exact (congrArg (G.toGroupoidInFunctors.identity _) hK.symm).trans
        (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ (c.restrict k hT').hpt).symm
  have h₂ : mK ≫ g₀ ≫ chartDiagramPoint G G.target.hom dT.U dT.V dT.g dT.comm =
      pointwiseSpecial G k c.pt ≫ q := by
    apply pointwiseHom_ext G.toGroupoidInFunctors
    · show kV ≫ g₀.base ≫ dt = k ≫ q.base
      rw [hg₀b, Category.id_comp, hg₂]
    · refine (pointwiseArrow_comp_of_left G _ _ hmK).trans ?_
      refine Eq.trans ?_ (pointwiseArrow_comp_of_left G _ _ rfl).symm
      rw [pointwiseArrow_comp_of_right G _ _ (pointwiseArrow_chartDiagramPoint G _ _ _ _ _)]
      exact (congrArg (G.arrows.obj.map kV.op) hg₀a).trans hρk.symm
  have hVa : IsAffineOver C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj dS.U) := hV
  let j := F.map mK
  have e₁ : presentationChartedExtension F hF φ hM (c.restrict k hT') =
      presentationArrowExtAlong F hF χ hM j hVa (presentation_isAffineOver F hF hT') := by
    refine Eq.trans ?_
      (presentationExtAlong_src F hF φ χ hM hsqs dS j hVa c.hW (presentation_isAffineOver F hF hT'))
    exact presentationExtAlong_congr F hF φ hM ((congrArg F.map h₁).symm.trans
      (F.map_comp _ _)) _ _
  have e₂ : presentationExtAlong F hF φ hM (F.map (pointwiseSpecial G k c.pt ≫ q))
      hW' (presentation_isAffineOver F hF hT') =
      presentationArrowExtAlong F hF χ hM j hVa (presentation_isAffineOver F hF hT') := by
    refine Eq.trans ?_ (presentationExtAlong_tgt F hF φ χ hM hsqt dT g₀ hg₀ j hVa hW'
      (presentation_isAffineOver F hF hT'))
    exact presentationExtAlong_congr F hF φ hM ((congrArg F.map h₂).symm.trans
      (F.map_comp _ _)) _ _
  refine (presentationMap_chartedExtension F hF φ hM c k hT' _).trans ?_
  rw [e₁, ← e₂]
  have hcomp : F.map (pointwiseSpecial G k c.pt ≫ q) =
      F.map (pointwiseSpecial G k c.pt) ≫ F.map q :=
    F.map_comp _ _
  have hx : M.val.map (F.map (pointwiseSpecial G k c.pt)).op
      (M.val.map (F.map q).op x) =
      M.val.map (F.map (pointwiseSpecial G k c.pt ≫ q)).op x := by
    rw [hcomp, op_comp]
    exact (M.val.map_comp_apply (F.map q).op (F.map (pointwiseSpecial G k c.pt)).op x).symm
  refine (congrArg (presentationExtAlong F hF φ hM (F.map
    (pointwiseSpecial G k c.pt ≫ q)) hW' (presentation_isAffineOver F hF hT')) hx).trans ?_
  refine (FibredSite.extendAlong_map M hM (F.map (pointwiseSpecial G k c.pt ≫ q))
    (presentation_isAffineOver F hF hW') (presentation_isAffineOver F hF hT') H _ x).trans ?_
  show H.val.map (F.map (pointwiseSpecial G k c.pt ≫ q)).op
    (presentationChartSectionValue F hF φ W' x) = _
  rw [hcomp, op_comp]
  exact H.val.map_comp_apply _ _ _


end PtExt

section PtGlue

attribute [local instance] FibredSite.objModule

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  {hp : p.IsFiberedInGroupoids}

variable {M H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)}
  (φ : presentationObjectRestriction F hF M ⟶
    presentationObjectRestriction F hF H) (χ : presentationArrowRestriction F hF M ⟶
        presentationArrowRestriction F hF H)
  (hM : M.IsQuasicoherentOnSite)

/-- **The extensions over charted points are natural** for every arrow of `𝒳` between charted
points.  Both sides are semilinear and agree on restrictions of sections over the chart of the
target, where they are `AlgebraicGeometry.Stack.chartedExtension_naturality`. -/
theorem presentationChartedExtension_map
    (hsqs : presentationSourceComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ presentationSourceComparison F hF H)
    (hsqt : presentationTargetComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ presentationTargetComparison F hF H)
    {c₁ c₂ : ChartedPointCat G} (m : c₁ ⟶ c₂)
    (σ : M.val.obj (op ((presentationChartedPointFunctor F).obj c₂))) :
    presentationChartedExtension F hF φ hM c₁
        (M.val.map ((presentationChartedPointFunctor F).map m).op σ) =
      H.val.map ((presentationChartedPointFunctor F).map m).op
        (presentationChartedExtension F hF φ hM c₂ σ) := by
  let τ : FibredSite.objRing C S hS p ((presentationChartedPointFunctor F).obj c₂) →+*
      FibredSite.objRing C S hS p ((presentationChartedPointFunctor F).obj c₁) :=
    ((FibredSite.ringStructureSheafCore C S hS p
      hp .fppf).obj.map ((presentationChartedPointFunctor F).map m).op).hom
  let L₁ : M.val.obj (op ((presentationChartedPointFunctor F).obj c₂)) →ₛₗ[τ]
      H.val.obj (op ((presentationChartedPointFunctor F).obj c₁)) :=
    { toFun := fun t => presentationChartedExtension F hF φ hM c₁
        (M.val.map ((presentationChartedPointFunctor F).map m).op t)
      map_add' := fun a b => (congrArg (presentationChartedExtension F hF φ hM c₁)
        (map_add (M.val.map ((presentationChartedPointFunctor F).map m).op).hom a b)).trans
        (map_add _ _ _)
      map_smul' := fun r a => (congrArg (presentationChartedExtension F hF φ hM c₁)
        (M.val.map_smul ((presentationChartedPointFunctor F).map m).op r a)).trans
        (map_smul _ _ _) }
  let L₂ : M.val.obj (op ((presentationChartedPointFunctor F).obj c₂)) →ₛₗ[τ]
      H.val.obj (op ((presentationChartedPointFunctor F).obj c₁)) :=
    { toFun := fun t => H.val.map ((presentationChartedPointFunctor F).map m).op
        (presentationChartedExtension F hF φ hM c₂ t)
      map_add' := fun a b => (congrArg (H.val.map ((presentationChartedPointFunctor F).map m).op)
        (map_add (presentationChartedExtension F hF φ hM c₂) a b)).trans (map_add _ _ _)
      map_smul' := fun r a => (congrArg (H.val.map ((presentationChartedPointFunctor F).map m).op)
        (map_smul (presentationChartedExtension F hF φ hM c₂) r a)).trans
        (H.val.map_smul ((presentationChartedPointFunctor F).map m).op r _) }
  have := FibredSite.semilinearMap_ext_of_restriction M hM (presentationChartMap F c₂)
    (presentation_isAffineOver (w := chartPoint G c₂.W) F hF c₂.hW)
    (presentation_isAffineOver (w := c₂.toPoint) F hF c₂.hT) (θ₁ := L₁) (θ₂ := L₂)
    (fun x => by
      show presentationChartedExtension F hF φ hM c₁
          (M.val.map ((presentationChartedPointFunctor F).map m).op
            (M.val.map (presentationChartMap F c₂).op x)) =
        H.val.map ((presentationChartedPointFunctor F).map m).op
          (presentationChartedExtension F hF φ hM c₂ (M.val.map (presentationChartMap F c₂).op x))
      rw [presentationChartedExtension_chartMap]
      have hm : (presentationChartedPointFunctor F).map m = F.map m.hom := rfl
      rw [hm]
      have hq : F.map (m.hom ≫ c₂.special) =
          F.map m.hom ≫ (presentationChartMap F c₂) :=
        F.map_comp _ _
      have e1 : M.val.map (F.map (m.hom ≫ c₂.special)).op x =
          M.val.map (F.map m.hom).op (M.val.map (presentationChartMap F c₂).op x) := by
        rw [hq]; exact M.val.map_comp_apply _ _ x
      have e2 : H.val.map (F.map (m.hom ≫ c₂.special)).op
            (presentationChartSectionValue F hF φ c₂.W x) =
          H.val.map (F.map m.hom).op
            (H.val.map (presentationChartMap F c₂).op
              (presentationChartSectionValue F hF φ c₂.W x)) := by
        rw [hq]; exact H.val.map_comp_apply _ _ _
      refine (congrArg (presentationChartedExtension F hF φ hM c₁) e1.symm).trans (Eq.trans ?_ e2)
      exact presentationChartedExtension_naturality F hF φ χ hM hsqs hsqt c₁ c₂.hW _ x)
  exact LinearMap.congr_fun this σ

variable [F.Full] [F.Faithful] (hloc : ∀ y : 𝒳, ∃ (I : Type u) (x : I → PointwiseFibration G)
  (g : ∀ i, F.obj (x i) ⟶ y),
    Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS p .fppf y)

include hF hloc

/-- The sheaf of sets of sections of a module on the fppf site of `𝒳`. -/
noncomputable abbrev presentationSectionsSheaf
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)) : Sheaf
    (BigFppfOver.associatedTopology C S hS p .fppf) (Type u) :=
  ⟨M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}, M.isSheaf_sections⟩

/-- A section of a module on `𝒳` is determined by its restrictions to charted points. -/
theorem presentationSections_ext_of_chartedPoint
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)) {y : 𝒳}
    {σ τ : M.val.obj (op y)}
    (h : ∀ ⦃c : ChartedPointCat G⦄ (f : (presentationChartedPointFunctor F).obj c ⟶ y),
      M.val.map f.op σ = M.val.map f.op τ) : σ = τ :=
  have := isCoverDense_presentationChartedPointFunctor F hF hp hloc
  Functor.IsCoverDense.ext (presentationChartedPointFunctor F) (presentationSectionsSheaf M) y h

variable (hsqs : presentationSourceComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.source).map φ ≫ presentationSourceComparison F hF H)
    (hsqt : presentationTargetComparison F hF M ≫ χ =
      (Space.modulePullback C S hS G.target).map φ ≫ presentationTargetComparison F hF H)

/-- The extensions over the charted points, as a morphism of abelian presheaves on the charted
points. -/
noncomputable def presentationChartedExtensionTrans :
    (presentationChartedPointFunctor F).op ⋙ M.val.presheaf ⟶
      (presentationChartedPointFunctor F).op ⋙ H.val.presheaf where
  app c := AddCommGrpCat.ofHom (presentationChartedExtension F hF φ hM c.unop).toAddMonoidHom
  naturality c₁ c₂ m := by
    ext σ
    exact presentationChartedExtension_map F hF φ χ hM hsqs hsqt m.unop σ

/-- The morphism of abelian presheaves on `𝒳` glued from the extensions over the charted
points along the cover-dense full subcategory of charted points. -/
noncomputable def presentationChartedGluedPresheafHom : M.val.presheaf ⟶ H.val.presheaf :=
  haveI := isCoverDense_presentationChartedPointFunctor F hF hp hloc
  (Functor.IsCoverDense.restrictHomEquivHom (G := presentationChartedPointFunctor F) (K :=
      BigFppfOver.associatedTopology C S hS p .fppf)
    (ℱ' := ⟨H.val.presheaf, H.isSheaf⟩)) (presentationChartedExtensionTrans F hF φ χ hM hsqs hsqt)

/-- Over a charted point, the glued morphism is the extension. -/
theorem presentationChartedGluedPresheafHom_app (c : ChartedPointCat G)
    (σ : M.val.obj (op ((presentationChartedPointFunctor F).obj c))) :
    (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt).app
        (op ((presentationChartedPointFunctor F).obj c)) σ =
      presentationChartedExtension F hF φ hM c σ := by
  have := isCoverDense_presentationChartedPointFunctor F hF hp hloc
  have h := Functor.IsCoverDense.sheafHom_restrict_eq (G := presentationChartedPointFunctor F) (K :=
      BigFppfOver.associatedTopology C S hS p .fppf)
    (ℱ' := ⟨H.val.presheaf, H.isSheaf⟩) (presentationChartedExtensionTrans F hF φ χ hM hsqs hsqt)
  exact congrArg (fun f => f σ) (congrArg (fun t => (t.app (op c)).hom) h)

/-- Naturality of the glued morphism, on sections. -/
theorem presentationChartedGluedPresheafHom_naturality {y y' : 𝒳} (f : y' ⟶ y)
    (σ : M.val.obj (op y)) :
    (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt).app (op y')
        (M.val.map f.op σ) =
      H.val.map f.op
        ((presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt).app (op y) σ) :=
  NatTrans.naturality_apply (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt) f.op σ

/-- The glued morphism is linear: it is so over charted points, and those cover. -/
theorem presentationChartedGluedPresheafHom_smul (y : 𝒳)
    (r : (FibredSite.ringStructureSheafCore C S hS p
      hp .fppf).obj.obj (op y))
    (σ : M.val.obj (op y)) :
    (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt).app (op y) (r • σ) =
      r • (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt).app (op y) σ := by
  refine presentationSections_ext_of_chartedPoint F hF hloc H (fun c f => ?_)
  rw [← presentationChartedGluedPresheafHom_naturality, M.val.map_smul]
  refine Eq.trans ?_ (H.val.map_smul f.op r _).symm
  rw [← presentationChartedGluedPresheafHom_naturality]
  refine (presentationChartedGluedPresheafHom_app F hF φ χ hM hloc hsqs hsqt c _).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => _ • t)
    (presentationChartedGluedPresheafHom_app F hF φ χ hM hloc hsqs hsqt c _)).symm
  exact map_smul (presentationChartedExtension F hF φ hM c) _ _

/-- **The morphism of modules glued from a compatible `φ`.** -/
noncomputable def presentationChartedGluedHom : M ⟶ H :=
  ⟨PresheafOfModules.homMk (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt)
    (fun y r σ => presentationChartedGluedPresheafHom_smul F hF φ χ hM hloc hsqs hsqt y.unop r σ)⟩

/-- The sections of the glued morphism of modules. -/
theorem presentationChartedGluedHom_app (y : 𝒳) (σ : M.val.obj (op y)) :
    (presentationChartedGluedHom F hF φ χ hM hloc hsqs hsqt).val.app (op y) σ =
      (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt).app (op y) σ := rfl

/-- `φ` is natural for morphisms of étale charts of `U`, on sections. -/
theorem presentationChartSectionValue_naturality {W₁ W₂ : Space.SmallEtale C S hS G.objects.obj}
    (i : W₁ ⟶ W₂)
    (t : M.val.obj (op (F.obj (chartPoint G W₂)))) :
    presentationChartSectionValue F hF φ W₁ (M.val.map (F.map (chartPointHom G i)).op t) =
      H.val.map (F.map (chartPointHom G i)).op (presentationChartSectionValue F hF φ W₂
          t) :=
  congrArg (fun f => f.hom t) (φ.val.naturality i.op)

/-- Over the image of an étale chart of `U`, the glued morphism is `φ`.  An affine open cover of
the chart reduces this to charted points, where the glued morphism is the extension. -/
theorem presentationChartedGluedHom_chart (W : Space.SmallEtale C S hS G.objects.obj)
    (t : M.val.obj (op (F.obj (chartPoint G W)))) :
    (presentationChartedGluedPresheafHom F hF φ χ hM hloc hsqs hsqt).app (op (F.obj
      (chartPoint G W))) t = presentationChartSectionValue F hF φ W t := by
  obtain ⟨J, V, π, hV, hπ, hcov⟩ := BigFppfOver.exists_affine_open_cover C S hS
    ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
  refine presentationSections_ext F hF H (chartPoint G W)
    (P := fun T' k => IsAffineOver C S hS T' ∧ ∃ (j : J) (e : T' ⟶ V j), e ≫ π j = k)
    ((BigFppfOver.topology C S hS).superset_covering ?_
      (BigFppfOver.generate_affine_mem C S hS hcov)) (fun T' k hk => ?_)
  · rintro T'' k ⟨T', e₁, e₂, ⟨he₂, hT'⟩, rfl⟩
    obtain ⟨T₃, e₃, e₄, ⟨j⟩, rfl⟩ := he₂
    exact ⟨T', e₁, e₃ ≫ π j, ⟨hT', j, e₃, rfl⟩, rfl⟩
  obtain ⟨hT', j, e, rfl⟩ := hk
  have hπj : Space.IsEtaleChart C S hS G.objects.obj
      (CostructuredArrow.mk (yoneda.map (π j) ≫ W.obj.hom)) := by
    have := hπ j
    exact Space.etale_comp_of_scheme C S hS (π j) W.obj.hom inferInstance W.property
  let Wj : Space.SmallEtale C S hS G.objects.obj := ⟨_, hπj⟩
  let ι : Wj ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk (π j) rfl)
  let c : ChartedPoint G := ⟨T', hT', G.objects.obj.map (e ≫ π j).op (yonedaEquiv W.obj.hom),
    Wj, hV j, e, by
      rw [op_comp, Functor.map_comp_apply]
      exact congrArg (G.objects.obj.map e.op) (chartPointHom_eq ι).symm⟩
  have hsp : pointwiseSpecial G (e ≫ π j) (yonedaEquiv W.obj.hom) =
      c.special ≫ chartPointHom G ι := by
    apply pointwiseHom_ext G.toGroupoidInFunctors
    · rfl
    · refine Eq.trans ?_ (pointwiseArrow_comp_of_right G _ _
        (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ (chartPointHom_eq ι))).symm
      exact (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ c.hpt).symm
  have hsp' : F.map (pointwiseSpecial G (e ≫ π j) (yonedaEquiv W.obj.hom)) =
      presentationChartMap F c ≫ F.map (chartPointHom G ι) := by
    rw [hsp]; exact F.map_comp _ _
  let sp := F.map (pointwiseSpecial G (e ≫ π j) (yonedaEquiv W.obj.hom))
  let m := F.map (chartPointHom G ι)
  have hM' : M.val.map sp.op t = M.val.map (presentationChartMap F c).op (M.val.map m.op t) :=
    (congrArg (fun f : F.obj c.toPoint ⟶
      F.obj (chartPoint G W) => M.val.map f.op t) hsp').trans
      (M.val.map_comp_apply _ _ t)
  have hH' : ∀ z, H.val.map sp.op z =
      H.val.map (presentationChartMap F c).op (H.val.map m.op z) := fun z =>
    (congrArg (fun f : F.obj c.toPoint ⟶
      F.obj (chartPoint G W) => H.val.map f.op z) hsp').trans
      (H.val.map_comp_apply _ _ z)
  refine (presentationChartedGluedPresheafHom_naturality F hF φ χ hM hloc hsqs hsqt sp
    t).symm.trans ?_
  refine (presentationChartedGluedPresheafHom_app F hF φ χ hM hloc hsqs hsqt c
    (M.val.map sp.op t)).trans ?_
  rw [hM']
  refine (presentationChartedExtension_chartMap F hF φ hM c (M.val.map m.op t)).trans ?_
  rw [presentationChartSectionValue_naturality (hloc := hloc)]
  exact (hH' _).symm

/-- **The glued morphism restricts to `φ`.** -/
theorem presentationObjectRestrictionMap_chartedGluedHom : presentationObjectRestrictionMap F hF
    (presentationChartedGluedHom F hF φ χ hM hloc hsqs hsqt) = φ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  exact presentationChartedGluedHom_chart F hF φ χ hM hloc hsqs hsqt W.unop t

end PtGlue

section PtRestriction

attribute [local instance] FibredSite.objModule

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  {hp : p.IsFiberedInGroupoids}
  {M H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)}
  (hM : M.IsQuasicoherentOnSite)

/-- A morphism of modules is, over a charted point, the extension of its restriction to `U`. -/
theorem presentationApp_eq_chartedExtension (ψ : M ⟶ H) (c : ChartedPoint G)
    (σ : M.val.obj (op ((presentationChartedPointFunctor F).obj c))) :
    ψ.val.app (op ((presentationChartedPointFunctor F).obj c)) σ =
      presentationChartedExtension F hF (presentationObjectRestrictionMap F hF ψ) hM c σ := by
  let L : M.val.obj (op ((presentationChartedPointFunctor F).obj c)) →ₗ[
      FibredSite.objRing C S hS p ((presentationChartedPointFunctor F).obj c)]
      H.val.obj (op ((presentationChartedPointFunctor F).obj c)) :=
    { toFun := fun x => ψ.val.app (op ((presentationChartedPointFunctor F).obj c)) x
      map_add' := map_add (ψ.val.app (op ((presentationChartedPointFunctor F).obj c))).hom
      map_smul' := (ψ.val.app (op ((presentationChartedPointFunctor F).obj c))).hom.map_smul }
  have := FibredSite.semilinearMap_ext_of_restriction M hM (presentationChartMap F c)
    (presentation_isAffineOver (w := chartPoint G c.W) F hF c.hW)
    (presentation_isAffineOver (w := c.toPoint) F hF c.hT) (θ₁ := L)
    (θ₂ := presentationChartedExtension F hF (presentationObjectRestrictionMap F hF ψ) hM c)
    (fun x => by
      rw [presentationChartedExtension_chartMap]
      exact PresheafOfModules.naturality_apply ψ.val (presentationChartMap F c).op x)
  exact LinearMap.congr_fun this σ

variable [F.Full] [F.Faithful] (hloc : ∀ y : 𝒳, ∃ (I : Type u) (x : I → PointwiseFibration G)
  (g : ∀ i, F.obj (x i) ⟶ y),
    Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS p .fppf y)

include hM hloc in
/-- **Injectivity in Stacks 076S** for a pointwise presentation: a morphism out of a
quasi-coherent module is determined by its restriction `x^*ψ|_{U_étale}`. -/
theorem presentationObjectRestrictionMap_injective {ψ₁ ψ₂ : M ⟶ H} (h :
    presentationObjectRestrictionMap F hF ψ₁ = presentationObjectRestrictionMap F hF ψ₂) :
    ψ₁ = ψ₂ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun y => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun σ => ?_)
  refine presentationSections_ext_of_chartedPoint F hF hloc H (fun c f => ?_)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  refine (presentationApp_eq_chartedExtension F hF hM ψ₁ c _).trans ?_
  refine Eq.trans ?_ (presentationApp_eq_chartedExtension F hF hM ψ₂ c _).symm
  rw [h]

end PtRestriction

section PtSquares

variable (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  {hp : p.IsFiberedInGroupoids}

/-- The square through the source commutes for the restriction of a morphism of modules: the
comparison map of equation 076R is natural in the module. -/
theorem presentationSource_square_restrictionMap
    {M H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)} (ψ : M ⟶ H) :
    presentationSourceComparison F hF M ≫ presentationArrowRestrictionMap F hF ψ =
      (Space.modulePullback C S hS G.source).map (presentationObjectRestrictionMap F hF ψ) ≫
          presentationSourceComparison F hF H :=
  Space.comparisonAlgebraicSpacesModules_naturality C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((fppfToEtaleSheafOfModules C S hS p hp).map ψ)

/-- The square through the target commutes for the restriction of a morphism of modules. -/
theorem presentationTarget_square_restrictionMap
    {M H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)} (ψ : M ⟶ H) :
    presentationTargetComparison F hF M ≫ presentationArrowRestrictionMap F hF ψ =
      (Space.modulePullback C S hS G.target).map (presentationObjectRestrictionMap F hF ψ) ≫
          presentationTargetComparison F hF H :=
  Space.comparisonAlgebraicSpacesModules_naturality C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((fppfToEtaleSheafOfModules C S hS p hp).map ψ)

variable [F.Full] [F.Faithful] (hloc : ∀ y : 𝒳, ∃ (I : Type u) (x : I → PointwiseFibration G)
  (g : ∀ i, F.obj (x i) ⟶ y),
    Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS p .fppf y)

include hloc in
/-- **Stacks 076S for a pointwise presentation.**  Let `(U, R, s, t, c)` be a groupoid in
algebraic spaces and `F` a fully faithful 1-morphism from its pointwise groupoid fibration to a
category `𝒳` fibred in groupoids over `(Sch/S)_{fppf}`, every object of which is fppf locally in
the image, and let `x` be the induced object of `𝒳` over `U`.  For a quasi-coherent
`𝒪_𝒳`-module `ℱ` and any `𝒪_𝒳`-module `ℋ`, the map `ψ ↦ x^*ψ|_{U_étale}` is injective, and its
image consists of exactly those `φ` for which some `χ` makes both squares through the comparison
maps of equation 076R commute. -/
theorem presentationObjectRestrictionMap_injective_and_range
    {M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)}
    (hM : M.IsQuasicoherentOnSite)
    (H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore C S hS p hp .fppf)) :
    Function.Injective (fun ψ : M ⟶ H => presentationObjectRestrictionMap F hF ψ) ∧
      ∀ φ : presentationObjectRestriction F hF M ⟶ presentationObjectRestriction F hF H,
        (∃ ψ : M ⟶ H, presentationObjectRestrictionMap F hF ψ = φ) ↔
          ∃ χ, presentationSourceComparison F hF M ≫ χ =
              (Space.modulePullback C S hS G.source).map φ ≫ presentationSourceComparison F hF H ∧
            presentationTargetComparison F hF M ≫ χ =
              (Space.modulePullback C S hS G.target).map φ ≫
                presentationTargetComparison F hF H := by
  refine ⟨fun ψ₁ ψ₂ h => presentationObjectRestrictionMap_injective F hF hM hloc h,
    fun φ => ⟨?_, ?_⟩⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨presentationArrowRestrictionMap F hF ψ, presentationSource_square_restrictionMap F hF ψ,
      presentationTarget_square_restrictionMap F hF ψ⟩
  · rintro ⟨χ, hs, ht⟩
    exact ⟨presentationChartedGluedHom F hF φ χ hM hloc hs ht,
      presentationObjectRestrictionMap_chartedGluedHom F hF φ χ hM hloc hs ht⟩

end PtSquares




end AlgebraicGeometry.Stack

