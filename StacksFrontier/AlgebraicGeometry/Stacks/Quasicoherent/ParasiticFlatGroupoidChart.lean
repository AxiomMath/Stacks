module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectFlatLift
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FiniteDisjointSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorSmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSheafFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations

/-!
# Parasitic modules are detected on the étale charts of a flat groupoid presentation

Let `𝒳` be an algebraic stack over `S`, with its flat groupoid presentation `(U, R, s, t, c)`
(`AlgebraicGeometry.Stack.flatGroupoidPresentation`) and the 1-morphism `x : U → 𝒳` given by
including the points of `U` into the pointwise groupoid fibration and applying the presentation.
Part (1) of **Stacks 0779** identifies the kernel of the functor `r` restricting a module in
`LQCoh^fbc(𝒪_𝒳)` to the groupoid with the parasitic modules. Its geometric half, proved here, is
the statement about objects: a module `ℱ` on `𝒳_fppf` in `LQCoh^fbc(𝒪_𝒳)` is parasitic
(**Stacks 0773**) exactly when its sections vanish at the image under `x` of every étale chart of
`U`, that is, when `ℱ|_{U_étale}` is zero.

The proof is the source's.

* *(⇒)* `U → 𝒳` is smooth, so the image under `x` of an étale chart `V → U` names the flat
  1-morphism `V → U → 𝒳`, i.e. it is a flat object of `𝒳` (Stacks 0H14).
* *(⇐)* Let `y : V → 𝒳` be flat. The projection `V ×_𝒳 U ⟶ U` is a base change of `y`, hence flat,
  and `V ×_𝒳 U ⟶ V` is smooth and surjective; a smooth presentation of `V ×_𝒳 U` by a scheme `T`
  gives an fppf covering `T ⟶ V` over which `y` becomes the image of a *flat* morphism `T ⟶ U`
  (`AlgebraicGeometry.Stack.exists_scheme_lift_flat_of_flatObject`). The flat base change property
  along the arrow from that image to the image of `1_U`, which lies over the flat `T ⟶ U`, kills
  the sections there, because the sections vanish at every object étale over the image of `1_U`.
  The fppf sheaf condition then kills the sections at `y`.

## Main results

* `AlgebraicGeometry.Stack.subsingleton_obj_of_hasFlatBaseChangePropertySheaf`: a sheaf with the
  flat base change property of Stacks 0762 vanishes at the source of an arrow over a flat morphism
  of schemes as soon as it vanishes étale-locally at its target.
* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.isParasitic_iff_forall_subsingleton_chart`:
  the statement for the flat groupoid presentation attached to any presentation by a scheme.
* `AlgebraicGeometry.Stack.isParasitic_iff_forall_subsingleton_flatGroupoidPresentation_chart`:
  **Stacks 0779 (1)**, the geometric half, for `AlgebraicGeometry.Stack.flatGroupoidPresentation`.
* `AlgebraicGeometry.Space.isZero_etaleRestrictedModuleInverseImage_iff`: the restriction
  `f^*ℱ|_{U_étale}` vanishes exactly when the sections of `ℱ` vanish on the charts, which turns
  the right-hand side above into the vanishing of `ℱ|_{U_étale}`.

## Implementation notes

The étale charts are those of the object space `U = P.G.objects` of the groupoid; the base space
`P.A` of the presentation is the final algebraic space and is not the space the restriction is
taken to. The étale chart `c` is read in `𝒳` through
`AlgebraicGeometry.Space.restrictionFunctor` at the identity equivalence, which is the functor
along which `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` restricts; so the
right-hand side is the vanishing of the sections of `ℱ|_{U_étale}` over every chart.

The presentation `AlgebraicGeometry.Stack.FlatGroupoidPresentation.ofScheme` comes from a smooth
surjective 1-morphism `f : 𝒮_W ⟶ 𝒳` with `U` the space represented by `W`, and the comparison of
Stacks 04T4 (5) identifies `x(c)` with `f(V → W)` up to a vertical isomorphism
(`AlgebraicGeometry.Stack.FlatGroupoidPresentation.chartObjIso`); the whole argument runs through
`f`. Only the flat base change property of `ℱ` is used, not its local quasi-coherence.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

section General

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Vanishing of the sections of a presheaf of modules is invariant under isomorphism of
objects: restriction along an isomorphism is a bijection of sections. -/
theorem subsingleton_obj_of_iso {R : 𝒳ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)
    {a b : 𝒳} (e : a ≅ b) (hb : Subsingleton (M.obj (op b))) :
    Subsingleton (M.obj (op a)) := by
  refine ⟨fun m n => ?_⟩
  have key : ∀ k : M.obj (op a), M.map e.hom.op (M.map e.inv.op k) = k := fun k => by
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.hom_inv_id, op_id, M.map_id]
    rfl
  rw [← key m, ← key n, hb.elim (M.map e.inv.op m) (M.map e.inv.op n)]

/-- A sheaf of modules is zero as soon as its sections vanish at every object. -/
private theorem isZero_of_forall_subsingleton_obj {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}
    (h : ∀ V, Subsingleton (M.val.obj V)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  ext m
  exact (h V).elim _ _

/-- The sections of a zero sheaf of modules vanish at every object. -/
private theorem subsingleton_obj_of_isZero {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}
    (hz : IsZero M) (V : Cᵒᵖ) : Subsingleton (M.val.obj V) :=
  ModuleCat.subsingleton_of_isZero (Functor.map_isZero (SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ V) hz)

/-- A sheaf of modules on the small étale site of the scheme below `x` vanishes as soon as the
sections of the presheaf of modules on `𝒳` vanish at every object the restriction of Stacks 06W1
evaluates at. -/
theorem isZero_restrictModuleToSmallEtaleSheafFunctor_obj (x : 𝒳)
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hℱ : ∀ V, Subsingleton (ℱ.val.obj (op ((smallEtaleToStack B E h S hS p hp x).obj V)))) :
    IsZero ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).obj ℱ) := by
  exact isZero_of_forall_subsingleton_obj fun V => hℱ V.unop

/-- If the restriction of a sheaf of modules to the small étale site of the scheme below `z`
vanishes, then so do its sections at `z`: those are the sections of the restriction at the final
object of the small étale site. -/
theorem subsingleton_obj_of_isZero_restrictModuleToSmallEtaleSheafFunctor_obj (z : 𝒳)
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hz : IsZero ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp z).obj ℱ)) :
    Subsingleton (ℱ.val.obj (op z)) := by
  have h₂ := subsingleton_obj_of_isZero hz (op (smallEtaleFinal B E h S hS p z))
  exact subsingleton_obj_of_iso ℱ.val (smallEtaleFinalObjectIso B E h S hS p hp z).symm h₂

/-- **Flat base change kills a module along a flat arrow into an object where it vanishes
étale-locally.** Let `ℱ` be a sheaf of modules on `𝒳_étale` with the flat base change property of
Stacks 0762, read on sheaves of modules, and let `φ : z ⟶ x` lie over a flat morphism of schemes.
If the sections of `ℱ` vanish at every object of `𝒳` named by the small étale site of the scheme
below `x`, then they vanish at `z`. -/
theorem subsingleton_obj_of_hasFlatBaseChangePropertySheaf
    (ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hℱ : HasFlatBaseChangePropertySheaf B E h S hS p hp ℱ)
    {x z : 𝒳} (φ : z ⟶ x) (hφ : Flat (B.inclusion.map (p.map φ).left))
    (hx : ∀ V, Subsingleton (ℱ.val.obj (op ((smallEtaleToStack B E h S hS p hp x).obj V)))) :
    Subsingleton (ℱ.val.obj (op z)) := by
  have hzx := isZero_restrictModuleToSmallEtaleSheafFunctor_obj B E h S hS p hp x ℱ hx
  have : IsIso ((sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ).app ℱ) := hℱ φ hφ
  have hpb : IsZero ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).obj
        ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).obj ℱ)) :=
    Functor.map_isZero _ hzx
  exact subsingleton_obj_of_isZero_restrictModuleToSmallEtaleSheafFunctor_obj B E h S hS p hp z ℱ
    (hpb.of_iso (asIso ((sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ).app ℱ)).symm)

/-- A morphism of schemes over a base which is isomorphic, over that base, to an étale one is
étale. -/
theorem etale_of_iso_of_etale {Y : B.Schemes} {W Z : Over Y}
    (e : W ≅ Z) (hZ : Etale (B.inclusion.map Z.hom)) :
    Etale (B.inclusion.map W.hom) := by
  have h1 : Over.Hom.left e.hom ≫ Z.hom = W.hom := Over.w e.hom
  have hiso : IsIso (Over.Hom.left e.hom) := by
    simpa using (Over.forget Y).map_isIso e.hom
  have het : Etale (B.inclusion.map (Over.Hom.left e.hom) ≫ B.inclusion.map Z.hom) :=
    inferInstance
  exact h1 ▸ (B.inclusion.map_comp (Over.Hom.left e.hom) Z.hom ▸ het)

/-- **Every object named by the small étale site of the scheme below `x` maps to `x` over an étale
morphism of schemes.** The object comes, through the localization equivalence of Stacks 06W0, with
a morphism to `x`, and that morphism lies over the étale structure morphism of the small étale
object, up to the counit of the equivalence. -/
theorem exists_smallEtaleToStack_obj_hom_etale (x : 𝒳)
    (V : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    ∃ g : (smallEtaleToStack B E h S hS p hp x).obj V ⟶ x,
      Etale (B.inclusion.map (p.map g).left) := by
  have := isEquivalence_overPost B S hS p hp x
  exact ⟨((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
      ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj V)).hom,
    etale_of_iso_of_etale B
      ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.app
        ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj V))
      (smallEtaleInclusion_etale B E h _ _ V)⟩

/-- **A sheaf whose sections vanish over the source of a covering singleton vanishes.** If the
sieve generated by a single arrow `α : z ⟶ y` covers `y`, the sections of a sheaf of modules at
`y` inject into those at `z` by the sheaf condition, so they vanish when those at `z` do. -/
theorem subsingleton_obj_of_generate_singleton_mem {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R)
    {y z : C} (α : z ⟶ y) (hα : Sieve.generate (Presieve.singleton α) ∈ J y)
    (hz : Subsingleton (M.val.obj (op z))) :
    Subsingleton (M.val.obj (op y)) := by
  refine ⟨fun s t => ?_⟩
  refine ((SheafOfModules.isSheaf_sections M).isSheafFor _ hα).isSeparatedFor.ext ?_
  rintro Y g ⟨Z, k, -, ⟨⟩, rfl⟩
  show M.val.map (k ≫ α).op s = M.val.map (k ≫ α).op t
  rw [op_comp, PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply,
    hz.elim (M.val.map α.op s) (M.val.map α.op t)]

/-- A morphism property of schemes holding at the underlying morphism of schemes of a morphism
`g` of the site holds at the image under the structure functor of any arrow lying over `g`. -/
theorem prop_inclusion_map_left_of_isHomLift (P : MorphismProperty Scheme.{u})
    {a b : 𝒳} (φ : a ⟶ b) {T T' : BigFppfOver B S hS} (g : T ⟶ T') (hφ : p.IsHomLift g φ)
    (hg : P (B.inclusion.map g.left)) : P (B.inclusion.map (p.map φ).left) := by
  obtain rfl : p.obj a = T := IsHomLift.domain_eq p g φ
  obtain rfl : p.obj b = T' := IsHomLift.codomain_eq p g φ
  obtain rfl : g = p.map φ := IsHomLift.eq_of_isHomLift p g φ
  exact hg

include hp in
/-- **In a category fibred in groupoids, two arrows into the same object over the same morphism
of the base have isomorphic sources.** The second arrow is strongly cartesian, so the first
factors through it over the identity, and an arrow over an identity is an isomorphism. -/
theorem nonempty_iso_of_isHomLift {a a' b : 𝒳} (ψ : a ⟶ b) (ψ' : a' ⟶ b)
    {T T' : BigFppfOver B S hS} (g : T ⟶ T') (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ') :
    Nonempty (a ≅ a') := by
  have hcart : p.IsStronglyCartesian g ψ' := hp.isStronglyCartesian_homLift g ψ'
  obtain ⟨χ, ⟨hχ, -⟩, -⟩ :=
    Functor.IsStronglyCartesian.universal_property p g ψ' (𝟙 T) g (Category.id_comp g).symm ψ
  have : p.IsStronglyCartesian (𝟙 T) χ := hp.isStronglyCartesian_homLift (𝟙 T) χ
  have : IsIso χ := Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 T) χ
  exact ⟨asIso χ⟩

end General

section Charts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {W : BigFppfOver B S hS}

/-- The morphism of schemes `V ⟶ W` named by an étale chart `yoneda V ⟶ yoneda W` of the algebraic
space represented by `W` is étale. -/
theorem etale_yonedaEquiv_of_smallEtale (c : Space.SmallEtale B S hS (yoneda.obj W)) :
    Etale ((BigFppfOver.toScheme B S hS).map (yonedaEquiv c.obj.hom)) := by
  have hc : yoneda.map (yonedaEquiv c.obj.hom) = c.obj.hom :=
    yonedaEquiv.injective (yonedaEquiv_yoneda_map _)
  have := c.property
  rw [Space.IsEtaleChart, ← hc] at this
  exact (Space.presheaf_yoneda_map_iff B S hS inferInstance _).1 this

/-- The morphism of schemes `V ⟶ W` named by an étale chart of the algebraic space represented by
`W` is flat. -/
theorem flat_yonedaEquiv_of_smallEtale (c : Space.SmallEtale B S hS (yoneda.obj W)) :
    Flat ((BigFppfOver.toScheme B S hS).map (yonedaEquiv c.obj.hom)) := by
  have := etale_yonedaEquiv_of_smallEtale c
  infer_instance

/-- The étale chart of the algebraic space represented by `W` attached to an étale morphism of
schemes `V ⟶ W`. -/
def smallEtaleOfEtale {V : BigFppfOver B S hS} (e : V ⟶ W)
    (he : Etale ((BigFppfOver.toScheme B S hS).map e)) :
    Space.SmallEtale B S hS (yoneda.obj W) :=
  ⟨CostructuredArrow.mk (yoneda.map e), (Space.presheaf_yoneda_map_iff B S hS inferInstance e).2 he⟩

/-- The étale chart attached to an étale morphism of schemes names that morphism. -/
theorem yonedaEquiv_smallEtaleOfEtale {V : BigFppfOver B S hS} (e : V ⟶ W)
    (he : Etale ((BigFppfOver.toScheme B S hS).map e)) :
    yonedaEquiv (smallEtaleOfEtale e he).obj.hom = e :=
  yonedaEquiv_yoneda_map e

end Charts

namespace FlatGroupoidPresentation

open SelfIntersection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {W : BigFppfOver B S hS}
  (f : schemeFibredCategory B S hS W ⟶ 𝒳.val)
  (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
  (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
    (Space.smoothMorphismProperty B S hS) f hf)
  (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
    (Space.surjectiveMorphismProperty B S hS) f hf)
  {R : AlgebraicSpaces B S hS}
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS (schemeFibredCategory B S hS W) 𝒳.val f.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- The presenting 1-morphism `𝒮_W ⟶ 𝒳`, read in the 2-category of algebraic stacks. -/
abbrev presentationHom : schemeStack.{u, w} B S hS W ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom f

include hsmooth in
/-- The presenting 1-morphism is smooth (Stacks 06FM from its relative smoothness). -/
theorem isSmooth_presentationHom : AlgebraicStacks.IsSmooth B S hS (presentationHom f) :=
  hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property f hf hsmooth

include hsurj in
/-- The presenting 1-morphism is surjective (Stacks 04XI from its relative surjectivity). -/
theorem isSurjective_presentationHom : IsSurjective B S hS (presentationHom f) :=
  (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS (presentationHom f) hf).mpr
    hsurj

/-- **The object of `𝒳` named by an étale chart of `U` is the image of the chart under the
presentation.** For an étale chart `c : V → U = W` of the object space, the composite of the
inclusion of points with the 1-morphism of the presentation sends `c` to an object isomorphic to
`f(V → W)`: this is the comparison of Stacks 04T4 (5) with `f`. -/
def chartObjIso (c : Space.SmallEtale B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj) :
    (pointwiseObjectInclusion (ofScheme f hf hsmooth hsurj eR).G ⋙
        (ofScheme f hf hsmooth hsurj eR).F).obj
      ((Space.restrictionFunctor B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj
        (fibredCategory B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)).obj c) ≅
      f.hom.obj (Over.mk (yonedaEquiv c.obj.hom : c.obj.left ⟶ W)) :=
  eqToIso (congrArg (selfIntersectionDatum f eR).canonicalMap.toFunctor.obj
      ((selfIntersectionDatum f eR).sourcePresentation_pointwise
        (Over.mk (yonedaEquiv c.obj.hom : c.obj.left ⟶ W)))) ≪≫
    (selfIntersectionDatum f eR).extends_f.1.app (Over.mk (yonedaEquiv c.obj.hom : c.obj.left ⟶ W))

/-- The image under the presentation of an arrow `k` of the slice over `W` lies over the
underlying morphism `k.left` of the site. -/
theorem isHomLift_presentation_map {z z' : Over W} (k : z ⟶ z') :
    𝒳.val.val.p.IsHomLift k.left (f.hom.map k) := by
  have : (schemeFibredCategory B S hS W).val.p.IsHomLift k.left k :=
    IsHomLift.map (Over.forget W) k
  exact Functor.isHomLift_map_of_comp_eq f.hom.w k.left k

/-- An isomorphism of a category over the site lies over an isomorphism of schemes, which is
flat. -/
theorem flat_map_left_of_iso {𝒴 : Type*} [Category* 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS)
    {a b : 𝒴} (e : a ≅ b) : Flat (B.inclusion.map (q.map e.hom).left) := by
  have : IsIso ((Over.forget (B.obj hS)).map (q.map e.hom)) := inferInstance
  have : IsIso (q.map e.hom).left := this
  infer_instance

include hsmooth in
/-- The image under the presentation of the unit object `1_W` is a flat object of `𝒳`: the
presentation is smooth, so this image is a smooth object, hence flat. -/
theorem flatObject_presentation_unit : flatObject B S hS 𝒳.val (f.hom.obj (Over.mk (𝟙 W))) :=
  flatObject_of_smoothObject.{u, w} B S hS 𝒳
    (smoothObject_atlas_obj.{u, w} B S hS (presentationHom f)
      (isSmooth_presentationHom f hf hsmooth))

include hsmooth in
/-- The image under the presentation of a flat morphism of schemes `V ⟶ W` is a flat object of
`𝒳`: it maps to the image of `1_W` over that flat morphism. -/
theorem flatObject_presentation_obj {V : BigFppfOver B S hS} (e : V ⟶ W)
    (he : Flat ((BigFppfOver.toScheme B S hS).map e)) :
    flatObject B S hS 𝒳.val (f.hom.obj (Over.mk e)) := by
  let k : Over.mk e ⟶ Over.mk (𝟙 W) := Over.homMk e
  exact flatObject_of_flat B S hS 𝒳 (f.hom.map k)
    (prop_inclusion_map_left_of_isHomLift B S hS 𝒳.val.val.p @Flat (f.hom.map k) k.left
      (isHomLift_presentation_map f k) he)
    (flatObject_presentation_unit f hf hsmooth)

include hsmooth in
/-- **(⇒) A parasitic module vanishes on the objects named by the étale charts of `U`.** Such an
object is, up to isomorphism, the image under the smooth presentation of an étale morphism
`V ⟶ W`, which is a flat object of `𝒳`. -/
theorem subsingleton_chart_of_isParasitic
    (ℱ : PresheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf).obj)
    (hℱ : IsParasitic B S hS 𝒳 .fppf ℱ)
    (c : Space.SmallEtale B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj) :
    Subsingleton (ℱ.obj (op ((pointwiseObjectInclusion (ofScheme f hf hsmooth hsurj eR).G ⋙
        (ofScheme f hf hsmooth hsurj eR).F).obj
      ((Space.restrictionFunctor B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj
        (fibredCategory B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)).obj c)))) := by
  have hfl : Flat ((BigFppfOver.toScheme B S hS).map (yonedaEquiv c.obj.hom : c.obj.left ⟶ W)) :=
    flat_yonedaEquiv_of_smallEtale (W := W) c
  exact hℱ _ (flatObject_of_flat B S hS 𝒳 (chartObjIso f hf hsmooth hsurj eR c).hom
    (flat_map_left_of_iso _ _) (flatObject_presentation_obj f hf hsmooth _ hfl))

/-- **Vanishing on the charts of `U` propagates to every object étale over the image of `1_W`.**
An object `o` with an arrow `ψ : o ⟶ f(1_W)` over an étale morphism of schemes is isomorphic to the
image under the presentation of that étale morphism, which is the object named by an étale chart
of `U`. -/
theorem subsingleton_of_hom_presentation_unit_etale
    (ℱ : PresheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf).obj)
    (H : ∀ c : Space.SmallEtale B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj,
      Subsingleton (ℱ.obj (op ((pointwiseObjectInclusion (ofScheme f hf hsmooth hsurj eR).G ⋙
        (ofScheme f hf hsmooth hsurj eR).F).obj
      ((Space.restrictionFunctor B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj
        (fibredCategory B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)).obj c)))))
    {o : 𝒳.val.val.obj} (ψ : o ⟶ f.hom.obj (Over.mk (𝟙 W)))
    (hψ : Etale (B.inclusion.map (𝒳.val.val.p.map ψ).left)) :
    Subsingleton (ℱ.obj (op o)) := by
  have h0 : 𝒳.val.val.p.obj (f.hom.obj (Over.mk (𝟙 W))) = W :=
    Functor.congr_obj f.hom.w (Over.mk (𝟙 W))
  let g : 𝒳.val.val.p.obj o ⟶ W := 𝒳.val.val.p.map ψ ≫ eqToHom h0
  have hg : Etale ((BigFppfOver.toScheme B S hS).map g) := by
    show Etale (B.inclusion.map (𝒳.val.val.p.map ψ ≫ eqToHom h0).left)
    rw [Over.comp_left, Functor.map_comp, Over.eqToHom_left, eqToHom_map]
    infer_instance
  let c : Space.SmallEtale B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj :=
    smallEtaleOfEtale g hg
  have hc : Subsingleton (ℱ.obj (op (f.hom.obj (Over.mk g)))) := by
    have h1 := subsingleton_obj_of_iso ℱ (chartObjIso f hf hsmooth hsurj eR c).symm (H c)
    have h2 : (yonedaEquiv c.obj.hom : c.obj.left ⟶ W) = g := yonedaEquiv_smallEtaleOfEtale g hg
    rwa [h2] at h1
  let k : Over.mk g ⟶ Over.mk (𝟙 W) := Over.homMk g
  have hψ' : 𝒳.val.val.p.IsHomLift g ψ := inferInstance
  obtain ⟨e⟩ := nonempty_iso_of_isHomLift B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ψ
    (f.hom.map k) g hψ' (isHomLift_presentation_map f k)
  exact subsingleton_obj_of_iso ℱ e hc

/-- **(⇐) A module with the flat base change property which vanishes on the charts of `U` is
parasitic.** Let `y` be a flat object of `𝒳`, over `V`. By the source's construction of
Stacks 06QA at the 2-fibre product `V ×_𝒳 W`, there is a flat, locally finitely presented,
surjective `T ⟶ V`, a flat morphism `T ⟶ W` and an arrow `f(T → W) ⟶ y` over `T ⟶ V`
(`AlgebraicGeometry.Stack.exists_scheme_lift_flat_of_flatObject`). Flat base change along the
arrow `f(T → W) ⟶ f(1_W)`, which lies over the flat `T ⟶ W`, kills the sections at `f(T → W)`,
since those at the objects étale over `f(1_W)` vanish; and `f(T → W) ⟶ y` generates an fppf
covering sieve, so the sections at `y` inject into those at `f(T → W)`. -/
theorem isParasitic_of_forall_subsingleton_chart
    (ℱ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))
    (hℱ : HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).obj ℱ))
    (H : ∀ c : Space.SmallEtale B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj,
      Subsingleton (ℱ.val.obj (op ((pointwiseObjectInclusion (ofScheme f hf hsmooth hsurj eR).G ⋙
        (ofScheme f hf hsmooth hsurj eR).F).obj
      ((Space.restrictionFunctor B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj
        (fibredCategory B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)).obj c))))) :
    IsParasitic B S hS 𝒳 .fppf ℱ.val := by
  intro y hy
  have hsm := isSmooth_presentationHom f hf hsmooth
  obtain ⟨T, m, hmflat, hmlfp, hmsurj, z, α, hz, hα⟩ :=
    exists_scheme_lift_flat_of_flatObject B S hS (presentationHom f)
      (isSurjective_presentationHom f hf hsurj) (AlgebraicStacks.isFlat_of_isSmooth B S hS _ hsm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _ hsm) y hy
  -- the sections at the lift vanish, by flat base change along `f(z) ⟶ f(1_W)`
  have hfz : Subsingleton (ℱ.val.obj (op (f.hom.obj z))) := by
    let k : z ⟶ Over.mk (𝟙 W) := Over.homMk z.hom
    refine subsingleton_obj_of_hasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl
      S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).obj ℱ) hℱ
      (f.hom.map k) (prop_inclusion_map_left_of_isHomLift B S hS 𝒳.val.val.p @Flat
        (f.hom.map k) k.left (isHomLift_presentation_map f k) hz) (fun V => ?_)
    obtain ⟨g, hg⟩ := exists_smallEtaleToStack_obj_hom_etale B (associatedBigEtaleSite B) rfl
      S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _ V
    exact subsingleton_of_hom_presentation_unit_etale f hf hsmooth hsurj eR ℱ.val H g hg
  -- the lift covers `y` in the fppf topology
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have hcov : Sieve.generate (Presieve.singleton α) ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf y := by
    refine Functor.generate_singleton_mem_inheritedTopology_of_isHomLift 𝒳.val.val.p
      (BigFppfOver.baseOverTopology B S hS .fppf) α
      (𝒳.val.isFiberedInGroupoids.isStronglyCartesian α) _ hα
      (mem_topology_of_family B S hS (I := PUnit.{u + 2}) (fun _ => T) (fun _ => m)
        (fun _ => hmflat) (fun _ => hmlfp) (fun x => ⟨PUnit.unit, hmsurj.1 x⟩)) ?_
    rintro W' u ⟨W'', k, -, ⟨i⟩, rfl⟩
    exact ⟨k, rfl⟩
  exact subsingleton_obj_of_generate_singleton_mem ℱ α hcov hfz

/-- **Stacks 0779 (1), the geometric half, for the flat groupoid presentation attached to a
presentation by a scheme.** A module in `LQCoh^fbc` is parasitic exactly when its sections vanish
at the objects named by the étale charts of the object space `U = W`. -/
theorem isParasitic_iff_forall_subsingleton_chart
    (ℱ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))
    (hℱ : locallyQuasicoherentFlatBaseChangeSheafFppf B (associatedBigEtaleSite B) rfl S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ℱ) :
    IsParasitic B S hS 𝒳 .fppf ℱ.val ↔
      ∀ c : Space.SmallEtale B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj,
        Subsingleton (ℱ.val.obj (op ((pointwiseObjectInclusion (ofScheme f hf hsmooth hsurj eR).G ⋙
          (ofScheme f hf hsmooth hsurj eR).F).obj
          ((Space.restrictionFunctor B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj
            (fibredCategory B S hS (ofScheme f hf hsmooth hsurj eR).G.objects.obj).val.p
            (StacksRepresentableCFG.EquivalenceOver.refl _)).obj c)))) :=
  ⟨subsingleton_chart_of_isParasitic f hf hsmooth hsurj eR ℱ.val,
    isParasitic_of_forall_subsingleton_chart f hf hsmooth hsurj eR ℱ hℱ.2⟩

end FlatGroupoidPresentation

/-- **Stacks 0779 (1), the geometric half: a module in `LQCoh^fbc` is parasitic exactly when it
vanishes on the étale charts of the object space of the flat groupoid presentation.** Let `𝒳` be
an algebraic stack with its flat groupoid presentation `(U, R, s, t, c)` and its 1-morphism
`x : U → 𝒳`, and let `ℱ` be a module on `𝒳_fppf` in `LQCoh^fbc(𝒪_𝒳)`. Then `ℱ` is parasitic if and
only if its sections vanish at the image under `x` of every étale chart of `U`, i.e. the
restriction `ℱ|_{U_étale}` is zero.

For the forward direction, `U → 𝒳` is smooth, so the image of an étale chart is a flat object.
For the converse, a flat object `y : V → 𝒳` is covered, in the fppf topology, by the image of a
scheme `T` flat over `U` (the source's `V ×_𝒳 U`), at which the sections vanish by flat base
change from the charts of `U`. -/
theorem isParasitic_iff_forall_subsingleton_flatGroupoidPresentation_chart
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (ℱ : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))
    (hℱ : locallyQuasicoherentFlatBaseChangeSheafFppf B (associatedBigEtaleSite B) rfl S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ℱ) :
    IsParasitic B S hS 𝒳 .fppf ℱ.val ↔
      ∀ c : Space.SmallEtale B S hS (flatGroupoidPresentation 𝒳).G.objects.obj,
        Subsingleton (ℱ.val.obj (op ((pointwiseObjectInclusion (flatGroupoidPresentation 𝒳).G ⋙
          (flatGroupoidPresentation 𝒳).F).obj
          ((Space.restrictionFunctor B S hS (flatGroupoidPresentation 𝒳).G.objects.obj
            (fibredCategory B S hS (flatGroupoidPresentation 𝒳).G.objects.obj).val.p
            (StacksRepresentableCFG.EquivalenceOver.refl _)).obj c)))) := by
  let hP := 𝒳.property.choose_spec.2.2
  let f : schemeFibredCategory B S hS hP.choose ⟶ 𝒳.val :=
    Bicategory.InducedBicategory.mkHom hP.choose_spec.choose
  have hf : IsRepresentableByAlgebraicSpaces B S hS f.hom := hP.choose_spec.choose_spec.1
  have hR := SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
    (schemeFibredCategory B S hS hP.choose) 𝒳.val f.hom 𝒳.property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS hP.choose)
  have hdef : flatGroupoidPresentation 𝒳 = FlatGroupoidPresentation.ofScheme f hf
      (fun V y hy G hG he => (hP.choose_spec.choose_spec.2 V y hy G hG he).2)
      (fun V y hy G hG he => (hP.choose_spec.choose_spec.2 V y hy G hG he).1)
      (R := ⟨hR.choose, hR.choose_spec.1⟩) hR.choose_spec.2.some := rfl
  rw [hdef]
  exact FlatGroupoidPresentation.isParasitic_iff_forall_subsingleton_chart f hf _ _ _ ℱ hℱ

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U : AlgebraicSpaces B S hS}
  {𝒰 : Type*} [Category* 𝒰] {𝒳 : Type*} [Category* 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)

/-- **`ℱ|_{U_étale}` vanishes exactly when the sections of `ℱ` vanish on the charts.** The
restriction `f^*ℱ|_{U_étale}` of
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` is zero if and only if the sections of
`ℱ` vanish at the object `f(u_U W)` named by every étale chart `W` of `U`: those are its sections
over `W`. -/
theorem isZero_etaleRestrictedModuleInverseImage_iff (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    (ℱ : SheafOfModules.{v} (FibredSite.ringStructureSheafCore B S hS r hr .etale)) :
    IsZero (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ) ↔
      ∀ W : SmallEtale B S hS U.1,
        Subsingleton (ℱ.val.obj (op (f.obj ((restrictionFunctor B S hS U.1 p eU).obj W)))) := by
  constructor
  · intro hz W
    exact Stack.subsingleton_obj_of_isZero hz (op W)
  · intro hW
    exact Stack.isZero_of_forall_subsingleton_obj fun W => hW W.unop

end AlgebraicGeometry.Space

end
