module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedNearSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeInclusionMonomorphism

/-!
# Two inputs of the Stacks 06N3 chart at a finite type point

Both results below feed the hypothesis `hchart` of
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart`, through
`AlgebraicGeometry.Stack`
`.exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear_mem_range`, and neither
touches the chart construction itself.

## The field-valued point in the spelling the fibre takes

Everything about the fibre `F = U ×_𝒳 Spec k` of **Stacks 06N2** is stated at the site object
`AlgebraicGeometry.Stack.fieldPointObject` of **Stacks 06PU**, built from a field `k` of the
working universe, a proof that `Spec k` lies in the site, and a morphism `Spec k ⟶ S`. The
unramified field-valued point at a finite type point of a DM stack,
`AlgebraicGeometry.Stack.exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint`,
is delivered at an `AlgebraicGeometry.Stack.FieldSpectrum` instead: an object of the site
together with an *isomorphism* of its underlying scheme with a field spectrum. The two are not
the same object of the site, so a 1-morphism out of the one is not a 1-morphism out of the other,
and the first result below crosses between them.

The crossing costs nothing beyond bookkeeping, and in particular no comparison of sites: the
underlying scheme of `fieldPointObject B S hS k hk toBase` is `Spec k` on the nose, so the
isomorphism carried by a field spectrum is already an isomorphism of the two site objects over
`S` once its target is given the structure morphism obtained by transport. The image on points is
unchanged because the 1-morphism induced by an isomorphism of the site is invertible on points,
by functoriality of `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap`.

## The étale chart of the fibre, transported along a representing isomorphism

The unramifiedness clause of **Stacks 06N2**,
`AlgebraicGeometry.Stack.FibreIsUnramifiedNear`, is produced by
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt` out of an étale chart `N` of the
*chosen* representing algebraic space `Fsp` of the fibre whose structure morphism over `Spec k`
factors that of `Fsp`. What the chart construction of **Stacks 06N3** has in hand instead is an
étale chart of a presheaf `G` only *isomorphic* to `Fsp` — the identification of the fibre of the
Stacks 06MD slice,
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_fibreOverFieldPoint_zeroLocusOnOpen`,
presents that fibre as a vanishing subfunctor inside a representing space of another fibre, and
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal`
produces the chart there — together with the factorisation of the morphism to `Spec k` through
the isomorphism. The second result below absorbs the isomorphism into the chart: a chart of `G`
composed with the inverse isomorphism is a chart of `Fsp`, the étale-chart condition respecting
isomorphisms, and the factorisation becomes exactly the square
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt` asks for.

The point of `|Fsp|` is returned existentially, which is the shape the consumers take it in:
`AlgebraicGeometry.Stack`
`.exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear_mem_range` quantifies over
the point of `|Fsp|` and reads the prescribed point of `|𝒳|` off the singleton range of the
field-valued point instead, so nothing downstream names it.

## Main results

* `AlgebraicGeometry.Stack.exists_fieldPointObject_schemeStack_range_eq_singleton`: the
  unramified field-valued point of **Stacks 06N3** at a finite type point of a DM algebraic
  stack, in the `(k, hk, toBase)` spelling, with its image on points still the prescribed point.
* `AlgebraicGeometry.Stack.exists_fibreIsUnramifiedNear_of_iso_etaleChart_unramifiedAt`: the
  unramifiedness clause of **Stacks 06N2** from an étale chart of a presheaf isomorphic to the
  representing algebraic space of the fibre.

## What is not settled

Neither result produces the Stacks 06MD slice, its flatness, or the identification of the fibre
of the slice; the second takes the isomorphism and the chart as hypotheses precisely so that it
is independent of which route produces them. No `@[stacks]` attribute is registered: the chart
construction of **Stacks 06N3** is no tag of its own, its registration sitting on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack`, which still carries the
hypothesis `hForward`; **Stacks 06PU** is the definition of the site object and is not proved
here.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The field-valued point in the spelling of Stacks 06PU -/

/-- **The 1-morphism induced by the identity of the site is the identity 1-morphism.** The
companion of `AlgebraicGeometry.Stack.schemeStackMap_comp`, proved the same way: both sides are
`CategoryTheory.Over.map` of the identity read in the 2-category of algebraic stacks, so the
claim is `CategoryTheory.Over.mapId_eq` together with the fact that a based functor is determined
by its underlying functor. -/
theorem schemeStackMap_id (V : BigFppfOver B S hS) :
    schemeStackMap.{u, w} B S hS (𝟙 V) = 𝟙 (schemeStack.{u, w} B S hS V) :=
  Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext' (Over.mapId_eq V)))

/-- **An isomorphism of the site induces a bijection on the points of the represented algebraic
stacks.** Functoriality of `AlgebraicGeometry.Stack.schemeStackMap` and of
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap` turn the two halves of the isomorphism into
mutually inverse maps. -/
theorem bijective_pointsMap_schemeStackMap_of_isIso {V W : BigFppfOver B S hS} (m : V ⟶ W)
    [IsIso m] :
    Function.Bijective
      (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS m)) := by
  have key : ∀ {V W : BigFppfOver B S hS} (n : V ⟶ W) [IsIso n],
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS (inv n)) ∘
        AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS n) = id := fun n _ => by
    rw [← AlgebraicStacks.pointsMap_comp, schemeStackMap_comp, IsIso.hom_inv_id,
      schemeStackMap_id, AlgebraicStacks.pointsMap_id]
  exact Function.bijective_iff_has_inverse.2
    ⟨_, congrFun (key m), fun a => by simpa using congrFun (key (inv m)) a⟩

/-- **A field spectrum of the site is isomorphic over `S` to the site object of Stacks 06PU.**
Let `V` be an object of the big fppf site of `S` and let `ι : V ≅ Spec k` identify its underlying
scheme with the spectrum of a field. Then `Spec k` lies in the site, carries the structure
morphism obtained by transporting that of `V`, and the resulting site object
`AlgebraicGeometry.Stack.fieldPointObject` is isomorphic to `V` over `S` through `ι`.

The underlying scheme of `fieldPointObject B S hS k hk toBase` is `Spec k` on the nose, so the
isomorphism of objects of the site is `ι` itself: the functor to schemes is fully faithful, and
the triangle over `S` commutes by the definition of the transported structure morphism. -/
theorem exists_contains_hom_iso_fieldPointObject (V : BigFppfOver B S hS) (k : Type u) [Field k]
    (ι : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) :
    ∃ (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
      (e : V ≅ fieldPointObject B S hS k hk toBase),
      (BigFppfOver.toScheme B S hS).map e.hom = ι.hom := by
  have hk : B.Contains (Spec (.of k)) := by
    show (Spec (.of k)).size < B.cutoff
    rw [← Scheme.size_congr ι]
    exact V.left.property
  refine ⟨hk, ι.inv ≫ (BigFppfSite.inclusion B).map V.hom, Over.isoMk
    (ObjectProperty.isoMk (schemeSizeBelow B.cutoff) ι) ?_, rfl⟩
  show (ObjectProperty.homMk ι.hom : V.left ⟶ B.obj hk) ≫
      (ObjectProperty.homMk (ι.inv ≫ (BigFppfSite.inclusion B).map V.hom) :
        B.obj hk ⟶ B.obj hS) = V.hom
  apply (ObjectProperty.faithful_ι (schemeSizeBelow B.cutoff)).map_injective
  show ι.hom ≫ ι.inv ≫ (BigFppfSite.inclusion B).map V.hom =
    (BigFppfSite.inclusion B).map V.hom
  rw [Iso.hom_inv_id_assoc]

variable (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The unramified field-valued point of Stacks 06N3 in the spelling of Stacks 06PU.** At a
finite type point `x` of a DM algebraic stack there are a field `k` of the working universe with
`Spec k` in the site, a morphism `Spec k ⟶ S`, and a 1-morphism
`g : Spec k ⟶ 𝒳` out of the site object `AlgebraicGeometry.Stack.fieldPointObject` whose image on
points is exactly `{x}`.

This is
`AlgebraicGeometry.Stack.exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint`
read through
`AlgebraicGeometry.Stack.exists_contains_hom_iso_fieldPointObject`: that lemma's field spectrum
is isomorphic over `S` to the site object of **Stacks 06PU**, and precomposing with the
1-morphism of the isomorphism leaves the image on points unchanged, because that 1-morphism is
bijective on points.

The relative unramifiedness is carried across as well, and it has to be: it is what
`AlgebraicGeometry.Stack.isUnramified_fibreSpaceProjection_of_relativeProperty` consumes to make
the projection `F ⟶ U` unramified, which is in turn the hypothesis of the slicing sequence
`AlgebraicGeometry.Space.exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_isUnramified`
and of its affine-chart form
`AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`,
whose conclusion is the fibre hypothesis of **Stacks 06MD**. It is carried by composition
(**Stacks 045B**): the comparison 1-morphism is representable, both of its ends being represented
by objects of the site, and on representing presheaves it is the Yoneda image of an isomorphism
of the site by `AlgebraicGeometry.Stack.representingMap_schemeStackMap`, hence étale, hence
unramified. -/
theorem exists_fieldPointObject_schemeStack_range_eq_singleton
    (h𝒳 : AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (k : Type u) (_ : Field k) (hk : B.Contains (Spec (.of k)))
      (toBase : Spec (.of k) ⟶ S)
      (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳),
      RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) g.hom ∧
        Set.range (AlgebraicStacks.pointsMap B S hS g) = {x} := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  obtain ⟨F, u, hunr, hrange⟩ :=
    exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint.{u, w} B S hS hZ 𝒳 h𝒳
      x hx
  obtain ⟨hk, toBase, e, -⟩ :=
    exists_contains_hom_iso_fieldPointObject B S hS F.base F.carrier F.isSpec
  -- the comparison 1-morphism is representable, both sides being represented by the site
  have hrepe : IsRepresentableByAlgebraicSpaces B S hS
      (schemeStackMap.{u, w} B S hS e.inv).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (schemeStack.{u, w} B S hS F.base).property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS
        (fieldPointObject B S hS F.carrier hk toBase))
      (schemeStackMap.{u, w} B S hS e.inv).hom
  have hrepu : IsRepresentableByAlgebraicSpaces B S hS u.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base) u.hom
  -- the comparison is unramified: on representing presheaves it is the Yoneda image of an
  -- isomorphism of the site
  have hunre : RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS)
      (schemeStackMap.{u, w} B S hS e.inv).hom := by
    refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.unramifiedMorphismProperty B S hS)
      (schemeStackMap.{u, w} B S hS e.inv).hom hrepe
      (yoneda.obj (fieldPointObject B S hS F.carrier hk toBase)) (yoneda.obj F.base)
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)
      (PresheafOfCategories.sliceElementsEquivalenceOver _)).2 ?_
    rw [representingMap_schemeStackMap.{u, w} B S hS e.inv]
    exact Space.isUnramified_of_isEtale B S hS (Space.isEtale_of_isIso B S hS (yoneda.map e.inv))
  refine ⟨F.carrier, F.field, hk, toBase, schemeStackMap.{u, w} B S hS e.inv ≫ u,
    hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
      (Space.unramifiedMorphismProperty B S hS)
      (schemeStackMap.{u, w} B S hS e.inv).hom u.hom hrepe hrepu hunre hunr, ?_⟩
  rw [AlgebraicStacks.pointsMap_comp,
    (bijective_pointsMap_schemeStackMap_of_isIso.{u, w} B S hS e.inv).2.range_comp]
  exact hrange

/-! ### The étale chart of the fibre, transported along a representing isomorphism -/

variable (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

include hFsp in
/-- **The unramifiedness clause of the fibre hypothesis of Stacks 06N2, from an étale chart of a
presheaf isomorphic to the representing algebraic space of the fibre.** Let `Fsp` represent the
fibre `F = U ×_𝒳 Spec k` through `eF`, let `ε : Fsp ≅ G` be an isomorphism of presheaves and let
`ζ : G ⟶ Spec k` carry the structure morphism of `Fsp` across it, in the sense that
`ε.hom ≫ ζ` is `AlgebraicGeometry.Stack.fibreSpaceStructureMorphism`. Let `a : A ⟶ G` be an
étale chart of `G` by an object of the site, let `q : A ⟶ Spec k` realise `a ≫ ζ`, and let the
morphism of schemes underlying `q` be unramified at a point `v` of `A` in the sense of
**Stacks 02G4**. Then `AlgebraicGeometry.Stack.FibreIsUnramifiedNear` holds at the point of `|F|`
below some point of `|Fsp|`.

The chart of `Fsp` is `a ≫ ε.inv`: the étale-chart condition of **Stacks 03ED** is a
`CategoryTheory.MorphismProperty.presheaf`, hence respects isomorphisms, and the factorisation of
`a ≫ ε.inv` through `AlgebraicGeometry.Stack.fibreSpaceStructureMorphism` is `hq` with `hζ`
inserted. `AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt` then applies verbatim,
at the point `v` read on that chart.

The point of `|Fsp|` is existential because that is how the consumers take it: the chart assembly
`AlgebraicGeometry.Stack`
`.exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear_mem_range` quantifies over it
and reads the prescribed point of `|𝒳|` off the singleton range of the field-valued point, so no
clause downstream mentions it. -/
theorem exists_fibreIsUnramifiedNear_of_iso_etaleChart_unramifiedAt
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ε : Fsp ≅ G)
    (ζ : G ⟶ yoneda.obj (fieldPointObject B S hS k hk toBase))
    (hζ : ε.hom ≫ ζ =
      fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF)
    {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ G)
    (ha : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (q : A ⟶ fieldPointObject B S hS k hk toBase) (hq : a ≫ ζ = yoneda.map q)
    (v : (BigFppfOver.toScheme B S hS).obj A)
    (hv : _root_.AlgebraicGeometry.UnramifiedAt ((BigFppfOver.toScheme B S hS).map q) v) :
    ∃ xF : Space.points B S hS Fsp,
      FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
        (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
          (representingEquivalence B S hS Fsp
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor xF) := by
  let E0 : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : E0.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let : E0.presheaf.RespectsIso := MorphismProperty.relative_respectsIso E0
  have ha' : E0.presheaf (a ≫ ε.inv) :=
    MorphismProperty.RespectsIso.postcomp E0.presheaf ε.inv a ha
  refine ⟨Space.chartPointsMap
    (⟨CostructuredArrow.mk (a ≫ ε.inv), ha'⟩ : Space.SmallEtale B S hS Fsp) v, ?_⟩
  refine fibreIsUnramifiedNear_of_unramifiedAt.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF
    ⟨CostructuredArrow.mk (a ≫ ε.inv), ha'⟩ q ?_ v hv
  show (a ≫ ε.inv) ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF =
    yoneda.map q
  rw [← hζ, Category.assoc, Iso.inv_hom_id_assoc]
  exact hq

end AlgebraicGeometry.Stack

end
