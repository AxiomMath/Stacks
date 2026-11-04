module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeSupport

/-!
# Naturality in the test object of the base-change map on finite-support sections

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, and let `F` be an abelian
sheaf on the small étale site of `X`. For every étale test object `V` of `Y` the base-change
map `f_{p!}F(V) ⟶ f'_{p!}(p⁻¹F)(V')` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeSupport` is available; this file shows
that those maps commute with the restriction maps of the two finite-support direct image
presheaves. Together with the functoriality in `F` already proved, this is what makes them a map
of abelian presheaves on the small étale site of `Y`, which is the map `c` of the proof of
Stacks 0F5J.

The two composites `X'_{V'₁} ⟶ X_V` through the comparisons of the étale base changes agree, by
the universal property of `X_V`; this is the geometric input, and everything else follows from
it. In particular the two base changes of a support finite over `V` to `X'_{V'₁}` — base change
along the square then restriction, or the other way round — are the same subset, and the two
pullbacks of a section supported on it agree after restriction to the inverse image of the
canonical open of the support.

## Main results

* `AlgebraicGeometry.SmallEtale.fiberBaseChangeMap_naturality` and
  `AlgebraicGeometry.SmallEtale.fiberBaseChangeScheme_naturality` — the comparison of the two
  étale base changes is natural in the test object, as a morphism of the site and of schemes.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangeSupport_restriction` — base changing a support
  along the square and restricting it to a smaller test object is restricting it first.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangeColimitMap_restriction` — the base-change map on
  finite-support sections commutes with the restriction maps, which is the naturality in `V` of
  the map `c` of Stacks 0F5J.

## Implementation notes

The two base-changed supports are equal as subsets but not definitionally, so the comparison of
the two maps on supported sections is stated after transporting along the inclusion of one into
the other, which is the identity in disguise; the colimit generators at the two supports then
agree by the transition map of the colimit, and no transport along the equality of supports is
needed anywhere.

The auxiliary comparison of the two opens carrying the base-changed sections is built with
`AlgebraicGeometry.SmallEtale.openObjectMap`, because the open of `X'_{V'₁}` is the inverse
image of the open of `X'_{V'}` only up to the containment proved here, not on the nose.

## References

* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Square

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The projection of the étale base change to the test object is natural in the test
object. -/
public theorem fiberProjection_naturality {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V) :
    ((smallEtaleBaseChange B f).map i).hom.left ≫ fiberProjection B f V =
      fiberProjection B f V₁ ≫ i.hom.left :=
  pullback.lift_fst _ _ _

/-- The comparison `X'_{V'} ⟶ X_V` of the two étale base changes is natural in the test
object: composing it with the base change of a morphism `V₁ ⟶ V` of test objects, on either
side, gives the same morphism `X'_{V'₁} ⟶ X_V`. -/
public theorem fiberBaseChangeMap_naturality (sq : IsPullback p f' f g)
    {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V) :
    fiberBaseChangeMap B p f' f g sq V₁ ≫ ((smallEtaleBaseChange B f).map i).hom.left =
      ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i)).hom.left ≫
        fiberBaseChangeMap B p f' f g sq V := by
  refine (isPullback_fiberProjection B f V).hom_ext ?_ ?_
  · have hL : (fiberBaseChangeMap B p f' f g sq V₁ ≫
          ((smallEtaleBaseChange B f).map i).hom.left) ≫ fiberProjection B f V =
        (fiberProjection B f' (baseChange B g V₁) ≫ fiberProjection B g V₁) ≫ i.hom.left := by
      rw [Category.assoc, fiberProjection_naturality, ← Category.assoc,
        fiberBaseChangeMap_fst, Category.assoc]
    have hR : (((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i)).hom.left ≫
          fiberBaseChangeMap B p f' f g sq V) ≫ fiberProjection B f V =
        (fiberProjection B f' (baseChange B g V₁) ≫ fiberProjection B g V₁) ≫ i.hom.left := by
      rw [Category.assoc, fiberBaseChangeMap_fst, ← Category.assoc,
        fiberProjection_naturality, Category.assoc, fiberProjection_naturality,
        ← Category.assoc]
    rw [hL, hR]
  · have hL : (fiberBaseChangeMap B p f' f g sq V₁ ≫
          ((smallEtaleBaseChange B f).map i).hom.left) ≫ (baseChange B f V).obj.hom =
        (baseChange B f' (baseChange B g V₁)).obj.hom ≫ p := by
      rw [Category.assoc, Over.w ((smallEtaleBaseChange B f).map i).hom,
        fiberBaseChangeMap_snd]
    have hR : (((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i)).hom.left ≫
          fiberBaseChangeMap B p f' f g sq V) ≫ (baseChange B f V).obj.hom =
        (baseChange B f' (baseChange B g V₁)).obj.hom ≫ p := by
      rw [Category.assoc, fiberBaseChangeMap_snd, ← Category.assoc,
        Over.w ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i)).hom]
    rw [hL, hR]

/-- The comparison of the two étale base changes, as a morphism of schemes, is natural in the
test object. -/
public theorem fiberBaseChangeScheme_naturality (sq : IsPullback p f' f g)
    {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V) :
    fiberBaseChangeScheme B p f' f g sq V₁ ≫
        (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map i) =
      (SmallEtale.toScheme B X'.obj X'.property).map
          ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i)) ≫
        fiberBaseChangeScheme B p f' f g sq V := by
  have h := congrArg B.inclusion.map (fiberBaseChangeMap_naturality B p f' f g sq i)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- Base changing a support along the square and then restricting it to a smaller test object
gives the same subset as restricting it first: both are the inverse image of the support under
the two equal composites `X'_{V'₁} ⟶ X_V`. -/
public theorem fiberBaseChangeSupport_restriction (sq : IsPullback p f' f g)
    {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (E : FiniteSupport B f V) :
    (fiberBaseChangeSupport B p f' f g sq V₁
        (finiteSupportBaseChange B f F i E).support).1 =
      (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
        ((smallEtaleBaseChange B g).map i)
        (fiberBaseChangeSupport B p f' f g sq V E)).support.1 := by
  rw [fiberBaseChangeSupport_coe, (finiteSupportBaseChange B f F i E).support_eq,
    (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
      ((smallEtaleBaseChange B g).map i)
      (fiberBaseChangeSupport B p f' f g sq V E)).support_eq,
    fiberBaseChangeSupport_coe, ← Set.preimage_comp, ← Set.preimage_comp]
  exact congrArg (fun k : (SmallEtale.toScheme B X'.obj X'.property).obj
      (baseChange B f' (baseChange B g V₁)) ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) => k.base ⁻¹' E.1)
    (fiberBaseChangeScheme_naturality B p f' f g sq i)

variable (sq : IsPullback p f' f g) {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (E : FiniteSupport B f V)

/-- The open of `X'_{V'₁}` on which the base change of a section supported on the restriction of
`E` lives sits inside the inverse image of the corresponding open of `X'_{V'}`. -/
public theorem fiberBaseChangeSupportOpen_restriction_subset :
    (fiberBaseChangeSupportOpen B p f' f g sq V₁
          (finiteSupportBaseChange B f F i E).support :
        Set ((SmallEtale.toScheme B X'.obj X'.property).obj
          (baseChange B f' (baseChange B g V₁)))) ⊆
      ((SmallEtale.toScheme B X'.obj X'.property).map
          ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i))).base ⁻¹'
        (fiberBaseChangeSupportOpen B p f' f g sq V E :
          Set ((SmallEtale.toScheme B X'.obj X'.property).obj
            (baseChange B f' (baseChange B g V)))) := by
  intro x hx
  have hsub := supportOpen_preimage_subset B f i E (finiteSupportBaseChange B f F i E).support
    (finiteSupportBaseChange B f F i E).support_eq hx
  have hcomp := congrArg (fun k : (SmallEtale.toScheme B X'.obj X'.property).obj
      (baseChange B f' (baseChange B g V₁)) ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V) => k.base x)
    (fiberBaseChangeScheme_naturality B p f' f g sq i)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hcomp
  simp only [Set.mem_preimage, Scheme.Hom.coe_preimage] at hsub ⊢
  rwa [← hcomp]

/-- The comparison of the open of `X'_{V'₁}` carrying the base change of a section supported on
the restriction of `E` with the corresponding open of `X'_{V'}`. -/
public def fiberBaseChangeOpenRestrictionMap :
    openObject B X'.obj X'.property (baseChange B f' (baseChange B g V₁))
        (fiberBaseChangeSupportOpen B p f' f g sq V₁
          (finiteSupportBaseChange B f F i E).support) ⟶
      openObject B X'.obj X'.property (baseChange B f' (baseChange B g V))
        (fiberBaseChangeSupportOpen B p f' f g sq V E) :=
  openObjectMap B X'.obj X'.property
    ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i))
    (fiberBaseChangeSupportOpen B p f' f g sq V E)
    (fiberBaseChangeSupportOpen B p f' f g sq V₁ (finiteSupportBaseChange B f F i E).support)
    (fiberBaseChangeSupportOpen_restriction_subset.{u, v} B p f' f g sq i F E)

/-- The comparison of the two opens lies over the base change of the morphism of test
objects. -/
public theorem fiberBaseChangeOpenRestrictionMap_map :
    (SmallEtale.toScheme B X'.obj X'.property).map
          (fiberBaseChangeOpenRestrictionMap.{u, v} B p f' f g sq i F E) ≫
        (fiberBaseChangeSupportOpen B p f' f g sq V E).ι =
      (fiberBaseChangeSupportOpen B p f' f g sq V₁
          (finiteSupportBaseChange B f F i E).support).ι ≫
        (SmallEtale.toScheme B X'.obj X'.property).map
          ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map i)) :=
  openObjectMap_map B X'.obj X'.property _ _ _ _

/-- The canonical open of a locally closed subset depends only on the subset. -/
private theorem supportOpen_congr (S : Scheme.{u}) (hS : B.Contains S) (W : SmallEtale B S hS)
    {Z Z' : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    (hZ' : IsLocallyClosed Z') (h : Z = Z') :
    supportOpen B S hS W Z hZ = supportOpen B S hS W Z' hZ' := by
  subst h
  rfl

/-- The open carrying the base change of a section supported on the restriction of `E` is an
admissible open for the restriction of the base change of `E`. -/
private theorem fiberBaseChangeSupportOpen_restriction_le :
    fiberBaseChangeSupportOpen B p f' f g sq V₁ (finiteSupportBaseChange B f F i E).support ≤
      supportOpen B X'.obj X'.property (baseChange B f' (baseChange B g V₁))
        (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
          ((smallEtaleBaseChange B g).map i)
          (fiberBaseChangeSupport B p f' f g sq V E)).support.1
        (finiteSupport_isLocallyClosed B f' (baseChange B g V₁)
          (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
            ((smallEtaleBaseChange B g).map i)
            (fiberBaseChangeSupport B p f' f g sq V E)).support) := by
  rw [← supportOpen_congr B X'.obj X'.property (baseChange B f' (baseChange B g V₁))
    (finiteSupport_isLocallyClosed B f' (baseChange B g V₁)
      (fiberBaseChangeSupport B p f' f g sq V₁ (finiteSupportBaseChange B f F i E).support))
    (finiteSupport_isLocallyClosed B f' (baseChange B g V₁)
      (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
        ((smallEtaleBaseChange B g).map i)
        (fiberBaseChangeSupport B p f' f g sq V E)).support)
    (fiberBaseChangeSupport_restriction.{u, v} B p f' f g sq i F E)]
  exact fiberBaseChangeSupportOpen_le B p f' f g sq V₁ (finiteSupportBaseChange B f F i E).support

/-- The comparison of the two opens is compatible with the inclusions into the canonical open
of the base-changed support over the larger test object. -/
private theorem fiberBaseChangeOpenRestrictionMap_comp :
    fiberBaseChangeOpenRestrictionMap.{u, v} B p f' f g sq i F E ≫
        openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V))
          (fiberBaseChangeSupportOpen_le B p f' f g sq V E) =
      openObjectHomOfLE B X'.obj X'.property (baseChange B f' (baseChange B g V₁))
          (fiberBaseChangeSupportOpen_restriction_le.{u, v} B p f' f g sq i F E) ≫
        (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
          ((smallEtaleBaseChange B g).map i)
          (fiberBaseChangeSupport B p f' f g sq V E)).openMap := by
  apply (SmallEtale.toScheme B X'.obj X'.property).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  apply (cancel_mono (supportOpen B X'.obj X'.property (baseChange B f' (baseChange B g V))
    (fiberBaseChangeSupport B p f' f g sq V E).1
    (finiteSupport_isLocallyClosed B f' (baseChange B g V)
      (fiberBaseChangeSupport B p f' f g sq V E))).ι).1
  rw [Category.assoc, Category.assoc, openObjectHomOfLE_map, Scheme.homOfLE_ι,
    (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
      ((smallEtaleBaseChange B g).map i)
      (fiberBaseChangeSupport B p f' f g sq V E)).openMap_commutes,
    fiberBaseChangeOpenRestrictionMap_map.{u, v}, ← Category.assoc, openObjectHomOfLE_map,
    Scheme.homOfLE_ι]

/-- The restrictions of the comparison of the two étale base changes to the canonical opens of
a support and of its restriction to a smaller test object are compatible with the comparison of
the two base-changed opens. -/
private theorem fiberBaseChangeOpenMap_restriction :
    fiberBaseChangeOpenMap B p f' f g sq V₁ (finiteSupportBaseChange B f F i E).support ≫
        (finiteSupportBaseChange B f F i E).openMap.hom.left =
      (fiberBaseChangeOpenRestrictionMap.{u, v} B p f' f g sq i F E).hom.left ≫
        fiberBaseChangeOpenMap B p f' f g sq V E := by
  apply B.inclusion.map_injective
  rw [Functor.map_comp, Functor.map_comp, fiberBaseChangeOpenMap_map,
    fiberBaseChangeOpenMap_map,
    show B.inclusion.map (finiteSupportBaseChange B f F i E).openMap.hom.left =
      (SmallEtale.toScheme B X.obj X.property).map
        (finiteSupportBaseChange B f F i E).openMap from rfl,
    show B.inclusion.map
        (fiberBaseChangeOpenRestrictionMap.{u, v} B p f' f g sq i F E).hom.left =
      (SmallEtale.toScheme B X'.obj X'.property).map
        (fiberBaseChangeOpenRestrictionMap.{u, v} B p f' f g sq i F E) from rfl,
    ← cancel_mono (supportOpen B X.obj X.property (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)).ι,
    Category.assoc, Category.assoc,
    (finiteSupportBaseChange B f F i E).openMap_commutes, morphismRestrict_ι,
    ← Category.assoc, morphismRestrict_ι, Category.assoc]
  conv_rhs => rw [← Category.assoc, fiberBaseChangeOpenRestrictionMap_map.{u, v},
    Category.assoc, ← fiberBaseChangeScheme_naturality B p f' f g sq i]

/-- The comparison arrows of a support and of its restriction to a smaller test object are
compatible with the comparison of the two base-changed opens and with the base change along `p`
of the comparison of the canonical opens. -/
private theorem fiberBaseChangeSupportArrow_restriction :
    fiberBaseChangeSupportArrow B p f' f g sq V₁ (finiteSupportBaseChange B f F i E).support ≫
        (smallEtaleBaseChange B p).map (finiteSupportBaseChange B f F i E).openMap =
      fiberBaseChangeOpenRestrictionMap.{u, v} B p f' f g sq i F E ≫
        fiberBaseChangeSupportArrow B p f' f g sq V E := by
  refine baseChangeObj_hom_ext B p ?_
  show ((fiberBaseChangeSupportArrow B p f' f g sq V₁
        (finiteSupportBaseChange B f F i E).support).hom.left ≫
      ((smallEtaleBaseChange B p).map
        (finiteSupportBaseChange B f F i E).openMap).hom.left) ≫ _ =
    ((fiberBaseChangeOpenRestrictionMap.{u, v} B p f' f g sq i F E).hom.left ≫
      (fiberBaseChangeSupportArrow B p f' f g sq V E).hom.left) ≫ _
  rw [Category.assoc, baseChangeObjProjection_naturality, ← Category.assoc,
    fiberBaseChangeSupportArrow_proj, Category.assoc, fiberBaseChangeSupportArrow_proj,
    fiberBaseChangeOpenMap_restriction.{u, v}]

/-- Base changing a supported section along the square and then restricting it to a smaller test
object is the same as restricting it first, read in the group of sections supported on the
restriction of the base-changed support. -/
private theorem fiberBaseChangeSectionsMap_restriction :
    (supportedSectionsMap B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
          (baseChange B f' (baseChange B g V₁))
          (fiberBaseChangeSupport B p f' f g sq V₁
            (finiteSupportBaseChange B f F i E).support).1
          (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
            ((smallEtaleBaseChange B g).map i)
            (fiberBaseChangeSupport B p f' f g sq V E)).support.1
          (finiteSupport_isLocallyClosed B f' (baseChange B g V₁)
            (fiberBaseChangeSupport B p f' f g sq V₁
              (finiteSupportBaseChange B f F i E).support))
          (finiteSupport_isLocallyClosed B f' (baseChange B g V₁)
            (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
              ((smallEtaleBaseChange B g).map i)
              (fiberBaseChangeSupport B p f' f g sq V E)).support)
          (fiberBaseChangeSupport_restriction.{u, v} B p f' f g sq i F E).subset
          (finiteSupport_closedWithin B f' (baseChange B g V₁) _ _
            (fiberBaseChangeSupport_restriction.{u, v} B p f' f g sq i F E).subset)).comp
        ((fiberBaseChangeSectionsMap B p f' f g sq V₁
            (finiteSupportBaseChange B f F i E).support F).comp
          (finiteSupportBaseChange B f F i E).sectionsMap) =
      (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
          ((smallEtaleBaseChange B g).map i)
          (fiberBaseChangeSupport B p f' f g sq V E)).sectionsMap.comp
        (fiberBaseChangeSectionsMap B p f' f g sq V E F) := by
  refine AddMonoidHom.ext fun s => ?_
  refine supportedSections_ext B X'.obj X'.property ((abPullback.{u, v} B p).obj F)
    (baseChange B f' (baseChange B g V₁))
    (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
      ((smallEtaleBaseChange B g).map i)
      (fiberBaseChangeSupport B p f' f g sq V E)).support.1
    (finiteSupport_isLocallyClosed B f' (baseChange B g V₁)
      (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
        ((smallEtaleBaseChange B g).map i)
        (fiberBaseChangeSupport B p f' f g sq V E)).support)
    (fiberBaseChangeSupportOpen B p f' f g sq V₁
      (finiteSupportBaseChange B f F i E).support)
    ((fiberBaseChangeSupport_restriction.{u, v} B p f' f g sq i F E).symm.subset.trans
      (fiberBaseChangeSupport_subset_open B p f' f g sq V₁
        (finiteSupportBaseChange B f F i E).support))
    (fiberBaseChangeSupport_restriction.{u, v} B p f' f g sq i F E ▸
      isClosed_fiberBaseChangeSupport_preimage B p f' f g sq V₁
        (finiteSupportBaseChange B f F i E).support)
    (fiberBaseChangeSupportOpen_restriction_le.{u, v} B p f' f g sq i F E) ?_
  rw [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_comp, Function.comp_apply, supportedSectionsMap_apply,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, openObjectHomOfLE_comp,
    fiberBaseChangeSectionsMap_restrict, (finiteSupportBaseChange B f F i E).sectionsMap_apply,
    pullbackSectionAlongHom_map]
  conv_rhs =>
    rw [(finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
        ((smallEtaleBaseChange B g).map i)
        (fiberBaseChangeSupport B p f' f g sq V E)).sectionsMap_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← fiberBaseChangeOpenRestrictionMap_comp.{u, v} B p f' f g sq i F E,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      fiberBaseChangeSectionsMap_restrict, pullbackSectionAlongHom_restrict,
      ← fiberBaseChangeSupportArrow_restriction.{u, v} B p f' f g sq i F E]

/-- **Stacks 0F5J.** The base-change map on finite-support sections is compatible with the
restriction maps of the finite-support direct image presheaves: restricting a section to a
smaller test object `V₁` of `Y` and then base changing it along the square is base changing it
and then restricting along `V'₁ ⟶ V'`. This is the naturality in `V` of the map `c` of the
source. -/
@[stacks 0F5J "naturality in the test object of the map c"]
public theorem fiberBaseChangeColimitMap_restriction :
    finiteSupportBaseChangeHom B f F i ≫ fiberBaseChangeColimitMap B p f' f g sq V₁ F =
      fiberBaseChangeColimitMap B p f' f g sq V F ≫
        finiteSupportBaseChangeHom B f' ((abPullback.{u, v} B p).obj F)
          ((smallEtaleBaseChange B g).map i) := by
  refine colimit.hom_ext fun E => ?_
  have hsub : fiberBaseChangeSupport B p f' f g sq V₁
        (finiteSupportBaseChange B f F i E).support ≤
      (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
        ((smallEtaleBaseChange B g).map i)
        (fiberBaseChangeSupport B p f' f g sq V E)).support :=
    (fiberBaseChangeSupport_restriction.{u, v} B p f' f g sq i F E).subset
  have hkey : (AddCommGrpCat.ofHom (finiteSupportBaseChange B f F i E).sectionsMap ≫
        fiberBaseChangeDiagramMap B p f' f g sq V₁ F
          (finiteSupportBaseChange B f F i E).support) ≫
      (finiteSupportDiagram B f' ((abPullback.{u, v} B p).obj F)
        (baseChange B g V₁)).map (homOfLE hsub) =
      fiberBaseChangeDiagramMap B p f' f g sq V F E ≫
        AddCommGrpCat.ofHom
          (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
            ((smallEtaleBaseChange B g).map i)
            (fiberBaseChangeSupport B p f' f g sq V E)).sectionsMap :=
    AddCommGrpCat.hom_ext (fiberBaseChangeSectionsMap_restriction.{u, v} B p f' f g sq i F E)
  have hL := (Category.assoc (colimit.ι (finiteSupportDiagram B f F V) E)
      (finiteSupportBaseChangeHom B f F i)
      (fiberBaseChangeColimitMap B p f' f g sq V₁ F)).symm.trans
    ((congrArg (fun k => k ≫ fiberBaseChangeColimitMap B p f' f g sq V₁ F)
        (finiteSupportBaseChangeHom_ι B f F i E)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => AddCommGrpCat.ofHom
              (finiteSupportBaseChange B f F i E).sectionsMap ≫ k)
            (fiberBaseChangeColimitMap_ι B p f' f g sq V₁ F
              (finiteSupportBaseChange B f F i E).support)).trans
          (Category.assoc _ _ _).symm)))
  have hR := (Category.assoc (colimit.ι (finiteSupportDiagram B f F V) E)
      (fiberBaseChangeColimitMap B p f' f g sq V F)
      (finiteSupportBaseChangeHom B f' ((abPullback.{u, v} B p).obj F)
        ((smallEtaleBaseChange B g).map i))).symm.trans
    ((congrArg (fun k => k ≫ finiteSupportBaseChangeHom B f'
          ((abPullback.{u, v} B p).obj F) ((smallEtaleBaseChange B g).map i))
        (fiberBaseChangeColimitMap_ι B p f' f g sq V F E)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => fiberBaseChangeDiagramMap B p f' f g sq V F E ≫ k)
            (finiteSupportBaseChangeHom_ι B f' ((abPullback.{u, v} B p).obj F)
              ((smallEtaleBaseChange B g).map i)
              (fiberBaseChangeSupport B p f' f g sq V E))).trans
          (Category.assoc _ _ _).symm)))
  have hmid := (congrArg (fun k => (AddCommGrpCat.ofHom
          (finiteSupportBaseChange B f F i E).sectionsMap ≫
        fiberBaseChangeDiagramMap B p f' f g sq V₁ F
          (finiteSupportBaseChange B f F i E).support) ≫ k)
      (colimit.w (finiteSupportDiagram B f' ((abPullback.{u, v} B p).obj F)
        (baseChange B g V₁)) (homOfLE hsub)).symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ colimit.ι (finiteSupportDiagram B f'
        ((abPullback.{u, v} B p).obj F) (baseChange B g V₁))
        (finiteSupportBaseChange B f' ((abPullback.{u, v} B p).obj F)
          ((smallEtaleBaseChange B g).map i)
          (fiberBaseChangeSupport B p f' f g sq V E)).support) hkey))
  exact hL.trans (hmid.trans hR.symm)

end Square

end AlgebraicGeometry.SmallEtale

end
