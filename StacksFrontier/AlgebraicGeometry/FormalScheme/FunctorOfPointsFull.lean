module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumMappingLimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsAffine
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsSheaf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsZariskiSheaf

/-!
# Fullness of the functor of points of a formal scheme

Fix a cardinal `κ` cutting the schemes down to `Sch_κ`, as in Stacks 000J. Stacks 0AI1 identifies
the morphisms of formal schemes `𝔛 → 𝔜` with the transformations `h_𝔛 → h_𝔜` of their functors of
points on `Sch_κ`, provided the size of `𝔛` is not too large. The injectivity half is
`AlgebraicGeometry.injective_formalSchemeFunctorOfPoints_map`; this file proves the surjectivity
half — fullness — and assembles the two into the bijection of the source.

The argument is the source's, in two steps. *For a formal spectrum* `𝔛 = Spf A`: a
transformation `φ` sends the points `i_λ : Spec (A/I_λ) → Spf A` to morphisms
`Spec (A/I_λ) → 𝔜`, naturality at the transition maps of the system of quotients makes them a
compatible family, and the mapping-limit formula
`AlgebraicGeometry.existsUnique_hom_of_spfQuotientPointOn_comp_eq` assembles them into
`f : Spf A → 𝔜`. That `f` induces `φ`: over an *affine* scheme every point of `Spf A` factors
through one of the quotients (`AlgebraicGeometry.exists_factor_spfQuotientPointOn`), so the two
transformations agree there by naturality; a general object of `Sch_κ` is covered by affine
opens, which again lie in `Sch_κ`, and `h_𝔜` is a Zariski sheaf.

*For a general size-bounded formal scheme*: each affine formal chart `𝔛|_{𝔘_x} ≅ Spf A_x`
carries such a morphism, and the chart-wise morphisms agree on the overlaps `𝔘_x ⊓ 𝔘_y`, which
are *not* themselves affine formal. The separation statement that settles that is
`AlgebraicGeometry.restrict_hom_ext_of_chart`: morphisms out of `𝔛|_𝔙` with `𝔙 ≤ 𝔘_x` are
separated by the chart points of `𝔘_x` restricted to the preimage of `𝔙`. The chart-wise
morphisms then glue by
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover`, and the glued
morphism induces `φ` because a point of `𝔛` over an object of `Sch_κ` is covered by the
preimages of the `𝔘_x`, on each of which it factors through `𝔛|_{𝔘_x}`.

## Main definitions

* `AlgebraicGeometry.spfFormalSchemePoint`: the point `Spec (A/I) → Spf A` as a morphism of
  formal schemes.
* `AlgebraicGeometry.spfCutoffQuotient`: the quotient `Spec (A/I)` as an object of `Sch_κ`.
* `AlgebraicGeometry.spfTransValue`: the morphism `Spec (A/I) → 𝔜` that a transformation of
  functors of points attaches to the point `Spec (A/I) → Spf A`.
* `AlgebraicGeometry.ltrsIsoOfPresheafedSpaceIso` and `AlgebraicGeometry.liftToRestrict`: an
  isomorphism of the underlying presheafed spaces is an isomorphism of locally topologically
  ringed spaces, and a morphism whose image lies in an open subspace factors through it.
* `AlgebraicGeometry.chartPointPreimage`, `AlgebraicGeometry.chartPointOn` and
  `AlgebraicGeometry.chartPointRestrict`: the chart point restricted to the preimage of an open
  `𝔙 ≤ 𝔘`, as a morphism into `𝔛|_𝔙`.

## Main results

* `AlgebraicGeometry.app_comp_of_natTrans`: naturality of a transformation of functors of
  points, spelled out on points.
* `AlgebraicGeometry.isSizeBoundedFormalScheme_spfLTRS`: a formal spectrum satisfies the size
  condition of Stacks 0AI1 as soon as all its quotients `Spec (A/I_λ)` are objects of `Sch_κ`.
* `AlgebraicGeometry.exists_formalSchemeFunctorOfPoints_map_eq_spf`: **Stacks 0AI1**,
  surjectivity for a formal spectrum.
* `AlgebraicGeometry.formalChartPoint_hom_ext_of_le`, and
  `AlgebraicGeometry.exists_chartPointRestrict_base_eq`: the chart points separate the sections
  of `𝒪_𝔛` over an open contained in the chart, and the restricted chart points are jointly
  surjective onto `𝔙`.
* `AlgebraicGeometry.restrict_hom_ext_of_chart`: morphisms out of `𝔛|_𝔙`, for `𝔙` inside an
  affine formal chart, are separated by the restricted chart points.
* `AlgebraicGeometry.exists_hom_restrict_of_chart`: the morphism a transformation of functors of
  points induces on an affine formal chart.
* `AlgebraicGeometry.exists_formalSchemeFunctorOfPoints_map_eq` and
  `AlgebraicGeometry.bijective_formalSchemeFunctorOfPoints_map`: **Stacks 0AI1** in full —
  `Mor(𝔛, 𝔜) = Mor(h_𝔛, h_𝔜)` for a formal scheme `𝔛` whose size is bounded by the cutoff.

## Implementation notes

The size hypothesis enters only through `hsize`, which says that each `Spec (A/I_λ)` is an
object of `Sch_κ`. This is exactly the source's analysis of "the size of `𝔛` is not too large",
and `AlgebraicGeometry.isSizeBoundedFormalScheme_spfLTRS` records that it is
`AlgebraicGeometry.IsSizeBoundedFormalScheme` for `Spf A`.

Morphisms of the cutoff category `Sch_κ` are wrapped, `Sch_κ` being an
`CategoryTheory.ObjectProperty.FullSubcategory`; `AlgebraicGeometry.app_comp_of_natTrans` is
stated with the *unwrapped* morphism of schemes so that it can be rewritten with directly.

In `AlgebraicGeometry.restrict_hom_ext_of_chart` the index `W` that
`AlgebraicGeometry.presheafedSpace_hom_ext_of_cover` supplies — an open of `𝔙` — and the index
`(Opens.map (𝔛|_𝔙 → 𝔛).base).obj (image of W)` that the factorisation
`AlgebraicGeometry.chartPointRestrict_comp_ofRestrict` produces are equal only propositionally.
The transport between them is the naturality square of the comparison map of
`AlgebraicGeometry.chartPointRestrict` at the `eqToHom` of that equality; the three remaining
comparison maps — the two `ofRestrict`s over opens inside their subspaces, and the correction
term of `AlgebraicGeometry.PresheafedSpace.congr_app` — are isomorphisms and are cancelled.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

/-! ### The functor of points on the cutoff category -/

/-- A morphism of schemes of size below `κ` acts on points by precomposition. -/
theorem formalSchemeFunctorOfPoints_obj_map (κ : Cardinal.{u}) (X : FormalScheme.{u})
    {S T : (schemeCutoff κ).FullSubcategory} (t : S.obj ⟶ T.obj)
    (u : schemeToFormalScheme.obj T.obj ⟶ X) :
    ((formalSchemeFunctorOfPoints κ).obj X).map (ObjectProperty.homMk t : S ⟶ T).op u
      = schemeToFormalScheme.map t ≫ u := rfl

/-- Naturality of a transformation of functors of points, spelled out on points: the
transformation commutes with precomposition by a morphism of `Sch_κ`. -/
theorem app_comp_of_natTrans {κ : Cardinal.{u}} {X Y : FormalScheme.{u}}
    (φ : (formalSchemeFunctorOfPoints κ).obj X ⟶ (formalSchemeFunctorOfPoints κ).obj Y)
    {S T : (schemeCutoff κ).FullSubcategory} (t : S.obj ⟶ T.obj)
    (u : schemeToFormalScheme.obj T.obj ⟶ X) :
    φ.app (op S) (schemeToFormalScheme.map t ≫ u)
      = schemeToFormalScheme.map t ≫ φ.app (op T) u :=
  NatTrans.naturality_apply φ (ObjectProperty.homMk t : S ⟶ T).op u

/-- The inclusion of an open subspace of a locally topologically ringed space is an open
immersion of presheafed spaces. -/
instance isOpenImmersion_ofRestrict (X : LTRS.{u}) (V : Opens X) :
    PresheafedSpace.IsOpenImmersion (X.ofRestrict V).toHom :=
  PresheafedSpace.IsOpenImmersion.ofRestrict _ _

/-! ### Lifting a morphism into an open subspace -/

/-- An isomorphism of the underlying presheafed spaces of two locally topologically ringed
spaces is an isomorphism in `LTRS`: the locality of the stalk maps is automatic, the stalk maps
of an isomorphism being isomorphisms. -/
noncomputable def ltrsIsoOfPresheafedSpaceIso {X Y : LTRS.{u}}
    (ee : X.toPresheafedSpace ≅ Y.toPresheafedSpace) : X ≅ Y where
  hom :=
    { toHom := ee.hom
      isLocalHom x := @TopCommRingCat.isLocalHom_val_of_isIso _ _ _
        (PresheafedSpace.IsOpenImmersion.stalk_iso ee.hom x) }
  inv :=
    { toHom := ee.inv
      isLocalHom x := @TopCommRingCat.isLocalHom_val_of_isIso _ _ _
        (PresheafedSpace.IsOpenImmersion.stalk_iso ee.inv x) }
  hom_inv_id := LocallyTopologicallyRingedSpace.Hom.ext' ee.hom_inv_id
  inv_hom_id := LocallyTopologicallyRingedSpace.Hom.ext' ee.inv_hom_id

/-- A morphism of locally topologically ringed spaces whose image lies in an open subspace
factors through that open subspace. The factorisation is
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`; its stalk maps are local because the
stalk maps of the inclusion of the open subspace are isomorphisms. -/
noncomputable def liftToRestrict {Z X : LTRS.{u}} (V : Opens X) (g : Z ⟶ X)
    (hg : Set.range g.toHom.base ⊆ Set.range (X.ofRestrict V).toHom.base) : Z ⟶ X.restrict V :=
  { toHom := PresheafedSpace.IsOpenImmersion.lift (X.ofRestrict V).toHom g.toHom hg
    isLocalHom := by
      intro q
      set j := (X.ofRestrict V).toHom with hj
      set l := PresheafedSpace.IsOpenImmersion.lift j g.toHom hg with hl
      have hfac : l ≫ j = g.toHom := PresheafedSpace.IsOpenImmersion.lift_fac _ _ _
      have h1 : IsLocalHom ((l ≫ j).stalkMap q).1 := by
        rw [hfac]; exact g.isLocalHom q
      rw [PresheafedSpace.stalkMap.comp] at h1
      have : IsIso (j.stalkMap (l.base q)) := PresheafedSpace.IsOpenImmersion.stalk_iso j _
      have h2 : IsLocalHom (inv (j.stalkMap (l.base q))).1 :=
        TopCommRingCat.isLocalHom_val_of_isIso _
      have h3 : l.stalkMap q
          = inv (j.stalkMap (l.base q)) ≫ (j.stalkMap (l.base q) ≫ l.stalkMap q) := by
        rw [IsIso.inv_hom_id_assoc]
      rw [h3]
      exact @TopCommRingCat.isLocalHom_comp _ _ _ _ _ h2 h1 }

/-- The factorisation of `AlgebraicGeometry.liftToRestrict` through the open subspace. -/
theorem liftToRestrict_comp_ofRestrict {Z X : LTRS.{u}} (V : Opens X) (g : Z ⟶ X)
    (hg : Set.range g.toHom.base ⊆ Set.range (X.ofRestrict V).toHom.base) :
    liftToRestrict V g hg ≫ X.ofRestrict V = g :=
  LocallyTopologicallyRingedSpace.Hom.ext'
    (PresheafedSpace.IsOpenImmersion.lift_fac (X.ofRestrict V).toHom g.toHom hg)

/-! ### Separation along the chart points over an open inside a chart -/

/-- The image under a presheaf of a morphism between two opens that happen to be equal is an
isomorphism: there is only one morphism between two given opens. -/
theorem isIso_presheaf_map_of_opens_eq {Z : TopCat.{u}} (F : Z.Presheaf TopCommRingCat.{u})
    {U W : Opens Z} (h : U = W) (i : op U ⟶ op W) : IsIso (F.map i) := by
  subst h
  rw [show i = 𝟙 (op U) from Quiver.Hom.unop_inj (Subsingleton.elim _ _), F.map_id]
  infer_instance

/-- **The chart points separate the sections over an open contained in the chart.** Two maps
into the sections of `𝒪_𝔛` over an open `W` contained in an affine formal chart `𝔛|_𝔘 ≅ Spf A`
agree as soon as they agree after the comparison maps of all the morphisms
`Spec (A/I) → 𝔛` attached to the chart.

This is the separation step of the injectivity half of Stacks 0AI1, isolated for a single chart:
the comparison map of the chart isomorphism is a monomorphism, and the sections of
`𝒪_{Spf A} = lim 𝒪_λ` are separated by the projections. -/
theorem formalChartPoint_c_app_hom_ext {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
    (W : Opens X) {R : TopCommRingCat.{u}} {a b : R ⟶ X.presheaf.obj (op W)}
    (h : ∀ I : IdealsOfDefinition A,
      a ≫ (formalChartPointOn U A e I).toHom.c.app (op W)
        = b ≫ (formalChartPointOn U A e I).toHom.c.app (op W)) :
    a ≫ (X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding').c.app (op W)
      = b ≫ (X.toPresheafedSpace.ofRestrict
        (f := U.inclusion') U.isOpenEmbedding').c.app (op W) := by
  set WU : Opens (spfSpace A) :=
    (Opens.map e.inv.base).obj ((Opens.map U.inclusion').obj W) with hWU
  have hmono : Mono (e.inv.c.app (op ((Opens.map U.inclusion').obj W))) :=
    mono_c_app_of_iso e.symm (op ((Opens.map U.inclusion').obj W))
  refine (cancel_mono (e.inv.c.app (op ((Opens.map U.inclusion').obj W)))).1 ?_
  refine spfPointOn_hom_ext A fun I => ?_
  exact h I


/-- The comparison map of the inclusion of an open subspace is an isomorphism over an open
contained in that subspace: there the image of the preimage is the open itself. -/
theorem isIso_ofRestrict_c_app {X : LTRS.{u}} (U : Opens X) {W : Opens X} (hWU : W ≤ U) :
    IsIso ((X.toPresheafedSpace.ofRestrict
      (f := U.inclusion') U.isOpenEmbedding').c.app (op W)) := by
  have heq : W = U.isOpenEmbedding'.isOpenMap.functor.obj ((Opens.map U.inclusion').obj W) :=
    (Opens.ext (Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hWU hx⟩, rfl⟩)).symm
  exact isIso_presheaf_map_of_opens_eq X.presheaf heq _

/-- **Two maps into the sections of `𝒪_𝔛` over an open contained in an affine formal chart
agree as soon as they agree after the comparison maps of the chart points.** -/
theorem formalChartPoint_hom_ext_of_le {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
    {W : Opens X} (hWU : W ≤ U) {R : TopCommRingCat.{u}} {a b : R ⟶ X.presheaf.obj (op W)}
    (h : ∀ I : IdealsOfDefinition A,
      a ≫ (formalChartPointOn U A e I).toHom.c.app (op W)
        = b ≫ (formalChartPointOn U A e I).toHom.c.app (op W)) : a = b := by
  have := isIso_ofRestrict_c_app U hWU
  exact (cancel_mono ((X.toPresheafedSpace.ofRestrict
    (f := U.inclusion') U.isOpenEmbedding').c.app (op W))).1
    (formalChartPoint_c_app_hom_ext U A e W h)

/-! ### Chart points restricted to a smaller open -/

section ChartRestrict

variable {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]
  (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
  (V : Opens X)

/-- The preimage in `Spec (A/I)` of an open `𝔙` of `𝔛` under the chart point attached to an
affine formal chart `𝔛|_𝔘 ≅ Spf A`. -/
noncomputable def chartPointPreimage (I : IdealsOfDefinition A) :
    Opens ↥(schemeToLTRSObj (Spec (spfQuotient A I))) :=
  (Opens.map (formalChartPointOn U A e I).toHom.base).obj V

/-- The chart point restricted to the preimage of `𝔙`, read as a morphism into `𝔛`. -/
noncomputable def chartPointOn (I : IdealsOfDefinition A) :
    (schemeToLTRSObj (Spec (spfQuotient A I))).restrict (chartPointPreimage U A e V I) ⟶ X :=
  (schemeToLTRSObj (Spec (spfQuotientOn A I))).ofRestrict (chartPointPreimage U A e V I)
    ≫ formalChartPointOn U A e I

/-- The chart point restricted to the preimage of `𝔙` has image inside `𝔙`. -/
theorem range_chartPointOn (I : IdealsOfDefinition A) :
    Set.range (chartPointOn U A e V I).toHom.base
      ⊆ Set.range (X.ofRestrict V).toHom.base := by
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨_, q.2⟩, rfl⟩

/-- **The chart point of `𝔛` over the preimage of an open `𝔙`, as a morphism into `𝔛|_𝔙`.** -/
noncomputable def chartPointRestrict (I : IdealsOfDefinition A) :
    (schemeToLTRSObj (Spec (spfQuotient A I))).restrict (chartPointPreimage U A e V I)
      ⟶ X.restrict V :=
  { toHom := PresheafedSpace.IsOpenImmersion.lift (X.ofRestrict V).toHom
      (chartPointOn U A e V I).toHom (range_chartPointOn U A e V I)
    isLocalHom := by
      intro q
      set j := (X.ofRestrict V).toHom with hj
      set l := PresheafedSpace.IsOpenImmersion.lift j (chartPointOn U A e V I).toHom
        (range_chartPointOn U A e V I) with hl
      have hfac : l ≫ j = (chartPointOn U A e V I).toHom :=
        PresheafedSpace.IsOpenImmersion.lift_fac _ _ _
      have h1 : IsLocalHom ((l ≫ j).stalkMap q).1 := by
        rw [hfac]; exact (chartPointOn U A e V I).isLocalHom q
      rw [PresheafedSpace.stalkMap.comp] at h1
      have : IsIso (j.stalkMap (l.base q)) := PresheafedSpace.IsOpenImmersion.stalk_iso j _
      have h2 : IsLocalHom (inv (j.stalkMap (l.base q))).1 :=
        TopCommRingCat.isLocalHom_val_of_isIso _
      have h3 : l.stalkMap q
          = inv (j.stalkMap (l.base q)) ≫ (j.stalkMap (l.base q) ≫ l.stalkMap q) := by
        rw [IsIso.inv_hom_id_assoc]
      rw [h3]
      exact @TopCommRingCat.isLocalHom_comp _ _ _ _ _ h2 h1 }

/-- The restricted chart point, followed by the inclusion of `𝔙`, is the chart point. -/
theorem chartPointRestrict_comp_ofRestrict (I : IdealsOfDefinition A) :
    chartPointRestrict U A e V I ≫ X.ofRestrict V = chartPointOn U A e V I :=
  LocallyTopologicallyRingedSpace.Hom.ext'
    (PresheafedSpace.IsOpenImmersion.lift_fac (X.ofRestrict V).toHom
      (chartPointOn U A e V I).toHom (range_chartPointOn U A e V I))

/-- The comparison map of the inclusion of an open subspace of a locally topologically ringed
space is an isomorphism over an open contained in that subspace. -/
theorem isIso_ofRestrict_toHom_c_app {X : LTRS.{u}} (U : Opens X) {W : Opens X} (hWU : W ≤ U) :
    IsIso ((X.ofRestrict U).toHom.c.app (op W)) :=
  isIso_ofRestrict_c_app U hWU

/-- **The restricted chart points are jointly surjective onto `𝔙`.** For an open `𝔙` inside an
affine formal chart `𝔛|_𝔘 ≅ Spf A`, every point of `𝔙` is in the image of the chart point
`Spec (A/I) → 𝔛` restricted to the preimage of `𝔙`, for every ideal of definition `I`. -/
theorem exists_chartPointRestrict_base_eq (hVU : V ≤ U) (I : IdealsOfDefinition A)
    (x : ↥(X.restrict V)) :
    ∃ y, (chartPointRestrict U A e V I).toHom.base y = x := by
  obtain ⟨y, hy⟩ := exists_formalChartPointOn_base_eq U A e I (hVU x.2)
  have hyQ : y ∈ chartPointPreimage U A e V I := by
    change (formalChartPointOn U A e I).toHom.base y ∈ V
    rw [hy]; exact x.2
  refine ⟨⟨y, hyQ⟩, Subtype.ext ?_⟩
  have hbase := congrArg (fun m : (schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict
      (chartPointPreimage U A e V I) ⟶ X => m.toHom.base)
    (chartPointRestrict_comp_ofRestrict U A e V I)
  exact (congrFun (congrArg (fun k => (ConcreteCategory.hom k : _ → _)) hbase) ⟨y, hyQ⟩).trans hy

/-- **Morphisms out of `𝔛|_𝔙`, for `𝔙` contained in an affine formal chart `𝔛|_𝔘 ≅ Spf A`, are
separated by the restricted chart points.** They are jointly surjective by
`AlgebraicGeometry.exists_chartPointRestrict_base_eq`, and they separate the sections of
`𝒪_𝔛` over the opens contained in `𝔙` by
`AlgebraicGeometry.formalChartPoint_hom_ext_of_le`, the sections of `𝒪_{𝔛|_𝔙}` over an open `W`
being those of `𝒪_𝔛` over the image of `W` in `𝔛`. -/
theorem restrict_hom_ext_of_chart (hA : IsPreAdmissible A) (hVU : V ≤ U) {Y : LTRS.{u}}
    {u v : X.restrict V ⟶ Y}
    (h : ∀ I : IdealsOfDefinition A,
      chartPointRestrict U A e V I ≫ u = chartPointRestrict U A e V I ≫ v) : u = v := by
  obtain ⟨I₀, hI₀⟩ := hA
  refine LocallyTopologicallyRingedSpace.Hom.ext' (presheafedSpace_hom_ext_of_cover
    (fun I : IdealsOfDefinition A => (chartPointRestrict U A e V I).toHom)
    (fun x => ⟨⟨I₀, hI₀⟩, exists_chartPointRestrict_base_eq U A e V hVU ⟨I₀, hI₀⟩ x⟩) ?_ _ _
    (fun I => congrArg LocallyTopologicallyRingedSpace.Hom.toHom (h I)))
  intro W R a b hab
  set WX : Opens X := V.isOpenEmbedding.isOpenMap.functor.obj W with hWXdef
  have hWXV : WX ≤ V := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hW : (Opens.map (X.ofRestrict V).toHom.base).obj WX = W :=
    Opens.ext (Set.preimage_image_eq _ Subtype.val_injective)
  have hcV : IsIso ((X.ofRestrict V).toHom.c.app (op WX)) :=
    isIso_ofRestrict_toHom_c_app V hWXV
  set m1 := (X.restrict V).presheaf.map (eqToHom (congrArg op hW.symm)) with hm1
  have : IsIso m1 := by rw [hm1]; infer_instance
  refine (cancel_mono (m1 ≫ inv ((X.ofRestrict V).toHom.c.app (op WX)))).1 ?_
  refine formalChartPoint_hom_ext_of_le U A e (hWXV.trans hVU) fun I => ?_
  set m3 := ((schemeToLTRSObj (Spec (spfQuotientOn A I))).ofRestrict
      (chartPointPreimage U A e V I)).toHom.c.app
      (op ((Opens.map (formalChartPointOn U A e I).toHom.base).obj WX)) with hm3
  have : IsIso m3 := by
    rw [hm3]
    exact isIso_ofRestrict_toHom_c_app (chartPointPreimage U A e V I) fun z hz => hWXV hz
  have hop : (Opens.map (chartPointOn U A e V I).toHom.base).obj WX
      = (Opens.map (chartPointRestrict U A e V I ≫ X.ofRestrict V).toHom.base).obj WX :=
    congrArg (fun m : (schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict
        (chartPointPreimage U A e V I) ⟶ X => (Opens.map m.toHom.base).obj WX)
      (chartPointRestrict_comp_ofRestrict U A e V I).symm
  set mm := ((schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict
      (chartPointPreimage U A e V I)).presheaf.map (eqToHom (congrArg op hop)) with hmm
  have : IsIso mm := by rw [hmm]; infer_instance
  have keyc : (chartPointRestrict U A e V I ≫ X.ofRestrict V).toHom.c.app (op WX)
      = (chartPointOn U A e V I).toHom.c.app (op WX) ≫ mm :=
    PresheafedSpace.congr_app (congrArg LocallyTopologicallyRingedSpace.Hom.toHom
      (chartPointRestrict_comp_ofRestrict U A e V I)) (op WX)
  have hnat := (chartPointRestrict U A e V I).toHom.c.naturality
    (eqToHom (congrArg op hW.symm))
  have hptc : (formalChartPointOn U A e I).toHom.c.app (op WX) ≫ (m3 ≫ mm)
      = (X.ofRestrict V).toHom.c.app (op WX)
        ≫ (chartPointRestrict U A e V I).toHom.c.app
            (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX)) :=
    (Category.assoc _ _ _).symm.trans keyc.symm
  have hcollapse : ∀ z : R ⟶ (X.restrict V).presheaf.obj (op W),
      (((z ≫ (m1 ≫ inv ((X.ofRestrict V).toHom.c.app (op WX))))
            ≫ (formalChartPointOn U A e I).toHom.c.app (op WX)) ≫ m3) ≫ mm
        = z ≫ m1 ≫ (chartPointRestrict U A e V I).toHom.c.app
            (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX)) := by
    intro z
    rw [Category.assoc _ m3 mm,
      Category.assoc _ ((formalChartPointOn U A e I).toHom.c.app (op WX)) (m3 ≫ mm), hptc]
    change (z ≫ (m1 ≫ inv ((X.ofRestrict V).toHom.c.app (op WX))))
          ≫ ((X.ofRestrict V).toHom.c.app (op WX)
            ≫ (chartPointRestrict U A e V I).toHom.c.app
                (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX)))
        = z ≫ m1 ≫ (chartPointRestrict U A e V I).toHom.c.app
            (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX))
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  refine (cancel_mono m3).1 ((cancel_mono mm).1 ?_)
  refine (hcollapse a).trans (Eq.trans ?_ (hcollapse b).symm)
  rw [hnat, ← Category.assoc, ← Category.assoc, hab I]

end ChartRestrict

/-! ### The formal spectrum as a size-bounded formal scheme -/

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hA : IsAdmissible A)

/-- The point `Spec (A/I) → Spf A` of the formal spectrum, as a morphism of formal schemes. -/
noncomputable def spfFormalSchemePoint (I : IdealsOfDefinition A) :
    schemeToFormalScheme.obj (Spec (spfQuotient A I)) ⟶ spfFormalScheme A hA :=
  ObjectProperty.homMk (spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) I)

/-- The points of the formal spectrum are compatible with the transition maps of the system of
quotients. -/
theorem schemeToFormalScheme_map_comp_spfFormalSchemePoint {I J : IdealsOfDefinition A}
    (h : I.1 ≤ J.1) :
    schemeToFormalScheme.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
          ≫ spfFormalSchemePoint A hA I
      = spfFormalSchemePoint A hA J :=
  InducedCategory.hom_ext
    (spfQuotientTransitionOn_comp_spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) h)

/-- The formal spectrum of an admissible topological ring satisfies the size condition of
Stacks 0AI1 as soon as all the schemes `Spec (A/I_λ)` do: it is its own affine formal chart. -/
theorem isSizeBoundedFormalScheme_spfLTRS {κ : Cardinal.{u}}
    (hsize : ∀ I : IdealsOfDefinition A, (Spec (spfQuotient A I)).size < κ) :
    IsSizeBoundedFormalScheme κ (spfLTRS A hA.1) := fun _ =>
  ⟨⊤, trivial, TopCommRingCat.of A, inferInstance, hA, hsize,
    ⟨PresheafedSpace.restrictTopIso _⟩⟩

/-! ### Fullness for a formal spectrum -/

variable {κ : Cardinal.{u}} {Y : FormalScheme.{u}}

/-- The quotient `Spec (A/I)` as an object of the cutoff category `Sch_κ`. -/
noncomputable def spfCutoffQuotient
    (hsize : ∀ I : IdealsOfDefinition A, (Spec (spfQuotient A I)).size < κ)
    (I : IdealsOfDefinition A) : (schemeCutoff κ).FullSubcategory :=
  ⟨Spec (spfQuotientOn A I), hsize I⟩

/-- The morphism `Spec (A/I) → 𝔜` that a transformation of functors of points attaches to the
point `Spec (A/I) → Spf A`. -/
noncomputable def spfTransValue
    (hsize : ∀ I : IdealsOfDefinition A, (Spec (spfQuotient A I)).size < κ)
    (φ : (formalSchemeFunctorOfPoints κ).obj (spfFormalScheme A hA) ⟶
      (formalSchemeFunctorOfPoints κ).obj Y) (I : IdealsOfDefinition A) :
    schemeToFormalScheme.obj (Spec (spfQuotient A I)) ⟶ Y :=
  φ.app (op (spfCutoffQuotient A hsize I)) (spfFormalSchemePoint A hA I)

/-- The morphisms a transformation of functors of points attaches to the points
`Spec (A/I) → Spf A` form a family compatible with the transition maps of the system of
quotients: this is the naturality of the transformation at those transition maps. -/
theorem spfQuotientTransition_comp_spfTransValue
    (hsize : ∀ I : IdealsOfDefinition A, (Spec (spfQuotient A I)).size < κ)
    (φ : (formalSchemeFunctorOfPoints κ).obj (spfFormalScheme A hA) ⟶
      (formalSchemeFunctorOfPoints κ).obj Y)
    (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1) :
    spfQuotientTransition A h ≫ (spfTransValue A hA hsize φ I).hom
      = (spfTransValue A hA hsize φ J).hom := by
  have key : schemeToFormalScheme.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
        ≫ spfTransValue A hA hsize φ I = spfTransValue A hA hsize φ J := by
    change schemeToFormalScheme.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
        ≫ φ.app (op (spfCutoffQuotient A hsize I)) (spfFormalSchemePoint A hA I)
      = φ.app (op (spfCutoffQuotient A hsize J)) (spfFormalSchemePoint A hA J)
    rw [← schemeToFormalScheme_map_comp_spfFormalSchemePoint A hA h]
    exact (app_comp_of_natTrans φ (S := spfCutoffQuotient A hsize J)
      (T := spfCutoffQuotient A hsize I)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
      (spfFormalSchemePoint A hA I)).symm
  exact congrArg InducedCategory.Hom.hom key

/-- **Fullness for a formal spectrum.** Every transformation of functors of points on `Sch_κ` out
of the functor of points of `Spf A` is induced by a morphism of formal schemes `Spf A → 𝔜`,
provided all the schemes `Spec (A/I_λ)` are objects of `Sch_κ`. -/
theorem exists_formalSchemeFunctorOfPoints_map_eq_spf
    (hsize : ∀ I : IdealsOfDefinition A, (Spec (spfQuotient A I)).size < κ)
    (φ : (formalSchemeFunctorOfPoints κ).obj (spfFormalScheme A hA) ⟶
      (formalSchemeFunctorOfPoints κ).obj Y) :
    ∃ f : spfFormalScheme A hA ⟶ Y, (formalSchemeFunctorOfPoints κ).map f = φ := by
  obtain ⟨f₀, hf₀, -⟩ := existsUnique_hom_of_spfQuotientPointOn_comp_eq A
    (preAdmissibleSpfIndex A hA.1)
    (fun I => (spfTransValue A hA hsize φ I).hom)
    (spfQuotientTransition_comp_spfTransValue A hA hsize φ)
  set f : spfFormalScheme A hA ⟶ Y := ObjectProperty.homMk f₀
  have hpoint : ∀ I : IdealsOfDefinition A,
      spfFormalSchemePoint A hA I ≫ f = spfTransValue A hA hsize φ I := fun I =>
    InducedCategory.hom_ext (hf₀ I)
  refine ⟨f, ?_⟩
  ext S s
  obtain ⟨S⟩ := S
  change s ≫ f = φ.app (op S) s
  set V : S.obj.affineCover.I₀ → S.obj.Opens := fun i => (S.obj.affineCover.f i).opensRange
  have hV : iSup V = ⊤ := S.obj.affineCover.iSup_opensRange
  have hVaff : ∀ i, IsAffine (V i).toScheme := fun i =>
    isAffineOpen_opensRange (S.obj.affineCover.f i)
  have hVsize : ∀ i, schemeCutoff κ (V i).toScheme := fun i =>
    Scheme.size_lt_of_isOpenImmersion (V i).ι S.property
  refine (isSheafFor_opensCover_formalSchemePoints Y V hV).isSeparatedFor.ext ?_
  rintro Z t ⟨i⟩
  change schemeToFormalScheme.map (V i).ι ≫ (s ≫ f)
    = schemeToFormalScheme.map (V i).ι ≫ φ.app (op S) s
  have := hVaff i
  obtain ⟨I, a, ha⟩ := exists_factor_spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1)
    (isIso_spfGammaHom A hA) (V i).toScheme (schemeToFormalScheme.map (V i).ι ≫ s).hom
  have hfac : schemeToFormalScheme.map a ≫ spfFormalSchemePoint A hA I
      = schemeToFormalScheme.map (V i).ι ≫ s := InducedCategory.hom_ext ha
  have e1 : schemeToFormalScheme.map (V i).ι ≫ φ.app (op S) s
      = φ.app (op ⟨(V i).toScheme, hVsize i⟩) (schemeToFormalScheme.map (V i).ι ≫ s) :=
    (app_comp_of_natTrans φ (S := ⟨(V i).toScheme, hVsize i⟩) (T := S) (V i).ι s).symm
  have e2 : φ.app (op ⟨(V i).toScheme, hVsize i⟩) (schemeToFormalScheme.map (V i).ι ≫ s)
      = schemeToFormalScheme.map a ≫ spfTransValue A hA hsize φ I := by
    rw [← hfac]
    exact app_comp_of_natTrans φ (S := ⟨(V i).toScheme, hVsize i⟩)
      (T := spfCutoffQuotient A hsize I) a (spfFormalSchemePoint A hA I)
  calc schemeToFormalScheme.map (V i).ι ≫ (s ≫ f)
      = (schemeToFormalScheme.map a ≫ spfFormalSchemePoint A hA I) ≫ f := by
        rw [hfac]; exact (Category.assoc _ _ _).symm
    _ = schemeToFormalScheme.map a ≫ spfTransValue A hA hsize φ I := by
        rw [Category.assoc, hpoint I]
    _ = schemeToFormalScheme.map (V i).ι ≫ φ.app (op S) s := (e1.trans e2).symm

end Spf

/-! ### Fullness in general -/

/-- **The morphism a transformation of functors of points induces on an affine formal chart.** For
an open `𝔘` of `𝔛` with `𝔛|_𝔘 ≅ Spf A`, all the schemes `Spec (A/I_λ)` being objects of `Sch_κ`,
every transformation `h_𝔛 → h_𝔜` is realized by a morphism `𝔛|_𝔘 → 𝔜` on every point of `𝔘` defined
over an object of `Sch_κ`. -/
theorem exists_hom_restrict_of_chart {κ : Cardinal.{u}} {X Y : FormalScheme.{u}}
    (U : Opens X.obj) (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsAdmissible A)
    (hsize : ∀ I : IdealsOfDefinition A, (Spec (spfQuotient A I)).size < κ)
    (e : X.obj.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
    (φ : (formalSchemeFunctorOfPoints κ).obj X ⟶ (formalSchemeFunctorOfPoints κ).obj Y) :
    ∃ fU : X.obj.restrict U ⟶ Y.obj, ∀ (S : (schemeCutoff κ).FullSubcategory)
      (t : schemeToLTRSObj S.obj ⟶ X.obj.restrict U),
      t ≫ fU = (φ.app (op S) (ObjectProperty.homMk (t ≫ X.obj.ofRestrict U) :
        schemeToFormalScheme.obj S.obj ⟶ X)).hom := by
  set χ : X.obj.restrict U ≅ spfLTRS A hA.1 := ltrsIsoOfPresheafedSpaceIso e
  set ι : spfFormalScheme A hA ⟶ X := ObjectProperty.homMk (χ.inv ≫ X.obj.ofRestrict U)
  obtain ⟨f', hf'⟩ := exists_formalSchemeFunctorOfPoints_map_eq_spf A hA hsize
    ((formalSchemeFunctorOfPoints κ).map ι ≫ φ)
  refine ⟨χ.hom ≫ f'.hom, fun S t => ?_⟩
  set w : schemeToFormalScheme.obj S.obj ⟶ spfFormalScheme A hA :=
    ObjectProperty.homMk (t ≫ χ.hom)
  have hwι : w ≫ ι = (ObjectProperty.homMk (t ≫ X.obj.ofRestrict U) :
      schemeToFormalScheme.obj S.obj ⟶ X) := by
    refine InducedCategory.hom_ext ?_
    change (t ≫ χ.hom) ≫ (χ.inv ≫ X.obj.ofRestrict U) = t ≫ X.obj.ofRestrict U
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  have key := congrFun (congrArg (fun η => (ConcreteCategory.hom (η.app (op S)) : _ → _)) hf') w
  have h2 : (φ.app (op S) (w ≫ ι)).hom
      = (φ.app (op S) (ObjectProperty.homMk (t ≫ X.obj.ofRestrict U) :
          schemeToFormalScheme.obj S.obj ⟶ X)).hom := by rw [hwι]
  exact (Category.assoc t χ.hom f'.hom).symm.trans
    ((congrArg InducedCategory.Hom.hom key).trans h2)


/-- **Fullness of the functor of points.** Every transformation `h_𝔛 → h_𝔜` of functors of points
on `Sch_κ` out of a formal scheme `𝔛` satisfying `AlgebraicGeometry.IsSizeBoundedFormalScheme` is
induced by a morphism of formal schemes `𝔛 → 𝔜`. -/
theorem exists_formalSchemeFunctorOfPoints_map_eq {κ : Cardinal.{u}} {X Y : FormalScheme.{u}}
    (hX : IsSizeBoundedFormalScheme κ X.obj)
    (φ : (formalSchemeFunctorOfPoints κ).obj X ⟶ (formalSchemeFunctorOfPoints κ).obj Y) :
    ∃ f : X ⟶ Y, (formalSchemeFunctorOfPoints κ).map f = φ := by
  classical
  choose U hxU A hlin hdata using hX
  have hchart : ∀ x : X.obj, ∃ fU : X.obj.restrict (U x) ⟶ Y.obj,
      ∀ (S : (schemeCutoff κ).FullSubcategory)
        (t : schemeToLTRSObj S.obj ⟶ X.obj.restrict (U x)),
        t ≫ fU = (φ.app (op S) (ObjectProperty.homMk (t ≫ X.obj.ofRestrict (U x)) :
          schemeToFormalScheme.obj S.obj ⟶ X)).hom := by
    intro x
    have := hlin x
    exact exists_hom_restrict_of_chart (U x) (A x).α (hdata x).1 (hdata x).2.1
      (hdata x).2.2.some φ
  choose fU hfU using hchart
  have hfU' : ∀ (x : ↥X.obj) (S : (schemeCutoff κ).FullSubcategory)
      (t : schemeToLTRSObj S.obj ⟶ X.obj.restrict (U x)) (g : schemeToLTRSObj S.obj ⟶ X.obj),
      t ≫ X.obj.ofRestrict (U x) = g → t ≫ fU x
        = (φ.app (op S) (ObjectProperty.homMk g : schemeToFormalScheme.obj S.obj ⟶ X)).hom :=
    fun x S t g h => h ▸ hfU x S t
  have compat : ∀ x y : X.obj, X.obj.resLE (inf_le_left : U x ⊓ U y ≤ U x) ≫ fU x
      = X.obj.resLE (inf_le_right : U x ⊓ U y ≤ U y) ≫ fU y := by
    intro x y
    have := hlin x
    refine restrict_hom_ext_of_chart (U x) (A x).α (hdata x).2.2.some (U x ⊓ U y)
      (hdata x).1.1 inf_le_left fun I => ?_
    set O : (Spec (spfQuotientOn (A x).α I)).Opens :=
      chartPointPreimage (U x) (A x).α (hdata x).2.2.some (U x ⊓ U y) I with hO
    have hOsize : schemeCutoff κ O.toScheme :=
      Scheme.size_lt_of_isOpenImmersion O.ι ((hdata x).2.1 I)
    set iso := schemeToLTRSRestrictIso (Spec (spfQuotientOn (A x).α I)) O with hiso
    set cpr := chartPointRestrict (U x) (A x).α (hdata x).2.2.some (U x ⊓ U y) I with hcpr
    have side : ∀ (z : ↥X.obj) (h : U x ⊓ U y ≤ U z),
        (iso.hom ≫ cpr) ≫ X.obj.resLE h ≫ fU z = (φ.app (op ⟨O.toScheme, hOsize⟩)
          (ObjectProperty.homMk ((iso.hom ≫ cpr) ≫ X.obj.ofRestrict (U x ⊓ U y)) :
            schemeToFormalScheme.obj O.toScheme ⟶ X)).hom := fun z h => by
      rw [← Category.assoc]
      refine hfU' z ⟨O.toScheme, hOsize⟩ _ _ ?_
      exact (Category.assoc _ _ _).trans
        (congrArg _ (LocallyTopologicallyRingedSpace.resLE_comp_ofRestrict ..))
    have main := (side x inf_le_left).trans (side y inf_le_right).symm
    exact (Iso.cancel_iso_hom_left iso _ _).1
      ((Category.assoc _ _ _).symm.trans (main.trans (Category.assoc _ _ _)))
  have hcover : iSup U = ⊤ :=
    Opens.ext (Set.eq_univ_iff_forall.2 fun x => by
      rw [Opens.coe_iSup]; exact Set.mem_iUnion.2 ⟨x, hxU x⟩)
  obtain ⟨f₀, hf₀, -⟩ := LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover
    U hcover fU compat
  set fglue : X ⟶ Y := ObjectProperty.homMk f₀ with hfglue
  refine ⟨fglue, ?_⟩
  ext S s
  obtain ⟨S⟩ := S
  change s ≫ fglue = φ.app (op S) s
  set O : ↥X.obj → S.obj.Opens := fun x => (Opens.map s.hom.toHom.base).obj (U x) with hOdef
  have hOcover : iSup O = ⊤ :=
    Opens.ext (Set.eq_univ_iff_forall.2 fun z =>
      Opens.mem_iSup.2 ⟨s.hom.toHom.base z, hxU _⟩)
  have hOsize : ∀ x, schemeCutoff κ (O x).toScheme := fun x =>
    Scheme.size_lt_of_isOpenImmersion (O x).ι S.property
  refine (isSheafFor_opensCover_formalSchemePoints Y O hOcover).isSeparatedFor.ext ?_
  rintro Z τ ⟨x⟩
  change schemeToFormalScheme.map (O x).ι ≫ (s ≫ fglue)
    = schemeToFormalScheme.map (O x).ι ≫ φ.app (op S) s
  set g : schemeToLTRSObj (O x).toScheme ⟶ X.obj :=
    (schemeToFormalScheme.map (O x).ι ≫ s).hom with hg
  have hrange : Set.range g.toHom.base ⊆ Set.range (X.obj.ofRestrict (U x)).toHom.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, z.2⟩, rfl⟩
  have hchar := hfU' x ⟨(O x).toScheme, hOsize x⟩ _ g
    (liftToRestrict_comp_ofRestrict (U x) g hrange)
  have hgmk : (ObjectProperty.homMk g : schemeToFormalScheme.obj (O x).toScheme ⟶ X)
      = schemeToFormalScheme.map (O x).ι ≫ s := InducedCategory.hom_ext rfl
  have hchar3 := (hchar.trans (congrArg
    (fun w : schemeToFormalScheme.obj (O x).toScheme ⟶ X =>
      (φ.app (op ⟨(O x).toScheme, hOsize x⟩) w).hom) hgmk)).trans (congrArg InducedCategory.Hom.hom
    (app_comp_of_natTrans φ (S := ⟨(O x).toScheme, hOsize x⟩) (T := S) (O x).ι s))
  refine InducedCategory.hom_ext (Eq.trans ?_ hchar3)
  change (schemeToFormalScheme.map (O x).ι).hom ≫ (s.hom ≫ f₀)
    = liftToRestrict (U x) g hrange ≫ fU x
  conv_rhs => rw [← hf₀ x]
  exact (Category.assoc _ _ _).symm.trans
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun m : schemeToLTRSObj (O x).toScheme ⟶ X.obj => m ≫ f₀)
        (liftToRestrict_comp_ofRestrict (U x) g hrange))).symm)

/-- **Morphisms of formal schemes are transformations of functors of points.** For a formal scheme
`𝔛` whose size is not too large — the schemes `Spec (A/I_λ)` cut out of its affine formal charts
being objects of `Sch_κ` — and any formal scheme `𝔜`,

`Mor_{Formal Schemes}(𝔛, 𝔜) = Mor_{PSh(Sch_κ)}(h_𝔛, h_𝔜)`. -/
@[stacks 0AI1 "the bijection Mor(𝔛, 𝔜) = Mor(h_𝔛, h_𝔜) for a formal scheme 𝔛 whose size is \
bounded by the cutoff"]
theorem bijective_formalSchemeFunctorOfPoints_map {κ : Cardinal.{u}} {X Y : FormalScheme.{u}}
    (hX : IsSizeBoundedFormalScheme κ X.obj) :
    Function.Bijective fun f : X ⟶ Y => (formalSchemeFunctorOfPoints κ).map f :=
  ⟨injective_formalSchemeFunctorOfPoints_map hX,
    fun φ => exists_formalSchemeFunctorOfPoints_map_eq hX φ⟩

end AlgebraicGeometry

end
