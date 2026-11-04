module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakFunctorOfPointsFpqcSheaf

/-!
# Fullness of the functor of points of a McQuillan formal scheme

Stacks 0AI3 records that the counterparts of Lemmas 87.2.1 and 87.2.2 hold for the larger
category of formal schemes built on weak admissibility, with the same proofs. This file completes
the counterpart of Lemma 87.2.1: for a McQuillan formal scheme `𝔛` satisfying the size condition
and any McQuillan formal scheme `𝔜`,

`Mor_{McQuillan Formal Schemes}(𝔛, 𝔜) = Mor_{PSh(Sch_κ)}(h_𝔛, h_𝔜)`.

The injectivity half was already available as
`AlgebraicGeometry.injective_mcQuillanFormalSchemeFunctorOfPoints_map`; what is added here is
fullness, and the bijection.

The argument is the source's, and the one already carried out for admissible rings in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull`. It splits along the two things
that file hard-codes.

*The chart machinery* — the chart points `Spec (A/I) → 𝔛` of a chart `𝔛|_𝔘 ≅ Spf A` restricted to
the preimage of a smaller open, and the separation statement they give for morphisms out of
`𝔛|_𝔙` — is stated there for the ideals of definition of a pre-admissible ring. It is in fact
asked of the family of ideals nothing beyond being a
`AlgebraicGeometry.IsWeakIdealSystem` with one member, so it is restated here for an arbitrary
such family, which is the form McQuillan's formal spectrum needs: the weak ideals of definition
of a weakly admissible ring are such a family. The underlying constructions
`AlgebraicGeometry.formalChartPointOn` and `AlgebraicGeometry.exists_formalChartPointOn_base_eq`,
and the mapping-limit formula `AlgebraicGeometry.existsUnique_hom_of_spfQuotientPointOn_comp_eq`
that the assembly rests on, are already stated at that generality.

*The ambient category* — `AlgebraicGeometry.FormalScheme` and its functor of points — is not
indexed by the family of ideals, and the McQuillan counterparts are built here on the McQuillan
category: chart by chart a transformation of functors of points induces a morphism
`𝔛|_𝔘_x → 𝔜`, the chart-wise morphisms agree on the overlaps by the separation statement, they
glue by `AlgebraicGeometry.LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover`, and
the glued morphism induces the transformation because the functor of points of `𝔜` is a Zariski
sheaf.

## Main definitions

* `AlgebraicGeometry.chartPointOnPreimage`, `AlgebraicGeometry.chartPointOnMap` and
  `AlgebraicGeometry.chartPointOnRestrict`: for a chart `𝔛|_𝔘 ≅ Spf_P A` taken along an arbitrary
  weak ideal system `P`, the chart point restricted to the preimage of an open `𝔙 ≤ 𝔘`, as a
  morphism into `𝔛|_𝔙`.
* `AlgebraicGeometry.spfwMcQuillanFormalSchemePoint`: the point `Spec (A/I) → Spfw A` as a
  morphism of McQuillan formal schemes.
* `AlgebraicGeometry.spfwCutoffQuotient` and `AlgebraicGeometry.spfwTransValue`: the quotient
  `Spec (A/I)` as an object of `Sch_κ`, and the morphism `Spec (A/I) → 𝔜` that a transformation
  of functors of points attaches to it.

## Main results

* `AlgebraicGeometry.formalChartPointOn_hom_ext_of_le` and
  `AlgebraicGeometry.restrict_hom_ext_of_chartOn`: the chart points of a chart taken along an
  arbitrary weak ideal system separate the sections of `𝒪_𝔛` over an open inside the chart, and
  the restricted chart points separate morphisms out of `𝔛|_𝔙`.
* `AlgebraicGeometry.exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq_spfw`: fullness for
  McQuillan's formal spectrum.
* `AlgebraicGeometry.exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq`: fullness for a
  size-bounded McQuillan formal scheme.
* `AlgebraicGeometry.bijective_mcQuillanFormalSchemeFunctorOfPoints_map`: **Stacks 0AI3**, the
  counterpart of Lemma 87.2.1 in full.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

/-! ### Chart points of a chart taken along an arbitrary weak ideal system -/

section ChartOn

variable {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] {P : Ideal A → Prop} [IsWeakIdealSystem A P]
  (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ SpfOn A P)

/-- **The chart points separate the sections over an open contained in the chart**, for a chart
`𝔛|_𝔘 ≅ Spf_P A` taken along an arbitrary weak ideal system `P`. Two maps into the sections of
`𝒪_𝔛` over an open `W` agree, after the comparison map of the inclusion of `𝔘`, as soon as they
agree after the comparison maps of all the chart points `Spec (A/I) → 𝔛`.

The comparison map of the chart isomorphism is a monomorphism, and the sections of
`𝒪_{Spf_P A} = lim 𝒪_λ` are separated by the projections
(`AlgebraicGeometry.spfPointOn_hom_ext`), neither of which asks that the members of `P` be the
powers of a single ideal. -/
theorem formalChartPointOn_c_app_hom_ext
    (W : Opens X) {R : TopCommRingCat.{u}} {a b : R ⟶ X.presheaf.obj (op W)}
    (h : ∀ I : SpfIndex A P,
      a ≫ (formalChartPointOn U A e I).toHom.c.app (op W)
        = b ≫ (formalChartPointOn U A e I).toHom.c.app (op W)) :
    a ≫ (X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding').c.app (op W)
      = b ≫ (X.toPresheafedSpace.ofRestrict
        (f := U.inclusion') U.isOpenEmbedding').c.app (op W) := by
  have hmono : Mono (e.inv.c.app (op ((Opens.map U.inclusion').obj W))) :=
    mono_c_app_of_iso e.symm (op ((Opens.map U.inclusion').obj W))
  refine (cancel_mono (e.inv.c.app (op ((Opens.map U.inclusion').obj W)))).1 ?_
  refine spfPointOn_hom_ext A fun I => ?_
  exact h I

/-- **Two maps into the sections of `𝒪_𝔛` over an open contained in a chart `𝔛|_𝔘 ≅ Spf_P A`
agree as soon as they agree after the comparison maps of the chart points**, for an arbitrary
weak ideal system `P`. -/
theorem formalChartPointOn_hom_ext_of_le
    {W : Opens X} (hWU : W ≤ U) {R : TopCommRingCat.{u}} {a b : R ⟶ X.presheaf.obj (op W)}
    (h : ∀ I : SpfIndex A P,
      a ≫ (formalChartPointOn U A e I).toHom.c.app (op W)
        = b ≫ (formalChartPointOn U A e I).toHom.c.app (op W)) : a = b := by
  have := isIso_ofRestrict_c_app U hWU
  exact (cancel_mono ((X.toPresheafedSpace.ofRestrict
    (f := U.inclusion') U.isOpenEmbedding').c.app (op W))).1
    (formalChartPointOn_c_app_hom_ext U A e W h)

variable (V : Opens X)

/-- The preimage in `Spec (A/I)` of an open `𝔙` of `𝔛` under the chart point attached to a chart
`𝔛|_𝔘 ≅ Spf_P A` taken along an arbitrary weak ideal system `P`. -/
noncomputable def chartPointOnPreimage (I : SpfIndex A P) :
    Opens ↥(schemeToLTRSObj (Spec (spfQuotientOn A I))) :=
  (Opens.map (formalChartPointOn U A e I).toHom.base).obj V

/-- The chart point of a chart taken along an arbitrary weak ideal system, restricted to the
preimage of `𝔙` and read as a morphism into `𝔛`. -/
noncomputable def chartPointOnMap (I : SpfIndex A P) :
    (schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict (chartPointOnPreimage U A e V I) ⟶ X :=
  (schemeToLTRSObj (Spec (spfQuotientOn A I))).ofRestrict (chartPointOnPreimage U A e V I)
    ≫ formalChartPointOn U A e I

/-- The chart point restricted to the preimage of `𝔙` has image inside `𝔙`. -/
theorem range_chartPointOnMap (I : SpfIndex A P) :
    Set.range (chartPointOnMap U A e V I).toHom.base
      ⊆ Set.range (X.ofRestrict V).toHom.base := by
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨_, q.2⟩, rfl⟩

/-- **The chart point of `𝔛` over the preimage of an open `𝔙`, as a morphism into `𝔛|_𝔙`**, for a
chart taken along an arbitrary weak ideal system. -/
noncomputable def chartPointOnRestrict (I : SpfIndex A P) :
    (schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict (chartPointOnPreimage U A e V I)
      ⟶ X.restrict V :=
  { toHom := PresheafedSpace.IsOpenImmersion.lift (X.ofRestrict V).toHom
      (chartPointOnMap U A e V I).toHom (range_chartPointOnMap U A e V I)
    isLocalHom := by
      intro q
      set j := (X.ofRestrict V).toHom with hj
      set l := PresheafedSpace.IsOpenImmersion.lift j (chartPointOnMap U A e V I).toHom
        (range_chartPointOnMap U A e V I) with hl
      have hfac : l ≫ j = (chartPointOnMap U A e V I).toHom :=
        PresheafedSpace.IsOpenImmersion.lift_fac _ _ _
      have h1 : IsLocalHom ((l ≫ j).stalkMap q).1 := by
        rw [hfac]; exact (chartPointOnMap U A e V I).isLocalHom q
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
theorem chartPointOnRestrict_comp_ofRestrict (I : SpfIndex A P) :
    chartPointOnRestrict U A e V I ≫ X.ofRestrict V = chartPointOnMap U A e V I :=
  LocallyTopologicallyRingedSpace.Hom.ext'
    (PresheafedSpace.IsOpenImmersion.lift_fac (X.ofRestrict V).toHom
      (chartPointOnMap U A e V I).toHom (range_chartPointOnMap U A e V I))

/-- **The restricted chart points are jointly surjective onto `𝔙`**, for a chart taken along an
arbitrary weak ideal system: every point of `𝔙` is in the image of the chart point
`Spec (A/I) → 𝔛` restricted to the preimage of `𝔙`, for every member `I` of the system. -/
theorem exists_chartPointOnRestrict_base_eq (hVU : V ≤ U) (I : SpfIndex A P)
    (x : ↥(X.restrict V)) :
    ∃ y, (chartPointOnRestrict U A e V I).toHom.base y = x := by
  obtain ⟨y, hy⟩ := exists_formalChartPointOn_base_eq U A e I (hVU x.2)
  have hyQ : y ∈ chartPointOnPreimage U A e V I := by
    show (formalChartPointOn U A e I).toHom.base y ∈ V
    rw [hy]; exact x.2
  refine ⟨⟨y, hyQ⟩, Subtype.ext ?_⟩
  have hbase := congrArg (fun m : (schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict
      (chartPointOnPreimage U A e V I) ⟶ X => m.toHom.base)
    (chartPointOnRestrict_comp_ofRestrict U A e V I)
  exact (congrFun (congrArg (fun k => (ConcreteCategory.hom k : _ → _)) hbase) ⟨y, hyQ⟩).trans hy

/-- **Morphisms out of `𝔛|_𝔙`, for `𝔙` contained in a chart `𝔛|_𝔘 ≅ Spf_P A` taken along an
arbitrary weak ideal system `P` with a member `I₀`, are separated by the restricted chart
points.** They are jointly surjective by
`AlgebraicGeometry.exists_chartPointOnRestrict_base_eq`, and they separate the sections of
`𝒪_𝔛` over the opens contained in `𝔙` by
`AlgebraicGeometry.formalChartPointOn_hom_ext_of_le`, the sections of `𝒪_{𝔛|_𝔙}` over an open `W`
being those of `𝒪_𝔛` over the image of `W` in `𝔛`.

This is the separation statement that settles the overlaps in the fullness argument, and the one
place where a member of the system has to be produced; the admissible counterpart
`AlgebraicGeometry.restrict_hom_ext_of_chart` takes a pre-admissibility hypothesis and extracts
one from it. -/
theorem restrict_hom_ext_of_chartOn (I₀ : SpfIndex A P) (hVU : V ≤ U) {Y : LTRS.{u}}
    {u v : X.restrict V ⟶ Y}
    (h : ∀ I : SpfIndex A P,
      chartPointOnRestrict U A e V I ≫ u = chartPointOnRestrict U A e V I ≫ v) : u = v := by
  refine LocallyTopologicallyRingedSpace.Hom.ext' (presheafedSpace_hom_ext_of_cover
    (fun I : SpfIndex A P => (chartPointOnRestrict U A e V I).toHom)
    (fun x => ⟨I₀, exists_chartPointOnRestrict_base_eq U A e V hVU I₀ x⟩) ?_ _ _
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
  refine formalChartPointOn_hom_ext_of_le U A e (hWXV.trans hVU) fun I => ?_
  -- The two further comparison isomorphisms, over the preimage of `WX`.
  set m3 := ((schemeToLTRSObj (Spec (spfQuotientOn A I))).ofRestrict
      (chartPointOnPreimage U A e V I)).toHom.c.app
      (op ((Opens.map (formalChartPointOn U A e I).toHom.base).obj WX)) with hm3
  have : IsIso m3 := by
    rw [hm3]
    exact isIso_ofRestrict_toHom_c_app (chartPointOnPreimage U A e V I) fun z hz => hWXV hz
  have hop : (Opens.map (chartPointOnMap U A e V I).toHom.base).obj WX
      = (Opens.map (chartPointOnRestrict U A e V I ≫ X.ofRestrict V).toHom.base).obj WX :=
    congrArg (fun m : (schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict
        (chartPointOnPreimage U A e V I) ⟶ X => (Opens.map m.toHom.base).obj WX)
      (chartPointOnRestrict_comp_ofRestrict U A e V I).symm
  set mm := ((schemeToLTRSObj (Spec (spfQuotientOn A I))).restrict
      (chartPointOnPreimage U A e V I)).presheaf.map (eqToHom (congrArg op hop)) with hmm
  have : IsIso mm := by rw [hmm]; infer_instance
  have keyc : (chartPointOnRestrict U A e V I ≫ X.ofRestrict V).toHom.c.app (op WX)
      = (chartPointOnMap U A e V I).toHom.c.app (op WX) ≫ mm :=
    PresheafedSpace.congr_app (congrArg LocallyTopologicallyRingedSpace.Hom.toHom
      (chartPointOnRestrict_comp_ofRestrict U A e V I)) (op WX)
  have hnat := (chartPointOnRestrict U A e V I).toHom.c.naturality
    (eqToHom (congrArg op hW.symm))
  have hptc : (formalChartPointOn U A e I).toHom.c.app (op WX) ≫ (m3 ≫ mm)
      = (X.ofRestrict V).toHom.c.app (op WX)
        ≫ (chartPointOnRestrict U A e V I).toHom.c.app
            (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX)) :=
    (Category.assoc _ _ _).symm.trans keyc.symm
  have hcollapse : ∀ z : R ⟶ (X.restrict V).presheaf.obj (op W),
      (((z ≫ (m1 ≫ inv ((X.ofRestrict V).toHom.c.app (op WX))))
            ≫ (formalChartPointOn U A e I).toHom.c.app (op WX)) ≫ m3) ≫ mm
        = z ≫ m1 ≫ (chartPointOnRestrict U A e V I).toHom.c.app
            (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX)) := by
    intro z
    rw [Category.assoc _ m3 mm,
      Category.assoc _ ((formalChartPointOn U A e I).toHom.c.app (op WX)) (m3 ≫ mm), hptc]
    show (z ≫ (m1 ≫ inv ((X.ofRestrict V).toHom.c.app (op WX))))
          ≫ ((X.ofRestrict V).toHom.c.app (op WX)
            ≫ (chartPointOnRestrict U A e V I).toHom.c.app
                (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX)))
        = z ≫ m1 ≫ (chartPointOnRestrict U A e V I).toHom.c.app
            (op ((Opens.map (X.ofRestrict V).toHom.base).obj WX))
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  refine (cancel_mono m3).1 ((cancel_mono mm).1 ?_)
  refine (hcollapse a).trans (Eq.trans ?_ (hcollapse b).symm)
  rw [hnat, ← Category.assoc, ← Category.assoc, hab I]

end ChartOn

/-! ### Naturality on the McQuillan functor of points -/

/-- A morphism of schemes of size below `κ` acts on points of a McQuillan formal scheme by
precomposition. -/
theorem mcQuillanFormalSchemeFunctorOfPoints_obj_map (κ : Cardinal.{u})
    (X : McQuillanFormalScheme.{u}) {S T : (schemeCutoff κ).FullSubcategory} (t : S.obj ⟶ T.obj)
    (u : schemeToMcQuillanFormalScheme.obj T.obj ⟶ X) :
    ((mcQuillanFormalSchemeFunctorOfPoints κ).obj X).map (ObjectProperty.homMk t : S ⟶ T).op u
      = schemeToMcQuillanFormalScheme.map t ≫ u := rfl

/-- Naturality of a transformation of functors of points of McQuillan formal schemes, spelled out
on points: the transformation commutes with precomposition by a morphism of `Sch_κ`. -/
theorem app_comp_of_natTrans_mcQuillan {κ : Cardinal.{u}} {X Y : McQuillanFormalScheme.{u}}
    (φ : (mcQuillanFormalSchemeFunctorOfPoints κ).obj X ⟶
      (mcQuillanFormalSchemeFunctorOfPoints κ).obj Y)
    {S T : (schemeCutoff κ).FullSubcategory} (t : S.obj ⟶ T.obj)
    (u : schemeToMcQuillanFormalScheme.obj T.obj ⟶ X) :
    φ.app (op S) (schemeToMcQuillanFormalScheme.map t ≫ u)
      = schemeToMcQuillanFormalScheme.map t ≫ φ.app (op T) u :=
  NatTrans.naturality_apply φ (ObjectProperty.homMk t : S ⟶ T).op u

/-! ### Fullness for McQuillan's formal spectrum -/

section Spfw

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hA : IsWeaklyAdmissible A)

/-- The point `Spec (A/I) → Spfw A` of McQuillan's formal spectrum, as a morphism of McQuillan
formal schemes. -/
noncomputable def spfwMcQuillanFormalSchemePoint (I : WeakIdealsOfDefinition A) :
    schemeToMcQuillanFormalScheme.obj (Spec (spfQuotientOn A I)) ⟶ spfwMcQuillanFormalScheme A hA :=
  ObjectProperty.homMk (spfQuotientPointOn A (weaklyPreAdmissibleSpfIndex A hA.1) I)

/-- The points of McQuillan's formal spectrum are compatible with the transition maps of the
system of quotients. -/
theorem schemeToMcQuillanFormalScheme_map_comp_spfwMcQuillanFormalSchemePoint
    {I J : WeakIdealsOfDefinition A} (h : I.1 ≤ J.1) :
    schemeToMcQuillanFormalScheme.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
          ≫ spfwMcQuillanFormalSchemePoint A hA I
      = spfwMcQuillanFormalSchemePoint A hA J :=
  InducedCategory.hom_ext (spfQuotientTransitionOn_comp_spfQuotientPointOn A
    (weaklyPreAdmissibleSpfIndex A hA.1) h)

/-- McQuillan's formal spectrum of a weakly admissible topological ring satisfies the size
condition in this setting as soon as all the schemes `Spec (A/I_λ)` do: it is its own weak affine
formal chart. -/
theorem isSizeBoundedMcQuillanFormalScheme_spfwLTRS {κ : Cardinal.{u}}
    (hsize : ∀ I : WeakIdealsOfDefinition A, (Spec (spfQuotientOn A I)).size < κ) :
    IsSizeBoundedMcQuillanFormalScheme κ (spfwLTRS A hA.1) := fun _ =>
  ⟨⊤, trivial, TopCommRingCat.of A, inferInstance, hA, hsize,
    ⟨PresheafedSpace.restrictTopIso _⟩⟩

variable {κ : Cardinal.{u}} {Y : McQuillanFormalScheme.{u}}

/-- The quotient `Spec (A/I)` by a weak ideal of definition, as an object of the cutoff category
`Sch_κ`. -/
noncomputable def spfwCutoffQuotient
    (hsize : ∀ I : WeakIdealsOfDefinition A, (Spec (spfQuotientOn A I)).size < κ)
    (I : WeakIdealsOfDefinition A) : (schemeCutoff κ).FullSubcategory :=
  ⟨Spec (spfQuotientOn A I), hsize I⟩

/-- The morphism `Spec (A/I) → 𝔜` that a transformation of functors of points attaches to the
point `Spec (A/I) → Spfw A`. -/
noncomputable def spfwTransValue
    (hsize : ∀ I : WeakIdealsOfDefinition A, (Spec (spfQuotientOn A I)).size < κ)
    (φ : (mcQuillanFormalSchemeFunctorOfPoints κ).obj (spfwMcQuillanFormalScheme A hA) ⟶
      (mcQuillanFormalSchemeFunctorOfPoints κ).obj Y) (I : WeakIdealsOfDefinition A) :
    schemeToMcQuillanFormalScheme.obj (Spec (spfQuotientOn A I)) ⟶ Y :=
  φ.app (op (spfwCutoffQuotient A hsize I)) (spfwMcQuillanFormalSchemePoint A hA I)

/-- The morphisms a transformation of functors of points attaches to the points
`Spec (A/I) → Spfw A` form a family compatible with the transition maps of the system of
quotients: this is the naturality of the transformation at those transition maps. -/
theorem spfQuotientTransition_comp_spfwTransValue
    (hsize : ∀ I : WeakIdealsOfDefinition A, (Spec (spfQuotientOn A I)).size < κ)
    (φ : (mcQuillanFormalSchemeFunctorOfPoints κ).obj (spfwMcQuillanFormalScheme A hA) ⟶
      (mcQuillanFormalSchemeFunctorOfPoints κ).obj Y)
    (I J : WeakIdealsOfDefinition A) (h : I.1 ≤ J.1) :
    spfQuotientTransitionOn A h ≫ (spfwTransValue A hA hsize φ I).hom
      = (spfwTransValue A hA hsize φ J).hom := by
  have key : schemeToMcQuillanFormalScheme.map
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
        ≫ spfwTransValue A hA hsize φ I = spfwTransValue A hA hsize φ J := by
    show schemeToMcQuillanFormalScheme.map
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
        ≫ φ.app (op (spfwCutoffQuotient A hsize I)) (spfwMcQuillanFormalSchemePoint A hA I)
      = φ.app (op (spfwCutoffQuotient A hsize J)) (spfwMcQuillanFormalSchemePoint A hA J)
    rw [← schemeToMcQuillanFormalScheme_map_comp_spfwMcQuillanFormalSchemePoint A hA h]
    exact (app_comp_of_natTrans_mcQuillan φ (S := spfwCutoffQuotient A hsize J)
      (T := spfwCutoffQuotient A hsize I)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
      (spfwMcQuillanFormalSchemePoint A hA I)).symm
  exact congrArg InducedCategory.Hom.hom key

/-- **Stacks 0AI3**, fullness for McQuillan's formal spectrum. Every transformation of functors
of points out of the functor of points of `Spfw A` comes from a morphism of McQuillan formal
schemes, provided all the schemes `Spec (A/I_λ)` are objects of `Sch_κ`.

This is the source's proof of Lemma 87.2.1 unchanged: the transformation sends the points
`Spec (A/I_λ) → Spfw A` to a compatible family of morphisms `Spec (A/I_λ) → 𝔜`, which assembles
into a morphism `Spfw A → 𝔜` by the mapping-limit formula
`AlgebraicGeometry.existsUnique_hom_of_spfQuotientPointOn_comp_eq`, stated for an arbitrary weak
ideal system. That morphism induces the given transformation: over an *affine* scheme every point
of `Spfw A` factors through one of the quotients by
`AlgebraicGeometry.exists_factor_spfQuotientPointOn`, the hypothesis it consumes on the canonical
map `A → Γ(Spfw A, 𝒪)` being `AlgebraicGeometry.isIso_spfwGammaHom`; a general scheme is covered
by affine opens, and the functor of points of `𝔜` is a Zariski sheaf. -/
theorem exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq_spfw
    (hsize : ∀ I : WeakIdealsOfDefinition A, (Spec (spfQuotientOn A I)).size < κ)
    (φ : (mcQuillanFormalSchemeFunctorOfPoints κ).obj (spfwMcQuillanFormalScheme A hA) ⟶
      (mcQuillanFormalSchemeFunctorOfPoints κ).obj Y) :
    ∃ f : spfwMcQuillanFormalScheme A hA ⟶ Y,
      (mcQuillanFormalSchemeFunctorOfPoints κ).map f = φ := by
  obtain ⟨f₀, hf₀, -⟩ := existsUnique_hom_of_spfQuotientPointOn_comp_eq A
    (weaklyPreAdmissibleSpfIndex A hA.1)
    (fun I => (spfwTransValue A hA hsize φ I).hom)
    (spfQuotientTransition_comp_spfwTransValue A hA hsize φ)
  set f : spfwMcQuillanFormalScheme A hA ⟶ Y := ObjectProperty.homMk f₀ with hf
  have hpoint : ∀ I : WeakIdealsOfDefinition A,
      spfwMcQuillanFormalSchemePoint A hA I ≫ f = spfwTransValue A hA hsize φ I := fun I =>
    InducedCategory.hom_ext (hf₀ I)
  refine ⟨f, ?_⟩
  ext S s
  obtain ⟨S⟩ := S
  show s ≫ f = φ.app (op S) s
  -- Cover `S` by affine opens.
  set V : S.obj.affineCover.I₀ → S.obj.Opens := fun i => (S.obj.affineCover.f i).opensRange
    with hVdef
  have hV : iSup V = ⊤ := S.obj.affineCover.iSup_opensRange
  have hVaff : ∀ i, IsAffine (V i).toScheme := fun i =>
    isAffineOpen_opensRange (S.obj.affineCover.f i)
  have hVsize : ∀ i, schemeCutoff κ (V i).toScheme := fun i =>
    Scheme.size_lt_of_isOpenImmersion (V i).ι S.property
  refine (isSheafFor_opensCover_mcQuillanFormalSchemePoints Y V hV).isSeparatedFor.ext ?_
  rintro Z t ⟨i⟩
  show schemeToMcQuillanFormalScheme.map (V i).ι ≫ (s ≫ f)
    = schemeToMcQuillanFormalScheme.map (V i).ι ≫ φ.app (op S) s
  have := hVaff i
  -- The point of `Spfw A` over the affine `V i` factors through a quotient.
  obtain ⟨I, a, ha⟩ := exists_factor_spfQuotientPointOn A (weaklyPreAdmissibleSpfIndex A hA.1)
    (isIso_spfwGammaHom A hA) (V i).toScheme
    (schemeToMcQuillanFormalScheme.map (V i).ι ≫ s).hom
  have hfac : schemeToMcQuillanFormalScheme.map a ≫ spfwMcQuillanFormalSchemePoint A hA I
      = schemeToMcQuillanFormalScheme.map (V i).ι ≫ s := InducedCategory.hom_ext ha
  have e1 : schemeToMcQuillanFormalScheme.map (V i).ι ≫ φ.app (op S) s
      = φ.app (op ⟨(V i).toScheme, hVsize i⟩)
          (schemeToMcQuillanFormalScheme.map (V i).ι ≫ s) :=
    (app_comp_of_natTrans_mcQuillan φ (S := ⟨(V i).toScheme, hVsize i⟩) (T := S) (V i).ι s).symm
  have e2 : φ.app (op ⟨(V i).toScheme, hVsize i⟩)
        (schemeToMcQuillanFormalScheme.map (V i).ι ≫ s)
      = schemeToMcQuillanFormalScheme.map a ≫ spfwTransValue A hA hsize φ I := by
    rw [← hfac]
    exact app_comp_of_natTrans_mcQuillan φ (S := ⟨(V i).toScheme, hVsize i⟩)
      (T := spfwCutoffQuotient A hsize I) a (spfwMcQuillanFormalSchemePoint A hA I)
  calc schemeToMcQuillanFormalScheme.map (V i).ι ≫ (s ≫ f)
      = (schemeToMcQuillanFormalScheme.map a ≫ spfwMcQuillanFormalSchemePoint A hA I) ≫ f := by
        rw [hfac]; exact (Category.assoc _ _ _).symm
    _ = schemeToMcQuillanFormalScheme.map a ≫ spfwTransValue A hA hsize φ I := by
        rw [Category.assoc, hpoint I]
    _ = schemeToMcQuillanFormalScheme.map (V i).ι ≫ φ.app (op S) s := (e1.trans e2).symm

end Spfw

/-! ### Fullness in general -/

/-- **The morphism a transformation of functors of points induces on a weak affine formal
chart.** Transporting the chart isomorphism `𝔛|_𝔘 ≅ Spfw A` turns the transformation into one out
of the functor of points of `Spfw A`, where
`AlgebraicGeometry.exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq_spfw` applies; the
resulting morphism `𝔛|_𝔘 → 𝔜` realizes the transformation on every point of `𝔘` defined over an
object of `Sch_κ`. -/
theorem exists_hom_restrict_of_weakChart {κ : Cardinal.{u}}
    {X Y : McQuillanFormalScheme.{u}}
    (U : Opens X.obj) (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : IsWeaklyAdmissible A)
    (hsize : ∀ I : WeakIdealsOfDefinition A, (Spec (spfQuotientOn A I)).size < κ)
    (e : X.obj.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spfw A)
    (φ : (mcQuillanFormalSchemeFunctorOfPoints κ).obj X ⟶
      (mcQuillanFormalSchemeFunctorOfPoints κ).obj Y) :
    ∃ fU : X.obj.restrict U ⟶ Y.obj, ∀ (S : (schemeCutoff κ).FullSubcategory)
      (t : schemeToLTRSObj S.obj ⟶ X.obj.restrict U),
      t ≫ fU = (φ.app (op S) (ObjectProperty.homMk (t ≫ X.obj.ofRestrict U) :
        schemeToMcQuillanFormalScheme.obj S.obj ⟶ X)).hom := by
  set χ : X.obj.restrict U ≅ spfwLTRS A hA.1 := ltrsIsoOfPresheafedSpaceIso e with hχ
  set ι : spfwMcQuillanFormalScheme A hA ⟶ X :=
    ObjectProperty.homMk (χ.inv ≫ X.obj.ofRestrict U) with hι
  obtain ⟨f', hf'⟩ := exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq_spfw A hA hsize
    ((mcQuillanFormalSchemeFunctorOfPoints κ).map ι ≫ φ)
  refine ⟨χ.hom ≫ f'.hom, fun S t => ?_⟩
  set w : schemeToMcQuillanFormalScheme.obj S.obj ⟶ spfwMcQuillanFormalScheme A hA :=
    ObjectProperty.homMk (t ≫ χ.hom) with hw
  have hwι : w ≫ ι = (ObjectProperty.homMk (t ≫ X.obj.ofRestrict U) :
      schemeToMcQuillanFormalScheme.obj S.obj ⟶ X) := by
    refine InducedCategory.hom_ext ?_
    show (t ≫ χ.hom) ≫ (χ.inv ≫ X.obj.ofRestrict U) = t ≫ X.obj.ofRestrict U
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  have key := congrFun (congrArg (fun η => (ConcreteCategory.hom (η.app (op S)) : _ → _)) hf') w
  have h2 : (φ.app (op S) (w ≫ ι)).hom
      = (φ.app (op S) (ObjectProperty.homMk (t ≫ X.obj.ofRestrict U) :
          schemeToMcQuillanFormalScheme.obj S.obj ⟶ X)).hom := by rw [hwι]
  exact (Category.assoc t χ.hom f'.hom).symm.trans
    ((congrArg InducedCategory.Hom.hom key).trans h2)

/-- **Stacks 0AI3**, fullness. Every transformation `h_𝔛 → h_𝔜` of functors of points on `Sch_κ`
out of a McQuillan formal scheme `𝔛` satisfying the size condition is induced by a morphism of
McQuillan formal schemes `𝔛 → 𝔜`.

The proof is the source's, and is the one already carried out for admissible rings in
`AlgebraicGeometry.exists_formalSchemeFunctorOfPoints_map_eq`. Each weak affine formal chart
`𝔛|_𝔘_x ≅ Spfw A_x` carries a morphism `𝔛|_𝔘_x → 𝔜` realizing the transformation, by
`AlgebraicGeometry.exists_hom_restrict_of_weakChart`. Those morphisms agree on the overlaps: the
restricted chart points separate morphisms out of `𝔛|_{𝔘_x ⊓ 𝔘_y}` by
`AlgebraicGeometry.restrict_hom_ext_of_chartOn`, and after a restricted chart point both sides
are the same value of the transformation. So they glue, by
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover`. The glued
morphism induces the transformation: a point of `𝔛` over an object of `Sch_κ` is covered by the
preimages of the `𝔘_x`, on each of which it factors through `𝔛|_{𝔘_x}`, and the functor of
points of `𝔜` is a Zariski sheaf. -/
theorem exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq {κ : Cardinal.{u}}
    {X Y : McQuillanFormalScheme.{u}} (hX : IsSizeBoundedMcQuillanFormalScheme κ X.obj)
    (φ : (mcQuillanFormalSchemeFunctorOfPoints κ).obj X ⟶
      (mcQuillanFormalSchemeFunctorOfPoints κ).obj Y) :
    ∃ f : X ⟶ Y, (mcQuillanFormalSchemeFunctorOfPoints κ).map f = φ := by
  classical
  choose U hxU A hlin hdata using hX
  have hchart : ∀ x : X.obj, ∃ fU : X.obj.restrict (U x) ⟶ Y.obj,
      ∀ (S : (schemeCutoff κ).FullSubcategory)
        (t : schemeToLTRSObj S.obj ⟶ X.obj.restrict (U x)),
        t ≫ fU = (φ.app (op S) (ObjectProperty.homMk (t ≫ X.obj.ofRestrict (U x)) :
          schemeToMcQuillanFormalScheme.obj S.obj ⟶ X)).hom := by
    intro x
    have := hlin x
    exact exists_hom_restrict_of_weakChart (U x) (A x).α (hdata x).1 (hdata x).2.1
      (hdata x).2.2.some φ
  choose fU hfU using hchart
  have hfU' : ∀ (w : X.obj) (S : (schemeCutoff κ).FullSubcategory)
      (m : schemeToLTRSObj S.obj ⟶ X.obj)
      (t : schemeToLTRSObj S.obj ⟶ X.obj.restrict (U w)), t ≫ X.obj.ofRestrict (U w) = m →
      t ≫ fU w = (φ.app (op S) (ObjectProperty.homMk m :
        schemeToMcQuillanFormalScheme.obj S.obj ⟶ X)).hom := by
    rintro w S - t rfl
    exact hfU w S t
  -- The chart-wise morphisms agree on the overlaps.
  have compat : ∀ x y : X.obj, X.obj.resLE (inf_le_left : U x ⊓ U y ≤ U x) ≫ fU x
      = X.obj.resLE (inf_le_right : U x ⊓ U y ≤ U y) ≫ fU y := by
    intro x y
    have := hlin x
    refine restrict_hom_ext_of_chartOn (U x) (A x).α (hdata x).2.2.some (U x ⊓ U y)
      (weaklyPreAdmissibleSpfIndex (A x).α (hdata x).1.1) inf_le_left fun I => ?_
    set O : (Spec (spfQuotientOn (A x).α I)).Opens :=
      chartPointOnPreimage (U x) (A x).α (hdata x).2.2.some (U x ⊓ U y) I with hO
    have hOsize : schemeCutoff κ O.toScheme :=
      Scheme.size_lt_of_isOpenImmersion O.ι ((hdata x).2.1 I)
    set iso := schemeToLTRSRestrictIso (Spec (spfQuotientOn (A x).α I)) O with hiso
    set cpr := chartPointOnRestrict (U x) (A x).α (hdata x).2.2.some (U x ⊓ U y) I with hcpr
    have side : ∀ (w : X.obj) (hle : U x ⊓ U y ≤ U w),
        (iso.hom ≫ cpr) ≫ (X.obj.resLE hle ≫ fU w)
          = (φ.app (op ⟨O.toScheme, hOsize⟩) (ObjectProperty.homMk
              ((iso.hom ≫ cpr) ≫ X.obj.ofRestrict (U x ⊓ U y)) :
            schemeToMcQuillanFormalScheme.obj O.toScheme ⟶ X)).hom := fun w hle =>
      (Category.assoc _ _ _).symm.trans (hfU' w ⟨O.toScheme, hOsize⟩ _ _ (by
        rw [Category.assoc, LocallyTopologicallyRingedSpace.resLE_comp_ofRestrict]; rfl))
    have main := (side x inf_le_left).trans (side y inf_le_right).symm
    exact (Iso.cancel_iso_hom_left iso _ _).1
      ((Category.assoc _ _ _).symm.trans (main.trans (Category.assoc _ _ _)))
  -- Glue.
  have hcover : iSup U = ⊤ :=
    Opens.ext (Set.eq_univ_iff_forall.2 fun x => by
      rw [Opens.coe_iSup]; exact Set.mem_iUnion.2 ⟨x, hxU x⟩)
  obtain ⟨f₀, hf₀, -⟩ := LocallyTopologicallyRingedSpace.existsUnique_hom_of_openCover
    U hcover fU compat
  set fglue : X ⟶ Y := ObjectProperty.homMk f₀ with hfglue
  refine ⟨fglue, ?_⟩
  ext S s
  obtain ⟨S⟩ := S
  show s ≫ fglue = φ.app (op S) s
  set O : ↥X.obj → S.obj.Opens := fun x => (Opens.map s.hom.toHom.base).obj (U x) with hOdef
  have hOcover : iSup O = ⊤ :=
    Opens.ext (Set.eq_univ_iff_forall.2 fun z =>
      Opens.mem_iSup.2 ⟨s.hom.toHom.base z, hxU _⟩)
  have hOsize : ∀ x, schemeCutoff κ (O x).toScheme := fun x =>
    Scheme.size_lt_of_isOpenImmersion (O x).ι S.property
  refine (isSheafFor_opensCover_mcQuillanFormalSchemePoints Y O hOcover).isSeparatedFor.ext ?_
  rintro Z τ ⟨x⟩
  show schemeToMcQuillanFormalScheme.map (O x).ι ≫ (s ≫ fglue)
    = schemeToMcQuillanFormalScheme.map (O x).ι ≫ φ.app (op S) s
  set g : schemeToLTRSObj (O x).toScheme ⟶ X.obj :=
    (schemeToMcQuillanFormalScheme.map (O x).ι ≫ s).hom with hg
  have hrange : Set.range g.toHom.base ⊆ Set.range (X.obj.ofRestrict (U x)).toHom.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, z.2⟩, rfl⟩
  have hfac : liftToRestrict (U x) g hrange ≫ X.obj.ofRestrict (U x) = g :=
    liftToRestrict_comp_ofRestrict (U x) g hrange
  have hgmk : (ObjectProperty.homMk g :
      schemeToMcQuillanFormalScheme.obj (O x).toScheme ⟶ X)
      = schemeToMcQuillanFormalScheme.map (O x).ι ≫ s := InducedCategory.hom_ext rfl
  have hchar3 := (hfU' x ⟨(O x).toScheme, hOsize x⟩ g _ hfac).trans
    ((congrArg (fun w : schemeToMcQuillanFormalScheme.obj (O x).toScheme ⟶ X =>
      (φ.app (op ⟨(O x).toScheme, hOsize x⟩) w).hom) hgmk).trans (congrArg InducedCategory.Hom.hom
    (app_comp_of_natTrans_mcQuillan φ (S := ⟨(O x).toScheme, hOsize x⟩) (T := S) (O x).ι s)))
  refine InducedCategory.hom_ext (Eq.trans ?_ hchar3)
  show (schemeToMcQuillanFormalScheme.map (O x).ι).hom ≫ (s.hom ≫ f₀)
    = liftToRestrict (U x) g hrange ≫ fU x
  conv_rhs => rw [← hf₀ x]
  exact (Category.assoc _ _ _).symm.trans
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun m : schemeToLTRSObj (O x).toScheme ⟶ X.obj => m ≫ f₀) hfac)).symm)

/-- **Stacks 0AI3**, the counterpart of Lemma 87.2.1 in McQuillan's setting, in full. For a
McQuillan formal scheme `𝔛` whose size is not too large — the schemes `Spec (A/I_λ)` cut out of
its weak affine formal charts being objects of `Sch_κ` — and any McQuillan formal scheme `𝔜`,

`Mor_{McQuillan Formal Schemes}(𝔛, 𝔜) = Mor_{PSh(Sch_κ)}(h_𝔛, h_𝔜)`.

Injectivity is `AlgebraicGeometry.injective_mcQuillanFormalSchemeFunctorOfPoints_map` and
surjectivity is `AlgebraicGeometry.exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq`. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.1: the bijection Mor(𝔛, 𝔜) = Mor(h_𝔛, h_𝔜) for a \
McQuillan formal scheme 𝔛 whose size is bounded by the cutoff"]
theorem bijective_mcQuillanFormalSchemeFunctorOfPoints_map {κ : Cardinal.{u}}
    {X Y : McQuillanFormalScheme.{u}} (hX : IsSizeBoundedMcQuillanFormalScheme κ X.obj) :
    Function.Bijective fun f : X ⟶ Y => (mcQuillanFormalSchemeFunctorOfPoints κ).map f :=
  ⟨injective_mcQuillanFormalSchemeFunctorOfPoints_map hX,
    fun φ => exists_mcQuillanFormalSchemeFunctorOfPoints_map_eq hX φ⟩

end AlgebraicGeometry

end
