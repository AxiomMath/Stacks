module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BirationalDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Birational morphisms of algebraic spaces are isomorphisms over dense opens

A birational morphism `f : X ⟶ Y` of decent algebraic spaces over a scheme `S` with finitely
many irreducible components restricts to an isomorphism between dense open subspaces, provided
it is locally of finite type with reduced target or locally of finite presentation. This is
**Stacks 0BBE**.

## Main results

* `AlgebraicGeometry.Space.exists_dense_isOpenSubspace_isIso_of_isBirational` is Stacks 0BBE:
  there are dense open subspaces `U ⊆ X` and `V ⊆ Y` and an isomorphism `U ⟶ V` commuting with
  `f`.

## Implementation notes

The whole content is the reduction of the statement to schemes, because the scheme-level
statement `AlgebraicGeometry.exists_dense_opens_isIso_resLE_of_isBirational` (Stacks 0BAC) is
available.

The reduction runs on representable dense open charts rather than on the schematic locus.
Decency supplies a representable open subspace with dense point set
(`AlgebraicGeometry.Space.hasDenseRepresentableOpenSubspace_of_isDecentSpace`), hence open
immersions `u : h_A ⟶ X` and `v : h_C ⟶ Y` from representable presheaves with dense point sets.
Shrinking `A` to the open subscheme cut out by the preimage of the point set of `v` makes
`u ≫ f` factor through `v`, by Stacks 03BZ in the form
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`, and the factorization comes from a
morphism `g : A ⟶ C` of the site. The point set of a dense open chart contains every generic
point, so the shrunken chart is still dense; here the point space is quasi-sober, which is
where decency enters a second time (Stacks 03K6).

The underlying morphism of schemes of `g` is birational: its bijection on generic points is
assembled from the bijections induced by the two open charts and the bijection of `f`, and its
stalk maps are identified with the local-ring maps of `f` at generic points by
`AlgebraicGeometry.Space.exists_genericLocalRingMap`, whose characterization is stated for
arbitrary generic charts and so applies to the two charts directly.

Being locally of finite type or locally of finite presentation is by definition a condition on
every commuting square of étale charts
(`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`), so it transfers to `g` by instantiation;
reducedness of the target is read off the chart `C` by Stacks 03E8
(`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`), and is therefore phrased as
`AlgebraicGeometry.Space.HasEtaleLocalProperty` for the property of being a reduced scheme.
Transporting the resulting isomorphism of open subschemes back upstairs uses
`AlgebraicGeometry.exists_restrict_bigFppfOver` to realize the two scheme opens as objects of
the site, and the image subfunctors of the resulting open immersions as the two open subspaces.

## References

* [Stacks Project, Tag 0BBE](https://stacks.math.columbia.edu/tag/0BBE)
* [Stacks Project, Tag 0BAC](https://stacks.math.columbia.edu/tag/0BAC)
* [Stacks Project, Tag 0ACV](https://stacks.math.columbia.edu/tag/0ACV)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-! ### Topological preliminaries -/

/-- In a quasi-sober space, a subset containing every generic point of an irreducible component
is dense: the generic points are themselves dense. -/
private theorem dense_of_genericPoints_subset {α : Type*} [TopologicalSpace α] [QuasiSober α]
    {V : Set α} (h : genericPoints α ⊆ V) : Dense V := by
  refine dense_iff_closure_eq.2 (Set.univ_subset_iff.1 ?_)
  calc (Set.univ : Set α) = closure (genericPoints α) := (genericPoints.closure (α := α)).symm
    _ ⊆ closure V := closure_mono h

/-- An open embedding with dense range bijects the generic points of the irreducible components
of its source onto those of its target, as soon as the target has finitely many irreducible
components. -/
private theorem bijOn_genericPoints_of_isOpenEmbedding_of_denseRange
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {i : α → β}
    (hi : Topology.IsOpenEmbedding i) (hd : DenseRange i)
    (hfin : (irreducibleComponents β).Finite) :
    Set.BijOn i (genericPoints α) (genericPoints β) := by
  refine Set.BijOn.mk (fun x hx => hi.mem_genericPoints hx) hi.injective.injOn fun y hy => ?_
  obtain ⟨x, rfl⟩ := mem_of_mem_genericPoints_of_dense hi.isOpen_range hd hfin hy
  exact ⟨x, hi.mem_genericPoints_of_image hy, rfl⟩

/-- A homeomorphism bijects the generic points of the irreducible components of its source onto
those of its target. -/
private theorem bijOn_genericPoints_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) :
    Set.BijOn e (genericPoints α) (genericPoints β) :=
  Set.BijOn.mk (fun _ hx => e.mem_genericPoints hx) e.injective.injOn fun y hy =>
    ⟨e.symm y, (e.mem_genericPoints_iff (e.symm y)).1 (by rwa [e.apply_symm_apply]),
      e.apply_symm_apply y⟩

/-- The image of a dense subset under a continuous map with dense range is dense. -/
private theorem dense_image_of_denseRange {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {i : α → β} (hc : Continuous i) (hi : DenseRange i)
    {E : Set α} (hE : Dense E) : Dense (i '' E) := by
  refine dense_iff_inter_open.2 fun O hO hne => ?_
  obtain ⟨b, hbO, a, rfl⟩ := dense_iff_inter_open.1 hi O hO hne
  obtain ⟨c, hcO, hcE⟩ := dense_iff_inter_open.1 hE (i ⁻¹' O) (hO.preimage hc) ⟨a, hbO⟩
  exact ⟨i c, hcO, c, hcE, rfl⟩

/-! ### Point sets of charts -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- The map on points of an open immersion of presheaves is an open embedding: it is
continuous, injective because an open immersion is a monomorphism, and open. -/
private theorem isOpenEmbedding_pointsMap_of_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (hp : IsOpenImmersion B S hS p) :
    Topology.IsOpenEmbedding (pointsMap B S hS F p) :=
  have _ : Mono p := mono_of_presheaf_isOpenImmersion hp
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_pointsMap B S hS p) (pointsMap_injective_of_mono B S hS p)
    (isOpenMap_pointsMap_of_isOpenImmersion B S hS p hp)

/-- Precomposing with an isomorphism of presheaves does not change the image of the induced map
on points. -/
private theorem range_pointsMap_comp_of_isIso
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] (p : G ⟶ H) :
    Set.range (pointsMap B S hS F (e ≫ p)) = Set.range (pointsMap B S hS G p) := by
  have hsurj : Function.Surjective (pointsMap B S hS F e) := by
    intro z
    refine ⟨pointsMap B S hS G (inv e) z, ?_⟩
    have h := congrFun (pointsMap_comp B S hS (F := G) (inv e) e) z
    rw [IsIso.inv_hom_id, pointsMap_id] at h
    exact h.symm
  rw [pointsMap_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- The point set of the inverse image of a subfunctor is the inverse image of its point set.
One inclusion is the factorization of the inverse image through the subfunctor, the other is
the lifting of points through the cartesian square of Stacks 083Q. -/
private theorem range_pointsMap_preimage
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F' ⟶ F) (V : Subfunctor F) :
    Set.range (pointsMap B S hS (V.preimage p).toFunctor (V.preimage p).ι) =
      pointsMap B S hS F' p ⁻¹' Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨z, rfl⟩
    refine ⟨pointsMap B S hS (V.preimage p).toFunctor (V.fromPreimage p) z, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  · rintro x ⟨w, hw⟩
    obtain ⟨z, -, hz⟩ :=
      exists_points_of_isPullback B S hS (Subfunctor.isPullback_preimage p V) w x hw
    exact ⟨z, hz⟩

/-- Composing an open immersion of presheaves with the yoneda image of a morphism of the site
whose underlying morphism of schemes is an open immersion gives an open immersion. -/
private theorem isOpenImmersion_yoneda_map_comp {A A₀ : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : A ⟶ A₀)
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    {u : yoneda.obj A₀ ⟶ X} (hu : IsOpenImmersion B S hS u) :
    IsOpenImmersion B S hS (yoneda.map i ≫ u) :=
  isOpenImmersion_comp B S hS _ _
    (presheaf_yoneda_map_of_inverseImage B S hS inferInstance i hi) hu

/-- The scheme of a chart of a space with finitely many irreducible components has finitely many
irreducible components. -/
private theorem finite_irreducibleComponents_of_isOpenImmersion
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : BigFppfOver B S hS} {u : yoneda.obj A ⟶ X}
    (hu : IsOpenImmersion B S hS u)
    (hfin : (irreducibleComponents (points B S hS X)).Finite) :
    (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj A)).Finite :=
  finite_irreducibleComponents_of_isOpenEmbedding (schemePointsHomeomorph B S hS A).symm
    (schemePointsHomeomorph B S hS A).symm.isOpenEmbedding
    (finite_irreducibleComponents_of_isOpenEmbedding
      (pointsMap B S hS (yoneda.obj A) u)
      (isOpenEmbedding_pointsMap_of_isOpenImmersion B S hS u hu) hfin)

/-- The image of the points of a morphism of the site, read as a subset of the point space of
the source of the chart, is cut out by the image of the underlying morphism of schemes. -/
private theorem range_pointsMap_yoneda_map_eq {A₀ A : BigFppfOver B S hS} (i : A ⟶ A₀)
    (D : Set (points B S hS (yoneda.obj A₀)))
    (hD : Set.range ((BigFppfOver.toScheme B S hS).map i) =
      pointsToScheme B S hS A₀ '' D) :
    Set.range (pointsMap B S hS (yoneda.obj A) (yoneda.map i)) = D := by
  refine Set.image_injective.2 (injective_pointsToScheme B S hS A₀) ?_
  rw [← hD, ← Set.range_comp,
    ← (surjective_pointsToScheme B S hS A).range_comp ⇑((BigFppfOver.toScheme B S hS).map i)]
  exact congrArg Set.range (funext fun w => pointsToScheme_pointsMap_yoneda B S hS i w)

/-- An algebraic space with a representable open subspace whose point set is dense has an open
immersion from a represented presheaf with dense point set. -/
private theorem exists_isOpenImmersion_denseRange
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hdense : HasDenseRepresentableOpenSubspace B S hS X) :
    ∃ (A : BigFppfOver B S hS) (u : yoneda.obj A ⟶ X), IsOpenImmersion B S hS u ∧
      DenseRange (pointsMap B S hS (yoneda.obj A) u) := by
  obtain ⟨G, hGopen, hGrep, hGdense⟩ := hdense
  have _ : G.toFunctor.IsRepresentable := hGrep
  refine ⟨G.toFunctor.reprX, G.toFunctor.reprW.hom ≫ G.ι,
    MorphismProperty.RespectsIso.precomp _ G.toFunctor.reprW.hom G.ι hGopen.2, ?_⟩
  rw [DenseRange, range_pointsMap_comp_of_isIso B S hS G.toFunctor.reprW.hom G.ι]
  exact hGdense

/-! ### Birationality of a morphism of charts -/

section Charts

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X)
    (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))

/-- A morphism of charts of a birational morphism bijects the generic points of the irreducible
components of the two chart point spaces.

Each chart has a dense point set, so it bijects the generic points of its own point space onto
the generic points of the ambient space; the square of point maps then transports the bijection
of the birational morphism. -/
private theorem bijOn_genericPoints_pointsMap_of_charts
    {f : X ⟶ Y} (hbir : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    {A C : BigFppfOver B S hS}
    {u : yoneda.obj A ⟶ X} (hu : IsOpenImmersion B S hS u)
    {v : yoneda.obj C ⟶ Y} (hv : IsOpenImmersion B S hS v)
    (hudense : DenseRange (pointsMap B S hS (yoneda.obj A) u))
    (hvdense : DenseRange (pointsMap B S hS (yoneda.obj C) v))
    {g : A ⟶ C} (hcomm : yoneda.map g ≫ v = u ≫ f) :
    Set.BijOn (pointsMap B S hS (yoneda.obj A) (yoneda.map g))
      (genericPoints (points B S hS (yoneda.obj A)))
      (genericPoints (points B S hS (yoneda.obj C))) := by
  have hembu : Topology.IsOpenEmbedding (pointsMap B S hS (yoneda.obj A) u) :=
    isOpenEmbedding_pointsMap_of_isOpenImmersion B S hS u hu
  have hembv : Topology.IsOpenEmbedding (pointsMap B S hS (yoneda.obj C) v) :=
    isOpenEmbedding_pointsMap_of_isOpenImmersion B S hS v hv
  have hbiju := bijOn_genericPoints_of_isOpenEmbedding_of_denseRange hembu hudense hfiniteX
  have hbijv := bijOn_genericPoints_of_isOpenEmbedding_of_denseRange hembv hvdense hfiniteY
  have hbijf := hbir.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY
  have hsq : ∀ α, pointsMap B S hS (yoneda.obj C) v
      (pointsMap B S hS (yoneda.obj A) (yoneda.map g) α) =
      pointsMap B S hS X f (pointsMap B S hS (yoneda.obj A) u α) := by
    intro α
    have h : pointsMap B S hS (yoneda.obj A) (yoneda.map g ≫ v) =
        pointsMap B S hS (yoneda.obj A) (u ≫ f) := by rw [hcomm]
    rw [pointsMap_comp, pointsMap_comp] at h
    exact congrFun h α
  refine Set.BijOn.mk (fun α hα => ?_) (fun α hα α' hα' h => ?_) fun γ hγ => ?_
  · refine hembv.mem_genericPoints_of_image ?_
    rw [hsq α]
    exact hbijf.mapsTo (hbiju.mapsTo hα)
  · refine hembu.injective (hbijf.injOn (hbiju.mapsTo hα) (hbiju.mapsTo hα') ?_)
    rw [← hsq α, ← hsq α', h]
  · obtain ⟨ξ, hξ, hξc⟩ := hbijf.surjOn (hbijv.mapsTo hγ)
    obtain ⟨α, rfl⟩ : ξ ∈ Set.range (pointsMap B S hS (yoneda.obj A) u) :=
      mem_of_mem_genericPoints_of_dense hembu.isOpen_range hudense hfiniteX hξ
    refine ⟨α, hembu.mem_genericPoints_of_image hξ, hembv.injective ?_⟩
    rw [hsq α]
    exact hξc

/-- A morphism of charts of a birational morphism bijects the generic points of the irreducible
components of the two charts.

This is `AlgebraicGeometry.Space.bijOn_genericPoints_pointsMap_of_charts` read through the
comparison homeomorphisms `AlgebraicGeometry.Space.schemePointsHomeomorph` at both ends. -/
private theorem bijOn_genericPoints_toScheme_map_of_charts
    {f : X ⟶ Y} (hbir : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    {A C : BigFppfOver B S hS}
    {u : yoneda.obj A ⟶ X} (hu : IsOpenImmersion B S hS u)
    {v : yoneda.obj C ⟶ Y} (hv : IsOpenImmersion B S hS v)
    (hudense : DenseRange (pointsMap B S hS (yoneda.obj A) u))
    (hvdense : DenseRange (pointsMap B S hS (yoneda.obj C) v))
    {g : A ⟶ C} (hcomm : yoneda.map g ≫ v = u ≫ f) :
    Set.BijOn ((BigFppfOver.toScheme B S hS).map g)
      (genericPoints ((BigFppfOver.toScheme B S hS).obj A))
      (genericPoints ((BigFppfOver.toScheme B S hS).obj C)) := by
  have hcomp := (bijOn_genericPoints_homeomorph (schemePointsHomeomorph B S hS C)).comp
    ((bijOn_genericPoints_pointsMap_of_charts B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY
        hbir hu hv hudense hvdense hcomm).comp
      (bijOn_genericPoints_homeomorph (schemePointsHomeomorph B S hS A).symm))
  refine hcomp.congr fun a _ => ?_
  change pointsToScheme B S hS C (pointsMap B S hS (yoneda.obj A) (yoneda.map g)
    ((schemePointsHomeomorph B S hS A).symm a)) = _
  have hback : pointsToScheme B S hS A ((schemePointsHomeomorph B S hS A).symm a) = a :=
    (schemePointsHomeomorph B S hS A).apply_symm_apply a
  rw [pointsToScheme_pointsMap_yoneda B S hS g, hback]

/-- A morphism of charts of a birational morphism induces an isomorphism on the local ring at
each generic point of an irreducible component of its source.

The two charts are generic charts at the corresponding point of the ambient space, and
`AlgebraicGeometry.Space.exists_genericLocalRingMap` identifies the stalk map of the morphism of
charts with the local-ring map of the birational morphism there, up to the canonical
identifications of chart stalks. -/
private theorem isIso_stalkMap_toScheme_map_of_charts
    {f : X ⟶ Y} (hbir : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    {A C : BigFppfOver B S hS}
    {u : yoneda.obj A ⟶ X} (hu : IsOpenImmersion B S hS u)
    {v : yoneda.obj C ⟶ Y} (hv : IsOpenImmersion B S hS v)
    {g : A ⟶ C} (hcomm : yoneda.map g ≫ v = u ≫ f)
    (a : (BigFppfOver.toScheme B S hS).obj A)
    (ha : a ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj A)) :
    IsIso (((BigFppfOver.toScheme B S hS).map g).stalkMap a) := by
  let T := BigFppfOver.toScheme B S hS
  have hdenseX := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecentX
  have hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  let q := T.map g
  obtain ⟨pA, hpA⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS A a
  let α := pA.class B S hS (yoneda.obj A)
  have hαa : pointsToScheme B S hS A α = a := hpA
  have hembu : Topology.IsOpenEmbedding (pointsMap B S hS (yoneda.obj A) u) :=
    isOpenEmbedding_pointsMap_of_isOpenImmersion B S hS u hu
  have hαgen : α ∈ genericPoints (points B S hS (yoneda.obj A)) := by
    refine (Homeomorph.mem_genericPoints_iff (schemePointsHomeomorph B S hS A) α).1 ?_
    rw [schemePointsHomeomorph_apply, hαa]
    exact ha
  let x := pointsMap B S hS (yoneda.obj A) u α
  have hx : x ∈ genericPoints (points B S hS X) := hembu.mem_genericPoints hαgen
  have hy : pointsMap B S hS X f x ∈ genericPoints (points B S hS Y) :=
    (hbir.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY).mapsTo hx
  let c : GenericChart B S hS x :=
    { U := A, immersion := u, isOpen := hu, point := pA, mapsTo := rfl }
  let pC := FieldValuedPoint.map B S hS (yoneda.obj A) (yoneda.map g) pA
  let d : GenericChart B S hS (pointsMap B S hS X f x) :=
    { U := C
      immersion := v
      isOpen := hv
      point := pC
      mapsTo := by
        rw [show pC.class B S hS (yoneda.obj C) =
          pointsMap B S hS (yoneda.obj A) (yoneda.map g) α from rfl,
          ← pointsMap_comp_apply, hcomm, pointsMap_comp_apply] }
  have hpoint : q (schemePoint B S hS c.U c.point) = schemePoint B S hS d.U d.point :=
    (schemePoint_map_yoneda B S hS g pA).symm
  have hcommCharts : c.immersion ≫ f = yoneda.map g ≫ d.immersion := hcomm.symm
  let hgeneric := exists_genericLocalRingMap B S hS hX hY hdenseX hdenseY hfiniteX hfiniteY
    f x hx hy
  have hformula := hgeneric.choose_spec c d g hcommCharts hpoint
  have hIsoφ : IsIso hgeneric.choose :=
    hbir.isIso_genericLocalRingMap B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY x hx
  rw [hformula] at hIsoφ
  have _ := hIsoφ
  have _ : IsIso (eqToHom (congrArg
      (fun z => (T.obj d.U).presheaf.stalk z) hpoint.symm) ≫
      (q.stalkMap (schemePoint B S hS c.U c.point) ≫
      (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom)) := by
    simpa only [Category.assoc] using
      (IsIso.of_isIso_comp_left
        (chartStalkIso B S hS hY hdenseY hfiniteY _ hy d).inv _)
  have hIso2 : IsIso (q.stalkMap (schemePoint B S hS c.U c.point) ≫
      (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom) :=
    IsIso.of_isIso_comp_left (eqToHom (congrArg
      (fun z => (T.obj d.U).presheaf.stalk z) hpoint.symm)) _
  have hIso3 : IsIso (q.stalkMap (schemePoint B S hS c.U c.point)) :=
    IsIso.of_isIso_comp_right _ (chartStalkIso B S hS hX hdenseX hfiniteX x hx c).hom
  rw [show a = schemePoint B S hS c.U c.point from hpA.symm]
  exact hIso3

/-- **The scheme-level reduction.** A morphism of representable open charts with dense point
sets over a birational morphism of algebraic spaces is a birational morphism of schemes. -/
private theorem isBirational_toScheme_map_of_charts
    {f : X ⟶ Y} (hbir : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    {A C : BigFppfOver B S hS}
    {u : yoneda.obj A ⟶ X} (hu : IsOpenImmersion B S hS u)
    {v : yoneda.obj C ⟶ Y} (hv : IsOpenImmersion B S hS v)
    (hudense : DenseRange (pointsMap B S hS (yoneda.obj A) u))
    (hvdense : DenseRange (pointsMap B S hS (yoneda.obj C) v))
    {g : A ⟶ C} (hcomm : yoneda.map g ≫ v = u ≫ f) :
    _root_.AlgebraicGeometry.IsBirational ((BigFppfOver.toScheme B S hS).map g) :=
  ⟨bijOn_genericPoints_toScheme_map_of_charts B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY
      hbir hu hv hudense hvdense hcomm,
    fun a ha => isIso_stalkMap_toScheme_map_of_charts B S hS hX hY hdecentX hdecentY
      hfiniteX hfiniteY hbir hu hv hcomm a ha⟩

end Charts

/-! ### Stacks 0BBE -/

/-- **Stacks 0BBE.** A birational morphism of decent algebraic spaces over `S` with finitely
many irreducible components restricts to an isomorphism between dense open subspaces, provided
it is locally of finite type with reduced target or locally of finite presentation.

The source reduces the statement to schemes and quotes Stacks 0BAC there; the reduction is
carried out on representable open charts with dense point sets, see the module docstring. -/
@[stacks 0BBE]
theorem exists_dense_isOpenSubspace_isIso_of_isBirational
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hbir : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (hfin : (IsLocallyOfFiniteType B S hS f ∧
        HasEtaleLocalProperty B S hS Y
          (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z)) ∨
      IsLocallyOfFinitePresentation B S hS f) :
    ∃ (U : Subfunctor X) (V : Subfunctor Y) (ψ : U.toFunctor ⟶ V.toFunctor),
      IsOpenSubspace B S hS U ∧ IsOpenSubspace B S hS V ∧
        DenseRange (pointsMap B S hS U.toFunctor U.ι) ∧
        DenseRange (pointsMap B S hS V.toFunctor V.ι) ∧
        ψ ≫ V.ι = U.ι ≫ f ∧ IsIso ψ := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let hdenseX := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hX hdecentX
  let hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  have hsoberX := stacksSober_points_of_isDecentSpace B S hS hX hdecentX
  have _ : QuasiSober (points B S hS X) := (stacksSober_iff_t0_and_quasiSober.mp hsoberX).2
  -- The two dense representable open charts.
  obtain ⟨A₀, u₀, hu₀, hu₀dense⟩ := exists_isOpenImmersion_denseRange B S hS hdenseX
  obtain ⟨C, v, hv, hvdense⟩ := exists_isOpenImmersion_denseRange B S hS hdenseY
  have hbijf := hbir.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY
  let pu₀ := pointsMap B S hS (yoneda.obj A₀) u₀
  let pf := pointsMap B S hS X f
  have hRVopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj C) v)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS v hv
  -- Shrink the chart of `X` so that it maps into the chart of `Y`.
  let D : Set (points B S hS (yoneda.obj A₀)) :=
    (pf ∘ pu₀) ⁻¹' Set.range (pointsMap B S hS (yoneda.obj C) v)
  have hDopen : IsOpen D :=
    hRVopen.preimage ((continuous_pointsMap B S hS f).comp (continuous_pointsMap B S hS u₀))
  have hD'open : IsOpen (pointsToScheme B S hS A₀ '' D) :=
    (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS A₀ D).1 hDopen
  obtain ⟨A, i, hiOI, hirange, -⟩ :=
    exists_restrict_bigFppfOver A₀ ⟨pointsToScheme B S hS A₀ '' D, hD'open⟩
  let u : yoneda.obj A ⟶ X := yoneda.map i ≫ u₀
  have hu : IsOpenImmersion B S hS u := isOpenImmersion_yoneda_map_comp B S hS i hiOI hu₀
  have hirangeD : Set.range (pointsMap B S hS (yoneda.obj A) (yoneda.map i)) = D :=
    range_pointsMap_yoneda_map_eq B S hS i D hirange
  have hurange : Set.range (pointsMap B S hS (yoneda.obj A) u) = pu₀ '' D := by
    rw [show u = yoneda.map i ≫ u₀ from rfl, pointsMap_comp, Set.range_comp, hirangeD]
  -- The shrunken chart is still dense, because it contains every generic point.
  have hudense : DenseRange (pointsMap B S hS (yoneda.obj A) u) := by
    refine dense_of_genericPoints_subset fun ξ hξ => ?_
    have hξ1 : pf ξ ∈ Set.range (pointsMap B S hS (yoneda.obj C) v) :=
      mem_of_mem_genericPoints_of_dense hRVopen hvdense hfiniteY (hbijf.mapsTo hξ)
    have hξ2 : ξ ∈ Set.range pu₀ :=
      mem_of_mem_genericPoints_of_dense
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS u₀ hu₀) hu₀dense hfiniteX hξ
    obtain ⟨α, rfl⟩ := hξ2
    rw [hurange]
    exact ⟨α, hξ1, rfl⟩
  -- The factorization of `u ≫ f` through `v`, as a morphism of the site.
  have _ : Mono u := mono_of_presheaf_isOpenImmersion hu
  have _ : Mono v := mono_of_presheaf_isOpenImmersion hv
  have hU₁ : IsOpenSubspace B S hS (Subfunctor.range u) :=
    isOpenSubspace_range_of_isOpenImmersion A u hu
  have hV₁ : IsOpenSubspace B S hS (Subfunctor.range v) :=
    isOpenSubspace_range_of_isOpenImmersion C v hv
  have hle : Subfunctor.range u ≤ (Subfunctor.range v).preimage f := by
    refine le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_preimage B S hS f (Subfunctor.range v) hY hX hV₁) ?_
    rw [range_pointsMap_preimage B S hS f (Subfunctor.range v),
      range_pointsMap_ι_range B S hS u, range_pointsMap_ι_range B S hS v, hurange]
    rintro ξ ⟨w, hw, rfl⟩
    exact hw
  have hinvtv : inv (Subfunctor.toRange v) ≫ v = (Subfunctor.range v).ι :=
    calc inv (Subfunctor.toRange v) ≫ v
        = inv (Subfunctor.toRange v) ≫ Subfunctor.toRange v ≫ (Subfunctor.range v).ι :=
          congrArg (fun m => inv (Subfunctor.toRange v) ≫ m) (Subfunctor.toRange_ι v).symm
      _ = (Subfunctor.range v).ι := IsIso.inv_hom_id_assoc _ _
  let g : A ⟶ C := yoneda.preimage (Subfunctor.toRange u ≫ Subfunctor.homOfLe hle ≫
    (Subfunctor.range v).fromPreimage f ≫ inv (Subfunctor.toRange v))
  have hgγ : yoneda.map g = Subfunctor.toRange u ≫ Subfunctor.homOfLe hle ≫
      (Subfunctor.range v).fromPreimage f ≫ inv (Subfunctor.toRange v) :=
    yoneda.map_preimage _
  have hcomm : yoneda.map g ≫ v = u ≫ f := by
    rw [hgγ]
    calc (Subfunctor.toRange u ≫ Subfunctor.homOfLe hle ≫
          (Subfunctor.range v).fromPreimage f ≫ inv (Subfunctor.toRange v)) ≫ v
        = Subfunctor.toRange u ≫ Subfunctor.homOfLe hle ≫
            (Subfunctor.range v).fromPreimage f ≫ inv (Subfunctor.toRange v) ≫ v := by
          simp only [Category.assoc]
      _ = Subfunctor.toRange u ≫ Subfunctor.homOfLe hle ≫
            (Subfunctor.range v).fromPreimage f ≫ (Subfunctor.range v).ι := by rw [hinvtv]
      _ = Subfunctor.toRange u ≫ Subfunctor.homOfLe hle ≫
            ((Subfunctor.range v).preimage f).ι ≫ f := by
          rw [Subfunctor.fromPreimage_ι]
      _ = Subfunctor.toRange u ≫
            (Subfunctor.homOfLe hle ≫ ((Subfunctor.range v).preimage f).ι) ≫ f := by
          rw [Category.assoc]
      _ = Subfunctor.toRange u ≫ (Subfunctor.range u).ι ≫ f := by rw [Subfunctor.homOfLe_ι]
      _ = (Subfunctor.toRange u ≫ (Subfunctor.range u).ι) ≫ f := by rw [Category.assoc]
      _ = u ≫ f := by rw [Subfunctor.toRange_ι]
  -- The underlying morphism of schemes is birational between schemes with finitely many
  -- irreducible components.
  have hbirq : _root_.AlgebraicGeometry.IsBirational (T.map g) :=
    isBirational_toScheme_map_of_charts B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY
      hbir hu hv hudense hvdense hcomm
  have hfinA := finite_irreducibleComponents_of_isOpenImmersion B S hS hu hfiniteX
  have hfinC := finite_irreducibleComponents_of_isOpenImmersion B S hS hv hfiniteY
  have _ : Finite (irreducibleComponents (T.obj A)) := hfinA.to_subtype
  have _ : Finite (irreducibleComponents (T.obj C)) := hfinC.to_subtype
  -- The finiteness hypothesis transfers to the morphism of charts.
  have hetaleu : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf u :=
    presheaf_etale_of_isOpenImmersion B S hS hu
  have hetalev : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf v :=
    presheaf_etale_of_isOpenImmersion B S hS hv
  have hfinq : (_root_.AlgebraicGeometry.LocallyOfFiniteType (T.map g) ∧
      _root_.AlgebraicGeometry.IsReduced (T.obj C)) ∨
      _root_.AlgebraicGeometry.LocallyOfFinitePresentation (T.map g) := by
    rcases hfin with ⟨hft, hred⟩ | hfp
    · exact Or.inl ⟨hft A C u v g hetaleu hetalev hcomm,
        (exists_atlas_iff_forall_etale B S hS Y
          (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z) hY).mp hred C v hetalev⟩
    · exact Or.inr (hfp A C u v g hetaleu hetalev hcomm)
  -- Stacks 0BAC on the morphism of charts.
  obtain ⟨U', V', hU'V', hU'dense, hV'dense, hisoRes⟩ :=
    _root_.AlgebraicGeometry.exists_dense_opens_isIso_resLE_of_isBirational (T.map g) hbirq hfinq
  obtain ⟨A', iA, hiAOI, hiArange, -⟩ := exists_restrict_bigFppfOver A U'
  obtain ⟨C', iC, hiCOI, hiCrange, hiCuniv⟩ := exists_restrict_bigFppfOver C V'
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion (T.map iA) := hiAOI
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion (T.map iC) := hiCOI
  have hsub : Set.range (T.map (iA ≫ g)) ⊆ (V' : Set (T.obj C)) := by
    rintro z ⟨w, rfl⟩
    have hmemU : T.map iA w ∈ U' := by
      have hrange : T.map iA w ∈ Set.range (T.map iA) := ⟨w, rfl⟩
      rw [hiArange] at hrange
      exact hrange
    have hmemV := hU'V' hmemU
    change T.map (iA ≫ g) w ∈ (V' : Set (T.obj C))
    rw [T.map_comp]
    exact hmemV
  obtain ⟨g', hg'⟩ := hiCuniv (iA ≫ g) hsub
  -- The morphism of charts restricts to the isomorphism produced by Stacks 0BAC.
  let a : T.obj A' ≅ U'.toScheme :=
    _root_.AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq (T.map iA) U'.ι
      (by rw [hiArange, U'.range_ι])
  let b : T.obj C' ≅ V'.toScheme :=
    _root_.AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq (T.map iC) V'.ι
      (by rw [hiCrange, V'.range_ι])
  have hafac : a.hom ≫ U'.ι = T.map iA :=
    _root_.AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hbfac : b.hom ≫ V'.ι = T.map iC :=
    _root_.AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hfac : T.map g' ≫ b.hom = a.hom ≫ (T.map g).resLE V' U' hU'V' := by
    refine (cancel_mono V'.ι).1 ?_
    rw [Category.assoc, hbfac, ← T.map_comp, hg', T.map_comp, ← hafac, Category.assoc,
      Category.assoc, Scheme.Hom.resLE_comp_ι]
  have _ : IsIso ((T.map g).resLE V' U' hU'V') := hisoRes
  have _ : IsIso (T.map g' ≫ b.hom) := by rw [hfac]; infer_instance
  have _ : IsIso (T.map g') := IsIso.of_isIso_comp_right (T.map g') b.hom
  have hg'iso : IsIso g' := isIso_of_reflects_iso g' T
  -- Transport the two scheme opens back to open subspaces upstairs.
  let uA : yoneda.obj A' ⟶ X := yoneda.map iA ≫ u
  let vC : yoneda.obj C' ⟶ Y := yoneda.map iC ≫ v
  have huA : IsOpenImmersion B S hS uA :=
    isOpenImmersion_yoneda_map_comp B S hS iA hiAOI hu
  have hvC : IsOpenImmersion B S hS vC :=
    isOpenImmersion_yoneda_map_comp B S hS iC hiCOI hv
  have _ : Mono uA := mono_of_presheaf_isOpenImmersion huA
  have _ : Mono vC := mono_of_presheaf_isOpenImmersion hvC
  have hdenseChart : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (E E' : BigFppfOver B S hS)
      (w : yoneda.obj E ⟶ Z) (j : E' ⟶ E) (W : ((BigFppfOver.toScheme B S hS).obj E).Opens),
      Set.range (T.map j) = (W : Set _) → Dense (W : Set (T.obj E)) →
      DenseRange (pointsMap B S hS (yoneda.obj E) w) →
      DenseRange (pointsMap B S hS (yoneda.obj E') (yoneda.map j ≫ w)) := by
    intro Z E E' w j W hjrange hWdense hwdense
    have hD : Set.range (T.map j) = pointsToScheme B S hS E '' (pointsToScheme B S hS E ⁻¹' W) := by
      rw [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS E), hjrange]
    have hrange : Set.range (pointsMap B S hS (yoneda.obj E') (yoneda.map j)) =
        pointsToScheme B S hS E ⁻¹' W :=
      range_pointsMap_yoneda_map_eq B S hS j _ hD
    have hpre : Dense (pointsToScheme B S hS E ⁻¹' (W : Set (T.obj E))) :=
      hWdense.preimage (schemePointsHomeomorph B S hS E).isOpenMap
    rw [DenseRange, pointsMap_comp, Set.range_comp, hrange]
    exact dense_image_of_denseRange (continuous_pointsMap B S hS w) hwdense hpre
  refine ⟨Subfunctor.range uA, Subfunctor.range vC,
    inv (Subfunctor.toRange uA) ≫ yoneda.map g' ≫ Subfunctor.toRange vC,
    isOpenSubspace_range_of_isOpenImmersion A' uA huA,
    isOpenSubspace_range_of_isOpenImmersion C' vC hvC, ?_, ?_, ?_, ?_⟩
  · rw [DenseRange, range_pointsMap_ι_range B S hS uA]
    exact hdenseChart X A A' u iA U' hiArange hU'dense hudense
  · rw [DenseRange, range_pointsMap_ι_range B S hS vC]
    exact hdenseChart Y C C' v iC V' hiCrange hV'dense hvdense
  · have hg'comm : yoneda.map g' ≫ vC = uA ≫ f := by
      change yoneda.map g' ≫ yoneda.map iC ≫ v = (yoneda.map iA ≫ u) ≫ f
      rw [← Category.assoc, ← Functor.map_comp, hg', Functor.map_comp, Category.assoc, hcomm,
        ← Category.assoc]
    calc (inv (Subfunctor.toRange uA) ≫ yoneda.map g' ≫ Subfunctor.toRange vC) ≫
          (Subfunctor.range vC).ι
        = inv (Subfunctor.toRange uA) ≫ yoneda.map g' ≫
            Subfunctor.toRange vC ≫ (Subfunctor.range vC).ι := by
          simp only [Category.assoc]
      _ = inv (Subfunctor.toRange uA) ≫ yoneda.map g' ≫ vC := by rw [Subfunctor.toRange_ι]
      _ = inv (Subfunctor.toRange uA) ≫ uA ≫ f := by rw [hg'comm]
      _ = inv (Subfunctor.toRange uA) ≫
            (Subfunctor.toRange uA ≫ (Subfunctor.range uA).ι) ≫ f :=
          congrArg (fun m => inv (Subfunctor.toRange uA) ≫ m ≫ f)
            (Subfunctor.toRange_ι uA).symm
      _ = inv (Subfunctor.toRange uA) ≫ Subfunctor.toRange uA ≫
            (Subfunctor.range uA).ι ≫ f := by simp only [Category.assoc]
      _ = (Subfunctor.range uA).ι ≫ f := IsIso.inv_hom_id_assoc _ _
  · have _ : IsIso g' := hg'iso
    have _ : IsIso (yoneda.map g') := Functor.map_isIso yoneda g'
    infer_instance

end AlgebraicGeometry.Space

end
