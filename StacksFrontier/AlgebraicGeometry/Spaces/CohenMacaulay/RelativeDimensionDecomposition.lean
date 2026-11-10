module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The relative-dimension decomposition of a Cohen–Macaulay morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
presentation and Cohen–Macaulay. Then `X` is the disjoint union of open-and-closed subspaces
`Xd d`, indexed by `d : ℕ`, on which `f` has constant relative dimension `d`.

## Main results

* `AlgebraicGeometry.Space.exists_clopen_relativeDimension_decomposition`: **Stacks 0E11**. The
  disjoint, exhaustive family of open-and-closed subspaces of constant relative dimension.

## Implementation notes

The decomposition is transported from the scheme-level one of Tag 02NM along a surjective étale
chart. Choose a surjective étale atlas `q` of `Y` and lift it through `f` to a surjective étale
chart `p` of `X` over a morphism `α` of the site (Tag 02X1). The scheme morphism `g` underlying
`α` is flat (Tag 03MM) and locally of finite presentation (Tag 03XP) because `f` is, and its
fibres are Cohen–Macaulay schemes: Cohen–Macaulayness of `f` at a point is Cohen–Macaulayness of
the local ring of the fibre of a pointed étale chart there (Tags 0E0V, 0E0U), the canonical
pointed chart at a scheme point of the chart is `α` itself, and a locally Noetherian scheme all
of whose local rings are Cohen–Macaulay is a Cohen–Macaulay scheme (Tag 02IP). So Tag 02NM
produces the clopen pieces of `g`, and the `d`-th piece of `X` is the image on points of the
`d`-th piece of the chart.

That image is a clopen subset of the point space `|X|` of Tag 03BU: it is open because an étale
chart is open on points (Tag 03BX), and it is closed because the images of the other pieces cover
its complement, disjointness being the uniqueness of the relative dimension at a point. The
subspace it cuts out is `AlgebraicGeometry.Space.openSubspaceOfPoints` of Tag 03BZ, which is both
an open and a closed subspace because its point set is clopen.

The pieces are subfunctors of `X` whose *point images* cover `|X|` and are pairwise disjoint,
rather than subfunctors whose pointwise supremum is `X`: the ranges of the inclusions are
subpresheaves, not subsheaves, so a section over a test object which the decomposition splits
into several pieces lies in no single piece before refinement. Point coverage is the form in
which the source states the conclusion `X = ⨿ X_d`.

The relative dimension of the restriction `(Xd d).ι ≫ f` is read off at a point by extending a
pointed étale chart of the restriction to one of `f`: precomposing the source chart with the open
immersion `(Xd d).ι` keeps it étale and does not change the induced morphism of charts.

## References

* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 0E11](https://stacks.math.columbia.edu/tag/0E11)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Function

universe u

namespace AlgebraicGeometry

/-- The fibres of a morphism locally of finite presentation are locally Noetherian: a fibre is
of finite type over the residue field of its image point. -/
private theorem isLocallyNoetherian_fiber_of_finitePresentation {X Z : Scheme.{u}}
    (g : X ⟶ Z) [LocallyOfFinitePresentation g] (y : Z) : IsLocallyNoetherian (g.fiber y) := by
  have : LocallyOfFiniteType (g.fiberToSpecResidueField y) := by
    change LocallyOfFiniteType (pullback.snd g (Z.fromSpecResidueField y))
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField y)

/-- The germ-level Cohen–Macaulay fibre condition at a point of the source, read as a condition
on the stalk of the set-theoretic fibre over a prescribed image point. -/
private theorem exists_isCohenMacaulayLocalRing_stalk_fiber {X Z : Scheme.{u}} (g : X ⟶ Z)
    {x : X} {y : Z} (hxy : g x = y) (z : g.fiber y) (hz : g.fiberι y z = x)
    (h : HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom g x)) :
    ∃ hN : IsNoetherianRing ((g.fiber y).presheaf.stalk z),
      @IsCohenMacaulayLocalRing ((g.fiber y).presheaf.stalk z) _ hN _ := by
  subst hxy
  obtain rfl : z = g.asFiber x :=
    (g.fiberι (g x)).isEmbedding.injective (hz.trans (Scheme.Hom.fiberι_asFiber g x).symm)
  exact (hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff g x).mp h

/-- On the `d`-th canonical relative-dimension piece of Tag 02NM the fibre has local dimension
`d`: the restriction of the morphism to that piece has relative dimension `d`. -/
private theorem topologicalKrullDimAt_fiber_eq_of_mem_relativeDimensionOpen {X Z : Scheme.{u}}
    (g : X ⟶ Z) [Flat g] [LocallyOfFinitePresentation g]
    (hCM : ∀ y : Z, IsCohenMacaulay (g.fiber y)) (d : ℕ) (x : X)
    (hx : x ∈ relativeDimensionOpen g hCM d) :
    topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) = (d : WithBot ℕ∞) :=
  topologicalKrullDimAt_fiber_eq_of_relativeDimension g (relativeDimensionOpen g hCM d) d
    (relativeDimensionOpen_relativeDimension g hCM d) x hx

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- A relative open immersion of presheaves on the big fppf site of `S` is étale after every
represented base change, because an open immersion of schemes is étale. -/
private theorem presheaf_etale_of_presheaf_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : F ⟶ G} (hi : IsOpenImmersion B S hS i) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i := by
  have hle : (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) := fun _ _ m hm =>
    have := hm
    inferInstance
  exact MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hle) _ hi

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A member of an open cover by pairwise disjoint open sets is closed: its complement is the
union of the other members. -/
private theorem isClosed_of_isOpen_of_pairwise_disjoint {ι α : Type*} [TopologicalSpace α]
    {W : ι → Set α} (ho : ∀ i, IsOpen (W i)) (hc : ∀ x, ∃ i, x ∈ W i)
    (hd : Pairwise (Disjoint on W)) (i : ι) : IsClosed (W i) := by
  have hEq : (W i)ᶜ = ⋃ j : {j : ι // j ≠ i}, W j := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    refine ⟨fun hx => ?_, ?_⟩
    · obtain ⟨j, hj⟩ := hc x
      exact ⟨⟨j, fun h => hx (h ▸ hj)⟩, hj⟩
    · rintro ⟨⟨j, hji⟩, hj⟩ hxi
      exact (Set.disjoint_left.mp (hd hji)) hj hxi
  rw [← isOpen_compl_iff, hEq]
  exact isOpen_iUnion fun j => ho j

/-- The restriction of `f` to a subfunctor with étale inclusion has relative dimension `d` once
`f` has relative dimension `d` at the image of every point of the subfunctor: a pointed étale
chart of the restriction extends to one of `f` by precomposing with the inclusion. -/
private theorem hasRelativeDimension_ι_comp {Z : Subfunctor X} (f : X ⟶ Y)
    (hZ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf Z.ι) (d : ℕ)
    (h : ∀ x, HasRelativeDimensionAt (d : ℕ∞) B S hS f (pointsMap B S hS Z.toFunctor Z.ι x)) :
    HasRelativeDimension d B S hS (Z.ι ≫ f) := by
  have := isMultiplicative_presheaf_etale B S hS
  intro x c
  exact h x
    { U := c.U, V := c.V, a := c.a ≫ Z.ι, b := c.b, h := c.h
      a_etale := MorphismProperty.comp_mem _ c.a _ c.a_etale hZ
      b_etale := c.b_etale
      comm := by simpa only [Category.assoc] using c.comm
      representative := c.representative, point := c.point
      maps_to := by rw [pointsMap_comp_apply, c.maps_to] }

/-- The pointed étale chart of `f` given by a commuting square of étale charts, with a
field-valued representative `t` of a point of the source chart as its representative. -/
private noncomputable def etaleChartOfRepresentative (f : X ⟶ Y)
    {U V : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (hp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hcomm : yoneda.map α ≫ q = p ≫ f) (t : FieldValuedPoint B S hS (yoneda.obj U)) :
    EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) p (t.class B S hS (yoneda.obj U))) :=
  { U := U, V := V, a := p, b := q, h := α, a_etale := hp, b_etale := hq, comm := hcomm
    representative := t, point := IsLocalRing.closedPoint t.carrier, maps_to := rfl }

/-- **The chart of a Cohen–Macaulay morphism has Cohen–Macaulay fibres.** In a commuting square
of étale charts of a Cohen–Macaulay morphism of algebraic spaces whose induced morphism of
charts is locally of finite presentation, every fibre of that morphism of schemes is a
Cohen–Macaulay scheme.

The fibres are locally Noetherian, so by Tag 02IP it suffices that every local ring of a fibre
is Cohen–Macaulay. A point of a fibre is a point of the chart, which carries the canonical
pointed étale chart whose field-valued representative is the residue field there; the
Cohen–Macaulay condition on `f` at the corresponding point of the algebraic space is exactly
Cohen–Macaulayness of that local ring. -/
private theorem isCohenMacaulay_fiber_chartMap (f : X ⟶ Y) (hCM : IsCohenMacaulay B S hS f)
    {U V : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (hp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hcomm : yoneda.map α ≫ q = p ≫ f)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α)]
    (y : (BigFppfOver.toScheme B S hS).obj V) :
    _root_.AlgebraicGeometry.IsCohenMacaulay
      (((BigFppfOver.toScheme B S hS).map α).fiber y) := by
  set g := (BigFppfOver.toScheme B S hS).map α
  have htfae := (isCohenMacaulay_tfae_stalk (g.fiber y)).out 2 1
    (a := IsLocallyNoetherian (g.fiber y) ∧ ∀ z : g.fiber y,
      ∃ h : IsNoetherianRing ((g.fiber y).presheaf.stalk z),
        @IsCohenMacaulayLocalRing ((g.fiber y).presheaf.stalk z) _ h _)
    (b := _root_.AlgebraicGeometry.IsCohenMacaulay (g.fiber y))
    (h₁ := by simp) (h₂ := by simp)
  refine htfae.mp ⟨isLocallyNoetherian_fiber_of_finitePresentation g y, fun z => ?_⟩
  set x := g.fiberι y z
  have hxy : g x = y := (g.range_fiberι y).le ⟨z, rfl⟩
  set t := schemePointRepresentative B S hS U x
  let c := etaleChartOfRepresentative B S hS f p q α hp hq hcomm t
  have hcpoint : c.sourcePoint B S hS = x := schemePointRepresentative_point B S hS U x
  exact exists_isCohenMacaulayLocalRing_stalk_fiber g (by rwa [hcpoint]) z hcpoint.symm
    ((hCM _).2 c)

/-- **Reading the relative dimension off a canonical piece of the chart.** If a point of an
étale chart of the source lands in the `d`-th canonical relative-dimension piece of the induced
morphism of charts, then the morphism of algebraic spaces has relative dimension `d` at the point
of the source it maps to.

The chart, with a field-valued representative of that point as its representative, is a pointed
étale chart there, and on it the germ-level fibre-dimension property of Tag 04NL is the local
dimension of the set-theoretic fibre, which the piece prescribes. -/
private theorem hasRelativeDimensionAt_of_mem_relativeDimensionOpen (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {U V : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (hp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hcomm : yoneda.map α ≫ q = p ≫ f)
    [Flat ((BigFppfOver.toScheme B S hS).map α)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α)]
    (hfib : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      _root_.AlgebraicGeometry.IsCohenMacaulay
        (((BigFppfOver.toScheme B S hS).map α).fiber y))
    (d : ℕ) (w : points B S hS (yoneda.obj U))
    (hw : pointsToScheme B S hS U w ∈
      relativeDimensionOpen ((BigFppfOver.toScheme B S hS).map α) hfib d) :
    HasRelativeDimensionAt (d : ℕ∞) B S hS f (pointsMap B S hS (yoneda.obj U) p w) := by
  obtain ⟨t, rfl⟩ := Quot.exists_rep w
  let c := etaleChartOfRepresentative B S hS f p q α hp hq hcomm t
  refine (holdsOnEveryEtaleChartAtPoint_iff_some B S hS
    (@_root_.AlgebraicGeometry.HasFiberDimensionAt.{u} (d : ℕ∞))
    (_root_.AlgebraicGeometry.fiberDimensionAt_isEtaleLocalOnSourceAndTarget (d : ℕ∞))
    hX hY f _).mpr ⟨c, ?_⟩
  exact (_root_.AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mpr
    (topologicalKrullDimAt_fiber_eq_of_mem_relativeDimensionOpen _ hfib d _ hw)

/-- **The relative dimension at a point is unique.** Two natural numbers which are both the
relative dimension of a morphism of algebraic spaces at a point are equal: on one pointed étale
chart at the point both are the local dimension of the same fibre. -/
private theorem eq_of_hasRelativeDimensionAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X) {d e : ℕ}
    (hd : HasRelativeDimensionAt (d : ℕ∞) B S hS f x)
    (he : HasRelativeDimensionAt (e : ℕ∞) B S hS f x) : d = e := by
  obtain ⟨c, hc⟩ := (holdsOnEveryEtaleChartAtPoint_iff_some B S hS
    (@_root_.AlgebraicGeometry.HasFiberDimensionAt.{u} (e : ℕ∞))
    (_root_.AlgebraicGeometry.fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞))
    hX hY f x).mp he
  exact_mod_cast ((_root_.AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp
    (hd c)).symm.trans ((_root_.AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp hc)

/-- **Stacks 0E11.** A locally finitely presented Cohen–Macaulay morphism of algebraic spaces
over `S` decomposes its source into open-and-closed subspaces of constant relative dimension:
there is a family `Xd : ℕ → Subfunctor X` of subfunctors which are both open and closed
subspaces of `X` in the sense of Tag 02YU, whose point sets cover the point space of `X` and are
pairwise disjoint, and such that the restriction of `f` to the `d`-th piece has relative
dimension `d`.

The pieces are given by their point sets rather than by a supremum of subfunctors: the ranges of
their inclusions are subpresheaves, so a section over a test object which the decomposition
splits into several pieces lies in no single piece before refinement. -/
@[stacks 0E11]
theorem exists_clopen_relativeDimension_decomposition (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hfp : IsLocallyOfFinitePresentation B S hS f) (hCM : IsCohenMacaulay B S hS f) :
    ∃ Xd : ℕ → Subfunctor X,
      (∀ d : ℕ, IsOpenSubspace B S hS (Xd d) ∧ IsClosedSubspace B S hS (Xd d)) ∧
      (∀ x : points B S hS X, ∃ d : ℕ,
        x ∈ Set.range (pointsMap B S hS (Xd d).toFunctor (Xd d).ι)) ∧
      Pairwise (Disjoint on fun d : ℕ =>
        Set.range (pointsMap B S hS (Xd d).toFunctor (Xd d).ι)) ∧
      (∀ d : ℕ, HasRelativeDimension d B S hS ((Xd d).ι ≫ f)) := by
  classical
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hqSurj hqEtale
  have : Flat ((BigFppfOver.toScheme B S hS).map α) :=
    (isFlat_iff_forall_isFlatAt B S hS f).mpr (fun x => (hCM x).1) U V p q α hpEtale hqEtale
      hcomm.symm
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α) :=
    hfp U V p q α hpEtale hqEtale hcomm.symm
  have hfib := isCohenMacaulay_fiber_chartMap B S hS f hCM p q α hpEtale hqEtale hcomm.symm
  -- The `d`-th piece of the point space of `X`: the image under the chart's map on points of
  -- the `d`-th canonical relative-dimension piece of the chart.
  set W : ℕ → Set (points B S hS X) := fun d =>
    pointsMap B S hS (yoneda.obj U) p ''
      (pointsToScheme B S hS U ⁻¹'
        (relativeDimensionOpen ((BigFppfOver.toScheme B S hS).map α) hfib d :
          Set ((BigFppfOver.toScheme B S hS).obj U)))
  have hWopen : ∀ d : ℕ, IsOpen (W d) := fun d => by
    refine isOpenMap_pointsMap_of_presheafEtale B S hS p hpEtale _ ?_
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image,
      Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)]
    exact (relativeDimensionOpen ((BigFppfOver.toScheme B S hS).map α) hfib d).isOpen
  have hWcover : ∀ x : points B S hS X, ∃ d : ℕ, x ∈ W d := fun x => by
    obtain ⟨w, rfl⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hpSurj x
    obtain ⟨d, hd⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show pointsToScheme B S hS U w ∈
          (⨆ d : ℕ, relativeDimensionOpen ((BigFppfOver.toScheme B S hS).map α) hfib d :
            ((BigFppfOver.toScheme B S hS).obj U).Opens) by
        rw [iSup_relativeDimensionOpen]
        trivial)
    exact ⟨d, w, hd, rfl⟩
  have hrel := hasRelativeDimensionAt_of_mem_relativeDimensionOpen B S hS f hX hY p q α hpEtale
    hqEtale hcomm.symm hfib
  have hWdisj : Pairwise (Disjoint on W) := fun i j hij => Set.disjoint_left.mpr
    fun x ⟨wi, hwi, hxi⟩ ⟨wj, hwj, hxj⟩ => hij (eq_of_hasRelativeDimensionAt B S hS hX hY f x
      (hxi ▸ hrel i wi hwi) (hxj ▸ hrel j wj hwj))
  refine ⟨fun d => openSubspaceOfPoints B S hS X (W d), fun d => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact isOpenSubspace_openSubspaceOfPoints B S hS hX (W d) (hWopen d)
  · exact isClosedSubspace_openSubspaceOfPoints B S hS hX (W d) (hWopen d)
      (isClosed_of_isOpen_of_pairwise_disjoint hWopen hWcover hWdisj d)
  · exact fun x => (hWcover x).imp fun d hd => by
      rwa [range_pointsMap_ι_openSubspaceOfPoints B S hS (W d)]
  · intro i j hij
    simpa only [Function.onFun, range_pointsMap_ι_openSubspaceOfPoints] using hWdisj hij
  · intro d
    refine hasRelativeDimension_ι_comp B S hS f (presheaf_etale_of_presheaf_isOpenImmersion B S hS
      (presheaf_isOpenImmersion_ι_openSubspaceOfPoints B S hS (W d) (hWopen d))) d fun x => ?_
    obtain ⟨w, hw, hwx⟩ := (range_pointsMap_ι_openSubspaceOfPoints B S hS (W d)).subset ⟨x, rfl⟩
    exact hwx ▸ hrel d w hw

end Space

end AlgebraicGeometry

end
