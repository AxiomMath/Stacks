module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatOfRepresentableFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Monomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Monomorphisms of formal algebraic spaces tested on a flat cover

Let `S` be a scheme contained in a big fppf site `B`. Condition (6) of **Stacks 0GHV** tests
monomorphy of a morphism `f : X ⟶ Y` of formal algebraic spaces over `S` against a single
morphism `Z ⟶ Y` of formal algebraic spaces which is representable by algebraic spaces,
surjective, flat and locally of finite presentation: `f` is a monomorphism exactly when such a
`Z ⟶ Y` exists with `X ×_Y Z ⟶ Z` a monomorphism.

## Main definitions

* `AlgebraicGeometry.Space.IsLocallyOfFinitePresentationULift`: being locally of finite
  presentation for a morphism of algebraic spaces over `S` with values in a larger universe,
  as the condition on every commuting square of étale scheme charts.
* `AlgebraicGeometry.FormalSpace.HasMonoFlatCover`: condition (6) of **Stacks 0GHV**.

## Main results

* `AlgebraicGeometry.Space.singleton_mem_bigFppf_topology_of_flat`: a surjective, flat,
  locally finitely presented morphism of a big fppf site generates a covering sieve.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_of_surjective_flat`: a morphism of fppf
  sheaves which is representable by algebraic spaces, surjective, flat and locally of finite
  presentation is a surjection of sheaves.
* `AlgebraicGeometry.FormalSpace.mono_tfae_flatCover`: **Stacks 0GHV** for its condition (6),
  together with conditions (1), (2), (3), (4) and (5).

## Implementation notes

Condition (6) asks for `Z ⟶ Y` to be surjective, flat and locally of finite presentation *as a
morphism representable by algebraic spaces*, which is the condition of Stacks 03XZ:
`AlgebraicGeometry.Space.HasPropertyULift` at the property in question, tested on the base
change along every scheme-valued point of `Y`. Surjectivity of a morphism of algebraic spaces
is surjectivity of the induced map on points (Stacks 03ME), so the property used for it is
`AlgebraicGeometry.Space.IsSurjectiveULift`, as in
`AlgebraicGeometry.FormalSpace.IsSurjective`; flatness and local finite presentation are
étale-chart conditions (Stacks 03ML), so the properties used for them are
`AlgebraicGeometry.Space.IsFlatULift` and
`AlgebraicGeometry.Space.IsLocallyOfFinitePresentationULift`.

The source states the conclusion of its condition (6) for `X ×_Y Z ⟶ X`. That is the first
projection, which is not the one the other conditions use and which no condition on `Z ⟶ Y`
can control: taking `Z = Y` and `Z ⟶ Y` the identity, the first projection is `f` itself, so
the condition so read is condition (1) with four properties of a cover attached. It is read
here, as in the rest of the source's list, as the second projection `X ×_Y Z ⟶ Z`.

The implication from condition (6) to condition (1) is the one with content: it needs the cover
`Z ⟶ Y` to be a surjection of sheaves, after which condition (5) applies with the one-member
family `{Z ⟶ Y}`. That is
`AlgebraicGeometry.FormalSpace.isLocallySurjective_of_surjective_flat`, and it is proved by
exhibiting, over a scheme-valued point `T ⟶ Y` of the target, a single fppf covering of `T`
along which the point lifts to `Z`. The base change `W = Z ×_Y T` is an algebraic space over
`S` with values in `Type (u + 1)`, hence the universe lift of an algebraic space `F` in the
value universe of the site
(`AlgebraicGeometry.Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift`); the projection
`W ⟶ T` is the universe lift of a morphism `a : F ⟶ T`, which inherits surjectivity on points,
flatness and local finite presentation because all three conditions are unchanged by the
universe lift. An étale scheme atlas `U ⟶ F` of `F`, surjective after every representable base
change, then gives a morphism `U ⟶ T` of the site which is surjective on points — hence
surjective as a morphism of schemes by Stacks 03H5 — and whose underlying morphism of schemes
is flat and locally of finite presentation, read off the chart condition at the pair of charts
`U ⟶ F` and `T ⟶ T`. A single surjective flat locally finitely presented morphism of the site
generates a covering sieve, and the point lifts to `Z` over `U` through the atlas and the
second projection.

The implication from condition (1) to condition (6) takes `Z = Y` and `Z ⟶ Y` the identity. Its
base change along a scheme-valued point `T ⟶ Y` is the identity of `T` up to isomorphism, so it
is an algebraic space, surjective on points, and flat and locally of finite presentation by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_uliftYoneda_map`, the identity of a scheme
being flat and locally of finite presentation.

## References

* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0GHV](https://stacks.math.columbia.edu/tag/0GHV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Local finite presentation in a larger value universe -/

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe `max w u`
independent of the universe `u` of the schemes is *locally of finite presentation* when the
morphism of schemes underlying every commuting square of étale scheme charts of it is locally
of finite presentation. This is `AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift` with local
finite presentation in place of local finite type. -/
abbrev IsLocallyOfFinitePresentationULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (f : F ⟶ G) : Prop :=
  HoldsOnEveryEtaleChartULift.{w} B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) f

/-- The universe lift of a morphism of presheaves of `Type u` is locally of finite presentation
in the larger value universe exactly when the morphism is locally of finite presentation. -/
theorem isLocallyOfFinitePresentationULift_whiskerRight_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    IsLocallyOfFinitePresentationULift.{w} B S hS
        (Functor.whiskerRight f uliftFunctor.{w}) ↔
      HoldsOnEveryEtaleChart B S hS
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) f :=
  holdsOnEveryEtaleChartULift_whiskerRight_iff B S hS _ f

/-! ### A single flat cover generates a covering sieve -/

attribute [local instance] schemeCutoff_hasPullbacks

/-- A morphism of a big fppf site which is surjective, flat and locally of finite presentation
generates a covering sieve: a one-member fppf covering. This is
`AlgebraicGeometry.Space.singleton_mem_bigFppf_topology` with flatness and local finite
presentation in place of étaleness. -/
theorem singleton_mem_bigFppf_topology_of_flat
    {X Y : B.Schemes} (g : Y ⟶ X) (hs : Surjective (B.inclusion.map g))
    (hflat : Flat (B.inclusion.map g))
    (hfp : LocallyOfFinitePresentation (B.inclusion.map g)) :
    Sieve.generate (Presieve.singleton g) ∈ B.topology X := by
  let E : Covering B.Schemes := ⟨X, PreZeroHypercover.singleton g⟩
  have hE : _root_.AlgebraicGeometry.IsFppfCovering E := by
    change (PreZeroHypercover.singleton g).presieve₀.map B.inclusion ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X)
    rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton,
      Scheme.fppfPrecoverage_eq_inf]
    let : Surjective (B.inclusion.map g) := hs
    exact ⟨(Scheme.singleton_mem_precoverage_iff
        (@Flat.{u} : MorphismProperty Scheme.{u}) (B.inclusion.map g)).2
        ⟨Scheme.Hom.surjective _, hflat⟩,
      (Scheme.singleton_mem_precoverage_iff
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
        (B.inclusion.map g)).2 ⟨Scheme.Hom.surjective _, hfp⟩⟩
  obtain ⟨E', hE', hEquiv⟩ := B.fppf_has_representative E hE
  have hpre : E.2.presieve₀ ∈ B.precoverage X := by
    obtain ⟨hX, hComb⟩ := hEquiv
    cases hX
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  simpa [E, PreZeroHypercover.presieve₀_singleton] using
    Precoverage.generate_mem_toGrothendieck hpre

/-! ### Surjectivity on points in the two value universes -/

/-- An isomorphism of presheaves on the big fppf site of `S` is surjective on points. -/
theorem surjective_pointsMapULift_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ⟶ G) [IsIso e] :
    Function.Surjective (pointsMapULift.{w} B S hS F e) := by
  intro p
  refine ⟨pointsMapULift.{w} B S hS G (inv e) p, ?_⟩
  have h : pointsMapULift.{w} B S hS G (inv e ≫ e) p = p := by
    rw [IsIso.inv_hom_id, pointsMapULift_id]
    rfl
  rwa [pointsMapULift_comp, Function.comp_apply] at h

/-- The universe lift of a morphism of presheaves of `Type u` is surjective on points exactly
when the morphism is. -/
theorem isSurjectiveULift_whiskerRight_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    IsSurjectiveULift.{w} B S hS (Functor.whiskerRight a uliftFunctor.{w}) ↔
      IsSurjective B S hS a := by
  have h : ∀ x, pointsMapULift.{w} B S hS (F ⋙ uliftFunctor.{w})
        (Functor.whiskerRight a uliftFunctor.{w}) (pointsULiftEquiv.{w} B S hS F x) =
      pointsULiftEquiv.{w} B S hS G (pointsMap B S hS F a x) :=
    fun x ↦ congrFun (pointsMapULift_whiskerRight_pointsULiftEquiv.{w} B S hS a) x
  constructor
  · intro hsurj y
    obtain ⟨x, hx⟩ := hsurj (pointsULiftEquiv.{w} B S hS G y)
    obtain ⟨x₀, rfl⟩ := (pointsULiftEquiv.{w} B S hS F).surjective x
    exact ⟨x₀, (pointsULiftEquiv.{w} B S hS G).injective ((h x₀).symm.trans hx)⟩
  · intro hsurj y
    obtain ⟨y₀, rfl⟩ := (pointsULiftEquiv.{w} B S hS G).surjective y
    obtain ⟨x₀, rfl⟩ := hsurj y₀
    exact ⟨pointsULiftEquiv.{w} B S hS F x₀, h x₀⟩

/-- A morphism of the big fppf site of `S` which is surjective on the points of the presheaves
its source and target represent is surjective as a morphism of schemes. This is the converse of
`AlgebraicGeometry.Space.isSurjective_yoneda_map`, by Stacks 03H5. -/
theorem surjective_of_isSurjective_yoneda_map {U V : BigFppfOver B S hS} (k : U ⟶ V)
    (hk : IsSurjective B S hS (yoneda.map k)) :
    AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map k) := by
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).mp
    ((surjective_yonedaMap_iff_surjective_pointsMap B S hS k).mpr hk)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A representable surjective flat cover is a surjection of sheaves -/

/-- **Stacks 05VM for a representable surjective flat cover.** A morphism of presheaves on the
big fppf site of `S` which is representable by algebraic spaces and which is surjective, flat
and locally of finite presentation in the sense of Stacks 03XZ is locally surjective, that is a
surjection of fppf sheaves.

Over a scheme-valued point `T ⟶ Y` of the target the base change is an algebraic space over
`S`, hence the universe lift of an algebraic space in the value universe of the site; an étale
scheme atlas of the latter provides a morphism `U ⟶ T` of the site which is surjective, flat
and locally of finite presentation, and the point lifts over it. A single such morphism
generates a covering sieve. -/
theorem isLocallySurjective_of_surjective_flat
    {Z G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (c : Z ⟶ G)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c)
    (hsurj : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsSurjectiveULift.{u + 1} B S hS g.hom) c hrep)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsFlatULift.{u + 1} B S hS g.hom) c hrep)
    (hfp : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsLocallyOfFinitePresentationULift.{u + 1} B S hS g.hom) c hrep) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c := by
  constructor
  intro T y
  set ξ : (uliftYoneda.{u + 1}).obj T ⟶ G := uliftYonedaEquiv.symm y with hξ
  have hW : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ c) := hrep T ξ
  obtain ⟨F, ⟨e⟩⟩ := Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hW
  have hF : IsAlgebraicSpace B S hS F :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS e.symm hW)
  obtain ⟨a, ha⟩ : ∃ a : F ⟶ yoneda.obj T,
      Functor.whiskerRight a uliftFunctor.{u + 1} = e.hom ≫ pullback.fst ξ c :=
    ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}).map_surjective _
  -- The three conditions on the cover, transported to the value universe of the site.
  have hasurj : Space.IsSurjective B S hS a := by
    refine (Space.isSurjectiveULift_whiskerRight_iff B S hS a).mp ?_
    have h : Function.Surjective (Space.pointsMapULift.{u + 1} B S hS
        (F ⋙ uliftFunctor.{u + 1}) (e.hom ≫ pullback.fst ξ c)) := by
      rw [Space.pointsMapULift_comp]
      exact (hsurj T ξ).comp (Space.surjective_pointsMapULift_of_isIso B S hS e.hom)
    rw [ha]
    exact h
  have hchart : ∀ P : MorphismProperty Scheme.{u},
      Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P (pullback.fst ξ c) →
        Space.HoldsOnEveryEtaleChart B S hS P a := fun P h ↦ by
    refine (Space.holdsOnEveryEtaleChartULift_whiskerRight_iff B S hS _ a).mp ?_
    rw [ha]
    exact Space.holdsOnEveryEtaleChartULift_precomp B S hS _ e.hom _ h
  have haflat := hchart _ (hflat T ξ)
  have hafp := hchart _ (hfp T ξ)
  -- An étale atlas of the base change gives a flat cover of `T` by a scheme of the site.
  obtain ⟨U, α, hαs, hαe⟩ := hF.exists_atlas
  set k : U ⟶ T := yoneda.preimage (α ≫ a) with hkdef
  have hk : yoneda.map k = α ≫ a := yoneda.map_preimage _
  have hid : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T)) := by
    simpa using (Space.presheaf_yoneda_map_etale_iff B S hS (𝟙 T)).2 inferInstance
  have hsq : yoneda.map k ≫ 𝟙 (yoneda.obj T) = α ≫ a := by rw [Category.comp_id, hk]
  have hkflat : Flat ((BigFppfOver.toScheme B S hS).map k) :=
    haflat U T α (𝟙 (yoneda.obj T)) k hαe hid hsq
  have hkfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k) :=
    hafp U T α (𝟙 (yoneda.obj T)) k hαe hid hsq
  have hksurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map k) := by
    refine Space.surjective_of_isSurjective_yoneda_map B S hS k ?_
    rw [hk]
    intro p
    obtain ⟨q, hq⟩ := hasurj p
    obtain ⟨r, hr⟩ := Space.surjective_pointsMap_of_presheaf_surjective B S hS α hαs q
    refine ⟨r, ?_⟩
    rw [Space.pointsMap_comp, Function.comp_apply, hr, hq]
  -- The covering sieve, and the lift of the point over it.
  have hbase := Space.singleton_mem_bigFppf_topology_of_flat B k.left hksurj hkflat hkfp
  have hcover : Sieve.generate (Presieve.singleton k) ∈ BigFppfOver.topology B S hS T := by
    change Sieve.generate (Presieve.singleton k) ∈ B.topology.over (B.obj hS) T
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact hbase
  apply (BigFppfOver.topology B S hS).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨⟩
  have hcomp : Functor.whiskerRight (α ≫ a) uliftFunctor.{u + 1} =
      Functor.whiskerRight α uliftFunctor.{u + 1} ≫
        Functor.whiskerRight a uliftFunctor.{u + 1} :=
    ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
      (Type (u + 1))).obj uliftFunctor.{u + 1}).map_comp α a
  have ha' : Functor.whiskerRight α uliftFunctor.{u + 1} ≫
      Functor.whiskerRight a uliftFunctor.{u + 1} = (uliftYoneda.{u + 1}).map k :=
    hcomp.symm.trans
      (congrArg (fun m ↦ Functor.whiskerRight m uliftFunctor.{u + 1}) hk.symm)
  obtain ⟨β, hβ⟩ : ∃ β : (uliftYoneda.{u + 1}).obj U ⟶ pullback ξ c,
      β ≫ pullback.fst ξ c = (uliftYoneda.{u + 1}).map k :=
    ⟨Functor.whiskerRight α uliftFunctor.{u + 1} ≫ e.hom,
      (Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ Functor.whiskerRight α uliftFunctor.{u + 1} ≫ m) ha.symm).trans
          ha')⟩
  refine ⟨uliftYonedaEquiv (β ≫ pullback.snd ξ c), ?_⟩
  have key : (β ≫ pullback.snd ξ c) ≫ c = (uliftYoneda.{u + 1}).map k ≫ ξ := by
    rw [← hβ, Category.assoc, Category.assoc, pullback.condition]
  have h2 : uliftYonedaEquiv ((uliftYoneda.{u + 1}).map k ≫ ξ) = G.map k.op y := by
    have hn := uliftYonedaEquiv_naturality ξ k.op
    simpa only [hξ, Quiver.Hom.unop_op, Equiv.apply_symm_apply] using hn.symm
  exact (uliftYonedaEquiv_comp _ _).symm.trans (by rw [key]; exact h2)

/-! ### Condition (6) of Stacks 0GHV -/

/-- An isomorphism onto a representable presheaf satisfies an étale-local property of scheme
morphisms which holds on identities on every étale chart. -/
private theorem holdsOnEveryEtaleChartULift_of_isIso {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) (hid : ∀ X : Scheme.{u}, P (𝟙 X))
    {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ⟶ (uliftYoneda.{u + 1}).obj U) [IsIso e] :
    Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P e := by
  have h0 := Space.holdsOnEveryEtaleChartULift_uliftYoneda_map B S hS hP (𝟙 U)
    (by rw [CategoryTheory.Functor.map_id]; exact hid _)
  have h1 := Space.holdsOnEveryEtaleChartULift_precomp B S hS P e
    ((uliftYoneda.{u + 1}).map (𝟙 U)) h0
  rwa [CategoryTheory.Functor.map_id, Category.comp_id] at h1

/-- **Stacks 0GHV, condition (6).** There is a morphism onto the target of a morphism of fppf
sheaves on the big fppf site of `S` whose source is a formal algebraic space over `S` and which
is representable by algebraic spaces, surjective, flat and locally of finite presentation, and
along which the base change of the morphism is a monomorphism.

The three properties of the cover are the conditions of Stacks 03XZ: surjectivity on points of
the base change along every scheme-valued point of the target, and flatness and local finite
presentation of every étale chart of such a base change. -/
abbrev HasMonoFlatCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (Z : FppfSheaf B S hS) (c : Z ⟶ Y), IsFormalAlgebraicSpace B S hS Z ∧
    ∃ hc : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsSurjectiveULift.{u + 1} B S hS g.hom) c.hom hc ∧
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsFlatULift.{u + 1} B S hS g.hom) c.hom hc ∧
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsLocallyOfFinitePresentationULift.{u + 1} B S hS g.hom) c.hom hc ∧
      ∀ (W : FppfSheaf B S hS) (p : W ⟶ Z) (q : W ⟶ X), IsPullback p q c f → Mono p

/-- **Stacks 0GHV, condition (6) implies condition (5).** A flat cover as in condition (6) is a
one-member family whose induced map from the coproduct is a surjection of sheaves, each of whose
base changes of the morphism is a monomorphism. -/
theorem hasMonoLocallySurjectiveFamily_of_hasMonoFlatCover {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : HasMonoFlatCover B S hS f) : HasMonoLocallySurjectiveFamily B S hS f := by
  obtain ⟨Z, c, -, hc, hsurj, hflat, hfp, hmono⟩ := h
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c.hom :=
    isLocallySurjective_of_surjective_flat B S hS c.hom hc hsurj hflat hfp
  refine ⟨PUnit.{u + 2}, fun _ ↦ Z, fun _ ↦ c, ?_, fun _ ↦ hmono⟩
  have hfac : (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit).hom ≫
      (Sigma.desc (fun _ : PUnit.{u + 2} ↦ c)).hom = c.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_comp_desc]
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac

/-- **Stacks 0GHV, condition (1) implies condition (6).** The identity of the target is a flat
cover of it as in condition (6): it is representable by algebraic spaces because its base
change along a scheme-valued point is that point, and for the same reason it is surjective on
points and its étale charts are flat and locally of finite presentation. -/
theorem hasMonoFlatCover_of_mono {X Y : FppfSheaf B S hS}
    (hY : IsFormalAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : Mono f) :
    HasMonoFlatCover B S hS f := by
  have hpb : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      IsPullback (𝟙 ((uliftYoneda.{u + 1}).obj U)) ξ ξ (𝟙 Y.obj) :=
    fun U ξ ↦ IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hiso : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      IsIso (pullback.fst ξ (𝟙 Y.obj)) := by
    intro U ξ
    let : IsIso ((hpb U ξ).isoPullback.hom ≫ pullback.fst ξ (𝟙 Y.obj)) := by
      rw [(hpb U ξ).isoPullback_hom_fst]
      infer_instance
    exact IsIso.of_isIso_comp_left (hpb U ξ).isoPullback.hom _
  have hc : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (𝟙 Y.obj) := fun U ξ ↦
    Space.isAlgebraicSpaceULift_of_iso B S hS (hpb U ξ).isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)
  refine ⟨Y, 𝟙 Y, hY, hc, ?_, ?_, ?_, fun _ _ _ sq ↦ Mono.of_isPullback B S hS sq hf⟩
  · intro U ξ
    let := hiso U ξ
    exact Space.surjective_pointsMapULift_of_isIso B S hS (pullback.fst ξ (𝟙 Y.obj))
  · exact fun U ξ ↦ have := hiso U ξ
      holdsOnEveryEtaleChartULift_of_isIso B S hS Flat.isEtaleLocalOnSourceAndTarget
        (fun _ ↦ inferInstance) (pullback.fst ξ (𝟙 Y.obj))
  · exact fun U ξ ↦ have := hiso U ξ
      holdsOnEveryEtaleChartULift_of_isIso B S hS
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
        (fun _ ↦ inferInstance) (pullback.fst ξ (𝟙 Y.obj))

/-- **Stacks 0GHV**, its condition (6) together with the conditions (1), (2), (3), (4) and (5).
For a morphism `f : X ⟶ Y` of formal algebraic spaces over `S`, with `Y` a formal algebraic
space, the following are equivalent:

1. `f` is a monomorphism;
2. for every scheme `T` over `S` in the site and every `T ⟶ Y` the projection
   `X ×_Y T ⟶ T` is a monomorphism;
3. the same for every affine scheme `T` over `S` in the site;
4. there is a covering `{Y_j ⟶ Y}` as in Definition 0AIM such that each `X ×_Y Y_j ⟶ Y_j` is a
   monomorphism;
5. there is a family `{Y_j ⟶ Y}` with `∐ Y_j ⟶ Y` a surjection of sheaves such that each
   `X ×_Y Y_j ⟶ Y_j` is a monomorphism;
6. there is a morphism `Z ⟶ Y` of formal algebraic spaces over `S` which is representable by
   algebraic spaces, surjective, flat and locally of finite presentation such that
   `X ×_Y Z ⟶ Z` is a monomorphism.

The equivalence of the first five conditions is
`AlgebraicGeometry.FormalSpace.mono_tfae`; condition (6) is absorbed into it by the identity of
`Y`, which is such a cover, and by the fact that such a cover is a surjection of sheaves. -/
@[stacks 0GHV "condition (6), and its equivalence with the conditions (1), (2), (3), (4) \
and (5)"]
theorem mono_tfae_flatCover {X Y : FppfSheaf B S hS} (hY : IsFormalAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [Mono f,
        IsMonoOnSchemeBaseChanges B S hS f,
        IsMonoOnAffineBaseChanges B S hS f,
        HasMonoFormalAtlas B S hS f,
        HasMonoLocallySurjectiveFamily B S hS f,
        HasMonoFlatCover B S hS f] := by
  have h := mono_tfae B S hS hY f
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 1 ↔ 3 := h.out 1 3
  tfae_have 1 ↔ 4 := h.out 1 4
  tfae_have 1 ↔ 5 := h.out 1 5
  tfae_have 1 → 6 := fun hf ↦ hasMonoFlatCover_of_mono B S hS hY hf
  tfae_have 6 → 1 := fun h6 ↦ mono_of_hasMonoLocallySurjectiveFamily B S hS
    (hasMonoLocallySurjectiveFamily_of_hasMonoFlatCover B S hS h6)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
