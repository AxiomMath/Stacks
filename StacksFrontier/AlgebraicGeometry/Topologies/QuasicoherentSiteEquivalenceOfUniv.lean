module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.QuasicoherenceTransportOfUniv
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality

/-!
# Quasi-coherence is carried along an equivalence of ringed sites in independent universes

`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` says that a sheaf of modules is
quasi-coherent exactly when its reindexing along an equivalence of ringed sites is
quasi-coherent, for two sites in the *same* pair of universes.  A site and its equi-universe
model are not such a pair: the total Zariski site of a simplicial scheme has objects in `Type u`
and morphisms in `Type 0`, while
`AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite` has both in `Type u`, so the return
trip of the model route is not available.

This file restates the transport with the morphism universes of the two sites independent.  The
reindexing is `Stacks.SheafOfModules.reindexEquivalence`, the universe-separated
packaging of `Stacks.SheafOfModules.reindexEquivalence`, which is also what the equi-universe
model of a ringed site is built from.

## Main definitions

* `Stacks.SheafOfModules.SiteTransport.uliftForPresentationBalancedIso`: the comparison
  isomorphism of the presented module that
  `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_map_ofUniv` asks for, for a functor
  at the universe in which the global presentations of both sites live.
* `Stacks.SheafOfModules.SiteTransport.transportOverEquivalence`: the equivalence between the
  slice sites induced by an equivalence of sites.

## Main results

* `Stacks.SheafOfModules.SiteTransport.coversTop_inverse_obj` and
  `Stacks.SheafOfModules.SiteTransport.coversTop_functor_obj`: a family covering the final
  object is carried along an equivalence of sites in independent universes, in both directions.
* `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_transport` and
  `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_of_transport`: a global
  presentation, Stacks 03DE (6), is carried along the reindexing, and is reflected by it, for
  two sites in independent object and morphism universes.
* `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport` and
  `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_of_transport`: quasi-coherence is
  carried along the reindexing, and is reflected by it, for two sites with the same universe of
  objects and independent universes of morphisms.
* `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff`: **clause (6) of
  Stacks 03DL is invariant under an equivalence of ringed sites whose two sides have different
  morphism universes.**
* `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff'` and its two
  halves: the same for two sites in independent object *and* morphism universes.

## Implementation notes

Two universe obstructions stand between the library's statements and these.

The first is the universe in which a global presentation lives, which is `max u v w m` on a site
with objects in `Type u` and morphisms in `Type v`, over rings with sections in `Type w`, for a
module with sections in `Type m`.  It is dealt with by
`Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_map_ofUniv`, whose module universe is
balanced so that the two sides agree; see the implementation notes of that file.  Here the module
universe is balanced further, to `max u u' v v' w n`, which is the presentation universe itself:
then the functor at the module universe and the functor at the presentation universe are the
*same* functor, and the two universe lifts that the two statements of
`SheafOfModules.HasGlobalPresentation` apply to the presented module are both absorbed, by
`SheafOfModules.uliftForPresentationSelfIso'`.  That is
`Stacks.SheafOfModules.SiteTransport.uliftForPresentationBalancedIso`, and it is what the lift
amounts `max u v w` and `max u' v' w` — which are different universes once the sites are
separated, so that no single application of
`Stacks.SheafOfModules.SiteTransport.pushforwardUliftIso_ofUniv` relates them — are handled with.

The balancing propagates to the slice sites, whose objects lie in `Type (max u v)` and
`Type (max u' v')` and whose morphisms stay in `Type v` and `Type v'`, since
`max (max u v) (max u' v') v v' w n = max u u' v v' w n`.  So the presentation layer needs no
relation between the four universes at all.

The second obstruction is the index type of `SheafOfModules.IsQuasicoherentOnSite`, which is
`Type (max u v)` on one side and `Type (max u' v')` on the other: a covering family produced on
one site is not even a candidate on the other.  What removes it is
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation`, which tests
quasi-coherence against a family covering the final object — `Sieve.ofObjects` depends only on
the *source* of an arrow, so such a family is indexed by a type in `Type u`, the universe of the
objects alone.  That is why the quasi-coherence statements ask the two sites to share their
universe of objects while leaving their morphism universes free, which is exactly the shape of a
site and its equi-universe model.  Transporting the covering family is then
`Stacks.SheafOfModules.SiteTransport.coversTop_inverse_obj` and its companion, the equivalence
case of `Stacks.CategoryTheory.coversTop_map_of_forall_exists_hom`, proved here so that this file
does not depend on the simplicial development.

Universe arguments are given explicitly at every application of the transport lemmas.  The
constraints that arise are of the form `max u u' v v' w ?n = max u u' v v' w n`, which the
elaborator does not solve on its own; a missing explicit argument shows up as `stuck at solving
universe constraint`, not as a mathematical error.

Nothing here carries a `stacks` attribute, for the reasons recorded in
`StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentSiteEquivalence.lean`: tag 03DM is the
single assertion that all eight clauses of Stacks 03DL are intrinsic, and one clause is not a
covering set for it; and the equivalence of ringed topoi is presented here by an equivalence of
the underlying *sites*, which is less general than the special cocontinuous functor of the
source.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.SiteTransport

universe u v u' v' w n

/-! ### Transport of a family covering the final object along an equivalence of sites -/

section CoversTop

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

/-- A continuous functor with an arrow from every object into its image carries a family covering
the final object to one. -/
private theorem coversTop_obj_of_forall_exists_hom {D : Type u} [Category.{v} D]
    {D' : Type u'} [Category.{v'} D'] {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
    (G : D ⥤ D') [G.IsContinuous K K'] (hG : ∀ A : D', ∃ T : D, Nonempty (A ⟶ G.obj T))
    {I : Type*} {W : I → D} (hW : K.CoversTop W) : K'.CoversTop fun i ↦ G.obj (W i) := by
  intro A
  obtain ⟨T, ⟨f⟩⟩ := hG A
  refine K'.superset_covering ?_ (K'.pullback_stable f
    ((CoverPreserving.of_isContinuous G K K').cover_preserve (hW T)))
  rintro B k ⟨Z, p, q, ⟨i, ⟨b⟩⟩, -⟩
  exact ⟨i, ⟨q ≫ G.map b⟩⟩

/-- **A family covering the final object is carried along the inverse of an equivalence of
sites.**  This is the equivalence case of
`Stacks.CategoryTheory.coversTop_map_of_forall_exists_hom`: at an object `A` of the target site
the arrow into the image of `e.inverse` is the unit of the equivalence. -/
theorem coversTop_inverse_obj (e : C' ≌ C) [e.inverse.IsContinuous J J']
    {I : Type*} {W : I → C} (hW : J.CoversTop W) :
    J'.CoversTop fun i ↦ e.inverse.obj (W i) :=
  coversTop_obj_of_forall_exists_hom e.inverse (fun A ↦ ⟨_, ⟨e.unit.app A⟩⟩) hW

/-- **A family covering the final object is carried along an equivalence of sites.**  The
companion of `Stacks.SheafOfModules.SiteTransport.coversTop_inverse_obj`, with the inverse of the
counit in place of the unit. -/
theorem coversTop_functor_obj (e : C' ≌ C) [e.functor.IsContinuous J' J]
    {I : Type*} {W : I → C'} (hW : J'.CoversTop W) :
    J.CoversTop fun i ↦ e.functor.obj (W i) :=
  coversTop_obj_of_forall_exists_hom e.functor (fun A ↦ ⟨_, ⟨e.counitInv.app A⟩⟩) hW

end CoversTop

/-! ### Transport of a global presentation -/

/-- The comparison isomorphism of the presented module that
`Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_map_ofUniv` asks for, for a functor
between the categories of sheaves of modules at the universe in which the global presentations
of both sites live.  There the module universe and the presentation universe coincide, so the
lift by `max a b r` on the source side and the lift by `max a' b' r` on the target side — two
different universes, which is why `pushforwardUliftIso_ofUniv` cannot relate them — are both
absorbed by `SheafOfModules.uliftForPresentationSelfIso'`. -/
noncomputable def uliftForPresentationBalancedIso.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {C' : Type a'} [Category.{b'} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{r}}
    (F : SheafOfModules.{max a a' b b' r m} R ⥤ SheafOfModules.{max a a' b b' r m} R')
    (M : SheafOfModules.{max a a' b b' r m} R) :
    F.obj (SheafOfModules.uliftForPresentation.{a, b, r,
        max a a' b b' r m, max a b r} M) ≅
      SheafOfModules.uliftForPresentation.{a', b', r,
        max a a' b b' r m, max a' b' r} (F.obj M) :=
  F.mapIso (SheafOfModules.uliftForPresentationSelfIso'.{a, b, r,
      max a a' b b' r m, max a b r} M) ≪≫
    (SheafOfModules.uliftForPresentationSelfIso'.{a', b', r,
      max a a' b b' r m, max a' b' r} (F.obj M)).symm

/-- **Reindexing along an equivalence of sites in independent universes carries global
presentations to global presentations.**  This is
`Stacks.SheafOfModules.hasGlobalPresentation_reindex` with the two sites in independent object
and morphism universes, at the balanced module universe that makes the two presentation
universes agree. -/
theorem hasGlobalPresentation_transport.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {C' : Type a'} [Category.{b'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{max a a' b b' r m} R)
    (h : M.HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{max a a' b b' r m}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).HasGlobalPresentation := by
  let φ : Stacks.SheafOfModules.reindexRing J' e R ⟶
      (e.functor.sheafPushforwardContinuous RingCat.{r} J' J).obj R := 𝟙 _
  let eHi : SheafOfModules.{max a a' b b' r m} R ≌
      SheafOfModules.{max a a' b b' r m} (Stacks.SheafOfModules.reindexRing J' e R) :=
    Stacks.SheafOfModules.reindexEquivalence e R
  let F := eHi.functor
  let : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : (SheafOfModules.pushforward.{r} φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.reindexRing J' e R) := Iso.refl _
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{a, b, r, r,
      max a a' b b' r m} (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{a', b', r, r, max a a' b b' r m}
        (SheafOfModules.unit (Stacks.SheafOfModules.reindexRing J' e R)) :=
    pushforwardUliftIso_ofUniv.{a, b, a', b', r, r, max a a' b b' r m} φ
        (SheafOfModules.unit R) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{a', b', r, r, max a a' b b' r m} hU
  exact hasGlobalPresentation_map_ofUniv.{a, b, a', b', r, max r m} M (F₀ := F) (F := F)
    hη₁ (uliftForPresentationBalancedIso.{a, b, a', b', r, m} F M) h

/-- **Reindexing along an equivalence of sites in independent universes reflects global
presentations.**  This is `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex` with the two
sites in independent object and morphism universes: the inverse of
`Stacks.SheafOfModules.reindexEquivalence` carries the presentation back, and its
unit isomorphism identifies the round trip with the identity. -/
theorem hasGlobalPresentation_of_transport.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {C' : Type a'} [Category.{b'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{max a a' b b' r m} R)
    (h : ((SheafOfModules.pushforward.{max a a' b b' r m}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).HasGlobalPresentation) :
    M.HasGlobalPresentation := by
  let S := Stacks.SheafOfModules.reindexRing J' e R
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{r} J J').obj S :=
    Stacks.SheafOfModules.reindexBackSharp e R
  let eHi : SheafOfModules.{max a a' b b' r m} R ≌
      SheafOfModules.{max a a' b b' r m} S := Stacks.SheafOfModules.reindexEquivalence e R
  let F := eHi.inverse
  let : F.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : (SheafOfModules.pushforward.{r} ψ).obj (SheafOfModules.unit S) ≅
      SheafOfModules.unit R :=
    ((Stacks.SheafOfModules.reindexEquivalence e R).unitIso.app (SheafOfModules.unit R)).symm
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{a', b', r, r,
      max a a' b b' r m} (SheafOfModules.unit S)) ≅
      SheafOfModules.uliftForPresentation.{a, b, r, r, max a a' b b' r m}
        (SheafOfModules.unit R) :=
    pushforwardUliftIso_ofUniv.{a', b', a, b, r, r, max a a' b b' r m} ψ
        (SheafOfModules.unit S) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{a, b, r, r, max a a' b b' r m} hU
  have h' := hasGlobalPresentation_map_ofUniv.{a', b', a, b, r, max r m}
    ((SheafOfModules.pushforward.{max a a' b b' r m} (𝟙 S)).obj M) (F₀ := F) (F := F) hη₁
    (uliftForPresentationBalancedIso.{a', b', a, b, r, m} F
      ((SheafOfModules.pushforward.{max a a' b b' r m} (𝟙 S)).obj M)) h
  exact SheafOfModules.HasGlobalPresentation.of_iso (eHi.unitIso.app M).symm h'

/-! ### The slice sites -/

section SliceSite

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsDenseSubsite J J']

/-- The equivalence of slice sites induced by an equivalence of sites, with the two sites in
independent universes.  That it is an equivalence of *sites* is
`Stacks.SheafOfModules.SiteTransport.overPostTransport_isDenseSubsite`, Stacks 03CH (2) for an
equivalence. -/
noncomputable abbrev transportOverEquivalence (V : C') : Over V ≌ Over (e.functor.obj V) :=
  (Over.post (X := V) e.functor).asEquivalence

/-- The inverse of `transportOverEquivalence e V` is a dense subsite functor from the slice
site `J.over (e.functor.obj V)` to the slice site `J'.over V`. -/
instance transportOverEquivalence_inverse_isDenseSubsite (V : C') :
    (transportOverEquivalence e V).inverse.IsDenseSubsite
      (J.over (e.functor.obj V)) (J'.over V) :=
  let : ((transportOverEquivalence e V).symm).inverse.IsDenseSubsite (J'.over V)
      (J.over (e.functor.obj V)) :=
    inferInstanceAs ((Over.post (X := V) e.functor).IsDenseSubsite _ _)
  inferInstanceAs (((transportOverEquivalence e V).symm).functor.IsDenseSubsite _ _)

end SliceSite

/-- The restriction to an object `V` of the reindexing of a sheaf of modules is the reindexing,
along the localized equivalence of sites, of the restriction to `e.functor.obj V`.  This is an
equality because `CategoryTheory.Over.post_forget_eq_forget_comp` is one. -/
theorem over_transport_eq.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {C' : Type a'} [Category.{b'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsDenseSubsite J J']
    (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{max a a' b b' r m} R) (V : C') :
    ((SheafOfModules.pushforward.{max a a' b b' r m}
        (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).over V =
      (SheafOfModules.pushforward.{max a a' b b' r m}
        (𝟙 (Stacks.SheafOfModules.reindexRing (J'.over V) (transportOverEquivalence e V)
          (R.over (e.functor.obj V))))).obj (M.over (e.functor.obj V)) := rfl

/-- Reindexing carries a global presentation of the restriction to `e.functor.obj V` to one of
the restriction of the reindexing to `V`.  The slice sites have objects in `Type (max a b)` and
`Type (max a' b')` and keep their morphisms, which leaves the balanced module universe
`max a a' b b' r m` unchanged. -/
theorem hasGlobalPresentation_over_transport.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {C' : Type a'} [Category.{b'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsDenseSubsite J J']
    (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{max a a' b b' r m} R) (V : C')
    (h : (M.over (e.functor.obj V)).HasGlobalPresentation) :
    (((SheafOfModules.pushforward.{max a a' b b' r m}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).over V).HasGlobalPresentation := by
  rw [over_transport_eq.{a, b, a', b', r, m} e R M V]
  exact hasGlobalPresentation_transport.{max a b, b, max a' b', b', r, m}
    (transportOverEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

/-- Reindexing reflects a global presentation of the restriction to `V`: it comes from one of the
restriction to `e.functor.obj V`. -/
theorem hasGlobalPresentation_of_over_transport.{a, b, a', b', r, m}
    {C : Type a} [Category.{b} C] {C' : Type a'} [Category.{b'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsDenseSubsite J J']
    (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{max a a' b b' r m} R) (V : C')
    (h : (((SheafOfModules.pushforward.{max a a' b b' r m}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).over V).HasGlobalPresentation) :
    (M.over (e.functor.obj V)).HasGlobalPresentation := by
  rw [over_transport_eq.{a, b, a', b', r, m} e R M V] at h
  exact hasGlobalPresentation_of_transport.{max a b, b, max a' b', b', r, m}
    (transportOverEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

/-! ### Quasi-coherence, with the object and morphism universes of the two sites independent -/

section QuasicoherentOfUniv

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsDenseSubsite J J']
  (R : Sheaf J RingCat.{w})

/-- **Quasi-coherence is carried along an equivalence of ringed sites whose two sides have
different object and morphism universes.**  This is
`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport` with the object universes of
the two sites independent as well.

The covering family is indexed by a type in the universe of the objects of the *source* site; it
is transported by `Stacks.SheafOfModules.SiteTransport.coversTop_inverse_obj`, whose index type
is free, and the transported family is accepted on the target site because the index universe of
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation'` is free as
well — a sieve generated by a family of objects depends only on the sources of its arrows. -/
theorem isQuasicoherentOnSite_transport' (M : SheafOfModules.{max u u' v v' w n} R)
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{max u u' v v' w n}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).IsQuasicoherentOnSite := by
  obtain ⟨I, W, hW, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation M).mp hM
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation' _
    (W := fun i ↦ e.inverse.obj (W i)) (coversTop_inverse_obj e hW) fun i ↦ ?_
  exact hasGlobalPresentation_over_transport.{u, v, u', v', w, n} e R M (e.inverse.obj (W i))
    (Stacks.SheafOfModules.hasGlobalPresentation_overMap M
      (e.counitIso.app (W i)).hom (hP i))

/-- **Quasi-coherence is reflected by an equivalence of ringed sites whose two sides have
different object and morphism universes.**  This is
`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_of_transport` with the object
universes of the two sites independent as well. -/
theorem isQuasicoherentOnSite_of_transport' (M : SheafOfModules.{max u u' v v' w n} R)
    (hN : ((SheafOfModules.pushforward.{max u u' v v' w n}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  obtain ⟨I, V, hV, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation _).mp hN
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation' M
    (W := fun i ↦ e.functor.obj (V i)) (coversTop_functor_obj e hV) fun i ↦ ?_
  exact hasGlobalPresentation_of_over_transport.{u, v, u', v', w, n} e R M (V i) (hP i)

/-- **Clause (6) of Stacks 03DL is invariant under an equivalence of ringed sites whose two
sides have different object and morphism universes.**  A sheaf of modules is quasi-coherent
exactly when its reindexing along the equivalence, over the transported sheaf of rings, is
quasi-coherent.

This is `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff` with all four
universes of the two sites independent, which is the shape a site and its equi-universe model
have when the objects of the site do not already lie in the universe of the sections of its
structure sheaf. -/
theorem isQuasicoherentOnSite_transport_iff' (M : SheafOfModules.{max u u' v v' w n} R) :
    ((SheafOfModules.pushforward.{max u u' v v' w n}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  ⟨isQuasicoherentOnSite_of_transport'.{u, v, u', v', w, n} e R M,
    isQuasicoherentOnSite_transport'.{u, v, u', v', w, n} e R M⟩

end QuasicoherentOfUniv

/-! ### Quasi-coherence, for two sites sharing their object universe

These are the cases `u' = u` of the statements above. -/

section Quasicoherent

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v'} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsDenseSubsite J J']
  (R : Sheaf J RingCat.{w})

/-- **Quasi-coherence is carried along an equivalence of ringed sites whose two sides have
different morphism universes.**  This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex`
with the morphism universes of the two sites independent.

Quasi-coherence is tested against a family covering the final object, by
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation`, so the
covering family is indexed by a type in the universe of the objects, which the two sites share;
the family is transported by `Stacks.SheafOfModules.SiteTransport.coversTop_inverse_obj` and the
presentations by `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_over_transport`. -/
theorem isQuasicoherentOnSite_transport (M : SheafOfModules.{max u v v' w n} R)
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{max u v v' w n}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_transport'.{u, v, u, v', w, n} e R M hM

/-- **Quasi-coherence is reflected by an equivalence of ringed sites whose two sides have
different morphism universes.**  This is
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex` with the morphism universes of the two
sites independent, which is what the return trip of the equi-universe model of a ringed site
needs. -/
theorem isQuasicoherentOnSite_of_transport (M : SheafOfModules.{max u v v' w n} R)
    (hN : ((SheafOfModules.pushforward.{max u v v' w n}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_transport'.{u, v, u, v', w, n} e R M hN

/-- **Clause (6) of Stacks 03DL is invariant under an equivalence of ringed sites whose two
sides have different morphism universes.**  A sheaf of modules is quasi-coherent exactly when its
reindexing along the equivalence, over the transported sheaf of rings, is quasi-coherent.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` with the morphism universes of
the two sites independent. -/
theorem isQuasicoherentOnSite_transport_iff (M : SheafOfModules.{max u v v' w n} R) :
    ((SheafOfModules.pushforward.{max u v v' w n}
      (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_transport_iff'.{u, v, u, v', w, n} e R M

end Quasicoherent

end Stacks.SheafOfModules.SiteTransport

end
