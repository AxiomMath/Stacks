module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceOfUniv

/-!
# Quasi-coherence along an equivalence of sites in independent universes

Let `e : C' ≌ C` be an equivalence of sites, with `C` in `Type u` with morphisms in `Type v` and
`C'` in `Type u'` with morphisms in `Type v'`, and let `R` be a sheaf of rings on `C`. A sheaf of
`R`-modules `M` with sections in `Type w` has a global presentation exactly when its reindexing
along `e` does, and the same holds for quasi-coherence.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_reindex_ofUniv`: reindexing along `e` carries
  global presentations to global presentations.
* `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex_ofUniv`: reindexing along `e` reflects
  global presentations.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv`: a sheaf of modules is
  quasi-coherent if and only if its reindexing along `e` is quasi-coherent.

## Implementation notes

A global presentation of a module with sections in `Type w` on a site with objects in `Type u`
and morphisms in `Type v` is indexed by types in `Type (max u v w)`. The module is lifted to the
universe `max u v u' v' w`, using that having a global presentation is invariant under raising the
universe of the sections, transported along `e` there, and brought back down.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

/-! ### Reindexing in independent universes

Global presentations and quasi-coherence of sheaves of modules with sections in the universe of
the structure sheaf, along an equivalence of sites whose universes of objects and of morphisms are
independent. -/

namespace Stacks.SheafOfModules

universe u' v'

section ReindexOfUniv

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- **Reindexing carries global presentations to global presentations**, for two sites in
independent universes.  This is `Stacks.SheafOfModules.hasGlobalPresentation_reindex` with the
object and morphism universes of the two sites independent. -/
theorem hasGlobalPresentation_reindex_ofUniv
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R)
    (h : M.HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).HasGlobalPresentation := by
  have hup : (SheafOfModules.uliftForPresentation.{u, v, w, w,
      max u v u' v' w} M).HasGlobalPresentation :=
    SheafOfModules.hasGlobalPresentation_uliftForPresentation'.{u, v, w, w,
      max u v u' v' w} h
  have hmid := SiteTransport.hasGlobalPresentation_transport.{u, v, u', v', w, w}
    (J' := J') e R _ hup
  exact SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'.{u', v', w, w,
    max u v u' v' w} (SheafOfModules.HasGlobalPresentation.of_iso
      (SiteTransport.pushforwardUliftIso_ofUniv.{u, v, u', v', w, w, max u v u' v' w}
        (J' := J') (F := e.functor) (𝟙 (reindexRing J' e R)) M) hmid)

/-- **Reindexing reflects global presentations**, for two sites in independent universes.  This
is `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex` with the object and morphism
universes of the two sites independent. -/
theorem hasGlobalPresentation_of_reindex_ofUniv
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R)
    (h : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).HasGlobalPresentation) : M.HasGlobalPresentation := by
  have hup := SheafOfModules.hasGlobalPresentation_uliftForPresentation'.{u', v', w, w,
    max u v u' v' w} h
  have hmid := SheafOfModules.HasGlobalPresentation.of_iso
    (SiteTransport.pushforwardUliftIso_ofUniv.{u, v, u', v', w, w, max u v u' v' w}
      (J' := J') (F := e.functor) (𝟙 (reindexRing J' e R)) M).symm hup
  exact SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'.{u, v, w, w,
    max u v u' v' w}
    (SiteTransport.hasGlobalPresentation_of_transport.{u, v, u', v', w, w}
      (J' := J') e R _ hmid)

section Slice

variable [e.inverse.IsDenseSubsite J J']

omit [e.inverse.IsContinuous J J'] in
/-- The restriction of a reindexed sheaf of modules to an object `V` is the reindexing, along the
localized equivalence of sites, of the restriction to `e.functor.obj V`, for two sites in
independent universes.  This is `Stacks.SheafOfModules.over_reindex_eq` with the object and
morphism universes of the two sites independent. -/
theorem over_reindex_eq_ofUniv (M : SheafOfModules.{w} R) (V : C') :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V =
      (SheafOfModules.pushforward.{w}
        (𝟙 (reindexRing (J'.over V) (SiteTransport.transportOverEquivalence e V)
          (R.over (e.functor.obj V))))).obj (M.over (e.functor.obj V)) := rfl

omit [e.inverse.IsContinuous J J'] in
/-- Reindexing carries a global presentation of the restriction to `e.functor.obj V` to a global
presentation of the restriction of the reindexing to `V`, for two sites in independent universes.
The slice sites have objects in `Type (max u v)` and `Type (max u' v')` and keep their
morphisms. -/
theorem hasGlobalPresentation_over_reindex_ofUniv
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w})
    [e.inverse.IsDenseSubsite J J'] (M : SheafOfModules.{w} R) (V : C')
    (h : (M.over (e.functor.obj V)).HasGlobalPresentation) :
    (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasGlobalPresentation := by
  rw [over_reindex_eq_ofUniv]
  exact hasGlobalPresentation_reindex_ofUniv
    (SiteTransport.transportOverEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- The slice case of `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex_ofUniv`: a global
presentation of the restriction of the reindexing to `V` comes from one of the restriction to
`e.functor.obj V`. -/
theorem hasGlobalPresentation_of_over_reindex_ofUniv
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w})
    [e.inverse.IsDenseSubsite J J'] (M : SheafOfModules.{w} R) (V : C')
    (h : (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasGlobalPresentation) : (M.over (e.functor.obj V)).HasGlobalPresentation := by
  rw [over_reindex_eq_ofUniv] at h
  exact hasGlobalPresentation_of_reindex_ofUniv
    (SiteTransport.transportOverEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- **Quasi-coherence is carried along an equivalence of ringed sites in independent
universes.**  This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex` with the object and
morphism universes of the two sites independent. -/
theorem isQuasicoherentOnSite_reindex_ofUniv
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w})
    [e.inverse.IsDenseSubsite J J'] (M : SheafOfModules.{w} R)
    [hM : M.IsQuasicoherentOnSite] :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsQuasicoherentOnSite := by
  obtain ⟨I, W, hW, hP⟩ :=
    (isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation M).mp hM
  refine isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation' _
    (W := fun i ↦ e.inverse.obj (W i))
    (SiteTransport.coversTop_inverse_obj e hW) fun i ↦ ?_
  exact hasGlobalPresentation_over_reindex_ofUniv e R M (e.inverse.obj (W i))
    (hasGlobalPresentation_overMap M (e.counitIso.app (W i)).hom (hP i))

omit [e.inverse.IsContinuous J J'] in
/-- **Quasi-coherence is reflected by an equivalence of ringed sites in independent
universes.**  This is `Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex` with the object
and morphism universes of the two sites independent. -/
theorem isQuasicoherentOnSite_of_reindex_ofUniv
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w})
    [e.inverse.IsDenseSubsite J J'] (M : SheafOfModules.{w} R)
    (hN : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite := by
  obtain ⟨I, V, hV, hP⟩ :=
    (isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation _).mp hN
  refine isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation' M
    (W := fun i ↦ e.functor.obj (V i))
    (SiteTransport.coversTop_functor_obj e hV) fun i ↦ ?_
  exact hasGlobalPresentation_of_over_reindex_ofUniv e R M (V i) (hP i)

omit [e.inverse.IsContinuous J J'] in
/-- **Stacks 03DM for clause (6) of Stacks 03DL, for an equivalence of ringed sites in
independent universes.**  A sheaf of modules is quasi-coherent exactly when its reindexing along
an equivalence of sites, over the transported structure sheaf, is quasi-coherent.  This is
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` with the object and morphism universes
of the two sites independent. -/
theorem isQuasicoherentOnSite_reindex_iff_ofUniv
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w})
    [e.inverse.IsDenseSubsite J J'] (M : SheafOfModules.{w} R) :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsQuasicoherentOnSite ↔ M.IsQuasicoherentOnSite :=
  ⟨fun h ↦ isQuasicoherentOnSite_of_reindex_ofUniv e R M h,
    fun _ ↦ isQuasicoherentOnSite_reindex_ofUniv e R M⟩

end Slice

end ReindexOfUniv

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

section Slice

variable [e.inverse.IsDenseSubsite J J']

end Slice

end Stacks.SheafOfModules

end
