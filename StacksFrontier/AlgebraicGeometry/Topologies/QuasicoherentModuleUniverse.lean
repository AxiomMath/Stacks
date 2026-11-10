module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Quasi-coherence along an equivalence of sites and on slices, at a free module universe

The clause of Stacks 03DN for quasi-coherence and the invariance of quasi-coherence under an
equivalence of ringed sites (Stacks 03DM for clause (6) of Stacks 03DL) are both available in
this development only with the universe of the module sections tied to the universe of the
sections of the structure sheaf:
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite` and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex` are both stated for a
`CategoryTheory.SheafOfModules.{w}` over a `CategoryTheory.Sheaf J RingCat.{w}`.

This file states them with the two universes independent, as
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation` already does
for the clause of Stacks 03DN read with global presentations. Nothing is assumed of the site,
and no statement here is weaker than the one it generalizes: each is the same assertion with the
module universe left free.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex'`: reindexing along an equivalence of
  sites reflects global presentations.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex'`: reindexing along an equivalence of
  ringed sites reflects quasi-coherence.
* `Stacks.SheafOfModules.hasGlobalPresentation_iteratedSlice'`: a global presentation on a twice
  iterated slice site is one on the slice at the underlying object. This is the reindexing
  statement for `CategoryTheory.Over.iteratedSliceEquiv`, which is an equivalence of sites.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over`: **quasi-coherence is local on the
  site** — a sheaf of modules whose restriction to every slice is quasi-coherent is
  quasi-coherent.
* `Stacks.SheafOfModules.exists_cover_hasGlobalPresentation_of_isQuasicoherentOnSite_over`: a
  module quasi-coherent on the slice at an object admits a covering of that object on whose
  members it has a global presentation.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_over`: **quasi-coherence is local on a
  covering of each object** — the previous statement with the family of all objects replaced by a
  covering family of each one, which is the form a local finiteness hypothesis supplies.

## Implementation notes

The proofs are the ones of the pinned statements, with the module universe `w` replaced by `m`
throughout: `Stacks.SheafOfModules.hasGlobalPresentation_map` and
`Stacks.SheafOfModules.pushforwardUliftIso` are already stated with the module universe free, and
so is `Stacks.SheafOfModules.reindexEquivalence`, so only the explicit universe arguments move —
the universe at which a global presentation takes its coproducts becomes `max u v w m` rather
than `max u v w`.

`Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over` is not proved by the covering-family
criterion but directly: the covering of an object `U` witnessing quasi-coherence of `M` is the
one that quasi-coherence of `M.over U` provides at the terminal object `𝟙 U` of the slice, read
back along `CategoryTheory.Sieve.overEquiv`, and the global presentations travel by
`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSlice'`.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- **Reindexing along an equivalence of sites reflects global presentations**, with the universe
of the module sections independent of the universe of the coefficient rings.

This is `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex` with the module universe left
free; the proof is the same, the inverse of `Stacks.SheafOfModules.reindexEquivalence` carrying
the presentation back through `Stacks.SheafOfModules.hasGlobalPresentation_map`. -/
theorem hasGlobalPresentation_of_reindex' (M : SheafOfModules.{m} R)
    (h : ((SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj
      M).HasGlobalPresentation) : M.HasGlobalPresentation := by
  let S := reindexRing J' e R
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} J J').obj S :=
    reindexBackSharp e R
  let F₀ := SheafOfModules.pushforward.{m} ψ
  let eHi : SheafOfModules.{max u v w m} R ≌ SheafOfModules.{max u v w m} S :=
    reindexEquivalence e R
  let F := eHi.inverse
  let : F.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : (SheafOfModules.pushforward.{w} ψ).obj (SheafOfModules.unit S) ≅
      SheafOfModules.unit R :=
    ((reindexEquivalence.{w, w, u, v, u, v} e R).unitIso.app (SheafOfModules.unit R)).symm
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m}
      (SheafOfModules.unit S)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m} (SheafOfModules.unit R) :=
    pushforwardUliftIso.{u, v, w, w, max u v m} ψ (SheafOfModules.unit S) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v m} hU
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w}
      ((SheafOfModules.pushforward.{m} (𝟙 S)).obj M)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w}
        (F₀.obj ((SheafOfModules.pushforward.{m} (𝟙 S)).obj M)) :=
    pushforwardUliftIso.{u, v, w, m, max u v w} ψ ((SheafOfModules.pushforward.{m} (𝟙 S)).obj M)
  have h' := hasGlobalPresentation_map (F₀ := F₀) (F := F)
    ((SheafOfModules.pushforward.{m} (𝟙 S)).obj M) hη₁ hηM h
  exact SheafOfModules.HasGlobalPresentation.of_iso
    ((reindexEquivalence.{w, m, u, v, u, v} e R).unitIso.app M).symm h'

section Slice

variable [e.inverse.IsDenseSubsite J J']

omit [e.inverse.IsContinuous J J'] in
/-- The restriction of a reindexed sheaf of modules to an object `V` is the reindexing, along the
localized equivalence of sites, of the restriction to `e.functor.obj V`. This is
`Stacks.SheafOfModules.over_reindex_eq` with the module universe left free. -/
theorem over_reindex_eq' (M : SheafOfModules.{m} R) (V : C') :
    ((SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj M).over V =
      (SheafOfModules.pushforward.{m}
        (𝟙 (reindexRing (J'.over V) (overSiteEquivalence e V)
          (R.over (e.functor.obj V))))).obj (M.over (e.functor.obj V)) := rfl

omit [e.inverse.IsContinuous J J'] in
/-- The slice case of `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex'`: a global
presentation of the restriction of the reindexing to `V` comes from one of the restriction to
`e.functor.obj V`. -/
theorem hasGlobalPresentation_of_over_reindex' (M : SheafOfModules.{m} R) (V : C')
    (h : (((SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasGlobalPresentation) : (M.over (e.functor.obj V)).HasGlobalPresentation := by
  rw [over_reindex_eq'] at h
  exact hasGlobalPresentation_of_reindex' (overSiteEquivalence e V)
    (R.over (e.functor.obj V)) (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- **Quasi-coherence is reflected by an equivalence of ringed sites**, with the universe of the
module sections independent of the universe of the coefficient rings.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex` with the module universe left
free; the proof is the same, a covering of `e.inverse.obj U` lifting to a covering of `U` because
`e.inverse` is cocontinuous and the presentations travelling by
`Stacks.SheafOfModules.hasGlobalPresentation_of_over_reindex'`. -/
theorem isQuasicoherentOnSite_of_reindex' (M : SheafOfModules.{m} R)
    (hN : ((SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj
      M).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hcov, hpres⟩ := hN.locally_hasGlobalPresentation (e.inverse.obj U)
  refine ⟨I, fun i => e.functor.obj (V i),
    fun i => e.functor.map (f i) ≫ (e.counitIso.app U).hom, ?_, fun i => ?_⟩
  · apply J.superset_covering _ (e.inverse.cover_lift J J' hcov)
    intro Z h hh
    replace hh : (Sieve.ofArrows V f).arrows (e.inverse.map h) := hh
    rw [Sieve.mem_ofArrows_iff] at hh ⊢
    obtain ⟨i, b, hb⟩ := hh
    refine ⟨i, (e.counitIso.app Z).inv ≫ e.functor.map b, ?_⟩
    have hnat := e.counit.naturality h
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
    have key : e.functor.map b ≫ e.functor.map (f i) = e.functor.map (e.inverse.map h) := by
      rw [← Functor.map_comp, hb]
    simp only [Category.assoc]
    rw [← Category.assoc (e.functor.map b), key,
      show (e.counitIso.app U).hom = e.counit.app U from rfl, hnat]
    simp
  · exact hasGlobalPresentation_of_over_reindex' e R M (V i) (hpres i)

end Slice

/-- **A global presentation on a twice iterated slice site is one on the slice at the underlying
object.** For an object `f` of the slice `C/U`, the restriction of `M.over U` to `f` is the
reindexing of `M.over f.left` along `CategoryTheory.Over.iteratedSliceEquiv`, which is an
equivalence of sites matching the two structure sheaves on the nose; so
`Stacks.SheafOfModules.hasGlobalPresentation_of_reindex'` applies. -/
theorem hasGlobalPresentation_iteratedSlice' {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{m} R)
    (U : C) (f : Over U) (h : ((M.over U).over f).HasGlobalPresentation) :
    (M.over f.left).HasGlobalPresentation :=
  hasGlobalPresentation_of_reindex' (J' := (J.over U).over f)
    (Over.iteratedSliceEquiv f) (R.over f.left) (M.over f.left) h

/-- The covering of `U` provided by quasi-coherence of `M.over U`, with global presentations on its
members. -/
private theorem exists_cover_hasGlobalPresentation_over_aux {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{m} R) (U : C) (h : (M.over U).IsQuasicoherentOnSite) :
    ∃ (I : Type (max u v)) (V : I → C) (g : ∀ i, V i ⟶ U),
      Sieve.ofArrows V g ∈ J U ∧ ∀ i, (M.over (V i)).HasGlobalPresentation := by
  obtain ⟨I, V, g, hcov, hpres⟩ := h.locally_hasGlobalPresentation (Over.mk (𝟙 U))
  refine ⟨I, fun i => (V i).left, fun i => (g i).left, ?_,
    fun i => hasGlobalPresentation_iteratedSlice' M U (V i) (hpres i)⟩
  rwa [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hcov

/-- **Quasi-coherence is local on the site.** A sheaf of modules whose restriction to the slice
at every object is quasi-coherent is quasi-coherent.

This is the clause of Stacks 03DN for quasi-coherence at the family of all objects, which covers
the final object for a trivial reason, with the universe of the module sections independent of
the universe of the coefficient rings; it is
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite` in the
direction that produces quasi-coherence, with that universe left free. The covering of an object
`U` is the one quasi-coherence of `M.over U` provides at the terminal object `𝟙 U` of the slice,
and the global presentations travel by
`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSlice'`. -/
theorem isQuasicoherentOnSite_of_forall_over {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{m} R)
    (h : ∀ U : C, (M.over U).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite := by
  refine ⟨fun U => ?_⟩
  exact exists_cover_hasGlobalPresentation_over_aux M U (h U)

/-- **A module quasi-coherent on the slice at an object has a global presentation on a covering of
that object.**  The covering is the one quasi-coherence of `M.over U` provides at the terminal
object `𝟙 U` of the slice, and the global presentations travel down by
`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSlice'`.

This is the body of `Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over` at a single
object, isolated so that it can be iterated over a covering family. -/
theorem exists_cover_hasGlobalPresentation_of_isQuasicoherentOnSite_over {C : Type u}
    [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{m} R) (U : C) (h : (M.over U).IsQuasicoherentOnSite) :
    ∃ (I : Type (max u v)) (V : I → C) (g : ∀ i, V i ⟶ U),
      Sieve.ofArrows V g ∈ J U ∧ ∀ i, (M.over (V i)).HasGlobalPresentation := by
  exact exists_cover_hasGlobalPresentation_over_aux M U h

/-- **Quasi-coherence is local on a covering of each object.**  If every object of the site has a
covering on whose members the restriction of `M` to the slice is quasi-coherent, then `M` is
quasi-coherent.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over` with the family of all
objects relaxed to a covering family of each object, and it is the form in which a *local*
finiteness hypothesis — Stacks 03DL(6) or 03DL(7), which assert a property on a covering of each
object and not at the object itself — supplies its input.  The covering of `U` witnessing
quasi-coherence is obtained by refining the given covering `{V i → U}` against the coverings of
the `V i` that
`Stacks.SheafOfModules.exists_cover_hasGlobalPresentation_of_isQuasicoherentOnSite_over`
provides, which is transitivity of the topology; the index type is the resulting sigma type and
stays in `Type (max u v)`. -/
theorem isQuasicoherentOnSite_of_locally_over {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{m} R)
    (h : ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (g : ∀ i, V i ⟶ U),
      Sieve.ofArrows V g ∈ J U ∧ ∀ i, (M.over (V i)).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, g, hcov, hQC⟩ := h U
  choose K W k hWcov hWpres using fun i =>
    exists_cover_hasGlobalPresentation_of_isQuasicoherentOnSite_over M (V i) (hQC i)
  refine ⟨Σ i, K i, fun p => W p.1 p.2, fun p => k p.1 p.2 ≫ g p.1, ?_,
    fun p => hWpres p.1 p.2⟩
  refine J.transitive hcov _ fun Y a ha => ?_
  rw [Sieve.mem_ofArrows_iff] at ha
  obtain ⟨i, b, rfl⟩ := ha
  refine J.superset_covering (fun Z l hl => ?_) (J.pullback_stable b (hWcov i))
  have hl' : Sieve.ofArrows (W i) (k i) (l ≫ b) := hl
  rw [Sieve.mem_ofArrows_iff] at hl'
  obtain ⟨j, c, hc⟩ := hl'
  rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff]
  refine ⟨⟨i, j⟩, c, ?_⟩
  change l ≫ b ≫ g i = c ≫ k i j ≫ g i
  rw [← Category.assoc, hc, Category.assoc]

end Stacks.SheafOfModules

end
