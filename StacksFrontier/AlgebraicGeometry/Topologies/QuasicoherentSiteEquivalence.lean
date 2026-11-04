module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Quasi-coherence is carried along an equivalence of ringed sites

A sheaf of modules on a ringed site is quasi-coherent exactly when its reindexing along an
equivalence of ringed sites is quasi-coherent, so quasi-coherence depends only on the ringed topos
when the equivalence of topoi is presented by an equivalence of the underlying ringed sites.

The equivalence `e : C' ≌ C` is assumed to satisfy `e.inverse.IsDenseSubsite J J'`, which says that
a sieve is a covering sieve on one side exactly when its image is one on the other.

## Main definitions

* `Stacks.SheafOfModules.overSiteEquivalence`: the induced equivalence between the slice sites.

## Main results

* `Stacks.SheafOfModules.overPost_isDenseSubsite`: the localization of an equivalence of sites at
  an object is again an equivalence of sites.
* `Stacks.SheafOfModules.hasGlobalPresentation_reindex` and
  `Stacks.SheafOfModules.hasGlobalPresentation_of_reindex`: a global presentation is carried along
  reindexing, and is reflected by it.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex` and
  `Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex`: quasi-coherence is carried along
  reindexing, and is reflected by it.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`: quasi-coherence of a sheaf of modules
  is invariant under an equivalence of ringed sites.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- Reindexing along an equivalence of sites carries a sheaf of modules with a global presentation
to a sheaf of modules with a global presentation. -/
theorem hasGlobalPresentation_reindex (M : SheafOfModules.{w} R)
    (h : M.HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).HasGlobalPresentation := by
  let φ : reindexRing J' e R ⟶
      (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R := 𝟙 _
  let F₀ := SheafOfModules.pushforward.{w} φ
  let eHi : SheafOfModules.{max u v w} R ≌ SheafOfModules.{max u v w} (reindexRing J' e R) :=
    reindexEquivalence e R
  let F := eHi.functor
  let : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : F₀.obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit (reindexRing J' e R) := Iso.refl _
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (SheafOfModules.unit (reindexRing J' e R)) :=
    pushforwardUliftIso.{u, v, w, w, max u v w} φ (SheafOfModules.unit R) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w} hU
  exact hasGlobalPresentation_map (F₀ := F₀) (F := F) M hη₁
    (pushforwardUliftIso.{u, v, w, w, max u v w} φ M) h

/-- If the reindexing of a sheaf of modules along an equivalence of sites has a global
presentation, then so does the sheaf of modules. -/
theorem hasGlobalPresentation_of_reindex (M : SheafOfModules.{w} R)
    (h : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).HasGlobalPresentation) : M.HasGlobalPresentation := by
  let S := reindexRing J' e R
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} J J').obj S :=
    reindexBackSharp e R
  let F₀ := SheafOfModules.pushforward.{w} ψ
  let eHi : SheafOfModules.{max u v w} R ≌ SheafOfModules.{max u v w} S :=
    reindexEquivalence e R
  let F := eHi.inverse
  let : F.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : F₀.obj (SheafOfModules.unit S) ≅ SheafOfModules.unit R :=
    ((reindexEquivalence.{w, w, u, v, u, v} e R).unitIso.app (SheafOfModules.unit R)).symm
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit S)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (SheafOfModules.unit R) :=
    pushforwardUliftIso.{u, v, w, w, max u v w} ψ (SheafOfModules.unit S) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w} hU
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      ((SheafOfModules.pushforward.{w} (𝟙 S)).obj M)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (F₀.obj ((SheafOfModules.pushforward.{w} (𝟙 S)).obj M)) :=
    pushforwardUliftIso.{u, v, w, w, max u v w} ψ ((SheafOfModules.pushforward.{w} (𝟙 S)).obj M)
  exact SheafOfModules.HasGlobalPresentation.of_iso
    ((reindexEquivalence.{w, w, u, v, u, v} e R).unitIso.app M).symm
    (hasGlobalPresentation_map (F₀ := F₀) (F := F)
      ((SheafOfModules.pushforward.{w} (𝟙 S)).obj M) hη₁ hηM h)

section Slice

variable [e.inverse.IsDenseSubsite J J']

/-- Localizing an equivalence of sites at an object again gives an equivalence of sites: a sieve on
`V` is a covering sieve for the localized topology exactly when its image under
`Over.post e.functor` is one. -/
instance overPost_isDenseSubsite (V : C') :
    (Over.post (X := V) e.functor).IsDenseSubsite (J'.over V) (J.over (e.functor.obj V)) where
  functorPushforward_mem_iff := by
    intro X S
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post]
    exact e.functor.functorPushforward_mem_iff J' J

/-- The equivalence of slice sites induced by an equivalence of sites. -/
noncomputable abbrev overSiteEquivalence (V : C') : Over V ≌ Over (e.functor.obj V) :=
  (Over.post (X := V) e.functor).asEquivalence

/-- The inverse of the equivalence of slice sites identifies the two localized topologies. -/
instance (V : C') : (overSiteEquivalence e V).inverse.IsDenseSubsite
    (J.over (e.functor.obj V)) (J'.over V) :=
  letI : ((overSiteEquivalence e V).symm).inverse.IsDenseSubsite (J'.over V)
      (J.over (e.functor.obj V)) :=
    inferInstanceAs ((Over.post (X := V) e.functor).IsDenseSubsite _ _)
  inferInstanceAs (((overSiteEquivalence e V).symm).functor.IsDenseSubsite _ _)

omit [e.inverse.IsContinuous J J'] in
/-- The restriction of a reindexed sheaf of modules to an object `V` is the reindexing, along the
localized equivalence of sites, of the restriction to `e.functor.obj V`. -/
theorem over_reindex_eq (M : SheafOfModules.{w} R) (V : C') :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V =
      (SheafOfModules.pushforward.{w}
        (𝟙 (reindexRing (J'.over V) (overSiteEquivalence e V)
          (R.over (e.functor.obj V))))).obj (M.over (e.functor.obj V)) := rfl

omit [e.inverse.IsContinuous J J'] in
/-- Reindexing carries a global presentation of the restriction to `e.functor.obj V` to a global
presentation of the restriction of the reindexing to `V`. -/
theorem hasGlobalPresentation_over_reindex (M : SheafOfModules.{w} R) (V : C')
    (h : (M.over (e.functor.obj V)).HasGlobalPresentation) :
    (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasGlobalPresentation := by
  rw [over_reindex_eq]
  exact hasGlobalPresentation_reindex (overSiteEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

/-- A family of arrows covering `E.functor.obj U` is carried by `E.inverse` to a covering family
of `U`. -/
private theorem ofArrows_inverse_mem (E : C' ≌ C) [E.functor.IsCocontinuous J' J] {U : C'}
    {I : Type*} {W : I → C} {g : ∀ i, W i ⟶ E.functor.obj U}
    (hcov : Sieve.ofArrows W g ∈ J (E.functor.obj U)) :
    Sieve.ofArrows (fun i => E.inverse.obj (W i))
      (fun i => E.inverse.map (g i) ≫ (E.unitIso.app U).inv) ∈ J' U := by
  apply J'.superset_covering _ (E.functor.cover_lift J' J hcov)
  intro Z h hh
  replace hh : (Sieve.ofArrows W g).arrows (E.functor.map h) := hh
  rw [Sieve.mem_ofArrows_iff] at hh ⊢
  obtain ⟨i, a, ha⟩ := hh
  refine ⟨i, (E.unitIso.app Z).hom ≫ E.inverse.map a, ?_⟩
  have hnat := E.unit.naturality h
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  have key : E.inverse.map a ≫ E.inverse.map (g i) = E.inverse.map (E.functor.map h) := by
    rw [← Functor.map_comp, ha]
  simp only [Category.assoc]
  rw [← Category.assoc (E.inverse.map a), key, ← Category.assoc,
    show (E.unitIso.app Z).hom = E.unit.app Z from rfl, ← hnat]
  simp

omit [e.inverse.IsContinuous J J'] in
/-- If a sheaf of modules on `(C, J, R)` is quasi-coherent, so is its reindexing along an
equivalence of sites `e : C' ≌ C`, taken over the transported structure sheaf. -/
theorem isQuasicoherentOnSite_reindex (M : SheafOfModules.{w} R)
    [hM : M.IsQuasicoherentOnSite] :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsQuasicoherentOnSite := by
  constructor
  intro V
  obtain ⟨I, W, g, hcov, hpres⟩ := hM.locally_hasGlobalPresentation (e.functor.obj V)
  refine ⟨I, fun i => e.inverse.obj (W i),
    fun i => e.inverse.map (g i) ≫ (e.unitIso.app V).inv, ?_, fun i => ?_⟩
  · exact ofArrows_inverse_mem e hcov
  · exact hasGlobalPresentation_over_reindex e R M _
      (hasGlobalPresentation_overMap M (e.counitIso.app (W i)).hom (hpres i))

omit [e.inverse.IsContinuous J J'] in
/-- The slice case of `hasGlobalPresentation_of_reindex`: a global presentation of the restriction
of the reindexing to `V` comes from one of the restriction to `e.functor.obj V`. -/
theorem hasGlobalPresentation_of_over_reindex (M : SheafOfModules.{w} R) (V : C')
    (h : (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasGlobalPresentation) : (M.over (e.functor.obj V)).HasGlobalPresentation := by
  rw [over_reindex_eq] at h
  exact hasGlobalPresentation_of_reindex (overSiteEquivalence e V)
    (R.over (e.functor.obj V)) (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- If the reindexing of a sheaf of modules along an equivalence of sites `e : C' ≌ C`, taken over
the transported structure sheaf, is quasi-coherent, then so is the sheaf of modules. -/
theorem isQuasicoherentOnSite_of_reindex (M : SheafOfModules.{w} R)
    (hN : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite := by
  constructor
  intro U
  obtain ⟨I, V, f, hcov, hpres⟩ := hN.locally_hasGlobalPresentation (e.inverse.obj U)
  refine ⟨I, fun i => e.functor.obj (V i),
    fun i => e.functor.map (f i) ≫ (e.counitIso.app U).hom, ?_, fun i => ?_⟩
  · have : e.symm.functor.IsCocontinuous J J' := inferInstanceAs (e.inverse.IsCocontinuous J J')
    exact ofArrows_inverse_mem e.symm hcov
  · exact hasGlobalPresentation_of_over_reindex e R M (V i) (hpres i)

omit [e.inverse.IsContinuous J J'] in
/-- A sheaf of modules is quasi-coherent exactly when its reindexing along an equivalence of sites,
over the transported structure sheaf, is quasi-coherent. -/
theorem isQuasicoherentOnSite_reindex_iff (M : SheafOfModules.{w} R) :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsQuasicoherentOnSite ↔ M.IsQuasicoherentOnSite :=
  ⟨isQuasicoherentOnSite_of_reindex e R M, fun _ ↦ isQuasicoherentOnSite_reindex e R M⟩

end Slice

end Stacks.SheafOfModules

end
