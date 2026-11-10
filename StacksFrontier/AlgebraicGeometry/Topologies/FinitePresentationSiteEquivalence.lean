module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.ReindexFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation is carried along an equivalence of ringed sites

Let `e : C' ≌ C` be an equivalence of sites and `R` a sheaf of rings on `C`. This file proves that
finite presentation of a sheaf of modules, Stacks 03DL (7), is invariant under reindexing along
`e` (`Stacks.SheafOfModules.reindexEquivalence`), over the transported structure sheaf: Stacks 03DM
for clause (7) of Stacks 03DL, for an equivalence of ringed topoi presented by an equivalence of
the underlying ringed sites. It is proved for two predicates:
`SheafOfModules.IsFinitePresentationOnSite`, which asks for a finite global presentation of the
restriction to every object of the site, and `SheafOfModules.IsFinitePresentation`, which asks
for one over a covering family of the final object. A finite global presentation, Stacks 03DE (7),
is carried along the same reindexing at a module universe independent of the universe of the
sections of the structure sheaf, with the same numbers of generators and relations.

## Main results

* `Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor'`:
  a finite global presentation is carried by a functor that preserves colimits and zero
  morphisms and matches the two universe-lifted structure sheaves, at a free module universe.
* `Stacks.SheafOfModules.hasFiniteGlobalPresentation_reindex'`: reindexing along an equivalence
  of ringed sites carries finite global presentations to finite global presentations, at a free
  module universe.
* `Stacks.SheafOfModules.hasFiniteGlobalPresentation_of_reindex`: reindexing reflects finite
  global presentations.
* `Stacks.SheafOfModules.isFinitePresentationOnSite_of_reindex`: finite presentation on the site
  is reflected by reindexing.
* `Stacks.SheafOfModules.isFinitePresentationOnSite_reindex_iff`: finite presentation on the site
  is invariant under reindexing along an equivalence of ringed sites.
* `Stacks.SheafOfModules.isFinitePresentation_reindex`: reindexing preserves finite presentation.
* `Stacks.SheafOfModules.isFinitePresentation_of_reindex`: reindexing reflects it.
* `Stacks.SheafOfModules.isFinitePresentation_reindex_iff`: finite presentation is invariant
  under reindexing along an equivalence of sites.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace Stacks.SheafOfModules.FinitePresentationTransport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A finite global presentation is carried by a functor that preserves colimits and zero
morphisms, carries the universe-lifted structure sheaf to the universe-lifted structure sheaf,
and carries the universe-lifted module to the universe lift of the intended target**, at a module
universe independent of the universe of the sections of the structure sheaf. -/
@[ega "0 5.2.5" "special case"]
theorem hasFiniteGlobalPresentation_of_functor'
    {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}}
    (M : SheafOfModules.{m} R) (N : SheafOfModules.{m} R')
    {F : SheafOfModules.{max u v w m} R ⥤ SheafOfModules.{max u v w m} R'}
    (hF : PreservesColimitsOfSize.{max u v w m, max u v w m} F)
    (hF₀ : F.PreservesZeroMorphisms)
    (η₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m}
        (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m} (SheafOfModules.unit R'))
    (ηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w} N) :
    M.HasFiniteGlobalPresentation → N.HasFiniteGlobalPresentation := by
  classical
  have := hF
  have := hF₀
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  rintro ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩
  let ι' : ∀ _ : Fin n, SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m}
      (SheafOfModules.unit R') ⟶ F.obj P := fun i => η₁.inv ≫ F.map (ι i)
  let κ' : ∀ _ : Fin k, SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m}
      (SheafOfModules.unit R') ⟶ F.obj Q := fun i => η₁.inv ≫ F.map (κ i)
  have hPmap : IsColimit (Cofan.mk (F.obj P) (fun i => F.map (ι i))) :=
    (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk P ι)).toFun (isColimitOfPreserves F hP.some)
  have hQmap : IsColimit (Cofan.mk (F.obj Q) (fun i => F.map (κ i))) :=
    (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk Q κ)).toFun (isColimitOfPreserves F hQ.some)
  have hP' : Nonempty (IsColimit (Cofan.mk (F.obj P) ι')) :=
    ⟨Stacks.SheafOfModules.GlobalPresentationTransport.isColimitCofanPrecompose η₁.symm _ hPmap⟩
  have hQ' : Nonempty (IsColimit (Cofan.mk (F.obj Q) κ')) :=
    ⟨Stacks.SheafOfModules.GlobalPresentationTransport.isColimitCofanPrecompose η₁.symm _ hQmap⟩
  let b' : F.obj P ⟶ SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w} N :=
    F.map b ≫ ηM.hom
  have hab' : F.map a ≫ b' = 0 := by simp [b', ← F.map_comp_assoc, hab]
  let c' := CokernelCofork.ofπ b' hab'
  have hcMap : IsColimit (F.mapCocone (CokernelCofork.ofπ b hab)) :=
    isColimitOfPreserves F hc.some
  have hc' : IsColimit c' := by
    let d := (parallelPair a 0) ⋙ F
    let i₁ : d ≅ parallelPair (F.map a) (F.map 0) := by
      refine NatIso.ofComponents (fun j => ?_) ?_
      · cases j <;> exact Iso.refl _
      rintro _ _ (_ | _ | _) <;> simp [d]
    let i₂ : parallelPair (F.map a) (F.map 0) ≅ parallelPair (F.map a) 0 :=
      parallelPairIsoMk (Iso.refl (F.obj Q)) (Iso.refl (F.obj P))
    let i := i₁ ≪≫ i₂
    exact (IsColimit.equivOfNatIsoOfIso i (F.mapCocone (CokernelCofork.ofπ b hab)) c'
      (Cocone.ext ηM (by rintro (_ | _) <;>
        simp [c', b', d, i, i₁, i₂, parallelPairIsoMk, NatIso.ofComponents_inv_app]))).toFun hcMap
  exact ⟨n, k, F.obj P, F.obj Q, ι', κ', hP', hQ', F.map a, b', hab', ⟨hc'⟩⟩

end Stacks.SheafOfModules.FinitePresentationTransport

namespace Stacks.SheafOfModules

section GlobalPresentation

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : Sheaf J RingCat.{w})

/-- **Reindexing carries finite global presentations to finite global presentations**, at a free
module universe. -/
theorem hasFiniteGlobalPresentation_reindex' (M : SheafOfModules.{m} R)
    (h : M.HasFiniteGlobalPresentation) :
    ((SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj
      M).HasFiniteGlobalPresentation := by
  let φ : reindexRing J' e R ⟶
      (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R := 𝟙 _
  let F₀ := SheafOfModules.pushforward.{m} φ
  let eHi : SheafOfModules.{max u v w m} R ≌ SheafOfModules.{max u v w m} (reindexRing J' e R) :=
    reindexEquivalence e R
  let F := eHi.functor
  let _ : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  have hF : PreservesColimitsOfSize.{max u v w m, max u v w m} F := inferInstance
  have hF₀ : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : (SheafOfModules.pushforward.{w} φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit (reindexRing J' e R) := Iso.refl _
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m}
      (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v m}
        (SheafOfModules.unit (reindexRing J' e R)) :=
    pushforwardUliftIso.{u, v, w, w, max u v m} φ (SheafOfModules.unit R) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v m} hU
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, m, max u v w} (F₀.obj M) :=
    pushforwardUliftIso.{u, v, w, m, max u v w} φ M
  exact FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor'
    M (F₀.obj M) hF hF₀ hη₁ hηM h

end GlobalPresentation

section

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- **Reindexing reflects finite global presentations.** -/
theorem hasFiniteGlobalPresentation_of_reindex (M : SheafOfModules.{w} R)
    (h : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).HasFiniteGlobalPresentation) : M.HasFiniteGlobalPresentation := by
  let Sr := reindexRing J' e R
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} J J').obj Sr :=
    reindexBackSharp e R
  let F₀ := SheafOfModules.pushforward.{w} ψ
  let eHi : SheafOfModules.{max u v w} R ≌ SheafOfModules.{max u v w} Sr :=
    reindexEquivalence e R
  let F := eHi.inverse
  let : F.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  have hF : PreservesColimitsOfSize.{max u v w, max u v w} F := inferInstance
  have hF₀ : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : F₀.obj (SheafOfModules.unit Sr) ≅ SheafOfModules.unit R :=
    ((reindexEquivalence.{w, w, u, v, u, v} e R).unitIso.app (SheafOfModules.unit R)).symm
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit Sr)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (SheafOfModules.unit R) :=
    pushforwardUliftIso.{u, v, w, w, max u v w} ψ (SheafOfModules.unit Sr) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w} hU
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      ((SheafOfModules.pushforward.{w} (𝟙 Sr)).obj M)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M :=
    pushforwardUliftIso.{u, v, w, w, max u v w} ψ
        ((SheafOfModules.pushforward.{w} (𝟙 Sr)).obj M) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w}
        ((reindexEquivalence.{w, w, u, v, u, v} e R).unitIso.app M).symm
  exact FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor.{u, v, w}
    ((SheafOfModules.pushforward.{w} (𝟙 Sr)).obj M) M (F := F) hF hF₀ hη₁ hηM h

section Slice

variable [e.inverse.IsDenseSubsite J J']

omit [e.inverse.IsContinuous J J'] in
/-- The restriction of `M` to `e.functor.obj V` has a finite global presentation if the
restriction to `V` of its reindexing does. -/
theorem hasFiniteGlobalPresentation_of_over_reindex (M : SheafOfModules.{w} R) (V : C')
    (h : (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasFiniteGlobalPresentation) :
    (M.over (e.functor.obj V)).HasFiniteGlobalPresentation := by
  rw [over_reindex_eq] at h
  exact hasFiniteGlobalPresentation_of_reindex (overSiteEquivalence e V)
    (R.over (e.functor.obj V)) (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- **Finite presentation on the site is reflected by an equivalence of ringed sites.** -/
theorem isFinitePresentationOnSite_of_reindex (M : SheafOfModules.{w} R)
    (hN : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsFinitePresentationOnSite) : M.IsFinitePresentationOnSite := by
  constructor
  intro U
  obtain ⟨I, V, f, hcov, hpres⟩ := hN.locally_hasFiniteGlobalPresentation (e.inverse.obj U)
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
  · exact hasFiniteGlobalPresentation_of_over_reindex e R M (V i) (hpres i)

omit [e.inverse.IsContinuous J J'] in
/-- **Stacks 03DM for clause (7) of Stacks 03DL, for an equivalence of ringed sites.**  A sheaf of
modules is of finite presentation exactly when its reindexing along an equivalence of sites, over
the transported structure sheaf, is. -/
theorem isFinitePresentationOnSite_reindex_iff (M : SheafOfModules.{w} R) :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsFinitePresentationOnSite ↔ M.IsFinitePresentationOnSite :=
  ⟨isFinitePresentationOnSite_of_reindex e R M, fun _ => isFinitePresentationOnSite_reindex e R M⟩

end Slice

end

section CoveringPresentation

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J]
  (R : Sheaf J RingCat.{w})
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C', HasSheafify (J'.over U) AddCommGrpCat.{w}]
  [∀ U : C', (J'.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [e.inverse.IsDenseSubsite J J'] [e.functor.IsDenseSubsite J' J]

/-- A sheaf of modules with a finite presentation `P` is of finite presentation, with the
finiteness of `P` as an explicit hypothesis. -/
private theorem isFinitePresentation_of_finitePresentation {D : Type*} [Category D]
    {K : GrothendieckTopology D} {Rd : Sheaf K RingCat.{w}}
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{w}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (N : _root_.SheafOfModules.{w} Rd) (P : N.Presentation) (hP : P.IsFinite) :
    N.IsFinitePresentation :=
  have := hP
  SliceFinite.isFinitePresentation_of_presentation P

omit [e.functor.IsDenseSubsite J' J] in
/-- **Reindexing along an equivalence of sites preserves finite presentation.** -/
theorem isFinitePresentation_reindex (M : _root_.SheafOfModules.{w} R)
    (h : M.IsFinitePresentation) :
    ((_root_.SheafOfModules.pushforward.{w}
      (𝟙 (reindexRing J' e R))).obj M).IsFinitePresentation := by
  have := h
  let (U : C) (V : Over U) : HasSheafify ((J.over U).over V) AddCommGrpCat.{w} :=
    SliceFinite.hasSheafify_iteratedSlice J U V
  let (U : C) (V : Over U) :
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w} :=
    SliceFinite.wEqualsLocallyBijective_iteratedSlice J U V
  let (U : C') (V : Over U) : HasSheafify ((J'.over U).over V) AddCommGrpCat.{w} :=
    SliceFinite.hasSheafify_iteratedSlice J' U V
  let (U : C') (V : Over U) :
      ((J'.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w} :=
    SliceFinite.wEqualsLocallyBijective_iteratedSlice J' U V
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine (isFinitePresentation_iff_exists_cover_isFinitePresentation
    ((_root_.SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M)).2
    ⟨q.I, fun i ↦ e.inverse.obj (q.X i),
      GrothendieckTopology.coversTop_inverse_obj e q.coversTop, fun i ↦ ?_⟩
  have := hq.isFinite_presentation i
  rw [over_reindex_eq]
  let c : e.functor.obj (e.inverse.obj (q.X i)) ⟶ q.X i := e.counitIso.hom.app (q.X i)
  obtain ⟨P, hP⟩ := LocalCokernel.exists_finitePresentation_overMap M c (q.presentation i)
  have := hP
  let T := _root_.SheafOfModules.pushforward.{w}
    (𝟙 (reindexRing (J'.over (e.inverse.obj (q.X i)))
      (overSiteEquivalence e (e.inverse.obj (q.X i)))
      (R.over (e.functor.obj (e.inverse.obj (q.X i))))))
  exact isFinitePresentation_of_finitePresentation _
    (LocalCokernel.mapFinitePresentation P T (Iso.refl _))
    (LocalCokernel.mapFinitePresentation_isFinite P T (Iso.refl _))

/-- **Reindexing along an equivalence of sites reflects finite presentation.** -/
theorem isFinitePresentation_of_reindex (M : _root_.SheafOfModules.{w} R)
    (h : ((_root_.SheafOfModules.pushforward.{w}
      (𝟙 (reindexRing J' e R))).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  have := h
  let (U : C) (V : Over U) : HasSheafify ((J.over U).over V) AddCommGrpCat.{w} :=
    SliceFinite.hasSheafify_iteratedSlice J U V
  let (U : C) (V : Over U) :
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w} :=
    SliceFinite.wEqualsLocallyBijective_iteratedSlice J U V
  let (U : C') (V : Over U) : HasSheafify ((J'.over U).over V) AddCommGrpCat.{w} :=
    SliceFinite.hasSheafify_iteratedSlice J' U V
  let (U : C') (V : Over U) :
      ((J'.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w} :=
    SliceFinite.wEqualsLocallyBijective_iteratedSlice J' U V
  let : e.symm.inverse.IsDenseSubsite J' J :=
    inferInstanceAs (e.functor.IsDenseSubsite J' J)
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    ((_root_.SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M)
  refine (isFinitePresentation_iff_exists_cover_isFinitePresentation M).2
    ⟨q.I, fun i ↦ e.functor.obj (q.X i),
      GrothendieckTopology.coversTop_inverse_obj e.symm q.coversTop, fun i ↦ ?_⟩
  have := hq.isFinite_presentation i
  let eq := reindexEquivalence (J' := J'.over (q.X i)) (overSiteEquivalence e (q.X i))
    (R.over (e.functor.obj (q.X i)))
  let hPi : ((eq.functor.obj (M.over (e.functor.obj (q.X i)))).Presentation) :=
    q.presentation i
  have : hPi.IsFinite := hq.isFinite_presentation i
  have hu : IsIso (eq.unitIso.inv.app (M.over (e.functor.obj (q.X i)))) :=
    ⟨eq.unitIso.hom.app _, eq.unitIso.inv_hom_id_app _, eq.unitIso.hom_inv_id_app _⟩
  let : (LocalCokernel.mapFinitePresentation hPi eq.inverse
      (eq.unitIso.app (_root_.SheafOfModules.unit _))).IsFinite :=
    LocalCokernel.mapFinitePresentation_isFinite hPi eq.inverse
      (eq.unitIso.app (_root_.SheafOfModules.unit _))
  exact isFinitePresentation_of_finitePresentation _
    ((LocalCokernel.mapFinitePresentation hPi eq.inverse
        (eq.unitIso.app (_root_.SheafOfModules.unit _))).ofIsIso
      (eq.unitIso.inv.app (M.over (e.functor.obj (q.X i))))) inferInstance

/-- **Finite presentation is invariant under reindexing along an equivalence of sites.**  This
is the finite-presentation clause 03DL (7) of Modules on Sites, Lemma 03DM. -/
theorem isFinitePresentation_reindex_iff (M : _root_.SheafOfModules.{w} R) :
    M.IsFinitePresentation ↔
      ((_root_.SheafOfModules.pushforward.{w}
        (𝟙 (reindexRing J' e R))).obj M).IsFinitePresentation :=
  ⟨isFinitePresentation_reindex e R M, isFinitePresentation_of_reindex e R M⟩

end CoveringPresentation

end Stacks.SheafOfModules

end
