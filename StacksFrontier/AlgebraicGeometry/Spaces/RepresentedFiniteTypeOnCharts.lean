module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetTransport

/-!
# Finite type on a site is invariant under an equivalence of ringed sites

Stacks 03DM asserts that each of the eight local conditions of Stacks 03DL is intrinsic to the
ringed topos.  `StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentSiteEquivalence.lean`
proves the quasi-coherence clause, Stacks 03DL (6), for an equivalence of the underlying ringed
sites.  This file proves the *finite type* clause, Stacks 03DL (5), for the same kind of
equivalence, in both directions, and applies it to a representable algebraic space: a
finite-type quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the scheme underlying an object
`U` of the big fppf site, read on the small étale site of the algebraic space `yoneda.obj U`
through `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, is of finite type
on charts.

## Main results

* `Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_of_functor`: generation by
  finitely many global sections, Stacks 03DE (5), is carried by any functor which preserves
  colimits and matches the universe-lifted structure sheaves.
* `Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_overMap`: it restricts
  along an arrow of the site.
* `Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_reindex` and
  `Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_of_reindex`: reindexing
  along an equivalence of sites both carries generation by finitely many global sections and
  reflects it.
* `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex`,
  `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_reindex` and
  `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex_iff`: **Stacks 03DM for
  clause (5) of Stacks 03DL, for an equivalence of ringed sites** — a sheaf of modules is of
  finite type exactly when its reindexing along an equivalence of sites, over the transported
  sheaf of rings, is.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence` and
  `AlgebraicGeometry.Space.isFiniteTypeOnCharts_representedQuasicoherentSchemeEquivalence`: the
  application to a representable algebraic space.

## Implementation notes

`SheafOfModules.HasFiniteGlobalGenerators` and `SheafOfModules.HasGlobalPresentation` have the
same shape — a coproduct of copies of the universe-lifted structure sheaf mapping onto the
universe-lifted module — the first with a finite index and an epimorphism in place of the
second's cokernel.  The transport lemmas here are therefore the lemmas of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GlobalPresentationTransport.lean` with the cokernel
step replaced by preservation of epimorphisms, which a colimit-preserving functor has; in
particular no `PreservesZeroMorphisms` hypothesis is needed.

Like the quasi-coherence clause, the transport takes the functor twice: at the module universe,
whose image of the module the conclusion is about, and at the raised universe `max u v w` in
which the coproduct lives.  Both are the reindexing functor, and the two are tied together by
`Stacks.SheafOfModules.GlobalPresentationTransport.pushforwardUliftIso`.  The module universe is
the universe of the coefficient rings throughout, which is all the application needs: every site
in it has objects in `Type (u + 1)` and morphisms in `Type u`, with modules at `u`.

The slice step uses `Stacks.SheafOfModules.over_reindex_eq`, an equality of modules, so it needs
no comparison isomorphism; and the members of the covering produced on the source site are the
images `e.functor.obj (e.inverse.obj (W i))` of those on the target site, which is why
`hasFiniteGlobalGenerators_overMap` is applied at the counit before the reindexing.

**Why the reflecting direction is cheap here, and is not for finite presentation.**  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Topologies/FinitePresentationSiteEquivalence.lean` explain that
the reflecting direction of finite presentation cannot be the carrying direction applied to
`e.symm`, because that lands the module over the *twice*-reindexed sheaf of rings, which is only
isomorphic to `R`.  The same obstruction applies to finite type, and the same remedy works: run
the transport at the *inverse* functor of the single `Stacks.SheafOfModules.reindexEquivalence`,
which keeps the sheaf of rings on the nose.  Unlike finite presentation that costs nothing extra
here, because `SheafOfModules.HasFiniteGlobalGenerators` is stated with coproducts and
epimorphisms rather than sheafified free sheaves and so drags in no slice sheafification data:
the whole reflecting direction is
`Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_of_functor` at
`(Stacks.SheafOfModules.reindexEquivalence e R).inverse`, whose structure map is
`Stacks.SheafOfModules.reindexBackSharp`, together with the unit of the equivalence.

Both directions transport a covering family, in opposite directions, by
`CategoryTheory.Sieve.ofArrows_inverse_mem` — read at `e` for the carrying direction and at
`e.symm` for the reflecting one.  That is why the reflecting direction assumes the second
dense-subsite instance, `e.functor.IsDenseSubsite J' J`, exactly as
`Stacks.SheafOfModules.isFinitePresentation_of_reindex` does.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules.FiniteTypeTransport

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Generation by finitely many global sections is carried by a functor which preserves
colimits and carries the universe-lifted structure sheaf to the universe-lifted structure
sheaf.** -/
theorem hasFiniteGlobalGenerators_of_functor
    {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}}
    (M : SheafOfModules.{w} R)
    {F₀ : SheafOfModules.{w} R ⥤ SheafOfModules.{w} R'}
    {F : SheafOfModules.{max u v w} R ⥤ SheafOfModules.{max u v w} R'}
    [PreservesColimitsOfSize.{max u v w, max u v w} F]
    (η₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (SheafOfModules.unit R'))
    (ηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F₀.obj M))
    (h : M.HasFiniteGlobalGenerators) : (F₀.obj M).HasFiniteGlobalGenerators := by
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  obtain ⟨n, P, ι, hP, π, hπ⟩ := h
  have _ : Epi π := hπ
  have hPmap : IsColimit (Cofan.mk (F.obj P) (fun i ↦ F.map (ι i))) :=
    (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk P ι)).toFun (isColimitOfPreserves F hP.some)
  refine ⟨n, F.obj P, fun i ↦ η₁.inv ≫ F.map (ι i),
    ⟨GlobalPresentationTransport.isColimitCofanPrecompose η₁.symm _ hPmap⟩,
    F.map π ≫ ηM.hom, ?_⟩
  have _ : Epi (F.map π) := inferInstance
  infer_instance

/-- Generation by finitely many global sections is invariant under isomorphism. -/
theorem hasFiniteGlobalGenerators_of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N)
    (h : M.HasFiniteGlobalGenerators) : N.HasFiniteGlobalGenerators := by
  obtain ⟨n, P, ι, hP, π, hπ⟩ := h
  have _ : Epi π := hπ
  exact ⟨n, P, ι, hP, π ≫ (SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w}
    e).hom, inferInstance⟩

/-- **Generation by finitely many global sections restricts along an arrow of the site.** -/
theorem hasFiniteGlobalGenerators_overMap (M : SheafOfModules.{w} R) {X Y : C} (f : X ⟶ Y)
    (h : (M.over Y).HasFiniteGlobalGenerators) : (M.over X).HasFiniteGlobalGenerators := by
  have _ (Z : C) : HasSheafify (J.over Z) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over Z)
  have _ (Z : C) : (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (J.over Z)
  have _ : PreservesColimitsOfSize.{max u v w, max u v w}
      (SheafOfModules.overMap.{max u v w} R f) :=
    Stacks.SheafOfModules.overMap_preservesColimits.{u, v, max u v w, w} R f
  have hη₁ : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over Y))) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over X)) :=
    GlobalPresentationTransport.pushforwardUliftIso.{max u v, v, w, max u v w}
        (Sheaf.pushforwardOverMapIso R f).inv (SheafOfModules.unit (R.over Y)) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{max u v, v, w, w, max u v w}
        (SheafOfModules.overMapUnitIso f)
  have hηM : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} (M.over Y)) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        ((SheafOfModules.overMap.{w} R f).obj (M.over Y)) :=
    GlobalPresentationTransport.pushforwardUliftIso.{max u v, v, w, max u v w}
      (Sheaf.pushforwardOverMapIso R f).inv (M.over Y)
  exact hasFiniteGlobalGenerators_of_iso.{max u v, v, w}
    ((SheafOfModules.overFunctorMap R f).app M)
    (hasFiniteGlobalGenerators_of_functor.{max u v, v, w} (M.over Y)
      (F₀ := SheafOfModules.overMap.{w} R f)
      (F := SheafOfModules.overMap.{max u v w} R f) hη₁ hηM h)

/-- **Finite type on a site is invariant under isomorphism**, clause (5) of Stacks 03DL in its
categorical form.

Restriction to a slice is a functor, so an isomorphism of modules restricts to one on every
member of the covering family witnessing finite type, and generation by finitely many global
sections is itself invariant under isomorphism
(`Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_of_iso`).

This is the finite-type counterpart of
`Stacks.SheafOfModules.IsFinitePresentationOnSite.of_iso`, which it is proved exactly like; it
needs none of the slice sheafification instances that routing through Mathlib's
`SheafOfModules.IsFiniteType` and back would drag in. -/
theorem isFiniteTypeOnSite_of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N)
    (h : M.IsFiniteTypeOnSite) : N.IsFiniteTypeOnSite where
  locally_finitelyGenerated U := by
    obtain ⟨I, V, f, hcover, hgg⟩ := h.locally_finitelyGenerated U
    exact ⟨I, V, f, hcover, fun i =>
      hasFiniteGlobalGenerators_of_iso ((SheafOfModules.overFunctor R (V i)).mapIso e) (hgg i)⟩

end Transport

section Reindex

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- **Reindexing carries generation by finitely many global sections along.** -/
theorem hasFiniteGlobalGenerators_reindex (M : SheafOfModules.{w} R)
    (h : M.HasFiniteGlobalGenerators) :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).HasFiniteGlobalGenerators := by
  let φ : reindexRing J' e R ⟶
      (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R := 𝟙 _
  let F₀ := SheafOfModules.pushforward.{w} φ
  let eHi : SheafOfModules.{max u v w} R ≌ SheafOfModules.{max u v w} (reindexRing J' e R) :=
    reindexEquivalence e R
  let F := eHi.functor
  let _ : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  have hU : F₀.obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit (reindexRing J' e R) := Iso.refl _
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (SheafOfModules.unit (reindexRing J' e R)) :=
    GlobalPresentationTransport.pushforwardUliftIso.{u, v, w, max u v w} φ
        (SheafOfModules.unit R) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w} hU
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F₀.obj M) :=
    GlobalPresentationTransport.pushforwardUliftIso.{u, v, w, max u v w} φ M
  exact hasFiniteGlobalGenerators_of_functor (F₀ := F₀) (F := F) M hη₁ hηM h

/-- **Reindexing along an equivalence of ringed sites reflects generation by finitely many
global sections.**

This is `Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_of_functor` run at
the *inverse* of `Stacks.SheafOfModules.reindexEquivalence`.  As for finite presentation
(`Stacks.SheafOfModules.isFinitePresentation_of_reindex`) it is not the carrying direction
applied to `e.symm`, which would land the module over the twice-reindexed sheaf of rings; taking
the inverse functor of the one equivalence keeps the sheaf of rings on the nose.  The price is
that the inverse's structure map `Stacks.SheafOfModules.reindexBackSharp` is not the identity, so
its pushforward of the structure sheaf is only *isomorphic* to the structure sheaf — the
identification being the unit of the equivalence at
`Stacks.SheafOfModules.unit`, whose image under the reindexing functor is the structure sheaf of
the reindexed site on the nose. -/
theorem hasFiniteGlobalGenerators_of_reindex (M : SheafOfModules.{w} R)
    (h : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).HasFiniteGlobalGenerators) : M.HasFiniteGlobalGenerators := by
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} J J').obj (reindexRing J' e R) :=
    reindexBackSharp e R
  let F₀ := SheafOfModules.pushforward.{w} ψ
  let eLo : SheafOfModules.{w} R ≌ SheafOfModules.{w} (reindexRing J' e R) :=
    reindexEquivalence e R
  let eHi : SheafOfModules.{max u v w} R ≌ SheafOfModules.{max u v w} (reindexRing J' e R) :=
    reindexEquivalence e R
  let F := eHi.inverse
  let _ : F.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  have hU : F₀.obj (SheafOfModules.unit (reindexRing J' e R)) ≅ SheafOfModules.unit R :=
    (eLo.unitIso.app (SheafOfModules.unit R)).symm
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit (reindexRing J' e R))) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (SheafOfModules.unit R) :=
    GlobalPresentationTransport.pushforwardUliftIso.{u, v, w, max u v w} ψ
        (SheafOfModules.unit (reindexRing J' e R)) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w} hU
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (F₀.obj ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M)) :=
    GlobalPresentationTransport.pushforwardUliftIso.{u, v, w, max u v w} ψ _
  exact hasFiniteGlobalGenerators_of_iso (eLo.unitIso.app M).symm
    (hasFiniteGlobalGenerators_of_functor (F₀ := F₀) (F := F) _ hη₁ hηM h)

section Slice

variable [e.inverse.IsDenseSubsite J J']

omit [e.inverse.IsContinuous J J'] in
/-- Reindexing carries generation by finitely many global sections of the restriction to
`e.functor.obj V` to the restriction of the reindexing to `V`. -/
theorem hasFiniteGlobalGenerators_over_reindex (M : SheafOfModules.{w} R) (V : C')
    (h : (M.over (e.functor.obj V)).HasFiniteGlobalGenerators) :
    (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasFiniteGlobalGenerators := by
  rw [over_reindex_eq]
  exact hasFiniteGlobalGenerators_reindex (overSiteEquivalence e V)
    (R.over (e.functor.obj V)) (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- **Finite type on a site is carried along an equivalence of ringed sites.**  This is the
clause (5) of Stacks 03DL half of Stacks 03DM, for an equivalence of ringed sites. -/
theorem isFiniteTypeOnSite_reindex (M : SheafOfModules.{w} R) [hM : M.IsFiniteTypeOnSite] :
    ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsFiniteTypeOnSite where
  locally_finitelyGenerated V := by
    obtain ⟨I, W, g, hcov, hgen⟩ := hM.locally_finitelyGenerated (e.functor.obj V)
    exact ⟨I, fun i => e.inverse.obj (W i),
      fun i => e.inverse.map (g i) ≫ e.unitIso.inv.app V,
      Sieve.ofArrows_inverse_mem e g hcov,
      fun i => hasFiniteGlobalGenerators_over_reindex e R M _
        (hasFiniteGlobalGenerators_overMap M (e.counitIso.app (W i)).hom (hgen i))⟩

end Slice

section SliceReflect

variable [e.inverse.IsDenseSubsite J J'] [e.functor.IsDenseSubsite J' J]

omit [e.inverse.IsContinuous J J'] [Functor.IsDenseSubsite J' J e.functor] in
/-- Reindexing reflects generation by finitely many global sections of the restriction to a
slice: the restriction of `M` to `e.functor.obj V` is generated by finitely many global sections
as soon as the restriction of the reindexing to `V` is.

This is the slice form of
`Stacks.SheafOfModules.FiniteTypeTransport.hasFiniteGlobalGenerators_of_reindex`, reached through
`Stacks.SheafOfModules.over_reindex_eq`, which is an equality of modules and so needs no
comparison isomorphism. -/
theorem hasFiniteGlobalGenerators_over_of_reindex (M : SheafOfModules.{w} R) (V : C')
    (h : (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over
      V).HasFiniteGlobalGenerators) :
    (M.over (e.functor.obj V)).HasFiniteGlobalGenerators := by
  rw [over_reindex_eq] at h
  exact hasFiniteGlobalGenerators_of_reindex (overSiteEquivalence e V)
    (R.over (e.functor.obj V)) (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- **Finite type on a site is reflected by an equivalence of ringed sites.**  Together with
`Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex` this makes clause (5) of
Stacks 03DL invariant under an equivalence of ringed sites, which is the clause (5) half of
Stacks 03DM.

A covering family of `e.inverse.obj U` in `J'` is carried to one of `U` in `J` by
`CategoryTheory.Sieve.ofArrows_inverse_mem` read at `e.symm`, which is where the second
dense-subsite hypothesis is spent: the carrying direction transports a covering family by
`e.inverse` and this one by `e.functor`. -/
theorem isFiniteTypeOnSite_of_reindex (M : SheafOfModules.{w} R)
    (hN : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).IsFiniteTypeOnSite) : M.IsFiniteTypeOnSite where
  locally_finitelyGenerated U := by
    let : e.symm.inverse.IsDenseSubsite J' J :=
      inferInstanceAs (e.functor.IsDenseSubsite J' J)
    obtain ⟨I, W, g, hcov, hgen⟩ := hN.locally_finitelyGenerated (e.inverse.obj U)
    exact ⟨I, fun i => e.functor.obj (W i),
      fun i => e.functor.map (g i) ≫ e.counitIso.hom.app U,
      Sieve.ofArrows_inverse_mem e.symm g hcov,
      fun i => hasFiniteGlobalGenerators_over_of_reindex e R M (W i) (hgen i)⟩

/-- **Finite type on a site is invariant under an equivalence of ringed sites**, clause (5) of
Stacks 03DL in Stacks 03DM.  This is the finite-type companion of
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` and
`Stacks.SheafOfModules.isFinitePresentation_reindex_iff`. -/
theorem isFiniteTypeOnSite_reindex_iff (M : SheafOfModules.{w} R) :
    M.IsFiniteTypeOnSite ↔
      ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
        M).IsFiniteTypeOnSite :=
  ⟨fun h => isFiniteTypeOnSite_reindex (hM := h) e R M, isFiniteTypeOnSite_of_reindex e R M⟩

end SliceReflect

end Reindex

end Stacks.SheafOfModules.FiniteTypeTransport

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.FiniteTypeTransport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The transported module is of finite type on the small étale site of `yoneda.obj U`. -/
theorem isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence
    (M : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hM : SheafOfModules.IsQuasicoherent M) (hft : SheafOfModules.IsFiniteType M) :
    SheafOfModules.IsFiniteTypeOnSite
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨M, hM⟩).obj := by
  have : SheafOfModules.IsFiniteTypeOnSite
      ((AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M) :=
    AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property M
      (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType M hft)
  exact isFiniteTypeOnSite_reindex
    (J' := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (representedSchemeStructureSheaf B S hS U)
    ((AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M)

/-- **A finite-type quasi-coherent module on a scheme is of finite type on charts when read on
the small étale site of the algebraic space the scheme represents.** -/
theorem isFiniteTypeOnCharts_representedQuasicoherentSchemeEquivalence
    (M : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hM : SheafOfModules.IsQuasicoherent M) (hft : SheafOfModules.IsFiniteType M) :
    AlgebraicGeometry.Space.IsFiniteTypeOnCharts B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
      ((AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        ⟨M, hM⟩).obj :=
  isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS
    ⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩ _
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨M, hM⟩).property
    (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS U M hM hft)

end AlgebraicGeometry.Space

end
