module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# Quasi-coherence of a sheaf of modules is local on a covering family

Stacks 03DN asserts that each of the local conditions of Stacks 03DL may be tested on the
members of any family covering the final object.  This file proves the clause for
quasi-coherence: a sheaf of modules on a site is quasi-coherent exactly when its restrictions
to the members of some covering family are quasi-coherent, and exactly when those restrictions
admit global presentations.

Quasi-coherence is local by definition, so the whole content is that *having a global
presentation* is stable under restriction and comparison of slices.  A global presentation is
a cokernel of a map between coproducts of copies of the structure sheaf, all three expressed
by universal properties, so it is carried by any functor that preserves colimits and zero
morphisms and carries the structure sheaf to the structure sheaf: that is
`hasGlobalPresentation_map`.  Restriction along `h : X ⟶ Y` is such a functor — it is the
left adjoint `SheafOfModules.overFunctor` composed with the comparison of the iterated slice
over `Over.mk h` with the slice over `X` — which gives `hasGlobalPresentation_overMap`, and
with it both directions of both equivalences.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`:
  quasi-coherence is equivalent to quasi-coherence of the restrictions to the members of some
  covering family.  This is the equivalence of conditions (a) and (b) of Stacks 03DN for
  quasi-coherence.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`:
  quasi-coherence is equivalent to the existence of global presentations of those
  restrictions.  This is the equivalence of conditions (a) and (c).
* `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite'` and
  `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation'`: the same
  two equivalences with the universe of the module sections independent of the universe of the
  coefficient rings.
* `Stacks.SheafOfModules.isQuasicoherent_over`: **quasi-coherence is stable under restriction to
  a slice of the site**, with the universe of the module sections independent of the universe of
  the coefficient rings.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite` and a global presentation is
`SheafOfModules.HasGlobalPresentation`, both Stacks 03DL(6); no notion is introduced here.  The
statements are made for a sheaf of rings on an arbitrary site, which also covers the structure
sheaf of a ringed site, and `GrothendieckTopology.CoversTop` expresses that a family covers the
final object without choosing one.

The two equivalences are stated for a module whose sections lie in the universe of the
coefficient rings, because the direction which *produces* a quasi-coherent restriction on each
member of a covering family from quasi-coherence of the module passes through the slice at an
object twice.  `Stacks.SheafOfModules.isQuasicoherent_over` passes through it once, in the
direction that reads a presentation on an iterated slice off one on the slice at the underlying
object, and that direction is universe-free: the two universes are independent there, which is
what a module on the small étale site of an algebraic space needs, its sections living in a
universe containing the site while its coefficient rings do not.

A global presentation lives in the universe `max u v w`, which is why the transport lemma
`hasGlobalPresentation_map` takes two functors: the functor `F₀` at the module universe `w`,
whose image of `M` the conclusion is about, and the same functor `F` at the raised universe,
which is what actually moves the presentation.  The two are tied together by
`pushforwardUliftIso`, which says that restriction commutes with
`SheafOfModules.uliftForPresentation` — an objectwise identity.

The colimit-preservation hypothesis on restriction is obtained in
`overFunctor_preservesColimits` from left adjointness of the sheaf-level restriction, which
needs sheafification on the site and on the slice at the raised universe; both are supplied by
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`, which hold on every
site whose objects and morphisms lie below the universe of sections.  No sheafification
hypothesis therefore appears in the statements.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w s t

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)

/-- Precomposing the inclusions of a coproduct cofan with an isomorphism of the indexing
object leaves it a coproduct. -/
def isColimitCofan_precomposeIso
    {D : Type*} [Category D] {I : Type*} {A B Z : D}
    (e : A ≅ B) (f : I → (B ⟶ Z))
    (h : IsColimit (Cofan.mk Z f)) :
    IsColimit (Cofan.mk Z (fun i => e.hom ≫ f i)) := by
  refine Cofan.IsColimit.mk _ (fun s =>
    Cofan.IsColimit.desc h (fun i => e.inv ≫ s.inj i)) ?_ ?_
  · intro s i
    simpa [Category.assoc] using
      congrArg (fun g => e.hom ≫ g)
        (Cofan.IsColimit.fac h (fun i => e.inv ≫ s.inj i) i)
  · intro s m hm
    apply Cofan.IsColimit.hom_ext h
    intro i
    have hi := hm i
    dsimp at hi
    rw [Cofan.IsColimit.fac h (fun i => e.inv ≫ s.inj i) i]
    simpa [Category.assoc] using
      congrArg (fun g => e.inv ≫ g) hi

/-- Having a global presentation is carried along any functor of sheaves of modules that
preserves colimits and zero morphisms and carries the structure sheaf to the structure sheaf.

A global presentation lives in the universe `max u v w t`, so the transport takes two
functors: `F₀`, at the module universe, whose image of `M` the conclusion is about, and `F`,
the same functor at the raised universe, which is what moves the presentation.  The two are
tied together by the hypothesis `ηM`. -/
theorem hasGlobalPresentation_map (M : SheafOfModules.{t} R)
    {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{w}}
    {F₀ : SheafOfModules.{t} R ⥤ SheafOfModules.{t} R'}
    {F : SheafOfModules.{max u v w t} R ⥤ SheafOfModules.{max u v w t} R'}
    [PreservesColimitsOfSize.{max u v w t, max u v w t} F]
    [Functor.PreservesZeroMorphisms F]
    (η₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v t}
      (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v t}
        (SheafOfModules.unit R'))
    (ηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, t, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, t, max u v w} (F₀.obj M)) :
    M.HasGlobalPresentation → (F₀.obj M).HasGlobalPresentation := by
  classical
  let : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  rintro ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩
  let ι' : ∀ i : I, SheafOfModules.uliftForPresentation.{u, v, w, w, max u v t}
      (SheafOfModules.unit R') ⟶ F.obj P := fun i => η₁.inv ≫ F.map (ι i)
  let κ' : ∀ i : K, SheafOfModules.uliftForPresentation.{u, v, w, w, max u v t}
      (SheafOfModules.unit R') ⟶ F.obj Q := fun i => η₁.inv ≫ F.map (κ i)
  have hPmap : IsColimit (Cofan.mk (F.obj P) (fun i => F.map (ι i))) :=
    (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk P ι)).toFun
      (isColimitOfPreserves F hP.some)
  have hQmap : IsColimit (Cofan.mk (F.obj Q) (fun i => F.map (κ i))) :=
    (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk Q κ)).toFun
      (isColimitOfPreserves F hQ.some)
  have hP' : Nonempty (IsColimit (Cofan.mk (F.obj P) ι')) :=
    ⟨isColimitCofan_precomposeIso η₁.symm _ hPmap⟩
  have hQ' : Nonempty (IsColimit (Cofan.mk (F.obj Q) κ')) :=
    ⟨isColimitCofan_precomposeIso η₁.symm _ hQmap⟩
  let b' : F.obj P ⟶ SheafOfModules.uliftForPresentation.{u, v, w, t, max u v w}
      (F₀.obj M) := F.map b ≫ ηM.hom
  have hmap : F.map a ≫ F.map b = 0 := by simpa using congrArg F.map hab
  have hab' : F.map a ≫ b' = 0 := by simp [b', reassoc_of% hmap]
  let c' := CokernelCofork.ofπ b' hab'
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
        simp [c', b', d, i, i₁, i₂, parallelPairIsoMk,
          NatIso.ofComponents_inv_app]))).toFun
      (isColimitOfPreserves F hc.some)
  exact ⟨I, K, F.obj P, F.obj Q, ι', κ', hP', hQ', F.map a, b', hab', ⟨hc'⟩⟩

/-- Restriction of sheaves of modules along a continuous functor commutes with raising the
universe of the sections: both sides have the same sections over every object. -/
noncomputable def pushforwardUliftIso
    {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{w}} {F : C' ⥤ C}
    [Functor.IsContinuous F J' J]
    (φ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{w} J' J).obj R)
    (N : SheafOfModules.{s} R) :
    (SheafOfModules.pushforward.{max t s} φ).obj
        (SheafOfModules.uliftForPresentation.{u, v, w, s, t} N) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, s, t}
        ((SheafOfModules.pushforward.{s} φ).obj N) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso ?_
  exact PresheafOfModules.isoMk (fun X => Iso.refl _) (by
    intro X Y f
    ext x
    rfl)

private theorem iteratedSliceBackward_obj_eq
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R)
    (U : C) (f : Over U) :
    (SheafOfModules.pushforward.{t}
      (F := (Over.iteratedSliceEquiv f).functor)
      (S := (R.over U).over f) (R := R.over f.left)
      (𝟙 _ : ((R.over U).over f) ⟶
        ((Over.iteratedSliceEquiv f).functor.sheafPushforwardContinuous
          RingCat ((J.over U).over f) (J.over f.left)).obj (R.over f.left))).obj
      (M.over f.left) = (M.over U).over f :=
  rfl

-- Comparing the module functors unfolds the equivalence between iterated slice sites.
private theorem hasGlobalPresentation_iteratedSlice
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R)
    (U : C) (f : Over U) :
    ((M.over U).over f).HasGlobalPresentation → (M.over f.left).HasGlobalPresentation := by
  let E := Over.iteratedSliceEquiv f
  let ψ : (R.over f.left) ⟶
      (E.inverse.sheafPushforwardContinuous RingCat (J.over _) ((J.over _).over _)).obj
        ((R.over U).over f) := 𝟙 _
  let F₀ := SheafOfModules.pushforward.{t} ψ
  let e₀ : SheafOfModules.{t} (R.over f.left) ≌ SheafOfModules.{t} ((R.over U).over f) :=
    SheafOfModules.pushforwardPushforwardEquivalence E (𝟙 _) ψ
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  let F := SheafOfModules.pushforward.{max (max u v) v w t} ψ
  let eHi : SheafOfModules.{max (max u v) v w t} (R.over f.left) ≌
      SheafOfModules.{max (max u v) v w t} ((R.over U).over f) :=
    SheafOfModules.pushforwardPushforwardEquivalence E (𝟙 _) ψ
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  let : F.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, w,
      max (max u v) v t}
      (SheafOfModules.unit ((R.over U).over f))) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max (max u v) v t}
        (SheafOfModules.unit (R.over f.left)) :=
    pushforwardUliftIso.{max u v, v, w, w, max (max u v) v t} ψ
      (SheafOfModules.unit ((R.over U).over f))
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, t,
      max (max u v) v w} ((M.over U).over f)) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, t, max (max u v) v w}
        (F₀.obj ((M.over U).over f)) :=
    pushforwardUliftIso.{max u v, v, w, t, max (max u v) v w} ψ ((M.over U).over f)
  intro h
  have h' : (e₀.inverse.obj ((M.over U).over f)).HasGlobalPresentation :=
    hasGlobalPresentation_map (F₀ := F₀) (F := F) ((M.over U).over f) hη₁ hηM h
  rw [← iteratedSliceBackward_obj_eq M U f] at h'
  exact SheafOfModules.HasGlobalPresentation.of_iso (e₀.unitIso.app (M.over f.left)).symm h'

-- Comparing the module functors unfolds the equivalence between iterated slice sites.
private theorem hasGlobalPresentation_iteratedSlice_symm
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R)
    (U : C) (f : Over U) :
    (M.over f.left).HasGlobalPresentation → ((M.over U).over f).HasGlobalPresentation := by
  let E := Over.iteratedSliceEquiv f
  let φ : ((R.over U).over f) ⟶
      (E.functor.sheafPushforwardContinuous RingCat ((J.over U).over f)
        (J.over f.left)).obj
        (R.over f.left) := 𝟙 _
  let F₀ := SheafOfModules.pushforward.{t} φ
  let e₀ : SheafOfModules.{t} (R.over f.left) ≌ SheafOfModules.{t} ((R.over U).over f) :=
    SheafOfModules.pushforwardPushforwardEquivalence E φ (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  let F := SheafOfModules.pushforward.{max (max u v) v w t} φ
  let eHi : SheafOfModules.{max (max u v) v w t} (R.over f.left) ≌
      SheafOfModules.{max (max u v) v w t} ((R.over U).over f) :=
    SheafOfModules.pushforwardPushforwardEquivalence E φ (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  let : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, w,
      max (max u v) v t} (SheafOfModules.unit (R.over f.left))) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max (max u v) v t}
        (SheafOfModules.unit ((R.over U).over f)) :=
    pushforwardUliftIso.{max u v, v, w, w, max (max u v) v t} φ
      (SheafOfModules.unit (R.over f.left))
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, t,
      max (max u v) v w} (M.over f.left)) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, t, max (max u v) v w}
        (F₀.obj (M.over f.left)) :=
    pushforwardUliftIso.{max u v, v, w, t, max (max u v) v w} φ (M.over f.left)
  intro h
  have h' : (F₀.obj (M.over f.left)).HasGlobalPresentation :=
    hasGlobalPresentation_map (F₀ := F₀) (F := F) (M.over f.left) hη₁ hηM h
  rwa [iteratedSliceBackward_obj_eq M U f] at h'

/-- Restriction of sheaves of modules to a slice of the site preserves colimits: it is the
left adjoint of the pushforward along `CategoryTheory.Over.forget`, read through the faithful
inclusion of sheaves of modules into sheaves of abelian groups. -/
theorem overFunctor_preservesColimits
    (R : Sheaf J RingCat.{w}) (U : C) : PreservesColimitsOfSize.{max u v w t, max u v w t}
    (SheafOfModules.overFunctor.{max u v w t} R U) := by
  have : HasSheafify J AddCommGrpCat.{max u v w t} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w t, v, u} J
  have : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w t} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w t, u, v} J
  have : HasSheafify (J.over U) AddCommGrpCat.{max u v w t} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w t, v, max u v} (J.over U)
  have : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v w t} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w t,
      max u v, v} (J.over U)
  let F := SheafOfModules.overFunctor.{max u v w t} R U
  let G := SheafOfModules.toSheaf.{max u v w t} (R.over U)
  let H := (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{max u v w t} (J.over U) J
  let : H.IsLeftAdjoint :=
    ((Over.forget U).sheafAdjunctionCocontinuous
      AddCommGrpCat.{max u v w t} (J.over U) J).isLeftAdjoint
  let : ReflectsColimitsOfSize.{max u v w t, max u v w t} G :=
    reflectsColimits_of_reflectsIsomorphisms
  have e : F ⋙ G ≅ SheafOfModules.toSheaf.{max u v w t} R ⋙ H := Iso.refl _
  let : PreservesColimitsOfSize.{max u v w t, max u v w t} (F ⋙ G) :=
    preservesColimits_of_natIso e.symm
  exact preservesColimits_of_reflects_of_preserves F G

/-- For a morphism `f : X ⟶ Y` of the site, if the restriction `M.over Y` of a sheaf of modules
`M` has a global presentation, then so does the restriction `M.over X`. -/
theorem hasGlobalPresentation_overMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R)
    {X Y : C} (f : X ⟶ Y) :
    (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation := by
  let T : Over Y := Over.mk f
  let R' := R.over Y
  let φ : R'.over T ⟶ (Over.forget T).sheafPushforwardContinuous RingCat
      ((J.over Y).over T) (J.over Y) |>.obj R' := 𝟙 _
  let F₀ := SheafOfModules.overFunctor.{t} R' T
  let F := SheafOfModules.overFunctor.{max (max u v) v w t} R' T
  let : PreservesColimitsOfSize.{max u v w t, max u v w t} F :=
    overFunctor_preservesColimits.{max u v, v, w, t} R' T
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : (SheafOfModules.overFunctor.{w} R' T).obj (SheafOfModules.unit R') ≅
      SheafOfModules.unit (R'.over T) := Iso.refl _
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, w,
      max (max u v) v t} (SheafOfModules.unit R')) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max (max u v) v t}
        (SheafOfModules.unit (R'.over T)) :=
    pushforwardUliftIso.{max u v, v, w, w, max u v t} φ
      (SheafOfModules.unit R') ≪≫
      SheafOfModules.uliftForPresentationMapIso.{max u v, v, w, w, max u v t} hU
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, t,
      max (max u v) v w} (M.over Y)) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, t, max (max u v) v w}
        (F₀.obj (M.over Y)) :=
    pushforwardUliftIso.{max u v, v, w, t, max u v w} φ (M.over Y)
  intro h
  exact hasGlobalPresentation_iteratedSlice M Y T
    (hasGlobalPresentation_map (F₀ := F₀) (F := F) (M.over Y) hη₁ hηM h)

private theorem isQuasicoherentOnSite_of_hasGlobalPresentation'
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R)
    (U : C) (hM : (M.over U).HasGlobalPresentation) :
    (M.over U).IsQuasicoherentOnSite := by
  constructor
  intro f
  let T : Over U := Over.mk (𝟙 U)
  let α : f ⟶ T := Over.homMk f.hom (by simp [T])
  refine ⟨ULift.{max u v} PUnit, fun _ => f, fun _ => 𝟙 f,
    (J.over U).superset_covering (fun Z g _ => ?_) ((J.over U).top_mem f), fun _ =>
      hasGlobalPresentation_overMap (M.over U) α
        (hasGlobalPresentation_iteratedSlice_symm M U T hM)⟩
  rw [Sieve.mem_ofArrows_iff]
  exact ⟨ULift.up PUnit.unit, g, by simp⟩

/-- **Quasi-coherence is stable under restriction to a slice of the site.**  This is the easy
half of the clause of Stacks 03DN for quasi-coherence: a covering of an object of the slice at
`U` is the covering of its underlying object, read in the slice, and a global presentation on a
member travels to the iterated slice.

The universe of the module sections is independent of the universe of the coefficient rings. -/
theorem isQuasicoherent_over
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{t} R)
    (hM : M.IsQuasicoherentOnSite) (U : C) :
    (M.over U).IsQuasicoherentOnSite := by
  constructor
  intro f
  obtain ⟨I, V, g, hcover, hpres⟩ := hM.locally_hasGlobalPresentation f.left
  let V' : I → Over U := fun i => Over.mk (g i ≫ f.hom)
  let α : ∀ i, V' i ⟶ f := fun i => Over.homMk (g i) (by simp [V'])
  refine ⟨I, V', α, ?_, fun i => ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [V', α] using hcover
  · exact hasGlobalPresentation_iteratedSlice_symm M U (V' i) (hpres i)

/-- **Stacks 03DN, quasi-coherence**, with the universe of the module sections independent of the
universe of the coefficient rings: a sheaf of modules is quasi-coherent if and only if its
restriction to each member of some covering family of the final object is quasi-coherent.  This
is `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite` with the
module universe freed. -/
theorem isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite'
    (M : SheafOfModules.{t} R) :
    M.IsQuasicoherentOnSite ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, (M.over (U i)).IsQuasicoherentOnSite := by
  classical
  constructor
  · intro hM
    exact ⟨C, fun U => U, fun W => J.superset_covering (fun V _ _ => ⟨V, ⟨𝟙 V⟩⟩) (J.top_mem W),
      fun U => isQuasicoherent_over M hM U⟩
  · rintro ⟨I, U, hU, hQ⟩
    choose K Y g hcover hpres using fun (i : I) (f : Over (U i)) =>
      (hQ i).locally_hasGlobalPresentation f
    have hY : ∀ i : I, (J.over (U i)).CoversTop fun j : Σ f, K i f => Y i j.1 j.2 := by
      intro i Z
      have hrange : Set.range (Y i Z) ⊆ Set.range fun j : Σ f, K i f => Y i j.1 j.2 := by
        rintro x ⟨j, rfl⟩
        exact ⟨⟨Z, j⟩, rfl⟩
      exact (J.over (U i)).superset_covering
        ((Sieve.ofArrows_le_ofObjects (Y i Z) (g i Z)).trans (Sieve.ofObjects_mono hrange))
        (hcover i Z)
    let Z : (Σ i : I, Σ f : Over (U i), K i f) → C := fun k => (Y k.1 k.2.1 k.2.2).left
    have hZ : J.CoversTop Z := GrothendieckTopology.CoversTop.over hU hY
    have hpres' : ∀ k, (M.over (Z k)).HasGlobalPresentation := fun k =>
      hasGlobalPresentation_iteratedSlice M (U k.1) (Y k.1 k.2.1 k.2.2)
        (hpres k.1 k.2.1 k.2.2)
    refine ⟨fun W => ?_⟩
    let S := Sieve.ofObjects Z W
    let A : Type (max u v) := {f : Over W // S f.hom}
    let V : A → C := fun a => a.1.left
    let g : ∀ a, V a ⟶ W := fun a => a.1.hom
    refine ⟨A, V, g, ?_, ?_⟩
    · refine J.superset_covering (fun X f hf => ?_) (hZ W)
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨⟨Over.mk f, hf⟩, 𝟙 X, by simp [V, g]⟩
    · intro a
      obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff Z a.1.hom).mp a.2
      exact hasGlobalPresentation_overMap M b (hpres' k)

/-- **Stacks 03DN, quasi-coherence**, with the universe of the module sections independent of the
universe of the coefficient rings: a sheaf of modules is quasi-coherent if and only if its
restriction to each member of some covering family of the final object has a global
presentation.  This is
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation` with the
module universe freed. -/
theorem isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation'
    (M : SheafOfModules.{t} R) :
    M.IsQuasicoherentOnSite ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, (M.over (U i)).HasGlobalPresentation := by
  classical
  constructor
  · intro hM
    let T : Set C := {V | (M.over V).HasGlobalPresentation}
    let U : T → C := fun i => i.1
    refine ⟨T, U, ?_, fun i => i.2⟩
    intro W
    obtain ⟨I, V, f, hV, hP⟩ := hM.locally_hasGlobalPresentation W
    have hRange : Set.range V ⊆ Set.range U := by
      rintro x ⟨i, rfl⟩
      exact ⟨⟨V i, hP i⟩, rfl⟩
    exact J.superset_covering
      ((Sieve.ofArrows_le_ofObjects V f).trans (Sieve.ofObjects_mono hRange)) hV
  · rintro ⟨I, U, hU, hP⟩
    exact (isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite' M).2
      ⟨I, U, hU, fun i => isQuasicoherentOnSite_of_hasGlobalPresentation' M (U i) (hP i)⟩

/-- **Stacks 03DN, quasi-coherence.** A sheaf of modules is quasi-coherent if and only if its
restriction to each member of some covering family of the final object is quasi-coherent. -/
@[stacks 03DN "quasi_coherent"]
theorem isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite :
    M.IsQuasicoherentOnSite ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, (M.over (U i)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite' M

/-- **Stacks 03DN, quasi-coherence.** A sheaf of modules is quasi-coherent if and only if its
restriction to each member of some covering family of the final object has a global
presentation. -/
@[stacks 03DN "quasi_coherent"]
theorem isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation :
    M.IsQuasicoherentOnSite ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, (M.over (U i)).HasGlobalPresentation :=
  isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation' M

end Stacks.SheafOfModules

end
