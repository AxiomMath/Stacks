module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftTensorPresheaf

/-!
# Transporting a global presentation, and restricting one

`SheafOfModules.HasGlobalPresentation` is a cokernel of a map between coproducts of copies of the
universe-lifted structure sheaf, all three specified by their universal properties.  Any functor
that preserves colimits and zero morphisms and carries the lifted structure sheaf to the lifted
structure sheaf therefore carries a global presentation to one; that is
`hasGlobalPresentation_of_functor`.  Its one application here is restriction along an arrow of
the site, which gives `hasGlobalPresentation_overMap`: a global presentation of the restriction
of a module to a slice restricts further along any arrow into that slice's base.

Restriction stability is what lets two local conditions be tested on a common refinement of two
coverings, which is the step every statement "a tensor product inherits a local property" takes.

## Main results

* `Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_of_functor`: a global
  presentation is carried by a colimit-preserving functor matching the two structure sheaves.
* `Stacks.SheafOfModules.GlobalPresentationTransport.pushforwardUliftIso`: restriction along a
  continuous functor commutes with the universe lift of the sections.
* `Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap`: a global
  presentation restricts along an arrow of the site.

## Implementation notes

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence` proves both
statements for its own use, as
`hasGlobalPresentation_map` and `hasGlobalPresentation_overMap`, and both are `private` there, so
neither is importable; they are proved again here.  The route taken is shorter than that one:
restriction between two slice sites is `SheafOfModules.overMap`, which is a single pushforward
and is known to preserve colimits by
`Stacks.SheafOfModules.overMap_preservesColimits`, so the comparison of an iterated slice with a
slice that the other proof needs does not arise.

The colimit preservation is used at the module universe `max u v w` in which a global
presentation lives, over a ring sheaf at `w`; that is why
`Stacks.SheafOfModules.overMap_preservesColimits` is stated with the universe of the ring sheaf
independent of the universe of the module sections.

The two sheafification instances on the slice topologies at the raised universe are supplied by
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`, which hold on every
site whose objects and morphisms lie below the universe of sections; so no sheafification
hypothesis appears in the statements.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace Stacks.SheafOfModules.GlobalPresentationTransport

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Precomposing every leg of a colimit cofan `Cofan.mk Z f` with the isomorphism `e : A ≅ B`
gives again a colimit cofan. -/
public def isColimitCofanPrecompose
    {D : Type*} [Category D] {I : Type*} {A B Z : D}
    (e : A ≅ B) (f : I → (B ⟶ Z)) (h : IsColimit (Cofan.mk Z f)) :
    IsColimit (Cofan.mk Z (fun i ↦ e.hom ≫ f i)) := by
  refine Cofan.IsColimit.mk _ (fun s ↦ Cofan.IsColimit.desc h (fun i ↦ e.inv ≫ s.inj i)) ?_ ?_
  · intro s i
    simpa [Category.assoc] using
      congrArg (fun g ↦ e.hom ≫ g) (Cofan.IsColimit.fac h (fun i ↦ e.inv ≫ s.inj i) i)
  · intro s m hm
    apply Cofan.IsColimit.hom_ext h
    intro i
    have hi := hm i
    dsimp at hi
    rw [Cofan.IsColimit.fac h (fun i ↦ e.inv ≫ s.inj i) i]
    simpa [Category.assoc] using congrArg (fun g ↦ e.inv ≫ g) hi

/-- **A global presentation is carried by a functor that preserves colimits and zero morphisms
and carries the universe-lifted structure sheaf to the universe-lifted structure sheaf.** -/
theorem hasGlobalPresentation_of_functor
    {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}}
    (M : SheafOfModules.{w} R)
    {F₀ : SheafOfModules.{w} R ⥤ SheafOfModules.{w} R'}
    {F : SheafOfModules.{max u v w} R ⥤ SheafOfModules.{max u v w} R'}
    (hF : PreservesColimitsOfSize.{max u v w, max u v w} F)
    (hF₀ : F.PreservesZeroMorphisms)
    (η₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (SheafOfModules.unit R'))
    (ηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F₀.obj M)) :
    M.HasGlobalPresentation → (F₀.obj M).HasGlobalPresentation := by
  classical
  have := hF
  have := hF₀
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  rintro ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩
  have key : ∀ (S : SheafOfModules.{max u v w} R) (T : Type (max u v w))
      (g : T → (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (SheafOfModules.unit R) ⟶ S)), IsColimit (Cofan.mk S g) →
      Nonempty (IsColimit (Cofan.mk (F.obj S) (fun i ↦ η₁.inv ≫ F.map (g i)))) :=
    fun S T g h ↦ ⟨isColimitCofanPrecompose η₁.symm _
      ((Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk S g)).toFun (isColimitOfPreserves F h))⟩
  have hP' := key P I ι hP.some
  have hQ' := key Q K κ hQ.some
  let b' : F.obj P ⟶ SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F₀.obj M) :=
    F.map b ≫ ηM.hom
  have hmap : F.map a ≫ F.map b = 0 := by simpa using congrArg F.map hab
  have hab' : F.map a ≫ b' = 0 := by simp [b', reassoc_of% hmap]
  let c' := CokernelCofork.ofπ b' hab'
  have hcMap : IsColimit (F.mapCocone (CokernelCofork.ofπ b hab)) :=
    isColimitOfPreserves F hc.some
  have hc' : IsColimit c' := by
    let d := (parallelPair a 0) ⋙ F
    let i₁ : d ≅ parallelPair (F.map a) (F.map 0) := by
      refine NatIso.ofComponents (fun j ↦ ?_) ?_
      · cases j <;> exact Iso.refl _
      rintro _ _ (_ | _ | _) <;> simp [d]
    let i₂ : parallelPair (F.map a) (F.map 0) ≅ parallelPair (F.map a) 0 :=
      parallelPairIsoMk (Iso.refl (F.obj Q)) (Iso.refl (F.obj P))
    let i := i₁ ≪≫ i₂
    exact (IsColimit.equivOfNatIsoOfIso i (F.mapCocone (CokernelCofork.ofπ b hab)) c'
      (Cocone.ext ηM (by rintro (_ | _) <;>
        simp [c', b', d, i, i₁, i₂, parallelPairIsoMk, NatIso.ofComponents_inv_app]))).toFun hcMap
  exact ⟨I, K, F.obj P, F.obj Q, _, _, hP', hQ', F.map a, b', hab', ⟨hc'⟩⟩

end Transport

section Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Restriction along a continuous functor commutes with the universe lift of the sections,
which is computed objectwise. -/
noncomputable def pushforwardUliftIso
    {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{w}} {G : C' ⥤ C} [Functor.IsContinuous G J' J]
    (φ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{w} J' J).obj R)
    (N : SheafOfModules.{w} R) :
    (SheafOfModules.pushforward.{max t w} φ).obj
        (SheafOfModules.uliftForPresentation.{u, v, w, w, t} N) ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, t}
        ((SheafOfModules.pushforward.{w} φ).obj N) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y f; ext x; rfl))

/-- **A global presentation restricts along an arrow of the site.** -/
theorem hasGlobalPresentation_overMap (M : SheafOfModules.{w} R) {X Y : C} (f : X ⟶ Y)
    (h : (M.over Y).HasGlobalPresentation) : (M.over X).HasGlobalPresentation := by
  have h1 : HasSheafify (J.over X) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over X)
  have h2 : (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (J.over X)
  have h3 : HasSheafify (J.over Y) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over Y)
  have h4 : (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (J.over Y)
  have hF : PreservesColimitsOfSize.{max u v w, max u v w}
      (SheafOfModules.overMap.{max u v w} R f) :=
    Stacks.SheafOfModules.overMap_preservesColimits.{u, v, max u v w, w} R f
  have hF₀ : (SheafOfModules.overMap.{max u v w} R f).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have hη₁ : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over Y))) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (SheafOfModules.unit (R.over X)) :=
    pushforwardUliftIso.{max u v, v, w, max u v w} (Sheaf.pushforwardOverMapIso R f).inv
        (SheafOfModules.unit (R.over Y)) ≪≫
      SheafOfModules.uliftForPresentationMapIso.{max u v, v, w, w, max u v w}
        (SheafOfModules.overMapUnitIso f)
  have hηM : (SheafOfModules.overMap.{max u v w} R f).obj
      (SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} (M.over Y)) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        ((SheafOfModules.overMap.{w} R f).obj (M.over Y)) :=
    pushforwardUliftIso.{max u v, v, w, max u v w} (Sheaf.pushforwardOverMapIso R f).inv
      (M.over Y)
  exact SheafOfModules.HasGlobalPresentation.of_iso ((SheafOfModules.overFunctorMap R f).app M)
    (hasGlobalPresentation_of_functor.{max u v, v, w} (M.over Y)
      (F₀ := SheafOfModules.overMap.{w} R f)
      (F := SheafOfModules.overMap.{max u v w} R f) hF hF₀ hη₁ hηM h)

end Restriction

end Stacks.SheafOfModules.GlobalPresentationTransport

end
