module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous

/-!
# Quasi-coherent on the big crystalline site implies locally quasi-coherent

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation.  [Stacks, Tag 07IT] characterises quasi-coherence of `F` by two conditions read on the
restrictions `F_T` to the ambient schemes of the objects `(U, T, δ)`: that each `F_T` is a
quasi-coherent `𝒪_T`-module, which is local quasi-coherence in the sense of [Stacks, Tag 07IS],
and that `F` is a crystal.  This file proves the first of those two conditions from
quasi-coherence, that is, the implication (1) ⇒ (2)(a) of the tag:

> quasi-coherent on `CRIS(X/S)` implies locally quasi-coherent.

The restriction `F_T` is the pushforward of `F` along
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor`, the functor from the
opens of `T` to `CRIS(X/S)` sending `W` to `(U ∩ W, W, δ|_W)`, and that functor is both
continuous and cocontinuous.  Cocontinuity refines a crystalline covering of an object by the
restrictions of that object to an open cover of its ambient scheme, which is the content of
`Crystalline.GlobalCrystallineSituation.exists_hasGlobalPresentation_restrictOpen`; continuity
carries the global presentation found there from the localised crystalline site down to the
Zariski site of the open.

## The index universe

Carrying a global presentation along the restriction functor is not an instance of any transport
lemma of the library, because the two sites have their objects in different universes: the
objects of `CRIS(X/S)` lie in `Type (u + 1)` while the opens of `T` lie in `Type u`, and
`SheafOfModules.HasGlobalPresentation` indexes its coproducts by types in the universe
`max u v r m` containing the site, so the transport must *shrink* the index types from
`Type (u + 1)` to `Type u`.  The shrinking is
`SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'`, which lowers the universe of the
sections of a sheaf of modules by an arbitrary amount: raising the sections of the restricted
module to `Type (u + 1)` puts both presentations in one index universe, the presentation is
carried across in that universe, and the result is then lowered again.  That is
`Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_pushforward` below, the transport
of a global presentation along a continuous functor between two sites whose objects and morphisms
lie in unrelated universes.

## Main results

* `Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_of_functor` — a global
  presentation is carried by a colimit-preserving functor matching the two universe-lifted
  structure sheaves, with the two sites allowed to live in unrelated universes.
* `Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_pushforward` — **a global
  presentation is carried by restriction along a continuous functor and an isomorphism of
  structure sheaves**, again across unrelated universes.
* `Crystalline.GlobalCrystallineSituation.Thickening.isLimitPullbackConeRestrictOpen` — the
  restrictions to the opens of the ambient scheme preserve pullbacks, hence
  `Crystalline.GlobalCrystallineSituation.Thickening.isContinuous_restrictOpenOverFunctor`: the
  localised functor
  `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenOverFunctor` is continuous.
* `Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_moduleRestrictionSheaf_over` — a
  global presentation of `F` on the localised crystalline site over `(U ∩ V, V, δ|_V)` restricts
  to one of `F_T` on the Zariski site localised at `V`.
* `Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` —
  **[Stacks, Tag 07IT] for `𝒞 = CRIS(X/S)`, the implication (1) ⇒ (2)(a): a quasi-coherent sheaf
  of `𝒪_{X/S}`-modules is locally quasi-coherent.**

## Implementation notes

The transport across unrelated universes is stated at the section universe
`max u₁ v₁ u₂ v₂ r m`, which contains both sites: there the two index universes of a global
presentation, `max u₁ v₁ r` and `max u₂ v₂ r` applied to that section universe, both collapse to
it, so one functor between sheaves of modules at a single section universe moves the presentation.
The two lift amounts that the predicate itself applies to the presented module on the two sides
still differ, and `Stacks.SheafOfModules.MixedObjectUniverse.pushforwardUliftIso₂` is the
comparison that absorbs that difference; at equal amounts the comparison is the identity on
sections, which is `Stacks.SheafOfModules.MixedObjectUniverse.pushforwardUliftIso`.

Continuity of the localised restriction functor is obtained from
`CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks`, whose hypothesis is that
the opens of the ambient scheme have pullbacks — they are a complete lattice — and that the
restriction functor preserves them.  The latter is the statement that the restriction of an
object to `V ⊓ W` is the fibre product of its restrictions to `V` and to `W`, and it is proved
from the same two facts as the two halves of continuity of the restriction functor itself: a
morphism whose ambient image lies in an open factors through the restriction to that open
(`Crystalline.GlobalCrystallineSituation.Thickening.liftRestrictOpen`), and the structure
morphism of a restriction is a monomorphism.  Representable flatness, the other sufficient
condition for continuity of `Over.post`, is unavailable here: the structured arrow categories can
be empty, since an object of `CRIS(X/S)` need admit no morphism to the object being restricted.

[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike; everything in
this file is about the big site, and the same implication for the small site is
`Crystalline.GlobalCrystallineSituation.SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`
of `StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal`, which reuses
the universe transport proved here and redoes everything that mentions the site.  It does not
follow from the statement proved here: a sheaf of modules on `Cris(X/S)` is in general not the
restriction of one on `CRIS(X/S)`.

The other half of this implication, (1) ⇒ (2)(b) — that a quasi-coherent module is a crystal — is
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal` for this site,
and `Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal` for the small one.
The
converse implication (2) ⇒ (1) is a separate statement.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.SheafOfModules.MixedObjectUniverse

universe u₁ v₁ u₂ v₂ r m

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {R' : Sheaf K RingCat.{r}}

universe t

/-- Restriction along a continuous functor commutes with the universe lift of the sections, both
being computed objectwise on sections.  The two sites are allowed to have their objects and their
morphisms in unrelated universes, which is what distinguishes this from
`Stacks.SheafOfModules.GlobalPresentationTransport.pushforwardUliftIso`. -/
noncomputable def pushforwardUliftIso {G : D ⥤ C} [G.IsContinuous K J]
    (φ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R) (N : SheafOfModules.{m} R) :
    (SheafOfModules.pushforward.{max t m} φ).obj
        (SheafOfModules.uliftForPresentation.{u₁, v₁, r, m, t} N) ≅
      SheafOfModules.uliftForPresentation.{u₂, v₂, r, m, t}
        ((SheafOfModules.pushforward.{m} φ).obj N) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y f; ext x; rfl))

/-- Restriction along a continuous functor, compared with the universe lift of the sections at
the two lift amounts that a global presentation applies to the presented module on the two sides.
Those amounts are `max u₁ v₁ r` and `max u₂ v₂ r`, which differ, but both leave the universe
`max u₁ v₁ u₂ v₂ r m` of the sections unchanged, so the comparison is the shuffle of two universe
lifts of one and the same module. -/
noncomputable def pushforwardUliftIso₂ {G : D ⥤ C} [G.IsContinuous K J]
    (φ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R)
    (N : SheafOfModules.{max u₁ v₁ u₂ v₂ r m} R) :
    (SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ r m} φ).obj
        (SheafOfModules.uliftForPresentation.{u₁, v₁, r,
          max u₁ v₁ u₂ v₂ r m, max u₁ v₁ r} N) ≅
      SheafOfModules.uliftForPresentation.{u₂, v₂, r,
        max u₁ v₁ u₂ v₂ r m, max u₂ v₂ r}
          ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ r m} φ).obj N) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun X ↦ (ULift.moduleEquiv (R := R'.obj.obj X)
        (M := ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ r m} φ).obj N).val.obj X)).trans
          (ULift.moduleEquiv (R := R'.obj.obj X)
            (M := ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ r m}
              φ).obj N).val.obj X)).symm |>.toModuleIso)
      (by intro X Y f; ext x; rfl))

/-- **A global presentation is carried by a functor between sheaves of modules on two sites with
objects and morphisms in unrelated universes**, provided the functor preserves colimits and zero
morphisms and matches the two universe-lifted structure sheaves.

The module is taken at the section universe `max u₁ v₁ u₂ v₂ r m`, which contains both sites; a
global presentation of a module with sections there is indexed by that same universe on either
site, so a single functor moves the presentation and no second copy of it at a raised universe is
needed, in contrast to
`Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_of_functor`. -/
theorem hasGlobalPresentation_of_functor
    (N : SheafOfModules.{max u₁ v₁ u₂ v₂ r m} R)
    {F : SheafOfModules.{max u₁ v₁ u₂ v₂ r m} R ⥤ SheafOfModules.{max u₁ v₁ u₂ v₂ r m} R'}
    (hF : PreservesColimitsOfSize.{max u₁ v₁ u₂ v₂ r m, max u₁ v₁ u₂ v₂ r m} F)
    (hF₀ : F.PreservesZeroMorphisms)
    (η₁ : F.obj (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ u₂ v₂ r m}
        (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u₂, v₂, r, r, max u₁ v₁ u₂ v₂ r m}
        (SheafOfModules.unit R'))
    (ηN : F.obj (SheafOfModules.uliftForPresentation.{u₁, v₁, r,
        max u₁ v₁ u₂ v₂ r m, max u₁ v₁ r} N) ≅
      SheafOfModules.uliftForPresentation.{u₂, v₂, r,
        max u₁ v₁ u₂ v₂ r m, max u₂ v₂ r} (F.obj N))
    (h : N.HasGlobalPresentation) : (F.obj N).HasGlobalPresentation := by
  classical
  have := hF
  have := hF₀
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  obtain ⟨I, L, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := h
  let ι' : ∀ _ : I, SheafOfModules.uliftForPresentation.{u₂, v₂, r, r,
      max u₁ v₁ u₂ v₂ r m} (SheafOfModules.unit R') ⟶ F.obj P := fun i ↦ η₁.inv ≫ F.map (ι i)
  let κ' : ∀ _ : L, SheafOfModules.uliftForPresentation.{u₂, v₂, r, r,
      max u₁ v₁ u₂ v₂ r m} (SheafOfModules.unit R') ⟶ F.obj Q := fun i ↦ η₁.inv ≫ F.map (κ i)
  have hPmap : IsColimit (Cofan.mk (F.obj P) (fun i ↦ F.map (ι i))) :=
    (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk P ι)).toFun (isColimitOfPreserves F hP.some)
  have hQmap : IsColimit (Cofan.mk (F.obj Q) (fun i ↦ F.map (κ i))) :=
    (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk Q κ)).toFun (isColimitOfPreserves F hQ.some)
  have hP' : Nonempty (IsColimit (Cofan.mk (F.obj P) ι')) :=
    ⟨Stacks.SheafOfModules.isColimitCofan_precomposeIso η₁.symm _ hPmap⟩
  have hQ' : Nonempty (IsColimit (Cofan.mk (F.obj Q) κ')) :=
    ⟨Stacks.SheafOfModules.isColimitCofan_precomposeIso η₁.symm _ hQmap⟩
  let b' : F.obj P ⟶ SheafOfModules.uliftForPresentation.{u₂, v₂, r,
      max u₁ v₁ u₂ v₂ r m, max u₂ v₂ r} (F.obj N) := F.map b ≫ ηN.hom
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
      (Cocone.ext ηN (by rintro (_ | _) <;>
        simp [c', b', d, i, i₁, i₂, parallelPairIsoMk, NatIso.ofComponents_inv_app]))).toFun hcMap
  exact ⟨I, L, F.obj P, F.obj Q, ι', κ', hP', hQ', F.map a, b', hab', ⟨hc'⟩⟩

/-- **A global presentation is carried by restriction along a continuous functor and an
isomorphism of structure sheaves**, with the two sites allowed to have their objects and their
morphisms in unrelated universes.

The index universe of the conclusion can be smaller than that of the hypothesis, so this is a
genuine shrinking of the index types of a presentation and not only a transport: the sections of
the module are first raised to the universe containing both sites, where
`Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_of_functor` applies, and are
then lowered again by
`SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'`. -/
theorem hasGlobalPresentation_pushforward {G : D ⥤ C} [G.IsContinuous K J]
    (φ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{r} K J).obj R) [IsIso φ]
    (M : SheafOfModules.{m} R)
    (hF : PreservesColimitsOfSize.{max u₁ v₁ u₂ v₂ r m, max u₁ v₁ u₂ v₂ r m}
      (SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ r m} φ))
    (hM : M.HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{m} φ).obj M).HasGlobalPresentation := by
  have hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
    have : IsIso ((sheafToPresheaf K AddCommGrpCat.{r}).map
        ((SheafOfModules.toSheaf R').map (SheafOfModules.unitToPushforwardObjUnit φ))) := by
      change IsIso (Functor.whiskerRight φ.hom (forget₂ RingCat.{r} AddCommGrpCat.{r}))
      infer_instance
    have : IsIso ((SheafOfModules.toSheaf R').map
        (SheafOfModules.unitToPushforwardObjUnit φ)) :=
      isIso_of_reflects_iso _ (sheafToPresheaf K AddCommGrpCat.{r})
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R')
  have hzero : (SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ r m} φ).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext X x; rfl⟩
  have hN : (SheafOfModules.uliftForPresentation.{u₁, v₁, r, m,
      max u₁ v₁ u₂ v₂ r m} M).HasGlobalPresentation :=
    SheafOfModules.hasGlobalPresentation_uliftForPresentation'.{u₁, v₁, r, m,
      max u₁ v₁ u₂ v₂ r m} hM
  have hres := hasGlobalPresentation_of_functor.{u₁, v₁, u₂, v₂, r, m}
    (R' := R') (SheafOfModules.uliftForPresentation.{u₁, v₁, r, m, max u₁ v₁ u₂ v₂ r m} M)
    (F := SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ r m} φ) hF hzero
    (pushforwardUliftIso.{u₁, v₁, u₂, v₂, r, r, max u₁ v₁ u₂ v₂ r m} φ (SheafOfModules.unit R) ≪≫
      SheafOfModules.uliftForPresentationMapIso
        (asIso (SheafOfModules.unitToPushforwardObjUnit φ)).symm)
    (pushforwardUliftIso₂.{u₁, v₁, u₂, v₂, r, m} φ _) hN
  exact SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'.{u₂, v₂, r, m,
    max u₁ v₁ u₂ v₂ r m} (SheafOfModules.HasGlobalPresentation.of_iso
      (pushforwardUliftIso.{u₁, v₁, u₂, v₂, r, m, max u₁ v₁ u₂ v₂ r m} φ M) hres)

end Stacks.SheafOfModules.MixedObjectUniverse

namespace Crystalline.GlobalCrystallineSituation

universe u

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

section Pullbacks

variable (A : Thickening S) {V W Z : A.thickening.target.scheme.Opens}

/-- The restriction functor sends the two inclusions of an intersection into a commuting square,
both composites being the restriction to the intersection of the two opens. -/
theorem restrictOpenFunctor_map_inf_comm (f : V ⟶ Z) (g : W ⟶ Z) :
    A.restrictOpenFunctor.map (homOfLE (inf_le_left : V ⊓ W ≤ V)) ≫
        A.restrictOpenFunctor.map f =
      A.restrictOpenFunctor.map (homOfLE (inf_le_right : V ⊓ W ≤ W)) ≫
        A.restrictOpenFunctor.map g := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The intersection of two opens of a scheme is their fibre product over any open containing
both: the opens of a scheme form a complete lattice, where a pullback is an infimum and all
morphisms between two objects are equal. -/
noncomputable def isLimitPullbackConeOpens (f : V ⟶ Z) (g : W ⟶ Z) :
    IsLimit (PullbackCone.mk (homOfLE (inf_le_left : V ⊓ W ≤ V))
      (homOfLE (inf_le_right : V ⊓ W ≤ W)) (Subsingleton.elim _ _ :
        homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ f = homOfLE inf_le_right ≫ g)) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ ↦ Subsingleton.elim _ _) (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)

/-- **The two legs of a cone on the restrictions to two opens agree after composition with the
structure morphisms.**  Both composites are the morphism to the object itself through the
restriction to the open containing both. -/
theorem comp_restrictOpenHom_eq_of_pullbackCone_condition (f : V ⟶ Z) (g : W ⟶ Z)
    (s : PullbackCone (A.restrictOpenFunctor.map f) (A.restrictOpenFunctor.map g)) :
    s.snd ≫ A.restrictOpenHom W = s.fst ≫ A.restrictOpenHom V := by
  have h : s.fst ≫ A.restrictOpenFunctor.map f = s.snd ≫ A.restrictOpenFunctor.map g :=
    s.condition
  have e₁ : A.restrictOpenFunctor.map f ≫ A.restrictOpenHom Z = A.restrictOpenHom V :=
    restrictOpenLE_restrictOpenHom A (leOfHom f)
  have e₂ : A.restrictOpenFunctor.map g ≫ A.restrictOpenHom Z = A.restrictOpenHom W :=
    restrictOpenLE_restrictOpenHom A (leOfHom g)
  exact (congrArg (fun t ↦ s.snd ≫ t) e₂.symm).trans
    ((Category.assoc s.snd _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ A.restrictOpenHom Z) h.symm).trans
        ((Category.assoc s.fst _ _).trans (congrArg (fun t ↦ s.fst ≫ t) e₁))))

/-- **The restriction of an object of `CRIS(X/S)` to the intersection of two opens of its ambient
scheme is the fibre product of its restrictions to the two opens.**  A cone consists of two
morphisms whose composites with the structure morphisms agree, so their common value is a
morphism into the object itself whose ambient image lies in both opens; it therefore factors
uniquely through the restriction to the intersection, by
`Crystalline.GlobalCrystallineSituation.Thickening.liftRestrictOpen` and the fact that the
structure morphism of a restriction is a monomorphism. -/
noncomputable def isLimitPullbackConeRestrictOpen (f : V ⟶ Z) (g : W ⟶ Z) :
    IsLimit (PullbackCone.mk (A.restrictOpenFunctor.map (homOfLE (inf_le_left : V ⊓ W ≤ V)))
      (A.restrictOpenFunctor.map (homOfLE (inf_le_right : V ⊓ W ≤ W)))
      (restrictOpenFunctor_map_inf_comm A f g)) := by
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ liftRestrictOpen (s.fst ≫ A.restrictOpenHom V) (V ⊓ W) (fun y ↦
      ⟨targetHom_base_mem_of_comp_restrictOpenHom V s.fst _ rfl y,
        targetHom_base_mem_of_comp_restrictOpenHom W s.snd _
          (comp_restrictOpenHom_eq_of_pullbackCone_condition A f g s) y⟩))
    (fun s ↦ restrictOpenLE_comp_eq inf_le_left _ _ (liftRestrictOpen_comp _ _ _) s.fst rfl)
    (fun s ↦ restrictOpenLE_comp_eq inf_le_right _ _ (liftRestrictOpen_comp _ _ _) s.snd
      (comp_restrictOpenHom_eq_of_pullbackCone_condition A f g s))
    (fun s m h₁ _ ↦ ?_)
  refine (cancel_mono (A.restrictOpenHom (V ⊓ W))).1
    (Eq.trans ?_ (liftRestrictOpen_comp _ _ _).symm)
  have e : A.restrictOpenFunctor.map (homOfLE (inf_le_left : V ⊓ W ≤ V)) ≫
      A.restrictOpenHom V = A.restrictOpenHom (V ⊓ W) :=
    restrictOpenLE_restrictOpenHom A inf_le_left
  exact (congrArg (fun t ↦ m ≫ t) e.symm).trans
    ((Category.assoc m _ _).symm.trans
      (congrArg (fun t ↦ t ≫ A.restrictOpenHom V) h₁))

end Pullbacks

/-- **The restrictions to the opens of the ambient scheme preserve pullbacks.**  Every cospan of
opens is isomorphic to the cospan of its two legs, whose pullback is the intersection. -/
instance preservesLimitsOfShape_walkingCospan_restrictOpenFunctor (A : Thickening S) :
    PreservesLimitsOfShape WalkingCospan A.restrictOpenFunctor := by
  constructor
  intro G
  have _ : PreservesLimit (cospan (G.map WalkingCospan.Hom.inl) (G.map WalkingCospan.Hom.inr))
      A.restrictOpenFunctor :=
    preservesLimit_of_preserves_limit_cone (isLimitPullbackConeOpens A _ _)
      ((isLimitMapConePullbackConeEquiv _ _).symm (isLimitPullbackConeRestrictOpen A _ _))
  exact preservesLimit_of_iso_diagram _ (diagramIsoCospan G).symm

/-- **The localisation of the restriction functor** at an open `V` of the ambient scheme and at
the restriction of the object to `V`.  This is `Over.post` of
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor`, named so that its
codomain is the slice over the restriction of the object rather than the slice over the image of
`V` under the restriction functor; the two are the same category, but only the first is the one
the restricted structure sheaf and the restricted module are stated over. -/
noncomputable def restrictOpenOverFunctor (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    Over V ⥤ Over (A.restrictOpen V) :=
  Over.post (X := V) A.restrictOpenFunctor

/-- **The localisation of the restriction functor is continuous.**  This is the half of
[Stacks, Tag 03CF] that the localisation of a morphism of sites needs, available here because the
opens of the ambient scheme have pullbacks and the restriction functor preserves them. -/
instance isContinuous_restrictOpenOverFunctor (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    (restrictOpenOverFunctor A V).IsContinuous
      ((Opens.grothendieckTopology ↥A.thickening.target.scheme).over V)
      ((topology S).over (A.restrictOpen V)) :=
  Functor.isContinuous_overPost_of_preservesPullbacks _ _ _ V

/-- **The localisation of the restriction functor is cocontinuous**, the restriction functor
being so. -/
instance isCocontinuous_restrictOpenOverFunctor (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    (restrictOpenOverFunctor A V).IsCocontinuous
      ((Opens.grothendieckTopology ↥A.thickening.target.scheme).over V)
      ((topology S).over (A.restrictOpen V)) :=
  inferInstanceAs ((Over.post (X := V) A.restrictOpenFunctor).IsCocontinuous
    ((Opens.grothendieckTopology ↥A.thickening.target.scheme).over V)
    ((topology S).over (A.restrictOpenFunctor.obj V)))

/-- **The comparison of structure sheaves on the localised sites is the identity.**  The
restriction of `𝒪_{X/S}` to the opens of the ambient scheme of an object is by definition its
restriction along `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor`, and
localising at an open `V` and at the restriction of the object to `V` turns that into the
restriction along the localised functor of the localisation of `𝒪_{X/S}`. -/
noncomputable def restrictOpenOverStructureHom (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    (A.ringRestrictionSheaf).over V ⟶
      ((restrictOpenOverFunctor A V).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥A.thickening.target.scheme).over V)
        ((topology S).over (A.restrictOpen V))).obj
          ((crystallineStructureSheaf S).over (A.restrictOpen V)) :=
  𝟙 _

/-- The comparison `restrictOpenOverStructureHom A V` of structure sheaves is an isomorphism. -/
instance isIso_restrictOpenOverStructureHom (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) : IsIso (restrictOpenOverStructureHom A V) :=
  inferInstanceAs (IsIso (𝟙 ((A.ringRestrictionSheaf).over V)))

/-- Restriction of sheaves of modules along the localisation of the restriction functor preserves
colimits of size `u + 1`, the universe in which a global presentation on the localised crystalline
site is indexed.  The four sheafification hypotheses are discharged here, inside a statement that
mentions only the universe `u + 1`, rather than in the proof of
`Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_moduleRestrictionSheaf_over`: in
that proof instances of the same two classes at the module universe `u` are also in play, and two
candidate instances at an unresolved value universe make the universe constraints unsolvable. -/
theorem preservesColimitsOfSize_pushforward_restrictOpenOverStructureHom (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over (A.restrictOpen V)) ⥤
          SheafOfModules.{u + 1} ((A.ringRestrictionSheaf).over V) from
        SheafOfModules.pushforward.{u + 1} (restrictOpenOverStructureHom A V)) := by
  have _ : HasSheafify ((topology S).over (A.restrictOpen V)) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((topology S).over (A.restrictOpen V)).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify
      ((Opens.grothendieckTopology ↥A.thickening.target.scheme).over V)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      ((Opens.grothendieckTopology ↥A.thickening.target.scheme).over V)
      AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    (restrictOpenOverFunctor A V) (restrictOpenOverStructureHom A V)

end Thickening

/-- **A global presentation of a sheaf of `𝒪_{X/S}`-modules on the localised crystalline site
over the restriction of an object to an open of its ambient scheme restricts to a global
presentation of the restricted module on the Zariski site localised at that open.**

The restriction `F_T` is the pushforward of `F` along
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor`, and both the restricted
structure sheaf and the restricted module are, on the localised sites, the pushforwards along
`Over.post` of the restrictions of `𝒪_{X/S}` and of `F`; the comparison of structure sheaves is
therefore the identity, and the transport is
`Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_pushforward`, whose index
universes are allowed to differ. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_over
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)
    (V : A.thickening.target.scheme.Opens)
    (h : (M.over (A.restrictOpen V)).HasGlobalPresentation) :
    ((Thickening.moduleRestrictionSheaf M A).over V).HasGlobalPresentation :=
  Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_pushforward.{u + 1,
    u, u, u, u, u} (G := Thickening.restrictOpenOverFunctor A V)
    (R := (crystallineStructureSheaf S).over (A.restrictOpen V))
    (R' := (A.ringRestrictionSheaf).over V)
    (Thickening.restrictOpenOverStructureHom A V) (M.over (A.restrictOpen V))
    (Thickening.preservesColimitsOfSize_pushforward_restrictOpenOverStructureHom A V) h

/-- **Stacks Project, Tag 07IT, the implication (1) ⇒ (2)(a): a quasi-coherent sheaf of
`𝒪_{X/S}`-modules on the big crystalline site is locally quasi-coherent.**

Quasi-coherence gives, around every point of the ambient scheme `T` of every object `(U, T, δ)`,
an open `V` on whose restriction `(U ∩ V, V, δ|_V)` the module has a global presentation
(`Crystalline.GlobalCrystallineSituation.exists_hasGlobalPresentation_restrictOpen`, which is
cocontinuity of the restriction functor).  Intersecting `V` with a given open `W` of `T` makes
those opens into an open cover of `W`, and each presentation restricts to one of `F_T` on the
Zariski site localised at `V ⊓ W` by
`Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_moduleRestrictionSheaf_over`; that
is quasi-coherence of `F_T` over `W`.

This is one of the two halves of the implication (1) ⇒ (2) of the tag, on this site; the other
half, that a quasi-coherent module is a crystal, is
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal`.  The same
implication for `𝒞 = Cris(X/S)`, the other site the tag is stated for, is
`Crystalline.GlobalCrystallineSituation.SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`
of `StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal`. -/
@[stacks 07IT "the implication (1) ⇒ (2)(a) on the big site CRIS(X/S): quasi-coherent implies
  locally quasi-coherent.  The same implication on the small site Cris(X/S), and the other half
  (1) ⇒ (2)(b) that a quasi-coherent module is a crystal, on each of the two sites, carry this tag
  separately.  The converse (2) ⇒ (1) is a separate statement"]
theorem isLocallyQuasiCoherent_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasiCoherent M := by
  choose V hxV hV using exists_hasGlobalPresentation_restrictOpen M hM
  intro A
  refine ⟨(Thickening.moduleRestrictionSheaf M A).isSheaf, ⟨fun W ↦ ?_⟩⟩
  refine ⟨↥W, fun i ↦ V A i.1 ⊓ W, fun _ ↦ homOfLE inf_le_right, ?_, fun i ↦ ?_⟩
  · intro x hx
    exact ⟨V A x ⊓ W, homOfLE inf_le_right,
      Sieve.ofArrows_mk (fun i : ↥W ↦ V A i.1 ⊓ W) (fun _ ↦ homOfLE inf_le_right) ⟨x, hx⟩,
      ⟨hxV A x, hx⟩⟩
  · exact hasGlobalPresentation_moduleRestrictionSheaf_over M A _
      (Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap M
        (A.restrictOpenLE (inf_le_left : V A i.1 ⊓ W ≤ V A i.1)) (hV A i.1))

end Crystalline.GlobalCrystallineSituation

end
