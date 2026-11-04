module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import StacksFrontier.RingTheory.Coherent.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.FiniteModuleRestrictionLimits
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.LeftExact
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.Extension
public import StacksCore.Tactic.StacksAttribute

/-!
# Left exactness of extensions to all modules

For a coherent ring `A`, a left exact functor from the finitely presented `A`-modules to all
modules over a second ring stays left exact after extension to all `A`-modules with preservation
of filtered colimits; the commutation of filtered colimits with kernels in the target is
automatic for a module category. Over a Noetherian ring the finite modules are finitely
presented, which gives the corresponding statement for an extension of a functor between
categories of finite modules.

## Main results

* `ModuleCat.filteredColimitExtension_preservesFiniteLimits_moduleValued`: left exactness of the
  extension of a functor on finitely presented modules with values in all modules.
* `ModuleCat.filteredColimitExtension_preservesFiniteLimits_of_noetherian`: the Noetherian
  specialization, with a module universe independent of both ring universes.
* `ModuleCat.fgFilteredColimitExtension_preservesFiniteLimits`: left exactness of the extension
  of a left exact functor between categories of finite modules.

## Implementation notes

The published statement of the tag has a functor with values in the finitely presented modules
over the second ring; the statement here allows arbitrary modules over that ring, which is what
its consumers need. The extension is represented by a filtered-colimit-preserving functor
together with its identification on the finitely presented modules. The target module universe
is enlarged to contain the index universe before the general criterion of
`ModuleCat.filteredColimitExtension_preservesFiniteLimits` is applied, and the conclusion is
pulled back along the fully faithful universe-lifting functor.

The module-valued statement is a different one from
`ModuleCat.filteredColimitExtension_preservesFiniteLimits` of Tag 0GNM, whose target is an
arbitrary additive category with the commutation hypothesis as an assumption; the name here
carries a suffix for that reason, and the statement for finite modules carries an `fg` prefix
to match `ModuleCat.FGFilteredColimitExtension`.

## References

* [Stacks Project, Tag 0GP8](https://stacks.math.columbia.edu/tag/0GP8)
* [Stacks Project, Tag 0GP9](https://stacks.math.columbia.edu/tag/0GP9)
* [Stacks Project, Definition 05CV](https://stacks.math.columbia.edu/tag/05CV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x s p

namespace ModuleCat

private lemma filteredColimit_preservesKernels_univIndep
    {R : Type w} [Ring R]
    (J : Type s) [Category.{s} J] [IsFiltered J] :
    ∀ {X Y : J ⥤ ModuleCat.{max p s} R} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (colim : (J ⥤ ModuleCat.{max p s} R) ⥤ _) := by
  intro X Y f
  let : UnivLE.{s, max p s} := inferInstance
  let : AB5OfSize.{s, s} (AddCommGrpCat.{max p s}) :=
    AB5OfSize_of_univLE.{s, s, max p s, max p s} _
  let : HasExactColimitsOfShape J (AddCommGrpCat.{max p s}) := inferInstance
  let : HasExactColimitsOfShape J (ModuleCat.{max p s} R) :=
    HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat R) AddCommGrpCat)
  infer_instance

private lemma moduleCat_colimit_span
    {R : Type w} [Ring R] {J : Type s} [Category.{s} J]
    {F : J ⥤ ModuleCat.{p} R} {c : Cocone F} (hc : IsColimit c) :
    Submodule.span R (Set.range fun z : Σ j, F.obj j =>
      (show c.pt from (c.ι.app z.1).hom z.2)) = ⊤ := by
  let S : Submodule R c.pt :=
    Submodule.span R (Set.range fun z : Σ j, F.obj j =>
      (show c.pt from (c.ι.app z.1).hom z.2))
  let q : c.pt ⟶ ModuleCat.of R (c.pt ⧸ S) := ModuleCat.ofHom (Submodule.mkQ S)
  have hq : q = 0 := by
    refine hc.hom_ext fun j => ?_
    ext x
    show Submodule.Quotient.mk ((c.ι.app j).hom x) = 0
    exact (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨⟨j, x⟩, rfl⟩)
  apply top_unique
  intro x _
  show x ∈ S
  apply (Submodule.Quotient.mk_eq_zero S).1
  simpa [q] using ConcreteCategory.congr_hom hq x

private lemma exists_uliftFunctor_mono_apply_eq {R : Type w} [Ring R] [UnivLE.{w, p}]
    (M : ModuleCat.{max p s} R) (x : M) :
    ∃ (P : ModuleCat.{p} R) (m : (ModuleCat.uliftFunctor.{s} R).obj P ⟶ M)
      (a : (ModuleCat.uliftFunctor.{s} R).obj P), Mono m ∧ m.hom a = x := by
  let eR : Shrink.{p} R ≃ₗ[R] R := Shrink.linearEquiv R R
  let f₀ : Shrink.{p} R →ₗ[R] M := (LinearMap.toSpanSingleton R M x).comp eR.toLinearMap
  let fbar : (Shrink.{p} R ⧸ f₀.ker) →ₗ[R] M :=
    (f₀.range.subtype).comp (LinearMap.quotKerEquivRange f₀).toLinearMap
  let eP : ULift.{s, p} (Shrink.{p} R ⧸ f₀.ker) ≃ₗ[R] (Shrink.{p} R ⧸ f₀.ker) :=
    ULift.moduleEquiv
  let m : (ModuleCat.uliftFunctor.{s} R).obj (ModuleCat.of R (Shrink.{p} R ⧸ f₀.ker)) ⟶ M :=
    ModuleCat.ofHom (fbar.comp eP.toLinearMap)
  have hminj : Function.Injective m.hom := fun a b hab =>
    eP.injective ((LinearMap.quotKerEquivRange f₀).injective (Subtype.val_injective hab))
  refine ⟨_, m, eP.symm (Submodule.Quotient.mk (eR.symm 1)),
    (ModuleCat.mono_iff_injective m).2 hminj, ?_⟩
  show fbar (eP (eP.symm (Submodule.Quotient.mk (eR.symm 1)))) = x
  rw [eP.apply_symm_apply]
  show ↑(f₀.quotKerEquivRange (Submodule.Quotient.mk (eR.symm 1))) = x
  rw [LinearMap.quotKerEquivRange_apply_mk]
  simp [f₀, eR]

private lemma uliftColimitDesc_surjective {R : Type w} [Ring R] {J : Type s} [Category.{s} J]
    [UnivLE.{w, p}] {F : J ⥤ ModuleCat.{p} R} {c : Cocone F} (hc : IsColimit c) :
    Function.Surjective ((colimit.isColimit (F ⋙ ModuleCat.uliftFunctor.{s} R)).desc
      ((ModuleCat.uliftFunctor.{s} R).mapCocone c)) := by
  let U : ModuleCat.{p} R ⥤ ModuleCat.{max p s} R := ModuleCat.uliftFunctor.{s} R
  let eC : ULift.{s, p} c.pt ≃ₗ[R] c.pt := ULift.moduleEquiv
  let g : colimit (F ⋙ U) ⟶ U.obj c.pt := (colimit.isColimit (F ⋙ U)).desc (U.mapCocone c)
  intro y
  obtain ⟨x, rfl⟩ := eC.symm.surjective y
  have hT : Submodule.span R
      (Set.range fun z : Σ j, F.obj j => (show c.pt from (c.ι.app z.1).hom z.2)) ≤
        (LinearMap.range g.hom).comap eC.symm.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, z⟩, rfl⟩
    show eC.symm ((c.ι.app j).hom z) ∈ LinearMap.range g.hom
    let eF : ULift.{s, p} (F.obj j) ≃ₗ[R] F.obj j := ULift.moduleEquiv
    refine ⟨colimit.ι (F ⋙ U) j (eF.symm z), ?_⟩
    exact ConcreteCategory.congr_hom
      ((colimit.isColimit (F ⋙ U)).fac (U.mapCocone c) j) (eF.symm z)
  exact hT (by simp [moduleCat_colimit_span (R := R) hc])

private lemma uliftColimitDesc_injective {R : Type w} [Ring R] {J : Type s} [Category.{s} J]
    [UnivLE.{w, p}] {F : J ⥤ ModuleCat.{p} R} {c : Cocone F} (hc : IsColimit c) :
    Function.Injective ((colimit.isColimit (F ⋙ ModuleCat.uliftFunctor.{s} R)).desc
      ((ModuleCat.uliftFunctor.{s} R).mapCocone c)) := by
  let U : ModuleCat.{p} R ⥤ ModuleCat.{max p s} R := ModuleCat.uliftFunctor.{s} R
  let d : Cocone (F ⋙ U) := colimit.cocone (F ⋙ U)
  let hd : IsColimit d := colimit.isColimit (F ⋙ U)
  let g : d.pt ⟶ U.obj c.pt := hd.desc (U.mapCocone c)
  show Function.Injective g.hom
  refine (injective_iff_map_eq_zero g.hom).2 fun x hgx => ?_
  obtain ⟨P, m, a, hm, rfl⟩ : ∃ (P : ModuleCat.{p} R) (m : U.obj P ⟶ d.pt) (a : U.obj P),
      Mono m ∧ m.hom a = x := exists_uliftFunctor_mono_apply_eq d.pt x
  obtain ⟨I⟩ := EnoughInjectives.presentation P
  let mI : U.obj P ⟶ U.obj I.J := U.map I.f
  have hmI_inj : Function.Injective mI.hom := (ModuleCat.mono_iff_injective mI).1 inferInstance
  obtain ⟨h, hh⟩ := Injective.factors mI m
  let t : Cocone F := {
    pt := I.J
    ι := {
      app := fun j => U.preimage (d.ι.app j ≫ h)
      naturality := fun i j f => by
        apply U.map_injective
        simp only [Functor.map_comp, Functor.map_preimage]
        simpa [Category.assoc] using congrArg (fun f => f ≫ h) (d.ι.naturality f) } }
  let k : c.pt ⟶ I.J := hc.desc t
  have hh' : h = g ≫ U.map k := by
    refine hd.hom_ext fun j => ?_
    have hfac : d.ι.app j ≫ g = U.map (c.ι.app j) := hd.fac (U.mapCocone c) j
    calc
      d.ι.app j ≫ h = U.map (t.ι.app j) := by simp [t]
      _ = U.map (c.ι.app j ≫ k) := by rw [← hc.fac t j]
      _ = d.ι.app j ≫ g ≫ U.map k := by
        rw [Functor.map_comp, ← hfac]
        simp [Category.assoc]
  have hzero : h (m.hom a) = 0 := by
    simpa [ModuleCat.comp_apply, hgx] using
      ConcreteCategory.congr_hom hh' (m.hom a)
  have hval : h (m.hom a) = mI.hom a := by
    simpa [mI, ModuleCat.comp_apply] using
      ConcreteCategory.congr_hom hh a
  have ha : a = 0 := hmI_inj (by simpa using hval.symm.trans hzero)
  simp [ha]

private noncomputable def moduleCat_ulift_preservesFilteredColimit
    {R : Type w} [Ring R] {J : Type s}
    [Category.{s} J] [IsFiltered J]
    [UnivLE.{w, p}]
    (F : J ⥤ ModuleCat.{p} R) {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((ModuleCat.uliftFunctor.{s} R).mapCocone c) := by
  let U : ModuleCat.{p} R ⥤ ModuleCat.{max p s} R := ModuleCat.uliftFunctor.{s} R
  let hd := colimit.isColimit (F ⋙ U)
  letI : IsIso (hd.desc (U.mapCocone c)) := (ConcreteCategory.isIso_iff_bijective _).2
    ⟨uliftColimitDesc_injective hc, uliftColimitDesc_surjective hc⟩
  exact IsColimit.ofIsoColimit hd
    (Cocone.ext (asIso (hd.desc (U.mapCocone c))) (hd.fac (U.mapCocone c)))

/-- **Stacks Project, Tag 0GP8.** The filtered-colimit-preserving extension of a left exact
functor on finitely presented modules is left exact when the source ring is coherent. This is
the module-valued form: the functor takes values in all modules over the second ring, not only
in the finitely presented ones. -/
@[stacks 0GP8]
theorem filteredColimitExtension_preservesFiniteLimits_moduleValued
    (A : Type u) [CommRing A] [IsCoherentRing A]
    (B : Type w) [Ring B]
    (F : FinitelyPresentedModuleCat.{u, max u v} A ⥤
      ModuleCat.{max w x} B)
    (E : FilteredColimitExtension A F)
    [PreservesFiniteLimits F] :
    PreservesFiniteLimits E.functor := by
  let U : ModuleCat.{max w x} B ⥤ ModuleCat.{max (max u v) (max w x)} B :=
    ModuleCat.uliftFunctor.{max u v} B
  let F' := F ⋙ U
  let E' : FilteredColimitExtension A F' :=
    { functor := E.functor ⋙ U
      preservesFilteredColimits := by
        refine ⟨fun J _ hJ => ?_⟩
        refine ⟨fun {K} => ?_⟩
        refine ⟨fun {c} hc => ?_⟩
        let : PreservesColimitsOfShape J E.functor :=
          E.preservesFilteredColimits.preserves_filtered_colimits J
        obtain ⟨hcE⟩ := (show PreservesColimit K E.functor from inferInstance).preserves hc
        exact ⟨moduleCat_ulift_preservesFilteredColimit.{w, max u v, max w x}
          (K ⋙ E.functor) hcE⟩
      iso :=
        (Functor.associator _ _ _).symm.trans (Functor.isoWhiskerRight E.iso U) }
  let : UnivLE.{max u v, max (max w x) (max u v)} := inferInstance
  let : HasFiniteBiproducts (ModuleCat.{max (max u v) (max w x)} B) := inferInstance
  let : HasKernels (ModuleCat.{max (max u v) (max w x)} B) := inferInstance
  let : HasFilteredColimitsOfSize.{max u v, max u v}
      (ModuleCat.{max (max u v) (max w x)} B) := inferInstance
  let : ∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J],
      ∀ {X Y : J ⥤ ModuleCat.{max (max u v) (max w x)} B} (f : X ⟶ Y),
        PreservesLimit (parallelPair f 0)
      (colim : (J ⥤ ModuleCat.{max (max u v) (max w x)} B) ⥤ _) := by
    intro J _ hJ X Y f
    exact filteredColimit_preservesKernels_univIndep.{w, max u v, max w x}
      (R := B) J f
  let : PreservesFiniteLimits (E.functor ⋙ U) :=
    @filteredColimitExtension_preservesFiniteLimits A _ _ _ _ _ F' _ E' _ _ _ this
  exact preservesFiniteLimits_of_reflects_of_preserves E.functor U

/-- The Noetherian specialization of left exactness of filtered-colimit extensions, with a
module universe independent of both ring universes. Finite modules over `A` are finitely
presented, so this is the specialization used by Tag 0GP9. -/
theorem filteredColimitExtension_preservesFiniteLimits_of_noetherian
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type w) [Ring B]
    (F : FGModuleCat.{v} A ⥤ ModuleCat.{v} B)
    (E : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
    [PreservesFilteredColimitsOfSize.{v, v} E]
    (e : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E) ≅ F)
    [PreservesFiniteLimits F] : PreservesFiniteLimits E := by
  let : PreservesFiniteLimits (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E) :=
    preservesFiniteLimits_of_natIso e.symm
  exact ModuleCat.preservesFiniteLimits_of_finiteModuleRestriction E

/-- **Stacks Project, Tag 0GP9.** A left exact functor on finite modules over Noetherian rings
has a left exact filtered-colimit-preserving extension to all modules. -/
@[stacks 0GP9 "left_exactness"]
theorem fgFilteredColimitExtension_preservesFiniteLimits
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type w) [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B)
    (E : FGFilteredColimitExtension.{u, v, w} A B F)
    [PreservesFiniteLimits F] :
    PreservesFiniteLimits E.functor := by
  have := comp_preservesFiniteLimits F (forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B))
  exact filteredColimitExtension_preservesFiniteLimits_of_noetherian A B
    (F ⋙ forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B)) E.functor E.iso

end ModuleCat
