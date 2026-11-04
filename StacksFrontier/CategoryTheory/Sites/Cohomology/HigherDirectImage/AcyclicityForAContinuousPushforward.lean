module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Acyclicity for the direct image along a continuous functor of sites

Let `f : (C, O_C) → (D, O_D)` be a morphism of ringed sites given by a continuous functor
`u : D ⥤ C`, so that `f_* = u^s` is restriction along `u`. A sheaf of `O_C`-modules `F` is
right acyclic for `f_*` as soon as its cohomology over every object in the image of `u`
vanishes in positive degrees: by Stacks 072W the higher direct image `R^p f_* F` is the
sheafification of the presheaf `V ↦ H^p(u(V), F)`, so it vanishes as soon as that presheaf
does, and `f_*` is left exact, which is the other half of the criterion of Stacks 015C.

The cohomology `H^p(U, F)` appearing there is the one of the source, the `p`-th right derived
functor of `Γ(U, -) : Mod(O_C) ⥤ Mod(O_C(U))`. Its vanishing is also recorded here in terms of
the `Ext`-style sheaf cohomology `CategoryTheory.Sheaf.H'` of the underlying abelian sheaf,
which is the form the Čech-theoretic vanishing results are stated in.

## Main results

* `Stacks.Cohomology.ContinuousPushforward.isZero_presheafOfModules`: a presheaf of modules all
  of whose values vanish is zero.
* `Stacks.Cohomology.ContinuousPushforward.isZero_cohPresheafModule`: the cohomology presheaf
  `V ↦ H^p(u(V), F)` of Stacks 072W vanishes when the cohomology over each `u(V)` does.
* `Stacks.Cohomology.ContinuousPushforward.rightAcyclic_pushforward_of_isZero`: **a sheaf of
  modules with vanishing higher cohomology over the objects in the image of `u` is right
  acyclic for `f_* = u^s`.**
* `Stacks.Cohomology.ContinuousPushforward.isZero_rightDerived_evaluation_of_isZero_H'`: on a
  small site, vanishing of the `Ext`-style sheaf cohomology of the underlying abelian sheaf
  forces vanishing of the module-valued derived sections.

## Implementation notes

The criterion of Stacks 015C is stated for the `ℤ`-indexed higher right derived functors
`R ⁱ F` of `Functor.rightDerivedPlus`, whereas Stacks 072W is stated for Mathlib's
`ℕ`-indexed `Functor.rightDerived`; the two are matched by
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`.

The last result passes through the `Ext`-to-derived-sections comparison of Stacks 03FD
(`Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf`),
and then from sections of abelian groups back to sections of modules: the two functors agree on
the nose after forgetting the module structure, and a module whose underlying group vanishes
vanishes. Its universes are those of that comparison — a small site with its structure sheaf
and module sections in the universe of its objects.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.ContinuousPushforward

universe v₁ u₁ v₂ u₂ uRing uMod dC dD w

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section PresheafOfModules

variable {R : Type u₁} [Category.{v₁} R]

/-- A presheaf of modules all of whose values are zero is the zero presheaf: its identity is
zero in each degree, and a morphism of presheaves of modules is determined by its values. -/
theorem isZero_presheafOfModules {O : Rᵒᵖ ⥤ RingCat.{uRing}}
    (P : PresheafOfModules.{uMod} O)
    (h : ∀ V : Rᵒᵖ, IsZero ((PresheafOfModules.evaluation O V).obj P)) : IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  refine PresheafOfModules.hom_ext fun V ↦ ?_
  have hz : (0 : P ⟶ P).app V = 0 := rfl
  rw [hz]
  exact (h V).eq_of_src _ _

end PresheafOfModules

section Pushforward

variable {Dsite : Type u₁} [Category.{v₁} Dsite] {Csite : Type u₂} [Category.{v₂} Csite]
  {J𝒟 : GrothendieckTopology Dsite} {J𝒞 : GrothendieckTopology Csite}
  (u : Dsite ⥤ Csite) [u.IsContinuous J𝒟 J𝒞]
  (O𝒞 : Sheaf J𝒞 RingCat.{uRing}) (O𝒟 : Sheaf J𝒟 RingCat.{uRing})
  (φ : O𝒟 ⟶ (u.sheafPushforwardContinuous RingCat.{uRing} J𝒟 J𝒞).obj O𝒞)
  [HasSheafify J𝒞 AddCommGrpCat.{uMod}] [J𝒞.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [EnoughInjectives (SheafOfModules.{uMod} O𝒞)]
  [∀ V : Dsite, (SheafOfModules.evaluation O𝒞 (op (u.obj V))).Additive]

/-- **The cohomology presheaf of Stacks 072W vanishes** in a given degree as soon as the
cohomology over every object in the image of `u` does: a presheaf is zero when all its values
are, and the value at `V` is the cohomology `H^n(u(V), X)` read as an `O_D(V)`-module. -/
theorem isZero_cohPresheafModule (n : ℕ) (X : SheafOfModules.{uMod} O𝒞)
    (h : ∀ V : Dsite,
      IsZero (((SheafOfModules.evaluation O𝒞 (op (u.obj V))).rightDerived n).obj X)) :
    IsZero (cohPresheafModule u O𝒞 O𝒟 φ n X) := by
  refine isZero_presheafOfModules _ fun V ↦ ?_
  obtain ⟨e⟩ := cohPresheafModule_evaluation_iso u O𝒞 O𝒟 φ n X V.unop
  refine IsZero.of_iso ?_ e
  exact Functor.map_isZero _ (h V.unop)

variable [HasSheafify J𝒟 AddCommGrpCat.{uMod}]
  [J𝒟.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [HasDerivedCategory.{dC} (SheafOfModules.{uMod} O𝒞)]
  [HasDerivedCategory.{dD} (SheafOfModules.{uMod} O𝒟)]

/-- **A sheaf of modules whose higher cohomology vanishes over the objects in the image of `u`
is right acyclic for `f_* = u^s`.** By Stacks 072W the higher direct image `R^n f_* X` is the
sheafification of the cohomology presheaf `V ↦ H^n(u(V), X)`, which vanishes by hypothesis;
and `f_*` is left exact, so the criterion of Stacks 015C needs nothing in degree zero. -/
theorem rightAcyclic_pushforward_of_isZero (X : SheafOfModules.{uMod} O𝒞)
    (h : ∀ (V : Dsite) (n : ℕ), 0 < n →
      IsZero (((SheafOfModules.evaluation O𝒞 (op (u.obj V))).rightDerived n).obj X)) :
    (SheafOfModules.pushforward.{uMod} φ).rightAcyclic X := by
  have : (moduleSheafification O𝒟 : PresheafOfModules.{uMod} O𝒟.obj ⥤ _).Additive :=
    sheafification_additive O𝒟
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (SheafOfModules.pushforward.{uMod} φ) X).2 inferInstance).2 ?_
  intro i hi
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
  have hn0 : 0 < n := by omega
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ hn]
  obtain ⟨e⟩ := higherDirectImage_iso_sheafify_cohomologyPresheaf u O𝒞 O𝒟 φ n X
  exact (Functor.map_isZero _
    (isZero_cohPresheafModule u O𝒞 O𝒟 φ n X fun V ↦ h V n hn0)).of_iso e

end Pushforward

section Site

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (SheafOfModules.{w} R)]

/-- Sections over an object of a site are additive. -/
instance siteSheafSections_additive (U : C) :
    ((sheafSections J AddCommGrpCat.{w}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Module-valued sections over an object of a site are additive. -/
instance siteModuleEvaluation_additive (U : C) :
    (SheafOfModules.evaluation.{w} R (op U)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- On a site, the module-valued sections over `U` followed by forgetting the module structure
is the composite of passing to the underlying abelian sheaf with sections over `U`. -/
def evaluationCompForgetIsoSite (U : C) :
    SheafOfModules.evaluation.{w} R (op U) ⋙
        forget₂ (ModuleCat.{w} (R.obj.obj (op U))) AddCommGrpCat.{w} ≅
      SheafOfModules.toSheaf.{w} R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op U) :=
  Iso.refl _

/-- **Vanishing of the `Ext`-style sheaf cohomology forces vanishing of the module-valued
derived sections.** The two functors agree after forgetting the module structure, the forgetful
functor is exact and so commutes with right derivation, and a module whose underlying abelian
group vanishes vanishes. -/
theorem isZero_rightDerived_evaluation_of_isZero_H'
    (U : C) (n : ℕ) (F : SheafOfModules.{w} R)
    (h : IsZero (Sheaf.H'.{w, w, w} ((SheafOfModules.toSheaf.{w} R).obj F) n U)) :
    IsZero (((SheafOfModules.evaluation.{w} R (op U)).rightDerived n).obj F) := by
  have hzero :=
    (ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
      J R U n F).mpr h
  have : (forget₂ (ModuleCat.{w} (R.obj.obj (op U))) AddCommGrpCat.{w}).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have e := ModuleComparison.rightDerivedCompIso (SheafOfModules.evaluation.{w} R (op U))
    (forget₂ (ModuleCat.{w} (R.obj.obj (op U))) AddCommGrpCat.{w})
    (SheafOfModules.toSheaf.{w} R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op U))
    (evaluationCompForgetIsoSite J R U) n
  have hforget : IsZero ((forget₂ (ModuleCat.{w} (R.obj.obj (op U))) AddCommGrpCat.{w}).obj
      (((SheafOfModules.evaluation.{w} R (op U)).rightDerived n).obj F)) :=
    hzero.of_iso (e.app F)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.subsingleton_of_isZero hforget

end Site

end Stacks.Cohomology.ContinuousPushforward

end
