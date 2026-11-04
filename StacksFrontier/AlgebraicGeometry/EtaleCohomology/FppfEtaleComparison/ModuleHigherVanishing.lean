module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AcyclicityForAContinuousPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing

/-!
# A higher direct image of a sheaf of modules vanishes on a covering family

Let `f : (𝒞, 𝒪_𝒞) → (𝒟, 𝒪_𝒟)` be a morphism of ringed sites given by a continuous functor
`u : 𝒟 ⥤ 𝒞`, so that `f_* = u^s` is restriction along `u`.  Then `R^p f_* F = 0` as soon as
every object `V` of `𝒟` carries a covering family whose members `W` satisfy `H^p(u(W), F) = 0`.

## Main results

* `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_of_isZero_toSheaf`: a sheaf of modules
  whose underlying abelian sheaf vanishes vanishes.
* `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_moduleSheafification_of_locallyZero`: a
  presheaf of modules all of whose sections die on a covering sieve sheafifies to zero.
* `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`:
  **the criterion**, with the covering family given as a presieve.
* `Stacks.Cohomology.ModuleDirectImageOnACover.rightAcyclic_pushforward_of_presieve`: hence
  `F` is right acyclic for `f_*`, that is, `f_* F → R f_* F` is an isomorphism.
* `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_sheafCohomology_chgUniv`: vanishing of
  `CategoryTheory.Sheaf.H'` does not depend on the `Ext` universe.
* `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'` and
  its companion `..._chgUniv`: vanishing of the `Ext`-style cohomology of the underlying abelian
  sheaf over an object forces vanishing of the module-valued derived sections there.

## Implementation notes

The three steps are [Stacks, Tag 072W] for sheaves of modules, the vanishing of the
sheafification, and [Stacks, Tag 015C].  By 072W the higher direct image `R^p f_* F` is the
sheafification of the cohomology presheaf `V ↦ H^p(u(V), F)`, and
`cohPresheafModule_evaluation_iso` identifies its value at `V`; so the hypothesis makes every
section of that presheaf restrict into a zero module along the members of a covering family,
hence die on the sieve they generate.  A presheaf of modules with that property sheafifies to
zero because `PresheafOfModules.sheafificationCompToSheaf` identifies the underlying abelian
sheaf of the sheafification with the sheafification of the underlying abelian presheaf, where
`Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero` applies,
and `SheafOfModules.toSheaf` is faithful and additive, so it reflects zero objects.  Finally
`f_*` is left exact, so the criterion of 015C has nothing to ask in degree zero.

The hypothesis is a *presieve*, not a sieve: a covering family of affine objects is almost
never downward closed.  The analogous criterion for abelian sheaves is
`Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`; it
cannot be transported to sheaves of modules through
`Stacks.Cohomology.SiteModulePushforward.AnySite.rightDerivedPushforwardToSheafIso`, whose
module universe is forced to dominate the universe of the objects of the sites, whereas the
sites of schemes carry modules one universe *below* their objects.  All the universes here are
those of [Stacks, Tag 072W] for modules, which are mutually independent.

`isZero_rightDerived_evaluation_of_isZero_H'` is the bridge supplying the hypothesis from the
Čech-theoretic vanishing results, which are stated for `CategoryTheory.Sheaf.H'`.  Unlike
`Stacks.Cohomology.ContinuousPushforward.isZero_rightDerived_evaluation_of_isZero_H'` it does
not ask the site to be small: it is
`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`, whose `Ext` universe
is `max u' u` for a site with objects in `Type u'` and morphisms in `Type u`.  The Čech-theoretic
results measure instead at `u`, and `CategoryTheory.Abelian.Ext.chgUniv` reconciles the two:
`isZero_sheafCohomology_chgUniv` moves a vanishing statement between `Ext` universes, since
`CategoryTheory.Sheaf.H'` is an `Ext`-group out of an object that does not depend on it.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.ModuleDirectImageOnACover

universe v₁ u₁ v₂ u₂ uRing uMod dC dD w w'

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Reflecting the zero object -/

section Reflect

variable {Dsite : Type u₁} [Category.{v₁} Dsite] {J𝒟 : GrothendieckTopology Dsite}
  (O𝒟 : Sheaf J𝒟 RingCat.{uRing})

/-- **A sheaf of modules whose underlying abelian sheaf is zero is zero.**  Forgetting the
module structure is faithful and additive, so it carries the identity of a nonzero object to a
nonzero morphism. -/
public theorem isZero_of_isZero_toSheaf {X : SheafOfModules.{uMod} O𝒟}
    (h : IsZero ((SheafOfModules.toSheaf.{uMod} O𝒟).obj X)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  refine (SheafOfModules.toSheaf.{uMod} O𝒟).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp h

variable [HasSheafify J𝒟 AddCommGrpCat.{uMod}]
  [J𝒟.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [J𝒟.HasSheafCompose (forget AddCommGrpCat.{uMod})]

/-- **A presheaf of modules whose sections die locally sheafifies to zero.**  The underlying
abelian sheaf of the sheafification is the sheafification of the underlying abelian presheaf,
by `PresheafOfModules.sheafificationCompToSheaf`, and there the abelian statement
`Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero`
applies. -/
public theorem isZero_moduleSheafification_of_locallyZero
    (P : PresheafOfModules.{uMod} O𝒟.obj)
    (h : ∀ (V : Dsite) (x : ToType (P.presheaf.obj (op V))),
      Presheaf.equalizerSieve (F := P.presheaf) (X := op V) x 0 ∈ J𝒟 V) :
    IsZero ((moduleSheafification O𝒟).obj P) := by
  refine isZero_of_isZero_toSheaf O𝒟 (IsZero.of_iso ?_
    ((PresheafOfModules.sheafificationCompToSheaf (𝟙 O𝒟.obj)).app P))
  exact SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero J𝒟 P.presheaf h

end Reflect

/-! ### The criterion -/

section Criterion

variable {Dsite : Type u₁} [Category.{v₁} Dsite] {Csite : Type u₂} [Category.{v₂} Csite]
  {J𝒟 : GrothendieckTopology Dsite} {J𝒞 : GrothendieckTopology Csite}
  (u : Dsite ⥤ Csite) [u.IsContinuous J𝒟 J𝒞]
  (O𝒞 : Sheaf J𝒞 RingCat.{uRing}) (O𝒟 : Sheaf J𝒟 RingCat.{uRing})
  (φ : O𝒟 ⟶ (u.sheafPushforwardContinuous RingCat.{uRing} J𝒟 J𝒞).obj O𝒞)
  [HasSheafify J𝒞 AddCommGrpCat.{uMod}] [J𝒞.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [HasSheafify J𝒟 AddCommGrpCat.{uMod}] [J𝒟.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [J𝒟.HasSheafCompose (forget AddCommGrpCat.{uMod})]
  [EnoughInjectives (SheafOfModules.{uMod} O𝒞)]
  [(SheafOfModules.pushforward.{uMod} φ).Additive]
  [∀ V : Dsite, (SheafOfModules.evaluation O𝒞 (op (u.obj V))).Additive]

/-- **The higher direct image of a sheaf of modules vanishes if its cohomology vanishes on a
covering family.**  For each object `V` of the target site there has to be a covering *presieve*
of `V` all of whose members `W` have `H^p(u(W), F) = 0`; then `R^p f_* F = 0`.

Nothing is asked to be natural: the restriction of a section of the cohomology presheaf of
[Stacks, Tag 072W] along a member of the family lands in a zero module. -/
public theorem isZero_rightDerived_pushforward_of_presieve (p : ℕ)
    (F : SheafOfModules.{uMod} O𝒞)
    (h : ∀ V : Dsite, ∃ R : Presieve V, Sieve.generate R ∈ J𝒟 V ∧
      ∀ ⦃W : Dsite⦄ (g : W ⟶ V), R g →
        IsZero (((SheafOfModules.evaluation O𝒞 (op (u.obj W))).rightDerived p).obj F)) :
    IsZero (((SheafOfModules.pushforward.{uMod} φ).rightDerived p).obj F) := by
  have : (cohFunctor u O𝒞 O𝒟 φ : SheafOfModules.{uMod} O𝒞 ⥤ _).Additive :=
    cohFunctor_additive u O𝒞 O𝒟 φ
  obtain ⟨e⟩ := higherDirectImage_iso_sheafify_cohomologyPresheaf u O𝒞 O𝒟 φ p F
  refine IsZero.of_iso ?_ e
  refine isZero_moduleSheafification_of_locallyZero O𝒟 _ (fun V x ↦ ?_)
  obtain ⟨R, hgen, hvan⟩ := h V
  refine J𝒟.superset_covering ((Sieve.generate_le_iff R _).mpr (fun W g hg ↦ ?_)) hgen
  obtain ⟨ev⟩ := cohPresheafModule_evaluation_iso u O𝒞 O𝒟 φ p F W
  have h0 : Subsingleton (((SheafOfModules.evaluation O𝒞 (op (u.obj W))).rightDerived p).obj F) :=
    ModuleCat.isZero_iff_subsingleton.mp (hvan g hg)
  have hz : IsZero ((PresheafOfModules.evaluation O𝒟.obj (op W)).obj
      (cohPresheafModule u O𝒞 O𝒟 φ p F)) :=
    IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr h0) ev
  have hsub : Subsingleton
      (ToType ((cohPresheafModule u O𝒞 O𝒟 φ p F).presheaf.obj (op W))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact Subsingleton.elim _ _

variable [HasDerivedCategory.{dC} (SheafOfModules.{uMod} O𝒞)]
  [HasDerivedCategory.{dD} (SheafOfModules.{uMod} O𝒟)]

/-- **A sheaf of modules whose cohomology vanishes on a covering family in every positive
degree is right acyclic for `f_* = u^s`**, that is, the canonical map `f_* F → R f_* F` is an
isomorphism.  This is the criterion of [Stacks, Tag 015C]: the higher direct images vanish by
`isZero_rightDerived_pushforward_of_presieve`, and `f_*` is left exact, so nothing is asked in
degree zero. -/
public theorem rightAcyclic_pushforward_of_presieve (F : SheafOfModules.{uMod} O𝒞)
    (h : ∀ p : ℕ, 0 < p → ∀ V : Dsite, ∃ R : Presieve V, Sieve.generate R ∈ J𝒟 V ∧
      ∀ ⦃W : Dsite⦄ (g : W ⟶ V), R g →
        IsZero (((SheafOfModules.evaluation O𝒞 (op (u.obj W))).rightDerived p).obj F)) :
    (SheafOfModules.pushforward.{uMod} φ).rightAcyclic F := by
  have : (moduleSheafification O𝒟 : PresheafOfModules.{uMod} O𝒟.obj ⥤ _).Additive :=
    sheafification_additive O𝒟
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (SheafOfModules.pushforward.{uMod} φ) F).2 inferInstance).2 ?_
  intro i hi
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
  have hn0 : 0 < n := by omega
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ hn]
  exact isZero_rightDerived_pushforward_of_presieve u O𝒞 O𝒟 φ n F (h n hn0)

end Criterion

/-! ### From `Ext`-style sheaf cohomology to module-valued derived sections -/

/-- **An abelian category with enough injectives has `Ext`-groups in its own universe of
morphisms**, being locally small there.  Not an instance, following Mathlib's policy for
`CategoryTheory.HasExt`. -/
public theorem hasExt_morphismUniverse (A : Type u₁) [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] : HasExt.{v₁} A :=
  have : LocallySmall.{v₁} A := CategoryTheory.locallySmall_self A
  hasExt_of_enoughInjectives A

/-! ### The `Ext` universe -/

/-- **Vanishing of sheaf cohomology does not depend on the `Ext` universe.**
`CategoryTheory.Abelian.Ext.chgUniv` is a bijection between the `Ext`-groups computed at two
universes, and `CategoryTheory.Sheaf.H'` is such an `Ext`-group out of an object that does not
depend on the universe. -/
public theorem isZero_sheafCohomology_chgUniv {Csite : Type u₂} [Category.{uMod} Csite]
    (J𝒞 : GrothendieckTopology Csite) [HasSheafify J𝒞 AddCommGrpCat.{uMod}]
    [HasExt.{w} (Sheaf J𝒞 AddCommGrpCat.{uMod})]
    [HasExt.{w'} (Sheaf J𝒞 AddCommGrpCat.{uMod})]
    (G : Sheaf J𝒞 AddCommGrpCat.{uMod}) (n : ℕ) (U : Csite)
    (h : IsZero (Sheaf.H'.{w} G n U)) : IsZero (Sheaf.H'.{w'} G n U) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton] at h ⊢
  refine Equiv.subsingleton (β := ToType (Sheaf.H'.{w} G n U)) ?_
  exact Abelian.Ext.chgUniv.symm

section Bridge

variable {Csite : Type u₂} [Category.{uMod} Csite] (J𝒞 : GrothendieckTopology Csite)
  (O𝒞 : Sheaf J𝒞 RingCat.{uMod})
  [HasSheafify J𝒞 AddCommGrpCat.{uMod}] [J𝒞.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [HasExt.{max u₂ uMod} (Sheaf J𝒞 AddCommGrpCat.{uMod})]
  [EnoughInjectives (Sheaf J𝒞 AddCommGrpCat.{uMod})]
  [EnoughInjectives (SheafOfModules.{uMod} O𝒞)]
  [HasExt.{max u₂ uMod} (SheafOfModules.{uMod} O𝒞)]

/-- **Vanishing of the `Ext`-style sheaf cohomology of the underlying abelian sheaf forces
vanishing of the module-valued derived sections.**  This is
`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation` read as an `IsZero`
statement; the site's objects may live above its morphisms, as they do on the sites of
schemes. -/
public theorem isZero_rightDerived_evaluation_of_isZero_H' (W : Csite) (p : ℕ)
    (F : SheafOfModules.{uMod} O𝒞)
    (h : IsZero (Sheaf.H'.{max u₂ uMod} ((SheafOfModules.toSheaf.{uMod} O𝒞).obj F) (p + 1) W)) :
    IsZero (((SheafOfModules.evaluation O𝒞 (op W)).rightDerived (p + 1)).obj F) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (ObjectSections.subsingleton_rightDerived_evaluation J𝒞 O𝒞 F W p h)

/-- **The same bridge at an arbitrary `Ext` universe.**  This is the form the Čech-theoretic
vanishing results supply, their `Ext` universe being the morphism universe of the site rather
than the one enlarged by its objects. -/
public theorem isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
    [HasExt.{w} (Sheaf J𝒞 AddCommGrpCat.{uMod})] (W : Csite) (p : ℕ)
    (F : SheafOfModules.{uMod} O𝒞)
    (h : IsZero (Sheaf.H'.{w} ((SheafOfModules.toSheaf.{uMod} O𝒞).obj F) (p + 1) W)) :
    IsZero (((SheafOfModules.evaluation O𝒞 (op W)).rightDerived (p + 1)).obj F) :=
  have h' : IsZero (Sheaf.H'.{max u₂ uMod}
      ((SheafOfModules.toSheaf.{uMod} O𝒞).obj F) (p + 1) W) :=
    isZero_sheafCohomology_chgUniv.{u₂, uMod, w, max u₂ uMod} J𝒞 _ _ _ h
  isZero_rightDerived_evaluation_of_isZero_H' J𝒞 O𝒞 W p F h'

end Bridge

end Stacks.Cohomology.ModuleDirectImageOnACover

end
