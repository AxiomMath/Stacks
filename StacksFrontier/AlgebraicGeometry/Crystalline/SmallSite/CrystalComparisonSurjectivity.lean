module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackIsoAdjunct
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal

/-!
# A crystal has locally surjective comparison morphisms of presheaves of modules

Fix a global crystalline situation `(p, (S, I, γ), X)` and a sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site `Cris(X/S)`.  Hypothesis (2) of [Stacks, Tag 07JN],
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.IsSurjectiveComparison`,
asks that the comparison morphism `c_f : f^* F_{T'} ⟶ F_T` of *presheaves* of `𝒪_T`-modules be
locally surjective for the Zariski topology on `T`.  This file proves that a crystal in
`𝒪_{X/S}`-modules satisfies it.

That is the step the proof of [Stacks, Tag 07JH] takes when it writes
`M_e = M_{e+1}/p^e M_{e+1}` "since `ℱ` is a crystal", and which the footnote of
[Stacks, Tag 07LF] records as unavailable under the hypotheses of [Stacks, Tag 07JN] alone.

## Why the crystal condition suffices although it is a condition on sheaves

The crystal condition `Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal` of
[Stacks, Tag 07IS] says that the comparison map of *sheaves* of modules
`...CohomologyRestriction.moduleComparisonSheaf` is an isomorphism, and the sheaf-level pullback
is the sheafification of the presheaf-level one.  The condition read with the comparison morphisms
of presheaves of modules — `Crystalline.GlobalCrystallineSituation.IsCrystal` on the big
crystalline category — is *strictly stronger*: a countable coproduct of copies of `𝒪_{X/S}` is a
crystal at sheaf level and not at presheaf level, because an infinite coproduct of sheaves of
modules is not computed section by section, so a section of the coproduct over a countable
disjoint union of copies of `Spec 𝔽_p` may use a different summand on each component and is not in
the image of the presheaf-level pullback.  That counterexample is recorded in the module
documentation of `StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal`, and it
is why the two *isomorphism* conditions are inequivalent and why only
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal` holds, not its converse.

It does not obstruct the statement proved here, and nothing about quasi-coherence is needed.  The
reason is about the shape of the hypothesis rather than about the modules: `IsSurjectiveComparison`
asks for *local* surjectivity, which is invariant under the sheafification that separates the two
pullbacks.  The presheaf-level comparison morphism factors as the unit of the sheafification
adjunction followed by the sheaf-level comparison map — both are transposes of the same `f`-map,
which is
`...CohomologyRestriction.moduleComparison_eq_sheafificationAdjunction_unit_comp` below — and the
unit is locally bijective.  So as soon as the sheaf-level map is an isomorphism, which is exactly
the crystal condition, the presheaf-level map is locally surjective, however far it is from being
an isomorphism.  In the coproduct counterexample the presheaf-level comparison morphism is indeed
locally surjective while failing to be an isomorphism: on each component of the disjoint union a
section of the coproduct is a section of a single summand.

## Main results

* `...CohomologyRestriction.moduleComparison_eq_sheafificationAdjunction_unit_comp` — **the
  comparison morphism of presheaves of modules is the unit of the sheafification adjunction
  followed by the comparison map of sheaves of modules**, the two pullbacks being compared by
  `SheafOfModules.pullbackIso`.
* `...CohomologyRestriction.toPresheaf_map_moduleComparison_eq` — the same factorisation, read on
  underlying presheaves of abelian groups and with the composition distributed.
* `...CohomologyRestriction.isLocallySurjective_moduleComparison_of_isIso_moduleComparisonSheaf`
  — the comparison morphism of presheaves of modules along a morphism of `Cris(X/S)` is locally
  surjective as soon as the comparison map of sheaves of modules along that morphism is an
  isomorphism.
* `isSurjectiveComparison_of_isSheafCrystal` — **a crystal in `𝒪_{X/S}`-modules on `Cris(X/S)`
  satisfies hypothesis (2) of [Stacks, Tag 07JN]**, for every morphism of `Cris(X/S)` and not only
  for those whose map on ambient schemes is a closed immersion.
* `isSurjectiveComparison_restrictSheafOfModules_of_isSheafCrystal` and
  `isSurjectiveComparison_restrictSheafOfModules_of_isCrystal` — the same for the restriction to
  `Cris(X/S)` of a crystal on the big crystalline category `CRIS(X/S)`, at sheaf level and at
  presheaf level.

## What is and is not proved

No `@[stacks]` attribute is placed.  What is proved is that one *hypothesis* of
[Stacks, Tag 07JN] — hypothesis (2) — follows from the crystal condition; it is not any tag's own
assertion.

The identification of the two pullback functors that the argument uses is Mathlib's
`SheafOfModules.pullbackIso` together with
`SheafOfModules.homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app`; no new
identification is introduced.  In particular the *isomorphism* condition at presheaf level is not
derived from the one at sheaf level, which is false.

## Implementation notes

The last step — local surjectivity of a composition — is taken through the private
`isLocallySurjective_of_fac`, which takes its two factors as ordinary hypotheses, rather than
through Mathlib's `CategoryTheory.Presheaf.isLocallySurjective_comp` instance directly.  Instance
search on the concrete presheaves of this file does not find a local
`CategoryTheory.Presheaf.IsLocallySurjective` hypothesis for either factor, and left to itself it
selects a universe-polymorphic sheafification instance whose concrete-category parameters do not
typecheck here.  Supplying the two factors positionally fixes those parameters by unification and
avoids both problems.

## References

* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (M : SheafOfModules.{u} (structureSheaf S))
  {A B : CrystallineThickening S}

/-- A morphism of presheaves which factors as two locally surjective morphisms is locally
surjective.  This is `CategoryTheory.Presheaf.isLocallySurjective_comp` with the two factors
taken as hypotheses instead of instances, so that the concrete-category parameters are fixed by
unification; see the implementation notes of the module. -/
private theorem isLocallySurjective_of_fac {C : Type*} [Category C]
    (JJ : GrothendieckTopology C) {Av : Type*} [Category Av] {FA : Av → Av → Type*}
    {CA : Av → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory Av FA]
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ Av} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃}
    (h₁ : Presheaf.IsLocallySurjective JJ f₁) (h₂ : Presheaf.IsLocallySurjective JJ f₂)
    (fac : f₁ ≫ f₂ = f₃) : Presheaf.IsLocallySurjective JJ f₃ := by
  subst fac
  have := h₁
  have := h₂
  infer_instance

/-- **The comparison morphism of presheaves of modules is the unit of the sheafification
adjunction followed by the comparison map of sheaves of modules.**  The pullback of sheaves of
modules is the sheafification of the pullback of presheaves of modules — that is
`SheafOfModules.pullbackIso` — and both comparison maps are transposes of the same `f`-map, so the
two sides have the same transpose across the pullback–pushforward adjunction of presheaves of
modules, which is a bijection. -/
theorem moduleComparison_eq_sheafificationAdjunction_unit_comp (g : A ⟶ B) :
    moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g =
      (PresheafOfModules.sheafificationAdjunction
            (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).unit.app
          ((PresheafOfModules.pullback.{u}
              (Thickening.ringRestrictionSheafFMap g.hom).hom).obj
            (moduleRestrictionSheaf M B).val) ≫
        (SheafOfModules.forget (Thickening.ringRestrictionSheaf A.obj) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).map
          ((SheafOfModules.pullbackIso.{u}
              (Thickening.ringRestrictionSheafFMap g.hom)).inv.app
            (moduleRestrictionSheaf M B) ≫ moduleComparisonSheaf M g) := by
  apply ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (Thickening.ringRestrictionSheafFMap g.hom).hom).homEquiv _ _).injective
  refine Eq.trans ?_
    (SheafOfModules.homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app
      (Thickening.ringRestrictionSheafFMap g.hom) (moduleRestrictionSheaf M B)
      (moduleRestrictionSheaf M A) (moduleComparisonSheaf M g)).symm
  exact Eq.trans
    (moduleFMap_eq_moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g).symm
    (congrArg (SheafOfModules.forget (Thickening.ringRestrictionSheaf B.obj)).map
      (moduleFMapSheaf_eq_moduleComparisonSheaf M g))

/-- `...CohomologyRestriction.moduleComparison_eq_sheafificationAdjunction_unit_comp` read on the
underlying presheaves of abelian groups, with the composition distributed: that is the shape local
surjectivity of the two factors is combined at. -/
theorem toPresheaf_map_moduleComparison_eq (g : A ⟶ B) :
    (PresheafOfModules.toPresheaf (ringRestriction A)).map
        (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g) =
      (PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf A.obj).obj).map
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).unit.app
            ((PresheafOfModules.pullback.{u}
                (Thickening.ringRestrictionSheafFMap g.hom).hom).obj
              (moduleRestrictionSheaf M B).val)) ≫
        (PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf A.obj).obj).map
          ((SheafOfModules.forget (Thickening.ringRestrictionSheaf A.obj) ⋙
              PresheafOfModules.restrictScalars
                (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).map
            ((SheafOfModules.pullbackIso.{u}
                (Thickening.ringRestrictionSheafFMap g.hom)).inv.app
              (moduleRestrictionSheaf M B) ≫ moduleComparisonSheaf M g)) := by
  rw [moduleComparison_eq_sheafificationAdjunction_unit_comp]
  exact (PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf A.obj).obj).map_comp _ _

/-- **The comparison morphism of presheaves of modules along a morphism of `Cris(X/S)` is locally
surjective as soon as the comparison map of sheaves of modules along that morphism is an
isomorphism.**  The first factor of
`...CohomologyRestriction.toPresheaf_map_moduleComparison_eq` is the sheafification map of the
pullback of presheaves of abelian groups, which is locally bijective, and the second is an
isomorphism; local surjectivity is stable under composition. -/
theorem isLocallySurjective_moduleComparison_of_isIso_moduleComparisonSheaf (g : A ⟶ B)
    (h : IsIso (moduleComparisonSheaf M g)) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (ringRestriction A)).map
        (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g)) := by
  have := h
  have h1 : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf A.obj).obj).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).unit.app
          ((PresheafOfModules.pullback.{u}
              (Thickening.ringRestrictionSheafFMap g.hom).hom).obj
            (moduleRestrictionSheaf M B).val))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact ((Opens.grothendieckTopology
      ↥A.obj.thickening.target.scheme).W_toSheafify _).isLocallySurjective
  have : IsIso ((SheafOfModules.pullbackIso.{u}
      (Thickening.ringRestrictionSheafFMap g.hom)).inv.app (moduleRestrictionSheaf M B) ≫
    moduleComparisonSheaf M g) := inferInstance
  have h2 : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf A.obj).obj).map
        ((SheafOfModules.forget (Thickening.ringRestrictionSheaf A.obj) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).map
          ((SheafOfModules.pullbackIso.{u}
              (Thickening.ringRestrictionSheafFMap g.hom)).inv.app
            (moduleRestrictionSheaf M B) ≫ moduleComparisonSheaf M g))) := inferInstance
  exact isLocallySurjective_of_fac _ h1 h2 (toPresheaf_map_moduleComparison_eq M g).symm

end CohomologyRestriction

/-- **A crystal in `𝒪_{X/S}`-modules on the small crystalline site satisfies hypothesis (2) of
[Stacks, Tag 07JN]**: for every morphism of `Cris(X/S)` whose map on ambient schemes is a closed
immersion the comparison morphism `c_f : f^* F_{T'} ⟶ F_T` of presheaves of `𝒪_T`-modules is
locally surjective.

This is the step the proof of [Stacks, Tag 07JH] takes when it writes
`M_e = M_{e+1}/p^e M_{e+1}` "since `ℱ` is a crystal", and which the footnote of
[Stacks, Tag 07LF] records as unavailable under the hypotheses of [Stacks, Tag 07JN] alone.  No
hypothesis beyond the crystal condition is used — in particular neither quasi-coherence nor local
quasi-coherence — and the closed-immersion hypothesis is not used either: local surjectivity holds
along *every* morphism of `Cris(X/S)`, by
`...CohomologyRestriction.isLocallySurjective_moduleComparison_of_isIso_moduleComparisonSheaf`.

The crystal condition is the one of [Stacks, Tag 07IS], read — as the source intends — with the
comparison maps of *sheaves* of modules.  The presheaf-level reading is strictly stronger and is
not needed: `IsSurjectiveComparison` asks for local surjectivity, which is invariant under the
sheafification that separates the two pullbacks.  See the module documentation. -/
theorem isSurjectiveComparison_of_isSheafCrystal
    {S : GlobalCrystallineSituation.{u}} {M : SheafOfModules.{u} (structureSheaf S)}
    (h : IsSheafCrystal M) :
    CohomologyRestriction.IsSurjectiveComparison
      (M.val : PresheafOfModules.{u} (crisRing S)) := fun {A B} g _ ↦
  CohomologyRestriction.isLocallySurjective_moduleComparison_of_isIso_moduleComparisonSheaf
    M g (h A B g)

/-- **The restriction to `Cris(X/S)` of a crystal in `𝒪_{X/S}`-modules on `CRIS(X/S)` satisfies
hypothesis (2) of [Stacks, Tag 07JN].**  The restriction is a crystal on the small site by
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_restrictSheafOfModules`. -/
theorem isSurjectiveComparison_restrictSheafOfModules_of_isSheafCrystal
    {S : GlobalCrystallineSituation.{u}}
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (h : GlobalCrystallineSituation.IsSheafCrystal N) :
    CohomologyRestriction.IsSurjectiveComparison
      ((restrictSheafOfModules N).val : PresheafOfModules.{u} (crisRing S)) :=
  isSurjectiveComparison_of_isSheafCrystal (isSheafCrystal_restrictSheafOfModules h)

/-- **The restriction to `Cris(X/S)` of a module on `CRIS(X/S)` which is a crystal for the
comparison maps of presheaves of modules satisfies hypothesis (2) of [Stacks, Tag 07JN].**  The
presheaf-level crystal condition implies the sheaf-level one by
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal`. -/
theorem isSurjectiveComparison_restrictSheafOfModules_of_isCrystal
    {S : GlobalCrystallineSituation.{u}}
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (h : GlobalCrystallineSituation.IsCrystal N) :
    CohomologyRestriction.IsSurjectiveComparison
      ((restrictSheafOfModules N).val : PresheafOfModules.{u} (crisRing S)) :=
  isSurjectiveComparison_restrictSheafOfModules_of_isSheafCrystal
    (GlobalCrystallineSituation.isSheafCrystal_of_isCrystal h)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
