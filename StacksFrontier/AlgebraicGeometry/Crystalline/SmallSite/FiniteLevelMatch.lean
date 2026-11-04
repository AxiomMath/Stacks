module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineCrystallineSite.CompletedToposMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechCohomologyGlue
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDirectImageLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedPushforwardVanishing

/-!
# The uniform finite-level system, and the direct image of [Stacks, Tag 07JL]

[Stacks, Tag 07JL] computes the direct image `g_*` of the morphism of topoi
`Cris^∧(C/A) → Cris(C/A)` as a limit over the finite levels of a completed thickening, and
[Stacks, Tag 07JN] needs that computation for one specific diagram of finite levels: the one with
the *uniform* cutoff `Crystalline.uniformLevel`, over which the presheaf
`Crystalline.GlobalCrystallineSituation.SmallSite.levelLimitSections` — the presheaf whose values
on the objects `D(n)` are the terms `M(n)` of the complex `M(0) → M(1) → ⋯` — is defined.

The two diagrams were built differently.  `Crystalline.finiteLevelSections`, the diagram of
[Stacks, Tag 07JL], runs over a `Crystalline.FiniteLevelSystem`, a structure whose only producer
`Crystalline.exists_finiteLevelSystem` takes its cutoff from
`DividedPowers.eventually_isDividedPowerCompletionLimit` and its terms from a `private`
construction; `Crystalline.levelFunctor`, the diagram of [Stacks, Tag 07JN], runs over the uniform
cutoff `Crystalline.uniformLevel` with terms `Crystalline.levelThickening`.  They are matched by
exhibiting the uniform levels *as* a `FiniteLevelSystem`, `Crystalline.uniformLevelSystem` of
`CompletedDirectImageLevels.lean`, whose diagram of sections is the diagram of
[Stacks, Tag 07JN] on the nose (`Crystalline.finiteLevelSections_uniformLevelSystem`).

## Main definitions and results

* `Crystalline.abelianDirectImageObjObjIsoLimitLevelFunctor` and
  `Crystalline.abelianSheafPushforwardObjObjIsoLimitLevelFunctor` — hence the 07JL computation
  applies to the uniform diagram: `g_*(F)(B) ≅ lim_e F(B/(p)^{N + e})` with `N = uniformLevel`,
  for the right Kan extension and for the site-theoretic pushforward respectively.
* `Crystalline.GlobalCrystallineSituation.SmallSite.abelianDirectImageObjIsoLevelLimitSections` —
  the same statement in the global situation, in the spelling
  `Crystalline.GlobalCrystallineSituation.SmallSite.levelLimitSections` that
  [Stacks, Tag 07JN] uses.
* `HasSurjectiveUniformLevelRestrictions` and `hasSurjectiveLevelRestrictions_wholeSpaceSystem`,
  in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite` — hypothesis (2) of
  [Stacks, Tag 07JN] for the system `(X, T(n)_e, δ(n))`, read on the little affine crystalline
  category, where the map whose surjectivity is at stake is visibly the level drop
  `D(n)/(p)^{N + e + 1} → D(n)/(p)^{N + e}`.  It is the hypothesis
  `Crystalline.GlobalCrystallineSituation.SmallSite.HasSurjectiveLevelRestrictions` that the
  vanishing `R^p lim = 0` consumes, definitionally.
* `Crystalline.surjective_levelThickeningMap_id` and
  `Crystalline.surjective_uniformLevelSystem_transition` — the level drops are surjective on
  rings.

## What is and is not proved

No tag attribute is placed.  [Stacks, Tag 07JN] is **not** proved here, and neither is
[Stacks, Tag 07JL] — the latter's two halves are tagged where they are proved, in
`AffineCrystallineSite/CompletedToposMorphism.lean`, and what is added here is the instantiation
of its computation half at the diagram [Stacks, Tag 07JN] runs over.

Of the four steps that the module docstring of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechCohomologyGlue.lean` lists as separating
the material in the library from
`Crystalline.GlobalCrystallineSituation.SmallSite.IsCompletedSiteComparison`, this file closes the
first — *the two finite-level diagrams are built differently and have to be matched* — and only
that one.  What remains, and is deliberately not stated here under any weaker form:

* **naturality in `B`.**  The isomorphism below is objectwise: for each completed thickening `B`
  separately.  `levelLimitSections` is a functor, so the Leray step, which compares `Sheaf.H` of
  two sheaves on `Cris^∧(C/A)`, needs an isomorphism of the *presheaves*, that is a natural one.
  The objectwise maps are the canonical ones — `CategoryTheory.Functor.ranObjObjIsoLimit` is the
  limit comparison of the pointwise Kan extension, and the projections
  `Crystalline.finiteLevelProjection` of the uniform system are natural in `B` — so naturality is
  a matter of identifying the two cones rather than of new mathematics.
* **the derived half of [Stacks, Tag 07JL]**, `R^p g_* ≅ R^p lim_e` for `p ≥ 1`, which the Leray
  degeneration consumes and which is not in the library in any form.
* **hypothesis (2) of [Stacks, Tag 07JN] itself.**  It is *stated* here on the affine side and
  shown to be what the vanishing consumes, but it is not *discharged* from the hypothesis the
  source makes on `F`, namely
  `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.IsSurjectiveComparison`
  — local surjectivity of the comparison map `c_f`.  Three inputs are missing for that, none of
  them a matter of visibility:
  1. the passage from a surjective `c_f` to a surjective `f`-map.  The lemma
     `Crystalline.GlobalCrystallineSituation.Thickening.range_moduleComparison_app` bounds the
     image of the `f`-map by the image of `c_f`, and the reverse inclusion is what is needed.  The
     fixed-site form of the reverse inclusion is available, as
     `Stacks.NoncommChangeOfRings.Presheaf.isLocallySurjective_of_isLocallySurjective_transpose`,
     but it is stated for a change of rings along the *identity* functor of the site, whereas the
     crystalline comparison map is taken along `TopologicalSpace.Opens.map` of the closed
     immersion; for a non-identity functor of sites the sections of
     `PresheafOfModules.pullback` are a filtered colimit of base changes rather than a base
     change, and the collapse of
     `PresheafOfModules.generatedSubmodule` to the image of the `f`-map needs that the colimit is
     over a category with a terminal object, which here is the statement that the underlying map
     of the thickening is a *homeomorphism* and not merely a closed immersion.
  2. that the level transitions of the system `(X, T(n)_e, δ(n))` are closed immersions of affine
     schemes, which `IsSurjectiveComparison` must be applied to.  The ring-theoretic half is
     `Crystalline.surjective_levelThickeningMap_id` below; the scheme-theoretic half — that the
     transported morphism of `Cris(X/S)` has `IsClosedImmersion` ambient part — is not in the
     library for these maps.  `Crystalline.isClosedImmersion_pAdicLevelSchemeProj_hom` is the
     model, for the base rather than for `T(n)_e`.
  3. quasi-coherence of `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`'s
     `fmapSubmodule`, needed to run the affine vanishing
     `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` on it.  That lemma is about
     `AlgebraicGeometry.Scheme.Modules`, and there is no quasi-coherence theory for the
     presheaf-level `PresheafOfModules.generatedSubmodule` at all; the argument has to be run on
     the sheaf-level `moduleRestrictionSheaf` of `SmallSite/SheafCrystal.lean` instead.
* **the Leray degeneration itself**, which consumes the three previous items.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry

universe u v w

noncomputable section

namespace Crystalline

/-! ### The finite-level system of the uniform cutoff -/

section UniformSystem

variable {s : AffineCrystallineSituation.{u, v}}

/-- The cutoff of `Crystalline.uniformLevelSystem B` is `Crystalline.uniformLevel s`. -/
@[simp]
theorem uniformLevelSystem_cutoff (B : CompletedCrystallineThickening.{u, v, w} s) :
    (uniformLevelSystem B).cutoff = uniformLevel s := rfl

/-- The `e`-th term of `Crystalline.uniformLevelSystem B` is the level thickening
`B/(p)^{N + e}` with `N = Crystalline.uniformLevel s`. -/
@[simp]
theorem uniformLevelSystem_term (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕ) :
    (uniformLevelSystem B).term e =
      levelThickening B (uniformLevel s + e) (isPAdicLevel_uniformLevel_add B e) := rfl

/-- **A level drop of a completed thickening is surjective on rings**: for `k' ≤ k` the map
`B/(p)^k → B/(p)^{k'}` of `Crystalline.levelThickeningMap` of the identity of `B` is surjective,
both sides being quotients of `B`.

This is the ring-theoretic half of the statement that the transition maps of the tower of finite
levels are closed immersions of affine schemes, which is what hypothesis (2) of
[Stacks, Tag 07JN] is applied to; the scheme-theoretic half is not proved in this file. -/
theorem surjective_levelThickeningMap_id {B : CompletedCrystallineThickening.{u, v, w} s}
    {k k' : ℕ} (h : IsPAdicLevel B.ring.ideal B.ring.dividedPowers s.p k)
    (h' : IsPAdicLevel B.ring.ideal B.ring.dividedPowers s.p k') (hk : k' ≤ k) :
    Function.Surjective (levelThickeningMap h h' (𝟙 B) hk).1.hom.toRingHom := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- **The transition maps of the uniform finite-level system are surjective on rings.**  The
special case of `Crystalline.surjective_levelThickeningMap_id` that
`Crystalline.uniformLevelSystem` is built from. -/
theorem surjective_uniformLevelSystem_transition
    (B : CompletedCrystallineThickening.{u, v, w} s) {e e' : ℕ} (h : e ≤ e') :
    Function.Surjective ((uniformLevelSystem B).transition h).1.hom.toRingHom :=
  surjective_levelThickeningMap_id _ _ _

end UniformSystem

/-! ### The direct image of [Stacks, Tag 07JL] over the uniform levels -/

section DirectImage

variable {s : AffineCrystallineSituation.{u, v}}

/-- **The direct image of [Stacks, Tag 07JL], computed over the uniform finite levels.**  For an
abelian presheaf `F` on the ordinary affine crystalline category and a completed thickening `B`,

`g_*(F)(B) ≅ lim_e F(B/(p)^{N + e})`,

the limit being taken over the diagram `Crystalline.levelFunctor` of the uniform cutoff
`N = Crystalline.uniformLevel s`.

This is `Crystalline.abelianDirectImageObjObjIsoLimitFiniteLevelSections` at the system
`Crystalline.uniformLevelSystem`, whose diagram of sections is that diagram by
`Crystalline.finiteLevelSections_uniformLevelSystem`.  It is objectwise in `B`; see the
module docstring. -/
def abelianDirectImageObjObjIsoLimitLevelFunctor
    (F : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)})
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    ((abelianDirectImage s).obj F).obj B ≅
      limit ((Functor.curryObj (levelFunctor s)).obj B ⋙ F) :=
  abelianDirectImageObjObjIsoLimitFiniteLevelSections F (uniformLevelSystem B) ≪≫
    HasLimit.isoOfNatIso (eqToIso (finiteLevelSections_uniformLevelSystem B F))

/-- **The sections of the site-theoretic pushforward of [Stacks, Tag 07JL] over the uniform
finite levels.**  The same statement as
`Crystalline.abelianDirectImageObjObjIsoLimitLevelFunctor` for the pushforward of abelian sheaves
for the chaotic topologies rather than for the right Kan extension, which is the spelling the
Leray step of [Stacks, Tag 07JN] consumes. -/
def abelianSheafPushforwardObjObjIsoLimitLevelFunctor
    (s : AffineCrystallineSituation.{u, v})
    (F : Sheaf (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} s)ᵒᵖ)
      Ab.{max u v (w + 1)})
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    ((completedAbelianSheafEquivalence.{u, v, w} s).functor.obj
        ((abelianSheafPushforward s).obj F)).obj B ≅
      limit ((Functor.curryObj (levelFunctor s)).obj B ⋙
        (abelianSheafEquivalence.{u, v, w} s).functor.obj F) :=
  abelianSheafPushforwardObjObjIsoLimitFiniteLevelSections s F (uniformLevelSystem B) ≪≫
    HasLimit.isoOfNatIso (eqToIso (finiteLevelSections_uniformLevelSystem B _))

end DirectImage

end Crystalline

/-! ### The identification in the global situation -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable (S : GlobalCrystallineSituation.{u}) (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The value of the direct image of [Stacks, Tag 07JL] is the value of
`Crystalline.GlobalCrystallineSituation.SmallSite.levelLimitSections`.**  For an abelian presheaf
`F` on `Cris(X/S)` and a completed thickening `B` of the little affine crystalline category, the
value at `B` of the direct image of the sections of `F` read on that category is the limit
`lim_e F(B/(p)^{N + e})`, which is the value at `B` of the presheaf `levelLimitSections` whose
values on the objects `D(n)` are the terms `M(n)` of [Stacks, Tag 07JN].

This is `Crystalline.abelianDirectImageObjObjIsoLimitLevelFunctor` at the presheaf
`Crystalline.GlobalCrystallineSituation.SmallSite.affineSections`; it is the first of the four
steps the module docstring of `CechCohomologyGlue.lean` lists, and it is objectwise in `B`. -/
def abelianDirectImageObjIsoLevelLimitSections
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) :
    ((abelianDirectImage (affineSituation S hp)).obj (affineSections S hp F)).obj B ≅
      (levelLimitSections S hp F).obj B :=
  abelianDirectImageObjObjIsoLimitLevelFunctor (affineSections S hp F) B

/-! ### Hypothesis (2) of [Stacks, Tag 07JN] on the affine side -/

/-- **Hypothesis (2) of [Stacks, Tag 07JN] for the system `(X, T(n)_e, δ(n))`, read on the little
affine crystalline category.**  The restriction map of `F` along the level drop
`D(n)/(p)^{N + e + 1} ⟶ D(n)/(p)^{N + e}` is surjective, for every `n` and every `e`.

This is the same condition as
`Crystalline.GlobalCrystallineSituation.SmallSite.HasSurjectiveLevelRestrictions` for the system
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` — the two are equal by
definition, which is `hasSurjectiveLevelRestrictions_wholeSpaceSystem` below — but written with
the level maps of `Crystalline.levelThickeningMap` rather than with the transported system, so
that the map whose surjectivity is at stake is visibly the quotient
`D(n)/(p)^{N + e + 1} → D(n)/(p)^{N + e}` of divided power rings.  That is the shape in which the
source's hypothesis (2) is used: the closed immersion whose comparison map `c_f` must be
surjective is exactly this level drop. -/
def HasSurjectiveUniformLevelRestrictions
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Prop :=
  ∀ n e : ℕ, Function.Surjective (ConcreteCategory.hom
    ((affineSections S hp F).map
      (((affineLevelSystem (affineSituation S hp) (canonicalPresentation _)
            (canonicalPresentation_surjective _)).obj ⦋n⦌).map
        ((homOfLE (Nat.le_succ e)).op : (op (e + 1) : ℕᵒᵖ) ⟶ op e))))

/-- **Hypothesis (2) of [Stacks, Tag 07JN] on the affine side is the hypothesis the vanishing
`R^p lim = 0` consumes.**  The surjectivity of the level drops of `D(•)`, read through the
affine-to-global equivalence, *is*
`Crystalline.GlobalCrystallineSituation.SmallSite.HasSurjectiveLevelRestrictions` for the system
`(X, T(n)_e, δ(n))`, so it feeds
`Crystalline.GlobalCrystallineSituation.SmallSite.isZero_firstDerivedLimit_sectionSystem` and
`Crystalline.GlobalCrystallineSituation.SmallSite.isZero_homology_rightDerivedLimit_sectionSystem`
directly.  The identification is definitional: the system `(X, T(n)_e, δ(n))` is by construction
`Crystalline.affineLevelSystem` carried across the equivalence. -/
theorem hasSurjectiveLevelRestrictions_wholeSpaceSystem
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : HasSurjectiveUniformLevelRestrictions S hp F) :
    HasSurjectiveLevelRestrictions (wholeSpaceSystem S hp) F := h

end Crystalline.GlobalCrystallineSituation.SmallSite

end
