module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineChaoticCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDirectImageLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelLimitCollapse
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# The direct image of Stacks 07JL is the level-limit presheaf, naturally in the coefficients

Work in an affine crystalline situation `(A, I, γ) → C` ([Stacks, Tag 07MD]).  The degree-zero
half of [Stacks, Tag 07JL] is available in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompletedDirectImageLevels.lean` as an
isomorphism of presheaves on `Cris^∧(C/A)`

`g_* 𝓕 ≅ (B ↦ lim_e 𝓕(B/(p)^{N + e}))`

for each fixed abelian presheaf `𝓕` on `Cris(C/A)`, natural in the completed thickening `B` but
*objectwise in `𝓕`*.  This file upgrades it to an isomorphism of **functors of `𝓕`**, and uses
that upgrade to convert the collapse of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelLimitCollapse.lean` into the vanishing
of the higher direct images of [Stacks, Tag 07JL],

`R ⁿ g_* 𝓖 = 0` for `n ≥ 1`,

for an abelian sheaf `𝓖` on `𝒞 = (Cris(C/A))ᵒᵖ` whose level restrictions are surjective.

The naturality in `𝓕` reduces, by `CategoryTheory.Limits.limit.hom_ext`, to the naturality of the
counit of the right Kan extension in the coefficient presheaf: that is
`Crystalline.ranCounitApp_naturality_coeff` below, and it is the one new mathematical input of
the first half of the file.

## Main definitions

* `Crystalline.levelLimitPresheafFunctor` — the level-limit presheaf as a *functor* of the
  coefficient presheaf, `𝓕 ↦ (B ↦ lim_e 𝓕(B/(p)^{N + e}))`.  Its value is
  `Crystalline.levelLimitPresheaf` on the nose.
* `Crystalline.directImageToLevelLimitNatTrans` — the comparison of
  `Crystalline.directImageToLevelLimit` as a morphism of functors
  `(crystallineToCompleted s).ran ⟶ levelLimitPresheafFunctor s`.
* `Crystalline.completedSheafSections` — the sections over a completed thickening of an abelian
  sheaf on `𝒞^∧`, as a functor; this is the `ev_B` of the composition below.

## Main results

* `Crystalline.ranCounitApp_naturality_coeff` — the counit of the right Kan extension along the
  concrete inclusion is natural in the coefficient presheaf.
* `Crystalline.ranIsoLevelLimitPresheafFunctor` and
  `Crystalline.abelianDirectImageIsoLevelLimitPresheafFunctor` — **`g_* ≅ lim_e` as functors of
  the coefficient presheaf**, for the right Kan extension along
  `Crystalline.crystallineToCompleted` and for `Crystalline.abelianDirectImage`.
* `Crystalline.pushforwardCompSectionsIso` — **`ev_B ∘ g_* ≅ lim ∘ L_B`** as functors of the
  coefficient *sheaf*, where `g_*` is `Crystalline.abelianSheafPushforward`, the direct image of
  the morphism of topoi of [Stacks, Tag 07JL], and `lim ∘ L_B` is the functor whose derived
  functors `LevelLimitCollapse.lean` computes.
* `Crystalline.isZero_rightDerived_abelianSheafPushforward_of_surjective` —
  **`R ⁿ g_* 𝓖 = 0` for `n ≥ 1`** when the level restrictions of `𝓖` are surjective.
* `Crystalline.lerayPushforwardRightDerivedSectionsIso` and
  `Crystalline.sheafHAddEquivPushforward_of_surjective` — the Leray degeneration along that
  vanishing: `R ʲ Γ(𝒞^∧, g_* 𝓖) ≅ R ʲ Γ(𝒞, 𝓖)`, and the same read as sheaf cohomology,
  `H ʲ(𝒞^∧, g_* 𝓖) ≅ H ʲ(𝒞, 𝓖)`.
* `...SmallSite.isAbelianCompletedLerayComparison_of_surjective` and
  `...SmallSite.isCompletedLerayComparison_of_surjective` — the same in the spelling of
  `...SmallSite.IsAbelianCompletedLerayComparison` and of
  `...SmallSite.IsCompletedLerayComparison`, **discharging those propositions** under the
  surjectivity hypothesis; the second is the first at `abelianSheaf F`.
* `...SmallSite.computesCohomology_wholeSpaceSystem_of_abelianSurjective` and
  `...SmallSite.computesCohomology_wholeSpaceSystem_of_surjective` — hence the conclusion of
  [Stacks, Tag 07JN] for the source's system, under the surjectivity hypothesis together with
  `...SmallSite.Vanishing07JJ` in the abelian case and local quasi-coherence in the module case.

## What is and is not proved

**No tag attribute is placed.**  The morphism-of-topoi half of [Stacks, Tag 07JL] is attributed
where it lives, in
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineCrystallineSite/CompletedToposMorphism.lean`.

What is proved, with no hypothesis beyond those of the ambient affine crystalline situation:
the isomorphism `g_* ≅ lim_e` of functors of the coefficient presheaf, and its evaluation
`ev_B ∘ g_* ≅ lim ∘ L_B` on the sheaf side.

The vanishing `R ⁿ g_* 𝓖 = 0`, the Leray degeneration and
`isCompletedLerayComparison_of_surjective` carry exactly **one** hypothesis beyond the ambient
situation, named in their statements and repeated here because it is genuine and nothing below
discharges it:

> for every completed thickening `B` of `Cris^∧(C/A)` and every `e`, the restriction map of `𝓖`
> along the level drop `B/(p)^{N + e + 1} ↠ B/(p)^{N + e}` is surjective.

That is hypothesis (2) of [Stacks, Tag 07JN], stated for the uniform level system
`Crystalline.uniformLevelSystem` of every object of `Cris^∧(C/A)` at once.  It is **not** proved
here; it is an assumption on the coefficient sheaf, and in [Stacks, Tag 07JN] it is an assumption
of the theorem.

What is **not** proved is [Stacks, Tag 07JN].  Its conclusion is reached only in the conditional
forms `computesCohomology_wholeSpaceSystem_of_abelianSurjective` and
`computesCohomology_wholeSpaceSystem_of_surjective`, which carry that surjectivity hypothesis
together with, respectively, `...SmallSite.Vanishing07JJ` of the coefficient sheaf and the local
quasi-coherence of the coefficient module (a hypothesis of [Stacks, Tag 07JK] and of the source;
the first is what the second is used for).  Nothing here discharges any of them, and the
coefficient is an arbitrary abelian sheaf in the first form: the Leray degeneration of this file
uses no module structure.  In particular **the surjectivity of the level restrictions is not
derived from the hypotheses of [Stacks, Tag 07JN]**; deriving it is a separate step, carried out in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemCohomology.lean`.  This note
previously listed a third hypothesis, `HasBinaryCoproducts (Cris^∧(C/A))`, inherited from the
Čech engine; the engine now asks only for the powers of its covering object, so it is gone.

## Implementation notes

The functor `Crystalline.levelLimitPresheafFunctor` is assembled out of whiskering functors
rather than written with explicit `obj` and `map` fields, so that its functoriality is free and
its value at a presheaf is `Crystalline.levelLimitPresheaf` definitionally.  The same strict
associativity of `CategoryTheory.Functor.comp` is what makes
`Crystalline.levelLimitPresheafFunctor_comp_evaluation` hold by `rfl`: evaluating the level-limit
presheaf at `B` is precomposition with the diagram of uniform levels of `B` followed by `lim`,
which is `Crystalline.finiteLevelSectionsFunctor` of `Crystalline.uniformLevelSystem` followed by
`lim`.

The step from `R ⁿ (ev_B ∘ g_*) ≅ ev_B (R ⁿ g_*)` is
`CategoryTheory.Functor.rightDerivedCompIso` for the exact functor `ev_B`; it does **not** need
`g_*` to preserve injectives, unlike `Stacks.RightDerivedComp.objIso`.  Preservation of
injectives (`Crystalline.preservesInjectiveObjects_abelianSheafPushforward`) is used only in the
Leray step at the end, where `Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso` asks for it.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Crystalline

universe u v w

variable {s : AffineCrystallineSituation.{u, v}}

/-! ### The level-limit presheaf as a functor of the coefficient presheaf -/

/-- **The level-limit presheaf as a functor of its coefficients**: the functor sending an abelian
presheaf `𝓕` on `Cris(C/A)` to the presheaf `B ↦ lim_e 𝓕(B/(p)^{N + e})` on `Cris^∧(C/A)`.

It is built out of whiskering functors — whisker `𝓕` onto the diagrams of finite levels, take
limits, then precompose with the diagram of uniform levels of a completed thickening — so that
its value at `𝓕` is `Crystalline.levelLimitPresheaf` definitionally. -/
def levelLimitPresheafFunctor (s : AffineCrystallineSituation.{u, v}) :
    (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) ⥤
      (CompletedCrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :=
  Functor.whiskeringRight ℕᵒᵖ (CrystallineThickening.{u, v, w} s) Ab.{max u v (w + 1)} ⋙
    (Functor.whiskeringRight (ℕᵒᵖ ⥤ CrystallineThickening.{u, v, w} s)
        (ℕᵒᵖ ⥤ Ab.{max u v (w + 1)}) Ab.{max u v (w + 1)}).obj lim ⋙
      (Functor.whiskeringLeft (CompletedCrystallineThickening.{u, v, w} s)
        (ℕᵒᵖ ⥤ CrystallineThickening.{u, v, w} s) Ab.{max u v (w + 1)}).obj
        (Functor.curryObj (levelFunctor s))

/-- The value of `Crystalline.levelLimitPresheafFunctor` is `Crystalline.levelLimitPresheaf`. -/
theorem levelLimitPresheafFunctor_obj
    (𝓕 : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :
    (levelLimitPresheafFunctor s).obj 𝓕 = levelLimitPresheaf s 𝓕 :=
  rfl

/-- The action of `Crystalline.levelLimitPresheafFunctor` on a morphism of coefficient
presheaves, at a completed thickening: the map induced on the limits over the uniform levels. -/
theorem levelLimitPresheafFunctor_map_app
    {𝓕 𝓕' : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}} (α : 𝓕 ⟶ 𝓕')
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    ((levelLimitPresheafFunctor s).map α).app B =
      limMap (Functor.whiskerLeft (levelDiagram B) α) :=
  rfl

/-! ### Naturality in the coefficient presheaf -/

variable {𝓕 𝓕' : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}}

/-- **The counit of the right Kan extension along the concrete inclusion is natural in the
coefficient presheaf.**  This is `CategoryTheory.Functor.ranCounit` being a natural
transformation of functors on the coefficient category, read at one object of `Cris(C/A)`, and it
is the input to which naturality of `Crystalline.directImageToLevelLimit` in the coefficients
reduces. -/
theorem ranCounitApp_naturality_coeff (α : 𝓕 ⟶ 𝓕') (Y : CrystallineThickening.{u, v, w} s) :
    ((crystallineToCompleted s).ran.map α).app ((crystallineToCompleted s).obj Y) ≫
        ranCounitApp 𝓕' Y =
      ranCounitApp 𝓕 Y ≫ α.app Y :=
  congr_app ((crystallineToCompleted s).ranCounit.naturality α) Y

/-- **The legs of the cone of level sections are natural in the coefficient presheaf.**  This is
`Crystalline.ranCounitApp_naturality_coeff` together with naturality of `ran.map α` at the level
projection. -/
theorem levelLimitLeg_naturality_coeff (α : 𝓕 ⟶ 𝓕')
    (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕᵒᵖ) :
    ((crystallineToCompleted s).ran.map α).app B ≫ levelLimitLeg 𝓕' B e =
      levelLimitLeg 𝓕 B e ≫ α.app ((levelDiagram B).obj e) := by
  dsimp only [levelLimitLeg]
  rw [← Category.assoc, ← ((crystallineToCompleted s).ran.map α).naturality (levelProjection B e),
    Category.assoc, ranCounitApp_naturality_coeff, Category.assoc]

/-- **The value at a completed thickening of the comparison morphism is natural in the
coefficient presheaf.**  By `CategoryTheory.Limits.limit.hom_ext` this is
`Crystalline.levelLimitLeg_naturality_coeff` at each level. -/
theorem directImageToLevelLimitApp_naturality_coeff (α : 𝓕 ⟶ 𝓕')
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    ((crystallineToCompleted s).ran.map α).app B ≫ directImageToLevelLimitApp 𝓕' B =
      directImageToLevelLimitApp 𝓕 B ≫ limMap (Functor.whiskerLeft (levelDiagram B) α) := by
  refine limit.hom_ext fun e => ?_
  rw [Category.assoc, directImageToLevelLimitApp_comp_π, Category.assoc, limMap_π,
    ← Category.assoc, directImageToLevelLimitApp_comp_π]
  exact levelLimitLeg_naturality_coeff α B e

/-- **The comparison `g_* 𝓕 ⟶ lim_e 𝓕(B/(p)^{N + e})` as a morphism of functors of `𝓕`.**  This
is `Crystalline.directImageToLevelLimit` with its naturality in the coefficient presheaf
supplied. -/
def directImageToLevelLimitNatTrans (s : AffineCrystallineSituation.{u, v}) :
    ((crystallineToCompleted s).ran :
        (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) ⥤ _) ⟶
      levelLimitPresheafFunctor s where
  app 𝓕 := directImageToLevelLimit 𝓕
  naturality _ _ α :=
    NatTrans.ext (funext fun B => directImageToLevelLimitApp_naturality_coeff α B)

/-- The isomorphism `Crystalline.directImageIsoLevelLimit` is the comparison morphism. -/
theorem directImageIsoLevelLimit_hom
    (𝓕 : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :
    (directImageIsoLevelLimit 𝓕).hom = directImageToLevelLimit 𝓕 :=
  NatTrans.ext (funext fun B => directImageIsoLevelLimitApp_hom 𝓕 B)

/-- **`g_* ≅ lim_e` as functors of the coefficient presheaf**, for the right Kan extension along
`Crystalline.crystallineToCompleted`: the degree-zero half of [Stacks, Tag 07JL], natural in the
coefficient presheaf as well as in the completed thickening.

Objectwise this is `Crystalline.directImageIsoLevelLimit`; what is added is the naturality
square, which is `Crystalline.directImageToLevelLimitApp_naturality_coeff`. -/
def ranIsoLevelLimitPresheafFunctor (s : AffineCrystallineSituation.{u, v}) :
    ((crystallineToCompleted s).ran :
        (CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) ⥤ _) ≅
      levelLimitPresheafFunctor s :=
  NatIso.ofComponents directImageIsoLevelLimit (fun α => by
    rw [directImageIsoLevelLimit_hom, directImageIsoLevelLimit_hom]
    exact (directImageToLevelLimitNatTrans s).naturality α)

/-- **`g_* ≅ lim_e` as functors of the coefficient presheaf**, for
`Crystalline.abelianDirectImage`, the direct image of [Stacks, Tag 07JL] on abelian presheaves.

This is `Crystalline.ranIsoLevelLimitPresheafFunctor`, read for `Crystalline.abelianDirectImage`,
which is by definition the right Kan extension along `Crystalline.crystallineToCompleted`, exactly
as `Crystalline.abelianDirectImageIsoLevelLimitPresheaf` is objectwise. -/
def abelianDirectImageIsoLevelLimitPresheafFunctor (s : AffineCrystallineSituation.{u, v}) :
    (abelianDirectImage.{u, v, w} s) ≅ levelLimitPresheafFunctor s :=
  ranIsoLevelLimitPresheafFunctor s

/-! ### Evaluating at a completed thickening -/

/-- **Evaluating the level-limit presheaf at a completed thickening is `lim ∘ L_B`.**  Both sides
send `𝓕` to `lim_e 𝓕(B/(p)^{N + e})`: on the left by precomposing with the diagram of uniform
levels of `B` and taking the limit, on the right by the level functor of
`Crystalline.uniformLevelSystem` followed by `lim`.  The two diagrams agree by
`Crystalline.diagram_uniformLevelSystem`, so the identification is definitional. -/
theorem levelLimitPresheafFunctor_comp_evaluation
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    levelLimitPresheafFunctor s ⋙
        (evaluation (CompletedCrystallineThickening.{u, v, w} s) Ab.{max u v (w + 1)}).obj B =
      finiteLevelSectionsFunctor (uniformLevelSystem B) ⋙ lim :=
  rfl

/-- **The sections over a completed thickening of an abelian sheaf on `𝒞^∧`**, as a functor: the
identification of chaotic abelian sheaves on `𝒞^∧` with abelian presheaves on `Cris^∧(C/A)`
followed by evaluation at `B`.  This is the `ev_B` of the composition below; it is exact, being an
equivalence followed by an evaluation functor. -/
abbrev completedSheafSections (s : AffineCrystallineSituation.{u, v})
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    Sheaf (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)} ⥤
      Ab.{max u v (w + 1)} :=
  (completedAbelianSheafEquivalence.{u, v, w} s).functor ⋙
    (evaluation (CompletedCrystallineThickening.{u, v, w} s) Ab.{max u v (w + 1)}).obj B

/-- **The identification of chaotic abelian sheaves on `𝒞^∧` with abelian presheaves on
`Cris^∧(C/A)` is additive**: it is an equivalence, hence preserves binary products. -/
instance completedAbelianSheafEquivalence_functor_additive :
    ((completedAbelianSheafEquivalence.{u, v, w} s).functor).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of that identification is additive, for the same reason. -/
instance completedAbelianSheafEquivalence_inverse_additive :
    ((completedAbelianSheafEquivalence.{u, v, w} s).inverse).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **`ev_B ∘ g_* ≅ lim ∘ L_B` as functors of the coefficient sheaf**, for `g_*` the direct image
`Crystalline.abelianSheafPushforward` of the morphism of topoi of [Stacks, Tag 07JL]: the sections
over `B` of the direct image of an abelian sheaf `𝓖` on `𝒞` are the limit over the uniform finite
levels of `B` of the sections of `𝓖`, naturally in `𝓖`.

The three steps are `Crystalline.abelianSheafPushforwardIsoDirectImage`, which identifies the
direct image on sheaves with the right Kan extension on presheaves;
`Crystalline.abelianDirectImageIsoLevelLimitPresheafFunctor`, the naturality in the coefficients
proved above; and `Crystalline.levelLimitPresheafFunctor_comp_evaluation`, which is definitional.

This is the identification that the "What is and is not proved" note of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelLimitCollapse.lean` records as the
missing first step towards `R ⁿ g_* ≅ R ⁿ lim_e`. -/
def pushforwardCompSectionsIso (s : AffineCrystallineSituation.{u, v})
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    abelianSheafPushforward.{u, v, w} s ⋙ completedSheafSections s B ≅
      sheafFiniteLevelSectionsFunctor (uniformLevelSystem B) ⋙ lim :=
  Functor.isoWhiskerRight (abelianSheafPushforwardIsoDirectImage.{u, v, w} s)
      ((evaluation (CompletedCrystallineThickening.{u, v, w} s) Ab.{max u v (w + 1)}).obj B) ≪≫
    Functor.isoWhiskerLeft (abelianSheafEquivalence.{u, v, w} s).functor
      (Functor.isoWhiskerRight (abelianDirectImageIsoLevelLimitPresheafFunctor.{u, v, w} s)
        ((evaluation (CompletedCrystallineThickening.{u, v, w} s) Ab.{max u v (w + 1)}).obj B))

/-! ### The vanishing of the higher direct images -/

/-- **The higher direct images of [Stacks, Tag 07JL] vanish on a sheaf with surjective level
restrictions**: `R ⁿ g_* 𝓖 = 0` for every `n ≥ 1`, where `g_*` is
`Crystalline.abelianSheafPushforward`.

This is the derived half of [Stacks, Tag 07JL] in the form the Leray degeneration of
[Stacks, Tag 07JN] consumes.  The proof is: a sheaf on `𝒞^∧` vanishes as soon as its sections
over every completed thickening `B` vanish (`CategoryTheory.Functor.isZero_iff` through
`Crystalline.completedAbelianSheafEquivalence`); the sections functor `ev_B` is exact, so it may
be pulled out of the right derived functor
(`CategoryTheory.Functor.rightDerivedCompIso`); and `ev_B ∘ g_*` is `lim ∘ L_B` by
`Crystalline.pushforwardCompSectionsIso`, whose higher right derived functors vanish by
`Crystalline.isZero_rightDerivedLevelLimit_of_surjective`.

The hypothesis `h𝓖` is hypothesis (2) of [Stacks, Tag 07JN]: for every completed thickening `B`
and every `e`, the restriction map of `𝓖` along the level drop
`B/(p)^{N + e + 1} ↠ B/(p)^{N + e}` is surjective.  It is genuine, and nothing here discharges
it. -/
theorem isZero_rightDerived_abelianSheafPushforward_of_surjective
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)})
    (h𝓖 : ∀ (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        (((abelianSheafEquivalence.{u, v, w} s).functor.obj 𝓖).map
          ((uniformLevelSystem B).transition (Nat.le_succ e)))))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((abelianSheafPushforward.{u, v, w} s).rightDerived n).obj 𝓖) := by
  have key : ∀ B : CompletedCrystallineThickening.{u, v, w} s,
      IsZero (((completedAbelianSheafEquivalence.{u, v, w} s).functor.obj
        (((abelianSheafPushforward.{u, v, w} s).rightDerived n).obj 𝓖)).obj B) := by
    intro B
    refine (isZero_rightDerivedLevelLimit_of_surjective (uniformLevelSystem B) 𝓖 (h𝓖 B) n
      hn).of_iso ?_
    exact ((Functor.rightDerivedCompIso (abelianSheafPushforward.{u, v, w} s)
        (completedSheafSections s B) n).app 𝓖).symm ≪≫
      (Functor.rightDerivedIsoOfNatIso (pushforwardCompSectionsIso.{u, v, w} s B) n).app 𝓖
  have hfun : IsZero ((completedAbelianSheafEquivalence.{u, v, w} s).functor.obj
      (((abelianSheafPushforward.{u, v, w} s).rightDerived n).obj 𝓖)) :=
    (Functor.isZero_iff _).2 key
  exact ((completedAbelianSheafEquivalence.{u, v, w} s).inverse.map_isZero hfun).of_iso
    ((completedAbelianSheafEquivalence.{u, v, w} s).unitIso.app _)

/-! ### The Leray degeneration -/

/-- The global sections of abelian sheaves on `𝒞 = (Cris(C/A))ᵒᵖ` are additive, being a right
adjoint. -/
instance additive_gamma_littleChaotic :
    (Sheaf.Γ (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{max u v (w + 1), w, max u v (w + 1)} _

/-- The global sections of abelian sheaves on `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` are additive. -/
instance additive_gamma_completedChaotic :
    (Sheaf.Γ (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{max u v (w + 1), w, max u v (w + 1)} _

/-- **The Leray degeneration along the vanishing of the higher direct images of
[Stacks, Tag 07JL]**: for an abelian sheaf `𝓖` on `𝒞` whose level restrictions are surjective and
every degree `j`,

`R ʲ Γ(𝒞^∧, g_* 𝓖) ≅ R ʲ Γ(𝒞, 𝓖)`.

The edge morphism of the pair `(g_*, Γ(𝒞^∧, -))` is invertible in every degree by
`Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso`, whose hypotheses on `g_*` are
`Crystalline.abelianSheafPushforward_additive`,
`Crystalline.preservesFiniteLimits_abelianSheafPushforward`,
`Crystalline.preservesInjectiveObjects_abelianSheafPushforward` and the vanishing
`Crystalline.isZero_rightDerived_abelianSheafPushforward_of_surjective`; and the right derived
functors of the composite are those of `Γ(𝒞, -)` by
`Crystalline.gammaCompAbelianSheafPushforwardIso`.

The surjectivity hypothesis is hypothesis (2) of [Stacks, Tag 07JN] and is not discharged. -/
def lerayPushforwardRightDerivedSectionsIso
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)})
    (h𝓖 : ∀ (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        (((abelianSheafEquivalence.{u, v, w} s).functor.obj 𝓖).map
          ((uniformLevelSystem B).transition (Nat.le_succ e)))))
    (j : ℕ) :
    (((Sheaf.Γ (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}).rightDerived
        j).obj ((abelianSheafPushforward.{u, v, w} s).obj 𝓖)) ≅
      (((Sheaf.Γ (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}).rightDerived j).obj
        𝓖) :=
  Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso (abelianSheafPushforward.{u, v, w} s)
      (Sheaf.Γ (completedChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) 𝓖 j
      (fun q hq _ => isZero_rightDerived_abelianSheafPushforward_of_surjective 𝓖 h𝓖 q hq) ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (gammaCompAbelianSheafPushforwardIso.{u, v, w} s) j).app 𝓖

/-- **The Leray degeneration read as sheaf cohomology**: for an abelian sheaf `𝓖` on `𝒞` whose
level restrictions are surjective and every degree `j`,

`H ʲ(𝒞^∧, g_* 𝓖) ≅ H ʲ(𝒞, 𝓖)`.

This is `Crystalline.lerayPushforwardRightDerivedSectionsIso` read through
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`, which identifies the right derived
functors of global sections with the cohomology functors on each of the two sites.

The surjectivity hypothesis is hypothesis (2) of [Stacks, Tag 07JN] and is not discharged. -/
def sheafHAddEquivPushforward_of_surjective
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)})
    (h𝓖 : ∀ (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        (((abelianSheafEquivalence.{u, v, w} s).functor.obj 𝓖).map
          ((uniformLevelSystem B).transition (Nat.le_succ e)))))
    (j : ℕ) :
    Sheaf.H.{max u v (w + 1), max u v (w + 1)}
        ((abelianSheafPushforward.{u, v, w} s).obj 𝓖) j ≃+
      Sheaf.H.{max u v (w + 1), max u v (w + 1)} 𝓖 j :=
  (((Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{max u v (w + 1), w,
            max u v (w + 1)} (completedChaoticTopology.{u, v, w} s) j).app
          ((abelianSheafPushforward.{u, v, w} s).obj 𝓖)).symm ≪≫
      lerayPushforwardRightDerivedSectionsIso 𝓖 h𝓖 j ≪≫
        (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{max u v (w + 1), w,
          max u v (w + 1)} (littleChaoticTopology.{u, v, w} s) j).app 𝓖).addCommGroupIsoToAddEquiv

end Crystalline

/-! ### The Leray step of Stacks 07JN -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

universe u

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **The restriction of a sheaf on `Cris(X/S)` to the little affine chaotic site `𝒞`.**  This is
the abelian sheaf on `𝒞 = (Cris(C/A))ᵒᵖ` whose direct image along [Stacks, Tag 07JL] the Leray
step of [Stacks, Tag 07JN] is about: restrict `F` to the subcategory `𝒞_X ⊆ Cris(X/S)` of
thickenings of the whole of `X`, then transport across the equivalence `𝒞_X ≌ 𝒞`. -/
abbrev littleChaoticRestriction (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    Sheaf (littleChaoticTopology.{u, u, u} (affineSituation S hp)) AddCommGrpCat.{u + 1} :=
  littleChaoticSheafOfWhole hp ((restrictToWhole S).obj F)

omit [WholeSpacePresentation S hp] in
/-- **The affine-side sections of `F` are the sections of its restriction to `𝒞`.**  The presheaf
`Crystalline.GlobalCrystallineSituation.SmallSite.affineSections` on `Cris(C/A)` is the abelian
sheaf `littleChaoticRestriction` read through `Crystalline.abelianSheafEquivalence`; the two
agree on the nose, both being `F` precomposed with the transport of the little affine crystalline
category into `Cris(X/S)ᵒᵖ`. -/
theorem affineSections_eq (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    affineSections S hp F.obj =
      (abelianSheafEquivalence.{u, u, u} (affineSituation S hp)).functor.obj
        (littleChaoticRestriction hp F) :=
  rfl

/-- **The direct image of [Stacks, Tag 07JL] of the restriction of `F` to `𝒞`, read as a
presheaf.**  The sheaf `g_*(F|_𝒞)` on `𝒞^∧` is, through
`Crystalline.completedAbelianSheafEquivalence`, the right Kan extension
`Crystalline.abelianDirectImage` of the affine-side sections of `F` — which is the spelling in
which `...SmallSite.IsCompletedLerayComparison` is stated.

This is `Crystalline.abelianSheafPushforwardIsoDirectImage`, the identification of the sheaf
pushforward with the Kan extension, carried back along the equivalence. -/
def completedChaoticSheafOfPresheafIsoPushforward
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    completedChaoticSheafOfPresheaf (affineSituation S hp)
        ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
          (affineSections S hp F.obj)) ≅
      (abelianSheafPushforward.{u, u, u} (affineSituation S hp)).obj
        (littleChaoticRestriction hp F) :=
  (completedAbelianSheafEquivalence.{u, u, u} (affineSituation S hp)).inverse.mapIso
      ((abelianSheafPushforwardIsoDirectImage.{u, u, u} (affineSituation S hp)).app
        (littleChaoticRestriction hp F)).symm ≪≫
    ((completedAbelianSheafEquivalence.{u, u, u} (affineSituation S hp)).unitIso.app
      ((abelianSheafPushforward.{u, u, u} (affineSituation S hp)).obj
        (littleChaoticRestriction hp F))).symm

omit [WholeSpacePresentation S hp] in
/-- **The Leray step of [Stacks, Tag 07JN], granted the surjectivity of the level
restrictions.**  For an abelian sheaf `G` on `Cris(X/S)` whose affine-side sections have
surjective restriction maps along every level drop `B/(p)^{N + e + 1} ↠ B/(p)^{N + e}`,

`H ʲ(𝒞^∧, g_*(G|_𝒞)) ≅ H ʲ(𝒞, G|_𝒞)` for every `j`,

which is
`Crystalline.GlobalCrystallineSituation.SmallSite.IsAbelianCompletedLerayComparison`.

The isomorphism is `Crystalline.sheafHAddEquivPushforward_of_surjective`, read through
`completedChaoticSheafOfPresheafIsoPushforward` to match the spelling of that proposition.

**No tag attribute is placed**, and this does not prove [Stacks, Tag 07JN].  The hypothesis
`hG` is hypothesis (2) of [Stacks, Tag 07JN] — the surjectivity of the level restrictions — and
it is genuine: nothing here discharges it.  It is stated for the uniform level system
`Crystalline.uniformLevelSystem` of every object of `Cris^∧(C/A)` at once, which is what the
vanishing of the higher direct images needs.

The coefficient sheaf is an arbitrary abelian sheaf: the module structure plays no part in the
Leray degeneration, which sees only the sections of the coefficient sheaf on the affine side.  The
module-valued statement is `isCompletedLerayComparison_of_surjective` below. -/
theorem isAbelianCompletedLerayComparison_of_surjective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp G.obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) :
    IsAbelianCompletedLerayComparison hp G := fun j =>
  ⟨(((Sheaf.functorH (completedChaoticTopology.{u, u, u} (affineSituation S hp)) j).mapIso
        (completedChaoticSheafOfPresheafIsoPushforward hp G)).addCommGroupIsoToAddEquiv).trans
    (sheafHAddEquivPushforward_of_surjective (littleChaoticRestriction hp G) hG j)⟩

omit [WholeSpacePresentation S hp] in
/-- **The Leray step of [Stacks, Tag 07JN] for a sheaf of modules, granted the surjectivity of
the level restrictions.**  This is `isAbelianCompletedLerayComparison_of_surjective` at
`G = abelianSheaf F`; the statement is unchanged, and the hypothesis `hF` is still hypothesis (2)
of [Stacks, Tag 07JN], discharged by nothing here. -/
theorem isCompletedLerayComparison_of_surjective
    (F : SheafOfModules.{u} (structureSheaf S))
    (hF : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp (abelianSheaf F).obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) :
    IsCompletedLerayComparison hp F :=
  isAbelianCompletedLerayComparison_of_surjective hp (abelianSheaf F) hF

/-- **[Stacks, Tag 07JN] for the source's system `(X, T(n)_e, δ(n))`, conditional on the
surjectivity of the level restrictions.**  For a locally quasi-coherent sheaf of modules `F` on
an affine situation whose affine-side sections have surjective level restrictions, the complex
`M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), F)` in the graded sense of
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology`.

**No tag attribute is placed, and this is not a proof of [Stacks, Tag 07JN].**  Two hypotheses
beyond those of the ambient situation are carried and neither is discharged here:

1. `hsurj`, the surjectivity of the level restrictions, which is hypothesis (2) of
   [Stacks, Tag 07JN] stated for the uniform level system of every object of `Cris^∧(C/A)`;
2. local quasi-coherence of `F`, which is a hypothesis of [Stacks, Tag 07JK] and of the source.

This docstring previously listed a third, `HasBinaryCoproducts (Cris^∧(C/A))`, inherited from the
Čech engine; the engine now asks only for the powers of its covering object, which
[Stacks, Tag 07L4] supplies, so it is gone — see the "What is and is not proved" note of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompletedCechDescent.lean`.

This is `...SmallSite.computesCohomology_wholeSpaceSystem_of_leray` with its Leray hypothesis
discharged by `isCompletedLerayComparison_of_surjective`. -/
theorem computesCohomology_wholeSpaceSystem_of_surjective
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hsurj : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp (abelianSheaf F).obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) :
    ComputesCohomology (wholeSpaceSystem S hp) (abelianSheaf F) :=
  computesCohomology_wholeSpaceSystem_of_leray hp F hF
    (isCompletedLerayComparison_of_surjective hp F hsurj)

/-- **The conclusion of [Stacks, Tag 07JN] for the source's system, for an arbitrary abelian
coefficient sheaf, conditional on the surjectivity of the level restrictions.**  For an abelian
sheaf `G` on `Cris(X/S)` which satisfies the conclusion `Vanishing07JJ` of [Stacks, Tag 07JJ] and
whose affine-side sections have surjective level restrictions, the complex
`M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), G)` in the graded sense of
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology`.

**No tag attribute is placed, and this is not a proof of [Stacks, Tag 07JN].**  Two hypotheses
beyond those of the ambient situation are carried and neither is discharged here: `hsurj`, which
is hypothesis (2) of [Stacks, Tag 07JN] stated for the uniform level system of every object of
`Cris^∧(C/A)`, and `hG`, which is the abelian form of hypothesis (1) — it is what the module
hypothesis `IsLocallyQuasiCoherent` of
`computesCohomology_wholeSpaceSystem_of_surjective` is used for, and nothing more.

This is `...SmallSite.computesCohomology_wholeSpaceSystem_of_abelianLeray` with its Leray
hypothesis discharged by `isAbelianCompletedLerayComparison_of_surjective`; the module-valued
statement `computesCohomology_wholeSpaceSystem_of_surjective` above is this one at
`G = abelianSheaf F`, up to that discharge. -/
theorem computesCohomology_wholeSpaceSystem_of_abelianSurjective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G)
    (hsurj : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp G.obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) :
    ComputesCohomology (wholeSpaceSystem S hp) G :=
  computesCohomology_wholeSpaceSystem_of_abelianLeray hp G hG
    (isAbelianCompletedLerayComparison_of_surjective hp G hsurj)

/-! ### The comparison of [Stacks, Tag 07JN], named and discharged

Every step from the Čech engine of [Stacks, Tag 07JM] to the conclusion of [Stacks, Tag 07JN] is
an explicit isomorphism with a name, and each of the four `Nonempty`-valued propositions along
the way now has a carried-family form beside it.  What follows composes those named families
once, so that the conclusion of [Stacks, Tag 07JN] holds *of a particular map* rather than being
an unanchored existence statement. -/

/-- **The Leray isomorphism of [Stacks, Tag 07JN] in degree `j`, named.**  This is the composite
that `isAbelianCompletedLerayComparison_of_surjective` builds and then discards into a
`Nonempty`: the identification of the two spellings of `g_*(G|_𝒞)`, followed by the Leray
degeneration `H ʲ(𝒞^∧, g_* 𝓖) ≅ H ʲ(𝒞, 𝓖)` of
`Crystalline.sheafHAddEquivPushforward_of_surjective`. -/
def abelianCompletedLerayComparisonEquivOfSurjective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp G.obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) (j : ℕ) :
    Sheaf.H.{u + 1, u + 1} (completedChaoticSheafOfPresheaf (affineSituation S hp)
        ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
          (affineSections S hp G.obj))) j ≃+
      Sheaf.H.{u + 1, u + 1} (littleChaoticSheafOfWhole hp ((restrictToWhole S).obj G)) j :=
  (((Sheaf.functorH (completedChaoticTopology.{u, u, u} (affineSituation S hp)) j).mapIso
      (completedChaoticSheafOfPresheafIsoPushforward hp G)).addCommGroupIsoToAddEquiv).trans
    (sheafHAddEquivPushforward_of_surjective (littleChaoticRestriction hp G) hG j)

/-- **The Leray step of [Stacks, Tag 07JN] as a named family of maps**, the underlying additive
maps of `abelianCompletedLerayComparisonEquivOfSurjective`. -/
def abelianCompletedLerayComparisonMapsOfSurjective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp G.obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) :
    IsAbelianCompletedLerayComparisonMaps hp G :=
  fun j => (abelianCompletedLerayComparisonEquivOfSurjective hp G hG j).toAddMonoidHom

omit [WholeSpacePresentation S hp] in
/-- **The named Leray comparison is bijective**, being the composite of two isomorphisms. -/
theorem abelianCompletedLerayComparisonVia_of_surjective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp G.obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) :
    IsAbelianCompletedLerayComparisonVia hp G
      (abelianCompletedLerayComparisonMapsOfSurjective hp G hG) :=
  fun j => (abelianCompletedLerayComparisonEquivOfSurjective hp G hG j).bijective

/-- **The comparison of the conclusion of [Stacks, Tag 07JN], as a map, with nothing assumed
beyond the tag's own hypotheses in abelian form.**  The composite of the four named families:
the Leray degeneration, the passage to the direct image, the passage to the coefficient presheaf
`B ↦ lim_e G(B/(p)^{N + e})`, and the Čech comparison of [Stacks, Tag 07JM].

Its target is `(cohomologyFunctor S j).obj G`, so it has the type of a
`...SmallSite.ComputesCohomologyMaps` for the system `(X, T(n)_e, δ(n))`, and
`isIso_computesCohomologyMapsWholeSpaceSystemOfAbelianSurjective` says it is an isomorphism in
every degree.  Together they *discharge* the existential of
`...SmallSite.computesCohomology_iff_exists_computesCohomologyVia` rather than assuming it. -/
noncomputable def computesCohomologyMapsWholeSpaceSystemOfAbelianSurjective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G)
    (hsurj : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp G.obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) G.obj).homology j ⟶
      (cohomologyFunctor S j).obj G :=
  computesCohomologyMapsWholeSpaceSystem S hp G
    (isCompletedSiteComparisonMapsOfDirectImage S hp G
      (isDirectImageCohomologyComparisonMapsOfAbelianLeray hp G hG
        (abelianCompletedLerayComparisonMapsOfSurjective hp G hsurj))) j

/-- **The named comparison of [Stacks, Tag 07JN] is an isomorphism in every degree.**  This is
the tag's conclusion stated of a *given* map: each of the four named families it is built from
is bijective, so the composite is.

`...SmallSite.computesCohomology_wholeSpaceSystem_of_abelianSurjective` says only that *some*
isomorphism exists in each degree, and an existence statement cannot be used against a given
map.  This can. -/
theorem isIso_computesCohomologyMapsWholeSpaceSystemOfAbelianSurjective
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hG : Vanishing07JJ S G)
    (hsurj : ∀ (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ),
      Function.Surjective (ConcreteCategory.hom
        ((affineSections S hp G.obj).map
          ((uniformLevelSystem B).transition (Nat.le_succ e))))) (j : ℕ) :
    IsIso (computesCohomologyMapsWholeSpaceSystemOfAbelianSurjective hp G hG hsurj j) :=
  isIso_computesCohomologyMapsWholeSpaceSystem S hp G
    (isCompletedSiteComparisonVia_of_directImage S hp G
      (isDirectImageCohomologyComparisonVia_of_abelianLeray hp G hG
        (abelianCompletedLerayComparisonVia_of_surjective hp G hsurj))) j

end Crystalline.GlobalCrystallineSituation.SmallSite

end
