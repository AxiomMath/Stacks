module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechCohomologyGlue

/-!
# The direct image of Stacks 07JL is the presheaf of level limits of Stacks 07JN

Work in an affine crystalline situation `(A, I, γ) → C` ([Stacks, Tag 07MD]).  The proof of
[Stacks, Tag 07JN] runs the Čech engine [Stacks, Tag 07JM] on the completed site
`𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` with coefficients in the presheaf

`levelLimitSections F : B ↦ lim_e F(B/(p)^{N + e})`

of `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechCohomologyGlue.lean`, and the source
identifies that presheaf with the direct image `g_* F` of the morphism of topoi of
[Stacks, Tag 07JL].  This file **proves that identification, as an isomorphism of functors**:

`g_* 𝓕 ≅ (B ↦ lim_e 𝓕(B/(p)^{N + e}))`.

Two things stood in the way, both named in the module docstring of `CechCohomologyGlue.lean`.
The first is that the two finite-level diagrams are *built* differently: the 07JL side runs over
a `Crystalline.FiniteLevelSystem`, whose cutoff is chosen out of
`DividedPowers.eventually_isDividedPowerCompletionLimit`, while `levelLimitSections` runs over
`Crystalline.levelFunctor` with the uniform cutoff `Crystalline.uniformLevel`.  This is settled by
`Crystalline.uniformLevelSystem`: the uniform levels *are* a finite-level system, and the diagram
it presents is the `levelFunctor` diagram on the nose.  The second is naturality in `B`: the 07JL
computation `Crystalline.abelianDirectImageObjObjIsoLimitFiniteLevelSections` is objectwise, and
an isomorphism of presheaves — which is what the cohomology of `𝒞^∧` consumes — needs it to be
natural.  That is settled by building the comparison as a single morphism of functors,
`Crystalline.directImageToLevelLimit`, out of the counit of the Kan extension and the level
projections, and then checking objectwise that it is the composite of the Kan extension's limit
description with the cofinality isomorphism.

## Main definitions

* `Crystalline.uniformLevelSystem` — the finite-level system of a completed thickening given by
  the uniform cutoff of `Crystalline.uniformLevel`.
* `Crystalline.levelLimitPresheaf` — the presheaf `B ↦ lim_e 𝓕(B/(p)^{N + e})` on `Cris^∧(C/A)`,
  for an abelian presheaf `𝓕` on `Cris(C/A)`; this is `levelLimitSections` with the global
  situation abstracted away.
* `Crystalline.directImageToLevelLimit` — the comparison morphism
  `(crystallineToCompleted s).ran.obj 𝓕 ⟶ levelLimitPresheaf s 𝓕`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.IsDirectImageCohomologyComparison` — the one
  step of [Stacks, Tag 07JN] that remains, stated about the direct image of [Stacks, Tag 07JL]
  itself rather than about `levelLimitSections`.

## Main results

* `Crystalline.finiteLevelSections_uniformLevelSystem` — the inverse system of sections on the
  uniform levels is the `levelFunctor` diagram composed with `𝓕`.
* `Crystalline.directImageIsoLevelLimit` — **`g_* 𝓕 ≅ lim_e 𝓕(B/(p)^{N + e})` as functors**, for
  the right Kan extension along `Crystalline.crystallineToCompleted`.
* `Crystalline.abelianDirectImageIsoLevelLimitPresheaf` — the same for
  `Crystalline.abelianDirectImage`, the direct image of [Stacks, Tag 07JL].
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelLimitSectionsIsoDirectImage` — the
  presheaf `levelLimitSections F` of [Stacks, Tag 07JN] is the direct image of
  [Stacks, Tag 07JL].
* `Crystalline.GlobalCrystallineSituation.SmallSite.isCompletedSiteComparison_of_directImage` —
  hence `IsCompletedSiteComparison`, the hypothesis under which `CechCohomologyGlue.lean`
  concludes [Stacks, Tag 07JN], follows from the comparison stated for the direct image.
* `...SmallSite.computesCohomology_wholeSpaceSystem_of_directImage` — **[Stacks, Tag 07JN] for
  the source's system, conditional on `IsDirectImageCohomologyComparison`.**

## What is and is not proved

**No tag attribute is placed.**  [Stacks, Tag 07JN] is
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` of
`SmallSite/WholeSpaceSystemCohomology.lean`.  What is proved here is the identification of the
coefficient presheaf of [Stacks, Tag 07JN] with the direct image of [Stacks, Tag 07JL], in full,
with no carried hypothesis beyond those of the ambient situation; and the resulting reduction of
[Stacks, Tag 07JN] to the single named proposition `IsDirectImageCohomologyComparison`, which
carries no hypothesis of its own either.

`IsDirectImageCohomologyComparison S hp F` says

`H^j(𝒞^∧, g_*(F|_𝒞)) ≅ H^j(Cris(X/S), F)` for every `j`,

for the direct image `g_*` of [Stacks, Tag 07JL].  It is **not proved**, and it is exactly the
source's two remaining moves, neither of which is in the library:

1. the Leray degeneration `H^j(𝒞, F|_𝒞) ≅ H^j(𝒞^∧, g_*(F|_𝒞))` along the vanishing
   `R^p g_*(F|_𝒞) = 0` for `p ≥ 1`.  Every hypothesis of
   `Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso` on the functor being derived is available
   (`Crystalline.abelianSheafPushforward_additive`,
   `Crystalline.preservesFiniteLimits_abelianSheafPushforward`,
   `Crystalline.preservesInjectiveObjects_abelianSheafPushforward`), and so is its comparison of
   global sections, `Crystalline.gammaCompAbelianSheafPushforwardIso`.  What is missing is the
   vanishing itself: `CompletedPushforwardVanishing.lean` proves the vanishing of `R^p lim_e` of
   the inverse system of level sections, and converting that into the vanishing of `R^p g_*`
   needs the *derived* half of [Stacks, Tag 07JL], `R^p g_* ≅ R^p lim_e`, which is not in the
   library.  The isomorphism proved here is its degree-zero half; it does not give the derived
   one, because the functor `𝓕 ↦ (e ↦ 𝓕(B/(p)^{N + e}))` is exact but is not known to carry
   injective abelian presheaves on `Cris(C/A)` to injective inverse systems.  A further missing
   ingredient for the Leray step is `CategoryTheory.EnoughInjectives` for the chaotic abelian
   sheaves on `(Cris(C/A))ᵒᵖ` and on `(Cris^∧(C/A))ᵒᵖ`, which the library has for the sites of
   the global situation but not for these; `CompletedCechDescent.lean` avoids needing it by
   running the Čech engine on the small model instead.
2. the transport of the cohomology of `𝒞` across the equivalence
   `Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine` of the subcategory `𝒞` of
   thickenings of the whole of `X` with the little affine crystalline category, and across the
   small model `Crystalline.CompletedSmallSite` of `𝒞^∧`, together with [Stacks, Tag 07JK]
   (`Crystalline.GlobalCrystallineSituation.SmallSite.chaoticCohomologyComparisonIso`).

Nothing below carries a hypothesis beyond those of the ambient affine or global situation.  In
particular `computesCohomology_wholeSpaceSystem_of_directImage` does not need
`HasBinaryCoproducts (Cris^∧(C/A))`: the Čech engine asks only for the powers of its covering
object, which [Stacks, Tag 07L4] supplies; see the "What is and is not proved" note of
`CompletedCechDescent.lean`.

The smallness question that the module docstring of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean` leaves open in its
item 3 is **not** open: it is answered in the module docstring of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompletedCechDescent.lean`, and the answer
is that the sizes on the affine side do *not* coincide — an object of `Cris^∧(C/A)` bundles its own
carrier, so the objects form a `Type (max u v (t + 1))` while the morphisms form a `Type t` — but
that this does not matter, because `CategoryTheory.SmallCategory` asks only that objects and
morphisms share a universe and `CategoryTheory.AsSmall` always arranges that.  The engine
[Stacks, Tag 07JM] is already run on the resulting model, in
`Crystalline.nonempty_addEquiv_sheafH_homology_powerCechComplex_generator`.

## Implementation notes

The comparison is built for `Crystalline.crystallineToCompleted`, the inclusion
`Cris(C/A) ⥤ Cris^∧(C/A)` written out, so that the level projections are morphisms into its
image on the nose, with no `eqToHom` in the way.

`Crystalline.ranCounitApp`, `Crystalline.levelProjection` and `Crystalline.levelLimitPre` are the
counit of the Kan extension, the projection onto a finite level, and
`CategoryTheory.Limits.limit.pre` along the finite-level diagram, each restated with its domain
and codomain spelled as values of the functors actually in play.  The restatements are
definitional, and they are what keeps the composites in the proofs below type-correct without
unfolding `CategoryTheory.Functor.comp`, which the tactic framework will not do.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

noncomputable section

namespace Crystalline

/-! ### The uniform levels as a finite-level system -/

section UniformLevelSystem

variable {s : AffineCrystallineSituation.{u, v}}

/-- **The finite-level system of a completed crystalline thickening given by the uniform
cutoff.**  Its `e`-th term is `B/(p)^{N + e}` for `N = Crystalline.uniformLevel s`, a cutoff that
is a `p`-adic level for every object of `Cris^∧(C/A)` at once, and its transition maps are those
of `Crystalline.levelFunctor`.

This is what matches the finite-level diagram of [Stacks, Tag 07JL] with the diagram over which
`Crystalline.levelLimitPresheaf` takes its limit; see the module docstring. -/
def uniformLevelSystem (B : CompletedCrystallineThickening.{u, v, w} s) : FiniteLevelSystem B where
  cutoff := uniformLevel s
  term e := levelThickening B (uniformLevel s + e) (isPAdicLevel_uniformLevel_add B e)
  projection e := levelProj s.p B.ring (uniformLevel s + e) (isPAdicLevel_uniformLevel_add B e)
  projection_surjective _ := Ideal.Quotient.mk_surjective
  projection_ker _ := Ideal.mk_ker
  projection_fromBase _ := rfl
  projection_toQuotient _ := rfl
  transition h := levelThickeningMap _ _ (𝟙 B) (Nat.add_le_add_left h _)
  transition_projection _ := by ext a; rfl
  transition_id e := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  transition_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  limit_bijective := AdicCompletion.of_bijective_iff.mpr B.isComplete

/-- **The diagram of uniform finite levels of a completed thickening**, `e ↦ B/(p)^{N + e}`, as a
functor `ℕᵒᵖ ⥤ Cris(C/A)`: the finite-level functor `Crystalline.levelFunctor` with the
thickening fixed. -/
abbrev levelDiagram (B : CompletedCrystallineThickening.{u, v, w} s) :
    ℕᵒᵖ ⥤ CrystallineThickening.{u, v, w} s :=
  (Functor.curryObj (levelFunctor s)).obj B

/-- **The diagram presented by the uniform finite-level system is the `levelFunctor` diagram.**
Both have `B/(p)^{N + e}` in degree `e` and the level drops as transition maps; the identification
is definitional. -/
theorem diagram_uniformLevelSystem (B : CompletedCrystallineThickening.{u, v, w} s) :
    (uniformLevelSystem B).diagram = levelDiagram B :=
  rfl

/-- **The inverse system of sections of [Stacks, Tag 07JL] on the uniform levels is the system of
sections of `𝓕` on the diagram of uniform levels.**  This is the identification of the two
finite-level diagrams; it holds definitionally. -/
theorem finiteLevelSections_uniformLevelSystem
    (B : CompletedCrystallineThickening.{u, v, w} s)
    (𝓕 : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :
    finiteLevelSections (uniformLevelSystem B) 𝓕 = levelDiagram B ⋙ 𝓕 :=
  rfl

/-- **The projection of a completed thickening onto one of its uniform finite levels**,
`B ⟶ B/(p)^{N + e}`, as a morphism of `Cris^∧(C/A)`.  It is
`Crystalline.finiteLevelProjection` of `Crystalline.uniformLevelSystem`, written with the level
spelled by `Crystalline.levelDiagram`. -/
def levelProjection (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕᵒᵖ) :
    B ⟶ (crystallineToCompleted s).obj ((levelDiagram B).obj e) where
  hom := levelProj s.p B.ring (uniformLevel s + e.unop)
    (isPAdicLevel_uniformLevel_add B e.unop)
  fromBase_comp := rfl
  toQuotient_comp := rfl

/-- `Crystalline.levelProjection` is the projection of the uniform finite-level system. -/
theorem levelProjection_eq (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕᵒᵖ) :
    levelProjection B e = finiteLevelProjection (uniformLevelSystem B) e.unop :=
  rfl

/-- **The level projections are compatible with the level drops.** -/
theorem levelProjection_comp_map (B : CompletedCrystallineThickening.{u, v, w} s)
    {e e' : ℕᵒᵖ} (f : e ⟶ e') :
    levelProjection B e ≫ (crystallineToCompleted s).map ((levelDiagram B).map f) =
      levelProjection B e' := by
  apply CompletedCrystallineThickening.Hom.ext
  ext a
  rfl

/-- **The level projections are natural in the thickening**: projecting `B` onto its level
`N + e` and then pushing forward along `φ : B ⟶ B'` is `φ` followed by the projection of `B'`.
This is `Crystalline.levelProj_comp_levelHom` read in `Cris^∧(C/A)`, and it is what makes the
comparison morphism of this file natural. -/
theorem levelProjection_naturality {B B' : CompletedCrystallineThickening.{u, v, w} s}
    (φ : B ⟶ B') (e : ℕᵒᵖ) :
    levelProjection B e ≫
        (crystallineToCompleted s).map (((Functor.curryObj (levelFunctor s)).map φ).app e) =
      φ ≫ levelProjection B' e := by
  apply CompletedCrystallineThickening.Hom.ext
  ext a
  rfl

end UniformLevelSystem

/-! ### The presheaf of level limits -/

section LevelLimit

/-- **The presheaf `B ↦ lim_e 𝓕(B/(p)^{N + e})` on `Cris^∧(C/A)`** attached to an abelian
presheaf `𝓕` on `Cris(C/A)`: the sections of `𝓕` on the uniform finite levels of a completed
thickening, taken to the limit.

This is `Crystalline.GlobalCrystallineSituation.SmallSite.levelLimitSections` with the global
crystalline situation abstracted away; the two agree definitionally, by
`Crystalline.GlobalCrystallineSituation.SmallSite.levelLimitSections_eq`. -/
def levelLimitPresheaf (s : AffineCrystallineSituation.{u, v})
    (𝓕 : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}) :
    CompletedCrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)} :=
  Functor.curryObj (levelFunctor s) ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj 𝓕 ⋙ lim

variable {s : AffineCrystallineSituation.{u, v}}
  (𝓕 : CrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)})

/-- The sections of the level-limit presheaf over a completed thickening are the limit of the
sections of `𝓕` over its uniform finite levels. -/
theorem levelLimitPresheaf_obj (B : CompletedCrystallineThickening.{u, v, w} s) :
    (levelLimitPresheaf s 𝓕).obj B = limit (levelDiagram B ⋙ 𝓕) :=
  rfl

/-- **The counit of the right Kan extension along the concrete inclusion**, with its domain
written out as a value of the Kan extension rather than as a value of a composite of functors.
This spelling is what keeps the composites below type-correct without unfolding
`CategoryTheory.Functor.comp`. -/
def ranCounitApp (Y : CrystallineThickening.{u, v, w} s) :
    ((crystallineToCompleted s).ran.obj 𝓕).obj ((crystallineToCompleted s).obj Y) ⟶ 𝓕.obj Y :=
  ((crystallineToCompleted s).ranCounit.app 𝓕).app Y

/-- **The counit of the Kan extension is natural.** -/
theorem ranCounitApp_naturality {Y Y' : CrystallineThickening.{u, v, w} s} (g : Y ⟶ Y') :
    ((crystallineToCompleted s).ran.obj 𝓕).map ((crystallineToCompleted s).map g) ≫
        ranCounitApp 𝓕 Y' =
      ranCounitApp 𝓕 Y ≫ 𝓕.map g :=
  ((crystallineToCompleted s).ranCounit.app 𝓕).naturality g

/-- **The leg of the cone of level sections at a level `e`**: project `B` onto its level `N + e`,
push the right Kan extension along that projection, then evaluate the counit of the Kan
extension.  This is the comparison `g_* 𝓕 (B) ⟶ 𝓕(B/(p)^{N + e})` of [Stacks, Tag 07JL]. -/
def levelLimitLeg (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕᵒᵖ) :
    ((crystallineToCompleted s).ran.obj 𝓕).obj B ⟶ (levelDiagram B ⋙ 𝓕).obj e :=
  ((crystallineToCompleted s).ran.obj 𝓕).map (levelProjection B e) ≫
    ranCounitApp 𝓕 ((levelDiagram B).obj e)

/-- The Kan extension of `𝓕` applied to `u ≫ g`, for `g` a morphism of `Cris(C/A)`, followed by the
counit is the same composite for `u`, followed by `𝓕.map g`. -/
private theorem ran_map_comp_ranCounitApp {B : CompletedCrystallineThickening.{u, v, w} s}
    {Y Y' : CrystallineThickening.{u, v, w} s} (u : B ⟶ (crystallineToCompleted s).obj Y)
    (g : Y ⟶ Y') :
    ((crystallineToCompleted s).ran.obj 𝓕).map (u ≫ (crystallineToCompleted s).map g) ≫
        ranCounitApp 𝓕 Y' =
      (((crystallineToCompleted s).ran.obj 𝓕).map u ≫ ranCounitApp 𝓕 Y) ≫ 𝓕.map g := by
  rw [Functor.map_comp, Category.assoc, ranCounitApp_naturality, Category.assoc]

/-- **The legs of `Crystalline.levelLimitLeg` are compatible with the level drops**, so that they
form a cone over the diagram of level sections.  This is naturality of the counit of the Kan
extension together with `Crystalline.levelProjection_comp_map`. -/
theorem levelLimitLeg_comp_map (B : CompletedCrystallineThickening.{u, v, w} s) {e e' : ℕᵒᵖ}
    (f : e ⟶ e') :
    levelLimitLeg 𝓕 B e ≫ (levelDiagram B ⋙ 𝓕).map f = levelLimitLeg 𝓕 B e' := by
  have h := ran_map_comp_ranCounitApp 𝓕 (levelProjection B e) ((levelDiagram B).map f)
  rw [levelProjection_comp_map] at h
  exact h.symm

/-- The cone over the diagram of level sections of `𝓕` whose apex is the value at `B` of the
right Kan extension of `𝓕` along the concrete inclusion, with legs
`Crystalline.levelLimitLeg`. -/
def levelLimitCone (B : CompletedCrystallineThickening.{u, v, w} s) :
    Cone (levelDiagram B ⋙ 𝓕) where
  pt := ((crystallineToCompleted s).ran.obj 𝓕).obj B
  π :=
    { app := levelLimitLeg 𝓕 B
      naturality := fun _ _ f =>
        (Category.id_comp _).trans (levelLimitLeg_comp_map 𝓕 B f).symm }

/-- The leg of `Crystalline.levelLimitCone` at a level `e` is `Crystalline.levelLimitLeg`. -/
@[simp]
lemma levelLimitCone_π_app (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕᵒᵖ) :
    (levelLimitCone 𝓕 B).π.app e = levelLimitLeg 𝓕 B e :=
  rfl

/-- **The legs of `Crystalline.levelLimitLeg` are natural in the completed thickening.**  This is
naturality of the counit of the Kan extension together with
`Crystalline.levelProjection_naturality`, and it is what makes the comparison morphism of this
file a morphism of presheaves. -/
theorem levelLimitLeg_naturality {B B' : CompletedCrystallineThickening.{u, v, w} s}
    (φ : B ⟶ B') (e : ℕᵒᵖ) :
    ((crystallineToCompleted s).ran.obj 𝓕).map φ ≫ levelLimitLeg 𝓕 B' e =
      levelLimitLeg 𝓕 B e ≫
        (Functor.whiskerRight ((Functor.curryObj (levelFunctor s)).map φ) 𝓕).app e := by
  have h := ran_map_comp_ranCounitApp 𝓕 (levelProjection B e)
    (((Functor.curryObj (levelFunctor s)).map φ).app e)
  rw [levelProjection_naturality, Functor.map_comp, Category.assoc] at h
  exact h

/-- The level-`e` projection out of the level-limit presheaf is natural in the completed
thickening. -/
theorem limMap_whiskerRight_comp_π {B B' : CompletedCrystallineThickening.{u, v, w} s}
    (φ : B ⟶ B') (e : ℕᵒᵖ) :
    limMap (Functor.whiskerRight ((Functor.curryObj (levelFunctor s)).map φ) 𝓕) ≫
        limit.π (levelDiagram B' ⋙ 𝓕) e =
      limit.π (levelDiagram B ⋙ 𝓕) e ≫
        (Functor.whiskerRight ((Functor.curryObj (levelFunctor s)).map φ) 𝓕).app e :=
  limMap_π _ _

/-- **The value at a completed thickening of the comparison morphism
`g_* 𝓕 ⟶ lim_e 𝓕(B/(p)^{N + e})`**: the map into the limit given by the cone
`Crystalline.levelLimitCone`. -/
def directImageToLevelLimitApp (B : CompletedCrystallineThickening.{u, v, w} s) :
    ((crystallineToCompleted s).ran.obj 𝓕).obj B ⟶ limit (levelDiagram B ⋙ 𝓕) :=
  limit.lift _ (levelLimitCone 𝓕 B)

/-- The comparison morphism followed by the projection onto a level is the cone leg of that
level. -/
theorem directImageToLevelLimitApp_comp_π (B : CompletedCrystallineThickening.{u, v, w} s)
    (e : ℕᵒᵖ) :
    directImageToLevelLimitApp 𝓕 B ≫ limit.π (levelDiagram B ⋙ 𝓕) e = levelLimitLeg 𝓕 B e :=
  limit.lift_π _ _

/-- **The comparison morphism `g_* 𝓕 ⟶ lim_e 𝓕(B/(p)^{N + e})`**, as a morphism of presheaves on
`Cris^∧(C/A)`. -/
def directImageToLevelLimit : (crystallineToCompleted s).ran.obj 𝓕 ⟶ levelLimitPresheaf s 𝓕 where
  app B := directImageToLevelLimitApp 𝓕 B
  naturality B B' φ := by
    change ((crystallineToCompleted s).ran.obj 𝓕).map φ ≫ directImageToLevelLimitApp 𝓕 B' =
      directImageToLevelLimitApp 𝓕 B ≫
        limMap (Functor.whiskerRight ((Functor.curryObj (levelFunctor s)).map φ) 𝓕)
    apply limit.hom_ext
    intro e
    rw [Category.assoc, directImageToLevelLimitApp_comp_π, Category.assoc,
      limMap_whiskerRight_comp_π, ← Category.assoc, directImageToLevelLimitApp_comp_π,
      levelLimitLeg_naturality]

/-- **The comparison of the limit over the structured-arrow category with the limit over the
finite levels**, `CategoryTheory.Limits.limit.pre` along the finite-level diagram of the uniform
level system.  It is an isomorphism, by `Crystalline.isIso_levelLimitPre`. -/
def levelLimitPre (B : CompletedCrystallineThickening.{u, v, w} s) :
    limit (StructuredArrow.proj B (crystallineToCompleted s) ⋙ 𝓕) ⟶ limit (levelDiagram B ⋙ 𝓕) :=
  limit.pre (StructuredArrow.proj B (crystallineToCompleted s) ⋙ 𝓕)
    (finiteLevelStructuredArrow (uniformLevelSystem B))

/-- The comparison `Crystalline.levelLimitPre` followed by the projection onto a level is the
projection of the limit over the structured-arrow category at the corresponding arrow. -/
theorem levelLimitPre_comp_π (B : CompletedCrystallineThickening.{u, v, w} s) (e : ℕᵒᵖ) :
    levelLimitPre 𝓕 B ≫ limit.π (levelDiagram B ⋙ 𝓕) e =
      limit.π (StructuredArrow.proj B (crystallineToCompleted s) ⋙ 𝓕)
        ((finiteLevelStructuredArrow (uniformLevelSystem B)).obj e) :=
  limit.pre_π _ _ _

/-- **The finite-level comparison is an isomorphism**, because the finite-level diagram is
initial in the structured-arrow category, by `Crystalline.finiteLevel_initial`. -/
theorem isIso_levelLimitPre (B : CompletedCrystallineThickening.{u, v, w} s) :
    IsIso (levelLimitPre 𝓕 B) :=
  have := finiteLevel_initial (uniformLevelSystem B)
  inferInstanceAs (IsIso (limit.pre (StructuredArrow.proj B (crystallineToCompleted s) ⋙ 𝓕)
    (finiteLevelStructuredArrow (uniformLevelSystem B))))

/-- **The comparison morphism is the Kan extension's limit description followed by the
finite-level comparison.**  This is what makes it an isomorphism. -/
theorem directImageToLevelLimitApp_eq (B : CompletedCrystallineThickening.{u, v, w} s) :
    directImageToLevelLimitApp 𝓕 B =
      ((crystallineToCompleted s).ranObjObjIsoLimit 𝓕 B).hom ≫ levelLimitPre 𝓕 B := by
  refine limit.hom_ext fun e => ?_
  rw [directImageToLevelLimitApp_comp_π, Category.assoc, levelLimitPre_comp_π]
  symm
  exact Functor.ranObjObjIsoLimit_hom_π _ _ _ _

/-- **`g_* 𝓕 ≅ lim_e 𝓕(B/(p)^{N + e})`**: the right Kan extension of an abelian presheaf `𝓕` on
`Cris(C/A)` along the inclusion into `Cris^∧(C/A)` is the presheaf of limits over the uniform
finite levels, **as an isomorphism of presheaves**.

This is the computation half of [Stacks, Tag 07JL] made natural.  Objectwise it is
`Crystalline.abelianDirectImageObjObjIsoLimitFiniteLevelSections` for the uniform level system:
the value of the Kan extension at `B` is the limit over the structured-arrow category
(`CategoryTheory.Functor.ranObjObjIsoLimit`), the finite-level diagram is initial there
(`Crystalline.finiteLevel_initial`), and `CategoryTheory.Limits.limit.pre` along an initial
functor is invertible. -/
def directImageIsoLevelLimitApp (B : CompletedCrystallineThickening.{u, v, w} s) :
    ((crystallineToCompleted s).ran.obj 𝓕).obj B ≅ limit (levelDiagram B ⋙ 𝓕) :=
  haveI := isIso_levelLimitPre 𝓕 B
  (crystallineToCompleted s).ranObjObjIsoLimit 𝓕 B ≪≫ asIso (levelLimitPre 𝓕 B)

/-- The isomorphism `Crystalline.directImageIsoLevelLimitApp` is the comparison morphism. -/
theorem directImageIsoLevelLimitApp_hom (B : CompletedCrystallineThickening.{u, v, w} s) :
    (directImageIsoLevelLimitApp 𝓕 B).hom = directImageToLevelLimitApp 𝓕 B :=
  (directImageToLevelLimitApp_eq 𝓕 B).symm

/-- **`g_* 𝓕 ≅ lim_e 𝓕(B/(p)^{N + e})` as presheaves.** -/
def directImageIsoLevelLimit : (crystallineToCompleted s).ran.obj 𝓕 ≅ levelLimitPresheaf s 𝓕 :=
  NatIso.ofComponents (directImageIsoLevelLimitApp 𝓕) (fun φ => by
    rw [directImageIsoLevelLimitApp_hom, directImageIsoLevelLimitApp_hom]
    exact (directImageToLevelLimit 𝓕).naturality φ)

/-- **The direct image of [Stacks, Tag 07JL] is the presheaf of level limits**,

`g_* 𝓕 ≅ (B ↦ lim_e 𝓕(B/(p)^{N + e}))`,

as an isomorphism of abelian presheaves on `Cris^∧(C/A)`.  This is
`Crystalline.directImageIsoLevelLimit`, read for `Crystalline.abelianDirectImage`, which is by
definition the right Kan extension along `Crystalline.crystallineToCompleted`. -/
def abelianDirectImageIsoLevelLimitPresheaf :
    (abelianDirectImage.{u, v, w} s).obj 𝓕 ≅ levelLimitPresheaf s 𝓕 :=
  directImageIsoLevelLimit 𝓕

end LevelLimit

/-! ### Transporting a presheaf isomorphism to the small model of the completed site -/

section SmallSheaf

variable {s : AffineCrystallineSituation.{u, v}}
  {𝓖 𝓖' : CompletedCrystallineThickening.{u, v, w} s ⥤ Ab.{max u v (w + 1)}}

/-- An isomorphism of abelian presheaves on `Cris^∧(C/A)`, read as an isomorphism of the abelian
sheaves they define on the small model of `𝒞^∧`. -/
def smallSheafOfPresheafMapIso (i : 𝓖 ≅ 𝓖') :
    smallSheafOfPresheaf.{u, v, w} s 𝓖 ≅ smallSheafOfPresheaf.{u, v, w} s 𝓖' :=
  (fullyFaithfulSheafToPresheaf (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, w} s))
      Ab.{max u v (w + 1)}).preimageIso
    (Functor.isoWhiskerLeft (completedSmallSiteOpEquiv s).functor i)

/-- **The cohomology of the small model of `𝒞^∧` depends on the coefficient presheaf only up to
isomorphism.**  An isomorphism of abelian presheaves on `Cris^∧(C/A)` induces an additive
equivalence of the cohomology groups that [Stacks, Tag 07JM] computes. -/
def sheafHAddEquivOfPresheafIso (i : 𝓖 ≅ 𝓖') (j : ℕ) :
    Sheaf.H (smallSheafOfPresheaf.{u, v, w} s 𝓖) j ≃+
      Sheaf.H (smallSheafOfPresheaf.{u, v, w} s 𝓖') j :=
  ((Sheaf.functorH (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, w} s)) j).mapIso
    (smallSheafOfPresheafMapIso i)).addCommGroupIsoToAddEquiv

end SmallSheaf

end Crystalline

/-! ### The reduction of Stacks 07JN to a statement about the direct image -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable (S : GlobalCrystallineSituation.{u}) (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

omit [WholeSpacePresentation S hp] in
/-- **The coefficient presheaf of [Stacks, Tag 07JN] is the level-limit presheaf.**  The presheaf
`levelLimitSections F` of `CechCohomologyGlue.lean` is `Crystalline.levelLimitPresheaf` applied to
the affine-side sections of `F`; the two definitions agree on the nose. -/
theorem levelLimitSections_eq (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    levelLimitSections S hp F =
      levelLimitPresheaf (affineSituation S hp) (affineSections S hp F) :=
  rfl

/-- **The coefficient presheaf of [Stacks, Tag 07JN] is the direct image of
[Stacks, Tag 07JL].**  This is the identification the source makes and which
`CechCohomologyGlue.lean` recorded as owed: the presheaf `B ↦ lim_e F(B/(p)^{N + e})` on
`Cris^∧(C/A)`, whose values on the objects `D(n)` are the terms `M(n)` of [Stacks, Tag 07JN], is
the direct image `g_*(F|_𝒞)` of the morphism of topoi of [Stacks, Tag 07JL]. -/
def levelLimitSectionsIsoDirectImage (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    levelLimitSections S hp F ≅
      (abelianDirectImage.{u, u, u} (affineSituation S hp)).obj (affineSections S hp F) :=
  (abelianDirectImageIsoLevelLimitPresheaf (affineSections S hp F)).symm

/-- **The one step of [Stacks, Tag 07JN] that remains**, stated about the direct image of
[Stacks, Tag 07JL] itself: the cohomology of the completed site `𝒞^∧` with coefficients in
`g_*(F|_𝒞)` is the cohomology of `Cris(X/S)` with coefficients in `F`.

This replaces `Crystalline.GlobalCrystallineSituation.SmallSite.IsCompletedSiteComparison`, which
says the same thing about the ad hoc presheaf `levelLimitSections F`; the two are equivalent, by
`levelLimitSectionsIsoDirectImage`, and this one is what the source actually proves, by
[Stacks, Tag 07JK] and the Leray degeneration along `R^p g_* = 0`.  Neither move is in the
library; see the module docstring.  **This is a proposition, not a theorem**, and no tag
attribute is placed on it. -/
def IsDirectImageCohomologyComparison (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ j : ℕ, Nonempty (Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
    ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
      (affineSections S hp F.obj))) j ≃+ cohomology S F j)

omit [WholeSpacePresentation S hp] in
/-- **`IsCompletedSiteComparison` follows from the comparison stated for the direct image.**  The
coefficient presheaf of [Stacks, Tag 07JN] is the direct image of [Stacks, Tag 07JL], by
`levelLimitSectionsIsoDirectImage`, and the cohomology of the completed site depends on the
coefficient presheaf only up to isomorphism. -/
theorem isCompletedSiteComparison_of_directImage
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : IsDirectImageCohomologyComparison S hp F) :
    IsCompletedSiteComparison S hp F := fun j => by
  obtain ⟨e⟩ := h j
  exact ⟨(sheafHAddEquivOfPresheafIso (levelLimitSectionsIsoDirectImage S hp F.obj) j).trans e⟩

/-- **[Stacks, Tag 07JN] for the source's system `(X, T(n)_e, δ(n))`, conditional on
`IsDirectImageCohomologyComparison`.**  Granted that the cohomology of the completed site with
coefficients in the direct image of [Stacks, Tag 07JL] is the cohomology of `Cris(X/S)`, the
complex `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), F)` in the graded sense of
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology`.

This is `Crystalline.GlobalCrystallineSituation.SmallSite.computesCohomology_wholeSpaceSystem`
with its hypothesis replaced by the more faithful one, the two being equivalent.  **No tag
attribute is placed**: the hypothesis is a step of the source's proof, not a hypothesis of
[Stacks, Tag 07JN], and the tag means statement *and* proof.  This docstring previously also
recorded `HasBinaryCoproducts (Cris^∧(C/A))`, inherited from the Čech engine; the engine now asks
only for the powers of its covering object, which [Stacks, Tag 07L4] supplies, so the statement
carries no hypothesis about coproducts. -/
theorem computesCohomology_wholeSpaceSystem_of_directImage
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : IsDirectImageCohomologyComparison S hp F) :
    ComputesCohomology (wholeSpaceSystem S hp) F :=
  computesCohomology_wholeSpaceSystem S hp F
    (isCompletedSiteComparison_of_directImage S hp F h)

/-! ### The remaining step, with its comparison map named -/

/-- **The type of a named comparison for the remaining step of [Stacks, Tag 07JN]**: a family of
additive maps

`H^j(𝒞^∧, g_*(F|_𝒞)) →+ H^j(Cris(X/S), F)`,

one in each degree.  `IsDirectImageCohomologyComparison` asserts the two groups to be isomorphic
and names no map. -/
abbrev IsDirectImageCohomologyComparisonMaps
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ∀ j : ℕ, Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
    ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
      (affineSections S hp F.obj))) j →+ cohomology S F j

/-- **The remaining step of [Stacks, Tag 07JN] *via* a named comparison**: the carried family
`c` is bijective in every degree.  Equivalent, as a statement about `F`, to
`IsDirectImageCohomologyComparison`, by
`isDirectImageCohomologyComparison_iff_exists_via`. -/
def IsDirectImageCohomologyComparisonVia
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (c : IsDirectImageCohomologyComparisonMaps S hp F) : Prop :=
  ∀ j : ℕ, Function.Bijective (c j)

/-- The isomorphism of degree `j` named by a bijective comparison family. -/
noncomputable def IsDirectImageCohomologyComparisonVia.equiv
    {S : GlobalCrystallineSituation.{u}} {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}
    [IsAffine S.X] [IsAffine S.S.scheme] {F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    {c : IsDirectImageCohomologyComparisonMaps S hp F}
    (hc : IsDirectImageCohomologyComparisonVia S hp F c) (j : ℕ) :
    Sheaf.H (smallSheafOfPresheaf (affineSituation S hp)
      ((abelianDirectImage.{u, u, u} (affineSituation S hp)).obj
        (affineSections S hp F.obj))) j ≃+ cohomology S F j :=
  AddEquiv.ofBijective (c j) (hc j)

omit [WholeSpacePresentation S hp] in
/-- **A named bijective comparison gives the remaining step of [Stacks, Tag 07JN].** -/
theorem isDirectImageCohomologyComparison_of_via
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    {c : IsDirectImageCohomologyComparisonMaps S hp F}
    (hc : IsDirectImageCohomologyComparisonVia S hp F c) :
    IsDirectImageCohomologyComparison S hp F :=
  fun j => ⟨hc.equiv j⟩

omit [WholeSpacePresentation S hp] in
/-- **The remaining step of [Stacks, Tag 07JN] is exactly the existence of a named bijective
comparison**, so the named shape neither weakens nor strengthens it. -/
theorem isDirectImageCohomologyComparison_iff_exists_via
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    IsDirectImageCohomologyComparison S hp F ↔
      ∃ c : IsDirectImageCohomologyComparisonMaps S hp F,
        IsDirectImageCohomologyComparisonVia S hp F c :=
  ⟨fun h => ⟨fun j => (h j).some.toAddMonoidHom, fun j => (h j).some.bijective⟩,
    fun ⟨_, hc⟩ => isDirectImageCohomologyComparison_of_via S hp F hc⟩

/-- **A named comparison for the direct image is a named comparison for the ad hoc presheaf.**
The coefficient presheaf of [Stacks, Tag 07JN] is the direct image of [Stacks, Tag 07JL]
(`levelLimitSectionsIsoDirectImage`), so transporting along that isomorphism carries the one
named family to the other.  This is `isCompletedSiteComparison_of_directImage` with the maps
kept. -/
def isCompletedSiteComparisonMapsOfDirectImage
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (c : IsDirectImageCohomologyComparisonMaps S hp F) :
    IsCompletedSiteComparisonMaps S hp F :=
  fun j => (c j).comp
    (sheafHAddEquivOfPresheafIso (levelLimitSectionsIsoDirectImage S hp F.obj) j).toAddMonoidHom

omit [WholeSpacePresentation S hp] in
/-- **The transport preserves bijectivity**, since it composes with an isomorphism. -/
theorem isCompletedSiteComparisonVia_of_directImage
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    {c : IsDirectImageCohomologyComparisonMaps S hp F}
    (hc : IsDirectImageCohomologyComparisonVia S hp F c) :
    IsCompletedSiteComparisonVia S hp F
      (isCompletedSiteComparisonMapsOfDirectImage S hp F c) :=
  fun j => (hc j).comp
    (sheafHAddEquivOfPresheafIso (levelLimitSectionsIsoDirectImage S hp F.obj) j).bijective

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
