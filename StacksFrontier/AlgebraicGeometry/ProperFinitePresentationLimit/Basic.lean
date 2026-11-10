module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.IdealSheafFiniteType.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# A proper morphism as a limit of proper morphisms of finite presentation

Let `f : X ⟶ S` be a proper morphism onto a quasi-compact and quasi-separated scheme. Limits,
Tag 09ZR writes `X` as the limit of a cofiltered inverse system of schemes proper and of finite
presentation over `S`, in which every transition morphism and every projection `X ⟶ X_i` is a
closed immersion.

This file reduces that statement to its **single-stage** form: the existence of one closed
immersion `X ⟶ X'` with `X' ⟶ S` proper and of finite presentation. Given such an `X'`, the
system asked for is already available — it is the inverse system of the finite-presentation
closed subschemes of `X'` containing `X`, which Limits, Tag 09ZP exhibits as having limit `X`.
Each of its stages is a closed subscheme of `X'`, hence proper over `S` because a closed
immersion is finite and therefore proper, and of finite presentation over `S` because both
`X_i ⟶ X'` and `X' ⟶ S` are.

So the whole residue of the limit form is the single-stage form, which is the hypothesis
`h09ZR` of
`AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt_of_exists_factorisation`
and is where the source spends its work: a closed immersion into something separated and of
finite presentation over `S` (Tag 01ZJ), then Chow's lemma over a quasi-compact quasi-separated
base (Tag 0202) to upgrade a stage to properness.

Over a locally Noetherian base the single-stage form is the degenerate one — a proper morphism
onto a locally Noetherian scheme is already of finite presentation — so the limit form is
unconditional there, and that is what makes the reduction non-vacuous.

## Main definitions

* `AlgebraicGeometry.properStageDiagram`: the inverse system of `X`'s finite-presentation closed
  enlargements inside a model `X'`, as a diagram of schemes.
* `AlgebraicGeometry.properStageStructure`: its structure morphisms to `S`.
* `AlgebraicGeometry.properStageCone`: the projections from `X` to its stages.

## Main results

* `AlgebraicGeometry.exists_isProper_finitePresentation_isLimit_of_exists_model`: Limits,
  Tag 09ZR from its single-stage form.
* `AlgebraicGeometry.exists_isProper_finitePresentation_isLimit_of_isLocallyNoetherian`: the
  locally Noetherian case, unconditionally.

## Implementation notes

The limit is stated in the category of schemes, as a cone on `D : I ⥤ Scheme` together with a
natural transformation `t : D ⟶ (Functor.const I).obj S` recording the structure morphisms and
the identity `π ≫ t = (Functor.const I).map f` recording that the cone is a cone over `S`. The
source's limit is taken in schemes over `S`; the two agree because the index category is
cofiltered, hence connected, and `CategoryTheory.Over.forget` preserves cofiltered limits
(`CategoryTheory.Limits.instPreservesCofilteredLimitsOfSizeOverForget`) while a cone over `S`
whose underlying cone of schemes is a limit lifts uniquely, the index being nonempty. This is
also the shape in which the neighbouring eventual statements take their systems — compare
`AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit_of_initiallySmall`, Tag 0A0N.

The index category is `(Stacks.Flatness.FinitePresentationSubscheme ι.ker)ᵒᵖ` for the chosen
closed immersion `ι : X ⟶ X'`, which is a preorder on a subtype of `X'.IdealSheafData` and so a
small category in the scheme universe. No smallness hypothesis is needed, for the reason
recorded in
`StacksFrontier/AlgebraicGeometry/Limits/ClosedImmersionFinitePresentationLimit.lean`:
exhibiting a cone as limiting costs nothing, while an *eventual* statement about a limit needs a
cofinality bound.

`AlgebraicGeometry.properStageDiagram` and `AlgebraicGeometry.properStageCone` are `abbrev`
rather than `def`: as `def`s the instance `IsProper` of a stage's structure morphism and the
reassociation in the compatibility identity both failed, the goal reported as "not type-correct
under the `implicit` transparency level".

**No Stacks attribute is attached to either result.** The first carries the
single-stage form as a hypothesis, which Tag 09ZR discharges rather than assumes; the second
carries `IsLocallyNoetherian S`, which Tag 09ZR exists in order to avoid. Withholding is
deliberate, and with Tag 01ZJ and Tag 0202 in place the first statement gives the tag with its
hypothesis deleted and nothing else changed.

## References

* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
* [Stacks Project, Tag 01ZJ](https://stacks.math.columbia.edu/tag/01ZJ)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Flatness

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- **The inverse system of Tag 09ZR, built from a closed immersion `j : X ⟶ Y`.** Its stages are
the closed subschemes of `Y` which are of finite presentation over `Y` and contain `X`; it is
`Stacks.Flatness.subschemeDiagram` at the ideal sheaf of `j`, read as a diagram of schemes rather
than of schemes over `Y`. -/
abbrev properStageDiagram (j : X ⟶ Y) [IsClosedImmersion j] :
    (FinitePresentationSubscheme j.ker)ᵒᵖ ⥤ Scheme.{u} :=
  subschemeDiagram j.ker ⋙ Over.forget Y

/-- **The structure morphisms of `AlgebraicGeometry.properStageDiagram` over a base `S`.** A stage
maps to `S` through `Y`. -/
def properStageStructure (j : X ⟶ Y) [IsClosedImmersion j] (p : Y ⟶ S) :
    properStageDiagram j ⟶ (Functor.const (FinitePresentationSubscheme j.ker)ᵒᵖ).obj S where
  app i := ((subschemeDiagram j.ker).obj i).hom ≫ p
  naturality i i' g := by
    dsimp only [Functor.comp_map, Functor.const_obj_map, Functor.const_obj_obj, Over.forget_map]
    rw [Category.comp_id, ← Category.assoc, Over.w ((subschemeDiagram j.ker).map g)]

/-- **The projections from `X` to the stages of `AlgebraicGeometry.properStageDiagram`.** They are
the legs of `AlgebraicGeometry.finitePresentationCone`, read in schemes. -/
abbrev properStageCone (j : X ⟶ Y) [IsClosedImmersion j] :
    (Functor.const (FinitePresentationSubscheme j.ker)ᵒᵖ).obj X ⟶ properStageDiagram j :=
  ((Over.forget Y).mapCone (finitePresentationCone j (le_refl j.ker))).π

/-- `X` is the limit of its finite-presentation closed enlargements inside `Y`, as a cone of
schemes. This is Tag 09ZP transported along `CategoryTheory.Over.forget`, which preserves
cofiltered limits. -/
def isLimit_properStageCone (j : X ⟶ Y) [IsClosedImmersion j] [CompactSpace Y]
    [QuasiSeparatedSpace Y] : IsLimit (Cone.mk X (properStageCone j)) :=
  haveI := isCofiltered_finitePresentationSubscheme_op j.ker
  isLimitOfPreserves (Over.forget Y) (isLimit_finitePresentationCone_of_qcqs j)

/-- A projection `X ⟶ X_i` followed by the closed immersion `X_i ⟶ Y` is `j`. -/
private theorem properStageCone_app_comp_hom (j : X ⟶ Y) [IsClosedImmersion j]
    (i : (FinitePresentationSubscheme j.ker)ᵒᵖ) :
    (properStageCone j).app i ≫ ((subschemeDiagram j.ker).obj i).hom = j :=
  Over.w ((finitePresentationCone j (le_refl j.ker)).π.app i)

/-- Every projection `X ⟶ X_i` is a closed immersion: it composes with the closed immersion
`X_i ⟶ Y` to give the closed immersion `j`. -/
theorem isClosedImmersion_properStageCone_app (j : X ⟶ Y) [IsClosedImmersion j]
    (i : (FinitePresentationSubscheme j.ker)ᵒᵖ) :
    IsClosedImmersion ((properStageCone j).app i) := by
  have h2 : IsClosedImmersion ((properStageCone j).app i ≫
      ((subschemeDiagram j.ker).obj i).hom) := by
    rw [properStageCone_app_comp_hom]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ ((subschemeDiagram j.ker).obj i).hom

/-- Every stage is proper over `S` as soon as `Y` is: a closed immersion is finite, hence
proper. -/
theorem isProper_properStageStructure_app (j : X ⟶ Y) [IsClosedImmersion j] (p : Y ⟶ S)
    [IsProper p] (i : (FinitePresentationSubscheme j.ker)ᵒᵖ) :
    IsProper ((properStageStructure j p).app i) := by
  change IsProper (((subschemeDiagram j.ker).obj i).hom ≫ p)
  infer_instance

/-- Every stage is of finite presentation over `S` as soon as `Y` is: each stage is of finite
presentation over `Y` by construction. -/
theorem finitePresentation_properStageStructure_app (j : X ⟶ Y) [IsClosedImmersion j] (p : Y ⟶ S)
    (hp : FinitePresentation p) (i : (FinitePresentationSubscheme j.ker)ᵒᵖ) :
    FinitePresentation ((properStageStructure j p).app i) :=
  (finitePresentation_subschemeDiagram_obj j.ker i).comp hp

/-- The cone of `AlgebraicGeometry.properStageCone` is a cone over `S`. -/
theorem properStageCone_comp_properStageStructure (j : X ⟶ Y) [IsClosedImmersion j] (p : Y ⟶ S) :
    properStageCone j ≫ properStageStructure j p =
      (Functor.const (FinitePresentationSubscheme j.ker)ᵒᵖ).map (j ≫ p) := by
  ext i
  change (properStageCone j).app i ≫ ((subschemeDiagram j.ker).obj i).hom ≫ p = j ≫ p
  rw [← Category.assoc, properStageCone_app_comp_hom]

/-- **Limits, Tag 09ZR from its single-stage form.** Let `f : X ⟶ S` be a morphism onto a
quasi-compact and quasi-separated scheme which factors as a closed immersion `X ⟶ X'` followed by
a morphism `X' ⟶ S` that is proper and of finite presentation. Then `X` is the limit of a
cofiltered inverse system of schemes proper and of finite presentation over `S`, whose transition
morphisms and whose projections from `X` are all closed immersions.

The system is the finite-presentation closed enlargements of `X` inside `X'`, and the limit is
Tag 09ZP. See the implementation notes for why no attribute is attached. -/
theorem exists_isProper_finitePresentation_isLimit_of_exists_model (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    (hmodel : ∃ (X' : Scheme.{u}) (g : X' ⟶ S) (ι : X ⟶ X') (_ : IsClosedImmersion ι),
      ι ≫ g = f ∧ IsProper g ∧ FinitePresentation g) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (t : D ⟶ (Functor.const I).obj S) (π : (Functor.const I).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X π)),
      (∀ i : I, IsProper (t.app i)) ∧ (∀ i : I, FinitePresentation (t.app i)) ∧
        (∀ (i i' : I) (g : i ⟶ i'), IsClosedImmersion (D.map g)) ∧
        (∀ i : I, IsClosedImmersion (π.app i)) ∧
        π ≫ t = (Functor.const I).map f := by
  obtain ⟨X', g, ι, hι, hfac, hproper, hfp⟩ := hmodel
  have := hι
  have := hproper
  have := hfp.1
  have := hfp.2.1
  have := hfp.2.2
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated g
  refine ⟨(FinitePresentationSubscheme ι.ker)ᵒᵖ, inferInstance,
    isCofiltered_finitePresentationSubscheme_op ι.ker, properStageDiagram ι,
    properStageStructure ι g, properStageCone ι, isLimit_properStageCone ι,
    fun i => isProper_properStageStructure_app ι g i,
    fun i => finitePresentation_properStageStructure_app ι g hfp i,
    fun i i' e => isClosedImmersion_subschemeDiagram_map ι.ker e,
    fun i => isClosedImmersion_properStageCone_app ι i, ?_⟩
  rw [properStageCone_comp_properStageStructure ι g, hfac]

/-- **Limits, Tag 09ZR over a locally Noetherian base, unconditionally.** A proper morphism onto
a locally Noetherian, quasi-compact and quasi-separated scheme is itself of finite presentation
(Tag 01TX part (2)), so the single-stage form of Tag 09ZR holds with `X' = X`, and the inverse
system of Tag 09ZR is the one built from the identity closed immersion of `X`. -/
theorem exists_isProper_finitePresentation_isLimit_of_isLocallyNoetherian (f : X ⟶ S)
    [IsProper f] [IsLocallyNoetherian S] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (t : D ⟶ (Functor.const I).obj S) (π : (Functor.const I).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X π)),
      (∀ i : I, IsProper (t.app i)) ∧ (∀ i : I, FinitePresentation (t.app i)) ∧
        (∀ (i i' : I) (g : i ⟶ i'), IsClosedImmersion (D.map g)) ∧
        (∀ i : I, IsClosedImmersion (π.app i)) ∧
        π ≫ t = (Functor.const I).map f :=
  exists_isProper_finitePresentation_isLimit_of_exists_model f
    ⟨X, f, 𝟙 X, inferInstance, Category.id_comp f, ‹IsProper f›,
      finitePresentation_of_finiteType f⟩

end AlgebraicGeometry

end
