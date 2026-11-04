module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.Deformation.Artin.FormalObject.TruncationPullback
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSiteSupplement

/-!
# The étale lifts across a thickening, assembled into a diagram

Let `S` be a scheme contained in a big fppf site `B` and let `E : Λ ⥤ BigFppfOver B S hS` be a
diagram of objects of the site whose transition morphisms are thickenings — the shape of a
presentation of an affine formal algebraic space. Fix an index `i₀` below every other one and an
affine object `U` of the site étale over the stage `E i₀`. Then `U` lifts to an affine object
étale over every other stage, and the lifts assemble into a *diagram* over `E`, all of whose
squares are cartesian and all of whose transition morphisms are thickenings.

## Main definitions

* `AlgebraicGeometry.FormalSpace.EtaleLiftData`: the input of the construction — the diagram of
  stages, the thickening condition on its transition morphisms, the least index, and the affine
  object étale over the stage there.
* `AlgebraicGeometry.FormalSpace.StageLift` and
  `AlgebraicGeometry.FormalSpace.stageLift`: the datum of one lift, and the chosen one.
* `AlgebraicGeometry.FormalSpace.stageLiftTransition`: the transition morphism between two
  chosen lifts.
* `AlgebraicGeometry.FormalSpace.etaleLiftSiteDiagram`: **the diagram of lifts**, with
  `AlgebraicGeometry.FormalSpace.etaleLiftDiagramHom` its morphism to the diagram of stages.
* `AlgebraicGeometry.FormalSpace.etaleLiftDiagram`: the same diagram with codomain the big
  affine fppf category, which is where a presentation of an affine formal algebraic space
  lives; `AlgebraicGeometry.FormalSpace.etaleLiftSheafDiagram` is its composite with the
  sheafified Yoneda embedding, which is where the chart hypotheses of Stacks 0GVN live.

## Main results

* `AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isThickening_of_etale` and
  `AlgebraicGeometry.FormalSpace.existsUnique_siteHom_of_isThickening_of_etale`: a morphism into
  a scheme — or an object of the site — étale over `T` extends uniquely across a thickening over
  `T`. This is the one input the coherence needs.
* `AlgebraicGeometry.FormalSpace.nonempty_stageLift`: each individual lift exists.
* `AlgebraicGeometry.FormalSpace.existsUnique_stageLiftTransition` and
  `AlgebraicGeometry.FormalSpace.eq_stageLiftTransition`: the transition morphism exists and is
  characterised by two equations, which is what makes the lifts a diagram.
* `AlgebraicGeometry.FormalSpace.isPullback_etaleLiftDiagram_base`: the lift at `μ` base changes
  to `U` along the thickening from the stage at `i₀`.
* `AlgebraicGeometry.FormalSpace.isPullback_etaleLiftDiagram`: every square of the diagram of
  lifts over the diagram of stages is cartesian.
* `AlgebraicGeometry.FormalSpace.isThickening_etaleLiftSiteDiagram_map`: the transition
  morphisms of the diagram of lifts are thickenings.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_etaleLiftSheafDiagram_obj` and
  `AlgebraicGeometry.FormalSpace.relative_isThickening_etaleLiftSheafDiagram_map`: the two chart
  hypotheses `hGaff` and `hGthick` of Stacks 0GVN, for the diagram of lifts.

## Implementation notes

Each individual lift is
`AlgebraicGeometry.FormalSpace.exists_affine_etale_lift_of_isThickening`, which produces an
affine object of the site étale over the thicker stage whose base change along the thickening is
the given one, and does so from Stacks 039R and Stacks 06AD with no granted hypotheses.
Stacks 039R gives that lift only up to a unique isomorphism, so a choice of transition
morphisms between the lifts has to be made coherently; that choice, and not the lifting, is what
this file adds.

The coherence rests on a single statement, used four times: a morphism into a scheme étale over
`T` extends *uniquely* across a thickening over `T`. It is the section statement
`Stacks.Etale.existsUnique_section_of_universalHomeomorphism` for the base change of the étale
morphism, a thickening being a universal homeomorphism; no order hypothesis is placed on the
thickening and no nilpotence is used, so the statement applies to an arbitrary presentation.

With that in hand the transition morphism attached to `g : μ ⟶ ν` is *characterised* by two
equations — it lies over the transition morphism of the stages, and it is compatible with the
two morphisms out of `U`. Functoriality is then immediate: a composite of transition morphisms
satisfies the characterisation of the transition morphism of the composite, so the two agree.
No comparison isomorphism between iterated fibre products, and no cocycle condition on such
isomorphisms, is needed anywhere; that is the point of stating the characterisation in terms of
the morphisms out of `U` rather than in terms of chosen fibre products.

This is also the reason the index needs an element below every other one, and needs nothing
else — not directedness, not even that the index be a preorder beyond the morphisms `i₀ ⟶ μ`
being compatible with the transitions of `Λ`, which in a preorder they automatically are. A
directed index with no least element has to be handled by the consumer, by restricting to the
cofinal subpreorder above a chosen index; that restriction is not performed here.

That each square of the diagram is cartesian is proved the same way: the comparison morphism
from the lift at `μ` to the fibre product of the lift at `ν` with the stage at `μ` has an
inverse, both composites being endomorphisms compatible with the morphism from `U`, hence
identities. The transition morphisms of the diagram of lifts are therefore base changes of the
transition morphisms of the stages, and so thickenings.

Everything is proved for the big fppf category over `S` rather than for schemes. Two bridges do
that work: `AlgebraicGeometry.FormalSpace.exists_siteHom_of_comp_eq`, which recognizes a
morphism of schemes commuting with two morphisms to a common object of the category as a
morphism of the category, and
`Deformation.Artin.isPullback_of_toScheme`, which recognizes a commuting
square of the category whose image in schemes is cartesian as cartesian. The functor to schemes
is faithful but not full, so neither is formal.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### Unique extension of a morphism into an étale scheme across a thickening -/

/-- **A morphism into a scheme étale over `T` extends uniquely across a thickening.** Let
`i : U ⟶ V` be a thickening of schemes, let `w : G ⟶ T` be étale, let `v : V ⟶ T` and let
`d : U ⟶ G` lie over `i ≫ v`. Then there is a unique morphism `V ⟶ G` over `T` restricting to
`d` along `i`.

A thickening is a universal homeomorphism, so this is the statement that sections of the base
change `G ×_T V ⟶ V` of `w` are a topological invariant,
`Stacks.Etale.existsUnique_section_of_universalHomeomorphism`. -/
@[ega "IV 17.14.1" "partial",
  sga "1 I 5.5" "more general",
  sga "1 I 5.6",
  sga "1 IX 4.10" "full faithfulness",
  sga "3 X 2.0" "full faithfulness",
  sga "3 XI 1.1" "partial",
  sga "4 XII 6.13" "special case"]
theorem existsUnique_hom_of_isThickening_of_etale {U V T G : Scheme.{u}} (i : U ⟶ V)
    (hi : Stacks.Thickenings.IsThickening i) {v : V ⟶ T} {w : G ⟶ T} (hw : Etale w)
    (d : U ⟶ G) (hd : d ≫ w = i ≫ v) :
    ∃! α : V ⟶ G, i ≫ α = d ∧ α ≫ w = v := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion i := hi.1
  have : UniversalHomeomorphism i :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i hi.2
  have : Etale w := hw
  have : Etale (pullback.snd w v) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback w v) ‹Etale w›
  have hlift : d ≫ w = i ≫ v := hd
  set σ' : U ⟶ pullback w v := pullback.lift d i hlift with hσ'
  have hσ'snd : σ' ≫ pullback.snd w v = i := pullback.lift_snd _ _ _
  have hσ'fst : σ' ≫ pullback.fst w v = d := pullback.lift_fst _ _ _
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, hσuniq⟩ :=
    Stacks.Etale.existsUnique_section_of_universalHomeomorphism i (pullback.snd w v) σ' hσ'snd
  refine ⟨σ ≫ pullback.fst w v, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hσ₂, hσ'fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ₁, Category.id_comp]
  · rintro β ⟨hβ₁, hβ₂⟩
    have hβcond : β ≫ w = (𝟙 V) ≫ v := by rw [hβ₂, Category.id_comp]
    have hτ : pullback.lift β (𝟙 V) hβcond = σ := by
      refine hσuniq _ ⟨pullback.lift_snd _ _ _, pullback.hom_ext ?_ ?_⟩
      · rw [Category.assoc, pullback.lift_fst, hβ₁, hσ'fst]
      · rw [Category.assoc, pullback.lift_snd, Category.comp_id, hσ'snd]
    rw [← hτ, pullback.lift_fst]

/-- Auxiliary form of `AlgebraicGeometry.FormalSpace.exists_siteHom_of_comp_eq`, needed before
the variables of the next section are in scope. -/
private theorem exists_siteHom_of_comp_eq_aux (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y T : BigFppfOver B S hS} (t : X ⟶ T) (s : Y ⟶ T)
    (φ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hφ : φ ≫ (BigFppfOver.toScheme B S hS).map s = (BigFppfOver.toScheme B S hS).map t) :
    ∃ ψ : X ⟶ Y, (BigFppfOver.toScheme B S hS).map ψ = φ := by
  refine BigFppfOver.exists_hom_of_comp_eq B S hS φ ?_
  have hY : (Over.Hom.left s) ≫ T.hom = Y.hom := Over.w s
  have hX : (Over.Hom.left t) ≫ T.hom = X.hom := Over.w t
  rw [← hY, ← hX, B.inclusion.map_comp, B.inclusion.map_comp, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ B.inclusion.map T.hom) hφ

/-- **A morphism into an object of the big fppf category étale over `T` extends uniquely across
a thickening.** The form of
`AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isThickening_of_etale` for objects of the
big fppf category over `S`: the extension exists in the category because it commutes with the
structure morphisms to `S`, these being the composites through `T`, and it is unique there
because the functor to schemes is faithful. -/
@[sga "1 I 5.6" "special case"]
theorem existsUnique_siteHom_of_isThickening_of_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U V T G : BigFppfOver B S hS} (i : U ⟶ V)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    {v : V ⟶ T} {w : G ⟶ T} (hw : Etale ((BigFppfOver.toScheme B S hS).map w))
    (d : U ⟶ G) (hd : d ≫ w = i ≫ v) :
    ∃! α : V ⟶ G, i ≫ α = d ∧ α ≫ w = v := by
  have hinj : ∀ {X Y : BigFppfOver B S hS} {ψ₁ ψ₂ : X ⟶ Y},
      (BigFppfOver.toScheme B S hS).map ψ₁ = (BigFppfOver.toScheme B S hS).map ψ₂ → ψ₁ = ψ₂ :=
    fun h ↦ Over.OverMorphism.ext (B.inclusion.map_injective h)
  obtain ⟨α₀, ⟨hα₀₁, hα₀₂⟩, hα₀uniq⟩ :=
    existsUnique_hom_of_isThickening_of_etale ((BigFppfOver.toScheme B S hS).map i) hi
      (v := (BigFppfOver.toScheme B S hS).map v) hw ((BigFppfOver.toScheme B S hS).map d)
      (by rw [← Functor.map_comp, ← Functor.map_comp, hd])
  obtain ⟨α, hα⟩ := exists_siteHom_of_comp_eq_aux B S hS v w _ hα₀₂
  refine ⟨α, ⟨hinj ?_, hinj ?_⟩, ?_⟩
  · rw [Functor.map_comp, hα, hα₀₁]
  · rw [Functor.map_comp, hα, hα₀₂]
  · rintro β ⟨hβ₁, hβ₂⟩
    refine hinj ?_
    rw [hα]
    refine hα₀uniq _ ⟨?_, ?_⟩
    · rw [← Functor.map_comp, hβ₁]
    · rw [← Functor.map_comp, hβ₂]

/-! ### Recognizing morphisms and cartesian squares of the site among schemes -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor from the big fppf category over `S` to schemes is faithful: it is the forgetful
functor of an over category followed by the inclusion of a full subcategory of schemes. -/
theorem toScheme_map_injective {X Y : BigFppfOver B S hS} {ψ₁ ψ₂ : X ⟶ Y}
    (h : (BigFppfOver.toScheme B S hS).map ψ₁ = (BigFppfOver.toScheme B S hS).map ψ₂) :
    ψ₁ = ψ₂ :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

/-- A morphism between the underlying schemes of two objects of the big fppf category over `S`
which commutes with given morphisms of the category to a common object is itself a morphism of
the category: its compatibility with the structure morphisms to `S` is the compatibility with
the structure morphisms of the common object. -/
theorem exists_siteHom_of_comp_eq {X Y T : BigFppfOver B S hS} (t : X ⟶ T) (s : Y ⟶ T)
    (φ : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hφ : φ ≫ (BigFppfOver.toScheme B S hS).map s = (BigFppfOver.toScheme B S hS).map t) :
    ∃ ψ : X ⟶ Y, (BigFppfOver.toScheme B S hS).map ψ = φ :=
  exists_siteHom_of_comp_eq_aux B S hS t s φ hφ

/-! ### The individual lifts -/

/-- The input of the lifting construction: a diagram of objects of the big fppf category over
`S` whose transition morphisms are thickenings, an index `i₀` below every other one, and an
affine object of the category étale over the stage at `i₀`. -/
structure EtaleLiftData (Λ : Type (u + 1)) [Preorder Λ] where
  /-- The diagram of stages. -/
  stages : Λ ⥤ BigFppfOver B S hS
  /-- Every transition morphism of the diagram is a thickening. -/
  isThickening : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map (stages.map g))
  /-- The index at which the object to be lifted is given. -/
  bot : Λ
  /-- It lies below every other index. -/
  bot_le : ∀ μ : Λ, bot ≤ μ
  /-- The object to be lifted. -/
  src : BigFppfOver B S hS
  /-- Its underlying scheme is affine. -/
  srcAffine : IsAffine ((BigFppfOver.toScheme B S hS).obj src)
  /-- Its structure morphism to the stage at `bot`. -/
  srcProj : src ⟶ stages.obj bot
  /-- That morphism is étale. -/
  srcEtale : Etale ((BigFppfOver.toScheme B S hS).map srcProj)

variable {Λ : Type (u + 1)} [Preorder Λ]

/-- The datum of a lift of `d.src` across the thickening from the stage at `d.bot` to the stage
at `μ`: an affine object of the site étale over that stage, together with a cartesian square
exhibiting `d.src` as its base change. -/
structure StageLift (d : EtaleLiftData B S hS Λ) (μ : Λ) where
  /-- The lifted object of the site. -/
  obj : BigFppfOver B S hS
  /-- Its underlying scheme is affine. -/
  isAffine : IsAffine ((BigFppfOver.toScheme B S hS).obj obj)
  /-- Its structure morphism to the stage at `μ`. -/
  proj : obj ⟶ d.stages.obj μ
  /-- That morphism is étale. -/
  etale : Etale ((BigFppfOver.toScheme B S hS).map proj)
  /-- The morphism from `d.src`. -/
  base : d.src ⟶ obj
  /-- The square over the thickening of stages is cartesian. -/
  isPullback : IsPullback base d.srcProj proj (d.stages.map (homOfLE (d.bot_le μ)))

/-- **The lift exists.** This is
`AlgebraicGeometry.FormalSpace.exists_affine_etale_lift_of_isThickening` — Stacks 039R with the
size clause, together with the affineness of a thickening of an affine scheme, Stacks 06AD —
restated with its conclusion as a cartesian square of the site rather than as an isomorphism
with a fibre product of schemes. -/
theorem nonempty_stageLift (d : EtaleLiftData B S hS Λ) (μ : Λ) :
    Nonempty (StageLift B S hS d μ) := by
  obtain ⟨V, q, hq, hVaff, e, he⟩ :=
    exists_affine_etale_lift_of_isThickening B S hS
      (d.stages.map (homOfLE (d.bot_le μ))) (d.isThickening _) d.src d.srcAffine
      ((BigFppfOver.toScheme B S hS).map d.srcProj) d.srcEtale
  have hcomm : (e.inv ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ))))) ≫
          (BigFppfOver.toScheme B S hS).map q
      = (BigFppfOver.toScheme B S hS).map d.srcProj ≫
        (BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ))) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← he, Iso.inv_hom_id_assoc]
  have hschemePb : IsPullback (e.inv ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ)))))
      ((BigFppfOver.toScheme B S hS).map d.srcProj) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ)))) := by
    refine IsPullback.of_iso_pullback ⟨hcomm⟩ e.symm (by rw [Iso.symm_hom]) ?_
    rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]
  obtain ⟨b, hb⟩ := exists_siteHom_of_comp_eq B S hS
    (d.srcProj ≫ d.stages.map (homOfLE (d.bot_le μ))) q _ (by rw [hcomm, Functor.map_comp])
  have hbcomm : b ≫ q = d.srcProj ≫ d.stages.map (homOfLE (d.bot_le μ)) :=
    toScheme_map_injective B S hS (by rw [Functor.map_comp, Functor.map_comp, hb, hcomm])
  exact ⟨⟨V, hVaff, q, hq, b, Deformation.Artin.isPullback_of_toScheme hbcomm (by
    rwa [hb])⟩⟩

/-- The morphism from `d.src` into a lift is a thickening, being a base change of the
thickening of stages. -/
theorem StageLift.isThickening_base {d : EtaleLiftData B S hS Λ} {μ : Λ}
    (l : StageLift B S hS d μ) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map l.base) :=
  isThickening_isStableUnderBaseChange.of_isPullback
    (l.isPullback.map (BigFppfOver.toScheme B S hS)).flip (d.isThickening _)

/-! ### The chosen lifts and the transition morphisms between them -/

/-- The chosen lift of `d.src` to the stage at `μ`, from
`AlgebraicGeometry.FormalSpace.nonempty_stageLift`. Stacks 039R determines it only up to a
unique isomorphism, which is why a choice is made here and why the transition morphisms between
the choices have to be constructed. -/
noncomputable def stageLift (d : EtaleLiftData B S hS Λ) (μ : Λ) : StageLift B S hS d μ :=
  (nonempty_stageLift B S hS d μ).some

variable (d : EtaleLiftData B S hS Λ)

/-- **The transition morphism between two chosen lifts exists and is unique.** For `g : μ ⟶ ν`
there is exactly one morphism of the site from the lift at `μ` to the lift at `ν` which lies
over `d.stages.map g` and is compatible with the two morphisms out of `d.src`.

This is the whole content of the coherence: the two displayed equations *characterise* the
morphism, so a composite of transition morphisms, satisfying the characterisation of the
transition morphism of the composite, is it. The input is that the morphism out of `d.src` into
the lift at `μ` is a thickening and that the lift at `ν` is étale over the stage at `ν`, so that
`AlgebraicGeometry.FormalSpace.existsUnique_siteHom_of_isThickening_of_etale` applies. -/
theorem existsUnique_stageLiftTransition {μ ν : Λ} (g : μ ⟶ ν) :
    ∃! t : (stageLift B S hS d μ).obj ⟶ (stageLift B S hS d ν).obj,
      (stageLift B S hS d μ).base ≫ t = (stageLift B S hS d ν).base ∧
        t ≫ (stageLift B S hS d ν).proj
          = (stageLift B S hS d μ).proj ≫ d.stages.map g := by
  refine existsUnique_siteHom_of_isThickening_of_etale B S hS _
    (stageLift B S hS d μ).isThickening_base
    (v := (stageLift B S hS d μ).proj ≫ d.stages.map g) (stageLift B S hS d ν).etale
    (stageLift B S hS d ν).base ?_
  calc (stageLift B S hS d ν).base ≫ (stageLift B S hS d ν).proj
      = d.srcProj ≫ d.stages.map (homOfLE (d.bot_le ν)) := (stageLift B S hS d ν).isPullback.w
    _ = d.srcProj ≫ d.stages.map (homOfLE (d.bot_le μ) ≫ g) := by
        rw [Subsingleton.elim (homOfLE (d.bot_le μ) ≫ g) (homOfLE (d.bot_le ν))]
    _ = (d.srcProj ≫ d.stages.map (homOfLE (d.bot_le μ))) ≫ d.stages.map g := by
        rw [d.stages.map_comp, Category.assoc]
    _ = (stageLift B S hS d μ).base ≫ (stageLift B S hS d μ).proj ≫ d.stages.map g := by
        rw [← (stageLift B S hS d μ).isPullback.w, Category.assoc]

/-- The chosen transition morphism between two chosen lifts. -/
noncomputable def stageLiftTransition {μ ν : Λ} (g : μ ⟶ ν) :
    (stageLift B S hS d μ).obj ⟶ (stageLift B S hS d ν).obj :=
  (existsUnique_stageLiftTransition B S hS d g).exists.choose

/-- The transition morphism is compatible with the morphisms out of `d.src`. -/
theorem stageLiftTransition_base {μ ν : Λ} (g : μ ⟶ ν) :
    (stageLift B S hS d μ).base ≫ stageLiftTransition B S hS d g
      = (stageLift B S hS d ν).base :=
  (existsUnique_stageLiftTransition B S hS d g).exists.choose_spec.1

/-- The transition morphism lies over the transition morphism of the stages. -/
theorem stageLiftTransition_proj {μ ν : Λ} (g : μ ⟶ ν) :
    stageLiftTransition B S hS d g ≫ (stageLift B S hS d ν).proj
      = (stageLift B S hS d μ).proj ≫ d.stages.map g :=
  (existsUnique_stageLiftTransition B S hS d g).exists.choose_spec.2

/-- **The two equations characterise the transition morphism.** This is what makes the lifts
into a diagram. -/
theorem eq_stageLiftTransition {μ ν : Λ} (g : μ ⟶ ν)
    (t : (stageLift B S hS d μ).obj ⟶ (stageLift B S hS d ν).obj)
    (ht₁ : (stageLift B S hS d μ).base ≫ t = (stageLift B S hS d ν).base)
    (ht₂ : t ≫ (stageLift B S hS d ν).proj
      = (stageLift B S hS d μ).proj ≫ d.stages.map g) :
    t = stageLiftTransition B S hS d g :=
  (existsUnique_stageLiftTransition B S hS d g).unique ⟨ht₁, ht₂⟩
    ⟨stageLiftTransition_base B S hS d g, stageLiftTransition_proj B S hS d g⟩

/-- The transition morphism attached to an identity is the identity. -/
theorem stageLiftTransition_id (μ : Λ) :
    stageLiftTransition B S hS d (𝟙 μ) = 𝟙 (stageLift B S hS d μ).obj :=
  (eq_stageLiftTransition B S hS d (𝟙 μ) (𝟙 _) (Category.comp_id _)
    (by rw [Category.id_comp, d.stages.map_id, Category.comp_id])).symm

/-- The transition morphisms compose. -/
theorem stageLiftTransition_comp {μ ν ξ : Λ} (g : μ ⟶ ν) (h : ν ⟶ ξ) :
    stageLiftTransition B S hS d (g ≫ h)
      = stageLiftTransition B S hS d g ≫ stageLiftTransition B S hS d h :=
  (eq_stageLiftTransition B S hS d (g ≫ h) _
    (by rw [← Category.assoc, stageLiftTransition_base, stageLiftTransition_base])
    (by rw [Category.assoc, stageLiftTransition_proj, ← Category.assoc,
      stageLiftTransition_proj, Category.assoc, d.stages.map_comp])).symm


/-! ### The diagram -/

/-- **The lifts, assembled into a diagram of objects of the site.** The transition morphism of
`g : μ ⟶ ν` is the one characterised by
`AlgebraicGeometry.FormalSpace.existsUnique_stageLiftTransition`, and functoriality is the
uniqueness half of that characterisation. -/
noncomputable def etaleLiftSiteDiagram : Λ ⥤ BigFppfOver B S hS where
  obj μ := (stageLift B S hS d μ).obj
  map g := stageLiftTransition B S hS d g
  map_id μ := stageLiftTransition_id B S hS d μ
  map_comp g h := stageLiftTransition_comp B S hS d g h

/-- **The diagram of lifts lies over the diagram of stages.** Its component at `μ` is the
structure morphism of the lift at `μ`, and naturality is
`AlgebraicGeometry.FormalSpace.stageLiftTransition_proj`. -/
noncomputable def etaleLiftDiagramHom : etaleLiftSiteDiagram B S hS d ⟶ d.stages where
  app μ := (stageLift B S hS d μ).proj
  naturality _ _ g := stageLiftTransition_proj B S hS d g

/-- Each component of the morphism to the diagram of stages is étale. -/
theorem etale_etaleLiftDiagramHom_app (μ : Λ) :
    Etale ((BigFppfOver.toScheme B S hS).map ((etaleLiftDiagramHom B S hS d).app μ)) :=
  (stageLift B S hS d μ).etale

/-- Each object of the diagram of lifts is affine. -/
theorem isAffine_etaleLiftSiteDiagram_obj (μ : Λ) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((etaleLiftSiteDiagram B S hS d).obj μ)) :=
  (stageLift B S hS d μ).isAffine

/-- The square over the thickening from the stage at `d.bot` to the stage at `μ` is cartesian:
the lift at `μ` base changes to `d.src`. -/
theorem isPullback_etaleLiftDiagram_base (μ : Λ) :
    IsPullback (stageLift B S hS d μ).base d.srcProj ((etaleLiftDiagramHom B S hS d).app μ)
      (d.stages.map (homOfLE (d.bot_le μ))) :=
  (stageLift B S hS d μ).isPullback

/-- A self-map of `V` over `T` that is the identity on a thickening `i : U ⟶ V` is the identity,
when `V` is étale over `T`. -/
private theorem eq_id_of_isThickening_of_etale {U V T : Scheme.{u}} (i : U ⟶ V)
    (hi : Stacks.Thickenings.IsThickening i) {v : V ⟶ T} (hv : Etale v) (e : V ⟶ V)
    (he₁ : i ≫ e = i) (he₂ : e ≫ v = v) : e = 𝟙 V :=
  (existsUnique_hom_of_isThickening_of_etale i hi hv i rfl).unique ⟨he₁, he₂⟩
    ⟨Category.comp_id _, Category.id_comp _⟩

/-- **Every square of the diagram of lifts over the diagram of stages is cartesian.** The
comparison morphism from the lift at `μ` to the fibre product of the lift at `ν` with the stage
at `μ` is an isomorphism: both composites with the morphism in the other direction — which
exists because `d.src` is a thickening of both and both are étale over the stage at `μ` — are
endomorphisms compatible with the morphism from `d.src`, hence identities. -/
theorem isPullback_etaleLiftDiagram {μ ν : Λ} (g : μ ⟶ ν) :
    IsPullback ((etaleLiftSiteDiagram B S hS d).map g) ((etaleLiftDiagramHom B S hS d).app μ)
      ((etaleLiftDiagramHom B S hS d).app ν) (d.stages.map g) := by
  have hproj : stageLiftTransition B S hS d g ≫ (stageLift B S hS d ν).proj
      = (stageLift B S hS d μ).proj ≫ d.stages.map g :=
    stageLiftTransition_proj B S hS d g
  refine Deformation.Artin.isPullback_of_toScheme hproj ?_
  -- Notation for the images in schemes.
  set A := (BigFppfOver.toScheme B S hS).map (stageLift B S hS d ν).proj with hA
  set Gg := (BigFppfOver.toScheme B S hS).map (d.stages.map g) with hGg
  set t := IsPullback.of_hasPullback A Gg with ht
  have hsndEtale : Etale (pullback.snd A Gg) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback t (stageLift B S hS d ν).etale
  -- `d.src` is the fibre product of the lift at `ν` with the stage at `d.bot`; factoring that
  -- through the stage at `μ` exhibits it as a thickening of the fibre product.
  have hs : IsPullback ((BigFppfOver.toScheme B S hS).map (stageLift B S hS d ν).base)
      ((BigFppfOver.toScheme B S hS).map d.srcProj) A
      ((BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ))) ≫ Gg) := by
    rw [hGg, ← Functor.map_comp, ← d.stages.map_comp,
      Subsingleton.elim (homOfLE (d.bot_le μ) ≫ g) (homOfLE (d.bot_le ν))]
    exact (stageLift B S hS d ν).isPullback.map (BigFppfOver.toScheme B S hS)
  have hQ := IsPullback.of_right' hs t
  set uQ := t.lift ((BigFppfOver.toScheme B S hS).map (stageLift B S hS d ν).base)
    ((BigFppfOver.toScheme B S hS).map d.srcProj ≫
      (BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ))))
    (by rw [hs.w, Category.assoc]) with huQ
  have hQthick : Stacks.Thickenings.IsThickening uQ :=
    isThickening_isStableUnderBaseChange.of_isPullback hQ.flip (d.isThickening _)
  have huQfst : uQ ≫ pullback.fst A Gg
      = (BigFppfOver.toScheme B S hS).map (stageLift B S hS d ν).base := t.lift_fst _ _ _
  have huQsnd : uQ ≫ pullback.snd A Gg
      = (BigFppfOver.toScheme B S hS).map d.srcProj ≫
        (BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ))) :=
    t.lift_snd _ _ _
  -- The comparison morphism, and its inverse by unique extension across the thickening.
  have hcc : (BigFppfOver.toScheme B S hS).map (stageLiftTransition B S hS d g) ≫ A
      = (BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).proj ≫ Gg := by
    rw [hA, hGg, ← Functor.map_comp, ← Functor.map_comp, hproj]
  set c := t.lift ((BigFppfOver.toScheme B S hS).map (stageLiftTransition B S hS d g))
    ((BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).proj) hcc with hc
  have hcfst : c ≫ pullback.fst A Gg
      = (BigFppfOver.toScheme B S hS).map (stageLiftTransition B S hS d g) := t.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd A Gg
      = (BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).proj := t.lift_snd _ _ _
  have hPμetale : Etale ((BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).proj) :=
    (stageLift B S hS d μ).etale
  have hbaseμthick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).base) :=
    (stageLift B S hS d μ).isThickening_base
  have hbaseμproj : (BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).base ≫
      (BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).proj
      = (BigFppfOver.toScheme B S hS).map d.srcProj ≫
        (BigFppfOver.toScheme B S hS).map (d.stages.map (homOfLE (d.bot_le μ))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, (stageLift B S hS d μ).isPullback.w]
  have hbasec : (BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).base ≫ c = uQ := by
    refine t.hom_ext ?_ ?_
    · rw [Category.assoc, hcfst, huQfst, ← Functor.map_comp,
        stageLiftTransition_base B S hS d g]
    · rw [Category.assoc, hcsnd, huQsnd, hbaseμproj]
  obtain ⟨c', ⟨hc'₁, hc'₂⟩, -⟩ :=
    existsUnique_hom_of_isThickening_of_etale uQ hQthick (v := pullback.snd A Gg) hPμetale
      ((BigFppfOver.toScheme B S hS).map (stageLift B S hS d μ).base)
      (by rw [hbaseμproj, huQsnd])
  have hcc' : c ≫ c' = 𝟙 _ := eq_id_of_isThickening_of_etale _ hbaseμthick hPμetale _
    (by rw [← Category.assoc, hbasec, hc'₁]) (by rw [Category.assoc, hc'₂, hcsnd])
  have hc'c : c' ≫ c = 𝟙 _ := eq_id_of_isThickening_of_etale _ hQthick hsndEtale _
    (by rw [← Category.assoc, hc'₁, hbasec]) (by rw [Category.assoc, hcsnd, hc'₂])
  exact IsPullback.of_iso_pullback ⟨hcc⟩ ⟨c, c', hcc', hc'c⟩ hcfst hcsnd

/-- **The transition morphisms of the diagram of lifts are thickenings**, being base changes of
the transition morphisms of the diagram of stages. This is the hypothesis in the shape Stacks
0GVM and Stacks 0GVN consume. -/
theorem isThickening_etaleLiftSiteDiagram_map {μ ν : Λ} (g : μ ⟶ ν) :
    Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map ((etaleLiftSiteDiagram B S hS d).map g)) :=
  isThickening_isStableUnderBaseChange.of_isPullback
    ((isPullback_etaleLiftDiagram B S hS d g).map (BigFppfOver.toScheme B S hS)).flip
    (d.isThickening g)

/-- **The diagram of lifts, as a diagram of affine objects of the site.** This is the shape a
presentation of an affine formal algebraic space is given in, and the shape the chart
hypotheses of Stacks 0GVN are stated in; its composite with the inclusion is
`AlgebraicGeometry.FormalSpace.etaleLiftSiteDiagram`, about which everything above is
stated. -/
noncomputable def etaleLiftDiagram : Λ ⥤ BigAffineFppf B S hS where
  obj μ := ⟨(stageLift B S hS d μ).obj, (stageLift B S hS d μ).isAffine⟩
  map g := InducedCategory.homMk (stageLiftTransition B S hS d g)
  map_id μ := InducedCategory.hom_ext (stageLiftTransition_id B S hS d μ)
  map_comp g h := by
    apply InducedCategory.hom_ext
    simp only [InducedCategory.homMk_hom, ObjectProperty.FullSubcategory.comp_hom]
    exact stageLiftTransition_comp B S hS d g h

/-- The affine diagram of lifts is the diagram of lifts. -/
theorem etaleLiftDiagram_comp_inclusion :
    etaleLiftDiagram B S hS d ⋙ BigAffineFppf.inclusion B S hS
      = etaleLiftSiteDiagram B S hS d :=
  rfl


/-! ### The diagram of lifts as a diagram of sheaves -/

variable (d : EtaleLiftData B S hS Λ)

/-- **The diagram of lifts, as a diagram of fppf sheaves over `S`.** This is the shape in which
the chart hypotheses of Stacks 0GVN are stated. -/
noncomputable abbrev etaleLiftSheafDiagram : Λ ⥤ FppfSheaf B S hS :=
  etaleLiftSiteDiagram B S hS d ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)

/-- Each object of the sheaf diagram of lifts is an affine formal algebraic space: it is the
sheaf represented by an affine object of the site. This is the hypothesis `hGaff` of Stacks
0GVN. -/
theorem isAffineFormalAlgebraicSpace_etaleLiftSheafDiagram_obj (μ : Λ) :
    IsAffineFormalAlgebraicSpace B S hS ((etaleLiftSheafDiagram B S hS d).obj μ) :=
  isAffineFormalAlgebraicSpace_sheafifiedYoneda' B S hS _ (stageLift B S hS d μ).isAffine

/-- Each transition morphism of the sheaf diagram of lifts is a representable thickening, in the
relative form along the sheafified Yoneda embedding. This is the hypothesis `hGthick` of
Stacks 0GVN. -/
theorem relative_isThickening_etaleLiftSheafDiagram_map {μ ν : Λ} (g : μ ⟶ ν) :
    MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
      ((etaleLiftSheafDiagram B S hS d).map g) := by
  let : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro X₁ X₂ Y₂ X₃ f g f' g' hs hg
    exact isThickening_isStableUnderBaseChange.of_isPullback
      (hs.map (BigFppfOver.toScheme B S hS)) hg
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
    dsimp only [Sheaf.sheafifiedYoneda]
    infer_instance
  exact MorphismProperty.relative_map (isThickening_etaleLiftSiteDiagram_map B S hS d g)

end AlgebraicGeometry.FormalSpace

end
