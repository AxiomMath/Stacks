module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.FreeAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupActionQuotientAlgebraic

/-!
# The quotient of the arrow space by the stabilizer action (Stacks 06QJ)

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
and let `S ⟶ U` be its stabilizer group algebraic space (**Stacks 0448**). **Stacks 0449** makes
`S` act on `R`, read over `U` through the target morphism, by groupoid composition, and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFreeAction_stabilizer` says the action is free.
This file forms the quotient

    R' = R/S

and the two morphisms `s', t' : R' ⟶ U` through which the source and the target of the groupoid
factor, and records their properties.

This is the construction the proof of **Stacks 06QJ**, the implication (2) `⟹` (1), performs
after its first step: from a smooth groupoid presentation `𝒳 = [U/R]`, clause (2) makes `S ⟶ U`
flat and locally of finite presentation (**Stacks 06PR**), and then `R/S` is formed by
**Stacks 06PH**.

Nothing here is assumed beyond the flatness and the local finite presentation of the stabilizer
and of the source and the target of the groupoid, which is the datum clause (2) of Stacks 06QJ
supplies. Algebraicity of `R/S` is the first assertion of **Stacks 06PH**, which
`StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupActionQuotientAlgebraic` proves outright
from the bootstrap theorem **Stacks 04S6**, part (1) of which is
`AlgebraicGeometry.Bootstrap04S6.isAlgebraicSpace_quotient_preRelation`.

## Main definitions

All of these live in the namespace `AlgebraicGeometry.GroupoidInAlgebraicSpaces`.

* `stabilizerOrbitRelation`: the orbit pre-relation `S ×_U R ⟶ R ×_U R` of the stabilizer
  action, `(g, r) ↦ (c(g, r), r)`.
* `arrowStabilizerQuotient`: the quotient `R' = R/S`, and `toArrowStabilizerQuotient` the
  quotient map `π : R ⟶ R'`.
* `arrowStabilizerQuotientSource` and `arrowStabilizerQuotientTarget`: the morphisms
  `s', t' : R' ⟶ U` of the source's proof.

## Main results

* `stabilizerAction_left`: the action morphism, read on underlying arrows, is groupoid
  composition of the two projections.
* `stabilizerAction_comp_source` and `stabilizerAction_comp_target`: the action preserves both
  endpoints, which is what lets `s` and `t` descend.
* `toArrowStabilizerQuotient_comp_source` and `toArrowStabilizerQuotient_comp_target`: the
  descended morphisms restrict to `s` and `t` along `π`.
* `isSurjective_toArrowStabilizerQuotient`, `isFlat_toArrowStabilizerQuotient` and
  `isLocallyOfFinitePresentation_toArrowStabilizerQuotient`: `π` is surjective, flat and locally
  of finite presentation, which is **Stacks 06PH**.
* `isFlat_arrowStabilizerQuotientSource`, `isFlat_arrowStabilizerQuotientTarget` and their
  local-finite-presentation companions: `s'` and `t'` are flat and locally of finite
  presentation, by the fppf descent of **Stacks 06NR** along `π`.

## Implementation notes

The action morphism is identified on underlying arrows by evaluating
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerSMul_left` at the two projections of
`S ⊗ R`, whose `CartesianMonoidalCategory.lift` is the identity; so no separate computation of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerActionMap` is needed, and the
identification holds for the action of **Stacks 0449** as such rather than for the particular
morphism that builds it.

That the action preserves the source is `groupoidCompose_source`; that it preserves the target
is `groupoidCompose_target` together with the two structure equations of the projections out of
`S ⊗ R`, both sides being the structure morphism of that object. The descent of `s` and `t` is
then the universal property `AlgebraicGeometry.Space.quotientSheafDesc` of the quotient sheaf of
**Stacks 044J** at the sheaf of the object space.

Flatness and local finite presentation of `s'` and `t'` are **Stacks 06NR** applied to the
factorisations `s = π ≫ s'` and `t = π ≫ t'`, whose first factor is surjective as a map of fppf
sheaves; the hypotheses are flatness and local finite presentation of `s` and `t` themselves,
which for the presenting groupoid of **Stacks 04T3** come from its smoothness.

## References

* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 0449](https://stacks.math.columbia.edu/tag/0449)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 06PH](https://stacks.math.columbia.edu/tag/06PH)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The action morphism of **Stacks 0449**, read on underlying arrows: it is the groupoid
composition of the arrow of the first projection with the second projection. -/
theorem stabilizerAction_left (G : GroupoidInAlgebraicSpaces C S hS B) :
    (γ[stabilizer G, arrowsOverTarget G]).left =
      groupoidCompose G (stabilizerArrowHom G (fst (stabilizer G) (arrowsOverTarget G)))
        (snd (stabilizer G) (arrowsOverTarget G)).left
        (stabilizerArrowHom_arrowOverTarget_composable G
          (fst (stabilizer G) (arrowsOverTarget G))
          (snd (stabilizer G) (arrowsOverTarget G))) := by
  have hid : lift (fst (stabilizer G) (arrowsOverTarget G))
      (snd (stabilizer G) (arrowsOverTarget G)) ≫ γ[stabilizer G, arrowsOverTarget G] =
      γ[stabilizer G, arrowsOverTarget G] := by
    rw [lift_fst_snd, Category.id_comp]
  calc (γ[stabilizer G, arrowsOverTarget G]).left
      = (lift (fst (stabilizer G) (arrowsOverTarget G))
          (snd (stabilizer G) (arrowsOverTarget G)) ≫
            γ[stabilizer G, arrowsOverTarget G]).left := congrArg Over.Hom.left hid.symm
    _ = _ := stabilizerSMul_left G (fst (stabilizer G) (arrowsOverTarget G))
          (snd (stabilizer G) (arrowsOverTarget G))

/-- **The stabilizer action preserves the source of an arrow.** A composite `c(g, r)` has the
source of `r`. -/
theorem stabilizerAction_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    (γ[stabilizer G, arrowsOverTarget G]).left ≫ G.source.hom =
      (snd (stabilizer G) (arrowsOverTarget G)).left ≫ G.source.hom := by
  rw [stabilizerAction_left G, groupoidCompose_source]

/-- **The stabilizer action preserves the target of an arrow.** A composite `c(g, r)` has the
target of `g`, which is the point of the object space that `r` lies over, so the target of
`r`. -/
theorem stabilizerAction_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    (γ[stabilizer G, arrowsOverTarget G]).left ≫ G.target.hom =
      (snd (stabilizer G) (arrowsOverTarget G)).left ≫ G.target.hom := by
  rw [stabilizerAction_left G, groupoidCompose_target,
    stabilizerArrowHom_target G (fst (stabilizer G) (arrowsOverTarget G))]
  exact ((snd (stabilizer G) (arrowsOverTarget G)).w).symm

/-! ### The automorphism by which two arrows with the same endpoints differ -/

/-- **The arrow `f ∘ g⁻¹` attached to a pair `(f, g)` of arrows with the same source and the
same target.** It is an automorphism of their common target, which is the point of the object
space the stabilizer action of **Stacks 0449** is taken over.

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowDifference` is the companion `f⁻¹ ∘ g`, an
automorphism of the common *source*; that is the one the diagram of **Stacks 0454** uses, and it
is on the wrong side for the action by post-composition at the target. -/
noncomputable def arrowTargetDifference (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairs G ⟶ G.arrows.obj :=
  groupoidCompose G (arrowPairsFst G) (arrowPairsSnd G ≫ groupoidInverse G) (by
    rw [Category.assoc, groupoidInverse_target]
    exact arrowPairsFst_comp_source G)

/-- The source of `f ∘ g⁻¹` is the common target of `f` and `g`. -/
theorem arrowTargetDifference_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowTargetDifference G ≫ G.source.hom = arrowPairsSnd G ≫ G.target.hom := by
  rw [arrowTargetDifference, groupoidCompose_source, Category.assoc, groupoidInverse_source]

/-- The target of `f ∘ g⁻¹` is the common target of `f` and `g`. -/
theorem arrowTargetDifference_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowTargetDifference G ≫ G.target.hom = arrowPairsSnd G ≫ G.target.hom := by
  rw [arrowTargetDifference, groupoidCompose_target]
  exact arrowPairsFst_comp_target G

/-- The arrow `f ∘ g⁻¹`, read as a point of the stabilizer over the common target of `f` and
`g`. -/
noncomputable def arrowTargetDifferenceToStabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairs G ⟶ (stabilizer G).left :=
  pullback.lift (arrowTargetDifference G) (arrowPairsSnd G ≫ G.target.hom)
    (stabilizerArrow_condition G (arrowTargetDifference G) _
      (arrowTargetDifference_comp_source G) (arrowTargetDifference_comp_target G))

/-- The arrow underlying the stabilizer point `f ∘ g⁻¹` is `f ∘ g⁻¹`. -/
theorem arrowTargetDifferenceToStabilizer_comp_arrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowTargetDifferenceToStabilizer G ≫ stabilizerArrow G = arrowTargetDifference G :=
  pullback.lift_fst _ _ _

/-- The stabilizer point `f ∘ g⁻¹` lies over the common target of `f` and `g`. -/
theorem arrowTargetDifferenceToStabilizer_comp_hom
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowTargetDifferenceToStabilizer G ≫ (stabilizer G).hom =
      arrowPairsSnd G ≫ G.target.hom :=
  pullback.lift_snd _ _ _

/-- **Acting by `f ∘ g⁻¹` on `g` gives `f`.** This is the associativity of groupoid composition
together with the two unit laws, and it is what puts the two arrows of a pair with the same
source and the same target in one orbit of the stabilizer action. -/
theorem groupoidCompose_arrowTargetDifference_arrowPairsSnd
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (w : arrowTargetDifference G ≫ G.source.hom = arrowPairsSnd G ≫ G.target.hom) :
    groupoidCompose G (arrowTargetDifference G) (arrowPairsSnd G) w = arrowPairsFst G := by
  have wab : arrowPairsFst G ≫ G.source.hom =
      (arrowPairsSnd G ≫ groupoidInverse G) ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_target]
    exact arrowPairsFst_comp_source G
  have wbc : (arrowPairsSnd G ≫ groupoidInverse G) ≫ G.source.hom =
      arrowPairsSnd G ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  have hinv : groupoidCompose G (arrowPairsSnd G ≫ groupoidInverse G) (arrowPairsSnd G) wbc =
      identityAfterSource G (arrowPairsSnd G) :=
    groupoidCompose_inverseRight G (arrowPairsSnd G)
  have hid : identityAfterSource G (arrowPairsSnd G) =
      identityAfterSource G (arrowPairsFst G) := by
    simp only [identityAfterSource, ← Category.assoc, arrowPairsFst_comp_source G]
  have wR : arrowPairsFst G ≫ G.source.hom =
      groupoidCompose G (arrowPairsSnd G ≫ groupoidInverse G) (arrowPairsSnd G) wbc ≫
        G.target.hom := by
    rw [hinv, hid]
    exact identityAfterSource_composable G (arrowPairsFst G)
  calc
    groupoidCompose G (arrowTargetDifference G) (arrowPairsSnd G) w
        = groupoidCompose G (groupoidCompose G (arrowPairsFst G)
            (arrowPairsSnd G ≫ groupoidInverse G) wab) (arrowPairsSnd G) w := rfl
    _ = groupoidCompose G (arrowPairsFst G)
          (groupoidCompose G (arrowPairsSnd G ≫ groupoidInverse G) (arrowPairsSnd G) wbc) wR :=
        groupoidCompose_assoc G _ _ _ wab wbc w wR
    _ = groupoidCompose G (arrowPairsFst G) (identityAfterSource G (arrowPairsFst G))
          (identityAfterSource_composable G (arrowPairsFst G)) :=
        groupoidCompose_congr G _ _ rfl (hinv.trans hid)
    _ = arrowPairsFst G := groupoidCompose_rightIdentity G (arrowPairsFst G)

section Quotient

variable [HasSheafify (BigFppfOver.topology C S hS) (Type u)]

/-- The orbit pre-relation of the stabilizer action of **Stacks 0449**: the pre-relation
`S ×_U R ⟶ R ×_U R`, `(g, r) ↦ (c(g, r), r)`, of the action of the stabilizer group algebraic
space on the arrow space read over the object space. -/
noncomputable abbrev stabilizerOrbitRelation (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.PreRelation (stabilizer G ⊗ arrowsOverTarget G) (arrowsOverTarget G) :=
  Space.actionPreRelation (stabilizer G) (arrowsOverTarget G)

/-- **The quotient `R' = R/S` of the arrow space by the stabilizer action**, the quotient sheaf
of **Stacks 044J** of the orbit pre-relation. -/
@[sga "3 V 10.4" "more general"]
noncomputable abbrev arrowStabilizerQuotient (G : GroupoidInAlgebraicSpaces C S hS B) :
    Sheaf (BigFppfOver.topology C S hS) (Type u) :=
  Space.actionQuotientSheaf (stabilizer G) (arrowsOverTarget G)

/-- The quotient map `π : R ⟶ R/S`. -/
noncomputable abbrev toArrowStabilizerQuotient (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows.obj ⟶ (arrowStabilizerQuotient G).obj :=
  Space.toQuotientSheaf (stabilizerOrbitRelation G)

omit [HasSheafify (BigFppfOver.topology C S hS) (Type u)] in
/-- The source morphism of the groupoid equalizes the orbit relation, in the form the universal
property of the quotient sheaf takes. -/
theorem stabilizerOrbitRelation_source_eq (G : GroupoidInAlgebraicSpaces C S hS B) :
    (stabilizerOrbitRelation G).target.left ≫ G.source.hom =
      (stabilizerOrbitRelation G).source.left ≫ G.source.hom := by
  rw [Space.actionPreRelation_target, Space.actionPreRelation_source]
  exact stabilizerAction_comp_source G

omit [HasSheafify (BigFppfOver.topology C S hS) (Type u)] in
/-- The target morphism of the groupoid equalizes the orbit relation, in the form the universal
property of the quotient sheaf takes. -/
theorem stabilizerOrbitRelation_target_eq (G : GroupoidInAlgebraicSpaces C S hS B) :
    (stabilizerOrbitRelation G).target.left ≫ G.target.hom =
      (stabilizerOrbitRelation G).source.left ≫ G.target.hom := by
  rw [Space.actionPreRelation_target, Space.actionPreRelation_source]
  exact stabilizerAction_comp_target G

/-- The morphism `s' : R/S ⟶ U` through which the source of the groupoid factors. -/
noncomputable def arrowStabilizerQuotientSource (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowStabilizerQuotient G).obj ⟶ G.objects.obj :=
  (Space.quotientSheafDesc (stabilizerOrbitRelation G)
    ⟨G.objects.obj, G.objects.property.isSheaf⟩ G.source.hom
    (stabilizerOrbitRelation_source_eq G)).hom

/-- The morphism `t' : R/S ⟶ U` through which the target of the groupoid factors. -/
noncomputable def arrowStabilizerQuotientTarget (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowStabilizerQuotient G).obj ⟶ G.objects.obj :=
  (Space.quotientSheafDesc (stabilizerOrbitRelation G)
    ⟨G.objects.obj, G.objects.property.isSheaf⟩ G.target.hom
    (stabilizerOrbitRelation_target_eq G)).hom

/-- `s = π ≫ s'`: the source of the groupoid factors through the quotient map. -/
theorem toArrowStabilizerQuotient_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    toArrowStabilizerQuotient G ≫ arrowStabilizerQuotientSource G = G.source.hom :=
  Space.toQuotientSheaf_quotientSheafDesc (stabilizerOrbitRelation G) _ _ _

/-- `t = π ≫ t'`: the target of the groupoid factors through the quotient map. -/
theorem toArrowStabilizerQuotient_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    toArrowStabilizerQuotient G ≫ arrowStabilizerQuotientTarget G = G.target.hom :=
  Space.toQuotientSheaf_quotientSheafDesc (stabilizerOrbitRelation G) _ _ _

/-- **The quotient map `π : R ⟶ R/S` identifies any two arrows with the same source and the same
target.** Such a pair `(f, g)` differs by the automorphism `f ∘ g⁻¹` of its common target, which
is a point of the stabilizer, so `f` is the result of acting by it on `g`; and the quotient map
of **Stacks 044J** equalizes the orbit pre-relation.

Read on the two projections of `R ×_{U ×_B U} R` this is exactly the statement that
`j' = (t', s') : R/S ⟶ U ×_B U` is injective on generalized points coming from `R`, which is the
step of the proof of **Stacks 06QJ** that makes `j'` a monomorphism. -/
theorem arrowPairsFst_comp_toArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowPairsFst G ≫ toArrowStabilizerQuotient G =
      arrowPairsSnd G ≫ toArrowStabilizerQuotient G := by
  let T : Over G.objects.obj := Over.mk (arrowPairsSnd G ≫ G.target.hom)
  let r : T ⟶ arrowsOverTarget G := Over.homMk (arrowPairsSnd G) rfl
  let g : T ⟶ stabilizer G := Over.homMk (arrowTargetDifferenceToStabilizer G)
    (arrowTargetDifferenceToStabilizer_comp_hom G)
  have hrleft : r.left = arrowPairsSnd G := rfl
  have hg : stabilizerArrowHom G g = arrowTargetDifference G :=
    arrowTargetDifferenceToStabilizer_comp_arrow G
  have hact : (lift g r ≫ γ[stabilizer G, arrowsOverTarget G]).left = arrowPairsFst G :=
    (stabilizerSMul_left G g r).trans
      ((groupoidCompose_congr G
        (stabilizerArrowHom_arrowOverTarget_composable G g r)
        (arrowTargetDifference_comp_source G) hg hrleft).trans
        (groupoidCompose_arrowTargetDifference_arrowPairsSnd G _))
  have hL : (lift g r).left ≫ (γ[stabilizer G, arrowsOverTarget G]).left =
      arrowPairsFst G := by
    rw [← Over.comp_left, hact]
  have hR : (lift g r).left ≫ (snd (stabilizer G) (arrowsOverTarget G)).left =
      arrowPairsSnd G := by
    rw [← Over.comp_left, lift_snd]
    exact hrleft
  have horb := Space.target_toQuotientSheaf_eq_source (stabilizerOrbitRelation G)
  rw [Space.actionPreRelation_target, Space.actionPreRelation_source] at horb
  rw [← hL, ← hR, Category.assoc, Category.assoc, horb]

/-- **The quotient map `π : R ⟶ R/S` identifies any two generalized arrows with the same source
and the same target.** This is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowPairsFst_comp_toArrowStabilizerQuotient` read
at the point of `R ×_{U ×_B U} R` that the two arrows determine, and it is the form a consumer
uses: it says that `t'` and `s'` jointly separate the generalized points of `R/S` that come
from `R`. -/
theorem toArrowStabilizerQuotient_eq_of_source_eq_of_target_eq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {W : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a b : W ⟶ G.arrows.obj)
    (hs : a ≫ G.source.hom = b ≫ G.source.hom)
    (ht : a ≫ G.target.hom = b ≫ G.target.hom) :
    a ≫ toArrowStabilizerQuotient G = b ≫ toArrowStabilizerQuotient G := by
  have hw : a ≫ (sourceTarget G).hom = b ≫ (sourceTarget G).hom := by
    refine pullback.hom_ext ?_ ?_
    · change (a ≫ (sourceTarget G).hom) ≫ (objectPairsTarget G).hom =
        (b ≫ (sourceTarget G).hom) ≫ (objectPairsTarget G).hom
      rw [Category.assoc, Category.assoc, sourceTarget_target_projection]
      exact ht
    · change (a ≫ (sourceTarget G).hom) ≫ (objectPairsSource G).hom =
        (b ≫ (sourceTarget G).hom) ≫ (objectPairsSource G).hom
      rw [Category.assoc, Category.assoc, sourceTarget_source_projection]
      exact hs
  have h1 : pullback.lift a b hw ≫ arrowPairsFst G = a := pullback.lift_fst _ _ _
  have h2 : pullback.lift a b hw ≫ arrowPairsSnd G = b := pullback.lift_snd _ _ _
  simpa only [← Category.assoc, h1, h2] using
    pullback.lift a b hw ≫= arrowPairsFst_comp_toArrowStabilizerQuotient G

/-- The quotient map `π : R ⟶ R/S` is a surjection of fppf sheaves. -/
theorem isLocallySurjective_toArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (toArrowStabilizerQuotient G) :=
  Space.isLocallySurjective_toQuotientSheaf (stabilizerOrbitRelation G)

/-- **Stacks 06PH.** The quotient `R/S` of the arrow space by the stabilizer action is an
algebraic space, as soon as the stabilizer is flat and locally of finite presentation over the
object space. -/
@[stacks 06PH "R/S is an algebraic space"]
theorem isAlgebraicSpace_arrowStabilizerQuotient (G : GroupoidInAlgebraicSpaces C S hS B)
    (hflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom) :
    IsAlgebraicSpace C S hS (arrowStabilizerQuotient G).obj :=
  Space.isAlgebraicSpace_actionQuotientSheaf G.objects.property
    (stabilizer G) (arrowsOverTarget G) (stabilizerOverBase G).property G.arrows.property
    (isFreeAction_stabilizer G) hflat hfp

/-- **Stacks 06PH.** The quotient map `π : R ⟶ R/S` is surjective. -/
@[stacks 06PH "surjectivity of R ⟶ R/S"]
theorem isSurjective_toArrowStabilizerQuotient (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsSurjective C S hS (toArrowStabilizerQuotient G) :=
  Space.isSurjective_toActionQuotientSheaf (stabilizer G) (arrowsOverTarget G)

/-- **Stacks 06PH.** The quotient map `π : R ⟶ R/S` is flat. -/
@[stacks 06PH "flatness of R ⟶ R/S"]
theorem isFlat_toArrowStabilizerQuotient (G : GroupoidInAlgebraicSpaces C S hS B)
    (hflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom) :
    Space.IsFlat C S hS (toArrowStabilizerQuotient G) :=
  Space.isFlat_toActionQuotientSheaf G.objects.property
    (stabilizer G) (arrowsOverTarget G) (stabilizerOverBase G).property G.arrows.property
    (isFreeAction_stabilizer G) hflat hfp

/-- **Stacks 06PH.** The quotient map `π : R ⟶ R/S` is locally of finite presentation. -/
@[stacks 06PH "local finite presentation of R ⟶ R/S"]
theorem isLocallyOfFinitePresentation_toArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom) :
    Space.IsLocallyOfFinitePresentation C S hS (toArrowStabilizerQuotient G) :=
  Space.isLocallyOfFinitePresentation_toActionQuotientSheaf G.objects.property
    (stabilizer G) (arrowsOverTarget G) (stabilizerOverBase G).property G.arrows.property
    (isFreeAction_stabilizer G) hflat hfp

/-- A morphism out of `R/S` is flat as soon as its composite with `π` is. -/
private theorem isFlat_of_comp_toArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    {f : (arrowStabilizerQuotient G).obj ⟶ G.objects.obj}
    (h : Space.IsFlat C S hS (toArrowStabilizerQuotient G ≫ f)) : Space.IsFlat C S hS f :=
  Space.isFlat_of_comp_of_locallySurjective C S hS G.arrows.property
    (isAlgebraicSpace_arrowStabilizerQuotient G hSflat hSfp) G.objects.property
    (toArrowStabilizerQuotient G) f h (isLocallySurjective_toArrowStabilizerQuotient G)

/-- A morphism out of `R/S` is locally of finite presentation as soon as its composite with `π`
is. -/
private theorem isLocallyOfFinitePresentation_of_comp_toArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    {f : (arrowStabilizerQuotient G).obj ⟶ G.objects.obj}
    (h : Space.IsLocallyOfFinitePresentation C S hS (toArrowStabilizerQuotient G ≫ f)) :
    Space.IsLocallyOfFinitePresentation C S hS f :=
  Space.isLocallyOfFinitePresentation_of_comp_of_locallySurjective C S hS
    G.arrows.property (isAlgebraicSpace_arrowStabilizerQuotient G hSflat hSfp)
    G.objects.property (toArrowStabilizerQuotient G) f h
    (isLocallySurjective_toArrowStabilizerQuotient G)

/-- **Stacks 06NR.** The descended source `s' : R/S ⟶ U` is flat, because `s = π ≫ s'` is and
`π` is a surjection of fppf sheaves. -/
theorem isFlat_arrowStabilizerQuotientSource (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    (hs : Space.IsFlat C S hS G.source.hom) :
    Space.IsFlat C S hS (arrowStabilizerQuotientSource G) :=
  isFlat_of_comp_toArrowStabilizerQuotient G hSflat hSfp
    (by rwa [toArrowStabilizerQuotient_comp_source])

/-- **Stacks 06NR.** The descended target `t' : R/S ⟶ U` is flat. -/
theorem isFlat_arrowStabilizerQuotientTarget (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    (ht : Space.IsFlat C S hS G.target.hom) :
    Space.IsFlat C S hS (arrowStabilizerQuotientTarget G) :=
  isFlat_of_comp_toArrowStabilizerQuotient G hSflat hSfp
    (by rwa [toArrowStabilizerQuotient_comp_target])

/-- **Stacks 06NR.** The descended source `s' : R/S ⟶ U` is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_arrowStabilizerQuotientSource
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    (hs : Space.IsLocallyOfFinitePresentation C S hS G.source.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (arrowStabilizerQuotientSource G) :=
  isLocallyOfFinitePresentation_of_comp_toArrowStabilizerQuotient G hSflat hSfp
    (by rwa [toArrowStabilizerQuotient_comp_source])

/-- **Stacks 06NR.** The descended target `t' : R/S ⟶ U` is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_arrowStabilizerQuotientTarget
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    (ht : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (arrowStabilizerQuotientTarget G) :=
  isLocallyOfFinitePresentation_of_comp_toArrowStabilizerQuotient G hSflat hSfp
    (by rwa [toArrowStabilizerQuotient_comp_target])

end Quotient

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
