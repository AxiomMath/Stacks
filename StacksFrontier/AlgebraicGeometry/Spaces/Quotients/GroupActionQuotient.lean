module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PseudoTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient of an algebraic space by a free action of a group algebraic space

Let `X ⟶ B` be a morphism of algebraic spaces and let a group algebraic space `G` over `B`
act on `X` over `B`. The action cuts out the pre-relation `(g, x) ↦ (g · x, x)` on `X`, whose
quotient sheaf is the quotient `X/G` of **Stacks 044J**. This file proves **Stacks 06PH**: if
the action is free and `G ⟶ B` is flat and locally of finite presentation, then `X/G` is an
algebraic space, the morphism `X ⟶ X/G` is surjective, flat and locally of finite
presentation, and `X` is an fppf `G`-torsor over `X/G`.

## Main definitions

* `AlgebraicGeometry.Space.actionPreRelation` is the orbit pre-relation
  `G ×_B X ⟶ X ×_B X`, `(g, x) ↦ (g · x, x)`, whose target is the action morphism and whose
  source is the projection.
* `AlgebraicGeometry.Space.actionQuotientSheaf` is **Stacks 044J** for a group action: the
  quotient `X/G`, the quotient sheaf of the orbit pre-relation.
* `AlgebraicGeometry.Space.QuotientBootstrap` is the instance of the bootstrap theorem
  **Stacks 04S6** which the first assertion of Stacks 06PH consumes.
* `AlgebraicGeometry.Space.groupOverQuotient` and
  `AlgebraicGeometry.Space.sourceOverQuotient` are `G` pulled back to `X/G` and `X` read over
  `X/G`, the group and the acted-on space of the torsor assertion.

## Main results

* `AlgebraicGeometry.Space.rel_actionPreRelation_iff` identifies the relation induced on the
  points of a test scheme over the base with the orbit relation `x ~ y ↔ ∃ g, g · y = x`, and
  `AlgebraicGeometry.Space.isPreEquivalenceRelation_actionPreRelation` deduces that it is a
  pre-equivalence relation.
* `AlgebraicGeometry.Space.mono_actionPreRelation_iff` is **Stacks 06P9** read for the orbit
  pre-relation: it is a monomorphism exactly when the action is free. Together with the
  previous item this gives
  `AlgebraicGeometry.Space.isEquivalenceRelation_actionPreRelation`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_snd` and
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_smul`: an étale-local, base-change-stable
  property of morphisms of schemes passes from `G ⟶ B` to the projection and to the action
  morphism `G ×_B X ⟶ X`.
* `AlgebraicGeometry.Space.quotientModObj` is the action of `G ×_B X/G` on `X` over `X/G`,
  and `AlgebraicGeometry.Space.isIso_leftSMul_quotient` is the resulting pseudo-torsor
  condition, which is the identification `G ×_B X = X ×_{X/G} X`.
* `AlgebraicGeometry.Space.isSurjective_toActionQuotientSheaf`: the surjectivity assertion of
  **Stacks 06PH**, which needs no hypothesis on the action.
* `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap`,
  `AlgebraicGeometry.Space.isFlat_toActionQuotientSheaf_of_quotientBootstrap`,
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_toActionQuotientSheaf_of_quotientBootstrap`
  and `AlgebraicGeometry.Space.isFppfTorsor_actionQuotientSheaf_of_quotientBootstrap`: the other
  assertions of Stacks 06PH from any proof of the instance `QuotientBootstrap` of Stacks 04S6
  that they consume. That instance is proved, and the assertions are stated without it, in
  `StacksFrontier/AlgebraicGeometry/Spaces/Quotients/GroupActionQuotientAlgebraic.lean`.

## Implementation notes

The quotient is the quotient sheaf of the orbit pre-relation rather than of the pre-relation
of the action groupoid of **Stacks 0444**. The two pre-relations have the same target and
source, namely the action morphism and the projection, so they agree; taking the pre-relation
directly keeps the base an arbitrary presheaf, as the quotient-sheaf API of Stacks 044J has
it, and avoids the transport through the heterogeneous identifications that package the action
groupoid.

The orbit pre-relation lands in the categorical product `X ⨯ X` of the slice over `B`, which
is the shape a pre-relation has, whereas `CategoryTheory.ModObj.leftSMul` lands in the
monoidal product `X ⊗ X`. The two are the same fibre product `X ×_B X` presented by different
chosen objects, so the two morphisms differ by an isomorphism and monicity transfers; this is
the only content of `AlgebraicGeometry.Space.mono_actionPreRelation_iff`.

The first assertion of Stacks 06PH is immediate from the bootstrap theorem Stacks 04S6. This file
is imported by modules on which the proof of Stacks 04S6 does not depend, so the assertions are
stated here from the instance of Stacks 04S6 that they consume, `QuotientBootstrap`, as an
argument, and the argument is discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/GroupActionQuotientAlgebraic.lean`. Flatness and
local finite presentation consume the first assertion through
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_toQuotientSheaf`; surjectivity needs neither.

The torsor assertion is stated with `AlgebraicGeometry.Space.IsFppfTorsor` of Stacks 04TY,
whose base must be `X/G`, so the group is `G` pulled back along `X/G ⟶ B`. Its group-object
structure is transported by the monoidal functor `CategoryTheory.Over.pullback`, but the
action is not: `X` over `X/G` is not the pullback of `X`, so the action morphism is built
from the identification `(G ×_B X/G) ×_{X/G} X = G ×_B X`, whose `X/G`-coordinate is
determined by its `X`-coordinate. The module laws are reduced to the laws of the pointwise
action on hom-sets, for which the comparison is a monoid homomorphism.

Flatness and local finite presentation of the action morphism come from the corresponding
property of `G ⟶ B` in two steps, as in the source: the projection `G ×_B X ⟶ X` is the base
change of `G ⟶ B` along `X ⟶ B`, and the shear automorphism `(g, x) ↦ (g⁻¹, g · x)` of
`G ×_B X` carries the projection to the action morphism.

## References

* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 06P9](https://stacks.math.columbia.edu/tag/06P9)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 06PH](https://stacks.math.columbia.edu/tag/06PH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}

/-! ### The orbit pre-relation -/

/-- The orbit pre-relation `G ×_B X ⟶ X ×_B X`, `(g, x) ↦ (g · x, x)`, cut out by an action of
a group algebraic space `G` on `X` over `B`. Its target is the action morphism and its source
is the projection. -/
noncomputable def actionPreRelation (G X : Over B) [GrpObj G] [ModObj G X] :
    PreRelation (G ⊗ X) X :=
  prod.lift γ[G, X] (snd G X)

/-- The target of the orbit pre-relation is the action morphism. -/
@[simp]
theorem actionPreRelation_target (G X : Over B) [GrpObj G] [ModObj G X] :
    (actionPreRelation G X).target = γ[G, X] := by
  simp [actionPreRelation, PreRelation.target]

/-- The source of the orbit pre-relation is the projection `G ×_B X ⟶ X`. -/
@[simp]
theorem actionPreRelation_source (G X : Over B) [GrpObj G] [ModObj G X] :
    (actionPreRelation G X).source = snd G X := by
  simp [actionPreRelation, PreRelation.source]

/-- **Stacks 06P9** for the orbit pre-relation: it is a monomorphism exactly when the action
is free. The pre-relation and the shear morphism `CategoryTheory.ModObj.leftSMul` differ by
the isomorphism between the categorical and the monoidal product of the slice. -/
@[sga "3 IV 3.2.1" "(i), special case", sga "3 V 10.2.1" "more general"]
theorem mono_actionPreRelation_iff (G X : Over B) [GrpObj G] [ModObj G X] :
    Mono (actionPreRelation G X) ↔ IsFreeAction site S hS B G X := by
  obtain ⟨e, he⟩ : ∃ e : (X ⊗ X : Over B) ≅ X ⨯ X,
      actionPreRelation G X = ModObj.leftSMul G X ≫ e.hom :=
    ⟨{ hom := prod.lift (fst X X) (snd X X)
       inv := lift prod.fst prod.snd
       hom_inv_id := by apply CartesianMonoidalCategory.hom_ext <;> simp
       inv_hom_id := by apply prod.hom_ext <;> simp },
      by apply prod.hom_ext <;> simp [actionPreRelation]⟩
  rw [Space.isFreeAction_iff_mono_leftSMul]
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · have hinv : ModObj.leftSMul G X = actionPreRelation G X ≫ e.inv := by
      rw [he, Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [hinv]
    exact mono_comp _ _
  · rw [he]
    exact mono_comp _ _

/-- A free action cuts out a relation: its orbit pre-relation is a monomorphism. -/
theorem mono_actionPreRelation (G X : Over B) [GrpObj G] [ModObj G X]
    (hfree : IsFreeAction site S hS B G X) : Mono (actionPreRelation G X) :=
  (mono_actionPreRelation_iff G X).mpr hfree

/-- The relation induced by the orbit pre-relation on the `X`-valued points of a test scheme
over the base is the orbit relation: two points are related exactly when a point of `G` over
the same base point carries the second to the first. -/
theorem rel_actionPreRelation_iff (G X : Over B) [GrpObj G] [ModObj G X]
    {T : BigFppfOver site S hS} {b : yoneda.obj T ⟶ B} (x y : TestPoint T b X) :
    (actionPreRelation G X).Rel b x y ↔
      ∃ g : (Over.mk b : Over B) ⟶ G,
        g • (Over.homMk y.1 y.2 : (Over.mk b : Over B) ⟶ X) = Over.homMk x.1 x.2 := by
  constructor
  · rintro ⟨r, hx, hy⟩
    set R : (Over.mk b : Over B) ⟶ G ⊗ X := Over.homMk r.1 r.2 with hR
    have hsnd : R ≫ snd G X = Over.homMk y.1 y.2 :=
      Over.OverMorphism.ext (by simpa [hR] using hy)
    have hgam : R ≫ γ[G, X] = Over.homMk x.1 x.2 :=
      Over.OverMorphism.ext (by simpa [hR] using hx)
    have hlift : lift (R ≫ fst G X) (R ≫ snd G X) = R := by apply hom_ext <;> simp
    exact ⟨R ≫ fst G X, by rw [← hsnd, Hom.smul_def, hlift, hgam]⟩
  · rintro ⟨g, hg⟩
    refine ⟨⟨(lift g (Over.homMk y.1 y.2 : (Over.mk b : Over B) ⟶ X)).left, Over.w _⟩, ?_, ?_⟩
    · rw [actionPreRelation_target, ← Over.comp_left, ← Hom.smul_def, hg]
      rfl
    · rw [actionPreRelation_source, ← Over.comp_left, lift_snd]
      rfl

/-- The orbit relation of a group action is a pre-equivalence relation: on the points of every
test scheme over the base it is the orbit relation of a group action on a set. -/
theorem isPreEquivalenceRelation_actionPreRelation (G X : Over B) [GrpObj G] [ModObj G X] :
    IsPreEquivalenceRelation (actionPreRelation G X) := by
  intro T b
  refine ⟨fun x => (rel_actionPreRelation_iff G X x x).mpr ⟨1, one_smul _ _⟩,
    fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
  · obtain ⟨g, hg⟩ := (rel_actionPreRelation_iff G X x y).mp hxy
    exact (rel_actionPreRelation_iff G X y x).mpr ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  · obtain ⟨g, hg⟩ := (rel_actionPreRelation_iff G X x y).mp hxy
    obtain ⟨h, hh⟩ := (rel_actionPreRelation_iff G X y z).mp hyz
    exact (rel_actionPreRelation_iff G X x z).mpr ⟨g * h, by rw [mul_smul, hh, hg]⟩

/-- The orbit pre-relation of a free action is an equivalence relation. -/
@[sga "3 IV 3.2.1" "for a free action", sga "3 IV 3.4.4" "partial"]
theorem isEquivalenceRelation_actionPreRelation (G X : Over B) [GrpObj G] [ModObj G X]
    (hfree : IsFreeAction site S hS B G X) :
    IsEquivalenceRelation (actionPreRelation G X).target (actionPreRelation G X).source :=
  (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).mpr
    ⟨mono_actionPreRelation G X hfree, isPreEquivalenceRelation_actionPreRelation G X⟩

/-! ### Flatness and local finite presentation of the projection and the action -/

/-- The *shear* automorphism `(g, x) ↦ (g⁻¹, g · x)` of the action space `G ×_B X`. It
exchanges the projection and the action morphism. -/
noncomputable def actionShear (G X : Over B) [GrpObj G] [ModObj G X] : G ⊗ X ⟶ G ⊗ X :=
  lift (fst G X)⁻¹ γ[G, X]

/-- The first coordinate of the shear of `(g, x)` is `g⁻¹`. -/
@[reassoc (attr := simp)]
theorem actionShear_fst (G X : Over B) [GrpObj G] [ModObj G X] :
    actionShear G X ≫ fst G X = (fst G X)⁻¹ :=
  lift_fst _ _

/-- The second coordinate of the shear of `(g, x)` is `g · x`. -/
@[reassoc (attr := simp)]
theorem actionShear_snd (G X : Over B) [GrpObj G] [ModObj G X] :
    actionShear G X ≫ snd G X = γ[G, X] :=
  lift_snd _ _

/-- The shear automorphism is an involution, by the group and action laws on points. -/
theorem actionShear_actionShear (G X : Over B) [GrpObj G] [ModObj G X] :
    actionShear G X ≫ actionShear G X = 𝟙 (G ⊗ X) := by
  have hγ : γ[G, X] = (fst G X) • (snd G X) := by
    rw [CategoryTheory.Hom.smul_def, lift_fst_snd, Category.id_comp]
  apply hom_ext
  · rw [Category.assoc, actionShear_fst, GrpObj.comp_inv, actionShear_fst, inv_inv,
      Category.id_comp]
  · rw [Category.assoc, actionShear_snd, hγ, ModObj.comp_smul, actionShear_fst,
      actionShear_snd, hγ, inv_smul_smul, Category.id_comp]

/-- The presheaf morphism underlying the shear automorphism is an isomorphism. -/
theorem isIso_actionShear_left (G X : Over B) [GrpObj G] [ModObj G X] :
    IsIso (actionShear G X).left := by
  have h : (actionShear G X).left ≫ (actionShear G X).left = 𝟙 (G ⊗ X).left := by
    rw [← Over.comp_left, actionShear_actionShear, Over.id_left]
  exact ⟨(actionShear G X).left, h, h⟩

/-- A property of morphisms of schemes which is étale local on source and target and stable
under base change passes from `G ⟶ B` to the projection `G ×_B X ⟶ X`, which is the base
change of `G ⟶ B` along `X ⟶ B`. -/
theorem holdsOnEveryEtaleChart_snd (G X : Over B) [GrpObj G] [ModObj G X]
    (hB : IsAlgebraicSpace site S hS B) (hG : IsAlgebraicSpace site S hS G.left)
    (hX : IsAlgebraicSpace site S hS X.left)
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange]
    (hGB : HoldsOnEveryEtaleChart site S hS P G.hom) :
    HoldsOnEveryEtaleChart site S hS P (snd G X).left := by
  let Bsp : AlgebraicSpaces site S hS := ⟨B, hB⟩
  let gsp : (⟨G.left, hG⟩ : AlgebraicSpaces site S hS) ⟶ Bsp := ObjectProperty.homMk G.hom
  let xsp : (⟨X.left, hX⟩ : AlgebraicSpaces site S hS) ⟶ Bsp := ObjectProperty.homMk X.hom
  exact (holdsOnEveryEtaleChart_isStableUnderBaseChange site S hS P hP).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct site S hS gsp xsp) hGB

/-- A property of morphisms of schemes which is étale local on source and target and stable
under base change passes from `G ⟶ B` to the action morphism `G ×_B X ⟶ X`: the shear
automorphism carries the projection to the action morphism. -/
theorem holdsOnEveryEtaleChart_smul (G X : Over B) [GrpObj G] [ModObj G X]
    (hB : IsAlgebraicSpace site S hS B) (hG : IsAlgebraicSpace site S hS G.left)
    (hX : IsAlgebraicSpace site S hS X.left)
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange]
    (hGB : HoldsOnEveryEtaleChart site S hS P G.hom) :
    HoldsOnEveryEtaleChart site S hS P γ[G, X].left := by
  have := isIso_actionShear_left G X
  have h : γ[G, X].left = (actionShear G X).left ≫ (snd G X).left := by
    rw [← Over.comp_left, actionShear_snd]
  rw [h]
  let Q : MorphismProperty ((BigFppfOver site S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => HoldsOnEveryEtaleChart site S hS P f
  let _ : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso_presheaf site S hS P
  exact (Q.cancel_left_of_respectsIso (actionShear G X).left (snd G X).left).mpr
    (holdsOnEveryEtaleChart_snd G X hB hG hX P hP hGB)

/-! ### The quotient `X/G` -/

variable [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- **Stacks 044J** for a group action: the quotient `X/G` of an algebraic space by the action
of a group algebraic space, the quotient sheaf of the orbit pre-relation. -/
@[stacks 044J "quotient by a group action"]
noncomputable abbrev actionQuotientSheaf (G X : Over B) [GrpObj G] [ModObj G X] :
    Sheaf (BigFppfOver.topology site S hS) (Type u) :=
  quotientSheaf (actionPreRelation G X)

/-- The instance of the bootstrap theorem **Stacks 04S6**, part (1), that the quotient of a
free action consumes: the quotient sheaf of an equivalence relation on algebraic spaces whose
source and target are flat and locally of finite presentation is an algebraic space.

Stacks 04S6 is proved as `AlgebraicGeometry.Space.quotientBootstrap`. Part (1) of the source
asks in addition for a
composition law making the relation a groupoid in algebraic spaces; for an equivalence
relation that law is determined by the relation, so it is not imposed here. -/
abbrev QuotientBootstrap (site : BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (BigFppfOver.topology site S hS) (Type u)] : Prop :=
  ∀ {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z} (j : PreRelation R U),
    IsAlgebraicSpace site S hS Z → IsAlgebraicSpace site S hS R.left →
    IsAlgebraicSpace site S hS U.left →
    IsEquivalenceRelation j.target j.source →
    IsFlat site S hS j.source.left → IsFlat site S hS j.target.left →
    IsLocallyOfFinitePresentation site S hS j.source.left →
    IsLocallyOfFinitePresentation site S hS j.target.left →
    IsAlgebraicSpace site S hS (quotientSheaf j).obj

/-- **Stacks 06PH.** The quotient `X/G` of an algebraic space by a free action of a group
algebraic space which is flat and locally of finite presentation over the base is an
algebraic space.

The orbit pre-relation is an equivalence relation because the action is free, and its source
and target are flat and locally of finite presentation because `G ⟶ B` is; the bootstrap
theorem Stacks 04S6, given as the argument `h04S6`, then concludes. -/
theorem isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap
    (h04S6 : QuotientBootstrap site S hS)
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsAlgebraicSpace site S hS (actionQuotientSheaf G X).obj :=
  h04S6 (actionPreRelation G X) hB
    (isAlgebraicSpace_pullback site S hS G.hom X.hom hG hX hB) hX
    (isEquivalenceRelation_actionPreRelation G X hfree)
    (by
      simpa using holdsOnEveryEtaleChart_snd G X hB hG hX _
        Flat.isEtaleLocalOnSourceAndTarget hflat)
    (by
      simpa using holdsOnEveryEtaleChart_smul G X hB hG hX _
        Flat.isEtaleLocalOnSourceAndTarget hflat)
    (by
      simpa using holdsOnEveryEtaleChart_snd G X hB hG hX _
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hfp)
    (by
      simpa using holdsOnEveryEtaleChart_smul G X hB hG hX _
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hfp)

/-- **Stacks 06PH.** The quotient morphism `X ⟶ X/G` is surjective.

This holds for the quotient sheaf of any pre-relation, by Stacks 06PG, so neither freeness
nor any property of `G ⟶ B` is needed. -/
@[stacks 06PH "surjectivity of X ⟶ X/G"]
theorem isSurjective_toActionQuotientSheaf (G X : Over B) [GrpObj G] [ModObj G X] :
    IsSurjective site S hS (toQuotientSheaf (actionPreRelation G X)) :=
  isSurjective_toQuotientSheaf _

/-- The quotient morphism `X ⟶ X/G` inherits an étale-local property of `G ⟶ B` which is local
at the target and stable under base change, from the action morphism (Stacks 06PG). -/
private theorem holdsOnEveryEtaleChart_toActionQuotientSheaf
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X)
    (hQ : IsAlgebraicSpace site S hS (actionQuotientSheaf G X).obj)
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage] [P.IsStableUnderBaseChange]
    (hGB : HoldsOnEveryEtaleChart site S hS P G.hom) :
    HoldsOnEveryEtaleChart site S hS P (toQuotientSheaf (actionPreRelation G X)) :=
  holdsOnEveryEtaleChart_toQuotientSheaf (actionPreRelation G X)
    (isEquivalenceRelation_actionPreRelation G X hfree)
    (isAlgebraicSpace_pullback site S hS G.hom X.hom hG hX hB) hX hQ P hP
    (holdsOnEveryEtaleChart_isStableUnderBaseChange site S hS P hP)
    (by simpa using holdsOnEveryEtaleChart_smul G X hB hG hX P hP hGB)

/-- **Stacks 06PH.** The quotient morphism `X ⟶ X/G` of a free action of a group algebraic
space which is flat and locally of finite presentation over the base is flat.

By Stacks 06PG the quotient morphism inherits flatness from the target of the orbit
pre-relation, which is the action morphism, once the quotient is known to be an algebraic
space; that is the first assertion of Stacks 06PH, so the hypothesis `h04S6` reappears
here. -/
theorem isFlat_toActionQuotientSheaf_of_quotientBootstrap
    (h04S6 : QuotientBootstrap site S hS)
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsFlat site S hS (toQuotientSheaf (actionPreRelation G X)) :=
  holdsOnEveryEtaleChart_toActionQuotientSheaf hB G X hG hX hfree
    (isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap h04S6 hB G X hG hX hfree hflat hfp)
    _ Flat.isEtaleLocalOnSourceAndTarget hflat

/-- **Stacks 06PH.** The quotient morphism `X ⟶ X/G` of a free action of a group algebraic
space which is flat and locally of finite presentation over the base is locally of finite
presentation.

As for flatness, Stacks 06PG transfers the property from the action morphism once the
quotient is known to be an algebraic space, which is the first assertion of Stacks 06PH. -/
theorem isLocallyOfFinitePresentation_toActionQuotientSheaf_of_quotientBootstrap
    (h04S6 : QuotientBootstrap site S hS)
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsLocallyOfFinitePresentation site S hS (toQuotientSheaf (actionPreRelation G X)) :=
  holdsOnEveryEtaleChart_toActionQuotientSheaf hB G X hG hX hfree
    (isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap h04S6 hB G X hG hX hfree hflat hfp)
    _ LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hfp


/-! ### The quotient map as an fppf covering -/

/-- The diagonal `U ⟶ U ×_{U/R} U`, read as a section of the pullback of `U` along the
quotient map over `U` itself. -/
noncomputable def quotientDiagonalSection {R U : Over B} (j : PreRelation R U) :
    𝟙_ (Over U.left) ⟶
      (Over.pullback (toQuotientSheaf j)).obj (Over.mk (toQuotientSheaf j)) :=
  Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _)

/-- The quotient map of a pre-relation, read as a one-member family, is jointly surjective. -/
theorem isJointlySurjective_toQuotientSheaf {R U : Over B} (j : PreRelation R U) :
    IsJointlySurjective site S hS (fun _ : PUnit.{u + 2} => U.left)
      (fun _ => toQuotientSheaf j) :=
  (isJointlySurjective_const_iff site S hS (I := PUnit.{u + 2}) (toQuotientSheaf j)).mpr
    (isSurjective_toQuotientSheaf j)

/-- The quotient map of a pre-relation, read as a one-member family, is an fppf covering of
the quotient sheaf as soon as it is flat and locally of finite presentation and both the
source and the quotient are algebraic spaces. -/
theorem isFppfCovering_toQuotientSheaf {R U : Over B} (j : PreRelation R U)
    (hQ : IsAlgebraicSpace site S hS (quotientSheaf j).obj)
    (hU : IsAlgebraicSpace site S hS U.left)
    (hflat : IsFlat site S hS (toQuotientSheaf j))
    (hfp : IsLocallyOfFinitePresentation site S hS (toQuotientSheaf j)) :
    IsFppfCovering site S hS (fun _ : PUnit.{u + 2} => U.left)
      (fun _ => toQuotientSheaf j) where
  target_isAlgebraicSpace := hQ
  source_isAlgebraicSpace _ := hU
  flat _ := hflat
  locallyOfFinitePresentation _ := hfp
  jointly_surjective := isJointlySurjective_toQuotientSheaf j


/-! ### The action on the quotient -/

section Quotient

variable (hB : Presheaf.IsSheaf (BigFppfOver.topology site S hS) B)
  (G X : Over B) [GrpObj G] [ModObj G X]

/-- The quotient `X/G` of `X` by the action of `G`, as a presheaf on the big fppf site. -/
noncomputable abbrev actionQuotientPresheaf : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u :=
  (actionQuotientSheaf G X).obj

/-- The structure morphism `X/G ⟶ B` of the quotient. -/
noncomputable abbrev actionQuotientToBase : actionQuotientPresheaf G X ⟶ B :=
  (quotientSheafToBase hB (actionPreRelation G X)).hom

/-- `X`, read as a space over its quotient `X/G`. -/
noncomputable abbrev sourceOverQuotient : Over (actionQuotientPresheaf G X) :=
  Over.mk (toQuotientSheaf (actionPreRelation G X))

/-- `G`, pulled back from `B` to the quotient `X/G`. -/
noncomputable abbrev groupOverQuotient : Over (actionQuotientPresheaf G X) :=
  (Over.pullback (actionQuotientToBase hB G X)).obj G

/-- The two legs of `(G ×_B X/G) ×_{X/G} X` land over the same point of `B`. -/
theorem quotientTensorComparison_aux :
    (pullback.fst (groupOverQuotient hB G X).hom (sourceOverQuotient G X).hom ≫
        pullback.fst G.hom (actionQuotientToBase hB G X)) ≫ G.hom =
      pullback.snd (groupOverQuotient hB G X).hom (sourceOverQuotient G X).hom ≫ X.hom := by
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    show pullback.snd G.hom (actionQuotientToBase hB G X) =
      (groupOverQuotient hB G X).hom from rfl, pullback.condition, Category.assoc,
    show (sourceOverQuotient G X).hom ≫ actionQuotientToBase hB G X = X.hom from
      toQuotientSheaf_quotientSheafToBase hB _]

/-- The canonical comparison `(G ×_B X/G) ×_{X/G} X ⟶ G ×_B X`: the `X/G`-coordinate of a
point is the image of its `X`-coordinate, so the two fibre products agree. -/
noncomputable def quotientTensorComparison :
    (groupOverQuotient hB G X ⊗ sourceOverQuotient G X).left ⟶ (G ⊗ X).left :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst G.hom (actionQuotientToBase hB G X))
    (pullback.snd _ _) (quotientTensorComparison_aux hB G X)

/-- The `G`-coordinate of the comparison is the `G`-coordinate of the `G ×_B X/G` factor. -/
@[reassoc (attr := simp)]
theorem quotientTensorComparison_fst :
    quotientTensorComparison hB G X ≫ (fst G X).left =
      pullback.fst _ _ ≫ pullback.fst G.hom (actionQuotientToBase hB G X) :=
  pullback.lift_fst ..

/-- The `X`-coordinate of the comparison is the `X`-coordinate of the source. -/
@[reassoc (attr := simp)]
theorem quotientTensorComparison_snd :
    quotientTensorComparison hB G X ≫ (snd G X).left = pullback.snd _ _ :=
  pullback.lift_snd ..

/-- The quotient projection identifies the action with the second projection. -/
theorem action_toQuotientSheaf_eq_snd :
    γ[G, X].left ≫ toQuotientSheaf (actionPreRelation G X) =
      (snd G X).left ≫ toQuotientSheaf (actionPreRelation G X) := by
  have := target_toQuotientSheaf_eq_source (actionPreRelation G X)
  rwa [actionPreRelation_target, actionPreRelation_source] at this

/-- **Stacks 06PH.** The action of `G ×_B X/G` on `X` over the quotient `X/G`: the original
action read through the identification `(G ×_B X/G) ×_{X/G} X = G ×_B X`. -/
noncomputable def quotientSMul :
    groupOverQuotient hB G X ⊗ sourceOverQuotient G X ⟶ sourceOverQuotient G X :=
  Over.homMk (quotientTensorComparison hB G X ≫ γ[G, X].left) <| by
    rw [Category.assoc,
      show (sourceOverQuotient G X).hom = toQuotientSheaf (actionPreRelation G X) from rfl,
      action_toQuotientSheaf_eq_snd, quotientTensorComparison_snd_assoc,
      Over.tensorObj_hom]
    exact pullback.condition.symm

/-- The action over the quotient is the comparison followed by the original action. -/
@[simp]
theorem quotientSMul_left :
    (quotientSMul hB G X).left = quotientTensorComparison hB G X ≫ γ[G, X].left :=
  rfl

/-- A space over the quotient `X/G`, read as a space over `B`. -/
noncomputable abbrev overBaseOfOverQuotient (Z : Over (actionQuotientPresheaf G X)) : Over B :=
  Over.mk (Z.hom ≫ actionQuotientToBase hB G X)

variable {Z : Over (actionQuotientPresheaf G X)}

/-- A point of `G ×_B X/G` over the quotient, read as a point of `G` over `B`. -/
noncomputable def groupPointOverBase (m : Z ⟶ groupOverQuotient hB G X) :
    overBaseOfOverQuotient hB G X Z ⟶ G :=
  Over.homMk (m.left ≫ pullback.fst G.hom (actionQuotientToBase hB G X)) <| by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      show pullback.snd G.hom (actionQuotientToBase hB G X) =
        (groupOverQuotient hB G X).hom from rfl, Over.w]
    rfl

/-- A point of `X` over the quotient, read as a point of `X` over `B`. -/
noncomputable def sourcePointOverBase (x : Z ⟶ sourceOverQuotient G X) :
    overBaseOfOverQuotient hB G X Z ⟶ X :=
  Over.homMk x.left <| by
    rw [← toQuotientSheaf_quotientSheafToBase hB (actionPreRelation G X), ← Category.assoc,
      show toQuotientSheaf (actionPreRelation G X) = (sourceOverQuotient G X).hom from rfl,
      Over.w]
    rfl

/-- The underlying morphism of `groupPointOverBase` is the `G`-coordinate of the point. -/
@[simp]
theorem groupPointOverBase_left (m : Z ⟶ groupOverQuotient hB G X) :
    (groupPointOverBase hB G X m).left =
      m.left ≫ pullback.fst G.hom (actionQuotientToBase hB G X) :=
  rfl

/-- The underlying morphism of `sourcePointOverBase` is that of the point. -/
@[simp]
theorem sourcePointOverBase_left (x : Z ⟶ sourceOverQuotient G X) :
    (sourcePointOverBase hB G X x).left = x.left :=
  rfl

/-- The comparison morphism turns a pair of points over the quotient into the corresponding
pair of points over the base. -/
theorem lift_quotientTensorComparison (m : Z ⟶ groupOverQuotient hB G X)
    (x : Z ⟶ sourceOverQuotient G X) :
    (lift m x).left ≫ quotientTensorComparison hB G X =
      (lift (groupPointOverBase hB G X m) (sourcePointOverBase hB G X x)).left := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [quotientTensorComparison, Over.lift_left, groupPointOverBase_left,
      sourcePointOverBase_left, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc]

/-- Acting on a point of `X` over the quotient agrees with acting over the base. -/
theorem lift_quotientSMul_left (m : Z ⟶ groupOverQuotient hB G X)
    (x : Z ⟶ sourceOverQuotient G X) :
    (lift m x ≫ quotientSMul hB G X).left =
      (groupPointOverBase hB G X m • sourcePointOverBase hB G X x).left := by
  rw [Hom.smul_def, Over.comp_left, Over.comp_left, quotientSMul_left, ← Category.assoc,
    lift_quotientTensorComparison]

/-- The second projection of `B ×_B X/G` is inverted by a section whose first projection is
the structure morphism of the quotient. -/
theorem inv_snd_comp_fst_quotientToBase :
    inv (pullback.snd (𝟙 B) (actionQuotientToBase hB G X)) ≫
        pullback.fst (𝟙 B) (actionQuotientToBase hB G X) = actionQuotientToBase hB G X := by
  rw [IsIso.inv_comp_eq]
  simpa using pullback.condition (f := 𝟙 B) (g := actionQuotientToBase hB G X)

/-- Reading a point of `G ×_B X/G` over the base preserves the unit. -/
theorem groupPointOverBase_one :
    groupPointOverBase hB G X (1 : Z ⟶ groupOverQuotient hB G X) = 1 := by
  apply Over.OverMorphism.ext
  simp only [Hom.one_def, Over.comp_left, groupPointOverBase_left, Over.toUnit_left,
    Functor.obj.η_def, Over.ε_pullback_left, Over.pullback_map_left, Over.tensorUnit_hom,
    Category.assoc, pullback.lift_fst]
  rw [reassoc_of% inv_snd_comp_fst_quotientToBase hB G X]
  rfl

/-- The lax monoidal comparison for `Over.pullback` reads a pair of points of `G ×_B X/G` as
the corresponding pair of points of `G`. -/
theorem lift_mu_pullback_fst (m n : Z ⟶ groupOverQuotient hB G X) :
    (lift m n).left ≫
        (Functor.LaxMonoidal.μ (Over.pullback (actionQuotientToBase hB G X)) G G).left ≫
          pullback.fst (G ⊗ G).hom (actionQuotientToBase hB G X) =
      (lift (groupPointOverBase hB G X m) (groupPointOverBase hB G X n)).left := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [Over.lift_left, groupPointOverBase_left, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      Over.μ_pullback_left_fst_fst, Over.μ_pullback_left_fst_snd]

/-- Reading a point of `G ×_B X/G` over the base is multiplicative. -/
theorem groupPointOverBase_mul (m n : Z ⟶ groupOverQuotient hB G X) :
    groupPointOverBase hB G X (m * n) =
      groupPointOverBase hB G X m * groupPointOverBase hB G X n := by
  apply Over.OverMorphism.ext
  simp only [Hom.mul_def, Over.comp_left, groupPointOverBase_left, Functor.obj.μ_def,
    Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  rw [reassoc_of% lift_mu_pullback_fst hB G X m n]

/-- **Stacks 06PH.** `G ×_B X/G` acts on `X` over the quotient `X/G`. -/
noncomputable instance quotientModObj :
    ModObj (groupOverQuotient hB G X) (sourceOverQuotient G X) where
  smul := quotientSMul hB G X
  one_smul := by
    have h1 : (η : 𝟙_ (Over (actionQuotientPresheaf G X)) ⟶ groupOverQuotient hB G X) ▷
        sourceOverQuotient G X = lift (fst _ _ ≫ η) (snd _ _) := by
      refine hom_ext _ _ (by simp) (by simp)
    have h2 : fst (𝟙_ (Over (actionQuotientPresheaf G X))) (sourceOverQuotient G X) ≫ η =
        (1 : 𝟙_ (Over (actionQuotientPresheaf G X)) ⊗ sourceOverQuotient G X ⟶
          groupOverQuotient hB G X) := by
      rw [Hom.one_def, toUnit_unique (fst (𝟙_ (Over (actionQuotientPresheaf G X)))
        (sourceOverQuotient G X)) (toUnit _)]
    change _ ▷ _ ≫ quotientSMul hB G X = (λ_ (sourceOverQuotient G X)).hom
    rw [h1]
    apply Over.OverMorphism.ext
    rw [lift_quotientSMul_left, h2, groupPointOverBase_one, one_smul, leftUnitor_hom,
      sourcePointOverBase_left]
  mul_smul := by
    have h3 : (μ : groupOverQuotient hB G X ⊗ groupOverQuotient hB G X ⟶ _) ▷
        sourceOverQuotient G X = lift (fst _ _ ≫ μ) (snd _ _) := by
      refine hom_ext _ _ (by simp) (by simp)
    have h4 : fst (groupOverQuotient hB G X ⊗ groupOverQuotient hB G X)
          (sourceOverQuotient G X) ≫ μ =
        (fst _ _ ≫ fst (groupOverQuotient hB G X) (groupOverQuotient hB G X)) *
          (fst _ _ ≫ snd (groupOverQuotient hB G X) (groupOverQuotient hB G X)) := by
      rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
    have hα : (α_ (groupOverQuotient hB G X) (groupOverQuotient hB G X)
          (sourceOverQuotient G X)).hom =
        lift (fst _ _ ≫ fst _ _) (lift (fst _ _ ≫ snd _ _) (snd _ _)) :=
      hom_ext _ _ (by simp) (hom_ext _ _ (by simp) (by simp))
    have h6 : sourcePointOverBase hB G X
          (lift (fst (groupOverQuotient hB G X ⊗ groupOverQuotient hB G X)
              (sourceOverQuotient G X) ≫ snd _ _) (snd _ _) ≫ quotientSMul hB G X) =
        groupPointOverBase hB G X (fst (groupOverQuotient hB G X ⊗ groupOverQuotient hB G X)
            (sourceOverQuotient G X) ≫ snd _ _) •
          sourcePointOverBase hB G X (snd _ _) :=
      Over.OverMorphism.ext (by rw [sourcePointOverBase_left, lift_quotientSMul_left])
    change _ ▷ _ ≫ quotientSMul hB G X =
      (α_ (groupOverQuotient hB G X) (groupOverQuotient hB G X)
          (sourceOverQuotient G X)).hom ≫
        (groupOverQuotient hB G X ◁ quotientSMul hB G X) ≫ quotientSMul hB G X
    rw [h3, ← Category.assoc, hα, lift_whiskerLeft]
    apply Over.OverMorphism.ext
    rw [lift_quotientSMul_left, lift_quotientSMul_left, h4, groupPointOverBase_mul, mul_smul, h6]

/-- The action morphism of `quotientModObj` is `quotientSMul`. -/
@[simp]
theorem quotientModObj_smul :
    γ[groupOverQuotient hB G X, sourceOverQuotient G X] = quotientSMul hB G X :=
  rfl

/-- The action of a point of `G ×_B X/G` on a point of `X` over the quotient, computed in
`G ×_B X`. -/
theorem smul_left_eq (m : Z ⟶ groupOverQuotient hB G X) (x : Z ⟶ sourceOverQuotient G X) :
    (m • x).left =
      (lift (groupPointOverBase hB G X m) (sourcePointOverBase hB G X x)).left ≫
        γ[G, X].left := by
  rw [Hom.smul_def, quotientModObj_smul, lift_quotientSMul_left, Hom.smul_def, Over.comp_left]

/-- The `G`-coordinate of the pair of points over the base is the `G`-coordinate of `m`. -/
@[simp]
theorem lift_point_left_fst (m : Z ⟶ groupOverQuotient hB G X)
    (x : Z ⟶ sourceOverQuotient G X) :
    (lift (groupPointOverBase hB G X m) (sourcePointOverBase hB G X x)).left ≫
        pullback.fst G.hom X.hom =
      m.left ≫ pullback.fst G.hom (actionQuotientToBase hB G X) := by
  simp only [Over.lift_left, groupPointOverBase_left, pullback.lift_fst]

/-- The `X`-coordinate of the pair of points over the base is `x`. -/
@[simp]
theorem lift_point_left_snd (m : Z ⟶ groupOverQuotient hB G X)
    (x : Z ⟶ sourceOverQuotient G X) :
    (lift (groupPointOverBase hB G X m) (sourcePointOverBase hB G X x)).left ≫
        pullback.snd G.hom X.hom =
      x.left := by
  simp only [Over.lift_left, sourcePointOverBase_left, pullback.lift_snd]

/-- **Stacks 06PH.** For a free action with quotient an equivalence relation, `X` is a
pseudo-torsor under `G ×_B X/G` over the quotient `X/G`: the shear map is an isomorphism. -/
@[sga "3 IV 5.1.6" "(iv) ⇒ (ii)", sga "3 IV 5.1.7" "(i) ⇒ (ii)", sga "3 VIA 3.3.2" "more general"]
theorem isIso_leftSMul_quotient
    (hj : IsEquivalenceRelation (actionPreRelation G X).target (actionPreRelation G X).source)
    (hR : Presheaf.IsSheaf (BigFppfOver.topology site S hS) (G ⊗ X).left)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology site S hS) X.left) :
    IsIso (ModObj.leftSMul (groupOverQuotient hB G X) (sourceOverQuotient G X)) := by
  have hpb : IsPullback (pullback.snd G.hom X.hom) γ[G, X].left
      (toQuotientSheaf (actionPreRelation G X)) (toQuotientSheaf (actionPreRelation G X)) := by
    have h := isPullback_toQuotientSheaf (actionPreRelation G X) hj hR hU
    rwa [actionPreRelation_source, actionPreRelation_target] at h
  rw [ModObj.isIso_leftSMul_iff]
  intro T x y
  have hinj : ∀ m m' : T ⟶ groupOverQuotient hB G X, m • x = m' • x → m = m' := by
    intro m m' h
    apply Over.OverMorphism.ext
    refine pullback.hom_ext ?_ ((Over.w m).trans (Over.w m').symm)
    rw [← lift_point_left_fst hB G X m x, ← lift_point_left_fst hB G X m' x]
    congr 1
    refine hpb.hom_ext ?_ ?_
    · rw [lift_point_left_snd, lift_point_left_snd]
    · rw [← smul_left_eq, ← smul_left_eq, h]
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : T.left ⟶ (G ⊗ X).left,
      l ≫ pullback.snd G.hom X.hom = x.left ∧ l ≫ γ[G, X].left = y.left :=
    ⟨hpb.lift x.left y.left ((Over.w x).trans (Over.w y).symm), hpb.lift_fst .., hpb.lift_snd ..⟩
  have hm : (l ≫ pullback.fst G.hom X.hom) ≫ G.hom =
      T.hom ≫ actionQuotientToBase hB G X := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hl₁,
      ← toQuotientSheaf_quotientSheafToBase hB (actionPreRelation G X), ← Category.assoc]
    exact congrArg (fun k => k ≫ actionQuotientToBase hB G X) (Over.w x)
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : T ⟶ groupOverQuotient hB G X,
      m₀.left ≫ pullback.fst G.hom (actionQuotientToBase hB G X) =
        l ≫ pullback.fst G.hom X.hom :=
    ⟨Over.homMk (pullback.lift (l ≫ pullback.fst G.hom X.hom) T.hom hm) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  have hgoal : m₀ • x = y := by
    apply Over.OverMorphism.ext
    rw [smul_left_eq,
      show (lift (groupPointOverBase hB G X m₀) (sourcePointOverBase hB G X x)).left = l from
        pullback.hom_ext (by rw [lift_point_left_fst, hm₀]) (by rw [lift_point_left_snd, hl₁]),
      hl₂]
  exact ⟨m₀, hgoal, fun m' hm' => hinj m' m₀ (hm'.trans hgoal.symm)⟩

end Quotient


/-! ### `X` is an fppf `G`-torsor over `X/G` -/

/-- **Stacks 06PH.** For a free action of a group algebraic space which is flat and locally of
finite presentation over the base, `X` is an fppf torsor over `X/G` under the group `G` pulled
back to `X/G`.

The pseudo-torsor condition is `AlgebraicGeometry.Space.isIso_leftSMul_quotient`, which is the
identification `G ×_B X = X ×_{X/G} X` of Stacks 06PG; the trivializing family is the single
morphism `X ⟶ X/G`, an fppf covering by the surjectivity, flatness and local finite
presentation already proved, and the section over it is the diagonal. -/
@[sga "3 IV 5.1.6" "(iv) ⇒ (i)", sga "6 IX 4.1" "more general"]
theorem isFppfTorsor_actionQuotientSheaf_of_quotientBootstrap
    (h04S6 : QuotientBootstrap site S hS)
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsFppfTorsor site S hS (actionQuotientPresheaf G X)
      (isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap h04S6 hB G X hG hX hfree hflat hfp)
      (groupOverQuotient hB.isSheaf G X) (sourceOverQuotient G X)
      (isAlgebraicSpace_pullback site S hS G.hom (actionQuotientToBase hB.isSheaf G X) hG
        (isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap h04S6 hB G X hG hX hfree hflat
          hfp) hB)
      hX := by
  have hQ :=
    isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap h04S6 hB G X hG hX hfree hflat hfp
  refine ⟨isIso_leftSMul_quotient hB.isSheaf G X
      (isEquivalenceRelation_actionPreRelation G X hfree)
      (isAlgebraicSpace_pullback site S hS G.hom X.hom hG hX hB).isSheaf hX.isSheaf,
    PUnit.{u + 2}, fun _ => X.left, fun _ => toQuotientSheaf (actionPreRelation G X),
    fun _ => hX, ?_, fun _ => ⟨quotientDiagonalSection (actionPreRelation G X)⟩⟩
  exact isFppfCovering_toQuotientSheaf (actionPreRelation G X) hQ hX
    (isFlat_toActionQuotientSheaf_of_quotientBootstrap h04S6 hB G X hG hX hfree hflat hfp)
    (isLocallyOfFinitePresentation_toActionQuotientSheaf_of_quotientBootstrap h04S6 hB G X hG hX
      hfree hflat hfp)

end AlgebraicGeometry.Space

end
