module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescentBridgeOverlap
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssSurjCanonicalPullbackData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssSurjInterSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsUnconditionalStageIso

/-!
# The comparison isomorphism over the intersection, on the system of base changes of a square

`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean` is the
elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ, and the
pair it takes as input is a comparison isomorphism `c` of the two descended objects over the
intersection, at a stage, together with the equation `hfac` saying that the hom-level map to the
limit sends `c` to the comparison of the two inductive hypotheses.

**This file produces that pair** from the colimit assertion of Stacks 09RI on the system of
intersections of the base changes of the square,
`AlgebraicGeometry.Space.edsPreimageInterLimitSystem`, read with the pullback-pseudofunctor datum
`AlgebraicGeometry.Space.canonicalPullbackData` whose composition comparison is the one the step's
`hfac` is written with.

## Main results

* `AlgebraicGeometry.Space.projHom_edsPreimageInterLimitSystem`: **the hom-level map to the limit
  of Stacks 09RI, on the system of intersections, is the conjugation by
  `AlgebraicGeometry.Space.edsBridgeInterComp` that the step's `hfac` speaks of.**  This is the
  respelling that connects the two files, and it is its own declaration so that it carries its own
  elaboration budget; see "Implementation notes".
* `AlgebraicGeometry.Space.exists_interStageIso_of_isColim`: **the pair `(c, hfac)`.**  Given the
  colimit assertion in the four orders and two isomorphisms `α`, `β` with a common target over the
  intersection at the limit, there are a stage `j` and an isomorphism `c` of the two objects
  restricted to the intersection at that stage whose image under the hom-level map is `β⁻¹ ∘ α`,
  written exactly as the step's `hfac`.
* `AlgebraicGeometry.Space.exists_interStageIso_projHom_of_isColim`: the same with the equation
  written with `CategoryTheory.PullbackData.LimitSystem.projHom` rather than with the conjugation
  written out.  It is the cheap form; see "Implementation notes".
* `AlgebraicGeometry.Space.limit_edsPreimageInterLimitSystem`,
  `…pull_toBase_edsPreimageInterLimitSystem`,
  `…pull_limitToBase_edsPreimageInterLimitSystem`: the three identities that move between the
  system's own spelling of its vertex and structure morphisms and the induced maps of
  intersections.  They are the spelling the objects and isomorphisms of
  `AlgebraicGeometry.Space.exists_interStageIso_of_isColim` are stated at, and they are what a
  consumer that has those data written out as maps of intersections uses to supply them; see
  "Implementation notes" for why the existence statement is not written out in that spelling
  directly.

## The hypotheses carried, and why each is an input rather than part of the conclusion

*The elementary distinguished square `hsq`, the morphism `p_b` and the system `T`.*  The geometry:
an elementary distinguished square over `W₀`, a base stage `W_b ⟶ W₀`, and a directed system over
`W_b` with a cone, which in Situation 09RH is the system of base changes `W₀ ×_{X₀} X_j` with
vertex `W₀ ×_{X₀} X`.  This is the data the step is run with and nothing is added to it.

*The four colimit assertions.*  `CategoryTheory.PullbackData.LimitSystem.IsColim` for the system of
intersections, in the orders `(X, Y)`, `(Y, X)`, `(X, X)` and `(Y, Y)`.  That is the conclusion of
Stacks 09RI read for this system; see "The hypotheses carried, and why each is an input rather than
part of the conclusion" in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectObjectsUnconditionalStageIso.lean` for
why all four are needed.  **No `AlgebraicGeometry.Space.DescentSituation.RingModel` appears**: the
library's Stacks 09RI for perfect objects carries one, but it is not used here, and the four
assertions are hypotheses.

*Directedness of the index.*  Needed to advance two stages to a common one.

Nothing else is assumed.  No `Prop` binder stands in for missing mathematics, the comparison
isomorphism being produced is nowhere assumed, and no clause of Stacks 09RJ, of Stacks 09RI or of
Stacks 08HB is assumed.

## What is not here

*Stacks 09RI for this system.*  The four colimit assertions are hypotheses.  What relates them to
the colimit assertion for the datum Stacks 09RI is formalized at,
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, is
`AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomUnconditionalPullbackData.lean`; it is
not used below, since the assertions are taken for the datum the square step's `hfac` is written
with.

*The composition with the square step.*  Feeding the pair below to
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` needs the two
inductive hypotheses `αU`, `αV` **at the stage `j` the pair is produced at**, whereas the induction
supplies them at the stage the descended objects were found at.  The missing step is therefore the
transport of `αU` and `αV` along a transition morphism together with the invariance of
`AlgebraicGeometry.Space.edsBridgeFst` and `…edsBridgeSnd` under that transport; neither is proved
nor assumed below.

## Implementation notes

The respelling `AlgebraicGeometry.Space.projHom_edsPreimageInterLimitSystem` is the one place where
the two spellings of the composition comparison of the maps of intersections meet: the left side is
`CategoryTheory.PullbackData.LimitSystem.projHom` for
`AlgebraicGeometry.Space.canonicalPullbackData`, which
`AlgebraicGeometry.Space.projHom_canonicalPullbackData` writes out in terms of
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`'s identification of the
factorisation of the *system's* projection, and the right side is
`AlgebraicGeometry.Space.edsBridgeInterComp`, which is that same identification with the maps of
intersections written out.  They agree by `rfl` — the system's fields are those maps, and the two
proofs of the factorisation are propositions — and the agreement is given its own declaration
rather than being inlined into the existence statement, because the composites involved are
comparisons of total left derived functors and a failed unification inside the larger statement is
the expensive one; the same discipline, and the measurements that forced it, are recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean`.

That is also why the objects, the isomorphisms `α`, `β` and the produced isomorphism `c` of
`AlgebraicGeometry.Space.exists_interStageIso_of_isColim` are written at the system's own fields —
`(edsPreimageInterLimitSystem hsq pb T).limit`, `…limitToBase`, `…toBase j` — rather than as the
induced maps of intersections.  With them written as the induced maps, assembling the existential
from the general `CategoryTheory.PullbackData.LimitSystem.exists_stageIso_of_limitIso` asks the
elaborator to unify four whole `Iso` types across the two spellings at once, and that unification
does not terminate inside the heartbeat budget: **247,182 heartbeats and a deterministic timeout at
`isDefEq`**.  Written at the fields it costs **188,589**, which fits, and the three identities
`…limit_edsPreimageInterLimitSystem`, `…pull_toBase_edsPreimageInterLimitSystem` and
`…pull_limitToBase_edsPreimageInterLimitSystem` give a consumer the crossing one piece at a time,
at 281, 1,181 and 1,178 heartbeats.

Even so, 188,589 is most of the budget, and all of it is the one remaining crossing: the equation
of the conclusion is the conjugation written out, so matching the respelling against it unifies the
two spellings of the inverse image at the stage inside a threefold composite of comparisons of
total left derived functors.  `AlgebraicGeometry.Space.exists_interStageIso_projHom_of_isColim` is
the same statement with that equation written with
`CategoryTheory.PullbackData.LimitSystem.projHom`, where no crossing arises at all and the cost is
**1,744**; a consumer that can work with the hom-level map rather than with the conjugation written
out should use that one and reach for
`AlgebraicGeometry.Space.projHom_edsPreimageInterLimitSystem` (**8,848**) only where it needs the
written-out form.  Rewriting with that respelling instead of composing with it does not help: the
two sides' proofs of the factorisation are elaborated separately, `rw` does not match, and the
declaration then exceeds the budget.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {Wb : AlgebraicSpaces B S hS} (pb : Wb ⟶ W₀)
  {J : Type w} [Preorder J]
  (T : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) Wb J)
  (X Y : derivedModules B S hS (edsInter B S hS (edsPreimage hsq pb)))

/-- **The hom-level map to the limit of Stacks 09RI, on the system of intersections of the base
changes of an elementary distinguished square, is the conjugation the square step's `hfac` speaks
of**: the derived pullback along the map of intersections induced by the projection `p_j`,
conjugated by `AlgebraicGeometry.Space.edsBridgeInterComp` — the identification of the
factorisation `r_P ≫ t_P = s_P` of the maps of intersections — at the source and at the target.

The two sides are the same morphism: the structure morphisms, transition morphisms and
projections of `AlgebraicGeometry.Space.edsPreimageInterLimitSystem` are the induced maps of
intersections, and the identification of a factorisation depends on the factorisation only through
its value. -/
theorem projHom_edsPreimageInterLimitSystem (j : J)
    (φ : ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb T).toBase j)).obj X ⟶
      ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb T).toBase j)).obj Y) :
    (edsPreimageInterLimitSystem hsq pb T).projHom (canonicalPullbackData B S hS) X Y j φ =
      ((edsBridgeInterComp hsq pb (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.toBase j) (T.proj j)
            rfl (by rw [← Category.assoc, T.proj_toBase j]) T.limitToBase
            (T.proj_toBase j).symm rfl).app X).inv ≫
        (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq (T.toBase j ≫ pb)
          (T.limitToBase ≫ pb) (T.proj j) (by rw [← Category.assoc, T.proj_toBase j]))).map φ ≫
        ((edsBridgeInterComp hsq pb (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.toBase j)
          (T.proj j) rfl (by rw [← Category.assoc, T.proj_toBase j]) T.limitToBase
          (T.proj_toBase j).symm rfl).app Y).hom :=
  projHom_canonicalPullbackData (edsPreimageInterLimitSystem hsq pb T) X Y j φ

/-- The vertex of the system of intersections is the intersection of the square over the vertex of
the given system. -/
theorem limit_edsPreimageInterLimitSystem :
    (edsPreimageInterLimitSystem hsq pb T).limit =
      edsInter B S hS (edsPreimage hsq (T.limitToBase ≫ pb)) :=
  rfl

/-- The inverse image along the structure morphism of the stage `j` of the system of intersections
is the derived pullback along the map of intersections induced by `k_j`. -/
theorem pull_toBase_edsPreimageInterLimitSystem (j : J) :
    (canonicalPullbackData B S hS).pull ((edsPreimageInterLimitSystem hsq pb T).toBase j) =
      smallEtaleDerivedModulePullback B S hS
        (edsPreimageInterMap hsq pb (T.toBase j ≫ pb) (T.toBase j) rfl) :=
  rfl

/-- The inverse image along the structure morphism of the vertex of the system of intersections is
the derived pullback along the map of intersections induced by the structure morphism of the
vertex. -/
theorem pull_limitToBase_edsPreimageInterLimitSystem :
    (canonicalPullbackData B S hS).pull (edsPreimageInterLimitSystem hsq pb T).limitToBase =
      smallEtaleDerivedModulePullback B S hS
        (edsPreimageInterMap hsq pb (T.limitToBase ≫ pb) T.limitToBase rfl) :=
  rfl

/-- **The comparison isomorphism over the intersection, with its compatibility stated by the
hom-level map itself.**  This is
`AlgebraicGeometry.Space.exists_interStageIso_of_isColim` with its conclusion written with
`CategoryTheory.PullbackData.LimitSystem.projHom` instead of the conjugation by
`AlgebraicGeometry.Space.edsBridgeInterComp`;
`AlgebraicGeometry.Space.projHom_edsPreimageInterLimitSystem` turns either into the other. -/
theorem exists_interStageIso_projHom_of_isColim [IsDirected J (· ≤ ·)]
    (hXY : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) X Y)
    (hYX : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) Y X)
    (hXX : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) X X)
    (hYY : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) Y Y)
    (E : derivedModules B S hS (edsPreimageInterLimitSystem hsq pb T).limit)
    (α : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb T).limitToBase).obj X ≅ E)
    (β : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb T).limitToBase).obj Y ≅ E) :
    ∃ (j : J) (c : ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb T).toBase j)).obj X ≅
      ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb T).toBase j)).obj Y),
      (edsPreimageInterLimitSystem hsq pb T).projHom (canonicalPullbackData B S hS) X Y j c.hom =
        α.hom ≫ β.inv :=
  PullbackData.LimitSystem.exists_stageIso_of_limitIso hXY hYX hXX hYY E α β

/-- **The comparison isomorphism `c` over the intersection, and its compatibility `hfac`, for the
elementary-distinguished-square step of Stacks 09RJ.**  Let `(U₀ ⊆ W₀, V₀ ⟶ W₀)` be an elementary
distinguished square, let `p_b : W_b ⟶ W₀` be a morphism and let `T` be a directed system over
`W_b` with a cone.  Let `X` and `Y` be objects of `D(𝒪_{P_b})` on the intersection of the square
over `W_b` whose systems of morphism sets along the system of intersections have the colimit
property of Stacks 09RI in the four orders, and let `α : Ls_P^*X ≅ E` and `β : Ls_P^*Y ≅ E` be
isomorphisms with a common object `E` of `D(𝒪_{P'})` on the intersection of the square over the
vertex.  Then there are a stage `j` and an isomorphism
`c : Lt_P^*X ≅ Lt_P^*Y` of `D(𝒪_{P_j})` whose conjugate by
`AlgebraicGeometry.Space.edsBridgeInterComp` is `β⁻¹ ∘ α`.

This is exactly the pair `(c, hfac)` that
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` takes as input,
with `X` read as `A_b|_{P_b}`, `Y` as `Bo_b|_{P_b}`, `E` as the restriction of the perfect object
being descended, and `α`, `β` as the two isomorphisms built from the inductive hypotheses;
see "What is not here" in this file's module documentation for what still separates the two. -/
theorem exists_interStageIso_of_isColim [IsDirected J (· ≤ ·)]
    (hXY : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) X Y)
    (hYX : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) Y X)
    (hXX : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) X X)
    (hYY : (edsPreimageInterLimitSystem hsq pb T).IsColim (canonicalPullbackData B S hS) Y Y)
    (E : derivedModules B S hS (edsPreimageInterLimitSystem hsq pb T).limit)
    (α : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb T).limitToBase).obj X ≅ E)
    (β : ((canonicalPullbackData B S hS).pull
        (edsPreimageInterLimitSystem hsq pb T).limitToBase).obj Y ≅ E) :
    ∃ (j : J) (c : ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb T).toBase j)).obj X ≅
      ((canonicalPullbackData B S hS).pull
        ((edsPreimageInterLimitSystem hsq pb T).toBase j)).obj Y),
      ((edsBridgeInterComp hsq pb (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.toBase j) (T.proj j)
            rfl (by rw [← Category.assoc, T.proj_toBase j]) T.limitToBase
            (T.proj_toBase j).symm rfl).app X).inv ≫
          (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq (T.toBase j ≫ pb)
            (T.limitToBase ≫ pb) (T.proj j) (by rw [← Category.assoc, T.proj_toBase j]))).map
            c.hom ≫
          ((edsBridgeInterComp hsq pb (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.toBase j)
            (T.proj j) rfl (by rw [← Category.assoc, T.proj_toBase j]) T.limitToBase
            (T.proj_toBase j).symm rfl).app Y).hom =
        α.hom ≫ β.inv := by
  obtain ⟨j, c, hc⟩ :=
    PullbackData.LimitSystem.exists_stageIso_of_limitIso hXY hYX hXX hYY E α β
  exact ⟨j, c, (projHom_edsPreimageInterLimitSystem hsq pb T X Y j c.hom).symm.trans hc⟩

end AlgebraicGeometry.Space

end
