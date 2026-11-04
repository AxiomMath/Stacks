module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat

/-!
# Tag 0GM7 and Tag 0GM8 at the structure sheaf

`Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_tensorUnit`
proves Tag 0GM7 at an object `K ∈ D(𝒪_Y)` which is a unit for the derived tensor product and
whose derived pullback is a unit on `X`, and it takes that unit structure as five explicit
hypotheses: the two unitors `uY`, `uX`, their naturality `huY`, `huX`, and the right-unitor
coherence `hcoh` of the comparison of Tag 079U.  None of the five is a hypothesis of the
statement of Tag 0GM7 — they are steps of the *construction* of the map of Tag 08I3, carried
because that theorem is an instance of a transpose construction stated over two arbitrary
categories, where there is nothing to prove them from.

This file supplies all five at `K = 𝒪_Y[0]` and so proves Tag 0GM7, and with it the stalk map
of Tag 0GM8, at the structure sheaf.  The structure sheaf is both perfect and
pseudo-coherent, so this is the common base instance of all three clauses of Tag 0GM7 and of
both cases of Tag 0GM8, and it needs neither flatness of `h`, nor finite tor dimension, nor any
bound on `M`.

Two of the five were data rather than propositions, which is why they could not be discharged
where they are carried: `uY` and `uX` have to be *constructed*, and there is nothing to construct
them from until `K` is pinned to the unit.  Pinning it is no loss, since the unit case is the only
case that theorem is about.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.rightUnitorAtUnit`: the `uY` datum, the right
  unit constraint `W ⊗^𝐋_{𝒪_Z} 𝒪_Z[0] ≅ W` at the derived tensor product the derived internal
  hom is stated at.
* `Stacks.Cohomology.DerivedInternalHomPullback.rightUnitorAtPullbackUnit`: the `uX` datum, the
  same constraint on `X` against `Lh^*(𝒪_Y[0])` rather than `𝒪_X[0]`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.rightUnitorAtUnit_naturality` and
  `...rightUnitorAtPullbackUnit_naturality`: `huY` and `huX`, discharged.
* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackTensorIso_rightUnitor_coherence`:
  `hcoh`, discharged.
* `Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_singleUnit`:
  **Tag 0GM7 at `K = 𝒪_Y[0]`, with no hypothesis.**
* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMap_singleUnit`:
  the stalk map of Tag 0GM8 at `K = 𝒪_X[0]`, at every stalk presentation of the point.

## Which right unitor, and why the choice is forced

The repository carries **two** right unit constraints for `⊗^𝐋_{𝒪_Z}` with no identification
between them proved anywhere:
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso` (pointwise, read on a ringed
space as `Stacks.RingedSpace.derivedTensorRightUnitIso`) and `…rightUnitorNatIso` (natural, read
as `Stacks.RingedSpace.derivedTensorRightUnitorNatIso`).  Everything below is built from the
**natural** one.

That is forced rather than chosen, and it is worth saying that the hypotheses discharged here did
not have to be restated to make it so.  `uY` and `uX` are data binders of
`isIso_derivedPullbackSheafHomMap_of_tensorUnit`, and `huY`, `huX`, `hcoh` are propositions
*about those binders*; so the theorem is stated at no unitor in particular, and instantiating the
binders at the natural one is an instantiation and not a restatement.  The natural one is the only
possible instantiation: `hcoh` is
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_unitObject`, whose chain
consumes the naturality of the unitor on both `X` and on `Y` — which the pointwise isomorphism
does not carry — and whose evaluation at an image `Q K` exists only for the natural one.  A
consumer holding `rightUnitIso` cannot use anything below until that identification is proved; it
is not proved here.

## Implementation notes

*Everything here is a transport along `tensorBridge`.*  The three propositions are proved at the
derived tensor product of Tag 079U — `huY` and `huX` by
`Stacks.RingedSpace.derivedTensorRightUnitor_naturality`, `hcoh` by
`rightUnitorCoherence_unitObject` — and the binders they have to fill are at the derived tensor
product the derived internal hom is stated at.  `tensorBridge` identifies the two, and the
transport is formal: each of the three proofs is the naturality of `tensorBridge` at the
morphism in question, followed by the statement at the other tensor product.  `hcoh` is the one
case where the bridge does not merely commute past but cancels: the comparison
`pullbackTensorIso` of Tag 079U *is* the Tag 079U comparison conjugated by `tensorBridge` on each
side, and the copy of `tensorBridge` on the `X` side of it meets the copy inside `uX` and
cancels, which is why `hcoh` reduces to `rightUnitorCoherence_unitObject` and to nothing else.

*`uX` is the unitor against `Lh^*(𝒪_Y[0])`, not against `𝒪_X[0]`.*  That is what the binder asks
for, and the difference is absorbed by the unit comparison `ν : Lh^*(𝒪_Y[0]) ≅ 𝒪_X[0]` which
`rightUnitorAtPullbackUnit` tensors in.  `ν` is
`Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso` and *not*
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`.  The two have the same type and
are different terms, built along different routes — the first from the comparison
`Lh^*(QM) ⟶ Q(h^*M)` at the K-flat complex `𝒪_Y[0]` together with the lax unit of the monoidal
lift of `h^*` to complexes, the second from the flat-single derived pullback
`Lh^*(F[0]) ≅ (h^*F)[0]` together with the ordinary comparison of Tag 01CD — and the repository
proves no identification between them.  The first is the one forced here, because
`rightUnitorCoherence_unitObject` is stated with it.

*The `Abelian` instance has to be named.*  `Abelian (RingedSpace.KFlatDerivedPullback.Modules Z)`
is synthesizable from the import closure of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk` alone, and it stops
being synthesizable once
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence` enters
that closure, which it does here by way of `ProjectionFormulaUnitKFlat`.  Registering
`Stacks.Cohomology.DerivedPullbackTensor.abelianModulesSheafTensor` as a local instance — the
same declaration, and the same underlying `SheafOfModules.instAbelian`, that
`PullbackTensorComplexCoherence` and `ProjectionFormulaUnitKFlat` register for themselves —
restores it, and the objects of the two import branches then agree: the imported
`internalHomTensorUncurried` and the imported `singleUnit` compose in one expression.  This is
also why these statements are not in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility`:
that module is imported by several others, and adding the `ProjectionFormulaUnitKFlat` import to
it would carry the same breakage into each of them.

*No step of any proof below is carried out at the concrete objects, and no heartbeat budget is
raised.*  Each of the three proofs is one generic lemma — `paste_two`, `paste_three`,
`coherence_paste` — applied by unification, fed the two or three concrete equations it pastes
together.  That is not stylistic.  Written inline, each proof is a chain of reassociations, and
`rw [Category.assoc]` has to match `(?f ≫ ?g) ≫ ?h` against objects of the derived category of
module sheaves on a ringed space, which exhausts the default budget three times
over, once inside `whnf` and twice inside `isDefEq`.
Inside the generic lemmas every object is a variable, so the same reassociations are free, and the
only cost left at the concrete terms is the one unification of each lemma's conclusion against the
goal.  `map_prod_comm` — the interchange of a morphism in the first slot of a bifunctor on pairs
with one in the second — is generic for the same reason, recorded throughout this directory: its
proof is `Functor.map_comp`, and matching `?F.map (?a ≫ ?b)` against the uncurried derived tensor
product of a ringed space is the step that fails.

*The `rfl` component lemmas, and why the spellings are uniform.*  `rightUnitorAtUnit_hom`,
`rightUnitorAtPullbackUnit_hom` and `pullbackTensorIso_hom_app` write out the components of the
two unitors and of the Tag 079U comparison; all three are `rfl`, and they exist so that the
proofs can proceed by `rw` on rigid terms instead of `dsimp`-ing through the `Iso.trans`,
`Functor.mapIso` and whiskering projections.  All three are stated in the `α.hom.app` and
`α.inv.app` spellings rather than `(α.app _).hom` and `(α.app _).inv`, which are the same terms:
that is what lets the naturality of `tensorBridge` and `Iso.hom_inv_id_app` be handed to the
generic lemmas directly, with no `Iso` projection left to be matched.  For the same reason
`coherence_paste` takes an isomorphism as a pair of morphisms with `p ≫ q = 𝟙` rather than as an
`Iso`.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0GM5](https://stacks.math.columbia.edu/tag/0GM5)
* [Stacks Project, Tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit pullbackTensorComparison
  derivedPullbackUnitIso rightUnitorCoherence_unitObject)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedInternalHomPullback

attribute [local instance] HasDerivedCategory.standard

-- See the implementation notes: `Abelian (RingedSpace.KFlatDerivedPullback.Modules Z)` is not
-- synthesizable once `PullbackTensorComplexCoherence` is in the import closure, and this is the
-- declaration that file and `ProjectionFormulaUnitKFlat` register for themselves.
open Stacks.Cohomology.DerivedPullbackTensor in
attribute [local instance] abelianModulesSheafTensor

-- The derived pullback and the derived internal hom name the structure sheaf of a ringed space
-- differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`; the two are the same sheaf of rings by `rfl`, and
-- the statements below mix them.  `structureSheafRing` is `@[instance_reducible]`, so it is
-- already unfolded both by instance search and at `implicit` transparency, but its reduct stops
-- at an explicit-constructor projection while `Tensor.ringSheaf Z.sheaf` reduces to
-- `(sheafCompose _ _).obj Z.sheaf`; the last two Mathlib definitions are the gap between them,
-- and they are the list `…DerivedPushforward.InternalHomPullbackInvertibility` carries for the
-- statements this file applies.
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **Interchange of the two slots of a bifunctor on pairs:** a morphism in the first slot
followed by one in the second is the other order, both being the image of the pair.

Stated over three arbitrary categories, and applied by unification.  Its proof is
`Functor.map_comp`, and at the concrete bifunctor below — the uncurried derived tensor product of
a ringed space — matching the pattern `?F.map (?a ≫ ?b)` exhausts the elaborator's budget inside
`isDefEq`; against this lemma's rigid left-hand side the same step is immediate. -/
private lemma map_prod_comm {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {A A' : C} {B B' : D} (a : A ⟶ A') (b : B ⟶ B') :
    F.map ((a ×ₘ 𝟙 B) : ((A, B) : C × D) ⟶ (A', B)) ≫ F.map (𝟙 A' ×ₘ b) =
      F.map ((𝟙 A ×ₘ b) : ((A, B) : C × D) ⟶ (A, B')) ≫ F.map (a ×ₘ 𝟙 B') := by
  rw [← F.map_comp, ← F.map_comp, prod_comp, prod_comp, Category.id_comp, Category.comp_id,
    Category.id_comp, Category.comp_id]

/-- **Two commuting squares pasted along their shared edge**: if `a ≫ b' = b ≫ c` and
`c ≫ r' = r ≫ g` then `a ≫ b' ≫ r' = (b ≫ r) ≫ g`. -/
lemma paste_two {C : Type*} [Category C] {P P' Q Q' W W' : C}
    (a : P ⟶ P') (b : P ⟶ Q) (b' : P' ⟶ Q') (c : Q ⟶ Q')
    (r : Q ⟶ W) (r' : Q' ⟶ W') (g : W ⟶ W')
    (h₁ : a ≫ b' = b ≫ c) (h₂ : c ≫ r' = r ≫ g) :
    a ≫ b' ≫ r' = (b ≫ r) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **Three commuting squares pasted along their shared edges.**  `paste_two` with one more
square in the middle, which is what the naturality against the pullback of the unit needs: the
morphism has to be moved past the unit comparison before it meets the unitor.  Generic and
applied by unification, for the reason given on `paste_two`. -/
private lemma paste_three {C : Type*} [Category C] {P P' Q Q' R R' W W' : C}
    (a : P ⟶ P') (b : P ⟶ Q) (b' : P' ⟶ Q') (c : Q ⟶ Q') (n : Q ⟶ R) (n' : Q' ⟶ R')
    (d : R ⟶ R') (r : R ⟶ W) (r' : R' ⟶ W') (g : W ⟶ W')
    (h₁ : a ≫ b' = b ≫ c) (h₂ : c ≫ n' = n ≫ d) (h₃ : d ≫ r' = r ≫ g) :
    a ≫ b' ≫ n' ≫ r' = (b ≫ n ≫ r) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc c, h₂, Category.assoc n, h₃]
  simp only [Category.assoc]

/-- **A coherence triangle read after an isomorphism that cancels against its own inverse.**  The
shape of the unitor coherence below: a comparison conjugated by an isomorphism `p` meets the
inverse `q` of that same isomorphism coming out of the unitor, the two cancel, and what is left
is the coherence `hyp` under the functor.

Generic, with the functor and every object and morphism a variable, and applied by unification.
The isomorphism is taken as the two morphisms `p`, `q` together with `hpq : p ≫ q = 𝟙` rather
than as an `Iso`, so that nothing here has to be matched against an `Iso` projection: at the
concrete terms the two sides arrive in the `α.hom.app` and `α.inv.app` spellings, and
`Iso.hom_inv_id_app` supplies `hpq` in exactly those.

*The three factors enter as the equations `h₁`, `h₂`, `h₃` rather than in expanded form, and that
is the point of this lemma's shape.*  The three are `rfl`, so the caller could instead rewrite
with them and leave this lemma stated at the expanded composite — and that does not work.  Each
such `rw` has to abstract a motive over an object of the derived category of module sheaves on a
ringed space, and two successive measurements showed the cost is in the abstraction and not in
the pattern: with the expansions un-applied the budget was exhausted on the second of them, and
with all three applied at their arguments it was exhausted on the *third*, a different one from
before, whichever happened to run against the largest goal.  Taking them as hypotheses moves
every rewrite inside this lemma, where the objects are variables and all of it is free; the only
work left at the concrete terms is one first-order match of the conclusion against the goal,
binding `lhs₁`, `lhs₂` and `rhsMor` to three of its subterms. -/
private lemma coherence_paste {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B Wo : C} {S T U : D}
    (lhs₁ : F.obj A ⟶ T) (lhs₂ : T ⟶ F.obj Wo) (rhsMor : A ⟶ Wo)
    (x : A ⟶ B) (y : B ⟶ Wo)
    (c : F.obj B ⟶ S) (p : S ⟶ T) (q : T ⟶ S) (n : S ⟶ U) (r : U ⟶ F.obj Wo)
    (h₁ : lhs₁ = F.map x ≫ c ≫ p) (h₂ : lhs₂ = q ≫ n ≫ r) (h₃ : rhsMor = x ≫ y)
    (hpq : p ≫ q = 𝟙 S) (hyp : c ≫ n ≫ r = F.map y) :
    lhs₁ ≫ lhs₂ = F.map rhsMor := by
  rw [h₁, h₂, h₃, F.map_comp, ← hyp]
  simp only [Category.assoc]
  rw [← Category.assoc p, hpq, Category.id_comp]

/-! ### The right unitor at the unit, on one space -/

section Unit

variable (Z : RingedSpace.{u, u})

/-- **The right unit constraint `W ⊗^𝐋_{𝒪_Z} 𝒪_Z[0] ≅ W` at the derived tensor product the
derived internal hom is stated at.**  This is the `uY` datum of
`isIso_derivedPullbackSheafHomMap_of_tensorUnit` at `K = 𝒪_Z[0]`: the comparison `tensorBridge`
of the two derived tensor products of this repository, followed by
`Stacks.RingedSpace.derivedTensorRightUnitorNatIso`, the **natural** right unit constraint of
[Stacks, Tag 0FPT] at the other one. -/
def rightUnitorAtUnit
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (internalHomTensorUncurried Z).obj (W, singleUnit Z) ≅ W :=
  ((tensorBridge Z).app (W, singleUnit Z)).symm ≪≫
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).app W

/-- The right unit constraint written out.  True by definition; the restatement is what lets `rw`
use it below without `dsimp`-ing through the `Iso.trans` projections. -/
private lemma rightUnitorAtUnit_hom
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (rightUnitorAtUnit Z W).hom =
      (tensorBridge Z).inv.app (W, singleUnit Z) ≫
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).app W).hom := rfl

/-- **Naturality of the right unit constraint at the unit**: the `huY` hypothesis of
`isIso_derivedPullbackSheafHomMap_of_tensorUnit`, discharged at `K = 𝒪_Z[0]`. -/
theorem rightUnitorAtUnit_naturality
    (W W' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    (g : W ⟶ W') :
    (internalHomTensorUncurried Z).map (g ×ₘ 𝟙 (singleUnit Z)) ≫
        (rightUnitorAtUnit Z W').hom =
      (rightUnitorAtUnit Z W).hom ≫ g := by
  exact paste_two _ _ _ _ _ _ g ((tensorBridge Z).inv.naturality _)
    (Stacks.RingedSpace.derivedTensorRightUnitor_naturality Z g)

end Unit

/-! ### The right unitor against the pullback of the unit -/

section Pullback

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **The right unit constraint `W ⊗^𝐋_{𝒪_X} Lh^*(𝒪_Y[0]) ≅ W`.**  This is the `uX` datum of
`isIso_derivedPullbackSheafHomMap_of_tensorUnit` at `K = 𝒪_Y[0]`: the tensor factor is the
derived pullback of the unit of `Y` rather than the unit of `X`, and the difference is absorbed
by the unit comparison `ν : Lh^*(𝒪_Y[0]) ≅ 𝒪_X[0]`.

`ν` is `Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso`, the one the
right-unitor coherence of [Stacks, Tag 079U] is proved with; see the implementation notes on why
the other isomorphism of that type cannot be used instead. -/
def rightUnitorAtPullbackUnit
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) :
    (internalHomTensorUncurried X).obj
        (W, (derivedPullbackFunctor h).obj (singleUnit Y)) ≅ W :=
  ((tensorBridge X).app (W, (derivedPullbackFunctor h).obj (singleUnit Y))).symm ≪≫
    (pullbackTensorUncurried X).mapIso
        (Iso.prod (Iso.refl W) (derivedPullbackUnitIso h)) ≪≫
      (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app W

/-- The constraint against the pullback of the unit, written out.  True by definition. -/
private lemma rightUnitorAtPullbackUnit_hom
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) :
    (rightUnitorAtPullbackUnit h W).hom =
      (tensorBridge X).inv.app (W, (derivedPullbackFunctor h).obj (singleUnit Y)) ≫
        (pullbackTensorUncurried X).map (𝟙 W ×ₘ (derivedPullbackUnitIso h).hom) ≫
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app W).hom := rfl

/-- **Naturality of the right unit constraint against the pullback of the unit**: the `huX`
hypothesis of `isIso_derivedPullbackSheafHomMap_of_tensorUnit`, discharged at `K = 𝒪_Y[0]`. -/
theorem rightUnitorAtPullbackUnit_naturality
    (W W' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (g : W ⟶ W') :
    (internalHomTensorUncurried X).map
          (g ×ₘ 𝟙 ((derivedPullbackFunctor h).obj (singleUnit Y))) ≫
        (rightUnitorAtPullbackUnit h W').hom =
      (rightUnitorAtPullbackUnit h W).hom ≫ g := by
  exact paste_three _ _ _ _ _ _ _ _ _ g ((tensorBridge X).inv.naturality _)
    (map_prod_comm (pullbackTensorUncurried X) g (derivedPullbackUnitIso h).hom)
    (Stacks.RingedSpace.derivedTensorRightUnitor_naturality X g)

/-- The comparison of [Stacks, Tag 079U], transported to the derived tensor product the derived
internal hom is stated at, written out at a pair: the derived pullback of `tensorBridge` on the
source, the untransported comparison, and `tensorBridge` on the target.  True by definition. -/
private lemma pullbackTensorIso_hom_app
    (A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (pullbackTensorIso h).hom.app (A, B) =
      (derivedPullbackFunctor h).map ((tensorBridge Y).inv.app (A, B)) ≫
        (pullbackTensorComparison h).app (A, B) ≫
          (tensorBridge X).hom.app
            ((derivedPullbackFunctor h).obj A, (derivedPullbackFunctor h).obj B) :=
  rfl

/-- **The right-unitor coherence of the transported comparison of [Stacks, Tag 079U]**: the
`hcoh` hypothesis of `isIso_derivedPullbackSheafHomMap_of_tensorUnit`, discharged at
`K = 𝒪_Y[0]`.  For every `W ∈ D(𝒪_Y)` the comparison

`Lh^*(W ⊗^𝐋_{𝒪_Y} 𝒪_Y[0]) ⟶ Lh^*W ⊗^𝐋_{𝒪_X} Lh^*(𝒪_Y[0])`

followed by the unit constraint on `X` is the derived pullback of the unit constraint on `Y`. -/
theorem pullbackTensorIso_rightUnitor_coherence
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (pullbackTensorIso h).hom.app (W, singleUnit Y) ≫
        (rightUnitorAtPullbackUnit h ((derivedPullbackFunctor h).obj W)).hom =
      (derivedPullbackFunctor h).map (rightUnitorAtUnit Y W).hom :=
  coherence_paste (derivedPullbackFunctor h) _ _ _ _ _ _ _ _ _ _
    (pullbackTensorIso_hom_app h W (singleUnit Y))
    (rightUnitorAtPullbackUnit_hom h ((derivedPullbackFunctor h).obj W))
    (rightUnitorAtUnit_hom Y W) ((tensorBridge X).hom_inv_id_app _)
    (rightUnitorCoherence_unitObject h W)

/-! ### Tag 0GM7 at the structure sheaf -/

/-- **Tag 0GM7 at `K = 𝒪_Y[0]`, with no hypothesis.**  Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be an
arbitrary morphism of ringed spaces and let `M ∈ D(𝒪_Y)` be arbitrary.  Then the canonical map

`Lh^*R𝓗om_{𝒪_Y}(𝒪_Y[0], M) ⟶ R𝓗om_{𝒪_X}(Lh^*(𝒪_Y[0]), Lh^*M)`

of Tag 08I3 is an isomorphism.

The structure sheaf is both perfect and pseudo-coherent, so this is the common base instance of
all three clauses of the source, and it needs neither flatness of `h`, nor finite tor dimension,
nor any bound on `M`.  The case of a general perfect `K` is
`Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect`. -/
theorem isIso_derivedPullbackSheafHomMap_singleUnit
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso (derivedPullbackSheafHomMap h (singleUnit Y) M) :=
  isIso_derivedPullbackSheafHomMap_of_tensorUnit h (singleUnit Y)
    (rightUnitorAtUnit Y) (rightUnitorAtPullbackUnit h)
    (rightUnitorAtUnit_naturality Y) (rightUnitorAtPullbackUnit_naturality h)
    (pullbackTensorIso_rightUnitor_coherence h) M

end Pullback

end Stacks.Cohomology.DerivedInternalHomPullback

/-! ### Tag 0GM8 at the structure sheaf -/

namespace Stacks.Cohomology.DerivedInternalHomStalk

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedPullbackTensor in
attribute [local instance] abelianModulesSheafTensor

-- The same two spellings of the structure sheaf as in the namespace above, and the same two
-- Mathlib definitions that bridge `structureSheafRing`'s explicit-constructor reduct to the
-- `(sheafCompose _ _).obj X.sheaf` one; `…DerivedPushforward.InternalHomStalk`, whose
-- statements the theorem below applies, carries this list for the same reason.
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open Stacks.Cohomology.DerivedInternalHomPullback

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

/-- At `K = 𝒪_X[0]`: for a ringed space `X`, a stalk presentation `P` of a point `x` of `X` and
an arbitrary `M ∈ D(𝒪_X)`, the displayed map

`R𝓗om_{𝒪_X}(𝒪_X[0], M)_x ⟶ RHom_{𝒪_{X,x}}((𝒪_X[0])_x, M_x)`

is an isomorphism. -/
theorem isIso_stalkSheafHomMap_singleUnit (P : StalkPresentation X x)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) :
    IsIso (stalkSheafHomMap X x P (singleUnit X) M) :=
  (isIso_stalkSheafHomMap_iff X x P (singleUnit X) M).2
    (isIso_derivedPullbackSheafHomMap_singleUnit P.hom M)

end Stacks.Cohomology.DerivedInternalHomStalk

end
