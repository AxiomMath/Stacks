module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomComp
import StacksCore.Tactic.StacksAttribute

/-!
# Compatibility of the canonical internal Hom map with composition

Let `φ : X ⟶ Y` and `ψ : Y ⟶ Z` be morphisms of ringed topoi presented by ringed sites.
The canonical map of Stacks 0GMX for their composite is the canonical map for `ψ`, pulled
back along `φ`, followed by the canonical map for `φ`, with the source and target identified
by the canonical comparison of pullbacks.

## Main results

* `Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_comp`: compatibility
  of the canonical map with composition.
* `Stacks.SheafOfModules.InternalHom.toposPullbackEvaluationExchange`: the categorical
  reassociation used to assemble the evaluation identity.
* `Stacks.SheafOfModules.InternalHom.toposPullbackCompComparison` and its inverse:
  the comparison components written with iterated pullbacks.

The proof tensors both sides with the pulled-back first argument and evaluates. Naturality
of the comparison and the composition law for the inverse tensor comparison identify the
two resulting maps. Injectivity of tensor-evaluation then gives the desired equality.

## Implementation notes

The tensor-coherence identity is proved at arbitrary module arguments before it is applied
to an internal Hom. Its comparison component is stated at the curried tensor object, matching
the evaluation identity. This avoids unfolding a nested internal Hom while comparing the
curried and uncurried presentations of the tensor product. All comparisons are the existing
canonical isomorphisms; no new module structures or equality transports are introduced.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.SheafOfModules.InternalHom

universe u

section AbstractExchange

variable {D : Type*} [Category* D]

/-- **Cancelling an invertible factor in front of a composite that begins with its inverse.**
From `f ≫ g = 𝟙 a` and a presentation `w = g ≫ k` of a morphism out of the codomain of `f`,
conclude `f ≫ w = k`.

This is the step that turns the composition law of Stacks 03EL, which is stated with the
*inverse* comparison of pullbacks on both sides, into a formula for the comparison of the
composite alone. Stated abstractly on purpose: `h₁` and `hw` are supplied by two declarations
whose statements spell the tensor product of sheaves of modules as the bifunctor of Stacks 03EL,
while the goal spells it with the curried tensor product of Stacks 0GMW, and in an abstract
category each of the two crossings is a single object comparison at an explicit argument, which
is free. Fed to `rw` or asked for inside a hand-written mixed statement the same crossings cost
more than the elaborator's whole budget. -/
theorem cancelWhisker {a b c : D} {f : a ⟶ b} {g : b ⟶ a} (h₁ : f ≫ g = 𝟙 a)
    {k : a ⟶ c} {w : b ⟶ c} (hw : w = g ≫ k) : f ≫ w = k := by
  rw [hw, ← Category.assoc, h₁, Category.id_comp]

/-- **The abstract shape of the composition law for the canonical map of Stacks 0GMX.**

Read `P₁ ≫ P₂ ≫ P₃` as the composite route's three tensorings — the comparison of pullbacks in
the first variable, the pullback of the inner canonical map, and the comparison of pullbacks in
the second variable — `t ≫ m` as that same composite with the two comparisons of pullbacks
collected into one action of the tensor bifunctor of Stacks 03EL, `ev` as the pulled-back
evaluation morphism, `u ≫ v₀` as the comparison of Stacks 03EL followed by the pullback of the
inner evaluation, `x` and `κ` as the comparison of pullbacks at the target and at the tensor
product, `ξ` as the evaluation pulled back along the composite and `Λ` as the comparison of
Stacks 03EL for the composite. The hypotheses are then, in order: the exchange of the two
tensorings; the pulled-back evaluation of a tensor--evaluation composite; the naturality of the
comparison of pullbacks past the comparison of Stacks 03EL; and the composition law of
Stacks 03EL with the comparison of pullbacks cancelled off. -/
theorem toposPullbackEvaluationExchange {o₀ o₁ o₂ o₃ o₄ o₅ q k l h : D}
    {P₁ : o₀ ⟶ o₁} {P₂ : o₁ ⟶ o₂} {P₃ : o₂ ⟶ o₃} {ev : o₃ ⟶ o₄} {x : o₄ ⟶ o₅}
    {t : o₀ ⟶ q} {m : q ⟶ o₃} {u : q ⟶ k} {v₀ : k ⟶ o₄} {v₁ : k ⟶ l}
    {κ : l ⟶ h} {ξ : h ⟶ o₅} {Λ : o₀ ⟶ h}
    (hP : P₁ ≫ P₂ ≫ P₃ = t ≫ m) (hm : m ≫ ev = u ≫ v₀) (hvx : v₀ ≫ x = v₁ ≫ κ ≫ ξ)
    (hkey : t ≫ u ≫ v₁ ≫ κ = Λ) :
    P₁ ≫ P₂ ≫ P₃ ≫ ev ≫ x = Λ ≫ ξ := by
  have h := congrArg (· ≫ ev ≫ x) hP
  simp only [Category.assoc] at h hm hvx hkey ⊢
  rw [h, ← Category.assoc m, hm, Category.assoc, hvx, ← hkey]
  simp only [Category.assoc]

/-- The pullback of a morphism followed by a pullback, split, with the second factor presented
as the outer functor applied to the inner functor's action.

This is `CategoryTheory.Functor.map_comp`, stated so that the middle object is `Ψ.obj B` rather
than whatever the codomain of `p` happens to be spelled as. In the application `p` is the
comparison of Stacks 03EL, whose codomain is the composite functor `⊗ ⋙ Ψ` evaluated at a pair,
and matching that against `Ψ.obj ?B` is one unfolding of `CategoryTheory.Functor.comp`, whereas
comparing the two whole composites afterwards is not affordable. -/
theorem map_comp_map {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (Ψ : C₁ ⥤ C₂) (Φ : C₂ ⥤ C₃) {A : C₂} {B B' : C₁} (p : A ⟶ Ψ.obj B) (q : B ⟶ B') :
    Φ.map (p ≫ Ψ.map q) = Φ.map p ≫ Φ.map (Ψ.map q) :=
  Φ.map_comp _ _

end AbstractExchange

section TensorExchange

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

/-- **Three tensorings exchanged.** Tensoring two morphisms into the first variable in turn and
then one into the second is the action of the tensor bifunctor of Stacks 03EL on the pair formed
by the first of them and the morphism in the second variable, followed by the second one.

This is the naturality of the curried tensor product of Stacks 0GMW applied twice, followed by
`sheafTensor_obj_map_comp_sheafTensor_map_app`. Everything here is at variables, which is why
the statement may mix the curried tensor product with the bifunctor at all: the one crossing it
contains is between two objects whose arguments are variables, and there it is free. -/
theorem sheafTensor_exchange_three
    {A A' A'' B B' : SheafOfModules.{u} (Tensor.ringSheaf O)}
    (p : A ⟶ A') (q : A' ⟶ A'') (r : B ⟶ B') :
    ((sheafTensor O).map p).app B ≫ ((sheafTensor O).map q).app B ≫
        ((sheafTensor O).obj A'').map r =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O))).map
          (Prod.mkHom p r) ≫
        ((sheafTensor O).map q).app B' := by
  rw [sheafTensor_map_app_comp_sheafTensor_obj_map O q r, ← Category.assoc,
    sheafTensor_map_app_comp_sheafTensor_obj_map O p r,
    sheafTensor_obj_map_comp_sheafTensor_map_app O p r]

end TensorExchange

section EvaluationUnfold

variable {X Y : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (F G : SheafOfModules.{u} (Tensor.ringSheaf Y.O))

/-- The pulled-back evaluation morphism of Stacks 0GMX written out: the comparison of
Stacks 03EL followed by the pullback of the evaluation morphism of the internal Hom sheaf.

This is the definition of `Stacks.SheafOfModules.InternalHom.toposPullbackEvaluation`, recorded
as an equation so that the two readings of the tensor product of sheaves of modules are compared
once, against the declared type of that definition, rather than inside every goal that needs the
composite.

`Eq` is applied to the two sides rather than written with the `=` notation: the notation
elaborates each side on its own, so the composite's source keeps the uncurried spelling of
`pullbackTensorIso`'s component and comparing it with the curried one unfolds sheafification;
applied directly, `Eq` fixes its type from the left-hand side. -/
theorem toposPullbackEvaluation_eq :
    Eq (toposPullbackEvaluation φ F G)
      ((pullbackTensorIso φ.toModulesHom).inv.app
          ((internalHomSecondFunctor Y.J Y.O F).obj G, F) ≫
        (toposPullback φ).map (internalHomEvaluation Y.O F G)) :=
  rfl

end EvaluationUnfold

section CompComparison

variable {X Y Z : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (ψ : RingedToposHom (RingedSite.ringedTopos Y) (RingedSite.ringedTopos Z))

/-- The comparison `(ψ ∘ φ)^*A ⟶ φ^*ψ^*A` of pullbacks of sheaves of modules along a composite
of morphisms of ringed topoi, with the two pullbacks applied in turn. -/
def toposPullbackCompComparison (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    ((toposCompHom φ ψ).toModulesHom.pullbackModules).obj A ⟶
      (φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A) :=
  (toposPullbackCompIso φ ψ).hom.app A

/-- The comparison `φ^*ψ^*A ⟶ (ψ ∘ φ)^*A` of pullbacks of sheaves of modules along a composite
of morphisms of ringed topoi, with the two pullbacks applied in turn. -/
def toposPullbackCompComparisonInv (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    (φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A) ⟶
      ((toposCompHom φ ψ).toModulesHom.pullbackModules).obj A :=
  (toposPullbackCompIso φ ψ).inv.app A

/-- `toposPullbackCompComparison` is the component of `toposPullbackCompIso`. -/
theorem toposPullbackCompComparison_eq (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    toposPullbackCompComparison φ ψ A = (toposPullbackCompIso φ ψ).hom.app A := rfl

/-- `toposPullbackCompComparisonInv` is the component of the inverse of
`toposPullbackCompIso`. -/
theorem toposPullbackCompComparisonInv_eq (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    toposPullbackCompComparisonInv φ ψ A = (toposPullbackCompIso φ ψ).inv.app A := rfl

/-- The comparison of pullbacks along a composite is natural. -/
theorem toposPullbackCompComparisonInv_naturality
    {A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)} (h : A ⟶ B) :
    (toposPullback φ).map ((toposPullback ψ).map h) ≫
        toposPullbackCompComparisonInv φ ψ B =
      toposPullbackCompComparisonInv φ ψ A ≫
        (toposPullback (toposCompHom φ ψ)).map h :=
  (toposPullbackCompIso φ ψ).inv.naturality h

/-- Pulling back along `ψ` and then along `φ` is the action of the composite functor.

This is `rfl`, and it is stated for an arbitrary morphism on purpose: at an arbitrary morphism
the two sides' types are compared structurally, whereas at the tensor product of Stacks 03EL
they are compared by unfolding a sheafification, which exceeds the elaborator's budget. The two
spellings both occur — the composite functor's action in the naturality of the comparison of
pullbacks, the two actions in turn in the pullback of a composite — so this is the identity that
lets them meet. -/
theorem toposPullbackComp_map {A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)} (h : A ⟶ B) :
    (toposPullback φ).map ((toposPullback ψ).map h) =
      (ψ.toModulesHom.pullbackModules ⋙ φ.toModulesHom.pullbackModules).map h :=
  rfl

/-- **The comparison of pullbacks along a composite is natural**, with its source read as the
tensor product of Stacks 03EL and its target through `toposPullbackCompComparisonInv`.

The two ends are spelled differently on purpose, for the reason the implementation notes record:
the target is the spelling the canonical map of Stacks 0GMX composes with, and the source is the
spelling the composition law of Stacks 03EL, `pullbackTensorIso_inv_app_toposCompHom`, uses. -/
theorem toposPullbackCompComparisonInv_naturality_tensor
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O))
    (C : SheafOfModules.{u} (Tensor.ringSheaf Z.O))
    (h : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
        (A, B) ⟶ C) :
    (toposPullback φ).map ((toposPullback ψ).map h) ≫
        toposPullbackCompComparisonInv φ ψ C =
      (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
            ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
            (RingedToposHom.toModulesHomPushforwardIso φ ψ)
            (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
            (A, B)) ≫
        ((toposCompHom φ ψ).toModulesHom.pullbackModules).map h :=
  (toposPullbackCompIso φ ψ).inv.naturality h

/-- **The comparison of pullbacks along a composite is natural, past a morphism into the middle
pullback**, with its target leg read through `toposPullbackCompComparisonInv` and its source leg
exactly as the composition law of Stacks 03EL spells it.

This is `Stacks.SheafOfModules.InternalHom.toposPullbackCompIso_inv_app_naturality`. Keeping
`p ≫ ψ^*h` under a single `φ^*` is what makes it usable, and is why it replaces the splitting of
the pullback of the inner evaluation that the abstract law used to ask for: splitting it is what
asks the curried tensor product of Stacks 0GMW and the tensor bifunctor of Stacks 03EL to be
compared *over the middle site*. With the two legs spelled as they are, it composes on the left
with the pullback of a tensor--evaluation composite and on the right with
`pullbackTensorIso_inv_app_toposCompHom`, and it discharges preservation of composition and
naturality together. -/
theorem toposPullbackCompComparisonInv_naturality_comp
    {A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)}
    {W : SheafOfModules.{u} (Tensor.ringSheaf Y.O)}
    (p : W ⟶ (toposPullback ψ).obj A) (h : A ⟶ B) :
    (toposPullback φ).map (p ≫ (toposPullback ψ).map h) ≫
        toposPullbackCompComparisonInv φ ψ B =
      (toposPullback φ).map p ≫
        (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
              ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
              (RingedToposHom.toModulesHomPushforwardIso φ ψ)
              (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app A ≫
          ((toposCompHom φ ψ).toModulesHom.pullbackModules).map h :=
  toposPullbackCompIso_inv_app_naturality φ ψ p h

/-- The tensor product of the two comparisons of pullbacks, followed by the tensor product of
the two inverse comparisons, is the identity.

The two factors are spelled differently on purpose: the first through
`toposPullbackCompComparison`, whose declared type applies the two pullbacks in turn, and the
second exactly as the composition law
`Stacks.SheafOfModules.InternalHom.pullbackTensorIso_inv_app_toposCompHom` of Stacks 03EL spells
it, so that the two can be composed with each other without the elaborator having to compare
`(ψ ∘ φ)^*` with `ψ^* ⋙ φ^*` inside the pair of objects the tensor bifunctor is applied to. -/
theorem tensorSheafBifunctor_map_toposPullbackCompComparison_comp_inv
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (Prod.mkHom (toposPullbackCompComparison φ ψ A)
            (toposPullbackCompComparison φ ψ B)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (((Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
              ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
              (RingedToposHom.toModulesHomPushforwardIso φ ψ)
              (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app A,
            (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
              ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
              (RingedToposHom.toModulesHomPushforwardIso φ ψ)
              (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app B) :
            (((φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A),
              (φ.toModulesHom.pullbackModules).obj
                ((ψ.toModulesHom.pullbackModules).obj B)) :
              SheafOfModules.{u} (Tensor.ringSheaf X.O) ×
                SheafOfModules.{u} (Tensor.ringSheaf X.O)) ⟶
            (((toposCompHom φ ψ).toModulesHom.pullbackModules).obj A,
              ((toposCompHom φ ψ).toModulesHom.pullbackModules).obj B)) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp]
  refine Eq.trans (congrArg _ ?_) (CategoryTheory.Functor.map_id _ _)
  exact Prod.hom_ext ((toposPullbackCompIso φ ψ).hom_inv_id_app A)
    ((toposPullbackCompIso φ ψ).hom_inv_id_app B)

/-- **The two one-variable tensorings of the comparison of pullbacks cancel against the two of
its inverse.** This is cancellation at the two comparisons of pullbacks along a composite.

Every morphism here is a one-variable action of the *curried* tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the form
`Stacks.SheafOfModules.InternalHom.tensorEvaluation` produces, and the identity is at the
curried tensor product's object.  Nothing in the statement mentions
`AlgebraicGeometry.SheafOfModules.tensorSheafBifunctor`, and that is what makes it elaborate:
the two readings meet only inside the proof, where
`sheafTensor_obj_map_comp_sheafTensor_map_app` identifies each pair of one-variable actions
with a single action of the bifunctor at a type the elaborator infers rather than checks.

With every object pinned and in a declaration of its own, the same cancellation with
its third factor *written* as `tensorSheafBifunctor.map` — the spelling
`pullbackTensorIso_inv_app_toposCompHom` produces — exhausts 200000 heartbeats at `whnf`,
whether the pair is given as `Prod.mkHom` or as an ascribed pair, and whether the identity is
taken at the curried object or at the bifunctor's.  The statement below, in the curried
spelling alone, elaborates in 3.6 seconds.  The cause is the seam the implementation notes
record: `tensorSheafBifunctor` is taken over `CategoryTheory.Sheaf.toRingCat X.J X.O` and
`sheafTensor` over `Stacks.SheafOfModules.Tensor.ringSheaf X.O`, so a hand-written statement
whose `≫` forces one against the other asks `CategoryTheory.sheafCompose` to be pushed through
the `Sheaf` constructor at these objects. -/
theorem sheafTensor_toposPullbackCompComparison_comp_inv
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    ((sheafTensor X.O).obj ((toposPullback (toposCompHom φ ψ)).obj A)).map
          (toposPullbackCompComparison φ ψ B) ≫
        ((sheafTensor X.O).map (toposPullbackCompComparison φ ψ A)).app
            ((toposPullback φ).obj ((toposPullback ψ).obj B)) ≫
          (((sheafTensor X.O).obj ((toposPullback φ).obj ((toposPullback ψ).obj A))).map
              (toposPullbackCompComparisonInv φ ψ B) ≫
            ((sheafTensor X.O).map (toposPullbackCompComparisonInv φ ψ A)).app
              ((toposPullback (toposCompHom φ ψ)).obj B)) =
      𝟙 (((sheafTensor X.O).obj ((toposPullback (toposCompHom φ ψ)).obj A)).obj
        ((toposPullback (toposCompHom φ ψ)).obj B)) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ _)
          (sheafTensor_obj_map_comp_sheafTensor_map_app X.O
            (toposPullbackCompComparison φ ψ A)
            (toposPullbackCompComparison φ ψ B))).trans
      ((congrArg (fun z ↦ _ ≫ z)
            (sheafTensor_obj_map_comp_sheafTensor_map_app X.O
              (toposPullbackCompComparisonInv φ ψ A)
              (toposPullbackCompComparisonInv φ ψ B))).trans
        (tensorSheafBifunctor_map_toposPullbackCompIso_hom_comp_inv φ ψ A B)))

/-- `toposPullbackCompComparisonInv_naturality_comp` at the inverse comparison of Stacks 03EL,
which is the morphism into the middle pullback that the canonical map of Stacks 0GMX supplies.

The general statement takes that morphism as `p : W ⟶ (toposPullback ψ).obj A`, so applying it at
`(pullbackTensorIso ψ).inv.app (A, B)`, whose codomain is the composite functor
`⊗ ⋙ ψ^*` evaluated at a pair, asks the elaborator to solve `(toposPullback ψ).obj ?A` against
that, and that inversion exhausts 200000 heartbeats. Here the tensor product is written
out, so `A` is given and the only thing left to compare is the curried tensor product of
Stacks 0GMW against the bifunctor of Stacks 03EL at one pair of objects, which is `rfl`. -/
theorem toposPullbackCompComparisonInv_naturality_pullbackTensorIso
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O))
    {T : SheafOfModules.{u} (Tensor.ringSheaf Z.O)}
    (h : ((sheafTensor Z.O).obj A).obj B ⟶ T) :
    (toposPullback φ).map
          ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B) ≫ (toposPullback ψ).map h) ≫
        toposPullbackCompComparisonInv φ ψ T =
      (toposPullback φ).map ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B)) ≫
        (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
              ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
              (RingedToposHom.toModulesHomPushforwardIso φ ψ)
              (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app
            (((sheafTensor Z.O).obj A).obj B) ≫
          ((toposCompHom φ ψ).toModulesHom.pullbackModules).map h :=
  toposPullbackCompComparisonInv_naturality_comp φ ψ
    (A := ((sheafTensor Z.O).obj A).obj B) (B := T)
    ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B)) h

/-- Tensor coherence at arbitrary arguments, with its comparison at the curried tensor. -/
private theorem pullbackTensorIso_inv_app_toposCompHom_cancel
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (Prod.mkHom (toposPullbackCompComparison φ ψ A)
            (toposPullbackCompComparison φ ψ B)) ≫
        (pullbackTensorIso φ.toModulesHom).inv.app
          ((toposPullback ψ).obj A, (toposPullback ψ).obj B) ≫
        (toposPullback φ).map ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B)) ≫
        (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom
          ψ.toModulesHom (toposCompHom φ ψ).toModulesHom
          (RingedToposHom.toModulesHomPushforwardIso φ ψ)
          (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).inv.app
            (((sheafTensor Z.O).obj A).obj B) =
      (pullbackTensorIso (toposCompHom φ ψ).toModulesHom).inv.app (A, B) :=
  cancelWhisker
    (tensorSheafBifunctor_map_toposPullbackCompComparison_comp_inv φ ψ A B)
    (pullbackTensorIso_inv_app_toposCompHom φ ψ A B)

/-- **The canonical map of Stacks 0GMX is compatible with composition.** For morphisms of ringed
topoi `φ : X ⟶ Y` and `ψ : Y ⟶ Z` between the topoi of three ringed sites and sheaves of
`O_Z`-modules `F`, `G`, the canonical map

`(ψ ∘ φ)^* Hom_{O_Z}(F, G) ⟶ Hom_{O_X}((ψ ∘ φ)^*F, (ψ ∘ φ)^*G)`

of the composite is the canonical map of `ψ` pulled back along `φ`, followed by the canonical
map of `φ`, read through the comparison of pullbacks along a composite at `Hom_{O_Z}(F, G)`, at
the source of the internal Hom sheaf — through `internalHomPre`, the comparison in the first
variable — and at its target.

This is the law the localization square of Stacks 04J0 reduces to, and it is proved by the route
the source's Remark 18.27.3 indicates: `tensorEvaluation_injective` turns it into an identity
between two morphisms out of `(ψ ∘ φ)^*Hom_{O_Z}(F, G) ⊗_{O_X} (ψ ∘ φ)^*F`, where
`tensorEvaluation_comp` and `tensorEvaluation_comp_internalHomPre_comp_map` read the composite
route off and `toposPullbackEvaluationExchange` assembles the four inputs — the exchange of
tensorings `sheafTensor_exchange_three`, the pulled-back tensor--evaluation composite
`toposPullback_tensorEvaluation`, the naturality
`toposPullbackCompComparisonInv_naturality_pullbackTensorIso` transported along the two readings
of the inner pulled-back evaluation, and the composition law of Stacks 03EL
`pullbackTensorIso_inv_app_toposCompHom` with the comparison of pullbacks cancelled off it by
`cancelWhisker`. -/
@[stacks 0GMX "compatibility of the canonical map with composition"]
theorem toposPullbackInternalHomMap_comp
    (F G : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    toposPullbackInternalHomMap (toposCompHom φ ψ) F G =
      toposPullbackCompComparison φ ψ ((internalHomSecondFunctor Z.J Z.O F).obj G) ≫
        (toposPullback φ).map (toposPullbackInternalHomMap ψ F G) ≫
          toposPullbackInternalHomMap φ ((toposPullback ψ).obj F) ((toposPullback ψ).obj G) ≫
            (internalHomPre X.O (toposPullbackCompComparison φ ψ F)).app
                ((toposPullback φ).obj ((toposPullback ψ).obj G)) ≫
              (internalHomSecondFunctor X.J X.O ((toposPullback (toposCompHom φ ψ)).obj F)).map
                (toposPullbackCompComparisonInv φ ψ G) := by
  have hP := sheafTensor_exchange_three X.O
    (toposPullbackCompComparison φ ψ ((internalHomSecondFunctor Z.J Z.O F).obj G))
    ((toposPullback φ).map (toposPullbackInternalHomMap ψ F G))
    (toposPullbackCompComparison φ ψ F)
  have hm := toposPullback_tensorEvaluation φ
    (A := (toposPullback ψ).obj ((internalHomSecondFunctor Z.J Z.O F).obj G))
    (toposPullbackInternalHomMap ψ F G)
  -- The two readings of the pulled-back evaluation morphism of `ψ` meet at the composite
  -- functor's spelling of the tensor product, so the `congrArg` binder is pinned there: left to
  -- be read off the curried spelling it costs the elaborator's whole budget.
  have hnat := toposPullbackCompComparisonInv_naturality_pullbackTensorIso φ ψ
    ((internalHomSecondFunctor Z.J Z.O F).obj G) F (internalHomEvaluation Z.O F G)
  have hvx₀ := congrArg (fun z : (Functor.prod (toposPullback ψ) (toposPullback ψ) ⋙
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj
            ((internalHomSecondFunctor Z.J Z.O F).obj G, F) ⟶ (toposPullback ψ).obj G ↦
        (toposPullback φ).map z ≫ toposPullbackCompComparisonInv φ ψ G)
      ((tensorEvaluation_toposPullbackInternalHomMap ψ F G).trans
        (toposPullbackEvaluation_eq ψ F G))
  have hvx := hvx₀.trans hnat
  have hkey := pullbackTensorIso_inv_app_toposCompHom_cancel φ ψ
    ((internalHomSecondFunctor Z.J Z.O F).obj G) F
  apply tensorEvaluation_injective X.O ((toposPullback (toposCompHom φ ψ)).obj F)
    ((toposPullback (toposCompHom φ ψ)).obj G)
  rw [tensorEvaluation_toposPullbackInternalHomMap (toposCompHom φ ψ) F G,
    toposPullbackEvaluation_eq (toposCompHom φ ψ) F G,
    tensorEvaluation_comp, tensorEvaluation_comp,
    tensorEvaluation_comp_internalHomPre_comp_map,
    tensorEvaluation_toposPullbackInternalHomMap]
  exact (toposPullbackEvaluationExchange hP hm hvx hkey).symm

end CompComparison

end Stacks.SheafOfModules.InternalHom

end
