module

public import StacksFrontier.CategoryTheory.Bicategory.NaturalTransformation.LocallyDiscrete
public import StacksFrontier.CategoryTheory.Sites.Descent.CoGrothendieckStack

/-!
# The unity coherence of the comparison with the pullback pseudofunctor

`StacksFrontier/CategoryTheory/Sites/Descent/CoGrothendieckStack.lean` builds, for a pseudofunctor
`F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat`, the comparison
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpIso` identifying the transition functor of
`F` along a one-morphism with the chosen pullback functor of the fibred category `∫ᶜ F`. Together
with the fibrewise identification
`CategoryTheory.Pseudofunctor.CoGrothendieck.fiberFunctor` that is the *data* of a strong
transformation `F ⟶ pullbackPseudofunctor (∫ᶜ F)`; what remains are its coherence axioms.

`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete` reduces those to two
componentwise equations — `naturality_naturality` being automatic over a locally discrete base —
and this file proves the first of them, the *unity* coherence: the comparison carries the identity
constraint of `F` to the unitor of the pullback pseudofunctor.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.fiberInclusion_map_fiberFunctor_map`: the spelling
  bridge between `Fiber.fiberInclusion ∘ fiberFunctor` and
  `CategoryTheory.Pseudofunctor.CoGrothendieck.ι`, in the form the rewrites below need. It is
  `CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_eq_vertHom` at the `Fiber.inducedFunctor`
  spelling of `ι`, and holds by `rfl`.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_comp_pbMapId`: **the unity coherence of
  the comparison.** Both sides are morphisms of a fibre, so they are compared by the faithfulness
  of `Fiber.fiberInclusion`; the left side is then the defining triangle of the comparison
  (`pullbackCmp_hom_fac`) composed with the description of the unitor
  (`pbMapId_hom_app` and `cmpUnderlying_cartPullback_cartId`), which is the tautological cartesian
  lift of an identity, and the right side is the vertical morphism attached to
  `F.mapId`. The two agree because `(F.mapId a).hom` and `(F.mapId a).inv` cancel.

## Implementation notes

**Why the comparison is indexed by a one-morphism of `LocallyDiscrete 𝒮ᵒᵖ`.** `pullbackCmp` used
to be stated for a morphism `f : W ⟶ U` of `𝒮`, mentioning `F.map f.op.toLoc`. The coherence
axioms of a strong transformation are indexed by one-morphisms of the source bicategory, so at an
identity they mention `F.map (𝟙 a)`; and `(𝟙 S).op.toLoc` and `𝟙 ⟨op S⟩`, while definitionally
equal, are not the same term. Every rewrite then failed with *the target expression is not
type-correct under the `implicit` transparency level*, because the two spellings sit inside the
semireducible `CategoryTheory.Functor.Fiber`. Re-indexing the comparison by a one-morphism of
`LocallyDiscrete 𝒮ᵒᵖ` removes the mismatch at the source, and is what lets the proof below run with
no transparency option.

**The reducibility list.** Beyond the four definitions
`StacksFrontier/CategoryTheory/Sites/Descent/CoGrothendieckStack.lean` declares reducible at
implicit
transparency, the proof here needs `CategoryTheory.Functor.IsFibered.pbObj` and `pbMap`: the
unitor `pbMapId` of the pullback pseudofunctor has a type spelled through `pbObj`, i.e. through
`Cat.of` of a fibre, while the comparison has one spelled through the fibre itself, and composing
the two is well formed only once those unfold. This is *not* a free addition — see the note in
`CoGrothendieckPullbackUnit`'s companion discussion: with `pbObj` and `pbMap` reducible, the
`@[simps]` projection lemmas `CoGrothendieck.categoryStruct_comp_base` and `_comp_fiber` stop
matching, so a proof needing those belongs in a file without them.

No Stacks tag is claimed: this is the bicategorical bookkeeping of the round trip through the
Grothendieck construction, Stacks 003S and 02XO, neither of which this file proves.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory CategoryTheory.Functor CategoryTheory.Functor.IsFibered Opposite
open scoped CategoryTheory.Bicategory

universe v₁ u₁ v₂ u₂

-- Load-bearing, for the reasons set out in the implementation notes: the four definitions of
-- `CoGrothendieckStack.lean`, plus `pbObj` and `pbMap`, so that a morphism typed through the
-- fibre and one typed through `Cat.of` of the fibre compose.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.mk CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.IsFibered.fiberPullback
  CategoryTheory.Functor.IsFibered.pbObj CategoryTheory.Functor.IsFibered.pbMap

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{max v₁ v₂, max u₁ u₂})

/-- `CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_eq_vertHom` at the
`CategoryTheory.Functor.Fiber.inducedFunctor` spelling of `ι`: the underlying morphism of `∫ᶜ F`
of the image of `α` under the fibrewise identification is the vertical morphism attached to `α`. -/
lemma fiberInclusion_map_fiberFunctor_map (S : 𝒮) {X Y : F.obj ⟨op S⟩} (α : X ⟶ Y) :
    Fiber.fiberInclusion.map ((fiberFunctor F S).map α) = vertHom F S α := rfl

/-- **The unity coherence of the comparison with the pullback pseudofunctor**: the comparison
carries the identity constraint of `F` to the unitor of the pullback pseudofunctor of `∫ᶜ F`.

This is the `naturality_id` hypothesis of
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete` for the comparison, written out
at the fibre. -/
lemma pullbackCmp_comp_pbMapId (a : LocallyDiscrete 𝒮ᵒᵖ) (X : F.obj a) :
    (pullbackCmp F (𝟙 a) X).hom ≫
        (pbMapId (CoGrothendieck.forget F) a).hom.toNatTrans.app
          ((fiberFunctor F a.as.unop).obj X) =
      (fiberFunctor F a.as.unop).map ((F.mapId a).hom.toNatTrans.app X) := by
  apply Fiber.fiberInclusion.map_injective
  have hfac : Fiber.fiberInclusion.map (pullbackCmp F (𝟙 a) X).hom ≫
      IsPreFibered.pullbackMap ((fiberFunctor F a.as.unop).obj X).2 (𝟙 a.as.unop) =
        CoGrothendieck.cartesianLift X (𝟙 a.as.unop) :=
    pullbackCmp_hom_fac F (𝟙 a) X
  rw [CategoryTheory.Functor.map_comp, pbMapId_hom_app, cmpUnderlying_cartPullback_cartId,
    hfac, fiberInclusion_map_fiberFunctor_map]
  refine CoGrothendieck.Hom.ext _ _ rfl ?_
  simp [vertHom]

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
