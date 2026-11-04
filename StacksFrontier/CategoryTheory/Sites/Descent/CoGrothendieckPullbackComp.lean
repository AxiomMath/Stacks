module

public import StacksFrontier.CategoryTheory.Sites.Descent.CoGrothendieckPullbackUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of a pseudofunctor with the pullback pseudofunctor of its fibration

`StacksFrontier/CategoryTheory/Sites/Descent/CoGrothendieckStack.lean` builds, for a pseudofunctor
`F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat`, the comparison
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpIso` identifying the transition functor of
`F` along a one-morphism with the chosen pullback functor of the fibred category `∫ᶜ F`, and
`StacksFrontier/CategoryTheory/Sites/Descent/CoGrothendieckPullbackUnit.lean` proves the unity
coherence that comparison satisfies. This file proves the remaining one — the *functoriality*
coherence — and assembles the three into the strong transformation
`F ⟶ pullbackPseudofunctor (∫ᶜ F)` of the round trip through the Grothendieck construction,
Stacks 003S and 02XO.

That transformation is what lets a descent statement about `F` be read as one about `∫ᶜ F`:
`CategoryTheory.Functor.isStack_pullbackPseudofunctor_iff` relates
`CategoryTheory.Functor.IsStack` of a fibred category to `CategoryTheory.Pseudofunctor.IsStack` of
its pullback pseudofunctor, and
`CategoryTheory.Pseudofunctor.StrongTrans.isStackFor_iff_of_app_isEquivalence` transports being a
stack along a fibrewise equivalence of pseudofunctors.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpIso_hom_app`: the component of the
  comparison at an object is the comparison isomorphism
  `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp` there, by `rfl`. Stated because the
  coherence goals mention the natural isomorphism and every lemma about it mentions the
  componentwise one.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_comp_pbMapComp`: **the functoriality
  coherence of the comparison.** Both sides are morphisms of a fibre into a chosen pullback
  object, so they are compared by the universal property of the chosen cartesian lift
  (`CategoryTheory.Functor.fiber_hom_ext_of_cartesian` against
  `CategoryTheory.Functor.IsFibered.cartComp`); each side then telescopes, by the defining triangle
  of the comparison and of the compositor, to a composite of tautological cartesian lifts of
  `∫ᶜ F`, and the two agree by
  `CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift_of_comp`.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans`: **the comparison of `F`
  with the pullback pseudofunctor of `∫ᶜ F`, as a strong transformation.**

## Implementation notes

**Why the functoriality coherence is proved at the `pbMapComp` spelling.** The compositor of the
pullback pseudofunctor is `CategoryTheory.Functor.IsFibered.pbMapComp`, and
`pullbackPseudofunctor_mapComp` says the pseudofunctor's `mapComp` is that. The two are the same
term up to the unfolding of `pullbackPseudofunctor`, but rewriting the *object* part of the
pseudofunctor into the `pbObj` spelling leaves the `Bicategory.homCategory` instance behind at the
old spelling, and the resulting goal is no longer type-correct at implicit transparency. Stating
the coherence at `pbMapComp` and letting the elaborator identify the two at the point of use —
where the identification is demanded of a term, not of a motive — avoids the problem entirely.
This is the same route `CoGrothendieckPullbackUnit`'s `pullbackCmp_comp_pbMapId` takes.

No Stacks tag is claimed: this is the bicategorical bookkeeping of the round trip through the
Grothendieck construction, Stacks 003S and 02XO, neither of which this file proves.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 02XO](https://stacks.math.columbia.edu/tag/02XO)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory CategoryTheory.Functor CategoryTheory.Functor.IsFibered Opposite
open scoped CategoryTheory.Bicategory

universe v₁ u₁ v₂ u₂

-- Load-bearing, for the reasons set out in `CoGrothendieckPullbackUnit`'s implementation notes:
-- the four definitions of `CoGrothendieckStack.lean`, plus `pbObj` and `pbMap`, so that a
-- morphism typed through the fibre and one typed through `Cat.of` of the fibre compose.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.mk CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.IsFibered.fiberPullback
  CategoryTheory.Functor.IsFibered.pbObj CategoryTheory.Functor.IsFibered.pbMap

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{max v₁ v₂, max u₁ u₂})

/-- The component of `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpIso` at an object is
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp` there. The coherence goals of
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete` are stated at the natural
isomorphism, while its defining triangle
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_hom_fac` is stated at the component, so
this `rfl` is what lets the triangle be used. -/
lemma pullbackCmpIso_hom_app {a b : LocallyDiscrete 𝒮ᵒᵖ} (φ : a ⟶ b) (X : F.obj a) :
    (pullbackCmpIso F φ).hom.app X = (pullbackCmp F φ X).hom := rfl

/-- **The functoriality coherence of the comparison with the pullback pseudofunctor**: the
comparison carries the composition constraint of `F` to the compositor of the pullback
pseudofunctor of `∫ᶜ F`.

This is the `nat_comp` hypothesis of
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete` for the comparison, written out
at the fibre. -/
lemma pullbackCmp_comp_pbMapComp {a b c : LocallyDiscrete 𝒮ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (X : F.obj a) :
    (pullbackCmpIso F (f ≫ g)).hom.app X ≫
        (pbMapComp (CoGrothendieck.forget F) f g).hom.toNatTrans.app
          ((fiberFunctor F a.as.unop).obj X) =
      (fiberFunctor F c.as.unop).map ((F.mapComp f g).hom.toNatTrans.app X) ≫
        (pullbackCmpIso F g).hom.app ((F.map f).toFunctor.obj X) ≫
          (fiberPullback g.as.unop).map ((pullbackCmpIso F f).hom.app X) := by
  let _ := (cartComp (p := CoGrothendieck.forget F) f.as.unop g.as.unop).isCart
    ((fiberFunctor F a.as.unop).obj X)
  refine Functor.fiber_hom_ext_of_cartesian (g.as.unop ≫ f.as.unop)
    ((cartComp (p := CoGrothendieck.forget F) f.as.unop g.as.unop).proj
      ((fiberFunctor F a.as.unop).obj X))
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _) _ _ ?_
  -- The left side: the compositor's triangle turns it into the comparison at `f ≫ g` followed by
  -- the chosen lift of `f ≫ g`, and the comparison's own triangle into the tautological lift.
  rw [Functor.map_comp, Category.assoc, pbMapComp_hom_app, CartStruct.cmpUnderlying_fac,
    cartPullback_proj, pullbackCmpIso_hom_app, pullbackCmp_hom_fac]
  -- The right side: split the projection of `cartComp` into the two chosen lifts it is made of.
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    fiberInclusion_map_fiberFunctor_map,
    show (cartComp (p := CoGrothendieck.forget F) f.as.unop g.as.unop).proj
          ((fiberFunctor F a.as.unop).obj X)
        = IsPreFibered.pullbackMap
            ((fiberPullback f.as.unop).obj ((fiberFunctor F a.as.unop).obj X)).2 g.as.unop ≫
          IsPreFibered.pullbackMap ((fiberFunctor F a.as.unop).obj X).2 f.as.unop from rfl]
  -- Slide the `g`-pullback of the comparison at `f` past the chosen lift of `g`, then cancel the
  -- comparison at `f` against its triangle.
  rw [show (fiberPullback g.as.unop).map ((pullbackCmpIso F f).hom.app X)
        = fiberPullbackMap g.as.unop ((pullbackCmpIso F f).hom.app X) from rfl,
    ← Category.assoc (Fiber.fiberInclusion.map
      (fiberPullbackMap g.as.unop ((pullbackCmpIso F f).hom.app X))),
    fiberPullbackMap_comm, Category.assoc, pullbackCmpIso_hom_app, pullbackCmpIso_hom_app]
  dsimp only [Functor.comp_obj]
  rw [pullbackCmp_hom_fac F f X]
  -- What is left is the composition law for the tautological cartesian lifts, and the triangle of
  -- the comparison at `g`.
  refine Eq.trans
    (cartesianLift_of_comp F f.as.unop g.as.unop X ((F.mapComp f g).hom.toNatTrans.app X) rfl) ?_
  simp only [← pullbackCmp_hom_fac F g]
  exact congrArg _ (Category.assoc _ _ _)

/-- **The comparison of `F` with the pullback pseudofunctor of its Grothendieck construction, as a
strong transformation.** Its component at an object is the identification
`CategoryTheory.Pseudofunctor.CoGrothendieck.fiberFunctor` of `F S` with the fibre of `∫ᶜ F` over
`S`, and its strong naturality constraint is
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpIso`. Of its three coherence axioms,
`naturality_naturality` is automatic over a locally discrete base and is discharged by
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete`; the other two are
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_comp_pbMapId` and
`CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmp_comp_pbMapComp`. -/
@[sga "4 VI 7.1.4" "partial", sga "4 XVII 3.3.3" "Reverse direction"]
def pullbackCmpStrongTrans :
    F.StrongTrans (pullbackPseudofunctor (CoGrothendieck.forget F)) :=
  catStrongTransOfIsLocallyDiscrete F (pullbackPseudofunctor (CoGrothendieck.forget F))
    (fun a => fiberFunctor F a.as.unop)
    (fun {_ _} φ => pullbackCmpIso F φ)
    (fun _ _ => by apply pullbackCmp_comp_pbMapId)
    (fun {_ _ _} _ _ _ => by apply pullbackCmp_comp_pbMapComp)

/-- The component of `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpStrongTrans` at an
object is the identification of `F S` with the fibre of `∫ᶜ F` over `S`. -/
@[simp]
lemma pullbackCmpStrongTrans_app_toFunctor (a : LocallyDiscrete 𝒮ᵒᵖ) :
    ((pullbackCmpStrongTrans F).app a).toFunctor = fiberFunctor F a.as.unop := rfl

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
