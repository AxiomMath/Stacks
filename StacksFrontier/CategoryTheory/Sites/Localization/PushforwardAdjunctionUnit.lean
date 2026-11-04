module

public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# The unit of the restricted adjunction of an adjoint pair of sites

For an adjoint pair `u ⊣ v` of continuous functors between sites, restriction of sheaves gives an
adjunction `u^s ⊣ v^s` (`CategoryTheory.Adjunction.sheafPushforwardAdjunction`). Both functors
are precomposition, so the unit of that adjunction ought to be nothing but the sheaf read along
the counit of `u ⊣ v`. It is, but not visibly: the adjunction is built by restricting the
adjunction of presheaves along the fully faithful inclusions of sheaves, and
`CategoryTheory.Adjunction.restrictFullyFaithful` wraps its unit in two comparison isomorphisms
and a `CategoryTheory.Functor.FullyFaithful.preimage`.

This file unwraps it.

## Main results

* `CategoryTheory.Adjunction.sheafPushforwardAdjunction_unit_hom_app`: the unit of the restricted
  adjunction, at a sheaf `Z` and an object `X`, is `Z` read along the opposite of the counit of
  `u ⊣ v` at `X`.

## Implementation notes

`CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` computes the *image* of the
restricted unit under the inclusion of sheaves, which is what avoids the `preimage`: the equation
is read back through the inclusion being faithful, or — as here — used directly, the image under
`sheafToPresheaf` of a morphism of sheaves being that morphism's underlying morphism of
presheaves on the nose.

The two comparison isomorphisms it then leaves are
`CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso`, which is `Iso.refl`;
but their components are identities at two *different spellings* of one object, so neither `simp`
nor `rw` can cancel them — `rw` reports that the target is not type-correct at `implicit`
transparency. A `change` to a single spelling is what clears them, and it is why the proof is not
one `simp`.

Mathlib's `CategoryTheory.Adjunction.sheafPushforwardContinuous` is the same adjunction built
directly from the whiskered opposite adjunction, where this computation is `simp`.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂ v' u'

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (A : Type u') [Category.{v'} A] {u : C ⥤ D} {v : D ⥤ C}
  (adj : u ⊣ v) [u.IsContinuous J K] [v.IsContinuous K J]

/-- **The unit of the restricted adjunction is restriction along the counit.** For an adjoint
pair `u ⊣ v` of continuous functors between sites, a sheaf `Z` on the target of `u` and an object
`X` of that target, the unit of `u^s ⊣ v^s` at `Z` is `Z` read along the opposite of the counit of
`u ⊣ v` at `X`.

This is not available from the definition: restricting the presheaf-level adjunction to sheaves
wraps the unit in a `CategoryTheory.Functor.FullyFaithful.preimage`. -/
theorem Adjunction.sheafPushforwardAdjunction_unit_hom_app (Z : Sheaf K A) (X : Dᵒᵖ) :
    ((adj.sheafPushforwardAdjunction (J := J) (K := K) A).unit.app Z).hom.app X =
      Z.obj.map (adj.counit.app X.unop).op := by
  have hu := Adjunction.map_restrictFullyFaithful_unit_app
    (Functor.whiskeringLeftAdjunctionOfAdjunction A adj)
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (v.sheafPushforwardContinuousCompSheafToPresheafIso A K J).symm Z
  refine (NatTrans.congr_app hu X).trans ?_
  simp only [Functor.whiskeringLeftAdjunctionOfAdjunction, NatTrans.comp_app,
    Adjunction.whiskerLeft_unit_app_app, Iso.symm_hom,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  change Z.obj.map (adj.counit.app X.unop).op ≫
      𝟙 (Z.obj.obj (Opposite.op (u.obj (v.obj X.unop)))) ≫
      𝟙 (Z.obj.obj (Opposite.op (u.obj (v.obj X.unop)))) = _
  simp

end CategoryTheory

end
