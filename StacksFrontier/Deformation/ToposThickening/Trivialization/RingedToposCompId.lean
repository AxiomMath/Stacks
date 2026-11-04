module

public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposId
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composing a morphism of ringed topoi with the identity

`AlgebraicGeometry.RingedToposHom.comp` is not the composition of a category instance on ringed
topoi — its two arguments may live in different universes — so the right unit law is a bare
lemma here. It is what lets a square of thickenings over a fixed base, whose left vertical
arrow is `AlgebraicGeometry.RingedToposHom.id`, be read as a plain commuting triangle.

## Main results

* `CategoryTheory.MorphismOfTopoi.comp_id` and `AlgebraicGeometry.RingedToposHom.comp_id`:
  composing with the identity morphism on the right changes nothing.
* `AlgebraicGeometry.RingedToposHom.hom_ext`: a morphism of ringed topoi is its underlying
  morphism of topoi together with its structure map.

## Implementation notes

Both halves of `comp_id` are facts about transported structure rather than about topoi. On
underlying morphisms of topoi the two functors agree definitionally and the two adjunctions
agree by `CategoryTheory.Adjunction.ext`, an adjunction being determined by its unit. On
structure maps it is `AlgebraicGeometry.RingedToposHom.comp_fSharp_forget` together with
`AlgebraicGeometry.RingedToposHom.forgetRing_map_id_fSharp`. The two halves are assembled by
`hom_ext`, which takes the structure-map equality as a heterogeneous one because the type of
`fSharp` depends on the underlying morphism of topoi.
-/

@[expose] public section

open CategoryTheory

universe v u w v' u' w'

namespace CategoryTheory.MorphismOfTopoi

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]

/-- Composing a morphism of topoi with the identity morphism on the right changes nothing. The
two underlying functors are the identity-composites, which agree with the originals
definitionally; the two adjunctions agree because an adjunction is determined by its unit and
the unit of a composite with the identity adjunction is the original unit. -/
@[sga "4 IV 3.3.1" "right identity law"]
theorem comp_id (g : MorphismOfTopoi E F) : g.comp (MorphismOfTopoi.id E) = g := by
  obtain ⟨pushforward, inverseImage, adj, preservesFiniteLimits⟩ := g
  have h : Adjunction.comp adj Adjunction.id = adj := by
    ext Z
    simp [Adjunction.comp_unit_app]
  exact congrArg
    (fun a ↦ MorphismOfTopoi.mk pushforward inverseImage a preservesFiniteLimits) h

end CategoryTheory.MorphismOfTopoi

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- Two morphisms of ringed topoi with the same underlying morphism of topoi and the same
structure map are equal. The structure-map hypothesis is heterogeneous because the type of
`fSharp` depends on the underlying morphism of topoi. -/
theorem hom_ext {f g : RingedToposHom X Y} (hToposHom : f.toToposHom = g.toToposHom)
    (hfSharp : HEq f.fSharp g.fSharp) : f = g := by
  obtain ⟨T, s⟩ := f
  obtain ⟨T', s'⟩ := g
  cases hToposHom
  cases hfSharp
  rfl

/-- **Composing a morphism of ringed topoi with the identity morphism on the right changes
nothing.** On structure maps this is the composition formula `comp_fSharp_forget`, read on
underlying sheaves of sets, where the structure map of the identity is the identity. -/
theorem comp_id (i : RingedToposHom X Y) : i.comp (RingedToposHom.id X) = i := by
  refine hom_ext (CategoryTheory.MorphismOfTopoi.comp_id _) (heq_of_eq ?_)
  refine Y.forgetRing.map_injective ?_
  refine (comp_fSharp_forget i (RingedToposHom.id X)).trans ?_
  refine (congrArg (fun m ↦ Y.forgetRing.map i.fSharp ≫ m) ?_).trans (Category.comp_id _)
  exact (congrArg i.toToposHom.pushforward.map (forgetRing_map_id_fSharp X)).trans
    (CategoryTheory.Functor.map_id _ _)

end AlgebraicGeometry.RingedToposHom

end
