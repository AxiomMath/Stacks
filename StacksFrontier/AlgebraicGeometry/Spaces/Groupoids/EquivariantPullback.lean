module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackAssoc

/-!
# Inverse image of an equivariant quasi-coherent module along an equivariant morphism

Let `G` be a group algebraic space over an algebraic space `B`, acting on two algebraic spaces
`X` and `Y` over `B`, and let `f : X ⟶ Y` be a morphism over `B` which is equivariant for the
two actions.  The inverse image `f^*ℱ` of a `G`-equivariant quasi-coherent `𝒪_Y`-module
`(ℱ, α)` of Stacks 043T again carries a transition morphism: reindex `α` along the morphism
`1_G × f : G ×_B X ⟶ G ×_B Y` of action spaces, and conjugate the result by the comparisons
`g^* ∘ f^* ≅ (f ≫ g)^*` of Stacks 03LU.  This file constructs that transition morphism and
identifies it.

Two commuting squares make the construction possible, and both come for free from the
hypotheses on `f`: the action square, because `f` is equivariant, and the projection square,
because `f` is a morphism over `B` and `1_G × f` is defined by a universal property.

## Main definitions

* `AlgebraicGeometry.Space.equivariantReindexTransport`: the reindexing of a transition
  morphism along `1_G × f`, with the transports across the two squares of `f` on either side.
* `AlgebraicGeometry.Space.equivariantModulePullbackTransition`: that same morphism, read as a
  transition morphism for the inverse image `f^*ℱ` on `G ×_B X`.

## Main results

* `AlgebraicGeometry.Space.action_comp_asSpaceHom` and
  `AlgebraicGeometry.Space.projection_comp_asSpaceHom`: the action square and the projection
  square of an equivariant morphism `f : X ⟶ Y`.
* `AlgebraicGeometry.Space.equivariantPullbackTransition_eq_modulePullbackReindex`: reindexing
  an equivariant transition morphism of Stacks 043T along a test morphism is reindexing in the
  sense of Stacks 03LU along the induced morphism of algebraic spaces, so the two calculi agree.
* `AlgebraicGeometry.Space.equivariantPullbackTransition_lift`: reindexing along `1_G × f` in
  particular, which is the morphism that enters the construction.
* `AlgebraicGeometry.Space.modulePullbackFlatten_equivariantModulePullbackTransition`:
  flattening the transition morphism of `f^*ℱ` recovers the reindexing of `α` along `1_G × f`,
  conjugated by the two squares of `f`.  Since flattening is injective, this characterises the
  construction.

## Implementation notes

In the category `AlgebraicGeometry.Space.Modules` of `𝒪`-modules on a small étale ringed topos,
a definition whose body is a chain of `≫` is for practical purposes unfoldable: reducing the
composition field of that `CategoryTheory.Category` instance opens the whole topos.  So every
composite built here is named — `CategoryTheory.comp₃` for a triple composite and
`AlgebraicGeometry.Space.modulePullbackUnflatten` for the conjugation by two comparison
isomorphisms — and each definition is related to its factors by a `rfl` equation lemma that
costs a single delta step.  No statement below depends on this; it is only why the bodies are
spelled the way they are.

## References

* [Stacks Project, Tag 043T](https://stacks.math.columbia.edu/tag/043T)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}

/-! ### The two commuting squares of an equivariant morphism -/

/-- The action square of an equivariant morphism `f : X ⟶ Y`: the action on `X` followed by `f`
is `1_G × f` followed by the action on `Y`. -/
theorem action_comp_asSpaceHom (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
    [AX : ModObj G.obj.X X] [AY : ModObj G.obj.X Y] (f : X ⟶ Y) [hf : IsModHom G.obj.X f] :
    action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY := by
  refine ObjectProperty.hom_ext _ ?_
  show (ModObj.smul (M := G.obj.X) (X := X)).left ≫ f.left =
    (lift (fst G.obj.X X) (snd G.obj.X X ≫ f)).left ≫
      (ModObj.smul (M := G.obj.X) (X := Y)).left
  exact congrArg Over.Hom.left hf.smul_hom

/-- The projection square of a morphism `f : X ⟶ Y` over `B`: the projection on `X` followed by
`f` is `1_G × f` followed by the projection on `Y`. -/
theorem projection_comp_asSpaceHom (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left) (f : X ⟶ Y) :
    projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY := by
  refine ObjectProperty.hom_ext _ ?_
  show (snd G.obj.X X).left ≫ f.left =
    (lift (fst G.obj.X X) (snd G.obj.X X ≫ f)).left ≫ (snd G.obj.X Y).left
  exact congrArg Over.Hom.left
    (lift_snd (fst G.obj.X X) (snd G.obj.X X ≫ f)).symm

/-! ### The reindexing form of the transition morphisms of Stacks 043T -/

/-- Reindexing a transition morphism is the reindexing of the inverse-image calculus.  The
identification holds by definition; it is recorded because the elaborator does not perform the
unfolding on its own.

It is stated at arbitrary algebraic spaces and an arbitrary morphism on purpose.  Instantiating
it is a single delta step, whereas asking for the same equation directly at a concrete morphism
into an action space makes the elaborator unfold that action space through the chosen limit cone
of the fibre product, and then the composition of
`AlgebraicGeometry.Space.Modules`, which does not terminate within the budget. -/
theorem transitionReindex_eq_modulePullbackReindex {U V W : AlgebraicSpaces 𝒞 S hS}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F) (f : W ⟶ V) :
    transitionReindex 𝒞 S hS F α f = modulePullbackReindex f α :=
  rfl

/-- The reindexing of an equivariant transition morphism of Stacks 043T along a test morphism is
the reindexing of Stacks 03LU along the induced morphism of algebraic spaces. -/
theorem equivariantPullbackTransition_eq_modulePullbackReindex
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) X hX).1
      (underlyingSpace (hS := hS) X hX).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G X hX A)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).obj F)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    equivariantPullbackTransition G X hX A F α hT w =
      modulePullbackReindex
        (asSpaceHom hT (actionSpace (hB := hB) G X hX).property w) α :=
  transitionReindex_eq_modulePullbackReindex F α
    (actionSpaceHom (hB := hB) G X hX hT w)

/-- The canonical identification of the inverse images along two equal morphisms is the
transport along the corresponding equality of functors. -/
theorem pullbackTransport_eq_eqToHom {T X : AlgebraicSpaces 𝒞 S hS}
    (F : Modules.{u, u} 𝒞 S hS X.1 X.2) {f g : T ⟶ X} (h : f = g) :
    pullbackTransport F h =
      eqToHom (congrArg (fun k : T ⟶ X => (modulePullback 𝒞 S hS k).obj F) h) :=
  rfl

/-! ### The pulled-back transition morphism -/

variable (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
  (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
  (AX : ModObj G.obj.X X) (AY : ModObj G.obj.X Y)

/-- Reindexing an equivariant transition morphism on `Y` along the morphism
`1_G × f : G ×_B X ⟶ G ×_B Y` of action spaces induced by `f : X ⟶ Y`. -/
theorem equivariantPullbackTransition_lift (f : X ⟶ Y)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F) :
    equivariantPullbackTransition G Y hY AY F α (actionSpace (hB := hB) G X hX).property
        (lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) =
      modulePullbackReindex (actionMap (hB := hB) G hX hY f)
        (a := action (hB := hB) G Y hY AY) (b := projection (hB := hB) G Y hY) (M := F) α :=
  transitionReindex_eq_modulePullbackReindex F α (actionMap (hB := hB) G hX hY f)

/-- The reindexing of a transition morphism `α` on `Y` along `1_G × f`, with the transports
across the action square and the projection square of `f` on either side.  It is a morphism
between the inverse images of the module along the two composites
`G ×_B X ⟶ G ×_B Y ⟶ Y`. -/
def equivariantReindexTransport (f : X ⟶ Y)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F) :
    (modulePullback 𝒞 S hS
        (action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f)).obj F ⟶
      (modulePullback 𝒞 S hS
        (projection (hB := hB) G X hX ≫ asSpaceHom hX hY f)).obj F :=
  comp₃ (pullbackTransport F ha)
    (modulePullbackReindex (actionMap (hB := hB) G hX hY f)
      (a := action (hB := hB) G Y hY AY) (b := projection (hB := hB) G Y hY) (M := F) α)
    (pullbackTransport F hp.symm)

/-- The reindexing of a transition morphism along `1_G × f` with its two transports is the
triple composite of the three, as a named operation. -/
theorem equivariantReindexTransport_eq (f : X ⟶ Y)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F) :
    equivariantReindexTransport G hX hY AX AY f ha hp F α =
      comp₃ (pullbackTransport F ha)
        (modulePullbackReindex (actionMap (hB := hB) G hX hY f)
          (a := action (hB := hB) G Y hY AY) (b := projection (hB := hB) G Y hY) (M := F) α)
        (pullbackTransport F hp.symm) :=
  rfl

/-- The reindexing of a transition morphism along `1_G × f` with its two transports, presented
as a chain of `≫`. -/
theorem equivariantReindexTransport_eq_comp (f : X ⟶ Y)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F) :
    equivariantReindexTransport G hX hY AX AY f ha hp F α =
      pullbackTransport F ha ≫
        modulePullbackReindex (actionMap (hB := hB) G hX hY f) α ≫
        pullbackTransport F hp.symm :=
  (equivariantReindexTransport_eq G hX hY AX AY f ha hp F α).trans (comp₃_eq _ _ _)

/-- The transition morphism of the inverse image of an equivariant quasi-coherent module along
an equivariant morphism `f : X ⟶ Y`: the reindexing of the given transition along `1_G × f`,
with the comparisons of Stacks 03LU and the two squares of `f` on either side. -/
def equivariantModulePullbackTransition (f : X ⟶ Y)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F) :
    (modulePullback 𝒞 S hS (action (hB := hB) G X hX AX)).obj
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).obj
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) :=
  modulePullbackUnflatten (asSpaceHom hX hY f)
    (a := action (hB := hB) G X hX AX) (b := projection (hB := hB) G X hX) (M := F)
    (equivariantReindexTransport G hX hY AX AY f ha hp F α)

/-- The transition morphism of `f^*ℱ` is the unflattening of the reindexing of the original
transition along `1_G × f`. -/
theorem equivariantModulePullbackTransition_eq (f : X ⟶ Y)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F) :
    equivariantModulePullbackTransition G hX hY AX AY f ha hp F α =
      modulePullbackUnflatten (asSpaceHom hX hY f)
        (a := action (hB := hB) G X hX AX) (b := projection (hB := hB) G X hX) (M := F)
        (equivariantReindexTransport G hX hY AX AY f ha hp F α) :=
  rfl

/-- Flattening the pulled-back transition morphism along `f` recovers the reindexing of the
original transition along `1_G × f`. -/
theorem modulePullbackFlatten_equivariantModulePullbackTransition (f : X ⟶ Y)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F) :
    modulePullbackFlatten (asSpaceHom hX hY f)
        (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α) =
      pullbackTransport F ha ≫
        modulePullbackReindex (actionMap (hB := hB) G hX hY f) α ≫
        pullbackTransport F hp.symm :=
  ((congrArg (modulePullbackFlatten (asSpaceHom hX hY f))
        (equivariantModulePullbackTransition_eq G hX hY AX AY f ha hp F α)).trans
      (modulePullbackFlatten_unflatten _ _)).trans
    (equivariantReindexTransport_eq_comp G hX hY AX AY f ha hp F α)

end AlgebraicGeometry.Space

end
