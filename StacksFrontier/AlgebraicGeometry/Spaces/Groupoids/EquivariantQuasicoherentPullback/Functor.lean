module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback.NamedFlattening
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback functor on equivariant quasi-coherent modules

Let `G` be a group algebraic space over `B` acting on `X` and `Y`, and `f : X ⟶ Y` an
equivariant morphism.  This file reads the two squares of `f` along a test object over the
action space, proves the unit law, the naturality and the cocycle law for the transition
morphism of the inverse image, and assembles the pullback functor of **Stacks 043U**,
`AlgebraicGeometry.Space.equivariantQuasicoherentPullback`, with object map
`AlgebraicGeometry.Space.equivariantQuasicoherentPullbackObj`.

See `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback` for the
overview and the implementation notes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-! ### The equivariant situation -/

section Equivariant

variable {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}

section Squares

variable (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
  (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
  (f : X ⟶ Y)

/-- A test morphism into `G ×_B X`, followed by `1_G × f`, is the test morphism into `G ×_B Y`
obtained by applying `f` in the second coordinate. -/
theorem actionSpaceHom_comp_actionMap {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    actionSpaceHom (hB := hB) G X hX hT w ≫ actionMap (hB := hB) G hX hY f =
      actionSpaceHom (hB := hB) G Y hY hT
        (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) :=
  rfl

/-- `1_G × f` after a test morphism, followed by the action on `Y`. -/
theorem actionSpaceHom_comp_actionMap_comp_action (AY : ModObj G.obj.X Y) {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    actionSpaceHom (hB := hB) G X hX hT w ≫
        actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY =
      actionSpaceHom (hB := hB) G Y hY hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        action (hB := hB) G Y hY AY := by
  rw [← Category.assoc, actionSpaceHom_comp_actionMap G hX hY f hT w]

/-- `1_G × f` after a test morphism, followed by the projection of `Y`. -/
theorem actionSpaceHom_comp_actionMap_comp_projection {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    actionSpaceHom (hB := hB) G Y hY hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        projection (hB := hB) G Y hY =
      actionSpaceHom (hB := hB) G X hX hT w ≫
        actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY := by
  rw [← actionSpaceHom_comp_actionMap G hX hY f hT w, Category.assoc]

variable (AX : ModObj G.obj.X X) (AY : ModObj G.obj.X Y)

/-- The action square of an equivariant morphism, read along a test object over the action space
of `X`, with the composite `1_G × f` after the test morphism contracted. -/
theorem actionSpaceHom_action_square
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    actionSpaceHom (hB := hB) G X hX hT w ≫
        action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionSpaceHom (hB := hB) G Y hY hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        action (hB := hB) G Y hY AY := by
  rw [← actionSpaceHom_comp_actionMap G hX hY f hT w, ha, Category.assoc]

/-- The projection square of a morphism over `B`, read along a test object over the action space
of `X`, with the composite `1_G × f` after the test morphism contracted. -/
theorem actionSpaceHom_projection_square
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    actionSpaceHom (hB := hB) G Y hY hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        projection (hB := hB) G Y hY =
      actionSpaceHom (hB := hB) G X hX hT w ≫
        projection (hB := hB) G X hX ≫ asSpaceHom hX hY f := by
  rw [← actionSpaceHom_comp_actionMap G hX hY f hT w, hp, Category.assoc]

/-- **The reindexing along a test morphism of the pulled-back transition morphism, flattened, is
the reindexing of the given transition morphism along the pushed test morphism**, between the two
canonical identifications of equal composites.

This is the identity the cocycle and unit laws of the inverse image of an equivariant
quasi-coherent module reduce to, and it is
`AlgebraicGeometry.Space.modulePullbackFlatten_reindex_conjugate` at the action morphism, the
projection and `1_G × f`. -/
theorem modulePullbackFlatten_equivariantConjugate
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    modulePullbackFlatten (asSpaceHom hX hY f)
        (modulePullbackReindex (actionSpaceHom (hB := hB) G X hX hT w)
          ((modulePullbackCompIso 𝒞 S hS (action (hB := hB) G X hX AX)
                (asSpaceHom hX hY f)).hom.app F ≫
            pullbackTransport F ha ≫
            modulePullbackReindex (actionMap (hB := hB) G hX hY f) α ≫
            pullbackTransport F hp.symm ≫
            (modulePullbackCompIso 𝒞 S hS (projection (hB := hB) G X hX)
              (asSpaceHom hX hY f)).inv.app F)) =
      pullbackTransport F (actionSpaceHom_action_square G hX hY f AX AY ha hT w) ≫
        equivariantPullbackTransition G Y hY AY F α hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        pullbackTransport F (actionSpaceHom_projection_square G hX hY f hp hT w) :=
  (modulePullbackFlatten_reindex_conjugate hassoc (asSpaceHom hX hY f)
      (actionMap (hB := hB) G hX hY f) ha hp F α
      (actionSpaceHom (hB := hB) G X hX hT w)
      (actionSpaceHom (hB := hB) G Y hY hT
        (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)))
      (actionSpaceHom_comp_actionMap G hX hY f hT w)
      (actionSpaceHom_action_square G hX hY f AX AY ha hT w)
      (actionSpaceHom_projection_square G hX hY f hp hT w)).trans
    (comp₃_congr rfl
      (equivariantPullbackTransition_eq_modulePullbackReindex G Y hY AY F α hT
        (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))).symm rfl)

end Squares

/-! ### The inverse image of an equivariant quasi-coherent module -/

section Pullback

variable (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
  (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
  (f : X ⟶ Y) (AX : ModObj G.obj.X X) (AY : ModObj G.obj.X Y)
  (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
    actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
  (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
    actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
  (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
    (underlyingSpace (hS := hS) Y hY).2)
  (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
    (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F)

/-- **The transition morphism of the inverse image, reindexed along a test morphism `w` into
`G ×_B X` and flattened along `f`, is the reindexing of the given transition morphism along `w`
followed by `1_G × f`**, between the two squares of `f` read at `w`.

This is the shape in which the cocycle and unit laws of the inverse image are verified: both
sides of each law are flattened along `f`, where they become the corresponding sides of the law
for the given module at the test morphisms pushed along `1_G × f`, and flattening is injective
(`AlgebraicGeometry.Space.modulePullbackFlatten_injective`). -/
theorem modulePullbackFlatten_equivariantPullbackTransition
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    modulePullbackFlatten (asSpaceHom hX hY f)
        (equivariantPullbackTransition G X hX AX
          ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F)
          ((modulePullbackCompIso 𝒞 S hS (action (hB := hB) G X hX AX)
                (asSpaceHom hX hY f)).hom.app F ≫
            pullbackTransport F ha ≫
            modulePullbackReindex (actionMap (hB := hB) G hX hY f) α ≫
            pullbackTransport F hp.symm ≫
            (modulePullbackCompIso 𝒞 S hS (projection (hB := hB) G X hX)
              (asSpaceHom hX hY f)).inv.app F) hT w) =
      pullbackTransport F (actionSpaceHom_action_square G hX hY f AX AY ha hT w) ≫
        equivariantPullbackTransition G Y hY AY F α hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        pullbackTransport F (actionSpaceHom_projection_square G hX hY f hp hT w) :=
  (congrArg (fun x => modulePullbackFlatten (asSpaceHom hX hY f) x)
      (equivariantPullbackTransition_eq_modulePullbackReindex G X hX AX
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) _ hT w)).trans
    (modulePullbackFlatten_equivariantConjugate G hX hY f AX AY hassoc ha hp F α hT w)

/-- A transition morphism on `f^*ℱ` whose flattening along `f` is the pushed transition morphism of
`ℱ`, read at a test morphism in the unit section, is the canonical transport. -/
private theorem unit_of_flatten_eq
    (hunitY : ∀ {T' : Over B} (hT' : IsAlgebraicSpace 𝒞 S hS T'.left) (v : T' ⟶ G.obj.X ⊗ Y),
      (v ≫ fst G.obj.X Y = toUnit T' ≫ η[G.obj.X]) →
      (hv : actionSpaceHom (hB := hB) G Y hY hT' v ≫ action (hB := hB) G Y hY AY =
        actionSpaceHom (hB := hB) G Y hY hT' v ≫ projection (hB := hB) G Y hY) →
      equivariantPullbackTransition G Y hY AY F α hT' v = pullbackTransport F hv)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X)
    (hunit : w ≫ fst G.obj.X X = toUnit T ≫ η[G.obj.X])
    (h : actionSpaceHom (hB := hB) G X hX hT w ≫ action (hB := hB) G X hX AX =
      actionSpaceHom (hB := hB) G X hX hT w ≫ projection (hB := hB) G X hX)
    (β : (modulePullback 𝒞 S hS (action (hB := hB) G X hX AX)).obj
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).obj
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F))
    (hflatten : modulePullbackFlatten (asSpaceHom hX hY f)
        (equivariantPullbackTransition G X hX AX
          ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) β hT w) =
      pullbackTransport F (actionSpaceHom_action_square G hX hY f AX AY ha hT w) ≫
        equivariantPullbackTransition G Y hY AY F α hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        pullbackTransport F (actionSpaceHom_projection_square G hX hY f hp hT w)) :
    equivariantPullbackTransition G X hX AX
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) β hT w =
      pullbackTransport ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) h :=
  have hunit' : (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ fst G.obj.X Y =
      toUnit T ≫ η[G.obj.X] := by
    rw [Category.assoc, lift_fst]; exact hunit
  have hflat : actionSpaceHom (hB := hB) G X hX hT w ≫
        action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionSpaceHom (hB := hB) G X hX hT w ≫
        projection (hB := hB) G X hX ≫ asSpaceHom hX hY f :=
    congrArg (· ≫ asSpaceHom hX hY f) h
  have hv : actionSpaceHom (hB := hB) G Y hY hT
        (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ action (hB := hB) G Y hY AY =
      actionSpaceHom (hB := hB) G Y hY hT
        (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ projection (hB := hB) G Y hY :=
    (actionSpaceHom_action_square G hX hY f AX AY ha hT w).symm.trans
      (hflat.trans (actionSpaceHom_projection_square G hX hY f hp hT w).symm)
  have hmid : actionSpaceHom (hB := hB) G Y hY hT
        (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ action (hB := hB) G Y hY AY =
      actionSpaceHom (hB := hB) G X hX hT w ≫
        projection (hB := hB) G X hX ≫ asSpaceHom hX hY f :=
    hv.trans (actionSpaceHom_projection_square G hX hY f hp hT w)
  modulePullbackFlatten_injective (asSpaceHom hX hY f)
    (hflatten.trans
      ((comp₃_congr rfl
            (hunitY hT (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) hunit' hv) rfl).trans
        ((comp₂_congr rfl
              (pullbackTransport_comp F hv
                (actionSpaceHom_projection_square G hX hY f hp hT w) hmid)).trans
          ((pullbackTransport_comp F
                (actionSpaceHom_action_square G hX hY f AX AY ha hT w) hmid hflat).trans
            (modulePullbackFlatten_pullbackTransport (asSpaceHom hX hY f) h F hflat).symm))))

/-- **The unit law for the transition morphism of the inverse image.**  Flattened along `f`, it
is the unit law for the given module at the test morphism pushed along `1_G × f`, which lands in
the unit section because `1_G × f` is the identity on the first coordinate. -/
theorem equivariantPullbackConjugate_unit (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    (hunitY : ∀ {T' : Over B} (hT' : IsAlgebraicSpace 𝒞 S hS T'.left) (v : T' ⟶ G.obj.X ⊗ Y),
      (v ≫ fst G.obj.X Y = toUnit T' ≫ η[G.obj.X]) →
      (hv : actionSpaceHom (hB := hB) G Y hY hT' v ≫ action (hB := hB) G Y hY AY =
        actionSpaceHom (hB := hB) G Y hY hT' v ≫ projection (hB := hB) G Y hY) →
      equivariantPullbackTransition G Y hY AY F α hT' v = pullbackTransport F hv)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X)
    (hunit : w ≫ fst G.obj.X X = toUnit T ≫ η[G.obj.X])
    (h : actionSpaceHom (hB := hB) G X hX hT w ≫ action (hB := hB) G X hX AX =
      actionSpaceHom (hB := hB) G X hX hT w ≫ projection (hB := hB) G X hX) :
    equivariantPullbackTransition G X hX AX
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F)
        ((modulePullbackCompIso 𝒞 S hS (action (hB := hB) G X hX AX)
              (asSpaceHom hX hY f)).hom.app F ≫
          pullbackTransport F ha ≫
          modulePullbackReindex (actionMap (hB := hB) G hX hY f) α ≫
          pullbackTransport F hp.symm ≫
          (modulePullbackCompIso 𝒞 S hS (projection (hB := hB) G X hX)
            (asSpaceHom hX hY f)).inv.app F) hT w =
      pullbackTransport ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) h :=
  unit_of_flatten_eq G hX hY f AX AY ha hp F α hunitY hT w hunit h _
    (modulePullbackFlatten_equivariantPullbackTransition G hX hY f AX AY ha hp F α hassoc hT w)

/-- **The transition morphism of the inverse image, reindexed along a test morphism `w` into
`G ×_B X` and flattened along `f`, is the reindexing of the given transition morphism along `w`
followed by `1_G × f`**, between the two squares of `f` read at `w`.

This is `AlgebraicGeometry.Space.modulePullbackFlatten_reindex_of_flatten` at the action
morphism, the projection and `1_G × f`. -/
theorem modulePullbackFlatten_reindex_equivariantModulePullbackTransition
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    modulePullbackFlatten (asSpaceHom hX hY f)
        (modulePullbackReindex (actionSpaceHom (hB := hB) G X hX hT w)
          (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α)) =
      pullbackTransport F (actionSpaceHom_action_square G hX hY f AX AY ha hT w) ≫
        modulePullbackReindex (actionSpaceHom (hB := hB) G Y hY hT
            (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))) α ≫
        pullbackTransport F (actionSpaceHom_projection_square G hX hY f hp hT w) :=
  modulePullbackFlatten_reindex_of_flatten (asSpaceHom hX hY f)
    (actionMap (hB := hB) G hX hY f) F α
    (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α) hassoc
    (modulePullbackFlatten_equivariantModulePullbackTransition G hX hY AX AY f ha hp F α)
    (actionSpaceHom (hB := hB) G X hX hT w)
    (actionSpaceHom (hB := hB) G Y hY hT (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)))
    (actionSpaceHom_comp_actionMap G hX hY f hT w)
    (actionSpaceHom_action_square G hX hY f AX AY ha hT w)
    (actionSpaceHom_projection_square G hX hY f hp hT w)

/-- **The transition morphism of the inverse image, reindexed along a test morphism and
flattened along `f`, is the reindexing of the given transition morphism along the pushed test
morphism**, both read with `AlgebraicGeometry.Space.equivariantPullbackTransition`. -/
theorem modulePullbackFlatten_equivariantModulePullbackTransition_at
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X) :
    modulePullbackFlatten (asSpaceHom hX hY f)
        (equivariantPullbackTransition G X hX AX
          ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F)
          (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α) hT w) =
      pullbackTransport F (actionSpaceHom_action_square G hX hY f AX AY ha hT w) ≫
        equivariantPullbackTransition G Y hY AY F α hT
          (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        pullbackTransport F (actionSpaceHom_projection_square G hX hY f hp hT w) :=
  ((congrArg (modulePullbackFlatten (asSpaceHom hX hY f))
        (equivariantPullbackTransition_eq_modulePullbackReindex G X hX AX
          ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F)
          (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α) hT w)).trans
      (modulePullbackFlatten_reindex_equivariantModulePullbackTransition G hX hY f AX AY
        ha hp F α hassoc hT w)).trans
    (comp₃_congr rfl
      (equivariantPullbackTransition_eq_modulePullbackReindex G Y hY AY F α hT
        (w ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))).symm rfl)

/-- **The unit law for the transition morphism of the inverse image.**  Flattened along `f`, it
is the unit law for the given module at the test morphism pushed along `1_G × f`, which lands in
the unit section because `1_G × f` is the identity on the first coordinate. -/
theorem equivariantModulePullbackTransition_unit
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    (hunitY : ∀ {T' : Over B} (hT' : IsAlgebraicSpace 𝒞 S hS T'.left) (v : T' ⟶ G.obj.X ⊗ Y),
      (v ≫ fst G.obj.X Y = toUnit T' ≫ η[G.obj.X]) →
      (hv : actionSpaceHom (hB := hB) G Y hY hT' v ≫ action (hB := hB) G Y hY AY =
        actionSpaceHom (hB := hB) G Y hY hT' v ≫ projection (hB := hB) G Y hY) →
      equivariantPullbackTransition G Y hY AY F α hT' v = pullbackTransport F hv)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (w : T ⟶ G.obj.X ⊗ X)
    (hunit : w ≫ fst G.obj.X X = toUnit T ≫ η[G.obj.X])
    (h : actionSpaceHom (hB := hB) G X hX hT w ≫ action (hB := hB) G X hX AX =
      actionSpaceHom (hB := hB) G X hX hT w ≫ projection (hB := hB) G X hX) :
    equivariantPullbackTransition G X hX AX
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F)
        (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α) hT w =
      pullbackTransport ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F) h :=
  unit_of_flatten_eq G hX hY f AX AY ha hp F α hunitY hT w hunit h _
    (modulePullbackFlatten_equivariantModulePullbackTransition_at G hX hY f AX AY
      ha hp F α hassoc hT w)

/-- **The transition morphism of the inverse image is natural in the equivariant module.**  A
morphism of modules on `Y` intertwining two transition morphisms intertwines their inverse
images. -/
theorem equivariantModulePullbackTransition_naturality
    {N : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2}
    (αN : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj N ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj N) (φ : F ⟶ N)
    (hφ : α ≫ (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).map φ =
      (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).map φ ≫ αN) :
    equivariantModulePullbackTransition G hX hY AX AY f ha hp F α ≫
        (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).map
          ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).map φ) =
      (modulePullback 𝒞 S hS (action (hB := hB) G X hX AX)).map
          ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).map φ) ≫
        equivariantModulePullbackTransition G hX hY AX AY f ha hp N αN :=
  (comp₂_congr (equivariantModulePullbackTransition_eq G hX hY AX AY f ha hp F α) rfl).trans
    ((modulePullbackUnflatten_naturality (asSpaceHom hX hY f) φ
          (equivariantReindexTransport G hX hY AX AY f ha hp F α)
          (equivariantReindexTransport G hX hY AX AY f ha hp N αN)
          (((comp₂_congr (equivariantReindexTransport_eq_comp G hX hY AX AY f ha hp F α)
                  rfl).trans
              (transportReindexTransport_naturality (actionMap (hB := hB) G hX hY f) ha hp.symm
                α αN φ hφ)).trans
            (comp₂_congr rfl
              (equivariantReindexTransport_eq_comp G hX hY AX AY f ha hp N αN).symm))).trans
      (comp₂_congr rfl
        (equivariantModulePullbackTransition_eq G hX hY AX AY f ha hp N αN).symm))

end Pullback

/-! ### The cocycle law -/

section Cocycle

/-- The right-hand side of the cocycle condition of Stacks 043T, as a chain of `≫`. -/
theorem equivariantTransitionComposite_eq_comp (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (X : Over B) (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) X hX).1
      (underlyingSpace (hS := hS) X hX).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G X hX A)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).obj F)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (p q r : T ⟶ G.obj.X ⊗ X)
    (hmiddle : actionSpaceHom (hB := hB) G X hX hT p ≫ projection (hB := hB) G X hX =
      actionSpaceHom (hB := hB) G X hX hT q ≫ action (hB := hB) G X hX A)
    (htarget : actionSpaceHom (hB := hB) G X hX hT r ≫ action (hB := hB) G X hX A =
      actionSpaceHom (hB := hB) G X hX hT p ≫ action (hB := hB) G X hX A)
    (hsource : actionSpaceHom (hB := hB) G X hX hT r ≫ projection (hB := hB) G X hX =
      actionSpaceHom (hB := hB) G X hX hT q ≫ projection (hB := hB) G X hX) :
    equivariantTransitionComposite G X hX A F α hT p q r hmiddle htarget hsource =
      pullbackTransport F htarget ≫
        (modulePullbackReindex (actionSpaceHom (hB := hB) G X hX hT p) α ≫
          pullbackTransport F hmiddle ≫
          modulePullbackReindex (actionSpaceHom (hB := hB) G X hX hT q) α) ≫
        pullbackTransport F hsource.symm :=
  transitionComposite_eq_comp F α _ _ _ htarget hmiddle hsource

variable (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
  (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
  (f : X ⟶ Y) (AX : ModObj G.obj.X X) (AY : ModObj G.obj.X Y)

/-- **The cocycle law for the transition morphism of the inverse image.**  Flattened along `f`,
both sides are the corresponding sides of the cocycle law for the given module at the three test
morphisms pushed along `1_G × f`.

This is `AlgebraicGeometry.Space.modulePullbackReindex_cocycle_of_flatten` at the action
morphism, the projection and `1_G × f`, with the two sides of each law read through
`AlgebraicGeometry.Space.equivariantPullbackTransition_eq_modulePullbackReindex` and
`AlgebraicGeometry.Space.equivariantTransitionComposite_eq_comp`. -/
theorem equivariantModulePullbackTransition_cocycle
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) Y hY).1
      (underlyingSpace (hS := hS) Y hY).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G Y hY AY)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G Y hY)).obj F)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (p q r : T ⟶ G.obj.X ⊗ X)
    (hmiddle : actionSpaceHom (hB := hB) G X hX hT p ≫ projection (hB := hB) G X hX =
      actionSpaceHom (hB := hB) G X hX hT q ≫ action (hB := hB) G X hX AX)
    (htarget : actionSpaceHom (hB := hB) G X hX hT r ≫ action (hB := hB) G X hX AX =
      actionSpaceHom (hB := hB) G X hX hT p ≫ action (hB := hB) G X hX AX)
    (hsource : actionSpaceHom (hB := hB) G X hX hT r ≫ projection (hB := hB) G X hX =
      actionSpaceHom (hB := hB) G X hX hT q ≫ projection (hB := hB) G X hX)
    (hmiddleY : actionSpaceHom (hB := hB) G Y hY hT
          (p ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ projection (hB := hB) G Y hY =
      actionSpaceHom (hB := hB) G Y hY hT
          (q ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ action (hB := hB) G Y hY AY)
    (htargetY : actionSpaceHom (hB := hB) G Y hY hT
          (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ action (hB := hB) G Y hY AY =
      actionSpaceHom (hB := hB) G Y hY hT
          (p ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ action (hB := hB) G Y hY AY)
    (hsourceY : actionSpaceHom (hB := hB) G Y hY hT
          (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ projection (hB := hB) G Y hY =
      actionSpaceHom (hB := hB) G Y hY hT
          (q ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ projection (hB := hB) G Y hY)
    (hcocY : equivariantPullbackTransition G Y hY AY F α hT
          (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) =
      equivariantTransitionComposite G Y hY AY F α hT
        (p ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))
        (q ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))
        (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) hmiddleY htargetY hsourceY) :
    equivariantPullbackTransition G X hX AX
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F)
        (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α) hT r =
      equivariantTransitionComposite G X hX AX
        ((modulePullback 𝒞 S hS (asSpaceHom hX hY f)).obj F)
        (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α) hT p q r
        hmiddle htarget hsource :=
  have hcocY' : modulePullbackReindex (actionSpaceHom (hB := hB) G Y hY hT
        (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))) α =
      pullbackTransport F htargetY ≫
        (modulePullbackReindex (actionSpaceHom (hB := hB) G Y hY hT
            (p ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))) α ≫
          pullbackTransport F hmiddleY ≫
          modulePullbackReindex (actionSpaceHom (hB := hB) G Y hY hT
            (q ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))) α) ≫
        pullbackTransport F hsourceY.symm :=
    ((equivariantPullbackTransition_eq_modulePullbackReindex G Y hY AY F α hT
            (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))).symm.trans hcocY).trans
      (equivariantTransitionComposite_eq_comp G Y hY AY F α hT _ _ _ hmiddleY htargetY
        hsourceY)
  (equivariantPullbackTransition_eq_modulePullbackReindex G X hX AX _ _ hT r).trans
    ((modulePullbackReindex_cocycle_of_flatten hassoc (asSpaceHom hX hY f)
          (actionMap (hB := hB) G hX hY f) F α
          (equivariantModulePullbackTransition G hX hY AX AY f ha hp F α)
          (modulePullbackFlatten_equivariantModulePullbackTransition G hX hY AX AY f ha hp
            F α)
          (actionSpaceHom (hB := hB) G X hX hT p) (actionSpaceHom (hB := hB) G X hX hT q)
          (actionSpaceHom (hB := hB) G X hX hT r)
          (actionSpaceHom (hB := hB) G Y hY hT
            (p ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)))
          (actionSpaceHom (hB := hB) G Y hY hT
            (q ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)))
          (actionSpaceHom (hB := hB) G Y hY hT
            (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)))
          (actionSpaceHom_comp_actionMap G hX hY f hT p)
          (actionSpaceHom_comp_actionMap G hX hY f hT q)
          (actionSpaceHom_comp_actionMap G hX hY f hT r)
          htarget hmiddle hsource htargetY hmiddleY hsourceY hcocY').trans
      (equivariantTransitionComposite_eq_comp G X hX AX _ _ hT p q r
        hmiddle htarget hsource).symm)

end Cocycle

/-! ### The pullback functor of Stacks 043U -/

section Functor

variable (G : GroupAlgebraicSpace 𝒞 S hS B hB) {X Y : Over B}
  (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
  (f : X ⟶ Y)

/-- A test morphism pushed along `1_G × f` has the same first coordinate. -/
theorem comp_lift_comp_fst {T : Over B} (u : T ⟶ G.obj.X ⊗ X) :
    (u ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ fst G.obj.X Y = u ≫ fst G.obj.X X := by
  rw [Category.assoc, lift_fst]

/-- `f` carries the multiplication condition of the cocycle law on `X` to the one on `Y`. -/
theorem comp_lift_comp_fst_mul {T : Over B} {p q r : T ⟶ G.obj.X ⊗ X}
    (hmul : r ≫ fst G.obj.X X = lift (p ≫ fst G.obj.X X) (q ≫ fst G.obj.X X) ≫ μ[G.obj.X]) :
    (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ fst G.obj.X Y =
      lift ((p ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ fst G.obj.X Y)
          ((q ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ fst G.obj.X Y) ≫
        μ[G.obj.X] := by
  simp only [comp_lift_comp_fst]
  exact hmul

/-- The projection square of `f`, carrying a matching of projections on `X` to one on `Y`. -/
theorem actionSpaceHom_projection_square_transfer
    (hp : projection (hB := hB) G X hX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ projection (hB := hB) G Y hY)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (u v : T ⟶ G.obj.X ⊗ X)
    (h : actionSpaceHom (hB := hB) G X hX hT u ≫ projection (hB := hB) G X hX =
      actionSpaceHom (hB := hB) G X hX hT v ≫ projection (hB := hB) G X hX) :
    actionSpaceHom (hB := hB) G Y hY hT
          (u ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ projection (hB := hB) G Y hY =
      actionSpaceHom (hB := hB) G Y hY hT
          (v ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ projection (hB := hB) G Y hY := by
  rw [actionSpaceHom_projection_square G hX hY f hp hT u,
    actionSpaceHom_projection_square G hX hY f hp hT v, ← Category.assoc,
    ← Category.assoc, h]

variable [AX : ModObj G.obj.X X] [AY : ModObj G.obj.X Y]

/-- **The equivariance of `f`**, read as the compatibility of `1_G × f` with the two actions. -/
theorem lift_comp_smul [hf : IsModHom G.obj.X f] :
    lift (fst G.obj.X X) (snd G.obj.X X ≫ f) ≫ ModObj.smul (M := G.obj.X) (X := Y) =
      ModObj.smul (M := G.obj.X) (X := X) ≫ f :=
  hf.smul_hom.symm

/-- `f` carries the composability condition of the cocycle law on `X` to the one on `Y`. -/
theorem comp_lift_comp_snd_smul [IsModHom G.obj.X f] {T : Over B} {u v : T ⟶ G.obj.X ⊗ X}
    (h : u ≫ snd G.obj.X X = v ≫ ModObj.smul (M := G.obj.X) (X := X)) :
    (u ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ snd G.obj.X Y =
      (v ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫
        ModObj.smul (M := G.obj.X) (X := Y) := by
  rw [Category.assoc, lift_snd, Category.assoc, lift_comp_smul G f, ← Category.assoc,
    ← Category.assoc, h]

/-- The action square of `f`, carrying a matching of action morphisms on `X` to one on `Y`. -/
theorem actionSpaceHom_action_square_transfer
    (ha : action (hB := hB) G X hX AX ≫ asSpaceHom hX hY f =
      actionMap (hB := hB) G hX hY f ≫ action (hB := hB) G Y hY AY)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (u v : T ⟶ G.obj.X ⊗ X)
    (h : actionSpaceHom (hB := hB) G X hX hT u ≫ action (hB := hB) G X hX AX =
      actionSpaceHom (hB := hB) G X hX hT v ≫ action (hB := hB) G X hX AX) :
    actionSpaceHom (hB := hB) G Y hY hT
          (u ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ action (hB := hB) G Y hY AY =
      actionSpaceHom (hB := hB) G Y hY hT
          (v ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f)) ≫ action (hB := hB) G Y hY AY := by
  rw [← actionSpaceHom_action_square G hX hY f AX AY ha hT u,
    ← actionSpaceHom_action_square G hX hY f AX AY ha hT v, ← Category.assoc,
    ← Category.assoc, h]

variable [IsModHom G.obj.X f]

/-- **The inverse image of a `G`-equivariant quasi-coherent module along an equivariant
morphism**: the inverse image of the underlying quasi-coherent module, with the reindexing of
the given transition morphism along `1_G × f`. -/
@[sga "3 I 6.3.1" "special case"]
def equivariantQuasicoherentPullbackObj
    (M : EquivariantQuasicoherentModule (hB := hB) G Y hY AY) :
    EquivariantQuasicoherentModule (hB := hB) G X hX AX where
  F := (quasicoherentPullbackFunctor 𝒞 S hS (asSpaceHom hX hY f)).obj M.F
  alpha := equivariantModulePullbackTransition G hX hY AX AY f
    (action_comp_asSpaceHom G hX hY f) (projection_comp_asSpaceHom G hX hY f) M.F.obj M.alpha
  cocycle := fun hT p q r hcomp hmul htarget hsource =>
    equivariantModulePullbackTransition_cocycle G hX hY f AX AY (modulePullbackCompIsoAssoc 𝒞 S hS)
      (action_comp_asSpaceHom G hX hY f) (projection_comp_asSpaceHom G hX hY f)
      M.F.obj M.alpha hT p q r _ htarget hsource _ _ _
      (M.cocycle hT (p ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))
        (q ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))
        (r ≫ lift (fst G.obj.X X) (snd G.obj.X X ≫ f))
        (comp_lift_comp_snd_smul G f hcomp) (comp_lift_comp_fst_mul G f hmul)
        (actionSpaceHom_action_square_transfer G hX hY f
          (action_comp_asSpaceHom G hX hY f) hT r p htarget)
        (actionSpaceHom_projection_square_transfer G hX hY f
          (projection_comp_asSpaceHom G hX hY f) hT r q hsource))
  unit := fun hT w hunit h =>
    equivariantModulePullbackTransition_unit G hX hY f AX AY
      (action_comp_asSpaceHom G hX hY f) (projection_comp_asSpaceHom G hX hY f)
      M.F.obj M.alpha (modulePullbackCompIsoAssoc 𝒞 S hS) M.unit hT w hunit h

/-- **Stacks 043U.**  The inverse image along a `G`-equivariant morphism `f : X ⟶ Y` of
algebraic spaces over `B` is a functor from the `G`-equivariant quasi-coherent `𝒪_Y`-modules to
the `G`-equivariant quasi-coherent `𝒪_X`-modules: it sends `(ℱ, α)` to `f^*ℱ` with the
reindexing of `α` along `1_G × f`. -/
@[stacks 043U, sga "3 I 6.3.1" "special case"]
def equivariantQuasicoherentPullback :
    EquivariantQuasicoherentModule (hB := hB) G Y hY AY ⥤
      EquivariantQuasicoherentModule (hB := hB) G X hX AX where
  obj M := equivariantQuasicoherentPullbackObj G hX hY f M
  map {M N} φ :=
    { hom := (modulePullback 𝒞 S hS (asSpaceHom hX hY f)).map φ.hom
      comm := equivariantModulePullbackTransition_naturality G hX hY f AX AY
        (action_comp_asSpaceHom G hX hY f) (projection_comp_asSpaceHom G hX hY f)
        M.F.obj M.alpha N.alpha φ.hom φ.comm }
  map_id M := by
    refine EquivariantQuasicoherentModule.Hom.ext ?_
    exact (modulePullback 𝒞 S hS (asSpaceHom hX hY f)).map_id M.F.obj
  map_comp φ ψ := by
    refine EquivariantQuasicoherentModule.Hom.ext ?_
    exact (modulePullback 𝒞 S hS (asSpaceHom hX hY f)).map_comp φ.hom ψ.hom

/-- The underlying quasi-coherent module of the inverse image of an equivariant quasi-coherent
module is the inverse image of its underlying module. -/
theorem equivariantQuasicoherentPullback_obj_F
    (M : EquivariantQuasicoherentModule (hB := hB) G Y hY AY) :
    ((equivariantQuasicoherentPullback G hX hY f).obj M).F =
      (quasicoherentPullbackFunctor 𝒞 S hS (asSpaceHom hX hY f)).obj M.F :=
  rfl

/-- The transition morphism of the inverse image of an equivariant quasi-coherent module is the
reindexing of the given one along `1_G × f`. -/
theorem equivariantQuasicoherentPullback_obj_alpha
    (M : EquivariantQuasicoherentModule (hB := hB) G Y hY AY) :
    ((equivariantQuasicoherentPullback G hX hY f).obj M).alpha =
      equivariantModulePullbackTransition G hX hY AX AY f
        (action_comp_asSpaceHom G hX hY f) (projection_comp_asSpaceHom G hX hY f)
        M.F.obj M.alpha :=
  rfl

/-- The morphism map of the inverse image of equivariant quasi-coherent modules is the inverse
image of the underlying morphism of modules. -/
theorem equivariantQuasicoherentPullback_map_hom
    {M N : EquivariantQuasicoherentModule (hB := hB) G Y hY AY} (φ : M ⟶ N) :
    ((equivariantQuasicoherentPullback G hX hY f).map φ).hom =
      (modulePullback 𝒞 S hS (asSpaceHom hX hY f)).map φ.hom :=
  rfl

end Functor

end Equivariant

end AlgebraicGeometry.Space

end
