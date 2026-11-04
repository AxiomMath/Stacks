module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Equivariant quasi-coherent modules

Let `G` be a group algebraic space over an algebraic space `B`, acting on an algebraic space `X`
over `B` through `a : G ×_B X ⟶ X`.  A `G`-equivariant quasi-coherent `𝒪_X`-module is a
quasi-coherent `𝒪_X`-module `ℱ` together with a morphism `α : a^*ℱ ⟶ pr₁^*ℱ` of
`𝒪_{G ×_B X}`-modules satisfying the cocycle condition on `G ×_B G ×_B X` and restricting to the
identity along the unit section.  This is Stacks 043T.  The cocycle and unit laws are stated
after an arbitrary base change: they quantify over an algebraic space `T` over `B` with morphisms
to the action space, and record the relations between those morphisms as hypotheses.

## Main definitions

* `AlgebraicGeometry.Space.actionSpaceHom` reads a morphism over `B` into `G ×_B X` as a
  morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.equivariantPullbackTransition` reindexes an equivariant transition
  morphism along a morphism of algebraic spaces over `B` into the action space, and
  `AlgebraicGeometry.Space.equivariantTransitionComposite` is the right-hand side of the
  cocycle condition.
* `AlgebraicGeometry.Space.EquivariantQuasicoherentModule` is **Stacks 043T**, with
  `AlgebraicGeometry.Space.EquivariantQuasicoherentModule.Hom` its morphisms.

## Main results

* `AlgebraicGeometry.Space.actionAt_eq_comp_action` and
  `AlgebraicGeometry.Space.projectionAt_eq_comp_projection`: the action morphism and the
  projection read along a test object are the action morphism and the projection after the test
  morphism.
* The cocycle and unit laws are fields of
  `AlgebraicGeometry.Space.EquivariantQuasicoherentModule`, and its morphisms form a category.

## References

* [Stacks Project, Tag 043T](https://stacks.math.columbia.edu/tag/043T)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}

/-- A morphism of algebraic spaces over `B` into the action space `G ×_B X`, read as a morphism
of algebraic spaces over `S`. -/
noncomputable abbrev actionSpaceHom (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (f : T ⟶ G.obj.X ⊗ X) :
    underlyingSpace (hS := hS) T hT ⟶ actionSpace (hB := hB) G X hX :=
  asSpaceHom hT (actionSpace (hB := hB) G X hX).property f

/-- The action morphism read along a test object over the action space is the action morphism
after the test morphism. -/
theorem actionAt_eq_comp_action (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X) {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (f : T ⟶ G.obj.X ⊗ X) :
    actionAt (hB := hB) G X hX A hT f =
      actionSpaceHom (hB := hB) G X hX hT f ≫ action (hB := hB) G X hX A :=
  rfl

/-- The projection read along a test object over the action space is the projection after the
test morphism. -/
theorem projectionAt_eq_comp_projection (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) {T : Over B}
    (hT : IsAlgebraicSpace 𝒞 S hS T.left) (f : T ⟶ G.obj.X ⊗ X) :
    projectionAt (hB := hB) G X hX hT f =
      actionSpaceHom (hB := hB) G X hX hT f ≫ projection (hB := hB) G X hX :=
  rfl

/-- An equivariant transition morphism `α : a^*ℱ ⟶ pr₁^*ℱ`, reindexed along a morphism `f` of
algebraic spaces over `B` into the action space: this is
`AlgebraicGeometry.Space.transitionReindex` at the action morphism and the projection, so the
inverse image of `α` along `f` with the composition isomorphisms of Stacks 03LU on either
side. -/
def equivariantPullbackTransition (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X)
    (F : Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) X hX).1
      (underlyingSpace (hS := hS) X hX).2)
    (α : (modulePullback 𝒞 S hS (action (hB := hB) G X hX A)).obj F ⟶
      (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).obj F)
    {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (f : T ⟶ G.obj.X ⊗ X) :
    (modulePullback 𝒞 S hS (actionSpaceHom (hB := hB) G X hX hT f ≫
        action (hB := hB) G X hX A)).obj F ⟶
      (modulePullback 𝒞 S hS (actionSpaceHom (hB := hB) G X hX hT f ≫
        projection (hB := hB) G X hX)).obj F :=
  transitionReindex 𝒞 S hS F α (actionSpaceHom (hB := hB) G X hX hT f)

/-- The right-hand side of the cocycle condition of Stacks 043T: the two reindexings of an
equivariant transition morphism along the two morphisms `p` and `q` out of a test object, with
the three identifications of equal composites on either side.  This is
`AlgebraicGeometry.Space.transitionComposite` at the action morphism and the projection. -/
def equivariantTransitionComposite (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X)
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
    (modulePullback 𝒞 S hS (actionSpaceHom (hB := hB) G X hX hT r ≫
        action (hB := hB) G X hX A)).obj F ⟶
      (modulePullback 𝒞 S hS (actionSpaceHom (hB := hB) G X hX hT r ≫
        projection (hB := hB) G X hX)).obj F :=
  transitionComposite 𝒞 S hS F α (actionSpaceHom (hB := hB) G X hX hT p)
    (actionSpaceHom (hB := hB) G X hX hT q) (actionSpaceHom (hB := hB) G X hX hT r)
    htarget hmiddle hsource

/-- A `G`-equivariant quasi-coherent `𝒪_X`-module for an action `A` of a group algebraic space
`G` over `B` on an algebraic space `X` over `B`: a quasi-coherent `𝒪_X`-module `ℱ` together with
a morphism `α : a^*ℱ ⟶ pr₁^*ℱ` of `𝒪_{G ×_B X}`-modules which satisfies the action cocycle
condition and is normalized along the unit section. -/
@[stacks 043T]
structure EquivariantQuasicoherentModule (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X) where
  /-- The underlying quasi-coherent module on `X`. -/
  F : QuasicoherentSheaves.{u, u} 𝒞 S hS X.left hX
  /-- The transition morphism from the action pullback to the projection pullback. -/
  alpha : (modulePullback 𝒞 S hS (action (hB := hB) G X hX A)).obj F.obj ⟶
    (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).obj F.obj
  /-- The cocycle condition, after an arbitrary base change: whenever `r` is the composite of
  `p` and `q` in the action groupoid, the reindexing of the transition along `r` is the
  composite of its reindexings along `p` and `q`. -/
  cocycle : ∀ {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left)
    (p q r : T ⟶ G.obj.X ⊗ X),
    (hcomp : p ≫ snd G.obj.X X =
      q ≫ (letI : ModObj G.obj.X X := A; ModObj.smul (M := G.obj.X) (X := X))) →
    (r ≫ fst G.obj.X X =
      lift (p ≫ fst G.obj.X X) (q ≫ fst G.obj.X X) ≫ μ[G.obj.X]) →
    (htarget : actionSpaceHom (hB := hB) G X hX hT r ≫ action (hB := hB) G X hX A =
      actionSpaceHom (hB := hB) G X hX hT p ≫ action (hB := hB) G X hX A) →
    (hsource : actionSpaceHom (hB := hB) G X hX hT r ≫ projection (hB := hB) G X hX =
      actionSpaceHom (hB := hB) G X hX hT q ≫ projection (hB := hB) G X hX) →
    equivariantPullbackTransition G X hX A F.obj alpha hT r =
      equivariantTransitionComposite G X hX A F.obj alpha hT p q r
        (by apply ObjectProperty.hom_ext; exact congrArg Over.Hom.left hcomp)
        htarget hsource
  /-- The unit condition, after an arbitrary base change: the reindexing of the transition along
  a morphism landing in the unit section is the identification of its two equal endpoints. -/
  unit : ∀ {T : Over B} (hT : IsAlgebraicSpace 𝒞 S hS T.left) (f : T ⟶ G.obj.X ⊗ X),
    (f ≫ fst G.obj.X X = toUnit T ≫ η[G.obj.X]) →
    (h : actionSpaceHom (hB := hB) G X hX hT f ≫ action (hB := hB) G X hX A =
      actionSpaceHom (hB := hB) G X hX hT f ≫ projection (hB := hB) G X hX) →
    equivariantPullbackTransition G X hX A F.obj alpha hT f = pullbackTransport F.obj h

namespace EquivariantQuasicoherentModule

variable {G : GroupAlgebraicSpace 𝒞 S hS B hB} {X : Over B}
  {hX : IsAlgebraicSpace 𝒞 S hS X.left} {A : ModObj G.obj.X X}

/-- A morphism of `G`-equivariant quasi-coherent modules: a morphism of the underlying
quasi-coherent modules on `X` which intertwines the two transition morphisms. -/
@[ext]
structure Hom (M N : EquivariantQuasicoherentModule (hB := hB) G X hX A) where
  /-- The underlying morphism of modules on `X`. -/
  hom : (show Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) X hX).1
      (underlyingSpace (hS := hS) X hX).2 from M.F.obj) ⟶
    (show Modules.{u, u} 𝒞 S hS (underlyingSpace (hS := hS) X hX).1
      (underlyingSpace (hS := hS) X hX).2 from N.F.obj)
  /-- Compatibility with the transition morphisms. -/
  comm : M.alpha ≫ (modulePullback 𝒞 S hS (projection (hB := hB) G X hX)).map hom =
    (modulePullback 𝒞 S hS (action (hB := hB) G X hX A)).map hom ≫ N.alpha

/-- `G`-equivariant quasi-coherent modules and the morphisms compatible with their transitions
form a category. -/
instance : Category (EquivariantQuasicoherentModule (hB := hB) G X hX A) where
  Hom := Hom
  id M := { hom := 𝟙 M.F.obj, comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, f.comm, Category.assoc,
          g.comm, ← Category.assoc] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

end EquivariantQuasicoherentModule

end AlgebraicGeometry.Space

end
