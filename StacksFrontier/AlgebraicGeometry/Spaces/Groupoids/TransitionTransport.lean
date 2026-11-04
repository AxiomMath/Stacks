module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Reindexing a transition morphism between two inverse images of a module

Two equal morphisms `f = g : T ⟶ X` of algebraic spaces have equal inverse-image functors on
`𝒪`-modules, and so the inverse images `f^*ℱ` and `g^*ℱ` of a module on `X` are canonically
identified.  This identification is what lets a transition morphism `α : a^*ℱ ⟶ b^*ℱ`, between
the inverse images of a module along two parallel morphisms, be reindexed along two composites
that are equal but not syntactically so.

Reindexing itself is the other construction of this file: the inverse image of `α` along a
morphism `f` into the common source of `a` and `b`, read as a morphism
`(f ≫ a)^*ℱ ⟶ (f ≫ b)^*ℱ` through the composition isomorphisms of Stacks 03LU.  Both the
transition morphism of a quasi-coherent module on a groupoid in algebraic spaces (Stacks 0441)
and the transition morphism of a `G`-equivariant quasi-coherent module (Stacks 043T) are
reindexed by this one construction, and their cocycle and unit laws are both instances of the
two conditions `AlgebraicGeometry.Space.TransitionCocycle` and
`AlgebraicGeometry.Space.TransitionUnit` below; that is why all of this lives below both of
them.

## Main definitions

* `CategoryTheory.comp₃` is the composite of a row of three morphisms, as a named operation;
  the two composites below are built from it rather than from `≫`.
* `AlgebraicGeometry.Space.pullbackTransport` is the canonical identification of the inverse
  images of a module along two equal morphisms.
* `AlgebraicGeometry.Space.transitionReindex` reindexes a transition morphism along a morphism
  into the common source of the two parallel morphisms it compares.
* `AlgebraicGeometry.Space.transitionPair` composes two reindexings of a transition morphism
  along a pair of morphisms with matching endpoints, and
  `AlgebraicGeometry.Space.transitionComposite` reads that composite between the endpoints of a
  third morphism.
* `AlgebraicGeometry.Space.TransitionCocycle` and `AlgebraicGeometry.Space.TransitionUnit` are
  the cocycle and unit conditions on a transition morphism, at a triple and at a single
  morphism into the common source.

## Main results

* `AlgebraicGeometry.Space.pullbackTransport_naturality`: the identification is natural in the
  module.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 043T](https://stacks.math.columbia.edu/tag/043T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

universe v₁ u₁

/-- The composite of a row of three morphisms, as a named operation.

It is `f ≫ g ≫ k`, and the point of naming it is that a definition whose body is `comp₃ f g k`
can be unfolded without exposing the composition operator of the ambient category: the three
factors stay as they are written, and the unfolding is compared factor by factor.  Writing
`f ≫ g ≫ k` instead makes unfolding expose `CategoryTheory.CategoryStruct.comp`, and then a
factor such as an `CategoryTheory.eqToHom` transport is driven down to its `Eq.rec`, which is
what makes the comparison expensive in a category whose objects carry a proof. -/
def comp₃ {C : Type u₁} [Category.{v₁} C] {X₁ X₂ X₃ X₄ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (k : X₃ ⟶ X₄) : X₁ ⟶ X₄ :=
  f ≫ g ≫ k

/-- The row composite is the composite of its three factors.

Stated once, generically, so that a consumer which needs the composition operator back gets it
by instantiating this lemma instead of by unfolding `CategoryTheory.comp₃` at its own types,
where the unfolding is what `comp₃` exists to avoid. -/
theorem comp₃_eq {C : Type u₁} [Category.{v₁} C] {X₁ X₂ X₃ X₄ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (k : X₃ ⟶ X₄) : comp₃ f g k = f ≫ g ≫ k :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The canonical identification of the inverse images of a module along two equal morphisms of
algebraic spaces. -/
def pullbackTransport {T X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    {f g : T ⟶ X} (h : f = g) :
    (modulePullback B S hS f).obj M ⟶ (modulePullback B S hS g).obj M :=
  (eqToIso (congrArg (fun k : T ⟶ X => (modulePullback B S hS k).obj M) h)).hom

/-- Transporting along an equality of morphisms is natural in the module. -/
@[reassoc]
theorem pullbackTransport_naturality {T X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) {f g : T ⟶ X} (h : f = g) :
    (modulePullback B S hS f).map φ ≫ pullbackTransport N h =
      pullbackTransport M h ≫ (modulePullback B S hS g).map φ := by
  subst h
  simp [pullbackTransport]

/-! ### Reindexing a transition morphism -/

section Reindex

variable (B S hS) {U V W : AlgebraicSpaces B S hS}

/-- A transition morphism `α : a^*ℱ ⟶ b^*ℱ` between the inverse images of a module along two
parallel morphisms `a`, `b`, reindexed along a morphism `f` into their common source: the
inverse image of `α` along `f`, with the composition isomorphisms of Stacks 03LU on either side
so that the result is a morphism `(f ≫ a)^*ℱ ⟶ (f ≫ b)^*ℱ`.

Both `AlgebraicGeometry.Space.groupoidPullbackTransition` of Stacks 0441 and
`AlgebraicGeometry.Space.equivariantPullbackTransition` of Stacks 043T are this
construction. -/
def transitionReindex (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (f : W ⟶ V) :
    (modulePullback B S hS (f ≫ a)).obj F ⟶ (modulePullback B S hS (f ≫ b)).obj F :=
  ((modulePullbackCompIso B S hS f a).app F).inv ≫
    (modulePullback B S hS f).map α ≫ ((modulePullbackCompIso B S hS f b).app F).hom

/-- The two reindexings of a transition morphism `α : a^*ℱ ⟶ b^*ℱ`, composed along a pair of
morphisms `p`, `q` into the common source of `a` and `b` whose endpoints match: `b` after `p`
is `a` after `q`.  The matching endpoints are identified by
`AlgebraicGeometry.Space.pullbackTransport`.

The composite is written at `CategoryTheory.comp₃` and not as a chain of `≫`, because a
consumer that needs to see through this definition cannot do so when the body exposes the
composition operator: unfolding it drives the `AlgebraicGeometry.Space.pullbackTransport`
factor down to its `Eq.rec` and the kernel exhausts its budget.  At `comp₃` the unfolding is
compared factor by factor and costs nothing. -/
def transitionPair (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (p q : W ⟶ V)
    (hm : p ≫ b = q ≫ a) :
    (modulePullback B S hS (p ≫ a)).obj F ⟶ (modulePullback B S hS (q ≫ b)).obj F :=
  comp₃ (transitionReindex B S hS F α p) (pullbackTransport F hm)
    (transitionReindex B S hS F α q)

/-- The composite of the two reindexings of a transition morphism `α : a^*ℱ ⟶ b^*ℱ` along a pair
of morphisms `p`, `q` into the common source of `a` and `b` whose endpoints match, read as a
morphism `(r ≫ a)^*ℱ ⟶ (r ≫ b)^*ℱ` for a third morphism `r` with the same outer endpoints; the
equal endpoints are identified by `AlgebraicGeometry.Space.pullbackTransport`.

This is the right-hand side of the cocycle condition of both Stacks 0441 and Stacks 043T, and
it is written at `CategoryTheory.comp₃` for the reason given at
`AlgebraicGeometry.Space.transitionPair`. -/
def transitionComposite (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (p q r : W ⟶ V)
    (ht : r ≫ a = p ≫ a) (hm : p ≫ b = q ≫ a) (hs : r ≫ b = q ≫ b) :
    (modulePullback B S hS (r ≫ a)).obj F ⟶ (modulePullback B S hS (r ≫ b)).obj F :=
  comp₃ (pullbackTransport F ht) (transitionPair B S hS F α p q hm)
    (pullbackTransport F hs.symm)

/-- The cocycle law for a transition morphism `α : a^*ℱ ⟶ b^*ℱ`, at a triple of morphisms `p`,
`q`, `r` into the common source of `a` and `b`: the reindexing of `α` along `r` is the composite
of its reindexings along `p` and along `q`.

This is the cocycle condition of Stacks 0441 at the space of composable pairs of arrows, and
the cocycle condition of Stacks 043T at a test object. -/
def TransitionCocycle (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (p q r : W ⟶ V) : Prop :=
  ∀ (ht : r ≫ a = p ≫ a) (hm : p ≫ b = q ≫ a) (hs : r ≫ b = q ≫ b),
    transitionReindex B S hS F α r = transitionComposite B S hS F α p q r ht hm hs

/-- The unit law for a transition morphism `α : a^*ℱ ⟶ b^*ℱ`, at a morphism `f` into the common
source of `a` and `b` which `a` and `b` agree on: the reindexing of `α` along `f` is the
identification of its two equal endpoints.

This is the unit condition of Stacks 0441 at the unit arrow, and the unit condition of
Stacks 043T at a test object landing in the unit section. -/
def TransitionUnit (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (f : W ⟶ V) :
    Prop :=
  ∀ h : f ≫ a = f ≫ b, transitionReindex B S hS F α f = pullbackTransport F h

end Reindex

end AlgebraicGeometry.Space

end
