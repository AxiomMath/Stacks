module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Diagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Quasi-coherent modules on a groupoid in algebraic spaces

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A`.  A
quasi-coherent module on it is a quasi-coherent `𝒪_U`-module `ℱ` together with a morphism
`α : t^*ℱ ⟶ s^*ℱ` of `𝒪_R`-modules satisfying a cocycle condition on the space of composable
pairs of arrows and normalized on the unit arrows.  This is Stacks 0441.

The three paths across the space of composable pairs are compared by pulling `α` back along the
composition, the first projection and the second projection; the comparisons that make this a
single equation are the composition isomorphism
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU and the three endpoint equations
of the composition diagram of Stacks 04P9.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow` is the unit `e : U ⟶ R`, assembled
  from the pointwise identities of the evaluated groupoids.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.firstArrow` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.secondArrow` are the two projections of the space
  of composable pairs of arrows.
* `AlgebraicGeometry.Space.groupoidPullbackTransition` reindexes a groupoid transition morphism
  along a morphism into the arrow space, and
  `AlgebraicGeometry.Space.groupoidTransitionComposite` is the right-hand side of the cocycle
  condition.
* `AlgebraicGeometry.Space.QuasicoherentModule` is **Stacks 0441**, a quasi-coherent module on a
  groupoid in algebraic spaces, with `AlgebraicGeometry.Space.QuasicoherentModule.Hom` its
  morphisms and `AlgebraicGeometry.Space.QuasicoherentModule.forget` the functor to the modules
  on the object space.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow_comp_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow_comp_target`: the unit is a section
  of both the source and the target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_comp_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_comp_target`: the composite of a composable
  pair has the source of its second arrow and the target of its first.
* `AlgebraicGeometry.Space.groupoidPullbackTransition_naturality` and
  `AlgebraicGeometry.Space.groupoidTransitionComposite_naturality`: both sides of the cocycle
  condition are natural in the module.
* `AlgebraicGeometry.Space.groupoidPullbackTransition_eq_transitionReindex` identifies the
  reindexing of a groupoid transition morphism with `AlgebraicGeometry.Space.transitionReindex`
  at the target and the source of the groupoid.
* The cocycle and unit laws are fields of `AlgebraicGeometry.Space.QuasicoherentModule`, and its
  morphisms form a category.

## Implementation notes

The unit arrow is the natural transformation `U ⟶ R` of Stacks 06K5,
`Deformation.existsUnique_identity`, read in the full subcategory of algebraic spaces.  Its two
endpoint equations are the two halves of
`Deformation.GroupoidInFunctors.evaluationArrowEquiv`, taken at an identity morphism of an
evaluated groupoid.

The two endpoint equations for the composition are not reproved: they are the commuting squares
of the two cartesian squares of the composition diagram already proved for Stacks 043Z and
Stacks 04P9, namely `AlgebraicGeometry.Space.isPullback_comp_source` and
`AlgebraicGeometry.Space.isPullback_fst_comp`.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`.

## References

* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04P9](https://stacks.math.columbia.edu/tag/04P9)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

universe v₁ u₁

/-- **Three commuting squares in a row paste into one.**  Given morphisms `nᵏ` from a row
`a, b, c` to a row `a', b', c'` which make the three squares commute, the outer rectangle
commutes.  Mathlib's `CategoryTheory.CommSq.vert_comp` pastes two squares and delivers the
result with the composites bracketed to the left; this states the three-square case for the
row composite `CategoryTheory.comp₃`, which is the naturality square of a morphism defined as
`comp₃ a b c`, with nothing reassociated on either side. -/
theorem comp₃_naturality {C : Type u₁} [Category.{v₁} C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄} {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃} {c' : Y₃ ⟶ Y₄}
    {n₁ : X₁ ⟶ Y₁} {n₂ : X₂ ⟶ Y₂} {n₃ : X₃ ⟶ Y₃} {n₄ : X₄ ⟶ Y₄}
    (h₁ : n₁ ≫ a' = a ≫ n₂) (h₂ : n₂ ≫ b' = b ≫ n₃) (h₃ : n₃ ≫ c' = c ≫ n₄) :
    n₁ ≫ comp₃ a' b' c' = comp₃ a b c ≫ n₄ := by
  rw [comp₃, comp₃, Category.assoc, Category.assoc, ← Category.assoc, h₁, Category.assoc,
    ← Category.assoc n₂ b' c', h₂, Category.assoc, h₃]

end CategoryTheory

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS}

namespace GroupoidInAlgebraicSpaces

/-- The first projection of the space of composable pairs of arrows of a groupoid in algebraic
spaces; it picks out the arrow that is applied second, so that the composite has its target. -/
abbrev firstArrow (G : GroupoidInAlgebraicSpaces B S hS A) :
    AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom)

/-- The second projection of the space of composable pairs of arrows of a groupoid in algebraic
spaces; it picks out the arrow that is applied first, so that the composite has its source. -/
abbrev secondArrow (G : GroupoidInAlgebraicSpaces B S hS A) :
    AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom)

/-- **Stacks 06K5** for a groupoid in algebraic spaces: the unit `e : U ⟶ R`, the morphism of
algebraic spaces assigning to every object the identity arrow at it.  It is the unique natural
transformation whose value at every point of every test scheme is the identity of the evaluated
groupoid. -/
def identityArrow (G : GroupoidInAlgebraicSpaces B S hS A) : G.objects ⟶ G.arrows :=
  ObjectProperty.homMk
    (Deformation.existsUnique_identity G.toGroupoidInFunctors).exists.choose

/-- The value of the unit arrow at a point of a test scheme is the identity arrow at that
point. -/
theorem identityArrow_hom_app (G : GroupoidInAlgebraicSpaces B S hS A)
    (T : (BigFppfOver B S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    (identityArrow G).hom.app T x = G.toGroupoidInFunctors.identity T x :=
  (Deformation.existsUnique_identity G.toGroupoidInFunctors).exists.choose_spec T x

/-- The unit arrow at a point of a test scheme has that point as its source and as its target. -/
private theorem identityArrow_app_source_target (G : GroupoidInAlgebraicSpaces B S hS A)
    (T : (BigFppfOver B S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    G.source.hom.app T ((identityArrow G).hom.app T x) = x ∧
      G.target.hom.app T ((identityArrow G).hom.app T x) = x := by
  let _ := G.toGroupoidInFunctors.evaluationGroupoid T
  have h := (G.toGroupoidInFunctors.evaluationArrowEquiv T
    (show G.toGroupoidInFunctors.Evaluation T from x) x (𝟙 _)).2
  rw [Deformation.GroupoidInFunctors.evaluationArrowEquiv_id] at h
  rw [identityArrow_hom_app]
  exact h

/-- The source of the unit arrow at an object is that object: `e ≫ s = 𝟙 U`. -/
@[simp]
theorem identityArrow_comp_source (G : GroupoidInAlgebraicSpaces B S hS A) :
    identityArrow G ≫ G.source = 𝟙 G.objects := by
  apply ObjectProperty.hom_ext
  ext T x
  exact (identityArrow_app_source_target G T x).1

/-- The target of the unit arrow at an object is that object: `e ≫ t = 𝟙 U`. -/
@[simp]
theorem identityArrow_comp_target (G : GroupoidInAlgebraicSpaces B S hS A) :
    identityArrow G ≫ G.target = 𝟙 G.objects := by
  apply ObjectProperty.hom_ext
  ext T x
  exact (identityArrow_app_source_target G T x).2

/-- The two projections of the space of composable pairs of arrows agree after the source and
the target: this is the commuting square of the defining fibre product. -/
theorem firstArrow_comp_source (G : GroupoidInAlgebraicSpaces B S hS A) :
    firstArrow G ≫ G.source = secondArrow G ≫ G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).w

/-- The composite of a composable pair of arrows has the source of its second arrow.  This is
the commuting square of the cartesian square of Stacks 043Z. -/
@[simp]
theorem comp_comp_source (G : GroupoidInAlgebraicSpaces B S hS A) :
    G.comp ≫ G.source = secondArrow G ≫ G.source :=
  (Space.isPullback_comp_source G).w

/-- The composite of a composable pair of arrows has the target of its first arrow.  This is the
commuting square of the upper cartesian square of Stacks 04P9. -/
@[simp]
theorem comp_comp_target (G : GroupoidInAlgebraicSpaces B S hS A) :
    G.comp ≫ G.target = firstArrow G ≫ G.target :=
  (Space.isPullback_fst_comp G).w.symm

end GroupoidInAlgebraicSpaces

namespace Space

open GroupoidInAlgebraicSpaces

/-- A groupoid transition morphism `α : t^*ℱ ⟶ s^*ℱ`, reindexed along a morphism `f` into the
arrow space: the inverse image of `α` along `f`, with the composition isomorphisms of
Stacks 03LU on either side so that the result is a morphism `(f ≫ t)^*ℱ ⟶ (f ≫ s)^*ℱ`. -/
def groupoidPullbackTransition (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ G.arrows) :
    (modulePullback B S hS (f ≫ G.target)).obj F ⟶
      (modulePullback B S hS (f ≫ G.source)).obj F :=
  ((modulePullbackCompIso B S hS f G.target).app F).inv ≫
    (modulePullback B S hS f).map α ≫
    ((modulePullbackCompIso B S hS f G.source).app F).hom

/-- Reindexing a groupoid transition morphism is natural in the module. -/
@[reassoc]
theorem groupoidPullbackTransition_naturality (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A)
    {M N : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    {α : (modulePullback B S hS G.target).obj M ⟶ (modulePullback B S hS G.source).obj M}
    {β : (modulePullback B S hS G.target).obj N ⟶ (modulePullback B S hS G.source).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback B S hS G.source).map φ =
      (modulePullback B S hS G.target).map φ ≫ β)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ G.arrows) :
    (modulePullback B S hS (f ≫ G.target)).map φ ≫
        groupoidPullbackTransition B S hS G N β f =
      groupoidPullbackTransition B S hS G M α f ≫
        (modulePullback B S hS (f ≫ G.source)).map φ := by
  simp only [groupoidPullbackTransition, Iso.app_inv, Iso.app_hom, Category.assoc]
  rw [NatTrans.naturality_assoc]
  show _ ≫ (modulePullback B S hS f).map
    ((modulePullback B S hS G.target).map φ) ≫ _ = _
  rw [← Functor.map_comp_assoc, ← hφ, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (modulePullbackCompIso B S hS f G.source).hom.naturality φ]
  rfl

/-- Reindexing the transition morphism of a quasi-coherent module on a groupoid in algebraic
spaces is `AlgebraicGeometry.Space.transitionReindex` at the target and the source of the
groupoid.  The identification holds by definition; it is recorded because the elaborator does
not perform the unfolding on its own. -/
theorem groupoidPullbackTransition_eq_transitionReindex (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ G.arrows) :
    groupoidPullbackTransition B S hS G F α f =
      transitionReindex B S hS (U := G.objects) (V := G.arrows) F α f :=
  rfl

section Pair

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- Two reindexings of a groupoid transition morphism, composed along a pair of morphisms `a`,
`b` into the arrow space whose endpoints match: the source of `a` is the target of `b`. -/
def groupoidTransitionPair (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.arrows)
    (h : a ≫ G.source = b ≫ G.target) :
    (modulePullback B S hS (a ≫ G.target)).obj F ⟶
      (modulePullback B S hS (b ≫ G.source)).obj F :=
  comp₃ (groupoidPullbackTransition B S hS G F α a) (pullbackTransport F h)
    (groupoidPullbackTransition B S hS G F α b)

/-- `AlgebraicGeometry.Space.groupoidTransitionPair` is the row composite of its three factors.

This is its definition, read as an equation, and it exists so that the unfolding is performed
once and propositionally: rewriting with it leaves a goal about
`CategoryTheory.comp₃` whose factors are spelled exactly as the naturality lemmas below spell
them, where `exact` needs no conversion at all. -/
private theorem groupoidTransitionPair_eq₃
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.arrows)
    (h : a ≫ G.source = b ≫ G.target) :
    groupoidTransitionPair B S hS G F α a b h =
      comp₃ (groupoidPullbackTransition B S hS G F α a) (pullbackTransport F h)
        (groupoidPullbackTransition B S hS G F α b) :=
  rfl

/-- The two-step composite of reindexings is natural in the module. -/
theorem groupoidTransitionPair_naturality
    {M N : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    {α : (modulePullback B S hS G.target).obj M ⟶ (modulePullback B S hS G.source).obj M}
    {β : (modulePullback B S hS G.target).obj N ⟶ (modulePullback B S hS G.source).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback B S hS G.source).map φ =
      (modulePullback B S hS G.target).map φ ≫ β)
    {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.arrows)
    (h : a ≫ G.source = b ≫ G.target) :
    (modulePullback B S hS (a ≫ G.target)).map φ ≫
        groupoidTransitionPair B S hS G N β a b h =
      groupoidTransitionPair B S hS G M α a b h ≫
        (modulePullback B S hS (b ≫ G.source)).map φ := by
  rw [groupoidTransitionPair_eq₃, groupoidTransitionPair_eq₃]
  exact comp₃_naturality (groupoidPullbackTransition_naturality B S hS G φ hφ a)
    (pullbackTransport_naturality φ h)
    (groupoidPullbackTransition_naturality B S hS G φ hφ b)

/-- `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidTransitionPair` unfolded by one layer,
to the general construction it wraps.

Recorded because the wrapper is a `def` and a consumer that needs to see through it cannot do so
by `rfl` on the fully written-out composite: that identification is not kernel-checkable at these
types, since the kernel reaches into `modulePullback` and unfolds
`RingedSite.ringSheaf (smallEtaleRingedSite …)`. Unfolding a *single* layer is syntactic and
costs nothing, which is what makes this lemma usable where the direct equation is not. -/
theorem groupoidTransitionPair_eq (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F)
    {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.arrows)
    (h : a ≫ G.source = b ≫ G.target) :
    groupoidTransitionPair B S hS G F α a b h
      = transitionPair B S hS (U := G.objects) (V := G.arrows) F α a b h :=
  rfl

end Pair

/-- The composite of the two reindexings of a groupoid transition morphism along the two
projections of the space of composable pairs of arrows, read as a morphism
`c^*t^*ℱ ⟶ c^*s^*ℱ` through the three endpoint equations of the composition diagram of
Stacks 04P9.  This is the right-hand side of the cocycle condition of Stacks 0441. -/
def groupoidTransitionComposite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F) :
    (modulePullback B S hS (G.comp ≫ G.target)).obj F ⟶
      (modulePullback B S hS (G.comp ≫ G.source)).obj F :=
  comp₃ (pullbackTransport F (comp_comp_target G))
    (groupoidTransitionPair B S hS G F α (firstArrow G) (secondArrow G)
      (firstArrow_comp_source G))
    (pullbackTransport F (comp_comp_source G).symm)

/-- `AlgebraicGeometry.Space.groupoidTransitionComposite` is the row composite of its three
factors; see `AlgebraicGeometry.Space.groupoidTransitionPair_eq₃` for why the unfolding is
recorded as an equation. -/
private theorem groupoidTransitionComposite_eq₃ (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F) :
    groupoidTransitionComposite B S hS G F α =
      comp₃ (pullbackTransport F (comp_comp_target G))
        (groupoidTransitionPair B S hS G F α (firstArrow G) (secondArrow G)
          (firstArrow_comp_source G))
        (pullbackTransport F (comp_comp_source G).symm) :=
  rfl

/-- The right-hand side of the cocycle condition is natural in the module. -/
theorem groupoidTransitionComposite_naturality (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A)
    {M N : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    {α : (modulePullback B S hS G.target).obj M ⟶ (modulePullback B S hS G.source).obj M}
    {β : (modulePullback B S hS G.target).obj N ⟶ (modulePullback B S hS G.source).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback B S hS G.source).map φ =
      (modulePullback B S hS G.target).map φ ≫ β) :
    (modulePullback B S hS (G.comp ≫ G.target)).map φ ≫
        groupoidTransitionComposite B S hS G N β =
      groupoidTransitionComposite B S hS G M α ≫
        (modulePullback B S hS (G.comp ≫ G.source)).map φ := by
  rw [groupoidTransitionComposite_eq₃, groupoidTransitionComposite_eq₃]
  exact comp₃_naturality (pullbackTransport_naturality φ (comp_comp_target G))
    (groupoidTransitionPair_naturality B S hS G φ hφ (firstArrow G) (secondArrow G)
      (firstArrow_comp_source G))
    (pullbackTransport_naturality φ (comp_comp_source G).symm)

/-- `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidTransitionComposite` unfolded by one
layer, to the general construction it wraps.

The cocycle condition of Stacks 0441 is an equation whose right-hand side is this composite, so
any proof of it must be able to see through the wrapper. As for
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidTransitionPair_eq`, the direct equation with
the composite written out is not kernel-checkable at these types, while this one-layer unfolding
is syntactic. -/
theorem groupoidTransitionComposite_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (modulePullback B S hS G.target).obj F ⟶ (modulePullback B S hS G.source).obj F) :
    groupoidTransitionComposite B S hS G F α
      = transitionComposite B S hS (U := G.objects) (V := G.arrows) F α
          (firstArrow G) (secondArrow G) G.comp
          (comp_comp_target G) (firstArrow_comp_source G) (comp_comp_source G) :=
  rfl

variable (B S hS)

/-- **Stacks 0441.**  A quasi-coherent module on a groupoid in algebraic spaces `(U, R, s, t, c)`
over `A`: a quasi-coherent `𝒪_U`-module `ℱ` together with a morphism `α : t^*ℱ ⟶ s^*ℱ` of
`𝒪_R`-modules which satisfies the cocycle condition on the space of composable pairs of arrows
and restricts to the identity along the unit. -/
@[stacks 0441]
structure QuasicoherentModule (G : GroupoidInAlgebraicSpaces B S hS A) where
  /-- The underlying quasi-coherent module on the space of objects. -/
  F : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property
  /-- The transition morphism from the target pullback to the source pullback. -/
  alpha : (modulePullback B S hS G.target).obj F.obj ⟶
    (modulePullback B S hS G.source).obj F.obj
  /-- Pulling the transition back along the composition agrees with pulling it back along the
  two projections in turn. -/
  cocycle :
    groupoidPullbackTransition B S hS G F.obj alpha G.comp =
      groupoidTransitionComposite B S hS G F.obj alpha
  /-- Pulling the transition back along the unit gives the identity. -/
  unit :
    groupoidPullbackTransition B S hS G F.obj alpha (identityArrow G) =
      pullbackTransport F.obj
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm)

namespace QuasicoherentModule

variable {B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

/-- A morphism of quasi-coherent modules on a groupoid in algebraic spaces: a morphism of the
underlying modules on the space of objects which commutes with the two transition
morphisms. -/
@[ext]
structure Hom (M N : QuasicoherentModule B S hS G) where
  /-- The underlying morphism of modules on the space of objects. -/
  hom : M.F.obj ⟶ N.F.obj
  /-- Compatibility with the transition morphisms. -/
  comm : M.alpha ≫ (modulePullback B S hS G.source).map hom =
    (modulePullback B S hS G.target).map hom ≫ N.alpha

/-- Quasi-coherent modules on a groupoid in algebraic spaces and the morphisms compatible with
their transitions form a category, the category `QCoh(U, R, s, t, c)` of Stacks 0441. -/
instance : Category (QuasicoherentModule B S hS G) where
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

/-- The functor forgetting the transition morphism of a quasi-coherent module on a groupoid in
algebraic spaces, keeping only the module on the space of objects. -/
@[implicit_reducible]
def forget (G : GroupoidInAlgebraicSpaces B S hS A) :
    QuasicoherentModule B S hS G ⥤ Modules.{u, u} B S hS G.objects.1 G.objects.2 where
  obj M := M.F.obj
  map f := f.hom

/-- The forgetful functor sends a quasi-coherent module on a groupoid to its underlying module on
the space of objects. -/
@[simp]
theorem forget_obj (G : GroupoidInAlgebraicSpaces B S hS A)
    (M : QuasicoherentModule B S hS G) : (forget G).obj M = M.F.obj := rfl

/-- The forgetful functor sends a morphism of quasi-coherent modules on a groupoid to its
underlying morphism of modules. -/
@[simp]
theorem forget_map (G : GroupoidInAlgebraicSpaces B S hS A)
    {M N : QuasicoherentModule B S hS G} (f : M ⟶ N) : (forget G).map f = f.hom := rfl

end QuasicoherentModule

end Space

end AlgebraicGeometry

end
