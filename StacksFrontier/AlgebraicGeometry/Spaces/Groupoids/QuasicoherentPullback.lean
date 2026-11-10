module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliarySpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image of a quasi-coherent module along a morphism of groupoids in algebraic spaces

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `A`.  A quasi-coherent module on the target groupoid is a quasi-coherent
`𝒪_{U'}`-module `ℱ` together with a transition morphism `α : t'^*ℱ ⟶ s'^*ℱ` satisfying a cocycle
condition on the space of composable pairs of arrows and a unit condition along the unit arrow.
Its inverse image along `f` is the pair `(f^*ℱ, f^*α)`, where `f^*α` reindexes `α` along the map
`R ⟶ R'` on arrows and reads the result through the two squares of `f` and the comparisons of
iterated inverse images of Stacks 03LU.

The content of the assertion that `(ℱ, α) ↦ (f^*ℱ, f^*α)` is a functor is that `f^*α` again
satisfies the two conditions.  Both are proved here, the unit condition from the unit condition
for `α` reindexed along the map `f` induces on the unit arrow, and the cocycle condition from
the cocycle condition for `α` reindexed along the map `f` induces on the spaces of composable
pairs of arrows.  Compatibility of `f^*α` with morphisms of modules is proved as well, so the
inverse image is available both on objects and on morphisms; see "What is not proved" for what
keeps the three from being assembled into a functor here.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.compPairsMap` is the map on the spaces of
  composable pairs of arrows induced by a morphism of groupoids in algebraic spaces.
* `AlgebraicGeometry.Space.groupoidReindexTransport` is the reindexing of a transition morphism
  along the map on arrows, read between the two squares of the morphism of groupoids, and
  `AlgebraicGeometry.Space.groupoidModulePullbackTransition` is its unflattening, the transition
  morphism `f^*α` of the inverse image.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj` is the inverse image
  `(ℱ, α) ↦ (f^*ℱ, f^*α)`, a quasi-coherent module on the source groupoid.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.identityArrow_comp_arrowsMap`: a morphism of
  groupoids in algebraic spaces carries the unit arrow to the unit arrow.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.comp_comp_arrowsMap`, together with
  `Hom.compPairsMap_comp_firstArrow` and `Hom.compPairsMap_comp_secondArrow`: the square of a
  morphism of groupoids in algebraic spaces over the spaces of composable pairs of arrows.  A
  morphism of groupoids commutes with the composition laws and with the two projections.
* `AlgebraicGeometry.Space.modulePullbackReindex_cocycle_comp`: a cocycle law for a transition
  morphism reindexes along a morphism into the space the law is stated on.
* `AlgebraicGeometry.Space.modulePullbackFlatten_reindex_groupoidTransition`: flattening a
  reindexing of `f^*α` reindexes `α` along the pushed morphism.  This is the identity both laws
  reduce to.
* `AlgebraicGeometry.Space.groupoidModulePullbackTransition_unit` and
  `AlgebraicGeometry.Space.groupoidModulePullbackTransition_cocycle`: **the unit and the cocycle
  law for the transition morphism of the inverse image**, the two conditions that make
  `(f^*ℱ, f^*α)` a quasi-coherent module on the source groupoid.
* `AlgebraicGeometry.Space.groupoidModulePullbackTransition_naturality`: the transition morphism
  of the inverse image is natural in the module.

## What is not proved

The inverse image is not assembled into a functor
`QCoh(U', R', s', t', c') ⥤ QCoh(U, R, s, t, c)`, so no unqualified tag is carried.  All three
ingredients are available — `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj` on
objects, `(AlgebraicGeometry.Space.modulePullback _ _ _ f).map` on morphisms, and
`AlgebraicGeometry.Space.groupoidModulePullbackTransition_naturality` for the compatibility —
and what stands in the way is not mathematical.

The compatibility field of a morphism of quasi-coherent modules on a groupoid is stated with
the underlying module of its source read as `M.F.obj`, so for the inverse image it is stated
with the module of the inverse image read through that projection, whereas the naturality
statement above is stated with `AlgebraicGeometry.Space.modulePullback` applied to the module
directly.  Identifying the two asks for the equality of two inverse images of definitionally
equal but syntactically different modules underneath `CategoryTheory.Functor.map`, and the only
route to it reaches into `AlgebraicGeometry.Space.modulePullback`, whose unfolding is the one
thing the implementation notes below say must be avoided.

With the object map taken as the definition `groupoidQuasicoherentPullbackObj` the elaborator
does not get through that identification; writing the object map inline in the functor instead
lets the elaborator reduce the projection on the spot and succeed, and then the kernel does not
get through it.  Spelling the module of the inverse image either as a pair or as
`AlgebraicGeometry.Space.quasicoherentPullback` changes neither outcome.  What is needed is a
form of the naturality statement whose two inverse images are the ones the compatibility field
names, so that no identification is asked for at all.

The inverse image of a quasi-coherent module on the *equivariant* side is assembled, as
`AlgebraicGeometry.Space.equivariantQuasicoherentPullback` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EquivariantQuasicoherentPullback.lean`, carrying
the tag for the sibling Stacks 043U.

## Implementation notes

Every identity about the inverse image of `𝒪`-modules is obtained by instantiating a lemma of
the reindexing calculus of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackAssoc.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EquivariantQuasicoherentPullback.lean`, rather
than by unfolding `AlgebraicGeometry.Space.modulePullback`, whose unfolding the kernel cannot
check within its budget.  The associativity coherence those lemmas take as input is now the
theorem `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, so nothing below is conditional.

For the same reason the transition morphism of the inverse image is *not* identified with a
written-out composite of `𝒪`-module morphisms: it is defined by
`AlgebraicGeometry.Space.modulePullbackUnflatten` applied to a separately named reindexing, and
the only identifications used are the proved lemma
`AlgebraicGeometry.Space.modulePullbackFlatten_unflatten` and the generic
`CategoryTheory.comp₃_eq`.  Rewriting with the equation of the definition instead exhausts the
kernel budget, measurably.

For the same reason again, every composite of morphisms of algebraic spaces that appears
underneath an inverse image is taken abstractly, as a morphism together with an equation
identifying it with the composite: a statement mentioning `w ≫ m` inside
`(AlgebraicGeometry.Space.modulePullback _ _ _ _).obj` forces the elaborator to reconcile
`w ≫ m ≫ a` with `(w ≫ m) ≫ a` there, which it cannot do.  This is why
`AlgebraicGeometry.Space.modulePullbackReindex_cocycle_comp` takes the three composed morphisms
as parameters rather than forming them.

Each law is proved after flattening along the map on objects, flattening being injective since
it is conjugation by two comparison isomorphisms.  The cocycle law is
`AlgebraicGeometry.Space.modulePullbackReindex_cocycle_of_flatten`, which performs that
flattening factor by factor, at the map on arrows and the map on composable pairs.

## References

* [Stacks Project, Tag 0442](https://stacks.math.columbia.edu/tag/0442)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS A}

namespace GroupoidInAlgebraicSpaces

/-- A morphism of groupoids in algebraic spaces carries the unit arrow to the unit arrow: the
identity arrow at an object goes to the identity arrow at the image object. -/
theorem Hom.identityArrow_comp_arrowsMap (φ : Hom G G') :
    identityArrow G ≫ φ.arrowsMap = φ.objectsMap ≫ identityArrow G' := by
  apply ObjectProperty.hom_ext
  ext T x
  change φ.toGroupoidHom.mapArrows.app T ((identityArrow G).hom.app T x) =
    (identityArrow G').hom.app T (φ.toGroupoidHom.mapObjects.app T x)
  rw [identityArrow_hom_app G T x, identityArrow_hom_app G' T (φ.toGroupoidHom.mapObjects.app T x)]
  exact φ.toGroupoidHom.map_id T x

/-- The two projections of the space of composable pairs of arrows of the source groupoid,
followed by the map on arrows, are again a composable pair of arrows of the target groupoid. -/
theorem Hom.compPairs_condition (φ : Hom G G') :
    (firstArrow G ≫ φ.arrowsMap) ≫ G'.source =
      (secondArrow G ≫ φ.arrowsMap) ≫ G'.target := by
  rw [Category.assoc, Category.assoc, φ.arrowsMap_comp_source, φ.arrowsMap_comp_target,
    ← Category.assoc, ← Category.assoc, firstArrow_comp_source]

/-- **The map on spaces of composable pairs of arrows induced by a morphism of groupoids in
algebraic spaces.**  Applying the map on arrows to both members of a composable pair of arrows
of the source groupoid gives a composable pair of arrows of the target groupoid; the resulting
morphism of the two spaces of composable pairs is obtained from the universal property of the
fibre product defining the space of composable pairs of the target groupoid. -/
def Hom.compPairsMap (φ : Hom G G') :
    AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶
      AlgebraicSpaces.fiberProduct B S hS G'.source G'.target :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G'.source G'.target).lift
    (firstArrow G ≫ φ.arrowsMap) (secondArrow G ≫ φ.arrowsMap) φ.compPairs_condition

/-- The map on composable pairs is compatible with the first projection. -/
@[simp]
theorem Hom.compPairsMap_comp_firstArrow (φ : Hom G G') :
    φ.compPairsMap ≫ firstArrow G' = firstArrow G ≫ φ.arrowsMap :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G'.source G'.target).lift_fst _ _ _

/-- The map on composable pairs is compatible with the second projection. -/
@[simp]
theorem Hom.compPairsMap_comp_secondArrow (φ : Hom G G') :
    φ.compPairsMap ≫ secondArrow G' = secondArrow G ≫ φ.arrowsMap :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G'.source G'.target).lift_snd _ _ _

/-- **A morphism of groupoids in algebraic spaces commutes with the composition laws.**  The
composite of a composable pair of arrows is carried by the map on arrows to the composite of the
image pair.  Together with the two projection identities this is the square of the morphism over
the spaces of composable pairs of arrows. -/
theorem Hom.comp_comp_arrowsMap (φ : Hom G G') :
    G.comp ≫ φ.arrowsMap = φ.compPairsMap ≫ G'.comp := by
  apply ObjectProperty.hom_ext
  ext T κ
  have hab : G.source.hom.app T ((pullback.fst G.source.hom G.target.hom).app T κ) =
      G.target.hom.app T ((pullback.snd G.source.hom G.target.hom).app T κ) :=
    natTrans_app_congr (pullback.condition (f := G.source.hom) (g := G.target.hom)) T κ
  have e₁ : (pullback.fst G'.source.hom G'.target.hom).app T (φ.compPairsMap.hom.app T κ) =
      φ.toGroupoidHom.mapArrows.app T
        ((pullback.fst G.source.hom G.target.hom).app T κ) :=
    natTrans_app_congr
      (congrArg (fun ψ => ψ.hom) φ.compPairsMap_comp_firstArrow) T κ
  have e₂ : (pullback.snd G'.source.hom G'.target.hom).app T (φ.compPairsMap.hom.app T κ) =
      φ.toGroupoidHom.mapArrows.app T
        ((pullback.snd G.source.hom G.target.hom).app T κ) :=
    natTrans_app_congr
      (congrArg (fun ψ => ψ.hom) φ.compPairsMap_comp_secondArrow) T κ
  change φ.toGroupoidHom.mapArrows.app T (G.comp.hom.app T κ) =
    G'.comp.hom.app T (φ.compPairsMap.hom.app T κ)
  rw [comp_hom_app_eq G T κ _ _ rfl rfl hab,
    comp_hom_app_eq G' T (φ.compPairsMap.hom.app T κ) _ _ e₁ e₂
      ((φ.toGroupoidHom.map_source T _).trans
        ((congrArg (φ.toGroupoidHom.mapObjects.app T) hab).trans
          (φ.toGroupoidHom.map_target T _).symm))]
  exact (φ.toGroupoidHom.map_comp T _ _ hab).symm

end GroupoidInAlgebraicSpaces

namespace Space

open GroupoidInAlgebraicSpaces

variable (B S hS)

/-- The transition morphism of a module on the target groupoid, reindexed along the map on
arrows of a morphism `f` of groupoids in algebraic spaces and read between the two squares of
`f` as a morphism `(t ≫ f)^*ℱ ⟶ (s ≫ f)^*ℱ`. -/
def groupoidReindexTransport (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F) :
    (modulePullback B S hS (G.target ≫ φ.objectsMap)).obj F ⟶
      (modulePullback B S hS (G.source ≫ φ.objectsMap)).obj F :=
  comp₃ (pullbackTransport F φ.arrowsMap_comp_target.symm)
    (modulePullbackReindex φ.arrowsMap α)
    (pullbackTransport F φ.arrowsMap_comp_source)

/-- `AlgebraicGeometry.Space.groupoidReindexTransport` is the row composite of its three
factors, read at `CategoryTheory.comp₃`. -/
theorem groupoidReindexTransport_eq (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F) :
    groupoidReindexTransport B S hS φ F α =
      comp₃ (pullbackTransport F φ.arrowsMap_comp_target.symm)
        (modulePullbackReindex φ.arrowsMap α)
        (pullbackTransport F φ.arrowsMap_comp_source) :=
  rfl

/-- `AlgebraicGeometry.Space.groupoidReindexTransport` as a composite of its three factors. -/
theorem groupoidReindexTransport_eq_comp (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F) :
    groupoidReindexTransport B S hS φ F α =
      pullbackTransport F φ.arrowsMap_comp_target.symm ≫
        modulePullbackReindex φ.arrowsMap α ≫
        pullbackTransport F φ.arrowsMap_comp_source :=
  (groupoidReindexTransport_eq B S hS φ F α).trans (comp₃_eq _ _ _)

/-- The transition morphism of the inverse image of a quasi-coherent module on a groupoid in
algebraic spaces along a morphism `f` of groupoids in algebraic spaces: the transition morphism
`α` of the given module, reindexed along the map on arrows and read through the two squares of
`f` and the comparisons of iterated inverse images of Stacks 03LU. -/
def groupoidModulePullbackTransition (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F) :
    (modulePullback B S hS G.target).obj ((modulePullback B S hS φ.objectsMap).obj F) ⟶
      (modulePullback B S hS G.source).obj ((modulePullback B S hS φ.objectsMap).obj F) :=
  modulePullbackUnflatten φ.objectsMap (a := G.target) (b := G.source) (M := F)
    (groupoidReindexTransport B S hS φ F α)

/-- The transition morphism of the inverse image is the unflattening of the reindexing of the
given transition morphism along the map on arrows. -/
theorem groupoidModulePullbackTransition_eq (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F) :
    groupoidModulePullbackTransition B S hS φ F α =
      modulePullbackUnflatten φ.objectsMap (a := G.target) (b := G.source) (M := F)
        (groupoidReindexTransport B S hS φ F α) :=
  rfl

/-- Flattening the transition morphism of the inverse image along the map on objects recovers
the reindexing of the given transition morphism along the map on arrows. -/
theorem modulePullbackFlatten_groupoidModulePullbackTransition (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F) :
    modulePullbackFlatten φ.objectsMap
        (groupoidModulePullbackTransition B S hS φ F α) =
      pullbackTransport F φ.arrowsMap_comp_target.symm ≫
        modulePullbackReindex φ.arrowsMap α ≫
        pullbackTransport F φ.arrowsMap_comp_source :=
  ((congrArg (fun x => modulePullbackFlatten φ.objectsMap x)
        (groupoidModulePullbackTransition_eq B S hS φ F α)).trans
      (modulePullbackFlatten_unflatten _ _)).trans
    (groupoidReindexTransport_eq_comp B S hS φ F α)

/-- **Flattening a reindexing of an unflattening.**  Reindexing an unflattening along a further
morphism and flattening again is reindexing the given morphism.  Both steps are lemmas of the
reindexing calculus, so nothing is unfolded. -/
theorem modulePullbackFlatten_reindex_unflatten {U U' V' W : AlgebraicSpaces B S hS}
    (g : U' ⟶ U) {a b : V' ⟶ U'} {M : Modules.{u, u} B S hS U.1 U.2}
    (X : (modulePullback B S hS (a ≫ g)).obj M ⟶ (modulePullback B S hS (b ≫ g)).obj M)
    (w : W ⟶ V') :
    modulePullbackFlatten g (modulePullbackReindex w (modulePullbackUnflatten g X)) =
      modulePullbackReindex w X :=
  ((modulePullbackCompIsoAssoc B S hS).modulePullbackFlatten_reindex w g _).trans
    (congrArg (fun x => modulePullbackReindex w x) (modulePullbackFlatten_unflatten g X))

/-- Three canonical identifications of inverse images compose to a fourth. -/
theorem pullbackTransport_comp₃ {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) {f g h k : T ⟶ X} (h₁ : f = g) (h₂ : g = h)
    (h₃ : h = k) (h₄ : f = k) :
    pullbackTransport M h₁ ≫ pullbackTransport M h₂ ≫ pullbackTransport M h₃ =
      pullbackTransport M h₄ :=
  (congrArg (fun x => pullbackTransport M h₁ ≫ x)
        (pullbackTransport_comp M h₂ h₃ (h₂.trans h₃))).trans
    (pullbackTransport_comp M h₁ (h₂.trans h₃) h₄)

/-- Reindexing a threefold composite factor by factor. -/
theorem modulePullbackReindex_comp₃ {V W Y : AlgebraicSpaces B S hS} (f : V ⟶ W)
    {a b c d : W ⟶ Y} {M : Modules.{u, u} B S hS Y.1 Y.2}
    (t₁ : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M)
    (R : (modulePullback B S hS b).obj M ⟶ (modulePullback B S hS c).obj M)
    (t₂ : (modulePullback B S hS c).obj M ⟶ (modulePullback B S hS d).obj M) :
    modulePullbackReindex f (t₁ ≫ R ≫ t₂) =
      modulePullbackReindex f t₁ ≫ modulePullbackReindex f R ≫ modulePullbackReindex f t₂ :=
  by simp only [modulePullbackReindex_comp_morphism]

/-- Reindexing a fivefold composite factor by factor. -/
theorem modulePullbackReindex_comp₅ {V W Y : AlgebraicSpaces B S hS} (f : V ⟶ W)
    {a₁ a₂ a₃ a₄ a₅ a₆ : W ⟶ Y} {M : Modules.{u, u} B S hS Y.1 Y.2}
    (x₁ : (modulePullback B S hS a₁).obj M ⟶ (modulePullback B S hS a₂).obj M)
    (x₂ : (modulePullback B S hS a₂).obj M ⟶ (modulePullback B S hS a₃).obj M)
    (x₃ : (modulePullback B S hS a₃).obj M ⟶ (modulePullback B S hS a₄).obj M)
    (x₄ : (modulePullback B S hS a₄).obj M ⟶ (modulePullback B S hS a₅).obj M)
    (x₅ : (modulePullback B S hS a₅).obj M ⟶ (modulePullback B S hS a₆).obj M) :
    modulePullbackReindex f (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) =
      modulePullbackReindex f x₁ ≫ modulePullbackReindex f x₂ ≫
        modulePullbackReindex f x₃ ≫ modulePullbackReindex f x₄ ≫
        modulePullbackReindex f x₅ :=
  by simp only [modulePullbackReindex_comp_morphism]

/-- Merging three runs of three canonical identifications around two morphisms: the nine
identifications surrounding the two morphisms collapse to three. -/
theorem comp_transport_merge₃ {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ B₁ B₂ B₃ B₄ D₁ D₂ D₃ D₄ : C}
    (u₁ : A₀ ⟶ A₁) (u₂ : A₁ ⟶ A₂) (u₃ : A₂ ⟶ A₃) (X : A₃ ⟶ B₁)
    (v₁ : B₁ ⟶ B₂) (v₂ : B₂ ⟶ B₃) (v₃ : B₃ ⟶ B₄) (Z : B₄ ⟶ D₁)
    (w₁ : D₁ ⟶ D₂) (w₂ : D₂ ⟶ D₃) (w₃ : D₃ ⟶ D₄)
    (k₁ : A₀ ⟶ A₃) (k₂ : B₁ ⟶ B₄) (k₃ : D₁ ⟶ D₄)
    (h₁ : u₁ ≫ u₂ ≫ u₃ = k₁) (h₂ : v₁ ≫ v₂ ≫ v₃ = k₂) (h₃ : w₁ ≫ w₂ ≫ w₃ = k₃) :
    u₁ ≫ (u₂ ≫ (u₃ ≫ X ≫ v₁) ≫ v₂ ≫ (v₃ ≫ Z ≫ w₁) ≫ w₂) ≫ w₃ =
      k₁ ≫ (X ≫ k₂ ≫ Z) ≫ k₃ := by
  rw [← h₁, ← h₂, ← h₃]
  simp

/-- **A cocycle law reindexes along a morphism.**  If a transition morphism `α` satisfies the
cocycle law at a triple of morphisms into the arrow space, then it satisfies it at the triple
obtained by composing them with a further morphism `p`.  Both sides are reindexed along `p`,
where the two reindexed transition morphisms contract to reindexings along the composed
morphisms and the three canonical identifications stay canonical identifications.

The three composites are taken abstractly, as morphisms together with equations identifying
them, for the reason recorded in the implementation notes: a composite appearing underneath an
inverse image forces a reassociation there that cannot be checked. -/
theorem modulePullbackReindex_cocycle_comp {Y V V₀ W : AlgebraicSpaces B S hS} {a b : V ⟶ Y}
    (F : Modules.{u, u} B S hS Y.1 Y.2)
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (P₀ Q₀ R₀ : V₀ ⟶ V) (p : W ⟶ V₀) (P Q R : W ⟶ V)
    (hP : p ≫ P₀ = P) (hQ : p ≫ Q₀ = Q) (hR : p ≫ R₀ = R)
    {ht₀ : R₀ ≫ a = P₀ ≫ a} {hm₀ : P₀ ≫ b = Q₀ ≫ a} {hs₀ : R₀ ≫ b = Q₀ ≫ b}
    (hcoc : modulePullbackReindex R₀ α =
      pullbackTransport F ht₀ ≫
        (modulePullbackReindex P₀ α ≫ pullbackTransport F hm₀ ≫
          modulePullbackReindex Q₀ α) ≫
        pullbackTransport F hs₀.symm)
    (ht : R ≫ a = P ≫ a) (hm : P ≫ b = Q ≫ a) (hs : R ≫ b = Q ≫ b) :
    modulePullbackReindex R α =
      pullbackTransport F ht ≫
        (modulePullbackReindex P α ≫ pullbackTransport F hm ≫
          modulePullbackReindex Q α) ≫
        pullbackTransport F hs.symm :=
  have K : ∀ {X₀ : V₀ ⟶ V} {X' : W ⟶ V}, p ≫ X₀ = X' → ∀ c : V ⟶ Y, p ≫ X₀ ≫ c = X' ≫ c :=
    fun h c => by rw [← h, Category.assoc]
  have E₁ := K hR a
  have E₂ := (K hR b).symm
  have K₁ := K hP a
  have K₂ := (K hP b).symm
  have L₁ := K hQ a
  have L₂ := (K hQ b).symm
  have et : p ≫ R₀ ≫ a = p ≫ P₀ ≫ a := congrArg (p ≫ ·) ht₀
  have em : p ≫ P₀ ≫ b = p ≫ Q₀ ≫ a := congrArg (p ≫ ·) hm₀
  have es : p ≫ Q₀ ≫ b = p ≫ R₀ ≫ b := congrArg (p ≫ ·) hs₀.symm
  calc modulePullbackReindex R α
      = pullbackTransport F E₁.symm ≫
          (pullbackTransport F E₁ ≫ modulePullbackReindex R α ≫
            pullbackTransport F E₂) ≫
          pullbackTransport F E₂.symm :=
        (sandwich_cancel (pullbackTransport_comp_self F E₁.symm E₁)
          (pullbackTransport_comp_self F E₂ E₂.symm) _).symm
    _ = pullbackTransport F E₁.symm ≫
          (pullbackTransport F et ≫
            (pullbackTransport F K₁ ≫ modulePullbackReindex P α ≫
              pullbackTransport F K₂) ≫
            pullbackTransport F em ≫
            (pullbackTransport F L₁ ≫ modulePullbackReindex Q α ≫
              pullbackTransport F L₂) ≫
            pullbackTransport F es) ≫
          pullbackTransport F E₂.symm :=
        congrArg (fun x => pullbackTransport F E₁.symm ≫ x ≫ pullbackTransport F E₂.symm)
          ((((modulePullbackReindex_comp' (modulePullbackCompIsoAssoc B S hS) p R₀ R hR α
                    E₁ E₂).symm.trans
                (congrArg (fun y => modulePullbackReindex p y)
                  (hcoc.trans (comp_assoc₅ _ _ _ _ _)))).trans
              (modulePullbackReindex_comp₅ B S hS p _ _ _ _ _)).trans
            (comp₅_congr (modulePullbackReindex_pullbackTransport p ht₀ F et)
              (modulePullbackReindex_comp' (modulePullbackCompIsoAssoc B S hS) p P₀ P hP α
                K₁ K₂)
              (modulePullbackReindex_pullbackTransport p hm₀ F em)
              (modulePullbackReindex_comp' (modulePullbackCompIsoAssoc B S hS) p Q₀ Q hQ α
                L₁ L₂)
              (modulePullbackReindex_pullbackTransport p hs₀.symm F es)))
    _ = pullbackTransport F ht ≫
          (modulePullbackReindex P α ≫ pullbackTransport F hm ≫
            modulePullbackReindex Q α) ≫
          pullbackTransport F hs.symm :=
        comp_transport_merge₃ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (pullbackTransport_comp₃ B S hS F E₁.symm et K₁ ht)
          (pullbackTransport_comp₃ B S hS F K₂ em L₁ hm)
          (pullbackTransport_comp₃ B S hS F L₂ es E₂.symm hs.symm)

/-- Reindexing a morphism flanked by two canonical identifications. -/
theorem modulePullbackReindex_pullbackTransport_sandwich
    {V W Y : AlgebraicSpaces B S hS} (f : V ⟶ W)
    {a b c d : W ⟶ Y} {M : Modules.{u, u} B S hS Y.1 Y.2} (hab : a = b) (hcd : c = d)
    (R : (modulePullback B S hS b).obj M ⟶ (modulePullback B S hS c).obj M)
    (e₁ : f ≫ a = f ≫ b) (e₂ : f ≫ c = f ≫ d) :
    modulePullbackReindex f
        (pullbackTransport M hab ≫ R ≫ pullbackTransport M hcd) =
      pullbackTransport M e₁ ≫ modulePullbackReindex f R ≫ pullbackTransport M e₂ :=
  (modulePullbackReindex_comp₃ B S hS f _ R _).trans
    (comp₃_congr (modulePullbackReindex_pullbackTransport f hab M e₁) rfl
      (modulePullbackReindex_pullbackTransport f hcd M e₂))

/-- Contracting two successive reindexings flanked by two canonical identifications: the
composite of the two reindexing morphisms is given as a separate morphism together with an
equation identifying it. -/
theorem transport_comp_reindex_comp_transport {U V W Y : AlgebraicSpaces B S hS} (w : W ⟶ V)
    (m : V ⟶ U) (n : W ⟶ U) (hn : w ≫ m = n) {a b : U ⟶ Y}
    {M : Modules.{u, u} B S hS Y.1 Y.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M)
    {p q : W ⟶ Y} (e₁ : p = w ≫ m ≫ a) (e₂ : w ≫ m ≫ b = q)
    (E₁ : p = n ≫ a) (E₂ : n ≫ b = q) :
    pullbackTransport M e₁ ≫
        modulePullbackReindex w (modulePullbackReindex m α) ≫ pullbackTransport M e₂ =
      pullbackTransport M E₁ ≫ modulePullbackReindex n α ≫ pullbackTransport M E₂ :=
  have e₃ : w ≫ m ≫ a = n ≫ a := congrArg (· ≫ a) hn
  have e₄ : n ≫ b = w ≫ m ≫ b := congrArg (· ≫ b) hn.symm
  (comp₃_congr rfl
      (modulePullbackReindex_comp' (modulePullbackCompIsoAssoc B S hS) w m n hn α e₃ e₄)
      rfl).trans
    (comp_transport_merge _ _ _ _ _ _ _ (pullbackTransport_comp M e₁ e₃ E₁)
      (pullbackTransport_comp M e₄ e₂ E₂))

/-- Reindexing `AlgebraicGeometry.Space.groupoidReindexTransport` along a morphism `w` into the
arrow space of the source groupoid is the reindexing of the given transition morphism along the
morphism `w` induces into the arrow space of the target groupoid. -/
theorem modulePullbackReindex_groupoidReindexTransport (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F)
    {W : AlgebraicSpaces B S hS} (w : W ⟶ G.arrows) (n : W ⟶ G'.arrows)
    (hn : w ≫ φ.arrowsMap = n)
    (E₁ : w ≫ G.target ≫ φ.objectsMap = n ≫ G'.target)
    (E₂ : n ≫ G'.source = w ≫ G.source ≫ φ.objectsMap) :
    modulePullbackReindex w (groupoidReindexTransport B S hS φ F α) =
      pullbackTransport F E₁ ≫ modulePullbackReindex n α ≫ pullbackTransport F E₂ :=
  have e₁ : w ≫ G.target ≫ φ.objectsMap = w ≫ φ.arrowsMap ≫ G'.target :=
    congrArg (w ≫ ·) φ.arrowsMap_comp_target.symm
  have e₂ : w ≫ φ.arrowsMap ≫ G'.source = w ≫ G.source ≫ φ.objectsMap :=
    congrArg (w ≫ ·) φ.arrowsMap_comp_source
  (congrArg (fun x => modulePullbackReindex w x)
        (groupoidReindexTransport_eq_comp B S hS φ F α)).trans
    ((modulePullbackReindex_pullbackTransport_sandwich B S hS w φ.arrowsMap_comp_target.symm
          φ.arrowsMap_comp_source _ e₁ e₂).trans
      (transport_comp_reindex_comp_transport B S hS w φ.arrowsMap n hn α e₁ e₂ E₁ E₂))

/-- **Flattening a reindexing of the transition morphism of the inverse image.**  Reindexing
`f^*α` along a morphism `w` into the arrow space of the source groupoid and flattening along the
map on objects is the reindexing of `α` along the morphism `w` induces into the arrow space of
the target groupoid, read between the two squares of `f`.

This is the identity both laws of the inverse image reduce to. -/
theorem modulePullbackFlatten_reindex_groupoidTransition (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F)
    {W : AlgebraicSpaces B S hS} (w : W ⟶ G.arrows) (n : W ⟶ G'.arrows)
    (hn : w ≫ φ.arrowsMap = n)
    (E₁ : w ≫ G.target ≫ φ.objectsMap = n ≫ G'.target)
    (E₂ : n ≫ G'.source = w ≫ G.source ≫ φ.objectsMap) :
    modulePullbackFlatten φ.objectsMap
        (modulePullbackReindex w (groupoidModulePullbackTransition B S hS φ F α)) =
      pullbackTransport F E₁ ≫ modulePullbackReindex n α ≫ pullbackTransport F E₂ :=
  (congrArg (fun x => modulePullbackFlatten φ.objectsMap (modulePullbackReindex w x))
        (groupoidModulePullbackTransition_eq B S hS φ F α)).trans
    ((modulePullbackFlatten_reindex_unflatten B S hS φ.objectsMap _ w).trans
      (modulePullbackReindex_groupoidReindexTransport B S hS φ F α w n hn E₁ E₂))

/-- **The unit law for the transition morphism of the inverse image.**  If the transition
morphism `α` of a module on the target groupoid restricts along the unit arrow to the canonical
identification of the two inverse images, then so does the transition morphism of the inverse
image along the unit arrow of the source groupoid.

This is the unit law of Stacks 0441 for the pair `(f^*ℱ, f^*α)`. -/
@[stacks 0442 "the unit law for the transition morphism of the inverse image"]
theorem groupoidModulePullbackTransition_unit (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F)
    (hunit : groupoidPullbackTransition B S hS G' F α (identityArrow G') =
      pullbackTransport F ((identityArrow_comp_target G').trans
        (identityArrow_comp_source G').symm)) :
    groupoidPullbackTransition B S hS G ((modulePullback B S hS φ.objectsMap).obj F)
        (groupoidModulePullbackTransition B S hS φ F α) (identityArrow G) =
      pullbackTransport ((modulePullback B S hS φ.objectsMap).obj F)
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) := by
  have E₁ : identityArrow G ≫ G.target ≫ φ.objectsMap =
      (φ.objectsMap ≫ identityArrow G') ≫ G'.target := by
    rw [← Category.assoc, identityArrow_comp_target, Category.id_comp, Category.assoc,
      identityArrow_comp_target, Category.comp_id]
  have E₂ : (φ.objectsMap ≫ identityArrow G') ≫ G'.source =
      identityArrow G ≫ G.source ≫ φ.objectsMap := by
    rw [Category.assoc, identityArrow_comp_source, Category.comp_id, ← Category.assoc,
      identityArrow_comp_source, Category.id_comp]
  have eN : (φ.objectsMap ≫ identityArrow G') ≫ G'.target =
      (φ.objectsMap ≫ identityArrow G') ≫ G'.source := by
    rw [Category.assoc, identityArrow_comp_target, Category.assoc, identityArrow_comp_source]
  have E : identityArrow G ≫ G.target ≫ φ.objectsMap =
      identityArrow G ≫ G.source ≫ φ.objectsMap := by
    rw [← Category.assoc, identityArrow_comp_target, ← Category.assoc,
      identityArrow_comp_source]
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex] at hunit
  have key : modulePullbackReindex (φ.objectsMap ≫ identityArrow G') α =
      pullbackTransport F eN :=
    ((modulePullbackCompIsoAssoc B S hS).modulePullbackReindex_comp φ.objectsMap
          (identityArrow G') α).symm.trans
      ((congrArg (fun x => modulePullbackReindex φ.objectsMap x) hunit).trans
        (modulePullbackReindex_pullbackTransport φ.objectsMap _ F eN))
  refine modulePullbackFlatten_injective φ.objectsMap ?_
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex,
    modulePullbackFlatten_pullbackTransport φ.objectsMap _ F E]
  exact (modulePullbackFlatten_reindex_groupoidTransition B S hS φ F α (identityArrow G)
        (φ.objectsMap ≫ identityArrow G') φ.identityArrow_comp_arrowsMap E₁ E₂).trans
    ((comp₃_congr rfl key rfl).trans (pullbackTransport_comp₃ B S hS F E₁ eN E₂ E))

/-- **The cocycle law for the transition morphism of the inverse image.**  If the transition
morphism `α` of a module on the target groupoid satisfies the cocycle law on the space of
composable pairs of arrows of the target groupoid, then the transition morphism of the inverse
image satisfies it on the space of composable pairs of arrows of the source groupoid.

This is the cocycle law of Stacks 0441 for the pair `(f^*ℱ, f^*α)`.  Flattened along the map on
objects, both sides become the corresponding sides of the law for `α` at the three morphisms the
map on composable pairs carries the composition and the two projections to. -/
@[stacks 0442 "the cocycle law for the transition morphism of the inverse image"]
theorem groupoidModulePullbackTransition_cocycle (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F)
    (hcocycle : groupoidPullbackTransition B S hS G' F α G'.comp =
      groupoidTransitionComposite B S hS G' F α) :
    groupoidPullbackTransition B S hS G ((modulePullback B S hS φ.objectsMap).obj F)
        (groupoidModulePullbackTransition B S hS φ F α) G.comp =
      groupoidTransitionComposite B S hS G ((modulePullback B S hS φ.objectsMap).obj F)
        (groupoidModulePullbackTransition B S hS φ F α) := by
  have htp : (φ.compPairsMap ≫ G'.comp) ≫ G'.target =
      (φ.compPairsMap ≫ firstArrow G') ≫ G'.target := by
    rw [Category.assoc, Category.assoc, comp_comp_target G']
  have hmp : (φ.compPairsMap ≫ firstArrow G') ≫ G'.source =
      (φ.compPairsMap ≫ secondArrow G') ≫ G'.target := by
    rw [Category.assoc, Category.assoc, firstArrow_comp_source G']
  have hsp : (φ.compPairsMap ≫ G'.comp) ≫ G'.source =
      (φ.compPairsMap ≫ secondArrow G') ≫ G'.source := by
    rw [Category.assoc, Category.assoc, comp_comp_source G']
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex, groupoidTransitionComposite_eq,
    transitionComposite_eq_comp] at hcocycle
  have hcoc := modulePullbackReindex_cocycle_comp B S hS F α (firstArrow G')
    (secondArrow G') G'.comp φ.compPairsMap _ _ _ rfl rfl rfl
    (ht₀ := comp_comp_target G') (hm₀ := firstArrow_comp_source G')
    (hs₀ := comp_comp_source G') hcocycle htp hmp hsp
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex, groupoidTransitionComposite_eq,
    transitionComposite_eq_comp]
  exact modulePullbackReindex_cocycle_of_flatten (modulePullbackCompIsoAssoc B S hS)
    φ.objectsMap φ.arrowsMap F α (groupoidModulePullbackTransition B S hS φ F α)
    (modulePullbackFlatten_groupoidModulePullbackTransition B S hS φ F α)
    (firstArrow G) (secondArrow G) G.comp (φ.compPairsMap ≫ firstArrow G')
    (φ.compPairsMap ≫ secondArrow G') (φ.compPairsMap ≫ G'.comp)
    φ.compPairsMap_comp_firstArrow.symm φ.compPairsMap_comp_secondArrow.symm
    φ.comp_comp_arrowsMap (comp_comp_target G) (firstArrow_comp_source G)
    (comp_comp_source G) htp hmp hsp hcoc

/-- **The transition morphism of the inverse image is natural in the module.**  A morphism of
modules on the objects of the target groupoid which intertwines two transition morphisms
intertwines their inverse images. -/
theorem groupoidModulePullbackTransition_naturality (φ : Hom G G')
    (F : Modules.{u, u} B S hS G'.objects.1 G'.objects.2)
    (α : (modulePullback B S hS G'.target).obj F ⟶ (modulePullback B S hS G'.source).obj F)
    {N : Modules.{u, u} B S hS G'.objects.1 G'.objects.2}
    (β : (modulePullback B S hS G'.target).obj N ⟶ (modulePullback B S hS G'.source).obj N)
    (ψ : F ⟶ N)
    (hψ : α ≫ (modulePullback B S hS G'.source).map ψ =
      (modulePullback B S hS G'.target).map ψ ≫ β) :
    groupoidModulePullbackTransition B S hS φ F α ≫
        (modulePullback B S hS G.source).map ((modulePullback B S hS φ.objectsMap).map ψ) =
      (modulePullback B S hS G.target).map ((modulePullback B S hS φ.objectsMap).map ψ) ≫
        groupoidModulePullbackTransition B S hS φ N β :=
  (comp₂_congr (groupoidModulePullbackTransition_eq B S hS φ F α) rfl).trans
    ((modulePullbackUnflatten_naturality φ.objectsMap ψ
          (groupoidReindexTransport B S hS φ F α) (groupoidReindexTransport B S hS φ N β)
          (((comp₂_congr (groupoidReindexTransport_eq_comp B S hS φ F α) rfl).trans
                (transportReindexTransport_naturality φ.arrowsMap
                  φ.arrowsMap_comp_target.symm φ.arrowsMap_comp_source α β ψ hψ)).trans
            (comp₂_congr rfl (groupoidReindexTransport_eq_comp B S hS φ N β).symm))).trans
      (comp₂_congr rfl (groupoidModulePullbackTransition_eq B S hS φ N β).symm))

/-- **The inverse image of a quasi-coherent module on a groupoid in algebraic spaces** along a
morphism `f` of groupoids in algebraic spaces: the inverse image of the underlying quasi-coherent
module on the space of objects, together with the transition morphism `f^*α`, which satisfies the
cocycle and unit conditions by the two laws above.

Quasi-coherence of the underlying module transports along an arbitrary morphism of algebraic
spaces by `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`
(Stacks 03GA), so no hypothesis on `φ.objectsMap` is needed here. -/
def groupoidQuasicoherentPullbackObj (φ : Hom G G')
    (M : QuasicoherentModule B S hS G') : QuasicoherentModule B S hS G where
  F := ⟨(modulePullback B S hS φ.objectsMap).obj M.F.obj,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ.objectsMap
      M.F.obj M.F.property⟩
  alpha := groupoidModulePullbackTransition B S hS φ M.F.obj M.alpha
  cocycle := groupoidModulePullbackTransition_cocycle B S hS φ M.F.obj M.alpha M.cocycle
  unit := groupoidModulePullbackTransition_unit B S hS φ M.F.obj M.alpha M.unit

end Space

end AlgebraicGeometry

end
