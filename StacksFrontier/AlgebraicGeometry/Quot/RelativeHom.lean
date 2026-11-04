module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.CategoryTheory.Functor.ConjugateHom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The relative Hom functor of two quasi-coherent modules, and change of base

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` and let `F`, `G` be
quasi-coherent `𝒪_X`-modules.  Every scheme `T` over `B` gives a base change
`X_T = X ×_B T` and pullbacks `F_T`, `G_T` of the two modules along the projection
`X_T ⟶ X`, and Stacks 08JT considers the assignment

`T ↦ Hom_{𝒪_{X_T}}(F_T, G_T)`

as a functor `(Sch/B)ᵒᵖ ⥤ Sets`.  This file supplies the standing data, the Hom set at a test
scheme, the pullback of a homomorphism along a morphism of test schemes, and the functor.

Stacks 08JW then changes the base: a morphism `B' ⟶ B` of algebraic spaces gives the base
change `X' = X ×_B B'` with the two modules pulled back, hence a second relative Hom functor on
`(Sch/B')ᵒᵖ`, and for a scheme `T` over `B'` the two Hom sets agree,
`Hom(F', G')(T) = Hom(F, G)(T)`, naturally in `T`.  That identification is the second half of
this file.

## Main definitions

* `AlgebraicGeometry.Space.SchemesOver`, `AlgebraicGeometry.Space.baseChangeSpace`,
  `AlgebraicGeometry.Space.baseChangeProjection` and
  `AlgebraicGeometry.Space.baseChangeMap`: the base change of a morphism of algebraic spaces
  along the test schemes over its target, for an arbitrary morphism rather than for the
  standing data of one situation.
* `AlgebraicGeometry.Space.overBaseChange`, `AlgebraicGeometry.Space.overProjection`,
  `AlgebraicGeometry.Space.overBaseChangeMap` and
  `AlgebraicGeometry.Space.overBaseChangeFunctor`: the same base change along an arbitrary
  algebraic space over the target, of which the base change along the test schemes is the
  restriction along `AlgebraicGeometry.Space.schemesOverToOver`.
* `AlgebraicGeometry.Space.HomSituation`: **the standing data of Stacks 08JT.**
* `AlgebraicGeometry.Space.HomSituation.homAt`: `Hom_{𝒪_{X_T}}(F_T, G_T)`.
* `AlgebraicGeometry.Space.HomSituation.homMap`: the pullback of a homomorphism along a
  morphism of test schemes.
* `AlgebraicGeometry.Space.baseChangeOver`: the base change of a morphism along the test
  schemes, as a functor to the algebraic spaces over its source.
* `AlgebraicGeometry.Space.moduleHomOver`: the relative Hom functor of two `𝒪_X`-modules
  indexed by the algebraic spaces *over* `X`.  Every relative Hom functor here is this one
  restricted along a base change, which is what makes the comparisons natural.
* `AlgebraicGeometry.Space.HomSituation.homFunctor`: **the relative Hom functor of
  Stacks 08JT.**
* `AlgebraicGeometry.Space.HomSituation.baseChangedSituation`: **the base-changed situation of
  Stacks 08JW**, and `AlgebraicGeometry.Space.HomSituation.baseChangeFiberIso` the
  pasted-pullback identification `X'_T ≅ X_T` it rests on.

## Main results

* `AlgebraicGeometry.Space.HomSituation.homMap_id` and
  `AlgebraicGeometry.Space.HomSituation.homMap_comp`: pullback of homomorphisms is functorial
  in the test scheme.  These are what make `homFunctor` a functor, and they are where the
  coherences of Stacks 03LU are consumed.
* `AlgebraicGeometry.Space.HomSituation.homFunctor_obj` and
  `AlgebraicGeometry.Space.HomSituation.homFunctor_map`: the functor's value at a test scheme
  is the Hom set of the base-changed modules, and its action is pullback of homomorphisms.
* `AlgebraicGeometry.Space.moduleHomOverPullback`: pulling the two modules back along a
  morphism `q` commutes with the relative Hom functor over the algebraic spaces.  This is the
  content of Stacks 08JW with the test schemes not yet in sight.
* `AlgebraicGeometry.Space.HomSituation.homFunctorBaseChange`: **Stacks 08JW**, the
  identification `Hom(F', G')(T) = Hom(F, G)(T)` as an isomorphism of functors.
* `AlgebraicGeometry.Space.ModuleMapSituation.baseChangeSpace_eq` and its two siblings: the
  base-change machinery of the standing data of Stacks 083F is this one, at its morphism.

## Implementation notes

**Where the coherence data comes from.**  Pullback of homomorphisms is functorial exactly
because the inverse images of Stacks 03LU are pseudofunctorial, which is
`AlgebraicGeometry.Space.ModulePushforwardCoherence`, the coherence data for the *direct*
images, from which the inverse-image coherences follow (see
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`).  That data
is proved with no hypothesis by `AlgebraicGeometry.Space.modulePushforwardCoherence`, and the
identification of the two relative Hom functors under a change of base uses it, so that
identification assumes nothing.  The Hom functor itself still takes the data as a parameter,
which lets a consumer that carries its own copy use that one.  Nothing else about the Hom
functor needs the data at all: the standing data, the Hom set at a test scheme and the
pullback of a homomorphism are unconditional.

Test schemes over the target are the costructured arrows from
`AlgebraicGeometry.schemeSpaceFunctor` — a scheme of the big fppf site regarded as an
algebraic space — so that a morphism of test schemes is a morphism of schemes commuting with
the two maps to the target.  The base-change machinery is stated for an arbitrary morphism
`f : X ⟶ Y` of algebraic spaces, which is its natural generality; the identically-named
methods of `AlgebraicGeometry.Space.ModuleMapSituation`, the standing data of Stacks 083F, are
the same constructions bound to that structure, and
`AlgebraicGeometry.Space.ModuleMapSituation.baseChangeSpace_eq` and its two siblings identify
them.

Quasi-coherence of the two modules is standing data, as in the source, and is never used for
the Hom functor itself: the Hom set is taken in all `𝒪_{X_T}`-modules.  Forming the
base-changed situation of Stacks 08JW does need it for the two pullbacks, and the pullback of a
quasi-coherent module along an arbitrary morphism of algebraic spaces is quasi-coherent — that
is Stacks 03GA, proved for an arbitrary morphism by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` — so
`AlgebraicGeometry.Space.HomSituation.baseChangedSituation` builds those two fields from the
quasi-coherence of `F` and `G` themselves and needs nothing further.

**Stacks 08JW is proved by whiskering, not by a hand-written naturality square.**  Both
relative Hom functors factor through `AlgebraicGeometry.Space.moduleHomOver`, indexed by the
algebraic spaces over `X` rather than by the test schemes, and the identification is the
composite of two whiskerings: `AlgebraicGeometry.Space.moduleHomOverPullback`, which is where
the comparison of Stacks 03LU is used, and the opposite of
`AlgebraicGeometry.Space.HomSituation.baseChangeOverIso`, whose components are the
pasted-pullback identifications and whose naturality is
`AlgebraicGeometry.Space.HomSituation.baseChangeFiberIso_naturality`, a pullback-uniqueness
argument.  Naturality in the test scheme is then automatic.  The single coherence with content
is `AlgebraicGeometry.Space.transportHom_modulePullbackTriangle`, one instance of the
associativity coherence of Stacks 03LU.

`AlgebraicGeometry.Space.HomSituation.homAt` is a `def` and not an `abbrev`, and the two
functoriality laws are deduced from `CategoryTheory.Functor.conjHom_id` and
`CategoryTheory.Functor.conjHom_comp` rather than proved in place.  Both choices are forced by
the cost of comparing the categories of modules involved: with the Hom set reducible, the
unifier unfolds it to the underlying homomorphisms of sheaves of modules and compares those
structurally, which does not terminate within the heartbeat limit, and a functoriality proof
written in place leaves a proof term the kernel does not finish checking.  Factoring the
computation through a general statement about an abstract comparison leaves only a syntactic
match at the point of use.

The module universe is the universe of the structure rings, as it is for
`AlgebraicGeometry.Space.modulePullback`.

## References

* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 04U8](https://stacks.math.columbia.edu/tag/04U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u m

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- The test schemes over an algebraic space: the schemes of the big fppf site of `S`,
regarded as algebraic spaces, equipped with a morphism to it. -/
abbrev SchemesOver (Y : AlgebraicSpaces B S hS) :=
  CostructuredArrow (schemeSpaceFunctor B S hS) Y

/-- A test scheme over `Z`, read as an algebraic space over `Z`.  Base change along the test
schemes is base change along the algebraic spaces over `Z`, restricted along this. -/
abbrev schemesOverToOver (Z : AlgebraicSpaces B S hS) : SchemesOver Z ⥤ Over Z :=
  CostructuredArrow.toOver (schemeSpaceFunctor B S hS) Z

/-! ### Base change along the algebraic spaces over the target -/

/-- The base change `X_T = X ×_Y T` of `f : X ⟶ Y` along an algebraic space `T` over `Y`. -/
def overBaseChange (f : X ⟶ Y) (T : Over Y) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS f T.hom

/-- The projection `X_T ⟶ X`. -/
def overProjection (f : X ⟶ Y) (T : Over Y) : overBaseChange f T ⟶ X :=
  ObjectProperty.homMk (pullback.fst f.hom T.hom.hom)

/-- The projection `X_T ⟶ T`. -/
def overInclusion (f : X ⟶ Y) (T : Over Y) : overBaseChange f T ⟶ T.left :=
  ObjectProperty.homMk (pullback.snd f.hom T.hom.hom)

/-- The morphism `X_U ⟶ X_T` of base changes induced by a morphism `U ⟶ T` of algebraic spaces
over `Y`. -/
def overBaseChangeMap (f : X ⟶ Y) {U T : Over Y} (g : U ⟶ T) :
    overBaseChange f U ⟶ overBaseChange f T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f T.hom).lift
    (overProjection f U)
    (overInclusion f U ≫ g.left)
    (by
      rw [Category.assoc, Over.w g]
      exact ObjectProperty.hom_ext _ pullback.condition)

/-- The morphisms of base changes commute with the projections to the source. -/
@[reassoc (attr := simp)]
theorem overBaseChangeMap_comp_projection (f : X ⟶ Y) {U T : Over Y} (g : U ⟶ T) :
    overBaseChangeMap f g ≫ overProjection f T = overProjection f U :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f T.hom).lift_fst _ _ _

/-- The morphisms of base changes commute with the projections to the algebraic spaces over
`Y`. -/
@[reassoc (attr := simp)]
theorem overBaseChangeMap_comp_inclusion (f : X ⟶ Y) {U T : Over Y} (g : U ⟶ T) :
    overBaseChangeMap f g ≫ overInclusion f T = overInclusion f U ≫ g.left :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f T.hom).lift_snd _ _ _

/-- A morphism into a base change is determined by its two projections. -/
theorem overBaseChange_hom_ext (f : X ⟶ Y) {T : Over Y} {W : AlgebraicSpaces B S hS}
    {k l : W ⟶ overBaseChange f T}
    (h₁ : k ≫ overProjection f T = l ≫ overProjection f T)
    (h₂ : k ≫ overInclusion f T = l ≫ overInclusion f T) : k = l :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f T.hom).hom_ext h₁ h₂

/-- Base change along the identity is the identity. -/
@[simp]
theorem overBaseChangeMap_id (f : X ⟶ Y) (T : Over Y) :
    overBaseChangeMap f (𝟙 T) = 𝟙 (overBaseChange f T) := by
  refine overBaseChange_hom_ext f ?_ ?_ <;> simp

/-- Base change along a composite is the composite of the base changes. -/
theorem overBaseChangeMap_comp (f : X ⟶ Y) {V U T : Over Y} (g : V ⟶ U) (h : U ⟶ T) :
    overBaseChangeMap f (g ≫ h) = overBaseChangeMap f g ≫ overBaseChangeMap f h := by
  refine overBaseChange_hom_ext f ?_ ?_ <;> simp

/-- **The square of a morphism of algebraic spaces over the target is cartesian.**  The
morphism `X_U ⟶ X_T` of base changes induced by a morphism `U ⟶ T` of algebraic spaces over
`Y`, together with the two projections to those algebraic spaces, is a cartesian square over
the induced morphism.

Cartesian squares cancel on the right (`IsPullback.of_right`): the outer square, whose
composites are the projection `X_U ⟶ X` and the structure morphism of `U`, is cartesian, as is
the square defining `X_T` on its right, hence so is the square on the left. -/
theorem isPullback_overBaseChangeMap (f : X ⟶ Y) {U T : Over Y} (g : U ⟶ T) :
    IsPullback (overBaseChangeMap f g) (overInclusion f U) (overInclusion f T) g.left := by
  have ht : IsPullback (overProjection f T) (overInclusion f T) f T.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f T.hom
  have hu : IsPullback (overProjection f U) (overInclusion f U) f U.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f U.hom
  have hs : IsPullback (overBaseChangeMap f g ≫ overProjection f T) (overInclusion f U) f
      (g.left ≫ T.hom) := by
    rw [overBaseChangeMap_comp_projection, Over.w g]
    exact hu
  exact IsPullback.of_right hs (overBaseChangeMap_comp_inclusion f g) ht

/-- The base change of `f : X ⟶ Y` along the algebraic spaces over `Y`, as a functor to the
algebraic spaces over `X`: the projection `X_T ⟶ X` makes `X_T` an object over `X`, and the
transition maps are morphisms over `X`. -/
def overBaseChangeFunctor (f : X ⟶ Y) : Over Y ⥤ Over X where
  obj T := Over.mk (overProjection f T)
  map g := Over.homMk (overBaseChangeMap f g) (overBaseChangeMap_comp_projection f g)
  map_id T := by
    ext
    simp
  map_comp g h := by
    ext
    simp [overBaseChangeMap_comp]

/-! ### Base change along the test schemes over the target -/

/-- The base change `X_T = X ×_Y T` of `f : X ⟶ Y` along a test scheme `T` over `Y`. -/
def baseChangeSpace (f : X ⟶ Y) (T : SchemesOver Y) : AlgebraicSpaces B S hS :=
  overBaseChange f ((schemesOverToOver Y).obj T)

/-- The projection `X_T ⟶ X`. -/
def baseChangeProjection (f : X ⟶ Y) (T : SchemesOver Y) : baseChangeSpace f T ⟶ X :=
  overProjection f ((schemesOverToOver Y).obj T)

/-- The projection `X_T ⟶ T`. -/
def baseChangeInclusion (f : X ⟶ Y) (T : SchemesOver Y) :
    baseChangeSpace f T ⟶ (schemeSpaceFunctor B S hS).obj T.left :=
  overInclusion f ((schemesOverToOver Y).obj T)

/-- The morphism `X_U ⟶ X_T` of base changes induced by a morphism `U ⟶ T` of test
schemes. -/
def baseChangeMap (f : X ⟶ Y) {U T : SchemesOver Y} (g : U ⟶ T) :
    baseChangeSpace f U ⟶ baseChangeSpace f T :=
  overBaseChangeMap f ((schemesOverToOver Y).map g)

/-- The morphisms of base changes commute with the projections to the source. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_comp_projection (f : X ⟶ Y) {U T : SchemesOver Y} (g : U ⟶ T) :
    baseChangeMap f g ≫ baseChangeProjection f T = baseChangeProjection f U :=
  overBaseChangeMap_comp_projection f _

/-- The morphisms of base changes commute with the projections to the test schemes. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_comp_inclusion (f : X ⟶ Y) {U T : SchemesOver Y} (g : U ⟶ T) :
    baseChangeMap f g ≫ baseChangeInclusion f T =
      baseChangeInclusion f U ≫ (schemeSpaceFunctor B S hS).map g.left :=
  overBaseChangeMap_comp_inclusion f _

/-- A morphism into a base change is determined by its two projections. -/
theorem baseChange_hom_ext (f : X ⟶ Y) {T : SchemesOver Y} {W : AlgebraicSpaces B S hS}
    {k l : W ⟶ baseChangeSpace f T}
    (h₁ : k ≫ baseChangeProjection f T = l ≫ baseChangeProjection f T)
    (h₂ : k ≫ baseChangeInclusion f T = l ≫ baseChangeInclusion f T) : k = l :=
  overBaseChange_hom_ext f h₁ h₂

/-- Base change along the identity of a test scheme is the identity. -/
@[simp]
theorem baseChangeMap_id (f : X ⟶ Y) (T : SchemesOver Y) :
    baseChangeMap f (𝟙 T) = 𝟙 (baseChangeSpace f T) :=
  overBaseChangeMap_id f _

/-- Base change along a composite of morphisms of test schemes is the composite of the base
changes. -/
theorem baseChangeMap_comp (f : X ⟶ Y) {V U T : SchemesOver Y} (g : V ⟶ U) (h : U ⟶ T) :
    baseChangeMap f (g ≫ h) = baseChangeMap f g ≫ baseChangeMap f h := by
  rw [baseChangeMap, baseChangeMap, baseChangeMap, Functor.map_comp]
  exact overBaseChangeMap_comp f _ _

/-- **The square of a morphism of test schemes is cartesian.**  The morphism `X_U ⟶ X_T` of base
changes induced by a morphism `U ⟶ T` of test schemes, together with the two projections to the
test schemes, is a cartesian square over the induced morphism of test schemes.

Cartesian squares cancel on the right (`IsPullback.of_right`): the outer square, whose
composites are the projection `X_U ⟶ X` and the structure morphism of `U`, is cartesian, as is
the square defining `X_T` on its right, hence so is the square on the left. -/
theorem isPullback_baseChangeMap (f : X ⟶ Y) {U T : SchemesOver Y} (g : U ⟶ T) :
    IsPullback (baseChangeMap f g) (baseChangeInclusion f U) (baseChangeInclusion f T)
      ((schemeSpaceFunctor B S hS).map g.left) :=
  isPullback_overBaseChangeMap f ((schemesOverToOver Y).map g)

/-- The base change of `f : X ⟶ Y` along the test schemes over `Y`, as a functor to the
algebraic spaces over `X`: the projection `X_T ⟶ X` makes `X_T` an object over `X`, and the
transition maps are morphisms over `X`. -/
def baseChangeOver (f : X ⟶ Y) : SchemesOver Y ⥤ Over X :=
  schemesOverToOver Y ⋙ overBaseChangeFunctor f

/-- The Hom set of the two pulled-back modules on an algebraic space over `X`. -/
def moduleHomOverObj (F G : Modules.{u, u} B S hS X.1 X.2) (Z : Over X) : Type (u + 1) :=
  (modulePullback B S hS Z.hom).obj F ⟶ (modulePullback B S hS Z.hom).obj G

/-- The Hom set over an algebraic space over `X` is the set of homomorphisms of the two
pulled-back modules. -/
theorem moduleHomOverObj_eq (F G : Modules.{u, u} B S hS X.1 X.2) (Z : Over X) :
    moduleHomOverObj F G Z =
      ((modulePullback B S hS Z.hom).obj F ⟶ (modulePullback B S hS Z.hom).obj G) :=
  rfl

/-- **The relative Hom functor of two `𝒪_X`-modules, indexed by the algebraic spaces over
`X`.**  It sends an algebraic space `z : Z ⟶ X` over `X` to the `𝒪_Z`-module homomorphisms
`z^*F ⟶ z^*G`, and a morphism over `X` to pullback of homomorphisms.

Its two functor laws are the unit law and the associativity coherence of Stacks 03LU, so it
carries the coherence data as a hypothesis.  Every relative Hom functor in this file is this
one composed with a base change. -/
def moduleHomOver (hc : ModulePushforwardCoherence B S hS)
    (F G : Modules.{u, u} B S hS X.1 X.2) : (Over X)ᵒᵖ ⥤ Type (u + 1) where
  obj Z := moduleHomOverObj F G Z.unop
  map m := ↾Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop))
  map_id Z := congrArg TypeCat.ofHom (funext fun α ↦
    Functor.conjHom_id _ _ (hc.modulePullbackTriangle_id _) α)
  map_comp m n := congrArg TypeCat.ofHom (funext fun α ↦
    Functor.conjHom_comp _ _ _
      (modulePullbackTriangle B S hS
        (rfl : n.unop.left ≫ m.unop.left = (m ≫ n).unop.left))
      (hc.modulePullbackTriangle_comp' rfl (Over.w m.unop) (Over.w n.unop)
        (Over.w (m ≫ n).unop)) α)

/-- The comparison of the inverse image along `z ≫ q` with the iterated inverse image is
compatible with pullback along a morphism over `W`.  This is the naturality that makes
`AlgebraicGeometry.Space.moduleHomOverPullback` a natural isomorphism. -/
theorem transportHom_modulePullbackTriangle (hc : ModulePushforwardCoherence B S hS)
    {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) (F G : Modules.{u, u} B S hS V.1 V.2)
    {Z Z' : Over W} (m : Z' ⟶ Z)
    (α : (modulePullback B S hS Z.hom).obj ((modulePullback B S hS q).obj F) ⟶
      (modulePullback B S hS Z.hom).obj ((modulePullback B S hS q).obj G)) :
    Functor.transportHom
        (modulePullbackTriangle B S hS (rfl : Z'.hom ≫ q = Z'.hom ≫ q))
        (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m)) α) =
      Functor.conjHom (modulePullbackTriangle B S hS (Over.w ((Over.map q).map m)))
        (Functor.transportHom
          (modulePullbackTriangle B S hS (rfl : Z.hom ≫ q = Z.hom ≫ q)) α) := by
  have h : modulePullbackTriangle B S hS (rfl : Z'.hom ≫ q = Z'.hom ≫ q) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS q)
            (modulePullbackTriangle B S hS (Over.w m)) ≪≫
          (Functor.associator (modulePullback B S hS q) (modulePullback B S hS Z.hom)
            (modulePullback B S hS m.left)).symm) =
      modulePullbackTriangle B S hS (Over.w ((Over.map q).map m)) ≪≫
        Functor.isoWhiskerRight
          (modulePullbackTriangle B S hS (rfl : Z.hom ≫ q = Z.hom ≫ q))
          (modulePullback B S hS m.left) := by
    rw [← Iso.trans_assoc, hc.modulePullbackTriangle_comp (Over.w m)
      (rfl : Z.hom ≫ q = Z.hom ≫ q) (Over.w ((Over.map q).map m))
      (rfl : Z'.hom ≫ q = Z'.hom ≫ q)]
    simp
  rw [← Functor.conjHom_isoWhiskerLeft (modulePullback B S hS q)
    (modulePullbackTriangle B S hS (Over.w m)) α]
  exact Functor.transportHom_conjHom _ _ _ _ h α

/-- Applying a composite of two functions, read as a composite in the category of types. -/
theorem ofHom_comp_apply {A A' A'' : Type (u + 1)} (f : A → A') (g : A' → A'') (a : A) :
    ConcreteCategory.hom (↾f ≫ ↾g) a = g (f a) := rfl

/-- Two composites of functions, read as composites in the category of types, agree as soon as
they agree on every element. -/
theorem ofHom_comp_eq_comp {A A' A'' B' : Type (u + 1)} (f : A → A') (g : A' → A'')
    (g' : A → B') (f' : B' → A'') (h : ∀ a, g (f a) = f' (g' a)) :
    (↾f) ≫ (↾g) = (↾g') ≫ (↾f') := by
  refine ConcreteCategory.hom_ext _ _ fun a ↦ ?_
  rw [ofHom_comp_apply, ofHom_comp_apply]
  exact h a

/-- Transport along the comparison of the inverse image along `z ≫ q` with the iterated
inverse image, as an isomorphism of the two Hom sets. -/
def moduleHomOverTransport {V W : AlgebraicSpaces B S hS} (q : W ⟶ V)
    (F G : Modules.{u, u} B S hS V.1 V.2) (Z : Over W) :
    moduleHomOverObj ((modulePullback B S hS q).obj F)
        ((modulePullback B S hS q).obj G) Z ≅
      moduleHomOverObj F G ((Over.map q).obj Z) where
  hom := ↾(Functor.transportHom
    (modulePullbackTriangle B S hS (rfl : Z.hom ≫ q = Z.hom ≫ q)))
  inv := ↾(Functor.transportHom
    (modulePullbackTriangle B S hS (rfl : Z.hom ≫ q = Z.hom ≫ q)).symm)
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun α ↦
    (Functor.transportHomEquiv
      (modulePullbackTriangle B S hS (rfl : Z.hom ≫ q = Z.hom ≫ q)) F G).left_inv α
  inv_hom_id := ConcreteCategory.hom_ext _ _ fun α ↦
    (Functor.transportHomEquiv
      (modulePullbackTriangle B S hS (rfl : Z.hom ≫ q = Z.hom ≫ q)) F G).right_inv α

/-- **Pulling the two modules back along `q : W ⟶ V` commutes with the relative Hom functor
over the algebraic spaces.**  The relative Hom functor of the pullbacks, over the algebraic
spaces over `W`, is the relative Hom functor of the two modules themselves, restricted along
`Over.map q`.

This is the content of Stacks 08JW with the test schemes not yet in sight: it is naturality in
the algebraic space over `W` that makes the identification of Stacks 08JW natural in the test
scheme. -/
def moduleHomOverPullback (hc : ModulePushforwardCoherence B S hS)
    {V W : AlgebraicSpaces B S hS} (q : W ⟶ V)
    (F G : Modules.{u, u} B S hS V.1 V.2) :
    moduleHomOver hc ((modulePullback B S hS q).obj F)
        ((modulePullback B S hS q).obj G) ≅
      (Over.map q).op ⋙ moduleHomOver hc F G :=
  NatIso.ofComponents
    (fun Z ↦ moduleHomOverTransport q F G Z.unop)
    (fun {Z Z'} m ↦ ofHom_comp_eq_comp _ _ _ _ fun α ↦
      transportHom_modulePullbackTriangle hc q F G m.unop α)

/-- The base-change space of the standing data of Stacks 083F is the base change of its
morphism: the two constructions are the same, and this identifies them. -/
theorem ModuleMapSituation.baseChangeSpace_eq (D : ModuleMapSituation.{u, m} B S hS)
    (T : D.SchemesOver) :
    D.baseChangeSpace T = _root_.AlgebraicGeometry.Space.baseChangeSpace D.f T := rfl

/-- The projection to the source of the standing data of Stacks 083F is the projection of the
base change of its morphism. -/
theorem ModuleMapSituation.baseChangeProjection_eq (D : ModuleMapSituation.{u, m} B S hS)
    (T : D.SchemesOver) :
    D.baseChangeProjection T =
      _root_.AlgebraicGeometry.Space.baseChangeProjection D.f T := rfl

/-- The transition map of the standing data of Stacks 083F is the transition map of the base
change of its morphism. -/
theorem ModuleMapSituation.baseChangeMap_eq (D : ModuleMapSituation.{u, m} B S hS)
    {U T : D.SchemesOver} (g : U ⟶ T) :
    D.baseChangeMap g = _root_.AlgebraicGeometry.Space.baseChangeMap D.f g := rfl

end BaseChange

/-- **Stacks 08JT.**  The standing data of the relative Hom functor: a morphism `f : X ⟶ base`
of algebraic spaces over `S` and two quasi-coherent `𝒪_X`-modules. -/
@[stacks 08JT "the standing data"]
structure HomSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The algebraic space carrying the two modules. -/
  X : AlgebraicSpaces B S hS
  /-- The algebraic space over which the test schemes live. -/
  base : AlgebraicSpaces B S hS
  /-- The morphism of algebraic spaces being base changed along. -/
  f : X ⟶ base
  /-- The source module. -/
  F : Modules.{u, u} B S hS X.1 X.2
  /-- The target module. -/
  G : Modules.{u, u} B S hS X.1 X.2
  /-- The source module is quasi-coherent. -/
  quasicoherent_F : F.IsQuasicoherentOnSite
  /-- The target module is quasi-coherent. -/
  quasicoherent_G : G.IsQuasicoherentOnSite

namespace HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (s : HomSituation B S hS)

/-- The test schemes over the base of the situation. -/
abbrev SchemesOver := _root_.AlgebraicGeometry.Space.SchemesOver s.base

/-- The base change `X_T` of the source along a test scheme. -/
abbrev baseChange (T : s.SchemesOver) : AlgebraicSpaces B S hS :=
  baseChangeSpace s.f T

/-- The projection `X_T ⟶ X`. -/
abbrev projection (T : s.SchemesOver) : s.baseChange T ⟶ s.X :=
  baseChangeProjection s.f T

/-- The base change `M_T` of an `𝒪_X`-module along a test scheme. -/
abbrev baseChangedModule (T : s.SchemesOver) (M : Modules.{u, u} B S hS s.X.1 s.X.2) :=
  (modulePullback B S hS (s.projection T)).obj M

/-- **Stacks 08JT.**  The value of the relative Hom functor at a test scheme `T` over the
base: the `𝒪_{X_T}`-module homomorphisms `F_T ⟶ G_T`. -/
def homAt (T : s.SchemesOver) : Type (u + 1) :=
  moduleHomOverObj s.F s.G ((baseChangeOver s.f).obj T)

/-- The Hom set at a test scheme is the set of homomorphisms of the base-changed modules. -/
theorem homAt_eq (T : s.SchemesOver) :
    s.homAt T = (s.baseChangedModule T s.F ⟶ s.baseChangedModule T s.G) := rfl

/-- The comparison of the base change to `U` with the base change to `T` followed by the
inverse image along `X_U ⟶ X_T`, as an isomorphism of the two inverse-image functors. -/
def baseChangeComparison {U T : s.SchemesOver} (g : U ⟶ T) :
    modulePullback B S hS (s.projection U) ≅
      modulePullback B S hS (s.projection T) ⋙
        modulePullback B S hS (baseChangeMap s.f g) :=
  modulePullbackTriangle B S hS (baseChangeMap_comp_projection s.f g)

/-- The comparison is the one that the base change over `X` of the test schemes provides. -/
theorem baseChangeComparison_eq {U T : s.SchemesOver} (g : U ⟶ T) :
    s.baseChangeComparison g =
      modulePullbackTriangle B S hS (Over.w ((baseChangeOver s.f).map g)) :=
  rfl

/-- **Stacks 08JT.**  The pullback of an `𝒪_{X_T}`-module homomorphism `F_T ⟶ G_T` along a
morphism `U ⟶ T` of test schemes: its inverse image along `X_U ⟶ X_T`, read through the
comparison of the two base changes. -/
def homMap {U T : s.SchemesOver} (g : U ⟶ T) (α : s.homAt T) : s.homAt U :=
  Functor.conjHom (s.baseChangeComparison g) α

/-- Pullback of a homomorphism is conjugation by the comparison of the two base changes. -/
theorem homMap_def {U T : s.SchemesOver} (g : U ⟶ T) :
    s.homMap g = Functor.conjHom (s.baseChangeComparison g) :=
  rfl

/-- The comparison for the identity morphism of a test scheme is whiskering by the unit law
`(𝟙 X_T)^* ≅ 𝟭` of Stacks 03LU, corrected by the identification of `X_T ⟶ X_T` with the
identity. -/
theorem baseChangeComparison_id (hc : ModulePushforwardCoherence B S hS) (T : s.SchemesOver) :
    s.baseChangeComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (s.projection T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (s.projection T))
          ((hc.modulePullbackIdIso (s.baseChange T)).symm ≪≫
            eqToIso (congrArg (modulePullback B S hS)
              (baseChangeMap_id s.f T).symm)) := by
  rw [baseChangeComparison,
    modulePullbackTriangle_congr_left (baseChangeMap_id s.f T)
      (baseChangeMap_comp_projection s.f (𝟙 T)) (Category.id_comp (s.projection T)),
    hc.modulePullbackTriangle_id, Functor.isoWhiskerLeft_trans, Iso.trans_assoc]

/-- **Pullback of homomorphisms along the identity is the identity.** -/
theorem homMap_id (hc : ModulePushforwardCoherence B S hS) (T : s.SchemesOver)
    (α : s.homAt T) : s.homMap (𝟙 T) α = α := by
  exact Functor.conjHom_id _ _ (s.baseChangeComparison_id hc T) α

/-- The comparison for a composite of morphisms of test schemes, in terms of the comparisons
for the two factors and the comparison of Stacks 03LU for the two base-change maps. -/
theorem baseChangeComparison_comp (hc : ModulePushforwardCoherence B S hS)
    {V U T : s.SchemesOver} (g : V ⟶ U) (h : U ⟶ T) :
    s.baseChangeComparison (g ≫ h) =
      (s.baseChangeComparison g ≪≫
          Functor.isoWhiskerRight (s.baseChangeComparison h)
            (modulePullback B S hS (baseChangeMap s.f g)) ≪≫
          Functor.associator (modulePullback B S hS (s.projection T))
            (modulePullback B S hS (baseChangeMap s.f h))
            (modulePullback B S hS (baseChangeMap s.f g))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (s.projection T))
          (modulePullbackTriangle B S hS (baseChangeMap_comp s.f g h).symm)).symm := by
  have key := hc.modulePullbackTriangle_comp (baseChangeMap_comp s.f g h).symm
    (baseChangeMap_comp_projection s.f h) (baseChangeMap_comp_projection s.f g)
    (baseChangeMap_comp_projection s.f (g ≫ h))
  calc s.baseChangeComparison (g ≫ h)
      = (s.baseChangeComparison (g ≫ h) ≪≫
            Functor.isoWhiskerLeft (modulePullback B S hS (s.projection T))
              (modulePullbackTriangle B S hS (baseChangeMap_comp s.f g h).symm)) ≪≫
          (Functor.isoWhiskerLeft (modulePullback B S hS (s.projection T))
            (modulePullbackTriangle B S hS (baseChangeMap_comp s.f g h).symm)).symm := by
        simp
    _ = _ := by rw [baseChangeComparison, baseChangeComparison, baseChangeComparison, key]

/-- **Pullback of homomorphisms is compatible with composition of morphisms of test
schemes.** -/
theorem homMap_comp (hc : ModulePushforwardCoherence B S hS) {V U T : s.SchemesOver}
    (g : V ⟶ U) (h : U ⟶ T) (α : s.homAt T) :
    s.homMap (g ≫ h) α = s.homMap g (s.homMap h α) :=
  Functor.conjHom_comp (s.baseChangeComparison h) (s.baseChangeComparison g)
    (s.baseChangeComparison (g ≫ h))
    (modulePullbackTriangle B S hS (baseChangeMap_comp s.f g h).symm)
    (s.baseChangeComparison_comp hc g h) α

/-- **Stacks 08JT.**  The relative Hom functor `Hom(F, G) : (Sch/base)ᵒᵖ ⥤ Sets`, whose value
at a test scheme `T` over the base is `Hom_{𝒪_{X_T}}(F_T, G_T)` and whose action on a morphism
of test schemes is pullback of homomorphisms.

The hypothesis is the pseudofunctoriality of the direct images of Stacks 03LU; the two
functor laws are exactly its associativity coherence and its unit law. -/
@[stacks 08JT "the Hom functor, conditional on the pseudofunctoriality of the direct images \
of Stacks 03LU"]
def homFunctor (hc : ModulePushforwardCoherence B S hS) :
    (s.SchemesOver)ᵒᵖ ⥤ Type (u + 1) :=
  (baseChangeOver s.f).op ⋙ moduleHomOver hc s.F s.G

/-- **Stacks 08JT.**  The value of the relative Hom functor at a test scheme over the base is
the set of `𝒪_{X_T}`-module homomorphisms `F_T ⟶ G_T`. -/
@[stacks 08JT "the value of the functor, conditional on the pseudofunctoriality of the \
direct images of Stacks 03LU"]
theorem homFunctor_obj (hc : ModulePushforwardCoherence B S hS) (T : s.SchemesOver) :
    (s.homFunctor hc).obj (Opposite.op T) = s.homAt T :=
  rfl

/-- **Stacks 08JT.**  The action of the relative Hom functor on a morphism of test schemes is
pullback of homomorphisms. -/
@[stacks 08JT "the action of the functor, conditional on the pseudofunctoriality of the \
direct images of Stacks 03LU"]
theorem homFunctor_map (hc : ModulePushforwardCoherence B S hS) {U T : s.SchemesOver}
    (g : U ⟶ T) :
    (s.homFunctor hc).map (Opposite.op g) = TypeCat.ofHom (s.homMap g) := by
  rw [s.homMap_def g, s.baseChangeComparison_eq g]
  rfl



/-! ### Base change of the base algebraic space, Stacks 08JW -/

section BaseChangeOfBase

variable {base' : AlgebraicSpaces B S hS} (p : base' ⟶ s.base)

/-- The source of the base-changed situation of Stacks 08JW: `X' = X ×_base base'`. -/
abbrev baseChangedSource : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS s.f p

/-- The projection `X' ⟶ X`, along which the two modules are pulled back. -/
def baseChangedSourceProjection : s.baseChangedSource p ⟶ s.X :=
  ObjectProperty.homMk (pullback.fst s.f.hom p.hom)

/-- The structure morphism `f' : X' ⟶ base'` of the base-changed situation. -/
def baseChangedMorphism : s.baseChangedSource p ⟶ base' :=
  ObjectProperty.homMk (pullback.snd s.f.hom p.hom)

/-- The pullback of the source module along the projection `X' ⟶ X` is quasi-coherent, because
`F` is.  This is Stacks 03GA at that projection. -/
theorem isQuasicoherentOnSite_baseChangedF :
    ((modulePullback B S hS (s.baseChangedSourceProjection p)).obj s.F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (s.baseChangedSourceProjection p) s.F s.quasicoherent_F

/-- The pullback of the target module along the projection `X' ⟶ X` is quasi-coherent, because
`G` is.  This is Stacks 03GA at that projection. -/
theorem isQuasicoherentOnSite_baseChangedG :
    ((modulePullback B S hS (s.baseChangedSourceProjection p)).obj s.G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (s.baseChangedSourceProjection p) s.G s.quasicoherent_G

/-- **Stacks 08JW.**  The relative Hom situation obtained by changing the base algebraic space
along `p : base' ⟶ base`: its source is `X' = X ×_base base'`, its morphism the second
projection, and its two modules the pullbacks of `F` and `G` along the first projection. -/
@[stacks 08JW "the base-changed situation"]
def baseChangedSituation : HomSituation B S hS where
  X := s.baseChangedSource p
  base := base'
  f := s.baseChangedMorphism p
  F := (modulePullback B S hS (s.baseChangedSourceProjection p)).obj s.F
  G := (modulePullback B S hS (s.baseChangedSourceProjection p)).obj s.G
  quasicoherent_F := s.isQuasicoherentOnSite_baseChangedF p
  quasicoherent_G := s.isQuasicoherentOnSite_baseChangedG p

/-- The pasted-pullback identification `X'_T ≅ X_T` of the base change of `X'` along a test
scheme over `base'` with the base change of `X` along the same scheme, read over `base`. -/
def baseChangeFiberIso
    (T : CostructuredArrow (schemeSpaceFunctor B S hS) base') :
    baseChangeSpace (s.baseChangedMorphism p) T ≅
      s.baseChange ((CostructuredArrow.map p).obj T) :=
  ObjectProperty.isoMk _ (pullbackLeftPullbackSndIso s.f.hom p.hom T.hom.hom)

/-- The identification `X'_T ≅ X_T` commutes with the projections `X_T ⟶ X` to the space carrying
the two modules, `AlgebraicGeometry.Space.baseChangeProjection`: it is a morphism over `X`.

Note that in this file `projection` names the map to `X`, following
`AlgebraicGeometry.Space.HomSituation.projection`, whereas in
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorBaseChange.lean` it names the map to the test
scheme, following `AlgebraicGeometry.Space.QuotientSituation.projection`; the two modules carry
a same-named lemma about different maps. -/
@[reassoc (attr := simp)]
theorem baseChangeFiberIso_hom_comp_projection
    (T : CostructuredArrow (schemeSpaceFunctor B S hS) base') :
    (s.baseChangeFiberIso p T).hom ≫
        baseChangeProjection s.f ((CostructuredArrow.map p).obj T) =
      baseChangeProjection (s.baseChangedMorphism p) T ≫ s.baseChangedSourceProjection p := by
  refine ObjectProperty.hom_ext _ ?_
  exact pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- The identification `X'_T ≅ X_T` commutes with the projections `X_T ⟶ T` to the test scheme,
`AlgebraicGeometry.Space.baseChangeInclusion`. -/
@[reassoc (attr := simp)]
theorem baseChangeFiberIso_hom_comp_inclusion
    (T : CostructuredArrow (schemeSpaceFunctor B S hS) base') :
    (s.baseChangeFiberIso p T).hom ≫
        baseChangeInclusion s.f ((CostructuredArrow.map p).obj T) =
      baseChangeInclusion (s.baseChangedMorphism p) T := by
  refine ObjectProperty.hom_ext _ ?_
  exact pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- The identification `X'_T ≅ X_T` is natural in the test scheme. -/
theorem baseChangeFiberIso_naturality
    {U T : CostructuredArrow (schemeSpaceFunctor B S hS) base'} (g : U ⟶ T) :
    baseChangeMap (s.baseChangedMorphism p) g ≫ (s.baseChangeFiberIso p T).hom =
      (s.baseChangeFiberIso p U).hom ≫
        baseChangeMap s.f ((CostructuredArrow.map p).map g) := by
  refine baseChange_hom_ext s.f ?_ ?_ <;> simp

/-- The base change of `X'` along the test schemes over `base'`, read over `X` through the
projection `X' ⟶ X`, is the base change of `X` along the same test schemes, read over
`base`. -/
def baseChangeOverIso :
    baseChangeOver (s.baseChangedMorphism p) ⋙
        Over.map (s.baseChangedSourceProjection p) ≅
      CostructuredArrow.map p ⋙ baseChangeOver s.f :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk (s.baseChangeFiberIso p T)
      (s.baseChangeFiberIso_hom_comp_projection p T))
    (fun g ↦ Over.OverMorphism.ext (s.baseChangeFiberIso_naturality p g))

/-- **Stacks 08JW.**  For a test scheme `T` over `base'` the two relative Hom sets agree:
`Hom(F', G')(T) = Hom(F, G)(T)`, where on the right `T` is read as a scheme over `base`
through `T ⟶ base' ⟶ base`.  The identification is natural in `T`, so it is an isomorphism of
the two relative Hom functors.

It has no hypotheses.  The coherence data for the direct images, which the Hom functor of
either situation is formed from, is `AlgebraicGeometry.Space.modulePushforwardCoherence`, and
the quasi-coherence of the two pullbacks, which forming the base-changed situation needs, is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`. -/
@[stacks 08JW "the identification Hom(F',G')(T) = Hom(F,G)(T), natural in T"]
def homFunctorBaseChange :
    (s.baseChangedSituation p).homFunctor (modulePushforwardCoherence B S hS) ≅
      (CostructuredArrow.map p).op ⋙ s.homFunctor (modulePushforwardCoherence B S hS) :=
  Functor.isoWhiskerLeft (baseChangeOver (s.baseChangedMorphism p)).op
      (moduleHomOverPullback (modulePushforwardCoherence B S hS)
        (s.baseChangedSourceProjection p) s.F s.G) ≪≫
    Functor.isoWhiskerRight (NatIso.op (s.baseChangeOverIso p)).symm
      (moduleHomOver (modulePushforwardCoherence B S hS) s.F s.G)

end BaseChangeOfBase

end HomSituation

end AlgebraicGeometry.Space

end
