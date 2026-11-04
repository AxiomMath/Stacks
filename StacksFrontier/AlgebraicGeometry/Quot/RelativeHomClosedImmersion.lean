module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The relative Hom functor and a closed immersion

Let `i : X' ⟶ X` be a closed immersion of algebraic spaces over an algebraic space `Y` over a
scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module and let `G'` be a quasi-coherent
`𝒪_{X'}`-module.  Stacks 08K5 asserts

`Hom(F, i_*G') = Hom(i^*F, G')`

**as functors on `(Sch/Y)`**, the two sides being the relative Hom functors of Stacks 08JT:
the first of the situation `(X ⟶ Y, F, i_*G')`, the second of the situation
`(X' ⟶ Y, i^*F, G')`.  This file proves that identification, as an isomorphism of those two
functors on the test schemes over `Y`, so that the compatibility with every change of test
scheme is part of the conclusion rather than an afterthought.

## The shape of the proof

Everything rests on one observation, which is what makes the naturality in the test scheme
free.  Write `X_T = X ×_Y T` and `X'_T = X' ×_Y T` for the two base changes along a test scheme
`T` over `Y`, with projections `π_T : X_T ⟶ X` and `π'_T : X'_T ⟶ X'`.  The closed immersion
induces `j_T : X'_T ⟶ X_T` with `j_T ≫ π_T = π'_T ≫ i`, so `X'_T` is an algebraic space *over
`X`* through either route, and `j_T` is a morphism over `X`.  Consequently

* the value of the second Hom functor at `T` is, unconditionally,
  `Hom_{𝒪_{X'_T}}((π'_T ≫ i)^*F, (π'_T ≫ i)^*(i_*G'))` — this is
  `AlgebraicGeometry.Space.moduleHomOverClosedImmersion`, the relative Hom functor over the
  algebraic spaces over `X'` compared with the one over the algebraic spaces over `X`
  restricted along `Over.map i`, which uses the counit isomorphism `i^*i_* ≅ 𝟭` of
  Stacks 04CJ, part (2);
* and the comparison map is then nothing but
  `AlgebraicGeometry.Space.moduleHomOver hc F (i_*G')` evaluated at the morphism `j_T` of
  `Over X`, assembled over all `T` by whiskering with the natural transformation
  `AlgebraicGeometry.Space.baseChangeSourceOver`.  Naturality in `T` is therefore the
  functoriality of `moduleHomOver` and needs no argument of its own.

What is left is that each component is bijective, and *that* is the whole mathematical content
of the lemma: pulling a homomorphism back along `j_T` is a bijection
`Hom_{𝒪_{X_T}}(F_T, (i_*G')_T) ≃ Hom_{𝒪_{X'_T}}(j_T^*F_T, j_T^*(i_*G')_T)`.  Via the adjunction
of Stacks 03LU this is the assertion that the unit `(i_*G')_T ⟶ (j_T)_*j_T^*(i_*G')_T` is an
isomorphism, which holds as soon as `(i_*G')_T` is a direct image along `j_T` — because `j_T` is
again a closed immersion, so `(j_T)_*` is fully faithful by Stacks 04CJ, part (2).  That
`(i_*G')_T` *is* a direct image along `j_T` is exactly the base-change clause of Stacks 07U8 for
the affine morphism `i`, and it is the one thing this development does not have; see below.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeSourceMap`: the morphism `X'_T ⟶ X_T` of base changes
  induced by a morphism `i : X' ⟶ X` of algebraic spaces over `Y`, and
  `AlgebraicGeometry.Space.baseChangeSourceOver` the same as a natural transformation
  `baseChangeOver (i ≫ p) ⋙ Over.map i ⟶ baseChangeOver p` of functors to `Over X`.
* `AlgebraicGeometry.Space.moduleHomOverCongrTarget`: an isomorphism of the target module
  induces an isomorphism of relative Hom functors over the algebraic spaces over `X`.
* `AlgebraicGeometry.Space.moduleHomOverClosedImmersion`: the relative Hom functor of `i^*F`
  and `G'` over the algebraic spaces over `X'` is the relative Hom functor of `F` and `i_*G'`
  over the algebraic spaces over `X`, restricted along `Over.map i`.
* `AlgebraicGeometry.Space.TestSchemePushforwardBaseChange`: **the base-change clause of
  Stacks 07U8 for `i`**, in the form consumed here; the one missing input.
* `AlgebraicGeometry.Space.pushforwardHomSituation` and
  `AlgebraicGeometry.Space.pullbackHomSituation`: the two relative Hom situations of
  Stacks 08JT whose functors Stacks 08K5 compares.

## Main results

* `AlgebraicGeometry.Space.isPullback_baseChangeSourceMap`: the square formed by `X'_T ⟶ X_T`
  and the two projections to `X'` and `X` is cartesian, so `X'_T ⟶ X_T` inherits every
  base-change-stable property of `i`.
* `AlgebraicGeometry.Space.homFunctorClosedImmersionIso`: the isomorphism of the two relative
  Hom functors, at the level of the whiskered composites that
  `AlgebraicGeometry.Space.HomSituation.homFunctor` is built from.
* `AlgebraicGeometry.Space.homFunctorClosedImmersion`: **Stacks 08K5**, the identification
  `Hom(F, i_*G') = Hom(i^*F, G')` as an isomorphism of the two relative Hom functors of
  Stacks 08JT on the test schemes over `Y`.

## Missing prerequisites, carried as hypotheses

Three inputs are not available in this development and are carried explicitly.  None of them is
a weakening of the source statement; each is a result the source quotes and this development
does not have, and the tag attribute names all three.

1. **The pseudofunctoriality of the direct images of Stacks 03LU**,
   `AlgebraicGeometry.Space.ModulePushforwardCoherence`.  The relative Hom *functor* of
   Stacks 08JT does not exist without it — see the implementation notes of
   `StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean` — so every statement here that
   mentions `AlgebraicGeometry.Space.HomSituation.homFunctor` inherits it.
2. **Quasi-coherence of `i_*G'` (Stacks 07U8, resp. Stacks 03M9) and of `i^*F`
   (Stacks 03GA).**  These are fields of `AlgebraicGeometry.Space.HomSituation`, so they are
   needed to *form* the two situations the source compares, exactly as in
   `AlgebraicGeometry.Space.HomSituation.baseChangedSituation` of Stacks 08JW.  Quasi-coherence
   of the direct image along the affine morphism `i` is available only granted
   `AlgebraicGeometry.Space.SchemeTargetAffinePushforwardQuasicoherent`
   (`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageQuasicoherent.lean`), and
   quasi-coherence of the pullback only granted
   `AlgebraicGeometry.Space.HasLocalInverseImagePresentations`
   (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackQuasicoherence.lean`); both
   are taken here as the two bare quasi-coherence hypotheses, which is weaker than taking
   either of those two.
3. **The base-change clause of Stacks 07U8**, that the formation of the direct image along an
   affine morphism commutes with arbitrary base change.  The file proving the first clause of
   Stacks 07U8, `StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageQuasicoherent.lean`,
   records in its implementation notes that this clause is not treated, and no base-change
   comparison for `AlgebraicGeometry.Space.modulePushforward` exists in this development beyond
   the étale one of Stacks 03LX
   (`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardEtaleBaseChange.lean`), which does
   not apply to a test scheme.  It is carried as
   `AlgebraicGeometry.Space.TestSchemePushforwardBaseChange`, stated for exactly the squares
   this file meets, and as `Nonempty` of an isomorphism because only its existence is used, and
   only to prove a proposition.

## Implementation notes

The declarations in the root `CategoryTheory` namespace are general facts about adjunctions and
about `CategoryTheory.Functor.conjHom`; they are here rather than with those notions in order
to leave `StacksFrontier/CategoryTheory/Functor/ConjugateHom.lean` untouched.

`AlgebraicGeometry.Space.moduleHomOverCongrTarget` is built from an isomorphism of Hom sets at
each algebraic space over `X` whose naturality is the naturality of the comparison of inverse
images *in the module*, which is a field of that natural transformation; no coherence of
Stacks 03LU is consumed by it, unlike
`AlgebraicGeometry.Space.moduleHomOverPullback`.

**Nothing below ever asks the elaborator to compare two Hom sets of
`AlgebraicGeometry.Space.Modules` that are equal only after unfolding.**  Such a comparison
does not terminate: `AlgebraicGeometry.Space.Modules` is a sheaf of modules on the small étale
site, and the unifier, failing to match the two Hom sets syntactically, unfolds
`Quiver.Hom` and compares the underlying sheaves structurally.  Even the identification of
`(Over.mk z).hom` with `z`, or of a component of
`AlgebraicGeometry.Space.baseChangeSourceOver` with
`AlgebraicGeometry.Space.baseChangeSourceMap`, is enough to trigger it when it stands inside
such a Hom set.  The two consequences for the proofs here are that
`AlgebraicGeometry.Space.isIso_moduleHomOver_map` states its hypothesis in the exact vocabulary
`AlgebraicGeometry.Space.moduleHomOver` uses — `(Opposite.unop Z).hom` and `m.unop.left`, not
the morphisms they reduce to — and that
`AlgebraicGeometry.Space.isIso_moduleHomOver_map_baseChangeSourceOver` reaches its hypothesis
with `apply`, which fixes the two Hom sets from the goal before the base-change isomorphism is
supplied.  Supplying that isomorphism first fixes them from *its* type instead, and the two
readings then have to be compared.

The module universe is the universe `u` of the structure rings throughout, as it is for
`AlgebraicGeometry.Space.modulePullback`.

## References

* [Stacks Project, Tag 08K5](https://stacks.math.columbia.edu/tag/08K5)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-! ### Two general facts -/

/-- **Applying a left adjoint to the homomorphisms into a fixed object is a bijection as soon as
the unit is an isomorphism there.**  For an adjunction `L ⊣ R` and objects `A`, `B` of the
source, if the unit `B ⟶ R(L B)` is an isomorphism then `α ↦ L α` is a bijection
`(A ⟶ B) ≃ (L A ⟶ L B)`.

Under the adjunction, `L α` corresponds to `α` followed by the unit at `B`. -/
theorem Adjunction.bijective_map_of_isIso_unit {C : Type*} {D : Type*} [Category* C]
    [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C) {Bb : C}
    (h : IsIso (adj.unit.app Bb)) :
    Function.Bijective (fun α : A ⟶ Bb ↦ L.map α) := by
  have := h
  have key : ∀ α : A ⟶ Bb,
      (adj.homEquiv A (L.obj Bb)).symm (α ≫ adj.unit.app Bb) = L.map α := by
    intro α
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      adj.left_triangle_components, Category.comp_id]
  have hb : Function.Bijective (fun α : A ⟶ Bb ↦ α ≫ adj.unit.app Bb) := by
    refine ⟨fun α β hab ↦ (cancel_mono (adj.unit.app Bb)).1 hab, fun β ↦ ?_⟩
    exact ⟨β ≫ inv (adj.unit.app Bb), by simp⟩
  convert (adj.homEquiv A (L.obj Bb)).symm.bijective.comp hb using 1
  exact funext fun α ↦ (key α).symm

/-- **Conjugation by a comparison is a bijection exactly when applying the further functor
is.**  For a comparison `e : P₂ ≅ P₁ ⋙ L`, conjugation by `e` is the image under `L` read
through two isomorphisms, so it is a bijection as soon as `L` is bijective on the Hom set. -/
theorem Functor.bijective_conjHom {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C]
    [Category* D₁] [Category* D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (h : Function.Bijective (fun α : P₁.obj M ⟶ P₁.obj N ↦ L.map α)) :
    Function.Bijective (Functor.conjHom e (M := M) (N := N)) := by
  let φ : (L.obj (P₁.obj M) ⟶ L.obj (P₁.obj N)) ≃ (P₂.obj M ⟶ P₂.obj N) :=
    { toFun := fun β ↦ e.hom.app M ≫ β ≫ e.inv.app N
      invFun := fun γ ↦ e.inv.app M ≫ γ ≫ e.hom.app N
      left_inv := fun β ↦ by simp
      right_inv := fun γ ↦ by simp }
  exact φ.bijective.comp h

/-- Postcomposing with the image of an isomorphism and then with the image of its inverse
changes nothing. -/
theorem Functor.comp_map_hom_map_inv {C : Type*} {D : Type*} [Category* C] [Category* D]
    (P : C ⥤ D) {G G₂ : C} (b : G ≅ G₂) {A : D} (α : A ⟶ P.obj G) :
    (α ≫ P.map b.hom) ≫ P.map b.inv = α := by
  simp

/-- Postcomposing with the image of the inverse of an isomorphism and then with the image of
the isomorphism changes nothing. -/
theorem Functor.comp_map_inv_map_hom {C : Type*} {D : Type*} [Category* C] [Category* D]
    (P : C ⥤ D) {G G₂ : C} (b : G ≅ G₂) {A : D} (α : A ⟶ P.obj G₂) :
    (α ≫ P.map b.inv) ≫ P.map b.hom = α := by
  simp

/-- **Conjugation commutes with postcomposition.**  Conjugating by a comparison
`e : P₂ ≅ P₁ ⋙ L` a morphism postcomposed with the image under `P₁` of a morphism of the index
category is the conjugate postcomposed with the image under `P₂` of the same morphism.

This is the naturality of `e` in the index object, which is a field of the natural
transformation. -/
theorem Functor.conjHom_comp_map {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C]
    [Category* D₁] [Category* D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    (e : P₂ ≅ P₁ ⋙ L) {M N N' : C} (b : N ⟶ N') (α : P₁.obj M ⟶ P₁.obj N) :
    Functor.conjHom e (α ≫ P₁.map b) = Functor.conjHom e α ≫ P₂.map b := by
  simp only [conjHom, Functor.map_comp, Category.assoc]
  rw [← Functor.comp_map, e.inv.naturality b]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS}

/-! ### Base change of the test-scheme fibre along a morphism of the source -/

/-- The morphism `X'_T ⟶ X_T` of base changes along a test scheme `T` over `Y` induced by a
morphism `i : X' ⟶ X` over `Y`: the morphism whose projection to `X` is `π'_T ≫ i` and whose
projection to `T` is the projection of `X'_T`. -/
def baseChangeSourceMap (p : X ⟶ Y) (i : X' ⟶ X) (T : SchemesOver Y) :
    baseChangeSpace (i ≫ p) T ⟶ baseChangeSpace p T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS p T.hom).lift
    (baseChangeProjection (i ≫ p) T ≫ i) (baseChangeInclusion (i ≫ p) T)
    (by
      rw [Category.assoc]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS (i ≫ p) T.hom).w)

/-- The morphism `X'_T ⟶ X_T` is a morphism over `X`. -/
@[reassoc (attr := simp)]
theorem baseChangeSourceMap_comp_projection (p : X ⟶ Y) (i : X' ⟶ X) (T : SchemesOver Y) :
    baseChangeSourceMap p i T ≫ baseChangeProjection p T =
      baseChangeProjection (i ≫ p) T ≫ i :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS p T.hom).lift_fst _ _ _

/-- The morphism `X'_T ⟶ X_T` commutes with the projections to the test scheme. -/
@[reassoc (attr := simp)]
theorem baseChangeSourceMap_comp_inclusion (p : X ⟶ Y) (i : X' ⟶ X) (T : SchemesOver Y) :
    baseChangeSourceMap p i T ≫ baseChangeInclusion p T = baseChangeInclusion (i ≫ p) T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS p T.hom).lift_snd _ _ _

/-- The morphisms `X'_T ⟶ X_T` are natural in the test scheme. -/
theorem baseChangeSourceMap_naturality (p : X ⟶ Y) (i : X' ⟶ X) {U T : SchemesOver Y}
    (g : U ⟶ T) :
    baseChangeMap (i ≫ p) g ≫ baseChangeSourceMap p i T =
      baseChangeSourceMap p i U ≫ baseChangeMap p g := by
  refine baseChange_hom_ext p ?_ ?_ <;> simp

/-- **The square of `i : X' ⟶ X` and a test scheme is cartesian.**  The morphism `X'_T ⟶ X_T`
together with the two projections to `X'` and `X` is a cartesian square over `i`, so `X'_T ⟶ X_T`
is a base change of `i`.

Cartesian squares cancel on the right (`IsPullback.of_right`): the outer square, whose
composites are the projection `X'_T ⟶ T` and the structure morphism `i ≫ p` of `X'`, is
cartesian, as is the square defining `X_T` on its right, hence so is the square on the left. -/
theorem isPullback_baseChangeSourceMap (p : X ⟶ Y) (i : X' ⟶ X) (T : SchemesOver Y) :
    IsPullback (baseChangeSourceMap p i T) (baseChangeProjection (i ≫ p) T)
      (baseChangeProjection p T) i := by
  have ht : IsPullback (baseChangeInclusion p T) (baseChangeProjection p T) T.hom p :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS p T.hom).flip
  have hu : IsPullback (baseChangeInclusion (i ≫ p) T) (baseChangeProjection (i ≫ p) T)
      T.hom (i ≫ p) :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (i ≫ p) T.hom).flip
  have hs : IsPullback (baseChangeSourceMap p i T ≫ baseChangeInclusion p T)
      (baseChangeProjection (i ≫ p) T) T.hom (i ≫ p) := by
    rw [baseChangeSourceMap_comp_inclusion]
    exact hu
  exact IsPullback.of_right hs (baseChangeSourceMap_comp_projection p i T) ht

/-- A base change of a closed immersion along a test scheme is a closed immersion: the
morphism `X'_T ⟶ X_T` is a closed immersion whenever `i` is. -/
theorem isClosedImmersion_baseChangeSourceMap (p : X ⟶ Y) (i : X' ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (T : SchemesOver Y) :
    IsClosedImmersion B S hS (baseChangeSourceMap p i T).hom :=
  isClosedImmersion_of_isPullback B S hS (isPullback_baseChangeSourceMap p i T).flip hi

/-- The base changes of `X'` along the test schemes over `Y`, read over `X` through `i`,
mapping to the base changes of `X` along the same test schemes: a natural transformation of
functors to the algebraic spaces over `X`.

This is the only thing the comparison of Stacks 08K5 is made of; its naturality is what makes
that comparison natural in the test scheme. -/
def baseChangeSourceOver (p : X ⟶ Y) (i : X' ⟶ X) :
    baseChangeOver (i ≫ p) ⋙ Over.map i ⟶ baseChangeOver p where
  app T := Over.homMk (baseChangeSourceMap p i T) (baseChangeSourceMap_comp_projection p i T)
  naturality _ _ g := Over.OverMorphism.ext (baseChangeSourceMap_naturality p i g)

/-! ### Changing the target module of the relative Hom functor over the algebraic spaces -/

/-- Postcomposition with the inverse image of an isomorphism of the target module, as an
isomorphism of the two Hom sets over an algebraic space over `X`. -/
def moduleHomOverTargetIso (F : Modules.{u, u} B S hS X.1 X.2)
    {G G₂ : Modules.{u, u} B S hS X.1 X.2} (b : G ≅ G₂) (Z : Over X) :
    moduleHomOverObj F G Z ≅ moduleHomOverObj F G₂ Z where
  hom := ↾fun α : (modulePullback B S hS Z.hom).obj F ⟶
      (modulePullback B S hS Z.hom).obj G ↦ α ≫ (modulePullback B S hS Z.hom).map b.hom
  inv := ↾fun α : (modulePullback B S hS Z.hom).obj F ⟶
      (modulePullback B S hS Z.hom).obj G₂ ↦ α ≫ (modulePullback B S hS Z.hom).map b.inv
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun α ↦
    Functor.comp_map_hom_map_inv (modulePullback B S hS Z.hom) b α
  inv_hom_id := ConcreteCategory.hom_ext _ _ fun α ↦
    Functor.comp_map_inv_map_hom (modulePullback B S hS Z.hom) b α

/-- **An isomorphism of the target module induces an isomorphism of relative Hom functors over
the algebraic spaces over `X`.**

Its naturality is the naturality, *in the module*, of the comparison of the inverse image along
a composite with the iterated inverse image, which is a field of that natural transformation;
so, unlike `AlgebraicGeometry.Space.moduleHomOverPullback`, this consumes no coherence of
Stacks 03LU beyond the one the functors themselves carry. -/
def moduleHomOverCongrTarget (hc : ModulePushforwardCoherence B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) {G G₂ : Modules.{u, u} B S hS X.1 X.2} (b : G ≅ G₂) :
    moduleHomOver hc F G ≅ moduleHomOver hc F G₂ :=
  NatIso.ofComponents (fun Z ↦ moduleHomOverTargetIso F b Z.unop)
    (fun {Z Z'} m ↦ ofHom_comp_eq_comp
      (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)))
      (fun α ↦ α ≫ (modulePullback B S hS (Opposite.unop Z').hom).map b.hom)
      (fun α ↦ α ≫ (modulePullback B S hS (Opposite.unop Z).hom).map b.hom)
      (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)))
      fun α ↦ (Functor.conjHom_comp_map
        (modulePullbackTriangle B S hS (Over.w m.unop)) b.hom α).symm)

/-- **The relative Hom functor out of an inverse image is the relative Hom functor into the
direct image, restricted along `Over.map i`.**  For a closed immersion `i : X' ⟶ X`, the functor
sending an algebraic space `z' : Z' ⟶ X'` to `Hom_{𝒪_{Z'}}((z')^*(i^*F), (z')^*G')` is the
functor sending it, read over `X` through `z' ≫ i`, to
`Hom_{𝒪_{Z'}}((z' ≫ i)^*F, (z' ≫ i)^*(i_*G'))`.

It is unconditional apart from the coherence the two functors carry: the target modules are
identified by the counit isomorphism `i^*i_*G' ≅ G'` of Stacks 04CJ, part (2), and the two
sides are then the two sides of `AlgebraicGeometry.Space.moduleHomOverPullback` at `i`. -/
def moduleHomOverClosedImmersion (hc : ModulePushforwardCoherence B S hS) (i : X' ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (G' : Modules.{u, u} B S hS X'.1 X'.2) :
    moduleHomOver hc ((modulePullback B S hS i).obj F) G' ≅
      (Over.map i).op ⋙ moduleHomOver hc F ((modulePushforward B S hS i).obj G') :=
  moduleHomOverCongrTarget hc ((modulePullback B S hS i).obj F)
      ((modulePullbackCounitIso B S hS i hi).app G').symm ≪≫
    moduleHomOverPullback hc i F ((modulePushforward B S hS i).obj G')

/-! ### The comparison of the two relative Hom functors -/

/-- The action of the relative Hom functor over the algebraic spaces over `X` on a morphism,
written out: it is conjugation by the comparison of the inverse images. -/
theorem moduleHomOver_map (hc : ModulePushforwardCoherence B S hS)
    (F G : Modules.{u, u} B S hS X.1 X.2) {Z Z' : (Over X)ᵒᵖ} (m : Z ⟶ Z') :
    (moduleHomOver hc F G).map m =
      ↾Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)) :=
  rfl

/-- **The base-change clause of Stacks 07U8 for `i`, in the form this file consumes.**  For
every test scheme `T` over `Y`, the pullback to `X_T` of the direct image `i_*G'` is a direct
image along the base change `X'_T ⟶ X_T` of `i`, namely of the pullback of `G'` to `X'_T`.

This is the assertion of Stacks 07U8 that the formation of the direct image along an affine
morphism commutes with arbitrary base change, specialised to the squares of
`AlgebraicGeometry.Space.isPullback_baseChangeSourceMap`.  It is the one input of Stacks 08K5
that this development does not have: the file proving the quasi-coherence clause of
Stacks 07U8 records the base-change clause as untreated, and the only base-change comparison
available for `AlgebraicGeometry.Space.modulePushforward` is the étale one of Stacks 03LX,
which does not apply to a test scheme.

It is stated as `Nonempty` of an isomorphism because only the existence of the isomorphism is
used, and only in the proof of a proposition. -/
def TestSchemePushforwardBaseChange (p : X ⟶ Y) (i : X' ⟶ X)
    (G' : Modules.{u, u} B S hS X'.1 X'.2) : Prop :=
  ∀ T : SchemesOver Y,
    Nonempty
      ((modulePullback B S hS (baseChangeProjection p T)).obj
          ((modulePushforward B S hS i).obj G') ≅
        (modulePushforward B S hS (baseChangeSourceMap p i T)).obj
          ((modulePullback B S hS (baseChangeProjection (i ≫ p) T)).obj G'))

/-- The relative Hom functor over the algebraic spaces over `X` carries a morphism to an
isomorphism of Hom sets as soon as the inverse image along that morphism is bijective on the
Hom set in question. -/
theorem isIso_moduleHomOver_map (hc : ModulePushforwardCoherence B S hS)
    (F G : Modules.{u, u} B S hS X.1 X.2) {Z Z' : (Over X)ᵒᵖ} (m : Z ⟶ Z')
    (h : Function.Bijective
      (fun α : (modulePullback B S hS (Opposite.unop Z).hom).obj F ⟶
          (modulePullback B S hS (Opposite.unop Z).hom).obj G ↦
        (modulePullback B S hS m.unop.left).map α)) :
    IsIso ((moduleHomOver hc F G).map m) := by
  rw [moduleHomOver_map]
  exact (bijective_iff_isIso_ofHom _).mp
    (Functor.bijective_conjHom (modulePullbackTriangle B S hS (Over.w m.unop)) h)

/-- **Inverse image along a closed immersion is bijective on the homomorphisms into a direct
image along it.**  For a closed immersion `j : W' ⟶ W` of algebraic spaces and an `𝒪_W`-module
`Bb` isomorphic to a direct image `j_*N`, the map `α ↦ j^*α` is a bijection
`Hom_{𝒪_W}(A, Bb) ≃ Hom_{𝒪_{W'}}(j^*A, j^*Bb)`.

Under the adjunction of Stacks 03LU this is the assertion that the unit `Bb ⟶ j_*j^*Bb` is an
isomorphism, which holds for `Bb = j_*N` because the direct image along a closed immersion is
fully faithful, Stacks 04CJ, part (2). -/
theorem bijective_modulePullback_map_of_isPushforward {W W' : AlgebraicSpaces B S hS}
    (j : W' ⟶ W) (hj : IsClosedImmersion B S hS j.hom)
    (A : Modules.{u, u} B S hS W.1 W.2) {Bb : Modules.{u, u} B S hS W.1 W.2}
    {N : Modules.{u, u} B S hS W'.1 W'.2}
    (e : Bb ≅ (modulePushforward B S hS j).obj N) :
    Function.Bijective (fun α : A ⟶ Bb ↦ (modulePullback B S hS j).map α) := by
  have := (fullyFaithfulModulePushforward B S hS j hj).full
  have := (fullyFaithfulModulePushforward B S hS j hj).faithful
  exact (modulePullbackAdjunction B S hS j).bijective_map_of_isIso_unit A
    (Adjunction.isIso_unit_app_of_iso (modulePullbackAdjunction B S hS j) e)

/-- **Pulling a homomorphism back along `X'_T ⟶ X_T` is a bijection.**  For a closed immersion
`i` and a test scheme `T` over `Y`, the relative Hom functor over the algebraic spaces over `X`
carries the morphism `X'_T ⟶ X_T` of `Over X` to an isomorphism of Hom sets.

This is the whole mathematical content of Stacks 08K5: `(i_*G')_T` is a direct image along
`X'_T ⟶ X_T` by the base-change hypothesis `hbc`, and `X'_T ⟶ X_T` is again a closed
immersion.

The two steps are taken by `apply` rather than as a term, and the morphism `X'_T ⟶ X_T` is
named as the component of `AlgebraicGeometry.Space.baseChangeSourceOver` rather than as
`AlgebraicGeometry.Space.baseChangeSourceMap`, so that the Hom sets of the hypothesis are the
ones of the goal on the nose.  Supplying the base-change isomorphism before the Hom sets are
fixed makes the elaborator compare two Hom sets of `AlgebraicGeometry.Space.Modules` that are
equal only after unfolding, which does not terminate; postponing it to a goal leaves only a
comparison of inverse images, where no Hom set is unfolded. -/
theorem isIso_moduleHomOver_map_baseChangeSourceOver (hc : ModulePushforwardCoherence B S hS)
    (p : X ⟶ Y) (i : X' ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G' : Modules.{u, u} B S hS X'.1 X'.2)
    (hbc : TestSchemePushforwardBaseChange p i G') (T : SchemesOver Y) :
    IsIso ((moduleHomOver hc F ((modulePushforward B S hS i).obj G')).map
      ((baseChangeSourceOver p i).app T).op) := by
  refine isIso_moduleHomOver_map hc F ((modulePushforward B S hS i).obj G') _ ?_
  apply bijective_modulePullback_map_of_isPushforward
    (((baseChangeSourceOver p i).app T).op.unop.left)
    (isClosedImmersion_baseChangeSourceMap p i hi T)
  exact (hbc T).some

/-- The comparison map of Stacks 08K5: the relative Hom functor over the algebraic spaces over
`X` evaluated at the morphisms `X'_T ⟶ X_T`, followed by the identification of
`AlgebraicGeometry.Space.moduleHomOverClosedImmersion`.

Its naturality in the test scheme is the functoriality of
`AlgebraicGeometry.Space.moduleHomOver` together with the naturality of
`AlgebraicGeometry.Space.baseChangeSourceOver`, so nothing is proved here. -/
def homFunctorClosedImmersionMap (hc : ModulePushforwardCoherence B S hS) (p : X ⟶ Y)
    (i : X' ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G' : Modules.{u, u} B S hS X'.1 X'.2) :
    (baseChangeOver p).op ⋙ moduleHomOver hc F ((modulePushforward B S hS i).obj G') ⟶
      (baseChangeOver (i ≫ p)).op ⋙
        moduleHomOver hc ((modulePullback B S hS i).obj F) G' :=
  Functor.whiskerRight (NatTrans.op (baseChangeSourceOver p i))
      (moduleHomOver hc F ((modulePushforward B S hS i).obj G')) ≫
    Functor.whiskerLeft (baseChangeOver (i ≫ p)).op
      (moduleHomOverClosedImmersion hc i hi F G').inv

/-- **Stacks 08K5 at the level of the whiskered composites.**  The comparison map of
`AlgebraicGeometry.Space.homFunctorClosedImmersionMap` is an isomorphism of functors on the
test schemes over `Y`. -/
def homFunctorClosedImmersionIso (hc : ModulePushforwardCoherence B S hS) (p : X ⟶ Y)
    (i : X' ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G' : Modules.{u, u} B S hS X'.1 X'.2)
    (hbc : TestSchemePushforwardBaseChange p i G') :
    (baseChangeOver p).op ⋙ moduleHomOver hc F ((modulePushforward B S hS i).obj G') ≅
      (baseChangeOver (i ≫ p)).op ⋙
        moduleHomOver hc ((modulePullback B S hS i).obj F) G' :=
  have h : ∀ T, IsIso ((homFunctorClosedImmersionMap hc p i hi F G').app T) := fun T ↦ by
    have := isIso_moduleHomOver_map_baseChangeSourceOver hc p i hi F G' hbc T.unop
    rw [homFunctorClosedImmersionMap, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.op_app]
    infer_instance
  have : IsIso (homFunctorClosedImmersionMap hc p i hi F G') :=
    NatIso.isIso_of_isIso_app _
  asIso (homFunctorClosedImmersionMap hc p i hi F G')

/-! ### The two relative Hom situations of Stacks 08K5 -/

/-- The relative Hom situation of Stacks 08JT on the left of Stacks 08K5: the morphism
`p : X ⟶ Y`, the module `F` and the direct image `i_*G'`.

Quasi-coherence of `i_*G'` is a field of `AlgebraicGeometry.Space.HomSituation` and is taken as
a hypothesis: it is Stacks 03M9 for the closed immersion `i`, equivalently the quasi-coherence
clause of Stacks 07U8 for the affine morphism `i`, which this development has only granted
`AlgebraicGeometry.Space.SchemeTargetAffinePushforwardQuasicoherent`. -/
def pushforwardHomSituation (p : X ⟶ Y) (i : X' ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2)
    (G' : Modules.{u, u} B S hS X'.1 X'.2) (hF : F.IsQuasicoherentOnSite)
    (hiG : ((modulePushforward B S hS i).obj G').IsQuasicoherentOnSite) :
    HomSituation B S hS where
  X := X
  base := Y
  f := p
  F := F
  G := (modulePushforward B S hS i).obj G'
  quasicoherent_F := hF
  quasicoherent_G := hiG

/-- The relative Hom situation of Stacks 08JT on the right of Stacks 08K5: the morphism
`i ≫ p : X' ⟶ Y`, the inverse image `i^*F` and the module `G'`.

Quasi-coherence of `i^*F` is a field of `AlgebraicGeometry.Space.HomSituation` and is taken as a
hypothesis: it is Stacks 03GA, which this development has only granted
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations`. -/
def pullbackHomSituation (p : X ⟶ Y) (i : X' ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2)
    (G' : Modules.{u, u} B S hS X'.1 X'.2)
    (hiF : ((modulePullback B S hS i).obj F).IsQuasicoherentOnSite)
    (hG' : G'.IsQuasicoherentOnSite) :
    HomSituation B S hS where
  X := X'
  base := Y
  f := i ≫ p
  F := (modulePullback B S hS i).obj F
  G := G'
  quasicoherent_F := hiF
  quasicoherent_G := hG'

/-- **Stacks 08K5.**  Let `i : X' ⟶ X` be a closed immersion of algebraic spaces over an
algebraic space `Y` over `S`, let `F` be a quasi-coherent `𝒪_X`-module and let `G'` be a
quasi-coherent `𝒪_{X'}`-module.  Then

`Hom(F, i_*G') = Hom(i^*F, G')`

as functors on the test schemes over `Y`: the relative Hom functor of Stacks 08JT of the
situation `(X ⟶ Y, F, i_*G')` is isomorphic to the one of the situation `(X' ⟶ Y, i^*F, G')`.
Being an isomorphism of functors, the identification includes the compatibility with every
change of test scheme.

The comparison is pullback of homomorphisms along the base changes `X'_T ⟶ X_T` of `i`, read
through the counit isomorphism `i^*i_* ≅ 𝟭` of Stacks 04CJ, part (2).

It is conditional on three inputs this development does not have, all of them results the
source quotes: the pseudofunctoriality `hc` of the direct images of Stacks 03LU, without which
the relative Hom functor of Stacks 08JT does not exist at all; the quasi-coherence `hiG` of
`i_*G'` (Stacks 03M9, resp. the quasi-coherence clause of Stacks 07U8) and `hiF` of `i^*F`
(Stacks 03GA), which are fields of `AlgebraicGeometry.Space.HomSituation` and so are needed to
form the two situations being compared; and the base-change clause `hbc` of Stacks 07U8, which
is the one input with mathematical content here. -/
@[stacks 08K5 "the identification Hom(F, i_*G') = Hom(i^*F, G') as functors on (Sch/B), \
conditional on the pseudofunctoriality of the direct images of Stacks 03LU, on the \
quasi-coherence of i_*G' (Stacks 03M9) and of i^*F (Stacks 03GA), and on the base-change \
clause of Stacks 07U8 for i"]
def homFunctorClosedImmersion (hc : ModulePushforwardCoherence B S hS) (p : X ⟶ Y)
    (i : X' ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G' : Modules.{u, u} B S hS X'.1 X'.2)
    (hF : F.IsQuasicoherentOnSite)
    (hiG : ((modulePushforward B S hS i).obj G').IsQuasicoherentOnSite)
    (hiF : ((modulePullback B S hS i).obj F).IsQuasicoherentOnSite)
    (hG' : G'.IsQuasicoherentOnSite)
    (hbc : TestSchemePushforwardBaseChange p i G') :
    (pushforwardHomSituation p i F G' hF hiG).homFunctor hc ≅
      (pullbackHomSituation p i F G' hiF hG').homFunctor hc :=
  homFunctorClosedImmersionIso hc p i hi F G' hbc

end AlgebraicGeometry.Space

end
