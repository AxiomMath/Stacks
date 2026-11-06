module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FiniteArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.SeparatedClosed
public import StacksFrontier.Deformation.Groupoid.Loops

/-!
# The target morphism of the finite part of a groupoid

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` and let `T` be an
algebraic space. A pair of Stacks 04PC for `s` over `T` is a morphism `u : T ⟶ U` together with
an open subspace `Z` of `T ×_{u, U, s} R` which is finite over `T`; in the reading of Stacks
04RT it is a `T`-valued family of finite collections of arrows all of whose sources are `u`.
Given moreover an arrow `z : T ⟶ R` with `s ∘ z = u`, the rule

`c(-, i ∘ z) : T ×_{u, U, s} R ⟶ T ×_{t ∘ z, U, s} R`

is an isomorphism, with inverse `c(-, z)`, and the image of `Z` under it is again a pair of
Stacks 04PC for `s` over `T`, now with base morphism `t ∘ z`. This is the translation
`c(Z, i ∘ z)` out of which the target morphism `t'` of the finite part of the groupoid is
built: Stacks 04RT gives the rule `t' : (u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z))`, and that morphism
`t' : Z_univ ⟶ U'` is constructed here, by translating the tautological pair over `Z_univ`
itself by the tautological arrow and reading the result as a point of `U'`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseHom`: the inverse `i : R ⟶ R` of a
  groupoid in algebraic spaces, as a morphism of algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.composeHom`: the composite `β ∘ α` of two
  families of arrows parametrized by a presheaf, when the source of `β` is the target of `α`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translateAmbientIso`: the isomorphism
  `c(-, i ∘ z)` of ambient fibre products.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePair`: the translation
  `(u, Z) ↦ (t ∘ z, c(Z, i ∘ z))` of a pair of Stacks 04PC by an arrow `z` of the groupoid.
* `AlgebraicGeometry.Space.ContainsArrow`: the condition `z ∈ Z` on a pair of Stacks 04PC and
  an arrow `z` over the same base, as a factorization of the section `(1_T, z)` through the
  open subspace.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.targetPair`: the pair
  `(t ∘ z, c(Z, i ∘ z))` over `Z_univ`, the value of the target rule at the tautological point.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.targetHom`: the target morphism
  `t' : Z_univ ⟶ U'` of the finite part of a groupoid whose source morphism is separated and
  locally of finite type.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePair_toBase`: the translated pair has
  base morphism `t ∘ z`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePair_containsUnit`: the translated pair
  contains the base change of the unit, as soon as `z` lies in the pair it translates. This is
  the clause of Stacks 04RT which needs `z ∈ Z`: pointwise it is the computation
  `z ∘ z⁻¹ = e(t(z))`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePair_isClosedSubspace`: the open
  subspace of the translated pair is also closed, when `s` is separated.
* `AlgebraicGeometry.Space.containsArrow_of_pointwise` and
  `AlgebraicGeometry.Space.containsSection_of_isPullback`: the two transfer results for the
  membership conditions, from and to a base change of a pair of Stacks 04PC.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.containsArrow_sourcePair`: clause (3)
  of Stacks 04RT, that the tautological arrow over `Z_univ` lies in the tautological pair.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.targetHom_comp_toBase`: the target morphism of
  the finite part lies over the target morphism of the groupoid.

## Implementation notes

The open subspace of the translated pair is the preimage of the given one under the inverse of
`c(-, i ∘ z)`, so openness and finiteness of its projection are not re-proved by hand but
transported along the ambient isomorphism by
`AlgebraicGeometry.Space.FiniteOpenSubspace.ofAmbientIso`; closedness is then Stacks 04PH for
the translated pair. Containment of the unit is the only clause with mathematical content, and
it is the pointwise identity `c(z, i(z)) = e(t(z))` of the groupoid.

The ambient isomorphism is assembled from `composeHom`, which turns two families of arrows
over a presheaf into their composite family. Its components are the composition map of the
groupoid, so nothing is chosen; the two families in question are the second projection of the
ambient fibre product and the inverse of `z` read along the first projection. The inverse
`inverseHom` is likewise a definition whose components are the inverse arrows of the evaluated
groupoids, in the same situation as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityHom`: a groupoid in algebraic spaces does
not carry the unit and the inverse as fields, since they are determined by the source, the
target and the composition, which is Stacks 06K5.

The translation is stated with the base morphism of the translated pair as a parameter `b`
together with the equation `z ≫ t = b`, rather than with `z ≫ t` itself, so that the ambient
fibre products of the statements have an atomic morphism as a leg; the intended instance is
`b = z ≫ t` and the equation is then a reflexivity.

The target morphism is built by applying the translation over the arrow space `Z_univ` itself,
with the tautological pair `(u, Z)` and the tautological arrow `z` there. The tautological pair
is the one that the source morphism followed by the inclusion of `U'` names under Stacks 04PE,
part (2); the translated pair is then named by a morphism `Z_univ ⟶ (R_s/U)_fin` under the same
bijection, and `t'` is that morphism read as a morphism into the open subspace `U'`. Reading it
there needs exactly that every pair the morphism names over a scheme of the site contains the
unit, which follows from containment over `Z_univ` by transport along the cartesian squares of
Stacks 04PE, part (2).

Clause (3) of Stacks 04RT, that the arrow of a point of `Z_univ` lies in that point's
collection, is not carried by `FinitePart`; it is proved here from the universal property, as
`FinitePart.containsArrow_sourcePair`. It is the hypothesis that the translated pair needs in
order to contain the unit.

`t'` is constructed for the finite part that `GroupoidInAlgebraicSpaces.finitePart` builds
rather than for an arbitrary term of `FinitePart`, because landing a point in the object space
of an arbitrary one would mean inverting its inclusion into the finite part on its range, and
the inverse of an injection is not available as data. For the constructed finite part the object
space is the subfunctor of Stacks 04RR itself, so the factorization is
`CategoryTheory.Subfunctor.lift`.

The three remaining structure morphisms `c'`, `e'`, `i'` of Stacks 04RT, the groupoid laws they
satisfy and therefore the canonical morphism of groupoids of Stacks 04RU are not constructed
here.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RS](https://stacks.math.columbia.edu/tag/04RS)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidTarget
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) AlgebraicGeometry.Space.hasPullback_presheaf_groupoidTarget
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidTarget B S hS).has_limit _

namespace Deformation.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- The inverse arrow of a groupoid in functors is the inverse arrow of the septuple obtained
by evaluating at the test object. -/
theorem inverseArrow_eq_pointwiseData (D : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a : D.arrows.obj T) :
    inverseArrow D T a = (D.pointwiseData T).inverseArrow a := rfl

/-- The identity arrow of a groupoid in functors is the unit of the septuple obtained by
evaluating at the test object. -/
theorem identity_eq_pointwiseData (D : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x : D.objects.obj T) :
    D.identity T x = (D.pointwiseData T).identityArrow x := rfl

/-- A composite has the source of its second argument. -/
theorem source_compose (D : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a b : D.arrows.obj T) (h : D.source.app T a = D.target.app T b) :
    D.source.app T (D.compose T a b h) = D.source.app T b :=
  (D.pointwiseData T).source_comp a b h

/-- A composite has the target of its first argument. -/
theorem target_compose (D : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a b : D.arrows.obj T) (h : D.source.app T a = D.target.app T b) :
    D.target.app T (D.compose T a b h) = D.target.app T a :=
  (D.pointwiseData T).target_comp a b h

/-- Composition is natural in the test object. -/
theorem map_compose (D : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    (a b : D.arrows.obj T) (h : D.source.app T a = D.target.app T b)
    (h' : D.source.app T' (D.arrows.map f a) = D.target.app T' (D.arrows.map f b)) :
    D.arrows.map f (D.compose T a b h) =
      D.compose T' (D.arrows.map f a) (D.arrows.map f b) h' := by
  have hpm : (composableArrows D.objects D.arrows D.source D.target).map f
        (⟨(a, b), h⟩ : (composableArrows D.objects D.arrows D.source D.target).obj T) =
      (⟨(D.arrows.map f a, D.arrows.map f b), h'⟩ :
        (composableArrows D.objects D.arrows D.source D.target).obj T') := Subtype.ext rfl
  have hn := NatTrans.naturality_apply D.comp f
    (⟨(a, b), h⟩ : (composableArrows D.objects D.arrows D.source D.target).obj T)
  rw [hpm] at hn
  exact hn.symm

/-- The inverse arrow is natural in the test object.

The inverse arrows assemble into a natural transformation of the arrow functor, which is
Stacks 06K5; naturality of the rule is read off from that transformation. -/
theorem map_inverseArrow (D : GroupoidInFunctors.{u, v, w} C) {T T' : C} (f : T ⟶ T')
    (a : D.arrows.obj T) :
    D.arrows.map f (inverseArrow D T a) = inverseArrow D T' (D.arrows.map f a) := by
  obtain ⟨i, hi, -⟩ := existsUnique_inverse D
  rw [← hi T a, ← hi T' (D.arrows.map f a)]
  exact (NatTrans.naturality_apply i f a).symm

end Deformation.GroupoidInFunctors

namespace AlgebraicGeometry

namespace Space

/-- The arrow `z` lies in the open subspace of a pair of Stacks 04PC over the same base: the
section `(1_T, z)` of the ambient fibre product factors through the open subspace.

In the reading of Stacks 04RT, where a pair over `T` is a `T`-valued family of finite
collections of arrows with source `a`, this is the condition `z ∈ Z` on a `T`-valued point `z`
of `X` with `f ∘ z = a`. -/
def ContainsArrow (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : AlgebraicSpaces B S hS} (f : X ⟶ Y) (p : FiniteOpenSubspace B S hS f T)
    (z : T ⟶ X) (hz : z.hom ≫ f.hom = p.toBase.hom) : Prop :=
  ∃ l : T.obj ⟶ p.subspace.toFunctor,
    l ≫ p.subspace.ι = pullback.lift (𝟙 T.obj) z.hom (by rw [Category.id_comp, hz])

/-- A pair of Stacks 04PC over `T` contains the arrow `z` as soon as every pair it base changes
to over a scheme of the site contains the restriction of `z` there.

The hypotheses are the data that Stacks 04PE, part (2), supplies for the morphism
`T ⟶ (X/Y)_fin` naming the pair; the factorization of `(1_V, z)` over `V` is transported along
the cartesian square, and the resulting pointwise membership assembles into a factorization
over `T`. -/
theorem containsArrow_of_pointwise (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : AlgebraicSpaces B S hS)
    (p : FiniteOpenSubspace B S hS f T) (z : T ⟶ X) (hz : z.hom ≫ f.hom = p.toBase.hom)
    (q : ∀ V : BigFppfOver B S hS, ((schemeSpace V).obj ⟶ T.obj) →
      FiniteOpenSubspace B S hS f (schemeSpace V))
    (hsquare : ∀ V g, ∃ j : (q V g).subspace.toFunctor ⟶ p.subspace.toFunctor,
      IsPullback ((q V g).subspace.ι ≫ pullback.fst (q V g).toBase.hom f.hom) j g
          (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) ∧
        j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
          (q V g).subspace.ι ≫ pullback.snd (q V g).toBase.hom f.hom)
    (hq : ∀ V g, ∃ l : (schemeSpace V).obj ⟶ (q V g).subspace.toFunctor,
      l ≫ (q V g).subspace.ι ≫ pullback.fst (q V g).toBase.hom f.hom =
          𝟙 (schemeSpace V).obj ∧
        l ≫ (q V g).subspace.ι ≫ pullback.snd (q V g).toBase.hom f.hom = g ≫ z.hom) :
    ContainsArrow B S hS f p z hz := by
  classical
  let s := pullback.lift (f := p.toBase.hom) (g := f.hom) (𝟙 T.obj) z.hom
    (by rw [Category.id_comp, hz])
  have hsfst : s ≫ pullback.fst p.toBase.hom f.hom = 𝟙 T.obj := pullback.lift_fst _ _ _
  have hssnd : s ≫ pullback.snd p.toBase.hom f.hom = z.hom := pullback.lift_snd _ _ _
  have hle : Subfunctor.range s ≤ p.subspace := by
    intro V y hy
    obtain ⟨w, rfl⟩ := hy
    let g : (schemeSpace V.unop).obj ⟶ T.obj := yonedaEquiv.symm w
    have hw : yonedaEquiv g = w := Equiv.apply_symm_apply _ _
    obtain ⟨j, hpbsq, hjsnd⟩ := hsquare V.unop g
    obtain ⟨l, hlfst, hlsnd⟩ := hq V.unop g
    have hfst : (l ≫ j) ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom = g := by
      rw [Category.assoc, ← hpbsq.w, ← Category.assoc, hlfst, Category.id_comp]
    have hsnd : (l ≫ j) ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom = g ≫ z.hom := by
      rw [Category.assoc, hjsnd, hlsnd]
    have hm : (l ≫ j) ≫ p.subspace.ι = g ≫ s := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfst, Category.assoc, hsfst, Category.comp_id]
      · rw [Category.assoc, hsnd, Category.assoc, hssnd]
    have hgoal : s.app V w = yonedaEquiv (g ≫ s) := by rw [yonedaEquiv_comp, hw]
    rw [hgoal.trans (congrArg (fun k => yonedaEquiv k) hm).symm]
    exact (yonedaEquiv (l ≫ j)).2
  exact ⟨Subfunctor.lift s hle, Subfunctor.lift_ι s hle⟩

/-- Containment of the section induced by `σ` passes to a base change: if the pair `q` over
`T'` is cartesian over the pair `p` over `T` along `g`, and `p` contains the section, then so
does `q`. -/
theorem containsSection_of_isPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj) {T T' : AlgebraicSpaces B S hS}
    (p : FiniteOpenSubspace B S hS f T) (q : FiniteOpenSubspace B S hS f T')
    (g : T'.obj ⟶ T.obj) (hbase : q.toBase.hom = g ≫ p.toBase.hom)
    (j : q.subspace.toFunctor ⟶ p.subspace.toFunctor)
    (hpb : IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom))
    (hsnd : j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom)
    (hp : ContainsSection B S hS f σ hσ p) : ContainsSection B S hS f σ hσ q := by
  obtain ⟨l, hl⟩ := hp
  have hlfst : l ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom = 𝟙 T.obj := by
    rw [← Category.assoc, hl]
    exact pullback.lift_fst _ _ _
  have hlsnd : l ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      p.toBase.hom ≫ σ.hom := by
    rw [← Category.assoc, hl]
    exact pullback.lift_snd _ _ _
  have hfirst : 𝟙 T'.obj ≫ g =
      (g ≫ l) ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom := by
    simp only [Category.id_comp, Category.assoc, hlfst, Category.comp_id]
  refine ⟨hpb.lift (𝟙 T'.obj) (g ≫ l) hfirst, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, hpb.lift_fst, pullback.lift_fst]
  · rw [pullback.lift_snd, Category.assoc, ← hsnd, hpb.lift_snd_assoc, Category.assoc,
      hlsnd, hbase, Category.assoc]

end Space

namespace GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- Equal morphisms of presheaves have equal values. -/
private theorem app_eq_of_eq {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {α β : F ⟶ F'}
    (h : α = β) (V : (BigFppfOver C S hS)ᵒᵖ) (x : F.obj V) : α.app V x = β.app V x :=
  congrArg (fun k : F ⟶ F' => k.app V x) h

/-! ### The inverse of a groupoid in algebraic spaces -/

/-- The inverse of a groupoid in algebraic spaces: the morphism `i : R ⟶ R` of the arrow space
to itself whose value at a point of a test scheme is the inverse arrow there.

A groupoid in algebraic spaces does not carry its inverse as data; the inverse is determined by
the source, target and composition, which is Stacks 06K5. Its components are the inverse arrows
of the underlying groupoid in presheaves, and these are natural. -/
noncomputable def inverseHom (G : GroupoidInAlgebraicSpaces C S hS B) : G.arrows ⟶ G.arrows :=
  ObjectProperty.homMk
    { app := fun V => ↾ fun x =>
        (G.toGroupoidInFunctors.pointwiseData V).inverseArrow x
      naturality := by
        intro V V' f
        ext x
        exact (Deformation.GroupoidInFunctors.map_inverseArrow
          G.toGroupoidInFunctors f x).symm }

/-- The component of `inverseHom G` at `V` sends an arrow `x` to the inverse arrow of `x` in
the groupoid of `V`-points. -/
@[simp]
theorem inverseHom_hom_app (G : GroupoidInAlgebraicSpaces C S hS B)
    (V : (BigFppfOver C S hS)ᵒᵖ) (x : G.arrows.obj.obj V) :
    (inverseHom G).hom.app V x =
      (G.toGroupoidInFunctors.pointwiseData V).inverseArrow x := rfl

/-- The components of the inverse are the inverse arrows of the evaluated groupoids. -/
theorem inverseHom_hom_app_eq_inverseArrow (G : GroupoidInAlgebraicSpaces C S hS B)
    (V : (BigFppfOver C S hS)ᵒᵖ) (x : G.arrows.obj.obj V) :
    (inverseHom G).hom.app V x =
      Deformation.inverseArrow G.toGroupoidInFunctors V x := rfl

/-- The source of the inverse of an arrow is the target of the arrow. -/
theorem inverseHom_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inverseHom G).hom ≫ G.source.hom = G.target.hom := by
  ext V x
  exact (G.toGroupoidInFunctors.pointwiseData V).source_inverseArrow x

/-- The target of the inverse of an arrow is the source of the arrow. -/
theorem inverseHom_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inverseHom G).hom ≫ G.target.hom = G.source.hom := by
  ext V x
  exact (G.toGroupoidInFunctors.pointwiseData V).target_inverseArrow x

/-! ### Families of arrows and their composites -/

variable {G : GroupoidInAlgebraicSpaces C S hS B}

/-- Two families of arrows over a presheaf, the source of the first being the target of the
second, are composable at every point. -/
theorem composeHom_condition {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {β α : F ⟶ G.arrows.obj} (h : β ≫ G.source.hom = α ≫ G.target.hom)
    (V : (BigFppfOver C S hS)ᵒᵖ) (x : F.obj V) :
    G.toGroupoidInFunctors.source.app V (β.app V x) =
      G.toGroupoidInFunctors.target.app V (α.app V x) :=
  app_eq_of_eq h V x

/-- The composite `β ∘ α` of two families of arrows parametrized by a presheaf `F`, defined
when the source of `β` is the target of `α`: at every point of `F` it is the composite of the
two arrows there. -/
noncomputable def composeHom {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (β α : F ⟶ G.arrows.obj)
    (h : β ≫ G.source.hom = α ≫ G.target.hom) : F ⟶ G.arrows.obj where
  app V := ↾ fun x => G.toGroupoidInFunctors.compose V (β.app V x) (α.app V x)
    (composeHom_condition h V x)
  naturality := by
    intro V V' f
    ext x
    have hb := NatTrans.naturality_apply β f x
    have ha := NatTrans.naturality_apply α f x
    have h2 : G.toGroupoidInFunctors.source.app V' (G.arrows.obj.map f (β.app V x)) =
        G.toGroupoidInFunctors.target.app V' (G.arrows.obj.map f (α.app V x)) := by
      rw [← hb, ← ha]
      exact composeHom_condition h V' (F.map f x)
    change G.toGroupoidInFunctors.compose V' (β.app V' (F.map f x)) (α.app V' (F.map f x))
        (composeHom_condition h V' (F.map f x)) =
      G.arrows.obj.map f (G.toGroupoidInFunctors.compose V (β.app V x) (α.app V x)
        (composeHom_condition h V x))
    exact (Deformation.GroupoidInFunctors.compose_congr G.toGroupoidInFunctors V'
        (composeHom_condition h V' (F.map f x)) h2 hb ha).trans
      (Deformation.GroupoidInFunctors.map_compose G.toGroupoidInFunctors f (β.app V x)
        (α.app V x) (composeHom_condition h V x) h2).symm

/-- A composite family depends only on the two families composed. -/
theorem composeHom_congr {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {β α β' α' : F ⟶ G.arrows.obj} (hβ : β = β') (hα : α = α')
    (h : β ≫ G.source.hom = α ≫ G.target.hom)
    (h' : β' ≫ G.source.hom = α' ≫ G.target.hom) :
    composeHom β α h = composeHom β' α' h' := by
  subst hβ hα
  rfl

/-- A composite family has the source of its second factor. -/
theorem composeHom_comp_source {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (β α : F ⟶ G.arrows.obj) (h : β ≫ G.source.hom = α ≫ G.target.hom) :
    composeHom β α h ≫ G.source.hom = α ≫ G.source.hom := by
  ext V x
  exact Deformation.GroupoidInFunctors.source_compose G.toGroupoidInFunctors V _ _ _

/-- A composite family has the target of its first factor. -/
theorem composeHom_comp_target {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (β α : F ⟶ G.arrows.obj) (h : β ≫ G.source.hom = α ≫ G.target.hom) :
    composeHom β α h ≫ G.target.hom = β ≫ G.target.hom := by
  ext V x
  exact Deformation.GroupoidInFunctors.target_compose G.toGroupoidInFunctors V _ _ _

/-- Reparametrizing a composite family is composing the reparametrized families. -/
theorem comp_composeHom {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (φ : F' ⟶ F)
    (β α : F ⟶ G.arrows.obj) (h : β ≫ G.source.hom = α ≫ G.target.hom)
    (h' : (φ ≫ β) ≫ G.source.hom = (φ ≫ α) ≫ G.target.hom) :
    φ ≫ composeHom β α h = composeHom (φ ≫ β) (φ ≫ α) h' := by
  ext V x
  rfl

/-- Reparametrizing a composite family, with the two reparametrized families named. -/
theorem composeHom_comp_left {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (φ : F' ⟶ F)
    {β α : F ⟶ G.arrows.obj} (h : β ≫ G.source.hom = α ≫ G.target.hom)
    {β' α' : F' ⟶ G.arrows.obj} (hβ : φ ≫ β = β') (hα : φ ≫ α = α')
    (h' : β' ≫ G.source.hom = α' ≫ G.target.hom) :
    φ ≫ composeHom β α h = composeHom β' α' h' := by
  subst hβ hα
  exact comp_composeHom φ β α h _

/-- A family composed with its own inverse on the right is the unit at its target. -/
theorem composeHom_inverse_self {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (β : F ⟶ G.arrows.obj)
    (h : β ≫ G.source.hom = (β ≫ (inverseHom G).hom) ≫ G.target.hom) :
    composeHom β (β ≫ (inverseHom G).hom) h = β ≫ G.target.hom ≫ (identityHom G).hom := by
  ext V x
  exact (G.toGroupoidInFunctors.pointwiseData V).comp_inverseArrow_snd (β.app V x) _

/-- Composing `β ∘ α⁻¹` with `α` returns `β`, for two families with a common source. -/
theorem composeHom_composeHom_inverse {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (β α : F ⟶ G.arrows.obj) (hs : β ≫ G.source.hom = α ≫ G.source.hom)
    (h₀ : β ≫ G.source.hom = (α ≫ (inverseHom G).hom) ≫ G.target.hom)
    (h₁ : composeHom β (α ≫ (inverseHom G).hom) h₀ ≫ G.source.hom = α ≫ G.target.hom) :
    composeHom (composeHom β (α ≫ (inverseHom G).hom) h₀) α h₁ = β := by
  ext V x
  show G.toGroupoidInFunctors.compose V
      (G.toGroupoidInFunctors.compose V (β.app V x)
        ((G.toGroupoidInFunctors.pointwiseData V).inverseArrow (α.app V x)) _)
      (α.app V x) _ = β.app V x
  exact (G.toGroupoidInFunctors.pointwiseData V).comp_comp_inverseArrow
    (β.app V x) (α.app V x) (app_eq_of_eq hs V x) _ _

/-- Composing `β ∘ α` with `α⁻¹` returns `β`, for the source of `β` the target of `α`. -/
theorem composeHom_composeHom_inverse' {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (β α : F ⟶ G.arrows.obj) (h : β ≫ G.source.hom = α ≫ G.target.hom)
    (h₁ : composeHom β α h ≫ G.source.hom = (α ≫ (inverseHom G).hom) ≫ G.target.hom) :
    composeHom (composeHom β α h) (α ≫ (inverseHom G).hom) h₁ = β := by
  ext V x
  show G.toGroupoidInFunctors.compose V
      (G.toGroupoidInFunctors.compose V (β.app V x) (α.app V x) _)
      ((G.toGroupoidInFunctors.pointwiseData V).inverseArrow (α.app V x)) _ = β.app V x
  exact (G.toGroupoidInFunctors.pointwiseData V).comp_comp_inverseArrow'
    (β.app V x) (α.app V x) (app_eq_of_eq h V x) _

/-! ### The isomorphism `c(-, i ∘ z)` of ambient fibre products -/

variable {T : AlgebraicSpaces C S hS} {a b : T ⟶ G.objects}

/-- The second projection of the ambient fibre product has the same source as the first
projection followed by any arrow `z` whose image under `k` is the base morphism. -/
private theorem snd_comp_source_eq (z : T ⟶ G.arrows) (k : G.arrows ⟶ G.objects)
    (hz : z.hom ≫ k.hom = a.hom) :
    pullback.snd a.hom G.source.hom ≫ G.source.hom =
      (pullback.fst a.hom G.source.hom ≫ z.hom) ≫ k.hom := by
  rw [Category.assoc, hz]
  exact pullback.condition.symm

/-- The two families of arrows composed by `c(-, i ∘ z)` are composable. -/
theorem translateFwd_condition (z : T ⟶ G.arrows)
    (hzs : z.hom ≫ G.source.hom = a.hom) :
    pullback.snd a.hom G.source.hom ≫ G.source.hom =
      ((pullback.fst a.hom G.source.hom ≫ z.hom) ≫ (inverseHom G).hom) ≫ G.target.hom := by
  rw [snd_comp_source_eq z _ hzs]
  simp only [Category.assoc, inverseHom_comp_target]

/-- The translating family lies over `b` on the base component. -/
theorem translateFwd_lift (z : T ⟶ G.arrows)
    (hzs : z.hom ≫ G.source.hom = a.hom) (hzt : z.hom ≫ G.target.hom = b.hom) :
    pullback.fst a.hom G.source.hom ≫ b.hom =
      composeHom (pullback.snd a.hom G.source.hom)
        ((pullback.fst a.hom G.source.hom ≫ z.hom) ≫ (inverseHom G).hom)
        (translateFwd_condition z hzs) ≫ G.source.hom := by
  rw [composeHom_comp_source]
  simp only [Category.assoc, inverseHom_comp_source]
  rw [hzt]

/-- The morphism `c(-, i ∘ z) : T ×_{a, U, s} R ⟶ T ×_{b, U, s} R`, for `z` an arrow over `T`
with source `a` and target `b`: it is the identity on the base component and composition with
the inverse of `z` on the arrow component. -/
noncomputable def translateFwd (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    pullback a.hom G.source.hom ⟶ pullback b.hom G.source.hom :=
  pullback.lift (pullback.fst a.hom G.source.hom)
    (composeHom (pullback.snd a.hom G.source.hom)
      ((pullback.fst a.hom G.source.hom ≫ z.hom) ≫ (inverseHom G).hom)
      (translateFwd_condition z hzs))
    (translateFwd_lift z hzs hzt)

/-- The first projection of `translateFwd z hzs hzt` is the first projection of the source
fibre product. -/
@[simp]
theorem translateFwd_fst (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    translateFwd z hzs hzt ≫ pullback.fst b.hom G.source.hom =
      pullback.fst a.hom G.source.hom := pullback.lift_fst _ _ _

/-- The second projection of `translateFwd z hzs hzt` is the composite of the second
projection with the inverse of `z`. -/
theorem translateFwd_snd (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    translateFwd z hzs hzt ≫ pullback.snd b.hom G.source.hom =
      composeHom (pullback.snd a.hom G.source.hom)
        ((pullback.fst a.hom G.source.hom ≫ z.hom) ≫ (inverseHom G).hom)
        (translateFwd_condition z hzs) := pullback.lift_snd _ _ _

/-- The two families of arrows composed by `c(-, z)` are composable. -/
theorem translateBwd_condition (z : T ⟶ G.arrows)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    pullback.snd b.hom G.source.hom ≫ G.source.hom =
      (pullback.fst b.hom G.source.hom ≫ z.hom) ≫ G.target.hom :=
  snd_comp_source_eq z _ hzt

/-- The inverse translating family lies over `a` on the base component. -/
theorem translateBwd_lift (z : T ⟶ G.arrows)
    (hzs : z.hom ≫ G.source.hom = a.hom) (hzt : z.hom ≫ G.target.hom = b.hom) :
    pullback.fst b.hom G.source.hom ≫ a.hom =
      composeHom (pullback.snd b.hom G.source.hom)
        (pullback.fst b.hom G.source.hom ≫ z.hom)
        (translateBwd_condition z hzt) ≫ G.source.hom := by
  rw [composeHom_comp_source]
  simp only [Category.assoc]
  rw [hzs]

/-- The morphism `c(-, z) : T ×_{b, U, s} R ⟶ T ×_{a, U, s} R` inverse to `c(-, i ∘ z)`. -/
noncomputable def translateBwd (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    pullback b.hom G.source.hom ⟶ pullback a.hom G.source.hom :=
  pullback.lift (pullback.fst b.hom G.source.hom)
    (composeHom (pullback.snd b.hom G.source.hom)
      (pullback.fst b.hom G.source.hom ≫ z.hom)
      (translateBwd_condition z hzt))
    (translateBwd_lift z hzs hzt)

/-- The first projection of `translateBwd z hzs hzt` is the first projection of the source
fibre product. -/
@[simp]
theorem translateBwd_fst (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    translateBwd z hzs hzt ≫ pullback.fst a.hom G.source.hom =
      pullback.fst b.hom G.source.hom := pullback.lift_fst _ _ _

/-- The second projection of `translateBwd z hzs hzt` is the composite of the second
projection with `z`. -/
theorem translateBwd_snd (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    translateBwd z hzs hzt ≫ pullback.snd a.hom G.source.hom =
      composeHom (pullback.snd b.hom G.source.hom)
        (pullback.fst b.hom G.source.hom ≫ z.hom)
        (translateBwd_condition z hzt) := pullback.lift_snd _ _ _

/-- The two translating morphisms are mutually inverse. -/
theorem translateFwd_translateBwd (z : T ⟶ G.arrows)
    (hzs : z.hom ≫ G.source.hom = a.hom) (hzt : z.hom ≫ G.target.hom = b.hom) :
    translateFwd z hzs hzt ≫ translateBwd z hzs hzt = 𝟙 _ := by
  have h₁ : composeHom (pullback.snd a.hom G.source.hom)
        ((pullback.fst a.hom G.source.hom ≫ z.hom) ≫ (inverseHom G).hom)
        (translateFwd_condition z hzs) ≫ G.source.hom =
      (pullback.fst a.hom G.source.hom ≫ z.hom) ≫ G.target.hom := by
    rw [composeHom_comp_source]
    simp only [Category.assoc, inverseHom_comp_source]
  apply pullback.hom_ext
  · rw [Category.assoc, translateBwd_fst, translateFwd_fst, Category.id_comp]
  · rw [Category.assoc, translateBwd_snd, Category.id_comp,
      composeHom_comp_left (translateFwd z hzs hzt) (translateBwd_condition z hzt)
        (translateFwd_snd z hzs hzt)
        (by simp only [← Category.assoc, translateFwd_fst]) h₁]
    exact composeHom_composeHom_inverse _ _ (snd_comp_source_eq z _ hzs)
      (translateFwd_condition z hzs) h₁

/-- The two translating morphisms are mutually inverse. -/
theorem translateBwd_translateFwd (z : T ⟶ G.arrows)
    (hzs : z.hom ≫ G.source.hom = a.hom) (hzt : z.hom ≫ G.target.hom = b.hom) :
    translateBwd z hzs hzt ≫ translateFwd z hzs hzt = 𝟙 _ := by
  have h₁ : composeHom (pullback.snd b.hom G.source.hom)
        (pullback.fst b.hom G.source.hom ≫ z.hom)
        (translateBwd_condition z hzt) ≫ G.source.hom =
      ((pullback.fst b.hom G.source.hom ≫ z.hom) ≫ (inverseHom G).hom) ≫ G.target.hom := by
    rw [composeHom_comp_source]
    simp only [Category.assoc, inverseHom_comp_target]
  apply pullback.hom_ext
  · rw [Category.assoc, translateFwd_fst, translateBwd_fst, Category.id_comp]
  · rw [Category.assoc, translateFwd_snd, Category.id_comp,
      composeHom_comp_left (translateBwd z hzs hzt) (translateFwd_condition z hzs)
        (translateBwd_snd z hzs hzt)
        (by simp only [← Category.assoc, translateBwd_fst]) h₁]
    exact composeHom_composeHom_inverse' _ _ (translateBwd_condition z hzt) h₁

/-- **The translation isomorphism of Stacks 04RT.** For an arrow `z` over `T` with source `a`
and target `b`, the rule `c(-, i ∘ z)` is an isomorphism
`T ×_{a, U, s} R ≅ T ×_{b, U, s} R` with inverse `c(-, z)`. -/
noncomputable def translateAmbientIso (z : T ⟶ G.arrows)
    (hzs : z.hom ≫ G.source.hom = a.hom) (hzt : z.hom ≫ G.target.hom = b.hom) :
    pullback a.hom G.source.hom ≅ pullback b.hom G.source.hom where
  hom := translateFwd z hzs hzt
  inv := translateBwd z hzs hzt
  hom_inv_id := translateFwd_translateBwd z hzs hzt
  inv_hom_id := translateBwd_translateFwd z hzs hzt

/-- The forward morphism of `translateAmbientIso z hzs hzt` is `translateFwd z hzs hzt`. -/
@[simp]
theorem translateAmbientIso_hom (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = a.hom)
    (hzt : z.hom ≫ G.target.hom = b.hom) :
    (translateAmbientIso z hzs hzt).hom = translateFwd z hzs hzt := rfl

/-! ### The translation of a pair of Stacks 04PC -/

/-- **The translation `c(Z, i ∘ z)` of Stacks 04RT.** The pair of Stacks 04PC for the source
morphism of a groupoid in algebraic spaces obtained from a pair `p = (u, Z)` over `T` and an
arrow `z : T ⟶ R` with source `u`: its base morphism is `t ∘ z` and its open subspace is the
image of `Z` under the isomorphism `c(-, i ∘ z)`.

Openness of the image and finiteness of its projection to `T` are transported along that
isomorphism. -/
noncomputable def translatePair (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom) :
    Space.FiniteOpenSubspace C S hS G.source T :=
  Space.FiniteOpenSubspace.ofAmbientIso C S hS p (z ≫ G.target)
    (translateAmbientIso (b := z ≫ G.target) z hz rfl)
    (translateFwd_fst (b := z ≫ G.target) z hz rfl)

/-- The base morphism of the translated pair is `z ≫ G.target`. -/
@[simp]
theorem translatePair_toBase (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom) :
    (translatePair p z hz).toBase = z ≫ G.target := rfl

/-- The open subspace of the translated pair is the preimage of the open subspace of `p` under
the inverse of `translateAmbientIso`. -/
theorem translatePair_subspace (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom) :
    (translatePair p z hz).subspace =
      p.subspace.preimage (translateAmbientIso (b := z ≫ G.target) z hz rfl).inv := rfl

/-- The open subspace of the translated pair is closed in the ambient fibre product as well as
open, because the source morphism is separated. This is Stacks 04PH. -/
theorem translatePair_isClosedSubspace (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom)
    (hsep : Space.IsSeparated C S hS G.source.hom) :
    Space.IsClosedSubspace C S hS (translatePair p z hz).subspace :=
  Space.FiniteOpenSubspace.isClosedSubspace C S hS G.source T (translatePair p z hz) hsep

/-- The section `(1_T, z)` of the ambient fibre product is carried by `c(-, i ∘ z)` to the
section of the translated ambient fibre product induced by the unit: pointwise this is the
identity `c(z, i(z)) = e(t(z))`. -/
theorem translateFwd_arrowSection (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom) :
    pullback.lift (f := p.toBase.hom) (g := G.source.hom) (𝟙 T.obj) z.hom
        (by rw [Category.id_comp, hz]) ≫
        translateFwd (b := z ≫ G.target) z hz rfl =
      pullback.lift (f := (z ≫ G.target).hom) (g := G.source.hom) (𝟙 T.obj)
        ((z ≫ G.target).hom ≫ (identityHom G).hom)
        (by simp only [Category.id_comp, Category.assoc,
          identityHom_comp_source G, Category.comp_id]) := by
  have hunit : z.hom ≫ G.source.hom = (z.hom ≫ (inverseHom G).hom) ≫ G.target.hom := by
    simp only [Category.assoc, inverseHom_comp_target]
  apply pullback.hom_ext
  · rw [Category.assoc, translateFwd_fst, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, translateFwd_snd,
      composeHom_comp_left
        (pullback.lift (f := p.toBase.hom) (g := G.source.hom) (𝟙 T.obj) z.hom
          (by rw [Category.id_comp, hz]))
        (translateFwd_condition z hz)
        (pullback.lift_snd _ _ _)
        (by simp only [← Category.assoc, pullback.lift_fst, Category.id_comp]) hunit,
      composeHom_inverse_self z.hom hunit, pullback.lift_snd]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]

/-- **Stacks 04RT, containment of the unit in the translated collection.** If the arrow `z`
lies in the pair `p`, then the translated pair contains the section of its ambient fibre
product induced by the unit of the groupoid.

Pointwise this is the computation `c(z, i(z)) = e(t(z))`: the unit at the new base point is the
image of `z` itself under the translation, and `z` was assumed to lie in the collection. -/
theorem translatePair_containsUnit (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom)
    (hmem : Space.ContainsArrow C S hS G.source p z hz) :
    Space.ContainsSection C S hS G.source (identityHom G) (identityHom_comp_source G)
      (translatePair p z hz) := by
  obtain ⟨l, hl⟩ := hmem
  refine ⟨l ≫ (Space.subfunctorIsoPreimage
    (translateAmbientIso (b := z ≫ G.target) z hz rfl) p.subspace).hom, ?_⟩
  show (l ≫ _) ≫
    (p.subspace.preimage (translateAmbientIso (b := z ≫ G.target) z hz rfl).inv).ι = _
  rw [Category.assoc, Space.subfunctorIsoPreimage_hom_ι, ← Category.assoc, hl,
    translateAmbientIso_hom, translateFwd_arrowSection p z hz]
  rfl

/-! ### The target morphism of the finite part -/

namespace FinitePart

variable (fp : FinitePart G)

/-- The arrow space `Z_univ` of the finite part, as an algebraic space: it is an open subspace
of the ambient fibre product, hence an algebraic space. -/
noncomputable abbrev arrowSpace : AlgebraicSpaces C S hS :=
  ⟨fp.pair.subspace.toFunctor, fp.pair.isOpen.1⟩

/-- The arrow `z` of a point `(u, Z, z)` of `Z_univ`, read as a morphism of algebraic spaces
from `Z_univ` to the arrow space of the groupoid. -/
noncomputable def arrowMap : arrowSpace fp ⟶ G.arrows := ObjectProperty.homMk fp.arrowHom

/-- The pair `(u, Z)` of a point `(u, Z, z)` of `Z_univ`, as a pair of Stacks 04PC over
`Z_univ` itself: it is the pair named by the source morphism `s'` followed by the inclusion of
`U'` into the finite part. -/
noncomputable def sourcePair : Space.FiniteOpenSubspace C S hS G.source (arrowSpace fp) :=
  (Space.finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)).1
    (fp.sourceHom ≫ fp.inclusion)

/-- The base morphism of the tautological pair over `Z_univ` is `u`, that is the source
morphism of the finite part followed by `g`. -/
theorem sourcePair_toBase : (sourcePair fp).toBase.hom = fp.sourceHom ≫ fp.pair.toBase.hom :=
  (Space.toBase_finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)
      (fp.sourceHom ≫ fp.inclusion)).trans
    (by rw [Category.assoc, ← fp.toBase_pair])

/-- The tautological arrow over `Z_univ` has the base morphism of the tautological pair as its
source. -/
theorem arrowMap_comp_source :
    (arrowMap fp).hom ≫ G.source.hom = (sourcePair fp).toBase.hom := by
  rw [sourcePair_toBase]
  exact (fp.sourceHom_comp_toBase).symm

/-- **Stacks 04RT, the target rule.** The pair `(t ∘ z, c(Z, i ∘ z))` of Stacks 04PC over
`Z_univ`, obtained by translating the tautological pair by the tautological arrow. -/
noncomputable def targetPair : Space.FiniteOpenSubspace C S hS G.source (arrowSpace fp) :=
  translatePair (sourcePair fp) (arrowMap fp) (arrowMap_comp_source fp)

/-- The base morphism of `targetPair fp` is `arrowMap fp ≫ G.target`. -/
theorem targetPair_toBase : (targetPair fp).toBase = arrowMap fp ≫ G.target := rfl

/-- The source morphism of the finite part read out of the pair. -/
theorem sourceHom_eq :
    fp.sourceHom = fp.pair.subspace.ι ≫ pullback.fst fp.pair.toBase.hom G.source.hom := by
  rw [FinitePart.sourceHom]

/-- The morphism on arrows of the canonical morphism of groupoids read out of the pair. -/
theorem arrowHom_eq :
    fp.arrowHom = fp.pair.subspace.ι ≫ pullback.snd fp.pair.toBase.hom G.source.hom := by
  rw [FinitePart.arrowHom]

/-- **Stacks 04RT, clause (3).** The tautological arrow over `Z_univ` lies in the tautological
pair: at every scheme-valued point `(u, Z, z)` of `Z_univ`, the arrow `z` lies in the collection
`Z`.

At a scheme-valued point `g` of `Z_univ`, the open subspace `Z` of the pair named by `u` is
cartesian over `Z_univ` along `u`, by Stacks 04PE, part (2), and `g` itself lies over `u`; so
the universal property of that cartesian square produces the factorization of `(1_V, z)`
through `Z`. -/
theorem containsArrow_sourcePair :
    Space.ContainsArrow C S hS G.source (sourcePair fp) (arrowMap fp)
      (arrowMap_comp_source fp) := by
  refine Space.containsArrow_of_pointwise C S hS G.source (arrowSpace fp) (sourcePair fp)
    (arrowMap fp) (arrowMap_comp_source fp)
    (fun V g => (Space.finiteOpenSubspacePresheaf C S hS G.source).sections V
      ((fp.sourceHom ≫ fp.inclusion).app (op V) (yonedaEquiv g)))
    (fun V g => ((Space.finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)).2
      (fp.sourceHom ≫ fp.inclusion) V g).2)
    (fun V g => ?_)
  have hpt : (fp.sourceHom ≫ fp.inclusion).app (op V) (yonedaEquiv g) =
      fp.inclusion.app (op V) (yonedaEquiv (g ≫ fp.sourceHom)) := rfl
  rw [hpt]
  have hspec := (Space.finiteOpenSubspaceEquiv C S hS G.source fp.objects).2
    fp.inclusion V (g ≫ fp.sourceHom)
  rw [← fp.pair_eq] at hspec
  obtain ⟨-, j, hpb, hjsnd⟩ := hspec
  have hcomm : 𝟙 (schemeSpace V).obj ≫ (g ≫ fp.sourceHom) =
      g ≫ fp.pair.subspace.ι ≫ pullback.fst fp.pair.toBase.hom G.source.hom :=
    (Category.id_comp (g ≫ fp.sourceHom)).trans
      (congrArg (fun k => g ≫ k) (sourceHom_eq fp))
  refine ⟨hpb.lift (𝟙 (schemeSpace V).obj) g hcomm, ?_, ?_⟩
  · simpa only [Category.assoc] using
      hpb.lift_fst (𝟙 (schemeSpace V).obj) g hcomm
  · have h₂ := hpb.lift_snd (𝟙 (schemeSpace V).obj) g hcomm
    calc hpb.lift (𝟙 (schemeSpace V).obj) g hcomm ≫
          _ ≫ pullback.snd _ G.source.hom
        = hpb.lift (𝟙 (schemeSpace V).obj) g hcomm ≫
            j ≫ fp.pair.subspace.ι ≫ pullback.snd fp.pair.toBase.hom G.source.hom := by
          simp only [hjsnd]
      _ = g ≫ fp.pair.subspace.ι ≫ pullback.snd fp.pair.toBase.hom G.source.hom := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ fp.pair.subspace.ι ≫
              pullback.snd fp.pair.toBase.hom G.source.hom) h₂
      _ = g ≫ (arrowMap fp).hom := by rw [← arrowHom_eq]; rfl

/-- **Stacks 04RT, containment of the unit in the translated collection, over `Z_univ`.** -/
theorem containsUnit_targetPair :
    Space.ContainsSection C S hS G.source (identityHom G) (identityHom_comp_source G)
      (targetPair fp) :=
  translatePair_containsUnit (sourcePair fp) (arrowMap fp) (arrowMap_comp_source fp)
    (containsArrow_sourcePair fp)

/-- The morphism from `Z_univ` into the finite part of the source morphism naming the
translated pair `(t ∘ z, c(Z, i ∘ z))`, by Stacks 04PE, part (2). -/
noncomputable def targetSection :
    (arrowSpace fp).obj ⟶ (Space.finiteOpenSubspacePresheaf C S hS G.source).toFunctor :=
  (Space.finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)).1.symm (targetPair fp)

/-- The pair named by `targetSection fp` is `targetPair fp`. -/
theorem targetSection_spec :
    (Space.finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)).1 (targetSection fp) =
      targetPair fp := Equiv.apply_symm_apply _ _

/-- Every pair which the translated section names over a scheme of the site contains the
section induced by the unit, so the section factors through the finite part containing the
unit, which is `U'`. -/
theorem range_targetSection_le :
    Subfunctor.range (targetSection fp) ≤
      (Space.finitePartWithSection C S hS G.source (identityHom G)
        (identityHom_comp_source G)).toSubfunctor := by
  intro V y hy
  obtain ⟨x, rfl⟩ := hy
  refine ((Space.finitePartWithSection C S hS G.source (identityHom G)
    (identityHom_comp_source G)).mem_iff V.unop ((targetSection fp).app V x)).2 ?_
  have hx : yonedaEquiv (yonedaEquiv.symm x :
      (schemeSpace V.unop).obj ⟶ (arrowSpace fp).obj) = x :=
    Equiv.apply_symm_apply _ _
  have hspec := (Space.finiteOpenSubspaceEquiv C S hS G.source (arrowSpace fp)).2
    (targetSection fp) V.unop (yonedaEquiv.symm x)
  rw [targetSection_spec, hx] at hspec
  obtain ⟨hb, j, hpb, hjsnd⟩ := hspec
  exact Space.containsSection_of_isPullback C S hS G.source (identityHom G)
    (identityHom_comp_source G) (targetPair fp) _ _ hb j hpb hjsnd (containsUnit_targetPair fp)

end FinitePart

/-- **Stacks 04RT, the target morphism `t'`.** The morphism `t' : Z_univ ⟶ U'` of the finite
part of a groupoid in algebraic spaces whose source morphism is separated and locally of finite
type: the rule `(u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z))`.

Its value is the morphism into the finite part of the source morphism naming the translation of
the tautological pair over `Z_univ` by the tautological arrow; that morphism factors through the
open subspace `U'` of pairs containing the unit because the translated pair does contain it. -/
noncomputable def targetHom (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    (finitePart G hsep hft).pair.subspace.toFunctor ⟶ (finitePart G hsep hft).objects.obj :=
  Subfunctor.lift (FinitePart.targetSection (finitePart G hsep hft))
    (FinitePart.range_targetSection_le (finitePart G hsep hft))

/-- Composing `targetHom` with the inclusion of the finite part gives the translated section
`FinitePart.targetSection`. -/
theorem targetHom_comp_inclusion (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    targetHom hsep hft ≫ (finitePart G hsep hft).inclusion =
      FinitePart.targetSection (finitePart G hsep hft) := Subfunctor.lift_ι _ _

/-- **Stacks 04RT.** The target morphism of the finite part lies over the target morphism of
the groupoid: the object `(t ∘ z, c(Z, i ∘ z))` of `U'` which `(u, Z, z)` is sent to has
`t ∘ z` as its morphism to `U`. -/
theorem targetHom_comp_toBase (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    targetHom hsep hft ≫ (finitePart G hsep hft).pair.toBase.hom =
      (finitePart G hsep hft).arrowHom ≫ G.target.hom := by
  calc targetHom hsep hft ≫ (finitePart G hsep hft).pair.toBase.hom
      = targetHom hsep hft ≫ (finitePart G hsep hft).inclusion ≫
          (Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap :=
        congrArg (fun k => targetHom hsep hft ≫ k) (finitePart G hsep hft).toBase_pair
    _ = FinitePart.targetSection (finitePart G hsep hft) ≫
          (Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap := by
        rw [← Category.assoc, targetHom_comp_inclusion]
    _ = ((Space.finiteOpenSubspaceEquiv C S hS G.source
            (FinitePart.arrowSpace (finitePart G hsep hft))).1
          (FinitePart.targetSection (finitePart G hsep hft))).toBase.hom :=
        (Space.toBase_finiteOpenSubspaceEquiv C S hS G.source
          (FinitePart.arrowSpace (finitePart G hsep hft))
          (FinitePart.targetSection (finitePart G hsep hft))).symm
    _ = (FinitePart.targetPair (finitePart G hsep hft)).toBase.hom :=
        congrArg (fun p : Space.FiniteOpenSubspace C S hS G.source
            (FinitePart.arrowSpace (finitePart G hsep hft)) => p.toBase.hom)
          (FinitePart.targetSection_spec (finitePart G hsep hft))
    _ = (finitePart G hsep hft).arrowHom ≫ G.target.hom := rfl

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
