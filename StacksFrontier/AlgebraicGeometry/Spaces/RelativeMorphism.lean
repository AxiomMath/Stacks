module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite

/-!
# The relative morphism functor (Stacks 05Y2)

Let `S` be a scheme contained in a big fppf site `B` and let `z : Z ⟶ Q` and `x : X ⟶ Q` be
morphisms of presheaves on the big fppf site of `S` — in the source, morphisms of algebraic spaces
over `S`. Stacks 05Y1 considers, for a test object `T`, the pairs `(a, b)` consisting of a morphism
`a : T ⟶ Q` and a morphism `b : T ×_{a, Q} Z ⟶ X` over `Q`, and Stacks 05Y2 assembles them into a
functor

```text
Mor_Q(Z, X) : (Sch/S)ᵒᵖ ⥤ Set,    T ↦ {(a, b) as above}.
```

This file constructs that functor together with its projection to `Q` and the identification of its
sections with pairs. The pair type is `AlgebraicGeometry.Space.RelativeMorphism`, in the source's
second description of `b` — a morphism to `X` rather than to `T ×_{a, Q} X`. The diagram the source
displays is `AlgebraicGeometry.Space.RelativeMorphismDiagram`, its first description, and the two
are the same data: `AlgebraicGeometry.Space.relativeMorphismEquivDiagram` proves the equivalence
the source only notes.

The one piece of content beyond bookkeeping is that the functor must be **small-valued**, while a
pair `(a, b)` is a pair of morphisms of presheaves and so a priori one universe too large.
Smallness is not special to algebraic spaces: the big fppf site of `S` is essentially small
(`AlgebraicGeometry.Stack.essentiallySmall_bigFppfOver`), so a natural transformation of presheaves
of `u`-types on it is determined by its components on a small model, and **every** hom type of that
presheaf category is `u`-small. That is
`AlgebraicGeometry.locallySmall_presheaf_bigFppfOver`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeMorphism`: **Stacks 05Y1**, a pair `(a, b)` over a test
  presheaf, in the source's second description of `b`.
* `AlgebraicGeometry.Space.RelativeMorphismDiagram`: **Stacks 05Y1** in the shape the source
  displays it, with `b : T ×_{a, Q} Z ⟶ T ×_{a, Q} X` over `T`.
* `AlgebraicGeometry.Space.RelativeMorphism.baseChangeMap`: the morphism
  `T ×_{a, Q} Z ⟶ T ×_{a, Q} X` of base changes a pair determines.
* `AlgebraicGeometry.Space.RelativeMorphism.restrict`: restriction of a pair along a morphism of
  test objects, by base change.
* `AlgebraicGeometry.Space.RelativeHomConstruction`: the relative morphism functor together with
  its projection to `Q`, the identification of its sections with pairs, and the description of its
  restriction maps.
* `AlgebraicGeometry.Space.relativeHom`, `AlgebraicGeometry.Space.relativeHomProjection` and
  `AlgebraicGeometry.Space.relativeHomSections`: the functor, its projection and the
  identification, read off the construction.

## Main results

* `AlgebraicGeometry.locallySmall_presheaf_bigFppfOver` and
  `AlgebraicGeometry.small_hom_presheaf`: the presheaf category of the big fppf site of `S` is
  locally `u`-small.
* `AlgebraicGeometry.Space.relativeMorphismEquivDiagram`: the source's two descriptions of a pair
  of Stacks 05Y1 are the same data.
* `AlgebraicGeometry.Space.relativeHomData`: **Stacks 05Y2**, the relative morphism functor.
* `AlgebraicGeometry.Space.relativeHomSections_map`: the restriction maps of the functor are
  restriction of pairs, as an equality.
* `CategoryTheory.Limits.pullback.mapFst`, `CategoryTheory.Limits.pullback.mapSnd` and their
  `isPullback` lemmas: precomposing one factor of a fibre product with a morphism produces a base
  change of that fibre product.

## Implementation notes

The second component of a pair lives in `pullback p.base z`, which depends on the first component,
so the functoriality of restriction cannot be checked componentwise; it needs a transport. The
transport is isolated in `AlgebraicGeometry.Space.RelativeMorphism.ext_of_base_eq`, which compares
the second components through `CategoryTheory.Limits.pullback.congrHom`. That comparison is
*literally the same `CategoryTheory.Limits.pullback.map`* as the one restriction along an identity
produces, so `AlgebraicGeometry.Space.RelativeMorphism.restrict_id` is `rfl` in its second
argument, and `restrict_comp` is one `CategoryTheory.Limits.pullback.hom_ext`.

Restriction is defined along an arbitrary morphism of test *presheaves*, not only along
`yoneda.map` of a morphism of the site; the identity and composition laws are then the plain ones,
and the presheaf is obtained by restricting along `yoneda.map`.

## References

* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

/-- The first projection of the canonical map between two pullbacks.
`CategoryTheory.Limits.pullback.map` is an `abbrev` for a
`CategoryTheory.Limits.pullback.lift`, so this is
`CategoryTheory.Limits.pullback.lift_fst`; it is recorded as a `simp` lemma because Mathlib has
none, and every comparison of base changes needs it. -/
@[reassoc (attr := simp)]
theorem pullback.map_fst {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫ pullback.fst g₁ g₂ =
      pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

/-- The second projection of the canonical map between two pullbacks. -/
@[reassoc (attr := simp)]
theorem pullback.map_snd {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫ pullback.snd g₁ g₂ =
      pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

/-- The comparison map `W' ×_Y X ⟶ W ×_Y X` of fibre products induced by `t : W' ⟶ W`, for the
structure morphism `t ≫ a` on the source. It is `CategoryTheory.Limits.pullback.map` of `t` and the
identity, but it is introduced as a definition of its own so that the only way it is ever used is
through its two components: the proof obligations `CategoryTheory.Limits.pullback.map` carries
mention the morphisms being compared, which blocks rewriting underneath it. -/
noncomputable def pullback.mapFst {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y)
    [HasPullback a z] [HasPullback (t ≫ a) z] : pullback (t ≫ a) z ⟶ pullback a z :=
  pullback.lift (pullback.fst (t ≫ a) z ≫ t) (pullback.snd (t ≫ a) z) (by
    rw [Category.assoc]
    exact pullback.condition)

/-- The first component of the comparison map of fibre products. -/
@[simp, reassoc (attr := simp)]
theorem pullback.mapFst_fst {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y) [HasPullback a z]
    [HasPullback (t ≫ a) z] :
    pullback.mapFst t a z ≫ pullback.fst a z = pullback.fst (t ≫ a) z ≫ t :=
  pullback.lift_fst _ _ _

/-- The second component of the comparison map of fibre products. -/
@[simp, reassoc (attr := simp), ega "I 3.3.4" "partial"]
theorem pullback.mapFst_snd {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y) [HasPullback a z]
    [HasPullback (t ≫ a) z] :
    pullback.mapFst t a z ≫ pullback.snd a z = pullback.snd (t ≫ a) z :=
  pullback.lift_snd _ _ _

/-- The comparison map of fibre products is `CategoryTheory.Limits.pullback.map` of `t` and the
identity. Stated with the proof obligations as variables so that it rewrites away any proofs they
were built with. Deliberately not a `simp` lemma: `CategoryTheory.Limits.pullback.map` of an
identity occurs throughout the library and rewriting it everywhere is not wanted. -/
theorem pullback.map_id_eq_mapFst {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y)
    [HasPullback a z] [HasPullback (t ≫ a) z] (eq₁ : (t ≫ a) ≫ 𝟙 Y = t ≫ a)
    (eq₂ : z ≫ 𝟙 Y = 𝟙 X ≫ z) :
    pullback.map (t ≫ a) z a z t (𝟙 X) (𝟙 Y) eq₁ eq₂ = pullback.mapFst t a z := by
  apply pullback.hom_ext <;> simp [pullback.map_fst, pullback.map_snd]

/-- Precomposing the first factor of a fibre product with `t : W' ⟶ W` produces a base change:
`W' ×_Y X` is the fibre product of `W ×_Y X` with `W'` over `W`. The square is cartesian because it
is the left half of the cartesian square for `W' ×_Y X` cut by the cartesian square for
`W ×_Y X`. -/
theorem pullback.isPullback_mapFst {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y)
    [HasPullback a z] [HasPullback (t ≫ a) z] :
    IsPullback (pullback.fst (t ≫ a) z) (pullback.mapFst t a z) t (pullback.fst a z) := by
  refine IsPullback.flip
    (IsPullback.of_right ?_ (pullback.mapFst_fst t a z) (IsPullback.of_hasPullback a z).flip)
  rw [pullback.mapFst_snd]
  exact (IsPullback.of_hasPullback (t ≫ a) z).flip

/-- The comparison map `W ×_Y X' ⟶ W ×_Y X` of fibre products induced by `t : X' ⟶ X`, for the
structure morphism `t ≫ b` on the source: the mirror image of
`CategoryTheory.Limits.pullback.mapFst`, and a definition of its own for the same reason. -/
noncomputable def pullback.mapSnd {W X X' Y : C} (t : X' ⟶ X) (a : W ⟶ Y) (b : X ⟶ Y)
    [HasPullback a b] [HasPullback a (t ≫ b)] : pullback a (t ≫ b) ⟶ pullback a b :=
  pullback.lift (pullback.fst a (t ≫ b)) (pullback.snd a (t ≫ b) ≫ t) (by
    rw [Category.assoc]
    exact pullback.condition)

/-- The first component of the comparison map of fibre products in the second factor. -/
@[simp, reassoc (attr := simp), ega "I 3.3.4" "first projection formula"]
theorem pullback.mapSnd_fst {W X X' Y : C} (t : X' ⟶ X) (a : W ⟶ Y) (b : X ⟶ Y) [HasPullback a b]
    [HasPullback a (t ≫ b)] :
    pullback.mapSnd t a b ≫ pullback.fst a b = pullback.fst a (t ≫ b) :=
  pullback.lift_fst _ _ _

/-- The second component of the comparison map of fibre products in the second factor. -/
@[simp, reassoc (attr := simp)]
theorem pullback.mapSnd_snd {W X X' Y : C} (t : X' ⟶ X) (a : W ⟶ Y) (b : X ⟶ Y) [HasPullback a b]
    [HasPullback a (t ≫ b)] :
    pullback.mapSnd t a b ≫ pullback.snd a b = pullback.snd a (t ≫ b) ≫ t :=
  pullback.lift_snd _ _ _

/-- Precomposing the second factor of a fibre product with `t : X' ⟶ X` produces a base change. -/
theorem pullback.isPullback_mapSnd {W X X' Y : C} (t : X' ⟶ X) (a : W ⟶ Y) (b : X ⟶ Y)
    [HasPullback a b] [HasPullback a (t ≫ b)] :
    IsPullback (pullback.snd a (t ≫ b)) (pullback.mapSnd t a b) t (pullback.snd a b) := by
  refine IsPullback.flip
    (IsPullback.of_right ?_ (pullback.mapSnd_snd t a b) (IsPullback.of_hasPullback a b))
  rw [pullback.mapSnd_fst]
  exact IsPullback.of_hasPullback a (t ≫ b)

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **The presheaf category of the big fppf site of `S` is locally `u`-small.** The site is
essentially small (Stacks 000J, through
`AlgebraicGeometry.Stack.essentiallySmall_bigFppfOver`), so restriction along a small model is a
faithful functor from the presheaf category to a locally small one.

This is what makes the relative morphism functor of Stacks 05Y2 small-valued, and it needs no
hypothesis on the presheaves involved: in particular the source's proof that a morphism out of an
algebraic space is determined by its restriction to an étale atlas is not needed for smallness. -/
theorem locallySmall_presheaf_bigFppfOver (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : LocallySmall.{u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  have := Stack.essentiallySmall_bigFppfOver B S hS
  locallySmall_of_faithful
    ((Functor.whiskeringLeft _ _ (Type u)).obj
      (equivSmallModel.{u} (BigFppfOver B S hS)).inverse.op)

/-- Morphisms between presheaves of `u`-types on the big fppf site of `S` form a `u`-small type. -/
theorem small_hom_presheaf {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (P X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Small.{u} (P ⟶ X) :=
  (locallySmall_presheaf_bigFppfOver B S hS).1 P X

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05Y1.** A pair `(a, b)` for the relative morphism functor of `z : Z ⟶ Q` and
`x : X ⟶ Q` at a test presheaf `T`: a morphism `a : T ⟶ Q` together with a morphism
`b : T ×_{a, Q} Z ⟶ X` lying over `Q`. The source's other description of `b`, as a morphism
`T ×_{a, Q} Z ⟶ T ×_{a, Q} X` over `T`, is equivalent to this one. -/
@[stacks_fixed 05Y1 "the pair `(a, b)` of the diagram"]
structure RelativeMorphism (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The morphism `a : T ⟶ Q` to the base. -/
  base : T ⟶ Q
  /-- The morphism `b : T ×_{a, Q} Z ⟶ X` from the base change of `Z`. -/
  morphism : pullback base z ⟶ X
  /-- The morphism `b` lies over the base. -/
  commutes : morphism ≫ x = pullback.snd base z ≫ z

variable {B S hS}

/-- **Two pairs with the same first component are equal as soon as their second components agree
after the canonical identification of the two base changes.** This is the only transport the
functoriality of the relative morphism functor needs. -/
theorem RelativeMorphism.ext_of_base_eq {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} {p q : RelativeMorphism B S hS Z X Q z x T} (hbase : p.base = q.base)
    (hm : p.morphism = (pullback.congrHom hbase rfl).hom ≫ q.morphism) : p = q := by
  obtain ⟨pb, pm, pc⟩ := p
  obtain ⟨qb, qm, qc⟩ := q
  cases hbase
  have hid : (pullback.congrHom (rfl : pb = pb) (rfl : z = z)).hom = 𝟙 (pullback pb z) := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  rw [hid, Category.id_comp] at hm
  cases hm
  rfl

/-- Restriction of a pair `(a, b)` along a morphism `t : T' ⟶ T` of test presheaves: compose `a`
with `t` and base change `b`. -/
noncomputable def RelativeMorphism.restrict {Z X Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (t : T' ⟶ T) (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism B S hS Z X Q z x T' where
  base := t ≫ p.base
  morphism :=
    pullback.map (t ≫ p.base) z p.base z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫ p.morphism
  commutes := by
    rw [Category.assoc, p.commutes, ← Category.assoc, pullback.map_snd]
    simp

/-- The first component of a restricted pair. -/
@[simp] theorem RelativeMorphism.restrict_base {Z X Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (t : T' ⟶ T) (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.restrict t p).base = t ≫ p.base := rfl

/-- The second component of a restricted pair. -/
@[simp] theorem RelativeMorphism.restrict_morphism {Z X Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (t : T' ⟶ T) (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.restrict t p).morphism =
      pullback.map (t ≫ p.base) z p.base z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫ p.morphism :=
  rfl

/-- Restriction along an identity does nothing. The second component is unchanged on the nose:
the base change `CategoryTheory.Limits.pullback.map` restriction along `𝟙` produces is literally
the comparison isomorphism of
`AlgebraicGeometry.Space.RelativeMorphism.ext_of_base_eq`. -/
@[simp] theorem RelativeMorphism.restrict_id {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism.restrict (𝟙 T) p = p :=
  RelativeMorphism.ext_of_base_eq (Category.id_comp p.base) rfl

/-- Restriction along a composite is the composite of the restrictions. -/
theorem RelativeMorphism.restrict_comp {Z X Q T T' T'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (t : T' ⟶ T) (t' : T'' ⟶ T')
    (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism.restrict t' (RelativeMorphism.restrict t p) =
      RelativeMorphism.restrict (t' ≫ t) p := by
  have key : pullback.map (t' ≫ t ≫ p.base) z (t ≫ p.base) z t' (𝟙 Z) (𝟙 Q)
        (by simp) (by simp) ≫
      pullback.map (t ≫ p.base) z p.base z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) =
      (pullback.congrHom (Category.assoc t' t p.base).symm (rfl : z = z)).hom ≫
        pullback.map ((t' ≫ t) ≫ p.base) z p.base z (t' ≫ t) (𝟙 Z) (𝟙 Q)
          (by simp) (by simp) := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  exact RelativeMorphism.ext_of_base_eq (Category.assoc t' t p.base).symm
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ p.morphism) key).trans (Category.assoc _ _ _)))

/-! ### The diagram of a pair, in the shape Stacks 05Y1 displays it -/

/-- **The morphism of base changes attached to a pair of Stacks 05Y1.** A pair `(a, b)` at a
test presheaf `T`, with `a : T ⟶ Q` and `b : T ×_{a, Q} Z ⟶ X` lying over `Q`, determines the
morphism `T ×_{a, Q} Z ⟶ T ×_{a, Q} X` with components the projection to `T` and `b`; this is
the morphism `b` that the diagram of Stacks 05Y1 displays. -/
noncomputable def RelativeMorphism.baseChangeMap
    {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} (p : RelativeMorphism B S hS Z X Q z x T) :
    pullback p.base z ⟶ pullback p.base x :=
  pullback.lift (pullback.fst p.base z) p.morphism (by
    rw [p.commutes]; exact pullback.condition)

/-- The morphism of base changes attached to a pair lies over the test presheaf. -/
@[reassoc (attr := simp)]
theorem RelativeMorphism.baseChangeMap_comp_fst {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (p : RelativeMorphism B S hS Z X Q z x T) :
    p.baseChangeMap ≫ pullback.fst p.base x = pullback.fst p.base z :=
  pullback.lift_fst _ _ _

/-- The second component of the morphism of base changes attached to a pair is the second
component of the pair. -/
@[reassoc (attr := simp)]
theorem RelativeMorphism.baseChangeMap_comp_snd {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (p : RelativeMorphism B S hS Z X Q z x T) :
    p.baseChangeMap ≫ pullback.snd p.base x = p.morphism :=
  pullback.lift_snd _ _ _

variable (B S hS)

/-- **Stacks 05Y1.** The diagram of a pair at a test presheaf `T`, in the shape the source
displays it: a morphism `a : T ⟶ Q` together with a morphism
`b : T ×_{a, Q} Z ⟶ T ×_{a, Q} X` *over `T`*, that is, commuting with the two projections to
`T`.

This is the first of the source's two descriptions of a pair; the second,
`AlgebraicGeometry.Space.RelativeMorphism`, reads `b` instead as a morphism
`T ×_{a, Q} Z ⟶ X` lying over `Q`. The two are the same data —
`AlgebraicGeometry.Space.relativeMorphismEquivDiagram`. -/
@[stacks_fixed 05Y1 "the displayed diagram: `b : T ×_{a, B} Z ⟶ T ×_{a, B} X` over `T`"]
structure RelativeMorphismDiagram (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (x : X ⟶ Q) (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The morphism `a : T ⟶ Q` to the base. -/
  base : T ⟶ Q
  /-- The morphism `b : T ×_{a, Q} Z ⟶ T ×_{a, Q} X` of the two base changes. -/
  morphism : pullback base z ⟶ pullback base x
  /-- The morphism `b` is a morphism over the test presheaf `T`. -/
  commutes : morphism ≫ pullback.fst base x = pullback.fst base z

variable {B S hS}

/-- The pair `(a, b)` underlying a diagram, in the source's second description: the second
component is the morphism of base changes followed by the projection to `X`. -/
noncomputable def RelativeMorphismDiagram.toRelativeMorphism
    {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (q : RelativeMorphismDiagram B S hS Z X Q z x T) :
    RelativeMorphism B S hS Z X Q z x T where
  base := q.base
  morphism := q.morphism ≫ pullback.snd q.base x
  commutes := by
    have h : pullback.snd q.base x ≫ x = pullback.fst q.base x ≫ q.base :=
      pullback.condition.symm
    rw [Category.assoc, h, ← Category.assoc, q.commutes]
    exact pullback.condition

/-- The first component of the pair underlying a diagram. -/
@[simp] theorem RelativeMorphismDiagram.toRelativeMorphism_base
    {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (q : RelativeMorphismDiagram B S hS Z X Q z x T) :
    q.toRelativeMorphism.base = q.base := rfl

/-- The second component of the pair underlying a diagram. -/
@[simp] theorem RelativeMorphismDiagram.toRelativeMorphism_morphism
    {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (q : RelativeMorphismDiagram B S hS Z X Q z x T) :
    q.toRelativeMorphism.morphism = q.morphism ≫ pullback.snd q.base x := rfl

attribute [local implicit_reducible] RelativeMorphismDiagram.toRelativeMorphism

/-- **The source's two descriptions of a pair of Stacks 05Y1 are the same data.** The displayed
diagram gives `b` as a morphism `T ×_{a, Q} Z ⟶ T ×_{a, Q} X` over `T`, and the source then
remarks that `b` may equally be read as a morphism `T ×_{a, Q} Z ⟶ X` lying over `Q`. The two
readings are exchanged by `AlgebraicGeometry.Space.RelativeMorphism.baseChangeMap`, which adds
the projection to `T` as a first component, and by composition with the projection to `X`. -/
noncomputable def relativeMorphismEquivDiagram {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} :
    RelativeMorphism B S hS Z X Q z x T ≃ RelativeMorphismDiagram B S hS Z X Q z x T where
  toFun p := ⟨p.base, p.baseChangeMap, p.baseChangeMap_comp_fst⟩
  invFun q := q.toRelativeMorphism
  left_inv p := by
    obtain ⟨b, m, hc⟩ := p
    simp only [RelativeMorphismDiagram.toRelativeMorphism, RelativeMorphism.mk.injEq, heq_eq_eq,
      true_and]
    exact RelativeMorphism.baseChangeMap_comp_snd _
  right_inv q := by
    obtain ⟨b, m, hc⟩ := q
    simp only [RelativeMorphismDiagram.toRelativeMorphism, RelativeMorphismDiagram.mk.injEq,
      heq_eq_eq, true_and]
    refine pullback.hom_ext ?_ ?_
    · rw [RelativeMorphism.baseChangeMap_comp_fst]
      exact hc.symm
    · rw [RelativeMorphism.baseChangeMap_comp_snd]

/-- The projection of the relative morphism functor reads off the first component of a pair, and
is natural: stated for a pair `pU` *presented* as a restriction of `pT`, so that the identification
of the values of the functor with pairs is supplied as an argument rather than rewritten into the
goal. -/
theorem yonedaEquiv_base_of_eq_restrict {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {T U : BigFppfOver B S hS} (f : U ⟶ T)
    {pT : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)}
    {pU : RelativeMorphism B S hS Z X Q z x (yoneda.obj U)}
    (h : pU = RelativeMorphism.restrict (yoneda.map f) pT) :
    yonedaEquiv pU.base = Q.map f.op (yonedaEquiv pT.base) := by
  subst h
  rw [RelativeMorphism.restrict_base]
  exact (yonedaEquiv_naturality _ f).symm

/-- The restriction maps of the relative morphism functor are base change of pairs: the
specification `AlgebraicGeometry.Space.RelativeHomConstruction.sections_map` asks for, stated for a
pair `pU` *presented* as a restriction of `pT`. -/
theorem sections_map_of_eq_restrict {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} {T U : BigFppfOver B S hS} (f : U ⟶ T)
    {pT : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)}
    {pU : RelativeMorphism B S hS Z X Q z x (yoneda.obj U)}
    (hpU : pU = RelativeMorphism.restrict (yoneda.map f) pT) :
    (pU.base = yoneda.map f ≫ pT.base) ∧
      ∃ h : pullback pU.base z ⟶ pullback pT.base z,
        (h ≫ pullback.fst pT.base z = pullback.fst pU.base z ≫ yoneda.map f) ∧
        (h ≫ pullback.snd pT.base z = pullback.snd pU.base z) ∧
        (pU.morphism = h ≫ pT.morphism) := by
  subst hpU
  exact ⟨rfl, pullback.map (yoneda.map f ≫ pT.base) z pT.base z (yoneda.map f) (𝟙 Z) (𝟙 Q)
      (by simp) (by simp), by simp, by simp, rfl⟩

variable (B S hS)

/-- The pairs of Stacks 05Y1 form a `u`-small type: a pair is a morphism `T ⟶ Q` together with a
morphism out of a base change of `Z`, and every hom type of the presheaf category is `u`-small by
`AlgebraicGeometry.locallySmall_presheaf_bigFppfOver`. No algebraic-space hypothesis is used. -/
instance small_relativeMorphism (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Small.{u} (RelativeMorphism B S hS Z X Q z x T) := by
  have : Small.{u} (T ⟶ Q) := small_hom_presheaf T Q
  have : ∀ a : T ⟶ Q, Small.{u} (pullback a z ⟶ X) := fun a => small_hom_presheaf _ X
  refine small_of_injective (f := fun p : RelativeMorphism B S hS Z X Q z x T =>
      (⟨p.base, ⟨p.morphism, p.commutes⟩⟩ :
        Σ a : T ⟶ Q, {b : pullback a z ⟶ X // b ≫ x = pullback.snd a z ≫ z})) ?_
  intro p q hpq
  obtain ⟨pb, pm, pc⟩ := p
  obtain ⟨qb, qm, qc⟩ := q
  cases hpq
  rfl

/-- **Stacks 05Y2**, the data the relative morphism functor is specified by: a presheaf on the big
fppf site of `S`, its projection to `Q`, the identification of its sections over a scheme `T` with
the pairs of Stacks 05Y1 at `T`, the compatibility of that identification with the projection, and
the description of its restriction maps as base change of pairs. -/
structure RelativeHomConstruction (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (x : X ⟶ Q) where
  /-- The relative morphism functor. -/
  functor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its projection to the base, remembering the first component of a pair. -/
  projection : functor ⟶ Q
  /-- Its sections over a scheme are the pairs of Stacks 05Y1. -/
  sections : ∀ T : BigFppfOver B S hS,
    functor.obj (Opposite.op T) ≃ RelativeMorphism B S hS Z X Q z x (yoneda.obj T)
  /-- The projection reads off the first component of a pair. -/
  projection_sections : ∀ (T : BigFppfOver B S hS) (p : functor.obj (Opposite.op T)),
    projection.app (Opposite.op T) p = yonedaEquiv ((sections T p).base)
  /-- The restriction maps are base change of pairs. -/
  sections_map : ∀ {T U : BigFppfOver B S hS} (f : U ⟶ T) (p : functor.obj (Opposite.op T)),
    let pT := sections T p
    let pU := sections U (functor.map f.op p)
    (pU.base = yoneda.map f ≫ pT.base) ∧
      ∃ h : pullback pU.base z ⟶ pullback pT.base z,
        (h ≫ pullback.fst pT.base z = pullback.fst pU.base z ≫ yoneda.map f) ∧
        (h ≫ pullback.snd pT.base z = pullback.snd pU.base z) ∧
        (pU.morphism = h ≫ pT.morphism)

/-- The relative morphism functor of Stacks 05Y2, as a presheaf: its value at `T` is the type of
pairs of Stacks 05Y1 at `yoneda.obj T`, transported into the universe of the site, and its
restriction maps are base change of pairs. -/
noncomputable def relativeHomPresheaf (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (x : X ⟶ Q) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := Shrink (RelativeMorphism B S hS Z X Q z x (yoneda.obj T.unop))
  map {T U} f := ↾fun p =>
    equivShrink (RelativeMorphism B S hS Z X Q z x (yoneda.obj U.unop))
      (RelativeMorphism.restrict (yoneda.map f.unop)
        ((equivShrink (RelativeMorphism B S hS Z X Q z x (yoneda.obj T.unop))).symm p))
  map_id T := by
    ext p
    simp
  map_comp {T U V} f g := by
    ext p
    simp [RelativeMorphism.restrict_comp]

/-- **Stacks 05Y2.** The relative morphism functor `Mor_Q(Z, X)` of two morphisms `z : Z ⟶ Q` and
`x : X ⟶ Q` of algebraic spaces over `S`: a small-valued presheaf on the big fppf site of `S`
whose sections over a scheme `T` are the pairs `(a, b)` of Stacks 05Y1, with its projection to `Q`
and with restriction given by base change.

The three algebraicity hypotheses are kept because the source states the functor for algebraic
spaces, but they are not used: smallness of the values comes from essential smallness of the
site (`AlgebraicGeometry.locallySmall_presheaf_bigFppfOver`), not from the existence of an étale
atlas. -/
@[stacks 05Y2]
noncomputable def relativeHomData (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (x : X ⟶ Q) (_hZ : IsAlgebraicSpace B S hS Z) (_hX : IsAlgebraicSpace B S hS X)
    (_hQ : IsAlgebraicSpace B S hS Q) : RelativeHomConstruction B S hS Z X Q z x where
  functor := relativeHomPresheaf B S hS Z X Q z x
  projection :=
    { app := fun T => ↾fun p => yonedaEquiv
        ((equivShrink (RelativeMorphism B S hS Z X Q z x (yoneda.obj T.unop))).symm p).base
      naturality := fun T U f => by
        ext p
        exact yonedaEquiv_base_of_eq_restrict f.unop (Equiv.symm_apply_apply _ _) }
  sections T := (equivShrink (RelativeMorphism B S hS Z X Q z x (yoneda.obj T))).symm
  projection_sections _T _p := rfl
  sections_map {_T _U} f p := sections_map_of_eq_restrict f (Equiv.symm_apply_apply _ _)

/-- **Stacks 05Y2.** The relative morphism functor `Mor_Q(Z, X)`. -/
noncomputable def relativeHom (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (relativeHomData B S hS Z X Q z x hZ hX hQ).functor

/-- The projection from the relative morphism functor to its base, remembering the first
component of a pair. -/
noncomputable def relativeHomProjection (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (x : X ⟶ Q) (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) : relativeHom B S hS Z X Q z x hZ hX hQ ⟶ Q :=
  (relativeHomData B S hS Z X Q z x hZ hX hQ).projection

/-- The sections of the relative morphism functor over a scheme are the pairs of Stacks 05Y1. -/
noncomputable def relativeHomSections (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (x : X ⟶ Q) (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) (T : BigFppfOver B S hS) :
    (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op T) ≃
      RelativeMorphism B S hS Z X Q z x (yoneda.obj T) :=
  (relativeHomData B S hS Z X Q z x hZ hX hQ).sections T

/-- Under the identification of the sections of the relative morphism functor with the pairs of
Stacks 05Y1, the restriction maps of the functor are restriction of pairs. This is the equality
`AlgebraicGeometry.Space.RelativeHomConstruction.sections_map` only asserts up to the existence of
a comparison map of base changes, available because the functor is built from
`AlgebraicGeometry.Space.RelativeMorphism.restrict` on the nose. -/
theorem relativeHomSections_map (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (p : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op T)) :
    relativeHomSections B S hS Z X Q z x hZ hX hQ T'
        ((relativeHom B S hS Z X Q z x hZ hX hQ).map g.op p) =
      RelativeMorphism.restrict (yoneda.map g)
        (relativeHomSections B S hS Z X Q z x hZ hX hQ T p) :=
  Equiv.symm_apply_apply _ _

end Space

end AlgebraicGeometry

end
